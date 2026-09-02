#!/usr/bin/env python3
"""Enforce a machine-readable Batteries lint baseline with a review-only ratchet.

This is the lint counterpart of ``check_warnings.py``.  It consumes the captured
output of Batteries' ``runLinter`` (``lake lint`` once the lint driver is
declared, or ``lake exe runLinter NumStability``), reconstructs every finding
as a line-independent fingerprint, and compares that census against a reviewed
baseline document.  New findings fail; resolved findings also fail, so the
ceiling can only move down through review.  Only the Python standard library
is used.

Identity never involves the reported line or column.  A finding is identified
by

    (linter, repo-relative path, fully-qualified declaration name,
     normalized message head, occurrence index within that group)

The declaration name is the stable anchor: editing a file shifts every line
below the edit, but ``runLinter`` names the declaration it is complaining
about, and that name survives reflowing, reordering, and unrelated edits in
the same file.  Lines and columns are recorded as evidence only.
"""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import io
import json
import re
import sys
import tempfile
from pathlib import Path
from typing import Any, Sequence


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_BASELINE = Path("docs/architecture/lint.json")
LEAN_TOOLCHAIN = Path("lean-toolchain")
LAKE_MANIFEST = Path("lake-manifest.json")

SCHEMA_VERSION = 1

# Bump whenever the normalization or fingerprint rules below change; a baseline
# written under an older normalization is refused rather than misread.
NORMALIZATION_VERSION = 1

# Lean source trees whose findings this contract governs.  Anything outside
# them (Mathlib, Batteries, toolchain sources) is not fingerprinted.
SOURCE_ROOTS = ("NumStability", "NumStabilityTest")

# ---------------------------------------------------------------------------
# Log grammar
# ---------------------------------------------------------------------------
#
# runLinter prints, in order:
#
#   -- Found N errors in M declarations (plus K automatically generated ones)
#      in <target> with L linters
#
#   /- The `<linter>` linter reports:
#   <note, one or more lines, the last ending in> -/
#   -- <Module.Name>
#   <abs path>.lean:<line>:<col>: error: <DeclName> <message head>
#     <indented continuation of the head (pretty-printer wrapping)>
#   <further message lines at column 0 (structural, not part of the head)>
#
# Modules are separated by blank lines; a blank line therefore ends a message.

ANSI_RE = re.compile("\x1b\\[[0-9;?]*[ -/]*[@-~]|\x1b\\][^\x07\x1b]*(?:\x07|\x1b\\\\)")
GH_TIMESTAMP_RE = re.compile(r"^\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d(?:\.\d+)?Z ")
RUNNER_WORKSPACE_RE = re.compile(
    r"(?:[A-Za-z]:)?(?:/[^/\s:]+)*/work/(?P<repo>[^/\s:]+)/(?P=repo)/"
)
ABSOLUTE_SOURCE_RE = re.compile(
    r"^(?:[A-Za-z]:)?[/\\][^\s]*?[/\\](?=(?:" + "|".join(SOURCE_ROOTS) + r")[/\\])"
)

SUMMARY_RE = re.compile(
    r"^-- Found (?P<findings>\d+) errors? in (?P<declarations>\d+) declarations? "
    r"\(plus (?P<generated>\d+) automatically generated ones?\) in "
    r"(?P<target>\S+) with (?P<linters>\d+) linters?"
)
ALL_PASSED_RE = re.compile(r"^-- All linting checks passed!")
MODULES_RE = re.compile(r"^Running linter on specified modules: \[(?P<modules>[^\]]*)\]")
LINTER_HEAD_RE = re.compile(r"^/- The `(?P<linter>[A-Za-z0-9_.]+)` linter reports:")
NOTE_END_RE = re.compile(r"-/\s*$")
MODULE_HEAD_RE = re.compile(r"^-- (?P<module>[^\s]+)\s*$")
FINDING_HEAD_RE = re.compile(
    r"^(?P<path>(?:[A-Za-z]:)?[^:]+?\.lean):(?P<line>\d+):(?P<column>\d+): "
    r"error: (?P<decl>@?\S+)(?: (?P<rest>.*))?$"
)
# Lake progress markers: "✔ [12/34] Built X", "⚠ [12/34] Replayed X".
LAKE_PROGRESS_RE = re.compile(r"^(?:[^\s\[]{1,3}\s*)?\[\d+/\d+\]")
# Positions inside a message body are evidence, never identity.
POSITION_RE = re.compile(r":\d+:\d+(?=\b|:)")
SHA1_RE = re.compile(r"^[0-9a-f]{40}$")

# ---------------------------------------------------------------------------
# Linter classification
# ---------------------------------------------------------------------------
#
# Batteries' standard linter set.  A finding attributed to a linter outside
# this table is unclassifiable and fails loudly; the table is extended by
# review rather than silently widened.
KNOWN_LINTERS = (
    "checkType",
    "checkUnivs",
    "defLemma",
    "docBlame",
    "docBlameThm",
    "dupNamespace",
    "explicitVarsOfIff",
    "impossibleInstance",
    "nonClassInstance",
    "simpComm",
    "simpNF",
    "simpVarHead",
    "structureInType",
    "synTaut",
    "unusedArguments",
    "unusedHavesSuffices",
)

LINTER_RATIONALE: dict[str, str] = {
    "defLemma": (
        "Pre-existing `def` whose type is a proposition (or `theorem` whose "
        "type is data); changing the keyword is mechanical but alters "
        "reducibility, so each site must be re-elaborated with its users."
    ),
    "docBlame": (
        "Pre-existing definition without a docstring; writing one requires "
        "understanding the declaration, not a mechanical edit."
    ),
    "simpNF": (
        "Pre-existing `@[simp]` lemma whose left-hand side is not in simp-normal "
        "form or that `simp` can already prove; fixing it changes the simp set "
        "and must be checked against every downstream `simp` call."
    ),
    "unusedArguments": (
        "Pre-existing hypothesis or instance argument that the declaration does "
        "not use; removing it changes the declaration's signature and every "
        "call site."
    ),
}

LINTER_RECONSIDERATION_TRIGGER: dict[str, str] = {
    "defLemma": (
        "Reconsider when the owning declaration is next edited, or in a "
        "reviewed def/theorem keyword batch for the owning module."
    ),
    "docBlame": (
        "Reconsider when the owning declaration is next edited, or in a "
        "reviewed documentation batch for the owning module."
    ),
    "simpNF": (
        "Reconsider when the owning lemma is next edited, or on a Mathlib bump "
        "that changes the simp set and hence the linter's verdict."
    ),
    "unusedArguments": (
        "Reconsider when the owning declaration's signature is next edited."
    ),
}
DEFAULT_RATIONALE = "Pre-existing accepted lint finding."
DEFAULT_RECONSIDERATION_TRIGGER = "Reconsider when the owning declaration is next edited."

BASELINE_DEBT = "baseline_debt"
# A record is either unreviewed debt or one the reviewer keeps deliberately.
# Both are enforced identically -- the disposition explains why a record is
# here, it never relaxes the contract.
REVIEWED_COMPATIBILITY_EXCEPTION = "reviewed_compatibility_exception"
REVIEWED_DEFERRED_MIGRATION = "reviewed_deferred_migration"
REVIEWED_UPSTREAM_EXCEPTION = "reviewed_upstream_exception"
REVIEWED_UNTYPED_PROOF_DEF = "reviewed_untyped_proof_def"
DISPOSITIONS = frozenset(
    {
        BASELINE_DEBT,
        REVIEWED_COMPATIBILITY_EXCEPTION,
        REVIEWED_DEFERRED_MIGRATION,
        REVIEWED_UPSTREAM_EXCEPTION,
        REVIEWED_UNTYPED_PROOF_DEF,
    }
)
# Reviewed dispositions keyed by (linter, path). Applied at record construction
# so they survive regeneration from a bare log, not only a carry from a previous
# baseline. Enforced identically to debt: the fingerprint is still frozen and any
# NEW finding under the same key is still a contract violation.
_UNTYPED_PROOF_DEF = {
    "disposition": REVIEWED_UNTYPED_PROOF_DEF,
    "rationale": (
        "Proof-valued declaration written as an untyped `def X := fun ... => ...` "
        "with no statement in the source. Converting it to `theorem` requires the "
        "statement, which Lean refuses to infer (`Failed to infer type of theorem`, "
        "verified empirically on all 108 PartialPivoting sites on 2026-09-01) and "
        "which pretty-prints to roughly 280 lines per declaration. Making these "
        "theorems is a rewrite of the generated Chapter 11 files, outside the lint "
        "programme. A `@[nolint defLemma]` marker was rejected because it would "
        "assert the def is deliberate, which is not the case."
    ),
    "expiry_release": "when the Chapter 11 generated proofs receive explicit statements",
    "reconsideration_trigger": (
        "Reconsider when the owning file is regenerated or its declarations gain "
        "explicit type signatures; a converted declaration then disappears from the "
        "census as a reviewed reduction."
    ),
}
REVIEWED_DISPOSITIONS: dict[tuple[str, str], dict[str, Any]] = {
    ("defLemma", "NumStability/Source/Higham/Chapter11/Section02/Aasen.lean"): _UNTYPED_PROOF_DEF,
    ("defLemma", "NumStability/Source/Higham/Chapter11/Section01/Tridiagonal.lean"): _UNTYPED_PROOF_DEF,
    ("defLemma", "NumStability/Source/Higham/Chapter11/Section01/PartialPivoting.lean"): _UNTYPED_PROOF_DEF,
}
# Reviewed dispositions survive a re-capture; debt is re-derived.
CARRIED_REVIEW_FIELDS = (
    "disposition",
    "expiry_release",
    "rationale",
    "reconsideration_trigger",
    "reviewer",
)
ACCEPTED_BASELINE = "accepted_baseline"
PRIMARY_REVIEWER = "primary-human"
LINT_COMMAND = "lake lint"


class InputError(RuntimeError):
    """Malformed input that prevents the contract from being evaluated."""


class Problems:
    """Accumulate malformed-input and contract-violation findings."""

    def __init__(self) -> None:
        self.format_errors: list[str] = []
        self.contract_errors: list[str] = []

    def malformed(self, context: str, message: str) -> None:
        self.format_errors.append(f"{context}: {message}")

    def violation(self, context: str, message: str) -> None:
        self.contract_errors.append(f"{context}: {message}")

    @property
    def ok(self) -> bool:
        return not self.format_errors and not self.contract_errors

    def render(self) -> None:
        for message in sorted(set(self.format_errors)):
            print(f"error: malformed input: {message}", file=sys.stderr)
        for message in sorted(set(self.contract_errors)):
            print(f"error: contract violation: {message}", file=sys.stderr)

    def exit_code(self) -> int:
        if self.format_errors:
            return 2
        return 1 if self.contract_errors else 0


# ---------------------------------------------------------------------------
# Small helpers
# ---------------------------------------------------------------------------


class DuplicateKeyError(ValueError):
    pass


def duplicate_safe_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise DuplicateKeyError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def load_json(path: Path, label: str) -> dict[str, Any]:
    try:
        value = json.loads(
            path.read_text(encoding="utf-8"), object_pairs_hook=duplicate_safe_object
        )
    except (OSError, UnicodeError, json.JSONDecodeError, DuplicateKeyError) as error:
        raise InputError(f"cannot read {label}: {error}") from error
    if not isinstance(value, dict):
        raise InputError(f"expected a JSON object in {label}")
    return value


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def module_name(path: str) -> str:
    return ".".join(Path(path).with_suffix("").parts)


def collapse(text: str) -> str:
    return " ".join(text.split())


def normalize_message(text: str) -> str:
    """Strip positions and collapse whitespace; the result is identity material."""

    return collapse(POSITION_RE.sub("", text))


def read_toolchain(root: Path) -> str | None:
    path = root / LEAN_TOOLCHAIN
    try:
        return path.read_text(encoding="utf-8").strip()
    except OSError:
        return None


def mathlib_rev(root: Path) -> str | None:
    path = root / LAKE_MANIFEST
    if not path.is_file():
        return None
    manifest = load_json(path, LAKE_MANIFEST.as_posix())
    packages = manifest.get("packages")
    if not isinstance(packages, list):
        return None
    for package in packages:
        if isinstance(package, dict) and package.get("name") == "mathlib":
            revision = package.get("rev")
            return revision if isinstance(revision, str) else None
    return None


# ---------------------------------------------------------------------------
# Log normalization and finding reconstruction
# ---------------------------------------------------------------------------


Identity = tuple[str, str, str, str, int]


class Finding:
    __slots__ = (
        "linter",
        "path",
        "line",
        "column",
        "declaration",
        "message_head",
        "message",
        "occurrence",
    )

    def __init__(
        self,
        linter: str,
        path: str,
        line: int,
        column: int,
        declaration: str,
        message_head: str,
        message: str,
    ) -> None:
        self.linter = linter
        self.path = path
        self.line = line
        self.column = column
        self.declaration = declaration
        self.message_head = message_head
        self.message = message
        self.occurrence = 0

    @property
    def message_head_sha256(self) -> str:
        return sha256_text(self.message_head)

    @property
    def identity(self) -> Identity:
        return (
            self.linter,
            self.path,
            self.declaration,
            self.message_head_sha256,
            self.occurrence,
        )


class LogCapture:
    """Everything a baseline needs from one captured runLinter log."""

    def __init__(self) -> None:
        self.modules: str | None = None
        self.reported_findings: int | None = None
        self.reported_declarations: int | None = None
        self.reported_generated: int | None = None
        self.reported_linters: int | None = None
        self.reported_target: str | None = None
        self.all_passed = False
        self.findings: list[Finding] = []
        # (line number, text, reason) for input the grammar does not cover.
        self.unclassified: list[tuple[int, str, str]] = []


def normalize_log_lines(raw: bytes) -> list[str]:
    """Apply every normalization step to a captured log, in order."""

    text = raw.decode("utf-8", errors="replace")
    if text.startswith("\ufeff"):
        text = text[1:]
    text = text.replace("\r\n", "\n").replace("\r", "\n")
    lines: list[str] = []
    for line in text.split("\n"):
        line = line.lstrip("\ufeff")
        line = ANSI_RE.sub("", line)
        line = GH_TIMESTAMP_RE.sub("", line)
        line = RUNNER_WORKSPACE_RE.sub("", line)
        lines.append(line.rstrip())
    return lines


def normalize_source_path(value: str) -> str:
    value = ABSOLUTE_SOURCE_RE.sub("", value)
    return value.replace("\\", "/")


def governed(path: str) -> bool:
    return path.startswith(tuple(root + "/" for root in SOURCE_ROOTS)) or (
        module_name(path) in SOURCE_ROOTS
    )


def is_record_boundary(line: str) -> bool:
    """True when `line` starts a new record rather than continuing a message."""

    return (
        not line.strip()
        or bool(FINDING_HEAD_RE.match(line))
        or bool(MODULE_HEAD_RE.match(line))
        or bool(LINTER_HEAD_RE.match(line))
        or bool(LAKE_PROGRESS_RE.match(line))
    )


def read_log(path: Path) -> LogCapture:
    try:
        raw = path.read_bytes()
    except OSError as error:
        raise InputError(f"cannot read log {path}: {error}") from error

    capture = LogCapture()
    lines = normalize_log_lines(raw)
    linter: str | None = None
    module: str | None = None
    in_note = False
    index = 0
    while index < len(lines):
        line = lines[index]
        number = index + 1
        index += 1
        if in_note:
            if NOTE_END_RE.search(line):
                in_note = False
            continue
        if not line.strip() or LAKE_PROGRESS_RE.match(line):
            continue
        modules = MODULES_RE.match(line)
        if modules:
            capture.modules = modules.group("modules").strip()
            continue
        summary = SUMMARY_RE.match(line)
        if summary:
            capture.reported_findings = int(summary.group("findings"))
            capture.reported_declarations = int(summary.group("declarations"))
            capture.reported_generated = int(summary.group("generated"))
            capture.reported_linters = int(summary.group("linters"))
            capture.reported_target = summary.group("target")
            continue
        if ALL_PASSED_RE.match(line):
            capture.all_passed = True
            continue
        head = LINTER_HEAD_RE.match(line)
        if head:
            linter = head.group("linter")
            module = None
            in_note = not NOTE_END_RE.search(line)
            continue
        finding = FINDING_HEAD_RE.match(line)
        if finding:
            if linter is None:
                capture.unclassified.append(
                    (number, line, "finding precedes any linter header")
                )
                continue
            source_path = normalize_source_path(finding.group("path"))
            body: list[str] = []
            while index < len(lines) and not is_record_boundary(lines[index]):
                body.append(lines[index])
                index += 1
            if not governed(source_path):
                continue
            # The head is the first message line plus its pretty-printer
            # wrapping (indented continuation lines).  Column-0 lines that
            # follow ("to", "using", "Try to change ...") are structural detail
            # kept as evidence, not identity.
            head_pieces = [finding.group("rest") or ""]
            for entry in body:
                if entry[:1].isspace():
                    head_pieces.append(entry)
                else:
                    break
            message_head = normalize_message(" ".join(head_pieces))
            message = normalize_message(" ".join(head_pieces[:1] + body))
            declaration = finding.group("decl").lstrip("@")
            item = Finding(
                linter=linter,
                path=source_path,
                line=int(finding.group("line")),
                column=int(finding.group("column")),
                declaration=declaration,
                message_head=message_head,
                message=message,
            )
            if linter not in KNOWN_LINTERS:
                capture.unclassified.append(
                    (number, line, f"unknown linter `{linter}`")
                )
                continue
            if module is not None and module_name(source_path) != module:
                capture.unclassified.append(
                    (
                        number,
                        line,
                        f"module header `{module}` does not match path {source_path}",
                    )
                )
                continue
            capture.findings.append(item)
            continue
        module_head = MODULE_HEAD_RE.match(line)
        if module_head and linter is not None:
            module = module_head.group("module")
            continue
        if linter is None:
            # Lake/Lean chatter before the first linter section.
            continue
        capture.unclassified.append((number, line, "line does not match the grammar"))

    assign_occurrences(capture.findings)
    return capture


def assign_occurrences(findings: Sequence[Finding]) -> None:
    counters: dict[tuple[str, str, str, str], int] = {}
    for finding in findings:
        key = (finding.linter, finding.path, finding.declaration, finding.message_head_sha256)
        finding.occurrence = counters.get(key, 0)
        counters[key] = finding.occurrence + 1


def sort_findings(findings: Sequence[Finding]) -> list[Finding]:
    return sorted(
        findings,
        key=lambda item: (
            item.path,
            item.linter,
            item.declaration,
            item.message_head_sha256,
            item.occurrence,
        ),
    )


# ---------------------------------------------------------------------------
# Census and baseline document
# ---------------------------------------------------------------------------


class Census:
    def __init__(self, findings: Sequence[Finding]) -> None:
        self.findings = list(findings)
        self.by_linter: dict[str, int] = {}
        self.by_file: dict[str, int] = {}
        self.files_by_linter: dict[str, set[str]] = {}
        for finding in self.findings:
            self.by_linter[finding.linter] = self.by_linter.get(finding.linter, 0) + 1
            self.by_file[finding.path] = self.by_file.get(finding.path, 0) + 1
            self.files_by_linter.setdefault(finding.linter, set()).add(finding.path)

    @property
    def total(self) -> int:
        return len(self.findings)

    @property
    def files(self) -> int:
        return len(self.by_file)

    def render(self) -> str:
        lines = [
            f"findings: {self.total}",
            f"linters: {len(self.by_linter)}",
            f"files: {self.files}",
        ]
        for linter in sorted(self.by_linter):
            lines.append(
                f"  {linter}: {self.by_linter[linter]} finding(s) / "
                f"{len(self.files_by_linter[linter])} file(s)"
            )
        return "\n".join(lines)


def finding_record(
    finding: Finding, commit: str | None, previous: dict[str, Any] | None
) -> dict[str, Any]:
    record: dict[str, Any] = {
        "declaration": finding.declaration,
        "disposition": BASELINE_DEBT,
        "evidence": {
            "column": finding.column,
            "line": finding.line,
            "message": finding.message,
        },
        "expiry_release": None,
        "introduced_at": commit,
        "linter": finding.linter,
        "message_head": finding.message_head,
        "message_head_sha256": finding.message_head_sha256,
        "module": module_name(finding.path),
        "occurrence": finding.occurrence,
        "owner_family": finding.linter,
        "path": finding.path,
        "rationale": LINTER_RATIONALE.get(finding.linter, DEFAULT_RATIONALE),
        "reconsideration_trigger": LINTER_RECONSIDERATION_TRIGGER.get(
            finding.linter, DEFAULT_RECONSIDERATION_TRIGGER
        ),
        "reviewer": PRIMARY_REVIEWER,
        "status": ACCEPTED_BASELINE,
    }
    reviewed = REVIEWED_DISPOSITIONS.get((finding.linter, finding.path))
    if reviewed is not None:
        record.update(reviewed)
    if previous is not None and previous.get("disposition") in DISPOSITIONS - {BASELINE_DEBT}:
        for key in CARRIED_REVIEW_FIELDS:
            if key in previous:
                record[key] = previous[key]
        if "introduced_at" in previous:
            record["introduced_at"] = previous["introduced_at"]
    return record


def previous_records(previous: dict[str, Any] | None) -> dict[Identity, dict[str, Any]]:
    known: dict[Identity, dict[str, Any]] = {}
    if not previous:
        return known
    entries = previous.get("findings")
    if not isinstance(entries, list):
        return known
    for entry in entries:
        if not isinstance(entry, dict):
            continue
        try:
            key = (
                str(entry["linter"]),
                str(entry["path"]),
                str(entry["declaration"]),
                str(entry["message_head_sha256"]),
                int(entry.get("occurrence") or 0),
            )
        except (KeyError, TypeError, ValueError):
            continue
        known[key] = entry
    return known


def build_baseline(
    root: Path,
    capture: LogCapture,
    findings: Sequence[Finding],
    census: Census,
    commit: str | None,
    previous: dict[str, Any] | None,
) -> dict[str, Any]:
    known = previous_records(previous)
    return {
        "capture": {
            "command": LINT_COMMAND,
            "commit": commit,
            "mathlib_revision": mathlib_rev(root),
            "modules": capture.modules,
            "reported": {
                "automatically_generated_declarations": capture.reported_generated,
                "declarations": capture.reported_declarations,
                "findings": capture.reported_findings,
                "linters_run": capture.reported_linters,
                "target": capture.reported_target,
            },
            "toolchain": read_toolchain(root),
        },
        "ceilings": {
            "by_file": dict(sorted(census.by_file.items())),
            "by_linter": dict(sorted(census.by_linter.items())),
            "global": census.total,
        },
        "findings": [
            finding_record(finding, commit, known.get(finding.identity))
            for finding in findings
        ],
        "normalization_version": NORMALIZATION_VERSION,
        "schema_version": SCHEMA_VERSION,
    }


def write_baseline(path: Path, document: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(document, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
        newline="\n",
    )


# ---------------------------------------------------------------------------
# --check
# ---------------------------------------------------------------------------


def baseline_identities(
    baseline: dict[str, Any], problems: Problems
) -> dict[Identity, dict[str, Any]]:
    entries = baseline.get("findings")
    if not isinstance(entries, list):
        problems.malformed("baseline", "`findings` must be a list")
        return {}
    identities: dict[Identity, dict[str, Any]] = {}
    for entry in entries:
        if not isinstance(entry, dict):
            problems.malformed("baseline", "each finding must be an object")
            continue
        linter = entry.get("linter")
        path = entry.get("path")
        declaration = entry.get("declaration")
        head = entry.get("message_head")
        head_sha = entry.get("message_head_sha256")
        occurrence = entry.get("occurrence")
        if not isinstance(linter, str) or not isinstance(path, str):
            problems.malformed("baseline", f"finding lacks linter/path: {entry!r}")
            continue
        if not isinstance(declaration, str) or not declaration:
            problems.malformed("baseline", f"finding lacks a declaration: {path}")
            continue
        if not isinstance(head, str) or not isinstance(head_sha, str):
            problems.malformed("baseline", f"finding lacks a message head: {declaration}")
            continue
        if sha256_text(head) != head_sha:
            problems.malformed("baseline", f"finding message head hash mismatch: {declaration}")
            continue
        if not isinstance(occurrence, int):
            problems.malformed("baseline", f"finding lacks an occurrence: {declaration}")
            continue
        if linter not in KNOWN_LINTERS:
            problems.malformed("baseline", f"finding records an unknown linter: {linter}")
            continue
        if entry.get("disposition") not in DISPOSITIONS:
            problems.malformed(
                "baseline",
                f"finding disposition must be one of {sorted(DISPOSITIONS)}: "
                f"{declaration} records {entry.get('disposition')!r}",
            )
        if entry.get("owner_family") != linter:
            problems.malformed(
                "baseline", f"finding owner_family must equal its linter: {declaration}"
            )
        for field in ("rationale", "reconsideration_trigger"):
            value = entry.get(field)
            if not isinstance(value, str) or not value.strip():
                problems.malformed(
                    "baseline", f"finding lacks a nonempty {field}: {declaration}"
                )
        if "expiry_release" not in entry:
            problems.malformed("baseline", f"finding lacks expiry_release: {declaration}")
        if entry.get("status") != ACCEPTED_BASELINE:
            problems.malformed(
                "baseline", f"finding status must be {ACCEPTED_BASELINE}: {declaration}"
            )
        if entry.get("reviewer") != PRIMARY_REVIEWER:
            problems.malformed("baseline", f"finding lacks a reviewer: {declaration}")
        key = (linter, path, declaration, head_sha, occurrence)
        if key in identities:
            problems.malformed(
                "baseline", f"duplicate finding fingerprint: {linter} {declaration}"
            )
            continue
        identities[key] = entry
    return identities


def check_ceilings(baseline: dict[str, Any], census: Census, problems: Problems) -> None:
    ceilings = baseline.get("ceilings")
    if not isinstance(ceilings, dict):
        problems.malformed("baseline", "`ceilings` must be an object")
        return
    global_ceiling = ceilings.get("global")
    if not isinstance(global_ceiling, int):
        problems.malformed("baseline", "`ceilings.global` must be an integer")
    elif census.total > global_ceiling:
        problems.violation(
            "ceilings",
            f"global lint ceiling exceeded: {census.total} finding(s) against a "
            f"ceiling of {global_ceiling}",
        )
    for bucket, observed, label in (
        ("by_linter", census.by_linter, "linter"),
        ("by_file", census.by_file, "file"),
    ):
        table = ceilings.get(bucket)
        if not isinstance(table, dict):
            problems.malformed("baseline", f"`ceilings.{bucket}` must be an object")
            continue
        for key, count in sorted(observed.items()):
            ceiling = table.get(key)
            if ceiling is None:
                if bucket == "by_file":
                    problems.violation(
                        "ceilings",
                        f"file has no reviewed lint allowance (zero-finding ceiling "
                        f"for new or changed files): {key} emitted {count} finding(s)",
                    )
                else:
                    problems.violation(
                        "ceilings",
                        f"per-{label} lint ceiling is missing for {key}: "
                        f"{count} finding(s) observed",
                    )
                continue
            if not isinstance(ceiling, int):
                problems.malformed("baseline", f"ceilings.{bucket}[{key}] must be an integer")
                continue
            if count > ceiling:
                problems.violation(
                    "ceilings",
                    f"per-{label} lint ceiling exceeded for {key}: {count} "
                    f"finding(s) against a ceiling of {ceiling}",
                )


def check_capture(
    root: Path, baseline: dict[str, Any], commit: str | None, problems: Problems
) -> None:
    recorded = baseline.get("capture")
    if not isinstance(recorded, dict):
        problems.malformed("baseline", "`capture` must be an object")
        return
    if baseline.get("normalization_version") != NORMALIZATION_VERSION:
        problems.malformed(
            "baseline",
            f"normalization_version {baseline.get('normalization_version')!r} does not "
            f"match this checker's {NORMALIZATION_VERSION}; regenerate the baseline",
        )
    if baseline.get("schema_version") != SCHEMA_VERSION:
        problems.malformed(
            "baseline", f"unsupported schema_version {baseline.get('schema_version')!r}"
        )
    # Capture facts are provenance, not gates: every later commit is meant to
    # be checked against this baseline, and a toolchain bump is expected to be
    # accompanied by a reviewed regeneration when (and only when) the census
    # actually changes.  The census itself is compared by fingerprint.
    if commit is not None and recorded.get("commit") != commit:
        print(
            f"note: commit {commit} differs from the baseline capture commit "
            f"{recorded.get('commit')}; the census is compared by fingerprint, "
            f"not by commit"
        )
    toolchain = read_toolchain(root)
    if toolchain is not None and recorded.get("toolchain") != toolchain:
        print(
            f"note: {LEAN_TOOLCHAIN.as_posix()} records {toolchain!r} but the baseline "
            f"was captured under {recorded.get('toolchain')!r}; provenance only"
        )


def check(
    root: Path,
    log_path: Path,
    baseline_path: Path,
    commit: str | None,
    expect_findings: int | None,
    expect_files: int | None,
) -> int:
    problems = Problems()
    baseline = load_json(baseline_path, baseline_path.name)
    capture = read_log(log_path)
    findings = sort_findings(capture.findings)
    census = Census(findings)
    print(census.render())

    for number, text, reason in capture.unclassified[:20]:
        problems.violation(
            "classification",
            f"unclassifiable runLinter output at log line {number} ({reason}): "
            f"{text[:120]}",
        )
    if len(capture.unclassified) > 20:
        problems.violation(
            "classification",
            f"unclassifiable runLinter output: {len(capture.unclassified)} line(s) total",
        )
    if capture.reported_findings is not None and capture.reported_findings != census.total:
        problems.malformed(
            "census",
            f"runLinter reports {capture.reported_findings} finding(s) but the parser "
            f"reconstructed {census.total}; the log grammar has drifted",
        )

    known = baseline_identities(baseline, problems)
    observed = {finding.identity: finding for finding in findings}
    new_keys = sorted(set(observed) - set(known))
    gone_keys = sorted(set(known) - set(observed))

    # Pair up unmatched fingerprints so a moved or reworded finding is named as
    # a mutation rather than as an unrelated new/resolved pair.
    by_path_free = {
        (linter, declaration, head, occurrence): key
        for key in gone_keys
        for linter, _, declaration, head, occurrence in [key]
    }
    by_head_free = {
        (linter, path, declaration, occurrence): key
        for key in gone_keys
        for linter, path, declaration, _, occurrence in [key]
    }
    consumed: set[Identity] = set()
    residual_new: list[Identity] = []
    for key in new_keys:
        linter, path, declaration, head, occurrence = key
        moved = by_path_free.get((linter, declaration, head, occurrence))
        if moved is not None and moved not in consumed and moved[1] != path:
            consumed.add(moved)
            problems.violation(
                "fingerprints",
                f"path mutation of a known fingerprint: {linter} {declaration} moved "
                f"from {moved[1]} to {path}",
            )
            continue
        reworded = by_head_free.get((linter, path, declaration, occurrence))
        if reworded is not None and reworded not in consumed and reworded[3] != head:
            consumed.add(reworded)
            problems.violation(
                "fingerprints",
                f"message mutation of a known fingerprint: {linter} {declaration} at "
                f"{path} now reads: {observed[key].message_head[:120]}",
            )
            continue
        residual_new.append(key)

    for key in residual_new:
        linter, path, declaration, _, occurrence = key
        finding = observed[key]
        problems.violation(
            "fingerprints",
            f"new lint finding that is not in the reviewed baseline: {linter} "
            f"{declaration} at {path} (occurrence {occurrence}, evidence line "
            f"{finding.line} column {finding.column}): {finding.message_head[:120]}",
        )
    gone_groups: dict[tuple[str, str], list[str]] = {}
    for key in gone_keys:
        if key in consumed:
            continue
        linter, path, declaration, _, _occurrence = key
        gone_groups.setdefault((path, linter), []).append(declaration)
    for (path, linter), declarations in sorted(gone_groups.items()):
        problems.violation(
            "fingerprints",
            f"{len(declarations)} baseline lint finding(s) no longer fire; this is an "
            f"improvement, not a regression, and it requires a reviewed baseline "
            f"reduction (--write-baseline): {linter} at {path} "
            f"({', '.join(sorted(declarations)[:5])}"
            f"{', ...' if len(declarations) > 5 else ''})",
        )

    check_ceilings(baseline, census, problems)
    check_capture(root, baseline, commit, problems)

    if expect_findings is not None and census.total != expect_findings:
        problems.malformed(
            "census", f"expected {expect_findings} finding(s), parsed {census.total}"
        )
    if expect_files is not None and census.files != expect_files:
        problems.malformed("census", f"expected {expect_files} file(s), parsed {census.files}")

    if not problems.ok:
        problems.render()
        return problems.exit_code()
    print(
        f"lint contract satisfied: {census.total} baselined finding(s) from "
        f"{len(census.by_linter)} linter(s) across {census.files} file(s), no new "
        f"fingerprints and no unreviewed improvements"
    )
    return 0


def regenerate(
    root: Path,
    log_path: Path,
    baseline_path: Path,
    commit: str | None,
    expect_findings: int | None,
    expect_files: int | None,
) -> int:
    capture = read_log(log_path)
    if capture.unclassified:
        number, text, reason = capture.unclassified[0]
        raise InputError(
            f"refusing to baseline a log with {len(capture.unclassified)} "
            f"unclassifiable line(s); first is log line {number} ({reason}): {text[:160]}"
        )
    findings = sort_findings(capture.findings)
    census = Census(findings)
    if capture.reported_findings is not None and capture.reported_findings != census.total:
        raise InputError(
            f"runLinter reports {capture.reported_findings} finding(s) but the parser "
            f"reconstructed {census.total}; refusing to baseline a drifted grammar"
        )
    if expect_findings is not None and census.total != expect_findings:
        raise InputError(f"expected {expect_findings} finding(s), parsed {census.total}")
    if expect_files is not None and census.files != expect_files:
        raise InputError(f"expected {expect_files} file(s), parsed {census.files}")
    previous = load_json(baseline_path, baseline_path.name) if baseline_path.is_file() else None
    document = build_baseline(
        root=root,
        capture=capture,
        findings=findings,
        census=census,
        commit=commit,
        previous=previous,
    )
    write_baseline(baseline_path, document)
    print(census.render())
    print(f"Wrote {baseline_path}")
    return 0


# ---------------------------------------------------------------------------
# --self-test
# ---------------------------------------------------------------------------

SELF_TEST_TOOLCHAIN = "leanprover/lean4:v4.99.0-fixture"
SELF_TEST_COMMIT = "0123456789abcdef0123456789abcdef01234567"
SELF_TEST_MATHLIB = "fedcba9876543210fedcba9876543210fedcba98"
SELF_TEST_WORKSPACE = "C:\\work\\fixture-repo\\"

# (linter, module, path, line, column, decl-as-printed, message lines)
SelfTestEntry = tuple[str, str, int, int, str, list[str]]


def self_test_findings() -> list[SelfTestEntry]:
    return [
        (
            "defLemma",
            "NumStability\\Fixture\\Alpha.lean",
            12,
            1,
            "NumStability.Fixture.alpha_bridge",
            ["is a def, should be lemma/theorem"],
        ),
        (
            "defLemma",
            "NumStability\\Fixture\\Beta.lean",
            40,
            1,
            "@NumStability.Fixture.beta_core",
            ["is a def, should be lemma/theorem"],
        ),
        (
            "docBlame",
            "NumStability\\Fixture\\Alpha.lean",
            48,
            3,
            "@NumStability.Fixture.Data.a",
            ["definition missing documentation string"],
        ),
        (
            "simpNF",
            "NumStability\\Fixture\\Beta.lean",
            264,
            1,
            "@NumStability.Fixture.split_11",
            [
                "Left-hand side simplifies from",
                "  NumStability.Fixture.split A (finSumFinEquiv (Sum.inl s))",
                "to",
                "  NumStability.Fixture.split A (Fin.castAdd r s)",
                "using",
                "  simp only [*, @finSumFinEquiv_apply_left]",
                "Try to change the left-hand side to the simplified term!",
            ],
        ),
        (
            "unusedArguments",
            "NumStability\\Fixture\\Alpha.lean",
            39,
            1,
            "@NumStability.Fixture.stable_y",
            ["argument 6 _hgamma_nonneg : 0 \u2264", "  gamma"],
        ),
    ]


def render_self_test_log(entries: Sequence[SelfTestEntry], *, total: int | None = None) -> bytes:
    out: list[str] = ["\u2714 [50/50] Built runLinter:exe (1.5s)"]
    out.append("Running linter on specified modules: [NumStability]")
    count = len(entries) if total is None else total
    out.append(
        f"-- Found {count} errors in 500 declarations (plus 300 automatically "
        f"generated ones) in NumStability with 16 linters"
    )
    notes = {
        "defLemma": ["INCORRECT DEF/LEMMA: -/"],
        "docBlame": ["DEFINITIONS ARE MISSING DOCUMENTATION STRINGS: -/"],
        "simpNF": [
            "SOME SIMP LEMMAS ARE NOT IN SIMP-NORMAL FORM.",
            "Please change the lemma to make sure their left-hand sides are in simp normal form. -/",
        ],
        "unusedArguments": ["UNUSED ARGUMENTS. -/"],
    }
    linters = sorted({entry[0] for entry in entries})
    for linter in linters:
        out.append("")
        out.append(f"/- The `{linter}` linter reports:")
        out.extend(notes.get(linter, ["FIXTURE NOTE. -/"]))
        modules: dict[str, list[SelfTestEntry]] = {}
        for entry in entries:
            if entry[0] == linter:
                modules.setdefault(entry[1], []).append(entry)
        first = True
        for path, group in modules.items():
            if not first:
                out.append("")
            first = False
            out.append(f"-- {module_name(path.replace(chr(92), '/'))}")
            for _, _, line, column, decl, message in group:
                out.append(
                    f"{SELF_TEST_WORKSPACE}{path}:{line}:{column}: error: {decl} {message[0]}"
                )
                out.extend(message[1:])
    out.append("")
    return "\r\n".join(out).encode("utf-8")


def build_self_test_root(root: Path) -> None:
    (root / "docs" / "architecture").mkdir(parents=True, exist_ok=True)
    (root / LEAN_TOOLCHAIN).write_text(
        SELF_TEST_TOOLCHAIN + "\n", encoding="utf-8", newline="\n"
    )
    (root / LAKE_MANIFEST).write_text(
        json.dumps(
            {"version": "1.1.0", "packages": [{"name": "mathlib", "rev": SELF_TEST_MATHLIB}]},
            indent=1,
        )
        + "\n",
        encoding="utf-8",
        newline="\n",
    )


def run_checker(argv: Sequence[str]) -> tuple[int, str]:
    buffer = io.StringIO()
    with contextlib.redirect_stdout(buffer), contextlib.redirect_stderr(buffer):
        code = main(list(argv))
    return code, buffer.getvalue()


def expect_failure(argv: Sequence[str], needle: str, label: str, *, code_expected: int | None = None) -> bool:
    code, output = run_checker(argv)
    if code == 0 or needle not in output or (code_expected is not None and code != code_expected):
        print(
            f"self-test failure: {label} was not rejected as expected (exit {code})\n{output}",
            file=sys.stderr,
        )
        return False
    return True


def run_self_test() -> int:
    accepted: list[str] = []
    cases: list[str] = []
    entries = self_test_findings()
    with tempfile.TemporaryDirectory(prefix="numstability-lint-selftest-") as tmp:
        base = Path(tmp)
        root = base / "repo"
        build_self_test_root(root)
        log_path = base / "fixture.log"
        log_path.write_bytes(render_self_test_log(entries))
        baseline_path = base / "lint.json"

        common = ["--root", str(root), "--log", str(log_path), "--baseline", str(baseline_path)]
        write = common + ["--write-baseline", "--commit", SELF_TEST_COMMIT]
        code, output = run_checker(
            write + ["--expect-findings", str(len(entries)), "--expect-files", "2"]
        )
        if code != 0:
            print(f"self-test failure: baseline generation failed\n{output}", file=sys.stderr)
            return 1
        document = json.loads(baseline_path.read_text(encoding="utf-8"))
        records = document["findings"]
        if len(records) != len(entries):
            print("self-test failure: fixture baseline lost findings", file=sys.stderr)
            return 1
        by_decl = {record["declaration"]: record for record in records}
        if "NumStability.Fixture.beta_core" not in by_decl:
            print("self-test failure: `@` prefix was not stripped from a declaration", file=sys.stderr)
            return 1
        if by_decl["NumStability.Fixture.stable_y"]["message_head"] != (
            "argument 6 _hgamma_nonneg : 0 \u2264 gamma"
        ):
            print("self-test failure: wrapped message head was not joined", file=sys.stderr)
            return 1
        if by_decl["NumStability.Fixture.split_11"]["message_head"] != (
            "Left-hand side simplifies from NumStability.Fixture.split A (finSumFinEquiv (Sum.inl s))"
        ):
            print("self-test failure: simpNF head did not stop at the structural line", file=sys.stderr)
            return 1
        if any(record["path"].count("\\") for record in records) or not all(
            record["path"].startswith("NumStability/") for record in records
        ):
            print("self-test failure: Windows paths were not made repo-relative", file=sys.stderr)
            return 1
        if any(record["owner_family"] != record["linter"] for record in records):
            print("self-test failure: owner_family must equal the linter", file=sys.stderr)
            return 1
        if document["ceilings"]["by_linter"] != {
            "defLemma": 2,
            "docBlame": 1,
            "simpNF": 1,
            "unusedArguments": 1,
        }:
            print("self-test failure: per-linter ceilings are wrong", file=sys.stderr)
            return 1
        if document["capture"]["reported"]["findings"] != len(entries):
            print("self-test failure: runLinter summary was not recorded", file=sys.stderr)
            return 1
        pristine = baseline_path.read_text(encoding="utf-8")

        code, output = run_checker(common + ["--check", "--commit", SELF_TEST_COMMIT])
        if code != 0:
            print(f"self-test failure: valid fixture was rejected\n{output}", file=sys.stderr)
            return 1
        accepted.append("valid fixture accepted")

        # Byte-for-byte reproducibility of the review-only regeneration.
        run_checker(write)
        if baseline_path.read_text(encoding="utf-8") != pristine:
            print("self-test failure: baseline regeneration is not reproducible", file=sys.stderr)
            return 1
        accepted.append("regeneration byte-reproducible")

        def restore() -> None:
            baseline_path.write_text(pristine, encoding="utf-8", newline="\n")
            log_path.write_bytes(render_self_test_log(entries))

        # New fingerprint in a file with no reviewed allowance.
        extra = entries + [
            (
                "docBlame",
                "NumStability\\Fixture\\Gamma.lean",
                7,
                1,
                "NumStability.Fixture.gamma",
                ["definition missing documentation string"],
            )
        ]
        log_path.write_bytes(render_self_test_log(extra))
        if not expect_failure(
            common + ["--check"], "new lint finding that is not in the reviewed baseline", "new fingerprint"
        ):
            return 1
        cases.append("new fingerprint")
        if not expect_failure(
            common + ["--check"], "file has no reviewed lint allowance", "zero-finding ceiling"
        ):
            return 1
        cases.append("zero-finding ceiling for a new file")
        restore()

        # Disappeared fingerprint: an improvement that must be reviewed down.
        log_path.write_bytes(render_self_test_log(entries[:-1]))
        if not expect_failure(
            common + ["--check"], "this is an improvement, not a regression", "disappeared fingerprint"
        ):
            return 1
        cases.append("disappeared fingerprint (improvement)")
        restore()

        # Ceiling breaches with an otherwise identical census: lower each table.
        mutated = json.loads(pristine)
        mutated["ceilings"]["global"] -= 1
        mutated["ceilings"]["by_linter"]["defLemma"] -= 1
        mutated["ceilings"]["by_file"]["NumStability/Fixture/Alpha.lean"] -= 1
        write_baseline(baseline_path, mutated)
        for needle, label in (
            ("global lint ceiling exceeded", "global ceiling"),
            ("per-linter lint ceiling exceeded", "per-linter ceiling"),
            ("per-file lint ceiling exceeded", "per-file ceiling"),
        ):
            if not expect_failure(common + ["--check"], needle, label):
                return 1
            cases.append(label)
        restore()

        # Malformed disposition is a format error (exit 2), not a violation.
        mutated = json.loads(pristine)
        mutated["findings"][0]["disposition"] = "ignored_forever"
        write_baseline(baseline_path, mutated)
        if not expect_failure(
            common + ["--check"], "disposition must be one of", "malformed disposition", code_expected=2
        ):
            return 1
        cases.append("malformed disposition")
        restore()

        # Path mutation: the same declaration reported from another file.
        mutated = json.loads(pristine)
        for entry in mutated["findings"]:
            if entry["linter"] == "docBlame":
                entry["path"] = "NumStability/Fixture/Gamma.lean"
                entry["module"] = "NumStability.Fixture.Gamma"
        mutated["ceilings"]["by_file"]["NumStability/Fixture/Gamma.lean"] = 1
        mutated["ceilings"]["by_file"]["NumStability/Fixture/Alpha.lean"] -= 1
        write_baseline(baseline_path, mutated)
        if not expect_failure(
            common + ["--check"], "path mutation of a known fingerprint", "path mutation"
        ):
            return 1
        cases.append("path mutation")
        restore()

        # Unknown linter.
        unknown = entries + [
            (
                "brandNewLinter",
                "NumStability\\Fixture\\Alpha.lean",
                3,
                1,
                "NumStability.Fixture.alpha_bridge",
                ["something new"],
            )
        ]
        log_path.write_bytes(render_self_test_log(unknown))
        if not expect_failure(
            common + ["--check"], "unknown linter `brandNewLinter`", "unknown linter"
        ):
            return 1
        cases.append("unknown linter")
        restore()

        # Parser/summary disagreement is a grammar drift, refused as malformed.
        log_path.write_bytes(render_self_test_log(entries, total=len(entries) + 1))
        if not expect_failure(
            common + ["--check"], "the log grammar has drifted", "summary disagreement", code_expected=2
        ):
            return 1
        cases.append("summary/parser disagreement")
        restore()

        # A differing capture commit is provenance drift, NOT a violation.
        code, output = run_checker(common + ["--check", "--commit", "f" * 40])
        if code != 0 or "differs from the baseline capture commit" not in output:
            print(
                f"self-test failure: a differing commit must be accepted with a "
                f"provenance note (exit {code})\n{output}",
                file=sys.stderr,
            )
            return 1
        accepted.append("later commit accepted as provenance drift")

        # Reviewed dispositions survive a regeneration; debt is re-derived.
        mutated = json.loads(pristine)
        mutated["findings"][0]["disposition"] = REVIEWED_UPSTREAM_EXCEPTION
        mutated["findings"][0]["rationale"] = "fixture reviewed rationale"
        write_baseline(baseline_path, mutated)
        run_checker(write)
        regenerated = json.loads(baseline_path.read_text(encoding="utf-8"))
        if regenerated["findings"][0]["disposition"] != REVIEWED_UPSTREAM_EXCEPTION or (
            regenerated["findings"][0]["rationale"] != "fixture reviewed rationale"
        ):
            print("self-test failure: reviewed disposition was reset by regeneration", file=sys.stderr)
            return 1
        accepted.append("reviewed disposition carried through regeneration")
        restore()

        # Stale normalization version.
        mutated = json.loads(pristine)
        mutated["normalization_version"] = NORMALIZATION_VERSION + 1
        write_baseline(baseline_path, mutated)
        if not expect_failure(
            common + ["--check"], "normalization_version", "stale normalization version", code_expected=2
        ):
            return 1
        cases.append("stale normalization version")
        restore()

        code, output = run_checker(common + ["--check"])
        if code != 0:
            print(
                f"self-test failure: fixture was not restored to a passing state\n{output}",
                file=sys.stderr,
            )
            return 1

    print(
        "lint contract self-test passed: "
        + "; ".join(accepted)
        + "; rejected: "
        + ", ".join(cases)
    )
    return 0


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--log", type=Path, help="captured runLinter / `lake lint` log to parse")
    parser.add_argument(
        "--baseline",
        type=Path,
        default=None,
        help=f"reviewed baseline document (default {DEFAULT_BASELINE.as_posix()})",
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=ROOT,
        help="repository root whose lean-toolchain and lake-manifest supply provenance",
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="verify the log against the baseline")
    mode.add_argument(
        "--write-baseline",
        action="store_true",
        help="review-only operation: regenerate the baseline from the log",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="exercise the contract against synthetic fixtures and exit",
    )
    parser.add_argument(
        "--commit",
        default=None,
        help="commit sha the log was captured at (provenance only, never a gate)",
    )
    parser.add_argument(
        "--expect-findings",
        type=int,
        default=None,
        help="assert the parsed finding total (reviewed census guard)",
    )
    parser.add_argument(
        "--expect-files",
        type=int,
        default=None,
        help="assert the parsed distinct-file total (reviewed census guard)",
    )
    args = parser.parse_args(argv)

    for stream in (sys.stdout, sys.stderr):
        reconfigure = getattr(stream, "reconfigure", None)
        if reconfigure is not None:
            try:
                reconfigure(encoding="utf-8", errors="replace")
            except (ValueError, OSError):
                pass

    if args.self_test:
        return run_self_test()

    root: Path = args.root.resolve()
    baseline_path: Path = args.baseline or (root / DEFAULT_BASELINE)

    try:
        if args.commit is not None and not SHA1_RE.fullmatch(args.commit):
            raise InputError(f"--commit is not a 40-hex sha: {args.commit}")
        if args.log is None:
            raise InputError("--log is required unless --self-test is given")
        if not args.log.is_file():
            raise InputError(f"log is not a file: {args.log}")
        if args.write_baseline:
            return regenerate(
                root=root,
                log_path=args.log,
                baseline_path=baseline_path,
                commit=args.commit,
                expect_findings=args.expect_findings,
                expect_files=args.expect_files,
            )
        if not baseline_path.is_file():
            raise InputError(f"baseline is not a file: {baseline_path}")
        return check(
            root=root,
            log_path=args.log,
            baseline_path=baseline_path,
            commit=args.commit,
            expect_findings=args.expect_findings,
            expect_files=args.expect_files,
        )
    except InputError as error:
        print(f"error: malformed input: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
