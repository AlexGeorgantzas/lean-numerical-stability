#!/usr/bin/env python3
"""Enforce a machine-readable Lean diagnostic baseline with a review-only ratchet.

The contract is deliberately independent of Lean: it consumes a captured
build/test log, normalizes it, reconstructs every diagnostic as a
line-independent fingerprint, and compares that census against a reviewed
baseline document.  New diagnostics fail; resolved diagnostics also fail, so
the ceiling can only move down through review.  Only the Python standard
library is used.

Identity never involves the reported line or column.  A diagnostic is
identified by

    (repo-relative path, kind, normalized message, source-anchor hash,
     occurrence index within that group)

where the source anchor is a hash of a small whitespace-normalized window of
the referenced source file.  Lines and columns are recorded as evidence only.
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
from datetime import date, datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Sequence


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_BASELINE = Path("docs/architecture/warnings.json")
DEFAULT_WORKFLOW = ".github/workflows/lean_action_ci.yml"
TIERS = Path("docs/architecture/tiers.json")
LEAN_TOOLCHAIN = Path("lean-toolchain")
LAKE_MANIFEST = Path("lake-manifest.json")

SCHEMA_VERSION = 1

# Bump whenever the normalization or fingerprint rules below change; a baseline
# written under an older normalization is refused rather than misread.
NORMALIZATION_VERSION = 1

# Lean source trees whose diagnostics this contract governs.  Anything outside
# them (Mathlib, toolchain sources) is not fingerprinted.
SOURCE_ROOTS = ("NumStability", "NumStabilityTest")

# The anchor hashes the whitespace-normalized source lines in the closed
# interval [line - 2, line + 2] (clamped to the file).  A five-line window is
# wide enough to pin the diagnostic to a recognisable piece of syntax and
# narrow enough that an unrelated edit elsewhere in the same file leaves it
# untouched.
ANCHOR_WINDOW_HALF = 2

# ---------------------------------------------------------------------------
# Normalization
# ---------------------------------------------------------------------------

# CSI/OSC escape sequences emitted by Lake's coloured output.
ANSI_RE = re.compile("\x1b\\[[0-9;?]*[ -/]*[@-~]|\x1b\\][^\x07\x1b]*(?:\x07|\x1b\\\\)")
# "2026-08-31T03:53:01.9589741Z " prefixes added by the GitHub Actions log API.
GH_TIMESTAMP_RE = re.compile(r"^\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d(?:\.\d+)?Z ")
# The hosted runner checks a repository out at /home/runner/work/<repo>/<repo>/.
RUNNER_WORKSPACE_RE = re.compile(
    r"(?:[A-Za-z]:)?(?:/[^/\s:]+)*/work/(?P<repo>[^/\s:]+)/(?P=repo)/"
)
ABSOLUTE_SOURCE_RE = re.compile(
    r"^(?:[A-Za-z]:)?[/\\][^\s]*?[/\\](?=(?:" + "|".join(SOURCE_ROOTS) + r")[/\\])"
)

DIAGNOSTIC_HEAD_RE = re.compile(
    r"^warning: (?P<path>[^\s:]+):(?P<line>\d+):(?P<column>\d+): (?P<rest>.*)$"
)
OTHER_HEAD_RE = re.compile(r"^(?:warning|error|info): ")
# Lake progress markers: "✔ [12/34] Built X", "⚠ [12/34] Replayed X", "[12/34] ...".
LAKE_PROGRESS_RE = re.compile(r"^(?:[^\s\[]{1,3}\s*)?\[\d+/\d+\]")
RECORD_MARKER_RE = re.compile(r"^(?:##\[|\[command\]|\$\{)")
GROUP_RE = re.compile(r"^##\[group\](?P<label>.*)$")
LINTER_NOTE_RE = re.compile(
    r"^Note: This linter can be disabled with "
    r"`set_option (?P<option>[A-Za-z0-9_.]+) false`"
)
GIT_HEAD_COMMAND_RE = re.compile(r"^\[command\]\S*git log -1 --format=%H$")
SHA1_RE = re.compile(r"^[0-9a-f]{40}$")
LEAN_VERSION_RE = re.compile(
    r"^Lean \(version (?P<version>[^,]+), (?P<platform>[^,]+), commit "
)

# ---------------------------------------------------------------------------
# Kind classification
# ---------------------------------------------------------------------------

# Rule, in order:
#   1. If the diagnostic body carries Lean's own escape hatch note
#      "Note: This linter can be disabled with `set_option <option> false`",
#      the kind IS that option (`linter.deprecated` is folded into
#      "deprecation" so the deprecation surface has a single kind).
#   2. Otherwise, a message containing "has been deprecated" is a deprecation
#      warning (Lean emits these without a linter note).
#   3. Otherwise, a message of the shape "Try this: intro ..." is the
#      intro/binder suggestion emitted when a binder list can be spelled out.
#   4. Anything else is unclassifiable and fails loudly; the classification
#      table must be extended by review rather than silently widened.
DEPRECATION_KIND = "deprecation"
INTRO_BINDER_KIND = "intro/binder suggestion"
DEPRECATION_OPTIONS = {"deprecated", "linter.deprecated"}
INTRO_BINDER_RE = re.compile(r"^Try this: intro\b")
DEPRECATION_MARKER = "has been deprecated"

KNOWN_KINDS = (
    DEPRECATION_KIND,
    INTRO_BINDER_KIND,
    "linter.unnecessarySeqFocus",
    "linter.unnecessarySimpa",
    "linter.unreachableTactic",
    "linter.unusedSimpArgs",
    "linter.unusedTactic",
    "linter.unusedVariables",
)

# Owner batches partition the *files*, first matching class wins, so no file is
# split across two batches and no batch can be worked without owning the file.
OWNER_BATCH_CLASSES: tuple[tuple[str, tuple[str, ...]], ...] = (
    ("B1", (DEPRECATION_KIND,)),
    ("B2", ("linter.unusedTactic", "linter.unreachableTactic")),
    ("B3", ("linter.unusedVariables", INTRO_BINDER_KIND)),
    ("B4", ("linter.unnecessarySimpa",)),
    ("B5", ("linter.unnecessarySeqFocus",)),
    ("B6", ("linter.unusedSimpArgs",)),
)
FALLBACK_OWNER_BATCH = "B6"

KIND_RATIONALE: dict[str, str] = {
    DEPRECATION_KIND: (
        "Pre-existing use of upstream declarations that Mathlib has deprecated; "
        "retargeting them is a mechanical but cross-cutting rename."
    ),
    INTRO_BINDER_KIND: (
        "Pre-existing binder list that Lean can spell out; rewriting it touches "
        "proof text without changing the statement."
    ),
    "linter.unnecessarySeqFocus": (
        "Pre-existing `tac1 <;> tac2` where `(tac1; tac2)` suffices; the rewrite "
        "is local but must be re-elaborated per proof."
    ),
    "linter.unnecessarySimpa": (
        "Pre-existing `simpa` that `simp` closes; collapsing it is safe but has "
        "to be checked proof by proof."
    ),
    "linter.unreachableTactic": (
        "Pre-existing unreachable tactic left behind by proof refactoring."
    ),
    "linter.unusedSimpArgs": (
        "Pre-existing redundant simp argument; dropping it is safe but the "
        "surviving call must still close the goal."
    ),
    "linter.unusedTactic": (
        "Pre-existing no-op tactic step left behind by proof refactoring."
    ),
    "linter.unusedVariables": (
        "Pre-existing unused hypothesis or binder name; renaming to `_` changes "
        "proof text that downstream proofs may reference."
    ),
}

KIND_RECONSIDERATION_TRIGGER: dict[str, str] = {
    DEPRECATION_KIND: (
        "Reconsider on the next Mathlib bump, or when the deprecated upstream "
        "declaration is removed and the build breaks."
    ),
    INTRO_BINDER_KIND: (
        "Reconsider when the surrounding proof is next edited for any reason."
    ),
    "linter.unnecessarySeqFocus": (
        "Reconsider when the owning module is next edited, or on a toolchain "
        "bump that changes the linter's verdict."
    ),
    "linter.unnecessarySimpa": (
        "Reconsider when the owning module is next edited, or on a toolchain "
        "bump that changes `simp`'s behaviour."
    ),
    "linter.unreachableTactic": (
        "Reconsider when the owning proof is next edited."
    ),
    "linter.unusedSimpArgs": (
        "Reconsider when the owning module is next edited, or on a toolchain "
        "bump that changes the simp set."
    ),
    "linter.unusedTactic": (
        "Reconsider when the owning proof is next edited."
    ),
    "linter.unusedVariables": (
        "Reconsider when the owning declaration's signature is next edited."
    ),
}

SUPPRESSION_RE = re.compile(
    r"set_option\s+(?P<option>linter\.[A-Za-z0-9_.]+|deprecated)\s+false\b"
)

BASELINE_DEBT = "baseline_debt"
# A record is either unreviewed debt or one the reviewer keeps deliberately.
# Both are enforced identically -- the disposition explains why a record is
# here, it never relaxes the contract.
REVIEWED_COMPATIBILITY_EXCEPTION = "reviewed_compatibility_exception"
REVIEWED_DEFERRED_MIGRATION = "reviewed_deferred_migration"
REVIEWED_UPSTREAM_EXCEPTION = "reviewed_upstream_exception"
DISPOSITIONS = frozenset(
    {
        BASELINE_DEBT,
        REVIEWED_COMPATIBILITY_EXCEPTION,
        REVIEWED_DEFERRED_MIGRATION,
        REVIEWED_UPSTREAM_EXCEPTION,
    }
)
ACCEPTED_BASELINE = "accepted_baseline"
PRIMARY_REVIEWER = "primary-human"

EXCEPTION_SCOPES = ("file", "kind", "role")


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


def parse_date(value: str) -> date | None:
    try:
        return date.fromisoformat(value[:10])
    except ValueError:
        return None


# ---------------------------------------------------------------------------
# Log normalization and diagnostic reconstruction
# ---------------------------------------------------------------------------


class Diagnostic:
    __slots__ = (
        "path",
        "line",
        "column",
        "message",
        "kind",
        "anchor_sha256",
        "occurrence",
        "pass_index",
    )

    def __init__(
        self,
        path: str,
        line: int,
        column: int,
        message: str,
        kind: str | None,
        anchor_sha256: str,
        pass_index: int,
    ) -> None:
        self.path = path
        self.line = line
        self.column = column
        self.message = message
        self.kind = kind
        self.anchor_sha256 = anchor_sha256
        self.occurrence = 0
        self.pass_index = pass_index

    @property
    def message_sha256(self) -> str:
        return sha256_text(self.message)

    @property
    def identity(self) -> tuple[str, str, str, str, int]:
        return (
            self.path,
            self.kind or "",
            self.message_sha256,
            self.anchor_sha256,
            self.occurrence,
        )


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
        lines.append(line)
    return lines


def normalize_source_path(value: str) -> str:
    value = ABSOLUTE_SOURCE_RE.sub("", value)
    return value.replace("\\", "/")


def is_block_break(line: str) -> bool:
    """True when `line` starts a new log record rather than continuing one."""

    return bool(
        OTHER_HEAD_RE.match(line)
        or LAKE_PROGRESS_RE.match(line)
        or RECORD_MARKER_RE.match(line)
    )


def classify(message: str, option: str | None) -> str | None:
    if option is not None:
        if option in DEPRECATION_OPTIONS:
            return DEPRECATION_KIND
        return option
    if DEPRECATION_MARKER in message:
        return DEPRECATION_KIND
    if INTRO_BINDER_RE.match(message):
        return INTRO_BINDER_KIND
    return None


class AnchorReader:
    """Hash a small whitespace-normalized window of a worktree source file."""

    def __init__(self, root: Path) -> None:
        self.root = root
        self._cache: dict[str, list[str] | None] = {}
        self.missing: set[str] = set()

    def lines(self, path: str) -> list[str] | None:
        if path not in self._cache:
            candidate = self.root / path
            if candidate.is_file():
                self._cache[path] = candidate.read_text(
                    encoding="utf-8-sig", errors="replace"
                ).splitlines()
            else:
                self._cache[path] = None
                self.missing.add(path)
        return self._cache[path]

    def anchor(self, path: str, line: int) -> str:
        source = self.lines(path)
        if source is None:
            return sha256_text("")
        if not source:
            return sha256_text("")
        centre = min(max(line, 1), len(source))
        low = max(1, centre - ANCHOR_WINDOW_HALF)
        high = min(len(source), centre + ANCHOR_WINDOW_HALF)
        window = "\n".join(
            " ".join(source[index - 1].split()) for index in range(low, high + 1)
        )
        return sha256_text(window)


class LogCapture:
    """Everything a baseline needs from one captured log."""

    def __init__(self) -> None:
        self.commit: str | None = None
        self.toolchain: str | None = None
        self.platform: str | None = None
        self.captured_at: str | None = None
        self.pass_labels: dict[int, str] = {}
        self.diagnostics: list[Diagnostic] = []
        self.unclassified: list[Diagnostic] = []

    @property
    def command(self) -> str:
        labels = [
            self.pass_labels.get(index, f"pass {index}")
            for index in sorted({diag.pass_index for diag in self.diagnostics})
        ]
        return "; ".join(labels) if labels else ""


def read_log(path: Path, anchors: AnchorReader) -> LogCapture:
    try:
        raw = path.read_bytes()
    except OSError as error:
        raise InputError(f"cannot read log {path}: {error}") from error

    capture = LogCapture()
    original_first_timestamp: str | None = None
    with path.open("rb") as handle:
        for chunk in handle:
            text = chunk.decode("utf-8", errors="replace").lstrip("\ufeff")
            match = re.match(r"^(\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d(?:\.\d+)?Z) ", text)
            if match:
                original_first_timestamp = match.group(1)
            break
    capture.captured_at = original_first_timestamp

    lines = normalize_log_lines(raw)
    pass_index = -1
    expect_commit = False
    for index, line in enumerate(lines):
        group = GROUP_RE.match(line)
        if group:
            pass_index += 1
            capture.pass_labels[pass_index] = group.group("label").strip()
        if expect_commit:
            expect_commit = False
            if SHA1_RE.fullmatch(line.strip()) and capture.commit is None:
                capture.commit = line.strip()
        if GIT_HEAD_COMMAND_RE.match(line):
            expect_commit = True
        version = LEAN_VERSION_RE.match(line)
        if version and capture.toolchain is None:
            capture.toolchain = f"leanprover/lean4:v{version.group('version')}"
            capture.platform = version.group("platform")
        if not line.startswith("warning: "):
            continue
        head = DIAGNOSTIC_HEAD_RE.match(line)
        if head is None:
            continue
        source_path = normalize_source_path(head.group("path"))
        if not source_path.startswith(tuple(root + "/" for root in SOURCE_ROOTS)) and (
            module_name(source_path) not in SOURCE_ROOTS
        ):
            continue
        body: list[str] = []
        cursor = index + 1
        while cursor < len(lines) and not is_block_break(lines[cursor]):
            body.append(lines[cursor])
            cursor += 1
        option: str | None = None
        for entry in body:
            note = LINTER_NOTE_RE.match(entry)
            if note:
                option = note.group("option")
        pieces = [head.group("rest")] + body
        message = " ".join(
            " ".join(piece.split()) for piece in pieces if piece.split()
        )
        kind = classify(message, option)
        diagnostic = Diagnostic(
            path=source_path,
            line=int(head.group("line")),
            column=int(head.group("column")),
            message=message,
            kind=kind,
            anchor_sha256=anchors.anchor(source_path, int(head.group("line"))),
            pass_index=max(pass_index, 0),
        )
        if kind is None:
            capture.unclassified.append(diagnostic)
        else:
            capture.diagnostics.append(diagnostic)

    assign_occurrences(capture.diagnostics)
    return capture


def assign_occurrences(diagnostics: Sequence[Diagnostic]) -> None:
    """Number repeats inside each (pass, path, kind, message, anchor) group.

    The same libraries are elaborated once per workflow step, so one physical
    diagnostic is printed once per step.  Occurrence indices are therefore
    assigned per elaboration pass (delimited by the log's `##[group]` records)
    and the resulting fingerprints are unioned across passes; a log with no
    group records is treated as a single pass.
    """

    counters: dict[tuple[int, str, str, str, str], int] = {}
    for diagnostic in diagnostics:
        key = (
            diagnostic.pass_index,
            diagnostic.path,
            diagnostic.kind or "",
            diagnostic.message_sha256,
            diagnostic.anchor_sha256,
        )
        diagnostic.occurrence = counters.get(key, 0)
        counters[key] = diagnostic.occurrence + 1


def deduplicate(diagnostics: Sequence[Diagnostic]) -> list[Diagnostic]:
    """One record per identity, keeping the first pass's evidence."""

    seen: dict[tuple[str, str, str, str, int], Diagnostic] = {}
    for diagnostic in diagnostics:
        seen.setdefault(diagnostic.identity, diagnostic)
    return sorted(
        seen.values(),
        key=lambda item: (
            item.path,
            item.kind or "",
            item.message_sha256,
            item.anchor_sha256,
            item.occurrence,
        ),
    )


# ---------------------------------------------------------------------------
# Roles and owner batches
# ---------------------------------------------------------------------------


def tier_lookup(root: Path) -> tuple[dict[str, str], list[tuple[str, str]]]:
    """Read tiers.json the way check_layout.py does: exact map, then prefixes."""

    manifest = load_json(root / TIERS, TIERS.as_posix())
    if manifest.get("schema_version") != 1:
        raise InputError("unsupported tier manifest schema")
    exact = manifest.get("exact")
    prefixes = manifest.get("prefixes")
    tiers = manifest.get("tiers")
    if not isinstance(exact, dict) or not isinstance(prefixes, list) or not isinstance(
        tiers, list
    ):
        raise InputError("invalid tier manifest structure")
    allowed = set(tiers)
    parsed: list[tuple[str, str]] = []
    for rule in prefixes:
        if not isinstance(rule, dict):
            raise InputError("invalid tier prefix rule")
        prefix, tier = rule.get("prefix"), rule.get("tier")
        if not isinstance(prefix, str) or tier not in allowed:
            raise InputError(f"invalid tier prefix rule: {rule!r}")
        parsed.append((prefix.rstrip("."), tier))
    parsed.sort(key=lambda item: (-len(item[0]), item[0]))
    return {name: tier for name, tier in exact.items() if isinstance(tier, str)}, parsed


def role_for(module: str, exact: dict[str, str], prefixes: list[tuple[str, str]]) -> str:
    if module in exact:
        return exact[module]
    for prefix, tier in prefixes:
        if module == prefix or module.startswith(prefix + "."):
            return tier
    if module == "NumStabilityTest" or module.startswith("NumStabilityTest."):
        return "test"
    return "unclassified"


def owner_batches(kinds_by_file: dict[str, set[str]]) -> dict[str, str]:
    batches: dict[str, str] = {}
    for path, kinds in kinds_by_file.items():
        batches[path] = FALLBACK_OWNER_BATCH
        for batch, members in OWNER_BATCH_CLASSES:
            if kinds & set(members):
                batches[path] = batch
                break
    return batches


# ---------------------------------------------------------------------------
# Suppression manifest
# ---------------------------------------------------------------------------


class Suppression:
    __slots__ = ("path", "line", "option", "anchor_sha256", "occurrence", "evidence")

    def __init__(
        self, path: str, line: int, option: str, anchor_sha256: str, evidence: str
    ) -> None:
        self.path = path
        self.line = line
        self.option = option
        self.anchor_sha256 = anchor_sha256
        self.occurrence = 0
        self.evidence = evidence

    @property
    def identity(self) -> tuple[str, str, str, int]:
        return (self.path, self.option, self.anchor_sha256, self.occurrence)


def lean_sources(root: Path) -> list[Path]:
    paths: list[Path] = []
    for name in SOURCE_ROOTS:
        entry = root / f"{name}.lean"
        if entry.is_file():
            paths.append(entry)
        directory = root / name
        if directory.is_dir():
            paths.extend(directory.rglob("*.lean"))
    return sorted(paths)


def scan_suppressions(root: Path, anchors: AnchorReader) -> list[Suppression]:
    found: list[Suppression] = []
    for path in lean_sources(root):
        relative = path.relative_to(root).as_posix()
        text = path.read_text(encoding="utf-8-sig", errors="replace")
        for number, line in enumerate(text.splitlines(), start=1):
            for match in SUPPRESSION_RE.finditer(line):
                found.append(
                    Suppression(
                        path=relative,
                        line=number,
                        option=match.group("option"),
                        anchor_sha256=anchors.anchor(relative, number),
                        evidence=" ".join(line.split()),
                    )
                )
    counters: dict[tuple[str, str, str], int] = {}
    for suppression in found:
        key = (suppression.path, suppression.option, suppression.anchor_sha256)
        suppression.occurrence = counters.get(key, 0)
        counters[key] = suppression.occurrence + 1
    return sorted(found, key=lambda item: item.identity)


# ---------------------------------------------------------------------------
# Census and baseline document
# ---------------------------------------------------------------------------


class Census:
    def __init__(self, diagnostics: Sequence[Diagnostic], root: Path) -> None:
        exact, prefixes = tier_lookup(root)
        self.diagnostics = list(diagnostics)
        self.role: dict[str, str] = {}
        kinds_by_file: dict[str, set[str]] = {}
        for diagnostic in self.diagnostics:
            module = module_name(diagnostic.path)
            self.role[diagnostic.path] = role_for(module, exact, prefixes)
            kinds_by_file.setdefault(diagnostic.path, set()).add(diagnostic.kind or "")
        self.owner_batch = owner_batches(kinds_by_file)
        self.by_kind: dict[str, int] = {}
        self.by_role: dict[str, int] = {}
        self.by_file: dict[str, int] = {}
        self.files_by_kind: dict[str, set[str]] = {}
        for diagnostic in self.diagnostics:
            kind = diagnostic.kind or ""
            self.by_kind[kind] = self.by_kind.get(kind, 0) + 1
            self.files_by_kind.setdefault(kind, set()).add(diagnostic.path)
            role = self.role[diagnostic.path]
            self.by_role[role] = self.by_role.get(role, 0) + 1
            self.by_file[diagnostic.path] = self.by_file.get(diagnostic.path, 0) + 1

    @property
    def total(self) -> int:
        return len(self.diagnostics)

    @property
    def files(self) -> int:
        return len(self.by_file)

    def render(self) -> str:
        lines = [f"diagnostics: {self.total}", f"files: {self.files}"]
        for kind in sorted(self.by_kind):
            lines.append(
                f"  {kind}: {self.by_kind[kind]} diagnostic(s) / "
                f"{len(self.files_by_kind[kind])} file(s)"
            )
        for role in sorted(self.by_role):
            lines.append(f"  role {role}: {self.by_role[role]} diagnostic(s)")
        return "\n".join(lines)


# Records the reviewer keeps deliberately, rather than as unreviewed debt. The
# table is consulted by --write-baseline so regeneration stays deterministic:
# a reviewed disposition survives a re-capture instead of resetting to debt.
# Vendored upstream sources carry another project's copyright and are adapted
# from a pinned commit, so their diagnostics are retained rather than fixed:
# editing them would diverge the copy from the source it is adapted from and
# make a future re-sync harder to verify. The reviewed CI-02 packet designates
# these exact records as retained exceptions to reconsider on an upstream
# revision, not as debt to clear.
_UPSTREAM_VENDORED = {
    "disposition": REVIEWED_UPSTREAM_EXCEPTION,
    "rationale": (
        "Vendored upstream source adapted from mathlib4 PR #28013 at a pinned "
        "commit, retaining the original Apache-2.0 notice and authorship. "
        "Style edits here would diverge the copy from its upstream original "
        "and complicate re-synchronisation, so the diagnostic is retained."
    ),
    "expiry_release": "next upstream re-synchronisation",
    "reconsideration_trigger": (
        "Reconsider when the vendored file is re-synchronised with a newer "
        "upstream revision, at which point the upstream text decides."
    ),
}

REVIEWED_DISPOSITIONS: dict[tuple[str, str], dict[str, str]] = {
    (
        "NumStability/Upstream/Lindemann/Basic.lean",
        "linter.unnecessarySeqFocus",
    ): _UPSTREAM_VENDORED,
    (
        "NumStability/Upstream/Lindemann/Basic.lean",
        "linter.unusedSimpArgs",
    ): _UPSTREAM_VENDORED,
    (
        "NumStability/Upstream/Lindemann/MonoidAlgebraCompat.lean",
        "linter.unusedSimpArgs",
    ): _UPSTREAM_VENDORED,
    (
        "NumStabilityTest/Reorganization/R06/OldOnly/"
        "NumStability_Source_Higham_Chapter09_Problems.lean",
        "deprecation",
    ): {
        "disposition": "reviewed_compatibility_exception",
        "rationale": (
            "This old-only R06 test exists to exercise the historical "
            "declaration surface, and the deprecated constructor index is part "
            "of that surface. Rewriting the call would delete the coverage the "
            "test was written to provide."
        ),
        "expiry_release": "alias-removal release",
        "reconsideration_trigger": (
            "Reconsider when the deprecated alias is removed upstream, which "
            "makes the historical surface unavailable and the test obsolete."
        ),
    },
    (
        "NumStabilityTest/Reorganization/R06/OldOnly/"
        "NumStability_Source_Higham_Chapter11_Section01_PartialPivoting.lean",
        "deprecation",
    ): {
        "disposition": "reviewed_compatibility_exception",
        "rationale": (
            "This old-only R06 test exists to exercise the historical "
            "declaration surface, and the deprecated constructor index is part "
            "of that surface. Rewriting the call would delete the coverage the "
            "test was written to provide."
        ),
        "expiry_release": "alias-removal release",
        "reconsideration_trigger": (
            "Reconsider when the deprecated alias is removed upstream, which "
            "makes the historical surface unavailable and the test obsolete."
        ),
    },
    (
        "NumStability/Algorithms/NormEstimation/TwoNorm/Dixon/Algebra/"
        "DixonCompletion.lean",
        "deprecation",
    ): {
        "disposition": "reviewed_deferred_migration",
        "rationale": (
            "Matrix.PosSemidef.commute_iff is not a rename: its replacement "
            "commute_iff_mul_nonneg is stated for a non-unital star-ordered "
            "ring with a continuous functional calculus and concludes 0 <= a * b "
            "rather than (A * B).PosSemidef. Migrating the site through the "
            "Loewner order the way Mathlib's own deprecated wrapper does fails "
            "instance synthesis here (StarRing (Matrix (Fin n) (Fin n) R)), so "
            "the migration is proof work rather than a mechanical edit and is "
            "deferred to its own reviewed batch."
        ),
        "expiry_release": None,
        "reconsideration_trigger": (
            "Reconsider in the reviewed PosSemidef migration batch, or sooner "
            "if upstream supplies the matrix instances the replacement needs."
        ),
    },
    (
        "NumStability/Source/Higham/Chapter13/DemmelSharpMultiplier.lean",
        "deprecation",
    ): {
        "disposition": "reviewed_deferred_migration",
        "rationale": (
            "Matrix.PosSemidef.commute_iff is not a rename: its replacement "
            "commute_iff_mul_nonneg is stated for a non-unital star-ordered "
            "ring with a continuous functional calculus and concludes 0 <= a * b "
            "rather than (A * B).PosSemidef. Migrating the site through the "
            "Loewner order the way Mathlib's own deprecated wrapper does fails "
            "instance synthesis here (StarRing (Matrix i i R)), so the "
            "migration is proof work rather than a mechanical edit and is "
            "deferred to its own reviewed batch."
        ),
        "expiry_release": None,
        "reconsideration_trigger": (
            "Reconsider in the reviewed PosSemidef migration batch, or sooner "
            "if upstream supplies the matrix instances the replacement needs."
        ),
    },
}


def diagnostic_record(
    diagnostic: Diagnostic, census: Census, commit: str | None
) -> dict[str, Any]:
    kind = diagnostic.kind or ""
    return {
        "anchor_sha256": diagnostic.anchor_sha256,
        "disposition": BASELINE_DEBT,
        "evidence": {"column": diagnostic.column, "line": diagnostic.line},
        "expiry_release": None,
        "introduced_at": commit,
        "kind": kind,
        "message": diagnostic.message,
        "message_sha256": diagnostic.message_sha256,
        "module": module_name(diagnostic.path),
        "occurrence": diagnostic.occurrence,
        "owner_batch": census.owner_batch[diagnostic.path],
        "path": diagnostic.path,
        "rationale": KIND_RATIONALE.get(kind, "Pre-existing accepted diagnostic."),
        "reconsideration_trigger": KIND_RECONSIDERATION_TRIGGER.get(
            kind, "Reconsider when the owning module is next edited."
        ),
        "reviewer": PRIMARY_REVIEWER,
        "role": census.role[diagnostic.path],
        "status": ACCEPTED_BASELINE,
    } | REVIEWED_DISPOSITIONS.get((diagnostic.path, kind), {})


def suppression_record(
    suppression: Suppression, commit: str | None, existing: dict[str, Any] | None
) -> dict[str, Any]:
    record = {
        "anchor_sha256": suppression.anchor_sha256,
        "evidence": {"line": suppression.line, "source": suppression.evidence},
        "expires_at": None,
        "expiry_trigger": (
            "Reconsider on the next toolchain bump, or when the guarded "
            "declaration is next edited; remove the scope once the underlying "
            "diagnostic no longer fires."
        ),
        "introduced_at": commit,
        "occurrence": suppression.occurrence,
        "option": suppression.option,
        "path": suppression.path,
        "rationale": (
            "Reviewed local escape hatch retained from before the warning "
            "baseline existed."
        ),
        "reviewer": PRIMARY_REVIEWER,
        "status": ACCEPTED_BASELINE,
    }
    if existing is not None:
        for key in ("expires_at", "expiry_trigger", "introduced_at", "rationale", "reviewer", "status"):
            if key in existing:
                record[key] = existing[key]
    return record


def build_baseline(
    root: Path,
    capture: LogCapture,
    diagnostics: Sequence[Diagnostic],
    suppressions: Sequence[Suppression],
    census: Census,
    previous: dict[str, Any] | None,
    workflow_path: str,
    run_id: str | None,
    job_id: str | None,
) -> dict[str, Any]:
    manifest = load_json(root / LAKE_MANIFEST, LAKE_MANIFEST.as_posix())
    mathlib_revision = mathlib_rev(manifest)
    toolchain_file = read_toolchain(root)
    previous_suppressions: dict[tuple[str, str, str, int], dict[str, Any]] = {}
    exceptions: list[Any] = []
    if previous:
        for entry in previous.get("suppressions", []) or []:
            if isinstance(entry, dict):
                previous_suppressions[
                    (
                        str(entry.get("path")),
                        str(entry.get("option")),
                        str(entry.get("anchor_sha256")),
                        int(entry.get("occurrence") or 0),
                    )
                ] = entry
        candidate = previous.get("exceptions")
        if isinstance(candidate, list):
            exceptions = candidate
    return {
        "capture": {
            "captured_at": capture.captured_at,
            "command": capture.command,
            "commit": capture.commit,
            "mathlib_revision": mathlib_revision,
            "platform": capture.platform,
            "toolchain": capture.toolchain or toolchain_file,
            "workflow_job_id": job_id,
            "workflow_path": workflow_path,
            "workflow_run_id": run_id,
        },
        "ceilings": {
            "by_file": dict(sorted(census.by_file.items())),
            "by_kind": dict(sorted(census.by_kind.items())),
            "by_role": dict(sorted(census.by_role.items())),
            "global": census.total,
        },
        "diagnostics": [
            diagnostic_record(diagnostic, census, capture.commit)
            for diagnostic in diagnostics
        ],
        "exceptions": sorted(
            (entry for entry in exceptions if isinstance(entry, dict)),
            key=lambda entry: (str(entry.get("scope")), str(entry.get("value"))),
        ),
        "normalization_version": NORMALIZATION_VERSION,
        "schema_version": SCHEMA_VERSION,
        "suppressions": [
            suppression_record(
                suppression,
                capture.commit,
                previous_suppressions.get(suppression.identity),
            )
            for suppression in suppressions
        ],
    }


def mathlib_rev(manifest: dict[str, Any]) -> str | None:
    packages = manifest.get("packages")
    if not isinstance(packages, list):
        raise InputError("lake-manifest.json has no package list")
    for package in packages:
        if isinstance(package, dict) and package.get("name") == "mathlib":
            revision = package.get("rev")
            return revision if isinstance(revision, str) else None
    return None


def read_toolchain(root: Path) -> str:
    path = root / LEAN_TOOLCHAIN
    try:
        return path.read_text(encoding="utf-8").strip()
    except OSError as error:
        raise InputError(f"cannot read {LEAN_TOOLCHAIN.as_posix()}: {error}") from error


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


def active_exceptions(
    baseline: dict[str, Any], today: date, problems: Problems
) -> dict[tuple[str, str], int]:
    allowances: dict[tuple[str, str], int] = {}
    entries = baseline.get("exceptions")
    if entries is None:
        entries = []
    if not isinstance(entries, list):
        problems.malformed("baseline", "`exceptions` must be a list")
        return allowances
    for entry in entries:
        if not isinstance(entry, dict):
            problems.malformed("baseline", "each exception must be an object")
            continue
        scope = entry.get("scope")
        value = entry.get("value")
        allowance = entry.get("allowance")
        if scope not in EXCEPTION_SCOPES or not isinstance(value, str) or not value:
            problems.malformed("baseline", f"invalid exception scope/value: {entry!r}")
            continue
        if not isinstance(allowance, int) or allowance < 0:
            problems.malformed(
                "baseline", f"exception allowance must be a non-negative integer: {value}"
            )
            continue
        if not isinstance(entry.get("reason"), str) or not entry["reason"]:
            problems.malformed("baseline", f"exception lacks a reason: {value}")
        if entry.get("reviewer") != PRIMARY_REVIEWER:
            problems.malformed("baseline", f"exception lacks a reviewer: {value}")
        expires = entry.get("expires_at")
        if isinstance(expires, str):
            parsed = parse_date(expires)
            if parsed is None:
                problems.malformed("baseline", f"exception expires_at is not a date: {value}")
                continue
            if parsed < today:
                problems.violation(
                    "baseline",
                    f"expired exception must be renewed or removed by review: "
                    f"{scope} {value} expired on {expires}",
                )
                continue
        allowances[(scope, value)] = allowances.get((scope, value), 0) + allowance
    return allowances


def baseline_identities(
    baseline: dict[str, Any], problems: Problems
) -> dict[tuple[str, str, str, str, int], dict[str, Any]]:
    entries = baseline.get("diagnostics")
    if not isinstance(entries, list):
        problems.malformed("baseline", "`diagnostics` must be a list")
        return {}
    identities: dict[tuple[str, str, str, str, int], dict[str, Any]] = {}
    for entry in entries:
        if not isinstance(entry, dict):
            problems.malformed("baseline", "each diagnostic must be an object")
            continue
        path = entry.get("path")
        kind = entry.get("kind")
        message = entry.get("message")
        message_sha = entry.get("message_sha256")
        anchor = entry.get("anchor_sha256")
        occurrence = entry.get("occurrence")
        if not isinstance(path, str) or not isinstance(kind, str):
            problems.malformed("baseline", f"diagnostic lacks path/kind: {entry!r}")
            continue
        if not isinstance(message, str) or not isinstance(message_sha, str):
            problems.malformed("baseline", f"diagnostic lacks a message: {path}")
            continue
        if sha256_text(message) != message_sha:
            problems.malformed("baseline", f"diagnostic message hash mismatch: {path}")
            continue
        if not isinstance(anchor, str) or not isinstance(occurrence, int):
            problems.malformed("baseline", f"diagnostic lacks an anchor/occurrence: {path}")
            continue
        if kind not in KNOWN_KINDS:
            problems.malformed("baseline", f"diagnostic records an unknown kind: {kind}")
            continue
        if entry.get("disposition") not in DISPOSITIONS:
            problems.malformed(
                "baseline",
                f"diagnostic disposition must be one of {sorted(DISPOSITIONS)}: "
                f"{path} records {entry.get('disposition')!r}",
            )
        if entry.get("status") != ACCEPTED_BASELINE:
            problems.malformed("baseline", f"diagnostic status must be {ACCEPTED_BASELINE}: {path}")
        if entry.get("reviewer") != PRIMARY_REVIEWER:
            problems.malformed("baseline", f"diagnostic lacks a reviewer: {path}")
        key = (path, kind, message_sha, anchor, occurrence)
        if key in identities:
            problems.malformed("baseline", f"duplicate diagnostic fingerprint: {path} {kind}")
            continue
        identities[key] = entry
    return identities


def check_ceilings(
    baseline: dict[str, Any],
    census: Census,
    allowances: dict[tuple[str, str], int],
    problems: Problems,
) -> None:
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
            f"global warning ceiling exceeded: {census.total} diagnostic(s) against a "
            f"ceiling of {global_ceiling}",
        )
    for bucket, observed, label in (
        ("by_kind", census.by_kind, "kind"),
        ("by_role", census.by_role, "role"),
        ("by_file", census.by_file, "file"),
    ):
        table = ceilings.get(bucket)
        if not isinstance(table, dict):
            problems.malformed("baseline", f"`ceilings.{bucket}` must be an object")
            continue
        scope = "file" if bucket == "by_file" else label
        for key, count in sorted(observed.items()):
            ceiling = table.get(key)
            extra = allowances.get((scope, key), 0) if scope in EXCEPTION_SCOPES else 0
            if ceiling is None:
                if bucket == "by_file":
                    if count > extra:
                        problems.violation(
                            "ceilings",
                            f"file has no reviewed warning allowance (zero-warning "
                            f"ceiling for new or changed files): {key} emitted "
                            f"{count} diagnostic(s)",
                        )
                else:
                    problems.violation(
                        "ceilings",
                        f"per-{label} warning ceiling is missing for {key}: "
                        f"{count} diagnostic(s) observed",
                    )
                continue
            if not isinstance(ceiling, int):
                problems.malformed("baseline", f"ceilings.{bucket}[{key}] must be an integer")
                continue
            if count > ceiling + extra:
                problems.violation(
                    "ceilings",
                    f"per-{label} warning ceiling exceeded for {key}: {count} "
                    f"diagnostic(s) against a ceiling of {ceiling + extra}",
                )


def check_capture(
    root: Path,
    baseline: dict[str, Any],
    capture: LogCapture,
    problems: Problems,
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
    # The capture commit is provenance, not an invariant: every later commit is
    # meant to be checked against this baseline, and the checkout step prints
    # `git log -1 --format=%H` into every CI log, so gating on equality would
    # fail every push after the census was taken. The environment facts below
    # (toolchain, Mathlib revision, platform) are the real invariants, because
    # those are what change the diagnostic set.
    if capture.commit is not None and recorded.get("commit") != capture.commit:
        print(
            f"note: log commit {capture.commit} differs from the baseline capture "
            f"commit {recorded.get('commit')}; the census is compared by "
            f"fingerprint, not by commit"
        )
    toolchain_file = read_toolchain(root)
    if recorded.get("toolchain") != toolchain_file:
        problems.violation(
            "capture",
            f"capture toolchain mismatch between baseline and worktree: baseline "
            f"records {recorded.get('toolchain')!r}, {LEAN_TOOLCHAIN.as_posix()} "
            f"records {toolchain_file!r}",
        )
    if capture.toolchain is not None and recorded.get("toolchain") != capture.toolchain:
        problems.violation(
            "capture",
            f"capture toolchain mismatch between baseline and log: baseline records "
            f"{recorded.get('toolchain')!r}, log shows {capture.toolchain!r}",
        )
    revision = mathlib_rev(load_json(root / LAKE_MANIFEST, LAKE_MANIFEST.as_posix()))
    if recorded.get("mathlib_revision") != revision:
        problems.violation(
            "capture",
            f"capture Mathlib revision mismatch between baseline and worktree: "
            f"baseline records {recorded.get('mathlib_revision')!r}, "
            f"{LAKE_MANIFEST.as_posix()} records {revision!r}",
        )
    if capture.platform is not None and recorded.get("platform") != capture.platform:
        problems.violation(
            "capture",
            f"capture platform mismatch between baseline and log: baseline records "
            f"{recorded.get('platform')!r}, log shows {capture.platform!r}",
        )
    workflow = recorded.get("workflow_path")
    if not isinstance(workflow, str) or not (root / workflow).is_file():
        problems.malformed("baseline", f"capture.workflow_path is not a tracked file: {workflow!r}")


def check_suppressions(
    baseline: dict[str, Any],
    scanned: Sequence[Suppression],
    today: date,
    problems: Problems,
) -> None:
    entries = baseline.get("suppressions")
    if not isinstance(entries, list):
        problems.malformed("baseline", "`suppressions` must be a list")
        return
    listed: dict[tuple[str, str, str, int], dict[str, Any]] = {}
    for entry in entries:
        if not isinstance(entry, dict):
            problems.malformed("baseline", "each suppression must be an object")
            continue
        path = entry.get("path")
        option = entry.get("option")
        anchor = entry.get("anchor_sha256")
        occurrence = entry.get("occurrence")
        if (
            not isinstance(path, str)
            or not isinstance(option, str)
            or not isinstance(anchor, str)
            or not isinstance(occurrence, int)
        ):
            problems.malformed("baseline", f"malformed suppression record: {entry!r}")
            continue
        trigger = entry.get("expiry_trigger")
        if not isinstance(trigger, str) or not trigger.strip():
            problems.malformed(
                "baseline",
                f"suppression lacks a nonempty expiry trigger: {option} at {path}",
            )
        expires = entry.get("expires_at")
        if isinstance(expires, str):
            parsed = parse_date(expires)
            if parsed is None:
                problems.malformed(
                    "baseline", f"suppression expires_at is not a date: {path}"
                )
            elif parsed < today:
                problems.violation(
                    "suppressions",
                    f"expired suppression must be renewed or removed by review: "
                    f"{option} at {path} expired on {expires}",
                )
        listed[(path, option, anchor, occurrence)] = entry

    observed = {suppression.identity: suppression for suppression in scanned}
    for identity, suppression in sorted(observed.items()):
        if identity not in listed:
            problems.violation(
                "suppressions",
                f"new or unlisted suppression: `set_option {suppression.option} false` "
                f"at {suppression.path}:{suppression.line} is not in the reviewed "
                f"suppression manifest",
            )
    for identity in sorted(set(listed) - set(observed)):
        path, option, _, occurrence = identity
        problems.violation(
            "suppressions",
            f"baseline suppression is no longer present in the worktree; this is an "
            f"improvement that requires a reviewed baseline reduction: {option} at "
            f"{path} (occurrence {occurrence})",
        )


def check(
    root: Path,
    log_path: Path,
    baseline_path: Path,
    today: date,
    expect_diagnostics: int | None,
    expect_files: int | None,
) -> int:
    problems = Problems()
    anchors = AnchorReader(root)
    baseline = load_json(baseline_path, baseline_path.name)
    capture = read_log(log_path, anchors)
    diagnostics = deduplicate(capture.diagnostics)
    census = Census(diagnostics, root)
    print(census.render())

    for diagnostic in capture.unclassified[:20]:
        problems.violation(
            "classification",
            f"unknown or unclassifiable diagnostic kind at {diagnostic.path}:"
            f"{diagnostic.line}:{diagnostic.column}: {diagnostic.message[:120]}",
        )
    if len(capture.unclassified) > 20:
        problems.violation(
            "classification",
            f"unknown or unclassifiable diagnostic kinds: "
            f"{len(capture.unclassified)} total",
        )
    for path in sorted(anchors.missing):
        problems.violation(
            "sources",
            f"diagnostic references a source file that is absent from the worktree, "
            f"so its anchor cannot be computed: {path}",
        )

    known = baseline_identities(baseline, problems)
    observed = {diagnostic.identity: diagnostic for diagnostic in diagnostics}
    new_keys = sorted(set(observed) - set(known))
    gone_keys = sorted(set(known) - set(observed))

    # Pair up unmatched fingerprints so a moved or reclassified diagnostic is
    # named as a mutation rather than as an unrelated new/resolved pair.
    by_path_free = {
        (kind, message_sha, anchor, occurrence): key
        for key in gone_keys
        for _, kind, message_sha, anchor, occurrence in [key]
    }
    by_kind_free = {
        (path, anchor, occurrence): key
        for key in gone_keys
        for path, _, _, anchor, occurrence in [key]
    }
    consumed: set[tuple[str, str, str, str, int]] = set()
    residual_new: list[tuple[str, str, str, str, int]] = []
    for key in new_keys:
        path, kind, message_sha, anchor, occurrence = key
        moved = by_path_free.get((kind, message_sha, anchor, occurrence))
        if moved is not None and moved not in consumed and moved[0] != path:
            consumed.add(moved)
            problems.violation(
                "fingerprints",
                f"path mutation of a known fingerprint: {kind} moved from "
                f"{moved[0]} to {path}",
            )
            continue
        reclassified = by_kind_free.get((path, anchor, occurrence))
        if (
            reclassified is not None
            and reclassified not in consumed
            and reclassified[1] != kind
        ):
            consumed.add(reclassified)
            problems.violation(
                "fingerprints",
                f"kind mutation of a known fingerprint: {path} changed from "
                f"{reclassified[1]} to {kind}",
            )
            continue
        residual_new.append(key)

    for key in residual_new:
        path, kind, _, _, occurrence = key
        diagnostic = observed[key]
        problems.violation(
            "fingerprints",
            f"new diagnostic that is not in the reviewed baseline: {kind} at {path} "
            f"(occurrence {occurrence}, evidence line {diagnostic.line} column "
            f"{diagnostic.column})",
        )
    gone_groups: dict[tuple[str, str], int] = {}
    for key in gone_keys:
        if key in consumed:
            continue
        path, kind, _, _, _occurrence = key
        gone_groups[(path, kind)] = gone_groups.get((path, kind), 0) + 1
    for (path, kind), count in sorted(gone_groups.items()):
        problems.violation(
            "fingerprints",
            f"{count} baseline diagnostic(s) no longer fire; this is an "
            f"improvement, not a regression, and it requires a reviewed baseline "
            f"reduction (--write-baseline): {kind} at {path}",
        )

    allowances = active_exceptions(baseline, today, problems)
    check_ceilings(baseline, census, allowances, problems)
    check_capture(root, baseline, capture, problems)
    check_suppressions(baseline, scan_suppressions(root, anchors), today, problems)

    if expect_diagnostics is not None and census.total != expect_diagnostics:
        problems.malformed(
            "census",
            f"expected {expect_diagnostics} diagnostic(s), parsed {census.total}",
        )
    if expect_files is not None and census.files != expect_files:
        problems.malformed(
            "census", f"expected {expect_files} file(s), parsed {census.files}"
        )

    if not problems.ok:
        problems.render()
        return problems.exit_code()
    print(
        f"warning contract satisfied: {census.total} baselined diagnostic(s) across "
        f"{census.files} file(s), {len(baseline.get('suppressions') or [])} reviewed "
        f"suppression(s), no new fingerprints and no unreviewed improvements"
    )
    return 0


def regenerate(
    root: Path,
    log_path: Path,
    baseline_path: Path,
    workflow_path: str,
    run_id: str | None,
    job_id: str | None,
    expect_diagnostics: int | None,
    expect_files: int | None,
) -> int:
    anchors = AnchorReader(root)
    capture = read_log(log_path, anchors)
    if capture.unclassified:
        sample = capture.unclassified[0]
        raise InputError(
            f"refusing to baseline {len(capture.unclassified)} unclassifiable "
            f"diagnostic(s); first is {sample.path}:{sample.line}:{sample.column}: "
            f"{sample.message[:160]}"
        )
    if anchors.missing:
        raise InputError(
            "refusing to baseline diagnostics whose source files are absent from the "
            "worktree: " + ", ".join(sorted(anchors.missing))
        )
    diagnostics = deduplicate(capture.diagnostics)
    census = Census(diagnostics, root)
    if expect_diagnostics is not None and census.total != expect_diagnostics:
        raise InputError(
            f"expected {expect_diagnostics} diagnostic(s), parsed {census.total}"
        )
    if expect_files is not None and census.files != expect_files:
        raise InputError(f"expected {expect_files} file(s), parsed {census.files}")
    previous = load_json(baseline_path, baseline_path.name) if baseline_path.is_file() else None
    document = build_baseline(
        root=root,
        capture=capture,
        diagnostics=diagnostics,
        suppressions=scan_suppressions(root, anchors),
        census=census,
        previous=previous,
        workflow_path=workflow_path,
        run_id=run_id,
        job_id=job_id,
    )
    write_baseline(baseline_path, document)
    print(census.render())
    print(f"suppressions: {len(document['suppressions'])}")
    print(f"Wrote {baseline_path}")
    return 0


# ---------------------------------------------------------------------------
# --self-test
# ---------------------------------------------------------------------------

SELF_TEST_ALPHA = """/-- Fixture alpha. -/
theorem fixture_alpha_one : True := by
  simp [and_true, mul_comm]
  trivial

theorem fixture_alpha_two (h : True) : True := by
  constructor

theorem fixture_alpha_three : True := by
  refine ?_ <;> trivial
"""

SELF_TEST_BETA = """/-- Fixture beta. -/
theorem fixture_beta_one : True := by
  simpa using trivial

theorem fixture_beta_two : True := by
  exact Fixture.legacy_lemma
"""

SELF_TEST_GAMMA = """/-- Fixture gamma, no diagnostics. -/
theorem fixture_gamma_one : True := trivial
"""

SELF_TEST_TOOLCHAIN = "leanprover/lean4:v4.99.0-fixture"
SELF_TEST_PLATFORM = "x86_64-unknown-linux-gnu"
SELF_TEST_COMMIT = "0123456789abcdef0123456789abcdef01234567"
SELF_TEST_MATHLIB = "fedcba9876543210fedcba9876543210fedcba98"


def self_test_diagnostics() -> list[tuple[str, int, int, list[str]]]:
    """(path, line, column, block-lines) for the synthetic fixture log."""

    return [
        (
            "NumStability/Fixture/Alpha.lean",
            3,
            15,
            [
                "This simp argument is unused:",
                "  mul_comm",
                "",
                "Hint: Omit it from the simp argument list.",
                "",
                "Note: This linter can be disabled with "
                "`set_option linter.unusedSimpArgs false`",
            ],
        ),
        (
            "NumStability/Fixture/Alpha.lean",
            6,
            27,
            [
                "",
                "Note: This linter can be disabled with "
                "`set_option linter.unusedVariables false`",
            ],
        ),
        (
            "NumStability/Fixture/Alpha.lean",
            10,
            13,
            [
                "",
                "Note: This linter can be disabled with "
                "`set_option linter.unnecessarySeqFocus false`",
            ],
        ),
        (
            "NumStability/Fixture/Beta.lean",
            3,
            2,
            [
                "",
                "Note: This linter can be disabled with "
                "`set_option linter.unnecessarySimpa false`",
            ],
        ),
        (
            "NumStability/Fixture/Beta.lean",
            6,
            8,
            [],
        ),
    ]


def self_test_head(path: str, line: int, column: int) -> str:
    if path.endswith("Beta.lean") and line == 6:
        return (
            "`Fixture.legacy_lemma` has been deprecated: Use `Fixture.lemma` instead"
        )
    if path.endswith("Alpha.lean") and line == 3:
        return "This simp argument is unused:"
    if path.endswith("Alpha.lean") and line == 6:
        return "unused variable `h`"
    if path.endswith("Alpha.lean") and line == 10:
        return "Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice"
    return "unnecessary `simpa`; use `simp` instead"


def render_self_test_log(
    entries: Sequence[tuple[str, int, int, list[str]]],
    *,
    workspace: str = "/home/runner/work/fixture-repo/fixture-repo/",
    extra: Sequence[str] = (),
) -> bytes:
    stamp = 0

    def line(text: str) -> str:
        nonlocal stamp
        stamp += 1
        return f"2026-08-31T03:{stamp // 60:02d}:{stamp % 60:02d}.0000001Z {text}\r\n"

    out: list[str] = []
    out.append(line("##[group]Checking out the ref"))
    out.append(line("[command]/usr/bin/git log -1 --format=%H"))
    out.append(line(SELF_TEST_COMMIT))
    out.append(line("##[endgroup]"))
    out.append(
        line(
            f"Lean (version {SELF_TEST_TOOLCHAIN.split(':v')[1]}, {SELF_TEST_PLATFORM}, "
            "commit deadbeefdeadbeefdeadbeefdeadbeefdeadbeef, Release)"
        )
    )
    for pass_index, label in enumerate(("Lake Build Output", "Run lake test")):
        out.append(line(f"##[group]{label}"))
        for index, (path, number, column, body) in enumerate(entries):
            out.append(line(f"\x1b[33m\u26a0\x1b[0m [{index + 1}/99] Built fixture"))
            head = self_test_head(path, number, column)
            out.append(
                line(f"warning: {workspace}{path}:{number}:{column}: {head}")
            )
            for entry in body[1:] if body and body[0] == head else body:
                out.append(line(entry))
        for entry in extra:
            out.append(line(entry))
        out.append(line(f"\u2714 [99/99] Replayed pass {pass_index}"))
    return "".join(out).encode("utf-8")


def build_self_test_root(root: Path) -> None:
    (root / "NumStability" / "Fixture").mkdir(parents=True, exist_ok=True)
    (root / "docs" / "architecture").mkdir(parents=True, exist_ok=True)
    (root / ".github" / "workflows").mkdir(parents=True, exist_ok=True)
    (root / "NumStability" / "Fixture" / "Alpha.lean").write_text(
        SELF_TEST_ALPHA, encoding="utf-8", newline="\n"
    )
    (root / "NumStability" / "Fixture" / "Beta.lean").write_text(
        SELF_TEST_BETA, encoding="utf-8", newline="\n"
    )
    (root / "NumStability" / "Fixture" / "Gamma.lean").write_text(
        SELF_TEST_GAMMA, encoding="utf-8", newline="\n"
    )
    (root / LEAN_TOOLCHAIN).write_text(
        SELF_TEST_TOOLCHAIN + "\n", encoding="utf-8", newline="\n"
    )
    (root / LAKE_MANIFEST).write_text(
        json.dumps(
            {
                "version": "1.1.0",
                "packages": [{"name": "mathlib", "rev": SELF_TEST_MATHLIB}],
            },
            indent=1,
        )
        + "\n",
        encoding="utf-8",
        newline="\n",
    )
    (root / TIERS).write_text(
        json.dumps(
            {
                "schema_version": 1,
                "tiers": ["reusable", "source", "internal"],
                "exact": {"NumStability.Fixture.Beta": "source"},
                "prefixes": [{"prefix": "NumStability.Fixture.", "tier": "reusable"}],
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
        newline="\n",
    )
    (root / DEFAULT_WORKFLOW).write_text(
        "name: fixture\n", encoding="utf-8", newline="\n"
    )


def run_checker(argv: Sequence[str]) -> tuple[int, str]:
    buffer = io.StringIO()
    with contextlib.redirect_stdout(buffer), contextlib.redirect_stderr(buffer):
        code = main(list(argv))
    return code, buffer.getvalue()


def expect_failure(argv: Sequence[str], needle: str, label: str) -> bool:
    code, output = run_checker(argv)
    if code == 0 or needle not in output:
        print(
            f"self-test failure: {label} was not rejected as expected "
            f"(exit {code})\n{output}",
            file=sys.stderr,
        )
        return False
    return True


def run_self_test() -> int:
    accepted: list[str] = []
    entries = self_test_diagnostics()
    with tempfile.TemporaryDirectory(prefix="numstability-warnings-selftest-") as tmp:
        base = Path(tmp)
        root = base / "repo"
        build_self_test_root(root)
        log_path = base / "fixture.log"
        log_path.write_bytes(render_self_test_log(entries))
        baseline_path = base / "warnings.json"

        common = ["--root", str(root), "--log", str(log_path), "--baseline", str(baseline_path)]
        code, output = run_checker(
            common
            + [
                "--write-baseline",
                "--capture-run-id",
                "1",
                "--capture-job-id",
                "2",
                "--expect-diagnostics",
                str(len(entries)),
                "--expect-files",
                "2",
            ]
        )
        if code != 0:
            print(f"self-test failure: baseline generation failed\n{output}", file=sys.stderr)
            return 1
        document = json.loads(baseline_path.read_text(encoding="utf-8"))
        if len(document["diagnostics"]) != len(entries):
            print("self-test failure: fixture baseline lost diagnostics", file=sys.stderr)
            return 1
        kinds = {entry["kind"] for entry in document["diagnostics"]}
        if DEPRECATION_KIND not in kinds or "linter.unusedSimpArgs" not in kinds:
            print("self-test failure: fixture kinds were misclassified", file=sys.stderr)
            return 1
        batches = {entry["path"]: entry["owner_batch"] for entry in document["diagnostics"]}
        if batches["NumStability/Fixture/Beta.lean"] != "B1":
            print("self-test failure: deprecation file was not routed to B1", file=sys.stderr)
            return 1
        if batches["NumStability/Fixture/Alpha.lean"] != "B3":
            print("self-test failure: owner batch partition is not first-match", file=sys.stderr)
            return 1
        pristine = baseline_path.read_text(encoding="utf-8")

        code, output = run_checker(common + ["--check"])
        if code != 0:
            print(f"self-test failure: valid fixture was rejected\n{output}", file=sys.stderr)
            return 1

        # Byte-for-byte reproducibility of the review-only regeneration.
        run_checker(
            common + ["--write-baseline", "--capture-run-id", "1", "--capture-job-id", "2"]
        )
        if baseline_path.read_text(encoding="utf-8") != pristine:
            print("self-test failure: baseline regeneration is not reproducible", file=sys.stderr)
            return 1

        def restore() -> None:
            baseline_path.write_text(pristine, encoding="utf-8", newline="\n")
            log_path.write_bytes(render_self_test_log(entries))

        cases: list[str] = []

        # New fingerprint: an extra diagnostic in a baselined file.
        extra = entries + [
            (
                "NumStability/Fixture/Gamma.lean",
                2,
                4,
                [
                    "",
                    "Note: This linter can be disabled with "
                    "`set_option linter.unusedTactic false`",
                ],
            )
        ]
        log_path.write_bytes(render_self_test_log(extra))
        if not expect_failure(
            common + ["--check"], "new diagnostic that is not in the reviewed baseline", "new fingerprint"
        ):
            return 1
        cases.append("new fingerprint")

        # Zero-warning ceiling for a file with no reviewed allowance.
        if not expect_failure(
            common + ["--check"],
            "file has no reviewed warning allowance",
            "zero-warning ceiling for a new file",
        ):
            return 1
        cases.append("zero-warning ceiling")
        restore()

        # Unknown kind.
        unknown = list(entries)
        unknown[0] = (
            "NumStability/Fixture/Alpha.lean",
            3,
            15,
            ["A brand new diagnostic shape with no linter note"],
        )
        log_path.write_bytes(render_self_test_log(unknown))
        if not expect_failure(
            common + ["--check"], "unknown or unclassifiable diagnostic kind", "unknown kind"
        ):
            return 1
        cases.append("unknown kind")
        restore()

        # Global and per-kind ceiling breach: the same diagnostic twice in one pass.
        doubled = list(entries)
        doubled.insert(1, entries[0])
        log_path.write_bytes(render_self_test_log(doubled))
        if not expect_failure(
            common + ["--check"], "global warning ceiling exceeded", "global ceiling breach"
        ):
            return 1
        cases.append("global ceiling")
        if not expect_failure(
            common + ["--check"], "per-kind warning ceiling exceeded", "per-kind ceiling breach"
        ):
            return 1
        cases.append("per-kind ceiling")
        if not expect_failure(
            common + ["--check"], "per-role warning ceiling exceeded", "per-role ceiling breach"
        ):
            return 1
        cases.append("per-role ceiling")
        if not expect_failure(
            common + ["--check"], "per-file warning ceiling exceeded", "per-file ceiling breach"
        ):
            return 1
        cases.append("per-file ceiling")
        restore()

        # Path mutation.
        mutated = json.loads(pristine)
        for entry in mutated["diagnostics"]:
            if entry["kind"] == "linter.unnecessarySimpa":
                entry["path"] = "NumStability/Fixture/Gamma.lean"
                entry["module"] = "NumStability.Fixture.Gamma"
        mutated["ceilings"]["by_file"]["NumStability/Fixture/Gamma.lean"] = 1
        mutated["ceilings"]["by_file"]["NumStability/Fixture/Beta.lean"] -= 1
        write_baseline(baseline_path, mutated)
        if not expect_failure(
            common + ["--check"], "path mutation of a known fingerprint", "path mutation"
        ):
            return 1
        cases.append("path mutation")
        restore()

        # Kind mutation.
        mutated = json.loads(pristine)
        for entry in mutated["diagnostics"]:
            if entry["kind"] == "linter.unnecessarySeqFocus":
                entry["kind"] = "linter.unreachableTactic"
        mutated["ceilings"]["by_kind"]["linter.unreachableTactic"] = 1
        mutated["ceilings"]["by_kind"]["linter.unnecessarySeqFocus"] = 1
        write_baseline(baseline_path, mutated)
        if not expect_failure(
            common + ["--check"], "kind mutation of a known fingerprint", "kind mutation"
        ):
            return 1
        cases.append("kind mutation")
        restore()

        # Toolchain mismatch.
        mutated = json.loads(pristine)
        mutated["capture"]["toolchain"] = "leanprover/lean4:v4.98.0-fixture"
        write_baseline(baseline_path, mutated)
        if not expect_failure(
            common + ["--check"], "capture toolchain mismatch", "toolchain mismatch"
        ):
            return 1
        cases.append("toolchain mismatch")
        restore()

        # A differing capture commit is provenance drift, NOT a violation: the
        # baseline must keep governing later commits. This case asserts the
        # accepting behaviour, because gating on it would break every push after
        # the census was taken.
        mutated = json.loads(pristine)
        mutated["capture"]["commit"] = "f" * 40
        write_baseline(baseline_path, mutated)
        code, output = run_checker(common + ["--check"])
        if code != 0 or "differs from the baseline capture" not in output:
            print(
                "self-test failure: a differing log commit must be accepted with "
                f"a provenance note (exit {code})",
                file=sys.stderr,
            )
            print(output, file=sys.stderr)
            return 1
        accepted.append("later commit accepted as provenance drift")
        restore()

        # Unlisted suppression in a file that carries no diagnostics.
        gamma = root / "NumStability" / "Fixture" / "Gamma.lean"
        original_gamma = gamma.read_text(encoding="utf-8")
        gamma.write_text(
            original_gamma + "\nset_option linter.unusedTactic false in\n"
            "theorem fixture_gamma_two : True := trivial\n",
            encoding="utf-8",
            newline="\n",
        )
        if not expect_failure(
            common + ["--check"], "new or unlisted suppression", "unlisted suppression"
        ):
            return 1
        cases.append("unlisted suppression")
        gamma.write_text(original_gamma, encoding="utf-8", newline="\n")

        # Expired suppression.
        gamma.write_text(
            original_gamma + "\nset_option linter.unusedTactic false in\n"
            "theorem fixture_gamma_two : True := trivial\n",
            encoding="utf-8",
            newline="\n",
        )
        run_checker(
            common + ["--write-baseline", "--capture-run-id", "1", "--capture-job-id", "2"]
        )
        mutated = json.loads(baseline_path.read_text(encoding="utf-8"))
        for entry in mutated["suppressions"]:
            entry["expires_at"] = "2020-01-01"
        write_baseline(baseline_path, mutated)
        if not expect_failure(common + ["--check"], "expired suppression", "expired suppression"):
            return 1
        cases.append("expired suppression")
        gamma.write_text(original_gamma, encoding="utf-8", newline="\n")
        if not expect_failure(
            common + ["--check"],
            "baseline suppression is no longer present in the worktree",
            "resolved suppression",
        ):
            return 1
        cases.append("resolved suppression")
        restore()

        # Disappeared fingerprint: an improvement that must be reviewed down.
        log_path.write_bytes(render_self_test_log(entries[:-1]))
        if not expect_failure(
            common + ["--check"],
            "this is an improvement, not a regression",
            "disappeared fingerprint",
        ):
            return 1
        cases.append("disappeared fingerprint (improvement)")
        restore()

        # Expired exception.
        mutated = json.loads(pristine)
        mutated["exceptions"] = [
            {
                "scope": "file",
                "value": "NumStability/Fixture/Gamma.lean",
                "allowance": 1,
                "reason": "fixture",
                "reviewer": PRIMARY_REVIEWER,
                "expires_at": "2020-01-01",
            }
        ]
        write_baseline(baseline_path, mutated)
        if not expect_failure(common + ["--check"], "expired exception", "expired exception"):
            return 1
        cases.append("expired exception")
        restore()

        # Stale normalization version.
        mutated = json.loads(pristine)
        mutated["normalization_version"] = NORMALIZATION_VERSION + 1
        write_baseline(baseline_path, mutated)
        code, output = run_checker(common + ["--check"])
        if code != 2 or "normalization_version" not in output:
            print(
                f"self-test failure: stale normalization version was not diagnosed "
                f"(exit {code})\n{output}",
                file=sys.stderr,
            )
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
        "warning contract self-test passed: valid fixture accepted; "
        + ", ".join(cases)
        + " rejected; "
        + ", ".join(accepted)
    )
    return 0


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--log", type=Path, help="captured build/test log to parse")
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
        help="repository root whose sources supply anchors and tiers",
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--check", action="store_true", help="verify the log against the baseline"
    )
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
    parser.add_argument("--capture-run-id", default=None, help="workflow run id to record")
    parser.add_argument("--capture-job-id", default=None, help="workflow job id to record")
    parser.add_argument(
        "--capture-workflow",
        default=DEFAULT_WORKFLOW,
        help=f"workflow path to record (default {DEFAULT_WORKFLOW})",
    )
    parser.add_argument(
        "--expect-diagnostics",
        type=int,
        default=None,
        help="assert the parsed diagnostic total (reviewed census guard)",
    )
    parser.add_argument(
        "--expect-files",
        type=int,
        default=None,
        help="assert the parsed distinct-file total (reviewed census guard)",
    )
    parser.add_argument(
        "--now",
        default=None,
        help="ISO date used for expiry evaluation (default: today, UTC)",
    )
    args = parser.parse_args(argv)

    if args.self_test:
        return run_self_test()

    root: Path = args.root.resolve()
    baseline_path: Path = args.baseline or (root / DEFAULT_BASELINE)

    try:
        if args.now is None:
            today = datetime.now(timezone.utc).date()
        else:
            parsed = parse_date(args.now)
            if parsed is None:
                raise InputError(f"--now is not an ISO date: {args.now}")
            today = parsed
        if args.log is None:
            raise InputError("--log is required unless --self-test is given")
        if not args.log.is_file():
            raise InputError(f"log is not a file: {args.log}")
        if args.write_baseline:
            return regenerate(
                root=root,
                log_path=args.log,
                baseline_path=baseline_path,
                workflow_path=args.capture_workflow,
                run_id=args.capture_run_id,
                job_id=args.capture_job_id,
                expect_diagnostics=args.expect_diagnostics,
                expect_files=args.expect_files,
            )
        if not baseline_path.is_file():
            raise InputError(f"baseline is not a file: {baseline_path}")
        return check(
            root=root,
            log_path=args.log,
            baseline_path=baseline_path,
            today=today,
            expect_diagnostics=args.expect_diagnostics,
            expect_files=args.expect_files,
        )
    except InputError as error:
        print(f"error: malformed input: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
