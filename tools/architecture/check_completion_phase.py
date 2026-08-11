#!/usr/bin/env python3
"""Validate the C0008-rooted repository-reorganization completion phase.

This checker is deliberately independent of ``check_phase.py``.  The generic
phase checker validates the reusable phase schema; this file enforces the
one-off, exact activation-to-C0001 contract for the completion successor.  It uses only
the Python standard library and disposable Git indexes rooted at C0000 to
materialize and hash-check the independently requested and reviewed-union
postimages.
"""

from __future__ import annotations

import argparse
import csv
import gzip
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Iterable, Iterator, Sequence


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_PHASE_DIR = Path(
    "docs/architecture/phases/2026-08-repository-reorganization-completion"
)
PREDECESSOR_DIR = Path(
    "docs/architecture/phases/2026-08-repository-reorganization"
)
ACTIVE_POINTER = Path("docs/architecture/phases/active-phase.json")

PHASE_ID = "repository-reorganization-completion-2026-08"
PREDECESSOR_PHASE_ID = "repository-reorganization-2026-08"
CODE_SHA = "b1b18772d80185ec08f49c818919558645c330a1"
INTEGRATED_CODE_SHA = "117aa2bb7e61f41e1531a78452f9f7f6cd5b0771"
R01_MERGE_SHA = "b5966cdc88d136936e6566010cd4113b81f20711"
R02_MERGE_SHA = "52632d28f0c78438d883bde337700f330895159a"
R01_MERGE_PARENTS = (
    "f98f0c8598b7834cb9a80567bc57053e9befa66a",
    "0bdf03a383377c8c6da89d85393e56fca8c00ccd",
)
R02_MERGE_PARENTS = (
    R01_MERGE_SHA,
    "f790c8413412177bb74f47fee74bb12c48c11155",
)
BUILD_LOCK = "lean-reorganization-2026-08"
CHECKPOINT_ID = "C0000"
SUCCESSOR_CHECKPOINT_ID = "C0001"
MATRIX_ALGEBRA = "NumStability/Analysis/MatrixAlgebra.lean"

SUCCESSOR_METRICS = {
    "production_modules": 2631,
    "unclassified_modules": 277,
    "mixed_modules": 9,
    "missing_module_docstrings": 72,
    "noncanonical_modules": 244,
    "declaration_bearing_umbrellas": 21,
    "unsorted_aggregate_imports": 0,
}
SUCCESSOR_MILESTONES = ["M01", "M02"]
SUCCESSOR_GATE_IDS = {
    "architecture",
    "canonical_import",
    "combined_baseline",
    "compatibility",
    "focused_build",
    "full_build",
    "full_tests",
    "layout",
    "old_import",
    "provenance",
    "scope",
    "strict_source",
}
REQUEST_RESOLUTION_EVIDENCE = {
    "R0001": (
        "docs/architecture/phases/2026-08-repository-reorganization-completion/"
        "requests/R0001-R0002-union-review.md",
        "620CFDEFA27F49655D0F399A56461DD60B7D8BCB2169BF1E2C84B515A46F7DF5",
    ),
    "R0002": (
        "docs/architecture/phases/2026-08-repository-reorganization-completion/"
        "requests/R0001-R0002-union-review.md",
        "620CFDEFA27F49655D0F399A56461DD60B7D8BCB2169BF1E2C84B515A46F7DF5",
    ),
    "R0002T": (
        "docs/architecture/phases/2026-08-repository-reorganization-completion/"
        "reviews/R01-R0002T-test-root-union.md",
        "B223E12C8B9571A41488F6ED0A3A180B2AA91C3870774081CE66073B7EBEB487",
    ),
}

SCOPE_HEADER = (
    "module",
    "path",
    "base_blob_oid",
    "current_tier",
    "debt_flags",
    "phase_scope",
    "lane_id",
    "wave_id",
    "planned_actions",
    "rationale",
)
SELECTOR_HEADER = ("module", "path")
DELIVERY_SCOPE_HEADER = ("status", "path")
SHA1_RE = re.compile(r"^[0-9a-f]{40}$")
SHA256_RE = re.compile(r"^[0-9A-Fa-f]{64}$")
RFC3339_RE = re.compile(
    r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?(?:Z|[+-]\d{2}:\d{2})$"
)
IMPORT_RE = re.compile(
    r"(?m)^[ \t]*(?:(?:public|private|meta)\s+)*import[ \t]+([A-Za-z0-9_'.]+)"
)
DEFERRED_RE = re.compile(
    r"\b(?:tbd|todo|pending|unreviewed|undecided|worker decides|decide later|later)\b",
    re.IGNORECASE,
)
GENERATED_PARTS = frozenset({".lake", "__pycache__", ".DS_Store"})
GENERATED_SUFFIXES = frozenset(
    {".olean", ".ilean", ".pyc", ".pyo", ".aux", ".log", ".out"}
)
GENERATED_PREFIXES = ("benchmark-results/",)


R01_PATHS = frozenset(
    """NumStability/Algorithms/StationaryIteration.lean
NumStability/Algorithms/StationaryIterationDrazin.lean
NumStability/Algorithms/StationaryIterationRounded.lean
NumStability/Algorithms/StationaryIterationSemiconvergent.lean
NumStability/Algorithms/StationaryIterationSemiconvergentExistence.lean
NumStability/Analysis/SemiconvergentBlockFormExists.lean
NumStability/Analysis/SemiconvergentExistenceComplete.lean
NumStability/Analysis/SemiconvergentExistenceFull.lean
NumStability/Analysis/SemiconvergentLimitGeneral.lean
NumStability/Analysis/SemiconvergentRealSpectrumComplete.lean
NumStability/Source/Higham/Chapter17/Equation08.lean
NumStability/Source/Higham/Chapter17/Equation12.lean
NumStability/Source/Higham/Chapter17/Equation15.lean
NumStability/Source/Higham/Chapter17/Equation16.lean
NumStability/Source/Higham/Chapter17/Equation17.lean
NumStability/Source/Higham/Chapter17/Equation20.lean""".splitlines()
)

R02_PATHS = frozenset(
    """NumStability/Algorithms/Ch15CondEstimators.lean
NumStability/Algorithms/Ch15DixonClosure.lean
NumStability/Algorithms/Ch15DixonProbability.lean
NumStability/Algorithms/Chapter15CondEst.lean
NumStability/Algorithms/HighamChapter15BoydBridges.lean
NumStability/Algorithms/HighamChapter15BoydConcreteLemma3.lean
NumStability/Algorithms/HighamChapter15BoydLocalStability.lean
NumStability/Algorithms/HighamChapter15BoydRowwiseDomain.lean
NumStability/Algorithms/HighamChapter15BoydScalar.lean
NumStability/Algorithms/HighamChapter15BoydSourceClosure.lean
NumStability/Algorithms/HighamChapter15BoydSourceDomain.lean
NumStability/Algorithms/HighamChapter15BoydSourceLocal.lean
NumStability/Algorithms/HighamChapter15BoydSourceSecondDerivative.lean
NumStability/Algorithms/HighamChapter15BoydUniqueness.lean
NumStability/Algorithms/HighamChapter15ConvergenceProse.lean
NumStability/Algorithms/HighamChapter15RectTermination.lean
NumStability/Algorithms/LU/Higham15Problem15_4.lean
NumStability/Algorithms/LU/Higham15Problem15_6.lean
NumStability/Algorithms/LU/Higham15Problem15_6Closure.lean
NumStability/Algorithms/LU/Higham15Problem15_6Operational.lean
NumStability/Algorithms/LU/TridiagonalCondCh15.lean
NumStability/Algorithms/LU/TridiagonalCondCh15Closure.lean
NumStability/Algorithms/LU/TridiagonalCondCh15IkebeClosure.lean
NumStability/Algorithms/NormEstimation/PNorm/Endpoints/ConvergenceStatements.lean
NumStability/Algorithms/NormEstimation/PNorm/Endpoints/PNormRectangular.lean
NumStability/Algorithms/PNormPowerMethod.lean
NumStability/Algorithms/PNormPowerMethodGeneralP.lean
NumStability/Algorithms/PNormPowerMethodRect.lean""".splitlines()
)

R01_DESTINATIONS = frozenset(
    {
        "NumStability/Algorithms/LinearSystems/Iterative/Stationary/Semiconvergence",
        "NumStability/Analysis/LinearOperators/MatrixPowers/Semiconvergence",
        "NumStability/Source/Higham/Chapter17/Results",
        "NumStabilityTest/Reorganization/R01",
        "docs/architecture/deliveries/R01",
    }
)

R01_CONSUMERS = frozenset(
    {
        "NumStability/Algorithms.lean",
        "NumStability/Analysis.lean",
        "NumStability/Algorithms/StationaryIterationSeries.lean",
        "NumStability/Source/Higham/Chapter17.lean",
        "NumStability/Source/Higham/Chapter17/Equation22.lean",
    }
)
R02_CONSUMERS = frozenset(
    {
        "NumStability/Algorithms.lean",
        "NumStability/Algorithms/NormEstimation/PNorm/All.lean",
        "NumStability/Algorithms/NormEstimation/PNorm/Rectangular/RectangularTermination.lean",
        "NumStability/Source/Higham/Chapter15/Lemma02/PNormPowerMethod/PNormRectangular.lean",
        "NumStability/Source/Higham/Chapter15/Section02/Boyd/EndpointTermination/ConvergenceStatements.lean",
        "NumStability/Source/Higham/Chapter15/Section02/Boyd/EndpointTermination/RectangularTermination.lean",
    }
)
SHARED_CONSUMERS = frozenset(
    R01_CONSUMERS
    | R02_CONSUMERS
    | {"NumStability/Source/Higham/Chapter15.lean"}
)
R0002T_PATHS = frozenset(
    {"NumStabilityTest.lean", "NumStabilityTest/Reorganization/R02.lean"}
)

BRANCH_FACTS = {
    "B0001": {
        "wave": "R01",
        "projection": "P0001",
        "operator": "codex-local",
        "lane": "codex-lane",
        "branch": "codex/reorg-completion-2026-08-r01-stationary-semiconvergence",
        "paths": R01_PATHS,
        "declarations": 243,
        "private": 10,
        "declaration_free": 0,
        "consumers": R01_CONSUMERS,
        "delivery_sha": "0bdf03a383377c8c6da89d85393e56fca8c00ccd",
        "changed_paths": 98,
        "delivery_report": "docs/architecture/deliveries/R01/DELIVERY.md",
        "delivery_report_sha256": "BD5CB4ED6A2C8CEDFAD35DEE491E65EA41A0DCD70181B533B0AD3534F91815B2",
        "scope_evidence": "docs/architecture/deliveries/R01/CHANGED_PATHS.md",
        "scope_evidence_sha256": "84AF04D86C4924295BA7E984F9DB69CD83E095FDE9E45713272F1CAA574D1E27",
    },
    "B0002": {
        "wave": "R02",
        "projection": "P0002",
        "operator": "claude-local",
        "lane": "claude-lane",
        "branch": "codex/reorg-completion-2026-08-r02-norm-estimation-ch15",
        "paths": R02_PATHS,
        "declarations": 142,
        "private": 76,
        "declaration_free": 14,
        "consumers": R02_CONSUMERS,
        "delivery_sha": "f790c8413412177bb74f47fee74bb12c48c11155",
        "changed_paths": 145,
        "delivery_report": "docs/architecture/deliveries/R02/DELIVERY.md",
        "delivery_report_sha256": "C8889350AE3E11CA4A951037D46BC1C9D3FD9F30A777C433EEADB8930E66A6AE",
        "scope_evidence": (
            "docs/architecture/phases/2026-08-repository-reorganization-completion/"
            "reviews/R02-intake-scope.tsv"
        ),
        "scope_evidence_sha256": "801759184E6F986D009F84E84164FD1DA06FA2B3BFC1BDD30A2982FD509132E0",
    },
}

TEST_CLASSES = frozenset(
    {"canonical-only", "old-only", "focused", "protected-consumer"}
)
OVERLAP_CATEGORIES = {
    "owner": ("owner", "overlap"),
    "destination": ("destination", "ancestor"),
    "direct_import": ("direct", "import"),
    "transitive": ("transitive", "reach"),
    "signature": ("signature", "edge"),
    "body": ("body", "edge"),
}


class ValidationFailure(RuntimeError):
    """Raised only by the isolated self-test."""


@dataclass(frozen=True)
class Artifact:
    path: str
    sha256: str


@dataclass(frozen=True)
class PathRule:
    path: str
    match: str

    @property
    def folded(self) -> str:
        return normalize_path(self.path).casefold()

    def intersects(self, other: "PathRule") -> bool:
        left, right = self.folded, other.folded
        if self.match == "exact" and other.match == "exact":
            return left == right
        if self.match == "prefix" and other.match == "prefix":
            return is_equal_or_child(left, right) or is_equal_or_child(right, left)
        prefix, exact = (self, other) if self.match == "prefix" else (other, self)
        return is_equal_or_child(exact.folded, prefix.folded)

    def matches(self, path: str) -> bool:
        folded = normalize_path(path).casefold()
        return folded == self.folded if self.match == "exact" else is_equal_or_child(
            folded, self.folded
        )


class Problems:
    def __init__(self) -> None:
        self.messages: list[str] = []

    def add(self, context: str, message: str) -> None:
        self.messages.append(f"{context}: {message}")

    def require(self, condition: bool, context: str, message: str) -> None:
        if not condition:
            self.add(context, message)


def normalize_path(value: str) -> str:
    return value.replace("\\", "/").rstrip("/")


def is_equal_or_child(path: str, parent: str) -> bool:
    return path == parent or path.startswith(parent + "/")


def module_from_path(path: str) -> str:
    path = normalize_path(path)
    return path[:-5].replace("/", ".") if path.endswith(".lean") else path.replace("/", ".")


def sha256_path(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def split_values(value: str) -> list[str]:
    return [part.strip() for part in re.split(r"[;,]", value) if part.strip() and part.strip() != "-"]


def flatten_strings(value: Any) -> Iterator[str]:
    if isinstance(value, str):
        yield value
    elif isinstance(value, dict):
        for key, item in value.items():
            yield str(key)
            yield from flatten_strings(item)
    elif isinstance(value, list):
        for item in value:
            yield from flatten_strings(item)


def remove_lean_comments(text: str) -> str:
    """Replace nested comments while preserving enough layout for import scans."""

    result: list[str] = []
    index = 0
    depth = 0
    in_string = False
    escaped = False
    while index < len(text):
        pair = text[index : index + 2]
        char = text[index]
        if depth:
            if pair == "/-":
                depth += 1
                result.extend("  ")
                index += 2
            elif pair == "-/":
                depth -= 1
                result.extend("  ")
                index += 2
            else:
                result.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if in_string:
            result.append(char)
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if pair == "/-":
            depth = 1
            result.extend("  ")
            index += 2
        elif pair == "--":
            newline = text.find("\n", index + 2)
            if newline < 0:
                result.extend(" " * (len(text) - index))
                break
            result.extend(" " * (newline - index))
            result.append("\n")
            index = newline + 1
        else:
            result.append(char)
            if char == '"':
                in_string = True
            index += 1
    return "".join(result)


class CompletionValidator:
    def __init__(self, root: Path, phase_dir: Path) -> None:
        self.root = root.resolve()
        self.phase_dir = (
            phase_dir.resolve()
            if phase_dir.is_absolute()
            else (self.root / phase_dir).resolve()
        )
        self.problems = Problems()
        self.phase: dict[str, Any] = {}
        self.scope: list[dict[str, str]] = []
        self.scope_by_path: dict[str, dict[str, str]] = {}
        self.shared_rules: list[PathRule] = []
        self.branch_records: dict[str, dict[str, Any]] = {}
        self.branch_evidence: dict[str, list[Artifact]] = defaultdict(list)
        self.requests: dict[str, dict[str, Any]] = {}
        self.current_checkpoint_id = CHECKPOINT_ID

    def relative(self, path: Path) -> str:
        try:
            return path.resolve().relative_to(self.root).as_posix()
        except ValueError:
            return str(path)

    def resolve_repo_path(self, value: str, context: str) -> Path | None:
        value = normalize_path(value)
        pure = PurePosixPath(value)
        if pure.is_absolute() or ".." in pure.parts or value in {"", "."}:
            self.problems.add(context, f"invalid repository-relative path {value!r}")
            return None
        path = (self.root / Path(*pure.parts)).resolve()
        try:
            path.relative_to(self.root)
        except ValueError:
            self.problems.add(context, f"path escapes repository: {value!r}")
            return None
        return path

    def read_json(self, path: Path, context: str) -> dict[str, Any] | None:
        try:
            value = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, UnicodeError, json.JSONDecodeError) as error:
            self.problems.add(context, f"cannot read JSON: {error}")
            return None
        if not isinstance(value, dict):
            self.problems.add(context, "expected a JSON object")
            return None
        return value

    def read_tsv(
        self,
        path: Path,
        context: str,
        expected_header: Sequence[str] | None = None,
    ) -> tuple[tuple[str, ...], list[dict[str, str]]]:
        try:
            raw = path.read_bytes()
        except OSError as error:
            self.problems.add(context, f"cannot read TSV: {error}")
            return (), []
        if b"\r" in raw:
            self.problems.add(context, "TSV must use LF line endings")
        if raw and not raw.endswith(b"\n"):
            self.problems.add(context, "TSV must end with a newline")
        try:
            text = raw.decode("utf-8-sig")
            reader = csv.DictReader(text.splitlines(), delimiter="\t")
            header = tuple(reader.fieldnames or ())
            rows = [dict(row) for row in reader]
        except (UnicodeError, csv.Error) as error:
            self.problems.add(context, f"cannot parse TSV: {error}")
            return (), []
        if expected_header is not None and header != tuple(expected_header):
            self.problems.add(
                context,
                "header must be exactly: " + "\t".join(expected_header),
            )
        if any(None in row or any(value is None for value in row.values()) for row in rows):
            self.problems.add(context, "malformed row or wrong column count")
        return header, rows

    def artifact(self, value: Any, context: str) -> Artifact | None:
        if not isinstance(value, dict) or set(value) != {"path", "sha256"}:
            self.problems.add(context, "expected exactly {path, sha256}")
            return None
        path_value, digest = value.get("path"), value.get("sha256")
        if not isinstance(path_value, str) or not isinstance(digest, str):
            self.problems.add(context, "path and sha256 must be strings")
            return None
        if not SHA256_RE.fullmatch(digest):
            self.problems.add(context, "sha256 must be 64 hexadecimal characters")
            return None
        path = self.resolve_repo_path(path_value, context)
        if path is None:
            return None
        if not path.is_file():
            self.problems.add(context, f"missing artifact {path_value}")
            return None
        actual = sha256_path(path)
        if actual != digest.upper():
            self.problems.add(
                context,
                f"SHA-256 mismatch for {path_value}: expected {digest.upper()}, found {actual}",
            )
        return Artifact(normalize_path(path_value), digest.upper())

    def git(self, *args: str, check: bool = True, env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
        process = subprocess.run(
            ["git", *args],
            cwd=self.root,
            env=env,
            text=True,
            encoding="utf-8",
            errors="replace",
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        if check and process.returncode:
            raise RuntimeError(
                f"git {' '.join(args)} failed ({process.returncode}): "
                f"{process.stderr.strip() or process.stdout.strip()}"
            )
        return process

    def git_bytes(
        self,
        *args: str,
        check: bool = True,
        env: dict[str, str] | None = None,
    ) -> subprocess.CompletedProcess[bytes]:
        process = subprocess.run(
            ["git", *args],
            cwd=self.root,
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        if check and process.returncode:
            detail = (process.stderr or process.stdout).decode(
                "utf-8", errors="replace"
            ).strip()
            raise RuntimeError(
                f"git {' '.join(args)} failed ({process.returncode}): {detail}"
            )
        return process

    def run(self) -> Problems:
        self.validate_pointer()
        self.load_phase()
        self.validate_checkpoint_and_scope()
        self.validate_branches()
        self.validate_routes_and_tests()
        self.validate_projections()
        self.validate_overlap_reviews()
        self.validate_requests_and_postimages()
        self.validate_milestone_dag()
        return self.problems

    def validate_pointer(self) -> None:
        path = self.root / ACTIVE_POINTER
        pointer = self.read_json(path, ACTIVE_POINTER.as_posix())
        if pointer is None:
            return
        expected = {
            "schema_version": 1,
            "record_kind": "active_reorganization_phase",
            "phase_id": PHASE_ID,
            "path": DEFAULT_PHASE_DIR.as_posix(),
        }
        self.problems.require(
            pointer == expected,
            ACTIVE_POINTER.as_posix(),
            f"must exactly equal {canonical_json(expected)}",
        )

    def load_phase(self) -> None:
        context = self.relative(self.phase_dir / "phase.json")
        phase = self.read_json(self.phase_dir / "phase.json", context)
        if phase is None:
            return
        self.phase = phase
        exact = {
            "schema_version": 1,
            "record_kind": "reorganization_phase",
            "phase_id": PHASE_ID,
            "origin_checkpoint_id": CHECKPOINT_ID,
            "status": "active",
        }
        for key, expected in exact.items():
            self.problems.require(
                phase.get(key) == expected,
                f"phase.json.{key}",
                f"expected {expected!r}, found {phase.get(key)!r}",
            )
        current = phase.get("current_checkpoint_id")
        self.problems.require(
            current in {CHECKPOINT_ID, SUCCESSOR_CHECKPOINT_ID},
            "phase.json.current_checkpoint_id",
            f"expected {CHECKPOINT_ID} or {SUCCESSOR_CHECKPOINT_ID}, found {current!r}",
        )
        if current in {CHECKPOINT_ID, SUCCESSOR_CHECKPOINT_ID}:
            self.current_checkpoint_id = current
        base = phase.get("base_policy")
        if not isinstance(base, dict):
            self.problems.add("phase.json.base_policy", "expected an object")
        else:
            self.problems.require(
                base.get("immutable_origin_sha") == CODE_SHA,
                "phase.json.base_policy.immutable_origin_sha",
                f"expected {CODE_SHA}",
            )
        authority = phase.get("authority")
        if not isinstance(authority, dict):
            self.problems.add("phase.json.authority", "expected an object")
        else:
            for key in ("integration_authority_id", "release_manager_id"):
                self.problems.require(
                    authority.get(key) == "primary-human",
                    f"phase.json.authority.{key}",
                    "expected primary-human",
                )
            self.problems.require(
                authority.get("build_lock_name") == BUILD_LOCK,
                "phase.json.authority.build_lock_name",
                f"expected {BUILD_LOCK}",
            )
            shared_auth = authority.get("shared_path_authority_ids")
            self.problems.require(
                isinstance(shared_auth, list) and set(shared_auth) == {"primary-human"},
                "phase.json.authority.shared_path_authority_ids",
                "expected exactly primary-human",
            )
            lanes = authority.get("lanes") if isinstance(authority.get("lanes"), list) else []
            operators = {
                operator
                for lane in lanes
                if isinstance(lane, dict)
                for operator in lane.get("operator_ids", [])
                if isinstance(operator, str)
            }
            self.problems.require(
                {"codex-local", "claude-local"} <= operators,
                "phase.json.authority.lanes",
                "local lanes must include codex-local and claude-local",
            )
        scope_ref = self.artifact(phase.get("scope"), "phase.json.scope")
        if scope_ref is not None:
            self.problems.require(
                scope_ref.path == self.relative(self.phase_dir / "scope.tsv"),
                "phase.json.scope.path",
                "must point to successor scope.tsv",
            )
        self.shared_rules = self.parse_rules(phase.get("shared_paths"), "phase.json.shared_paths")
        shared_exact = {rule.path for rule in self.shared_rules if rule.match == "exact"}
        missing = sorted(SHARED_CONSUMERS - shared_exact)
        if missing:
            self.problems.add(
                "phase.json.shared_paths",
                "missing exact integrator-shared consumer(s): " + ", ".join(missing),
            )
        readme = self.phase_dir / "README.md"
        try:
            text = readme.read_text(encoding="utf-8")
        except OSError as error:
            self.problems.add(self.relative(readme), f"cannot read phase README: {error}")
        else:
            for token in ("predecessor", "C0008", CODE_SHA):
                if token not in text:
                    self.problems.add(self.relative(readme), f"missing predecessor root token {token!r}")

    def parse_rules(self, value: Any, context: str) -> list[PathRule]:
        if not isinstance(value, list):
            self.problems.add(context, "expected a list")
            return []
        result: list[PathRule] = []
        for index, item in enumerate(value):
            item_context = f"{context}[{index}]"
            if not isinstance(item, dict) or set(item) != {"path", "match"}:
                self.problems.add(item_context, "expected exactly {path, match}")
                continue
            path, match = item.get("path"), item.get("match")
            if not isinstance(path, str) or match not in {"exact", "prefix"}:
                self.problems.add(item_context, "invalid path rule")
                continue
            normalized = normalize_path(path)
            if normalized != path.rstrip("/").replace("\\", "/"):
                self.problems.add(item_context, "path rule must use normalized repository separators")
            result.append(PathRule(normalized, match))
        keys = [(rule.path.casefold(), rule.match) for rule in result]
        if len(keys) != len(set(keys)):
            self.problems.add(context, "duplicate case-insensitive path rule")
        return result

    def validate_checkpoint_and_scope(self) -> None:
        checkpoint_path = self.phase_dir / "checkpoints/C0000.json"
        checkpoint = self.read_json(checkpoint_path, self.relative(checkpoint_path))
        if checkpoint is None:
            return
        for key, expected in {
            "schema_version": 1,
            "record_kind": "phase_checkpoint",
            "phase_id": PHASE_ID,
            "checkpoint_id": CHECKPOINT_ID,
            "commit_sha": CODE_SHA,
        }.items():
            self.problems.require(
                checkpoint.get(key) == expected,
                f"checkpoints/C0000.json.{key}",
                f"expected {expected!r}",
            )
        if self.current_checkpoint_id == SUCCESSOR_CHECKPOINT_ID:
            self.validate_successor_checkpoint()
        inventory_ref = self.artifact(
            checkpoint.get("inventory"), "checkpoints/C0000.json.inventory"
        )
        scope_path = self.phase_dir / "scope.tsv"
        _, scope = self.read_tsv(scope_path, self.relative(scope_path), SCOPE_HEADER)
        self.scope = scope
        self.scope_by_path = {row.get("path", ""): row for row in scope}
        self.problems.require(
            len(scope) == 2593,
            self.relative(scope_path),
            f"expected 2,593 production rows, found {len(scope)}",
        )
        if len(self.scope_by_path) != len(scope):
            self.problems.add(self.relative(scope_path), "duplicate scope path")
        if inventory_ref is not None:
            inventory_path = self.root / inventory_ref.path
            _, inventory = self.read_tsv(
                inventory_path, inventory_ref.path, SCOPE_HEADER
            )
            if inventory != scope:
                self.problems.add(
                    inventory_ref.path,
                    "C0000 inventory must byte-semantically equal successor scope.tsv",
                )
        predecessor_path = self.root / PREDECESSOR_DIR / "checkpoints/C0008-inventory.tsv"
        _, predecessor = self.read_tsv(
            predecessor_path,
            (PREDECESSOR_DIR / "checkpoints/C0008-inventory.tsv").as_posix(),
            SCOPE_HEADER,
        )
        predecessor_by_path = {row.get("path", ""): row for row in predecessor}
        self.problems.require(
            len(predecessor) == 2593,
            "predecessor C0008 inventory",
            f"expected 2,593 rows, found {len(predecessor)}",
        )
        debt = {row["path"] for row in predecessor if row.get("debt_flags") != "-"}
        clean_w90 = {
            row["path"]
            for row in predecessor
            if row.get("debt_flags") == "-" and row.get("wave_id") == "W90"
        }
        self.problems.require(len(debt) == 467, "residual accounting", f"expected 467 debt rows, found {len(debt)}")
        self.problems.require(len(clean_w90) == 15, "residual accounting", f"expected 15 debt-free W90 outliers, found {len(clean_w90)}")
        for path, old in predecessor_by_path.items():
            new = self.scope_by_path.get(path)
            if new is None:
                self.problems.add("scope.tsv", f"missing immutable C0008 path {path}")
                continue
            for key in ("module", "path", "base_blob_oid", "current_tier", "debt_flags"):
                if new.get(key) != old.get(key):
                    self.problems.add(
                        f"scope.tsv[{path}]",
                        f"immutable {key} drift: {old.get(key)!r} -> {new.get(key)!r}",
                    )
        in_scope = {row["path"] for row in scope if row.get("phase_scope") == "in_scope"}
        complete = {row["path"] for row in scope if row.get("phase_scope") == "already_complete"}
        self.problems.require(len(in_scope) == 492, "scope.tsv", f"expected 492 in_scope rows, found {len(in_scope)}")
        self.problems.require(len(complete) == 2101, "scope.tsv", f"expected 2,101 already_complete rows, found {len(complete)}")
        expected_editable = (debt | clean_w90) - {MATRIX_ALGEBRA}
        expected_in_scope = expected_editable | SHARED_CONSUMERS
        missing = sorted(expected_in_scope - in_scope)
        extra = sorted(in_scope - expected_in_scope)
        if missing or extra:
            self.problems.add(
                "scope.tsv residual assignment",
                f"expected exact 492-row set; missing={missing}, extra={extra}",
            )
        matrix = self.scope_by_path.get(MATRIX_ALGEBRA)
        if matrix is None:
            self.problems.add("scope.tsv", f"missing protected {MATRIX_ALGEBRA}")
        else:
            self.problems.require(
                matrix.get("phase_scope") == "already_complete"
                and matrix.get("lane_id") == "-"
                and matrix.get("wave_id") == "-",
                f"scope.tsv[{MATRIX_ALGEBRA}]",
                "must be protected already_complete with lane_id/wave_id '-'",
            )
        for path in SHARED_CONSUMERS:
            row = self.scope_by_path.get(path)
            if row is None:
                self.problems.add("scope.tsv", f"missing shared consumer {path}")
                continue
            self.problems.require(
                row.get("phase_scope") == "in_scope" and row.get("wave_id") == "I01",
                f"scope.tsv[{path}]",
                "integrator-shared consumer must be in_scope in I01",
            )
        for row in scope:
            disposition = row.get("phase_scope")
            if disposition == "in_scope":
                if row.get("lane_id") in {"", "-"} or row.get("wave_id") in {"", "-"}:
                    self.problems.add(
                        f"scope.tsv[{row.get('path')}]",
                        "in_scope row requires a lane and wave",
                    )
            elif disposition == "already_complete":
                if row.get("lane_id") != "-" or row.get("wave_id") != "-":
                    self.problems.add(
                        f"scope.tsv[{row.get('path')}]",
                        "already_complete row must use '-' lane and wave",
                    )
            else:
                self.problems.add(
                    f"scope.tsv[{row.get('path')}]",
                    f"completion scope permits only in_scope/already_complete, found {disposition!r}",
                )
        for wave, paths in (("R01", R01_PATHS), ("R02", R02_PATHS)):
            actual = {
                row["path"]
                for row in scope
                if row.get("phase_scope") == "in_scope" and row.get("wave_id") == wave
            }
            if actual != paths:
                self.problems.add(
                    f"scope.tsv wave {wave}",
                    f"must equal exact selector paths; missing={sorted(paths-actual)}, extra={sorted(actual-paths)}",
                )
        accounting = self.phase_dir / "reviews/residual-accounting.md"
        try:
            text = accounting.read_text(encoding="utf-8")
        except OSError as error:
            self.problems.add(self.relative(accounting), f"cannot read residual review: {error}")
        else:
            compact = text.replace(",", "")
            for token in ("467", "15", "481", "492", "2101", MATRIX_ALGEBRA):
                if token not in compact:
                    self.problems.add(self.relative(accounting), f"missing accounting token {token!r}")

    def validate_successor_checkpoint(self) -> None:
        context = "checkpoints/C0001.json"
        path = self.phase_dir / "checkpoints/C0001.json"
        checkpoint = self.read_json(path, self.relative(path))
        if checkpoint is None:
            return
        for key, expected in {
            "schema_version": 1,
            "record_kind": "phase_checkpoint",
            "phase_id": PHASE_ID,
            "checkpoint_id": SUCCESSOR_CHECKPOINT_ID,
            "parent_checkpoint_id": CHECKPOINT_ID,
            "commit_sha": INTEGRATED_CODE_SHA,
            "accepted_by": "primary-human",
            "milestones_satisfied": SUCCESSOR_MILESTONES,
            "unblocks": [],
            "metrics": SUCCESSOR_METRICS,
        }.items():
            self.problems.require(
                checkpoint.get(key) == expected,
                f"{context}.{key}",
                f"expected {expected!r}, found {checkpoint.get(key)!r}",
            )
        accepted_at = checkpoint.get("accepted_at")
        self.problems.require(
            isinstance(accepted_at, str)
            and RFC3339_RE.fullmatch(accepted_at) is not None,
            f"{context}.accepted_at",
            "expected an RFC3339 timestamp with timezone",
        )

        inventory = self.artifact(checkpoint.get("inventory"), f"{context}.inventory")
        expected_inventory = self.relative(
            self.phase_dir / "checkpoints/C0001-inventory.tsv"
        )
        if inventory is not None:
            self.problems.require(
                inventory.path == expected_inventory,
                f"{context}.inventory.path",
                f"expected {expected_inventory}",
            )
            _, rows = self.read_tsv(
                self.root / inventory.path,
                inventory.path,
                SCOPE_HEADER,
            )
            self.problems.require(
                len(rows) == SUCCESSOR_METRICS["production_modules"],
                inventory.path,
                "row count must equal the exact C0001 production-module metric",
            )
            paths = [row.get("path", "") for row in rows]
            self.problems.require(
                len(paths) == len(set(paths)),
                inventory.path,
                "C0001 inventory paths must be unique",
            )

        baseline = checkpoint.get("combined_baseline")
        if not isinstance(baseline, dict):
            self.problems.add(f"{context}.combined_baseline", "expected an object")
        else:
            self.problems.require(
                baseline.get("format_version") == 2,
                f"{context}.combined_baseline.format_version",
                "expected exact format version 2",
            )
            artifact = self.artifact(
                baseline.get("artifact"),
                f"{context}.combined_baseline.artifact",
            )
            summary = self.artifact(
                baseline.get("summary_artifact"),
                f"{context}.combined_baseline.summary_artifact",
            )
            expected_artifact = self.relative(
                self.phase_dir / "baselines/C0001-combined.json"
            )
            expected_summary = self.relative(
                self.phase_dir / "baselines/C0001-combined.md"
            )
            if artifact is not None:
                self.problems.require(
                    artifact.path == expected_artifact,
                    f"{context}.combined_baseline.artifact.path",
                    f"expected {expected_artifact}",
                )
                document = self.read_json(
                    self.root / artifact.path,
                    f"{context}.combined_baseline.artifact",
                )
                metadata = document.get("metadata") if document is not None else None
                self.problems.require(
                    isinstance(metadata, dict)
                    and metadata.get("commit") == INTEGRATED_CODE_SHA
                    and metadata.get("library_source_clean") is True
                    and metadata.get("library_source_dirty_paths") == [],
                    f"{context}.combined_baseline.artifact.metadata",
                    "must record the exact clean integrated code commit",
                )
            if summary is not None:
                self.problems.require(
                    summary.path == expected_summary,
                    f"{context}.combined_baseline.summary_artifact.path",
                    f"expected {expected_summary}",
                )
            self.problems.require(
                isinstance(baseline.get("generation_command"), str)
                and bool(baseline.get("generation_command", "").strip()),
                f"{context}.combined_baseline.generation_command",
                "must record a nonempty generation command",
            )

        gates = checkpoint.get("gates")
        if not isinstance(gates, list):
            self.problems.add(f"{context}.gates", "expected a list")
        else:
            gate_ids = [
                gate.get("gate_id")
                for gate in gates
                if isinstance(gate, dict)
            ]
            self.problems.require(
                len(gate_ids) == len(gates)
                and len(gate_ids) == len(set(gate_ids))
                and set(gate_ids) == SUCCESSOR_GATE_IDS,
                f"{context}.gates",
                "must contain every and only the 12 exact C0001 acceptance gates",
            )
            expected_evidence = self.relative(
                self.phase_dir / "checkpoints/C0001-gates.md"
            )
            for index, gate in enumerate(gates):
                if not isinstance(gate, dict):
                    self.problems.add(f"{context}.gates[{index}]", "expected an object")
                    continue
                gate_id = gate.get("gate_id")
                gate_context = f"{context}.gates[{gate_id or index}]"
                self.problems.require(
                    gate.get("status") == "PASS"
                    and gate.get("commit_sha") == INTEGRATED_CODE_SHA,
                    gate_context,
                    "must record PASS at the exact integrated code commit",
                )
                evidence = self.artifact(
                    gate.get("evidence"), f"{gate_context}.evidence"
                )
                if evidence is not None:
                    self.problems.require(
                        evidence.path == expected_evidence,
                        f"{gate_context}.evidence.path",
                        f"expected {expected_evidence}",
                    )

        milestones = self.phase.get("milestones")
        milestone_map = {
            item.get("milestone_id"): item
            for item in milestones
            if isinstance(item, dict) and isinstance(item.get("milestone_id"), str)
        } if isinstance(milestones, list) else {}
        for milestone_id in SUCCESSOR_MILESTONES:
            milestone = milestone_map.get(milestone_id)
            self.problems.require(
                isinstance(milestone, dict)
                and milestone.get("status") == "accepted"
                and milestone.get("accepted_checkpoint_id")
                == SUCCESSOR_CHECKPOINT_ID,
                f"phase.json.milestones[{milestone_id}]",
                "must be accepted at exact checkpoint C0001",
            )
        self.validate_successor_history()

    def validate_successor_history(self) -> None:
        for commit, parents, label in (
            (R01_MERGE_SHA, R01_MERGE_PARENTS, "R01 merge"),
            (R02_MERGE_SHA, R02_MERGE_PARENTS, "R02 merge"),
        ):
            process = self.git(
                "rev-list", "--parents", "-n", "1", commit, check=False
            )
            actual = process.stdout.strip().split()
            expected = [commit, *parents]
            self.problems.require(
                process.returncode == 0 and actual == expected,
                f"C0001 {label} ancestry",
                f"expected exact commit/parent vector {expected}, found {actual}",
            )
        for ancestor, label in (
            (R01_MERGE_SHA, "R01 merge"),
            (R02_MERGE_SHA, "R02 merge"),
            (BRANCH_FACTS["B0001"]["delivery_sha"], "R01 delivery"),
            (BRANCH_FACTS["B0002"]["delivery_sha"], "R02 delivery"),
        ):
            ancestry = self.git(
                "merge-base",
                "--is-ancestor",
                ancestor,
                INTEGRATED_CODE_SHA,
                check=False,
            )
            self.problems.require(
                ancestry.returncode == 0,
                f"C0001 {label} ancestry",
                f"{ancestor} must be an ancestor of exact integrated code {INTEGRATED_CODE_SHA}",
            )

    def validate_branches(self) -> None:
        base_paths = self.git_tree_paths(CODE_SHA)
        scope_rules = [PathRule(path, "exact") for path in self.scope_by_path]
        live_rules: dict[str, list[PathRule]] = {}
        statuses: set[str] = set()
        for branch_id, facts in BRANCH_FACTS.items():
            path = self.phase_dir / f"branches/{branch_id}.json"
            branch = self.read_json(path, self.relative(path))
            if branch is None:
                continue
            self.branch_records[branch_id] = branch
            for key, expected in {
                "schema_version": 1,
                "record_kind": "phase_branch",
                "phase_id": PHASE_ID,
                "branch_id": branch_id,
                "lane_id": facts["lane"],
                "wave_id": facts["wave"],
                "branch_name": facts["branch"],
                "owner_id": "primary-human",
                "base_checkpoint_id": CHECKPOINT_ID,
                "base_sha": CODE_SHA,
                "baseline_projection_id": facts["projection"],
            }.items():
                self.problems.require(
                    branch.get(key) == expected,
                    f"{branch_id}.{key}",
                    f"expected {expected!r}, found {branch.get(key)!r}",
                )
            operators = branch.get("operator_ids")
            self.problems.require(
                isinstance(operators, list) and operators == [facts["operator"]],
                f"{branch_id}.operator_ids",
                f"expected exactly [{facts['operator']!r}]",
            )
            status = branch.get("status")
            allowed_statuses = (
                {"delivered"}
                if self.current_checkpoint_id == CHECKPOINT_ID
                else {"accepted", "retired"}
            )
            self.problems.require(
                status in allowed_statuses,
                f"{branch_id}.status",
                f"must be one of {sorted(allowed_statuses)} while current checkpoint is "
                f"{self.current_checkpoint_id}",
            )
            if isinstance(status, str):
                statuses.add(status)
            owned = self.parse_rules(branch.get("owned_paths"), f"{branch_id}.owned_paths")
            actual_owned = {rule.path for rule in owned if rule.match == "exact"}
            self.problems.require(
                len(owned) == len(actual_owned) and actual_owned == facts["paths"],
                f"{branch_id}.owned_paths",
                "must be exact rules for every and only selector path",
            )
            destinations = self.parse_rules(
                branch.get("destination_prefixes"), f"{branch_id}.destination_prefixes"
            )
            if not destinations:
                self.problems.add(f"{branch_id}.destination_prefixes", "must not be empty")
            if any(rule.match != "prefix" for rule in destinations):
                self.problems.add(f"{branch_id}.destination_prefixes", "all destination rules must be prefixes")
            if branch_id == "B0001":
                actual_dest = {rule.path for rule in destinations}
                self.problems.require(
                    actual_dest == R01_DESTINATIONS,
                    f"{branch_id}.destination_prefixes",
                    f"must equal exact reviewed five-prefix set; found {sorted(actual_dest)}",
                )
            forbidden = self.parse_rules(
                branch.get("forbidden_paths"), f"{branch_id}.forbidden_paths"
            )
            self.problems.require(
                PathRule(MATRIX_ALGEBRA, "exact") in forbidden,
                f"{branch_id}.forbidden_paths",
                f"must protect exact {MATRIX_ALGEBRA}",
            )
            delivery = branch.get("delivery")
            delivery_required = status in {"delivered", "accepted", "retired"}
            if not isinstance(delivery, dict):
                self.problems.add(f"{branch_id}.delivery", "expected an object")
            elif delivery_required:
                self.problems.require(
                    delivery.get("commit_sha") == facts["delivery_sha"],
                    f"{branch_id}.delivery.commit_sha",
                    f"expected immutable delivery {facts['delivery_sha']}",
                )
                report = self.artifact(delivery.get("report"), f"{branch_id}.delivery.report")
                scope_evidence = self.artifact(
                    delivery.get("scope_evidence"), f"{branch_id}.delivery.scope_evidence"
                )
                for artifact, key in (
                    (report, "delivery_report"),
                    (scope_evidence, "scope_evidence"),
                ):
                    if artifact is not None:
                        self.problems.require(
                            artifact.path == facts[key]
                            and artifact.sha256 == facts[f"{key}_sha256"],
                            f"{branch_id}.delivery.{key}",
                            f"must exactly hash-pin {facts[key]} at "
                            f"{facts[f'{key}_sha256']}",
                        )
                self.validate_delivery_scope(
                    branch_id, facts, owned, destinations, forbidden
                )
            else:
                self.problems.require(
                    delivery
                    == {"commit_sha": None, "report": None, "scope_evidence": None},
                    f"{branch_id}.delivery",
                    "planned/active state requires an empty delivery record",
                )
            self.validate_branch_lifecycle(branch_id, branch, facts, status)
            evidence = branch.get("refresh", {}).get("evidence") if isinstance(branch.get("refresh"), dict) else None
            if not isinstance(evidence, list):
                self.problems.add(f"{branch_id}.refresh.evidence", "expected hash-pinned evidence list")
            else:
                for index, item in enumerate(evidence):
                    artifact = self.artifact(item, f"{branch_id}.refresh.evidence[{index}]")
                    if artifact is not None:
                        self.branch_evidence[branch_id].append(artifact)
            selector_path = self.phase_dir / f"selectors/{facts['wave']}.tsv"
            _, selector = self.read_tsv(
                selector_path, self.relative(selector_path), SELECTOR_HEADER
            )
            expected_rows = sorted(
                ((module_from_path(item), item) for item in facts["paths"]),
                key=lambda pair: pair[0],
            )
            actual_rows = [(row.get("module", ""), row.get("path", "")) for row in selector]
            self.problems.require(
                actual_rows == expected_rows,
                self.relative(selector_path),
                "selector must contain exact sorted module/path rows",
            )
            for own in owned:
                for shared in self.shared_rules:
                    if own.intersects(shared):
                        self.problems.add(
                            f"{branch_id} owner/shared collision",
                            f"{own.path} intersects {shared.path}",
                        )
            for dest in destinations:
                folded = dest.folded
                occupied = [
                    item for item in base_paths if is_equal_or_child(item.casefold(), folded)
                ]
                if occupied:
                    self.problems.add(
                        f"{branch_id}.destination_prefixes",
                        f"destination {dest.path} is not casefold-vacant at C0000: {occupied[:5]}",
                    )
                for rule in scope_rules + self.shared_rules + forbidden:
                    if dest.intersects(rule):
                        self.problems.add(
                            f"{branch_id}.destination_prefixes",
                            f"destination {dest.path} intersects protected/scope path {rule.path}",
                        )
            live_rules[branch_id] = owned + destinations
        self.problems.require(
            len(statuses) <= 1,
            "branch pair state",
            f"B0001/B0002 must transition together, found statuses {sorted(statuses)}",
        )
        if set(live_rules) == set(BRANCH_FACTS):
            left, right = live_rules["B0001"], live_rules["B0002"]
            for one in left:
                for two in right:
                    if one.intersects(two):
                        self.problems.add(
                            "B0001/B0002 ownership",
                            f"equal-or-ancestor collision {one.path} / {two.path}",
                        )

    def validate_branch_lifecycle(
        self,
        branch_id: str,
        branch: dict[str, Any],
        facts: dict[str, Any],
        status: Any,
    ) -> None:
        integration = branch.get("integration")
        remote_ref = f"refs/heads/{facts['branch']}"
        if self.current_checkpoint_id == CHECKPOINT_ID:
            self.problems.require(
                integration
                == {
                    "method": None,
                    "accepted_checkpoint_id": None,
                    "accepted_sha": None,
                },
                f"{branch_id}.integration",
                "C0000 delivery state requires an exact empty integration record",
            )
            expected_retirement = {
                "remote_ref": remote_ref,
                "rule": "delivery_ancestor_of_green_checkpoint",
                "status": "not_due",
                "retired_at": None,
                "retired_by": None,
                "ancestry_checkpoint_id": None,
            }
            self.problems.require(
                branch.get("retirement") == expected_retirement,
                f"{branch_id}.retirement",
                f"expected exact C0000 retirement state {expected_retirement!r}",
            )
            return

        expected_integration = {
            "method": "merge",
            "accepted_checkpoint_id": SUCCESSOR_CHECKPOINT_ID,
            "accepted_sha": INTEGRATED_CODE_SHA,
        }
        self.problems.require(
            integration == expected_integration,
            f"{branch_id}.integration",
            f"expected exact true-merge integration record {expected_integration!r}",
        )
        retirement = branch.get("retirement")
        if not isinstance(retirement, dict):
            self.problems.add(f"{branch_id}.retirement", "expected an object")
            return
        exact_common = {
            "remote_ref": remote_ref,
            "rule": "delivery_ancestor_of_green_checkpoint",
        }
        for key, expected in exact_common.items():
            self.problems.require(
                retirement.get(key) == expected,
                f"{branch_id}.retirement.{key}",
                f"expected {expected!r}",
            )
        if status == "accepted":
            expected = {
                **exact_common,
                "status": "due",
                "retired_at": None,
                "retired_by": None,
                "ancestry_checkpoint_id": None,
            }
            self.problems.require(
                retirement == expected,
                f"{branch_id}.retirement",
                f"accepted branch must have exact due retirement state {expected!r}",
            )
        elif status == "retired":
            self.problems.require(
                retirement.get("status") == "retired"
                and retirement.get("retired_by") == "primary-human"
                and retirement.get("ancestry_checkpoint_id")
                == SUCCESSOR_CHECKPOINT_ID,
                f"{branch_id}.retirement",
                "retired branch must be retired by primary-human against exact C0001 ancestry",
            )
            retired_at = retirement.get("retired_at")
            self.problems.require(
                isinstance(retired_at, str)
                and RFC3339_RE.fullmatch(retired_at) is not None,
                f"{branch_id}.retirement.retired_at",
                "expected an RFC3339 retirement timestamp with timezone",
            )

    def git_tree_paths(self, revision: str) -> list[str]:
        try:
            output = self.git("ls-tree", "-r", "--name-only", revision).stdout
        except RuntimeError as error:
            self.problems.add("git tree", str(error))
            return []
        return [normalize_path(line) for line in output.splitlines() if line]

    def validate_delivery_scope(
        self,
        branch_id: str,
        facts: dict[str, Any],
        owned: list[PathRule],
        destinations: list[PathRule],
        forbidden: list[PathRule],
    ) -> None:
        delivery_sha = facts["delivery_sha"]
        ancestry = self.git(
            "merge-base", "--is-ancestor", CODE_SHA, delivery_sha, check=False
        )
        self.problems.require(
            ancestry.returncode == 0,
            f"{branch_id}.delivery",
            f"immutable delivery {delivery_sha} must descend from {CODE_SHA}",
        )
        try:
            output = self.git(
                "diff",
                "--name-status",
                "--no-renames",
                f"{CODE_SHA}..{delivery_sha}",
            ).stdout
        except RuntimeError as error:
            self.problems.add(f"{branch_id}.delivery scope", str(error))
            return
        rows: list[tuple[str, str]] = []
        for index, line in enumerate(output.splitlines(), 1):
            fields = line.split("\t")
            if len(fields) != 2 or fields[0] not in {"A", "M", "D"}:
                self.problems.add(
                    f"{branch_id}.delivery scope[{index}]",
                    f"malformed no-renames name-status row {line!r}",
                )
                continue
            rows.append((fields[0], normalize_path(fields[1])))
        self.problems.require(
            len(rows) == facts["changed_paths"],
            f"{branch_id}.delivery scope",
            f"expected {facts['changed_paths']} actual paths, found {len(rows)}",
        )
        self.problems.require(
            len({path for _, path in rows}) == len(rows),
            f"{branch_id}.delivery scope",
            "actual diff contains duplicate paths",
        )
        authorized = owned + destinations
        for status, path in rows:
            context = f"{branch_id}.delivery scope[{path}]"
            if not any(rule.matches(path) for rule in authorized):
                self.problems.add(context, "path is outside owner/destination authority")
            if any(rule.matches(path) for rule in forbidden):
                self.problems.add(context, "path is forbidden")
            if any(rule.matches(path) for rule in self.shared_rules):
                self.problems.add(context, "path is integrator-shared")
            parts = set(PurePosixPath(path).parts)
            if (
                parts & GENERATED_PARTS
                or PurePosixPath(path).suffix in GENERATED_SUFFIXES
                or path.startswith(GENERATED_PREFIXES)
            ):
                self.problems.add(context, "path is prohibited generated output")
            if status == "D":
                self.problems.add(context, "delivery may not delete a scoped path")

        evidence_path = self.root / facts["scope_evidence"]
        if branch_id == "B0001":
            try:
                evidence_text = evidence_path.read_text(encoding="utf-8")
            except OSError as error:
                self.problems.add(f"{branch_id}.delivery.scope_evidence", str(error))
            else:
                evidence_rows = re.findall(
                    r"(?m)^- `([AMD])` `([^`]+)`$", evidence_text
                )
                self.problems.require(
                    Counter(evidence_rows) == Counter(rows),
                    f"{branch_id}.delivery.scope_evidence",
                    "worker CHANGED_PATHS ledger must exactly equal the 98-row diff",
                )
        else:
            _, evidence_rows = self.read_tsv(
                evidence_path,
                self.relative(evidence_path),
                DELIVERY_SCOPE_HEADER,
            )
            parsed = [(row.get("status", ""), row.get("path", "")) for row in evidence_rows]
            self.problems.require(
                parsed == rows,
                f"{branch_id}.delivery.scope_evidence",
                "primary-human intake ledger must exactly equal the ordered 145-row diff",
            )
            categories = Counter()
            for status, path in rows:
                if path in R02_PATHS:
                    categories["owners"] += 1
                    if status != "M":
                        self.problems.add(path, "R02 owner must be modified")
                elif path.startswith("NumStabilityTest/Reorganization/R02/"):
                    categories["tests"] += 1
                elif path.startswith("docs/architecture/deliveries/R02/"):
                    categories["evidence"] += 1
                else:
                    categories["destinations"] += 1
                if path not in R02_PATHS and status != "A":
                    self.problems.add(path, "R02 non-owner delivery path must be added")
            expected = Counter(
                {"owners": 28, "destinations": 14, "tests": 63, "evidence": 40}
            )
            self.problems.require(
                categories == expected,
                f"{branch_id}.delivery scope classes",
                f"expected {dict(expected)}, found {dict(categories)}",
            )
            audit_path = self.phase_dir / "reviews/R02-intake-audit.md"
            try:
                audit = audit_path.read_text(encoding="utf-8")
            except OSError as error:
                self.problems.add(self.relative(audit_path), str(error))
            else:
                ledger_digest = sha256_path(evidence_path)
                for token in (
                    delivery_sha,
                    ledger_digest,
                    "113",
                    "145",
                    "28 owners",
                    "14 destinations",
                    "63",
                    "40",
                    "zero paths outside",
                    "142 relocated",
                    "123-row",
                    "P0002 replay records PASS",
                ):
                    if token.casefold() not in audit.casefold():
                        self.problems.add(
                            self.relative(audit_path), f"missing intake token {token!r}"
                        )

    def evidence_for(self, branch_id: str, filename: str) -> Artifact | None:
        expected = self.relative(self.phase_dir / "branches" / filename)
        matches = [item for item in self.branch_evidence.get(branch_id, []) if item.path == expected]
        if len(matches) != 1:
            self.problems.add(
                f"{branch_id}.refresh.evidence",
                f"must hash-pin exactly one {expected}",
            )
            return None
        return matches[0]

    def validate_routes_and_tests(self) -> None:
        route_header = (
            "baseline_owner_module",
            "baseline_declaration_name",
            "visibility",
            "kind",
            "baseline_order",
            "destination_module",
            "route_class",
            "normalization_decision",
        )
        private_header = ("old_private", "new_private", "destination_module")
        for branch_id, facts in BRANCH_FACTS.items():
            filenames = {
                "routes": f"{branch_id}-declaration-routes.tsv",
                "private": f"{branch_id}-private-normalization.tsv",
                "modules": f"{branch_id}-module-routes.tsv",
                "tests": f"{branch_id}-test-plan.tsv",
                "closure": f"{branch_id}-private-closure.tsv",
            }
            artifacts = {
                key: self.evidence_for(branch_id, filename)
                for key, filename in filenames.items()
            }
            route_path = self.phase_dir / "branches" / filenames["routes"]
            _, routes = self.read_tsv(
                route_path, self.relative(route_path), route_header
            )
            self.problems.require(
                len(routes) == facts["declarations"],
                self.relative(route_path),
                f"expected {facts['declarations']} exact declaration routes, found {len(routes)}",
            )
            identities = [
                (row.get("baseline_owner_module", ""), row.get("baseline_declaration_name", ""))
                for row in routes
            ]
            if len(identities) != len(set(identities)):
                self.problems.add(self.relative(route_path), "duplicate baseline declaration route")
            if identities != sorted(identities, key=lambda item: (item[0], self.numeric_order(routes, item))):
                # The exact order is independently frozen by baseline_order; only enforce
                # that baseline_order is a positive, unique integer per owner below.
                pass
            by_owner_orders: dict[str, list[int]] = defaultdict(list)
            private_names: set[str] = set()
            selector_modules = {module_from_path(path) for path in facts["paths"]}
            for index, row in enumerate(routes):
                owner = row.get("baseline_owner_module", "")
                declaration = row.get("baseline_declaration_name", "")
                destination = row.get("destination_module", "")
                decision = row.get("normalization_decision", "")
                if owner not in selector_modules:
                    self.problems.add(
                        f"{self.relative(route_path)}[{index}]",
                        f"owner {owner!r} is absent from the selector",
                    )
                if not declaration or not destination:
                    self.problems.add(
                        f"{self.relative(route_path)}[{index}]",
                        "declaration and destination_module must be nonempty",
                    )
                if not decision or DEFERRED_RE.search(decision):
                    self.problems.add(
                        f"{self.relative(route_path)}[{index}]",
                        "normalization decision must be explicit and reviewed before activation",
                    )
                try:
                    order = int(row.get("baseline_order", ""))
                    if order < 1:
                        raise ValueError
                except ValueError:
                    self.problems.add(
                        f"{self.relative(route_path)}[{index}].baseline_order",
                        "expected a positive integer",
                    )
                else:
                    by_owner_orders[owner].append(order)
                visibility = row.get("visibility", "").casefold()
                if visibility == "private":
                    private_names.add(declaration)
                elif visibility != "public":
                    self.problems.add(
                        f"{self.relative(route_path)}[{index}].visibility",
                        "expected public or private",
                    )
            self.problems.require(
                len(private_names) == facts["private"],
                self.relative(route_path),
                f"expected {facts['private']} private declaration routes, found {len(private_names)}",
            )
            for owner, orders in by_owner_orders.items():
                if len(orders) != len(set(orders)):
                    self.problems.add(self.relative(route_path), f"duplicate baseline_order in {owner}")
            private_path = self.phase_dir / "branches" / filenames["private"]
            _, private_rows = self.read_tsv(
                private_path, self.relative(private_path), private_header
            )
            self.problems.require(
                len(private_rows) == facts["private"],
                self.relative(private_path),
                f"expected {facts['private']} private normalizations, found {len(private_rows)}",
            )
            old_private = {row.get("old_private", "") for row in private_rows}
            self.problems.require(
                len(old_private) == len(private_rows) and "" not in old_private,
                self.relative(private_path),
                "old_private values must be nonempty and unique",
            )
            if old_private != private_names:
                self.problems.add(
                    self.relative(private_path),
                    f"private map must exactly cover route privates; missing={sorted(private_names-old_private)}, extra={sorted(old_private-private_names)}",
                )
            for index, row in enumerate(private_rows):
                for key in private_header:
                    value = row.get(key, "")
                    if not value or DEFERRED_RE.search(value):
                        self.problems.add(
                            f"{self.relative(private_path)}[{index}].{key}",
                            "private normalization must be explicit; no deferred worker decision",
                        )
            module_path = self.phase_dir / "branches" / filenames["modules"]
            module_header, module_rows = self.read_tsv(module_path, self.relative(module_path))
            module_column = self.choose_column(
                module_header, "module", "owner_module", "baseline_owner_module"
            )
            count_column = self.choose_column(module_header, "declaration_count", "baseline_declaration_count")
            if module_column is None or count_column is None:
                self.problems.add(
                    self.relative(module_path),
                    "module routes require module and declaration_count columns",
                )
            else:
                module_names = [row.get(module_column, "") for row in module_rows]
                self.problems.require(
                    set(module_names) == selector_modules and len(module_names) == len(selector_modules),
                    self.relative(module_path),
                    "module routes must cover every and only selector owner once",
                )
                counts: list[int] = []
                for index, row in enumerate(module_rows):
                    try:
                        value = int(row.get(count_column, ""))
                        if value < 0:
                            raise ValueError
                    except ValueError:
                        self.problems.add(
                            f"{self.relative(module_path)}[{index}].{count_column}",
                            "expected a nonnegative integer",
                        )
                    else:
                        counts.append(value)
                self.problems.require(
                    sum(counts) == facts["declarations"],
                    self.relative(module_path),
                    f"module declaration counts must sum to {facts['declarations']}",
                )
                self.problems.require(
                    sum(value == 0 for value in counts) == facts["declaration_free"],
                    self.relative(module_path),
                    f"expected {facts['declaration_free']} declaration-free modules",
                )
            closure_path = self.phase_dir / "branches" / filenames["closure"]
            closure_header, closure_rows = self.read_tsv(closure_path, self.relative(closure_path))
            closure_text = "\n".join("\t".join(row.values()) for row in closure_rows)
            self.problems.require(
                len(closure_rows) >= facts["private"],
                self.relative(closure_path),
                "full-graph private closure cannot be smaller than the selected private set",
            )
            for name in private_names:
                if name not in closure_text:
                    self.problems.add(self.relative(closure_path), f"private closure omits {name}")
            if not any("closure" in column.casefold() for column in closure_header):
                self.problems.add(self.relative(closure_path), "private closure TSV needs an explicit closure column")
            test_path = self.phase_dir / "branches" / filenames["tests"]
            test_header, test_rows = self.read_tsv(test_path, self.relative(test_path))
            class_column = self.choose_column(test_header, "test_class", "class", "plan_class")
            if class_column is None:
                self.problems.add(self.relative(test_path), "test plan requires a test_class column")
            else:
                found = {
                    row.get(class_column, "").casefold().replace("_", "-")
                    for row in test_rows
                }
                missing_classes = sorted(TEST_CLASSES - found)
                if missing_classes:
                    self.problems.add(
                        self.relative(test_path),
                        "missing test-plan class(es): " + ", ".join(missing_classes),
                    )
                for index, row in enumerate(test_rows):
                    joined = " ".join(row.values())
                    if DEFERRED_RE.search(joined):
                        self.problems.add(
                            f"{self.relative(test_path)}[{index}]",
                            "test plan may not defer design to the worker",
                        )

    @staticmethod
    def numeric_order(rows: list[dict[str, str]], identity: tuple[str, str]) -> int:
        for row in rows:
            if (
                row.get("baseline_owner_module", ""),
                row.get("baseline_declaration_name", ""),
            ) == identity:
                try:
                    return int(row.get("baseline_order", "0"))
                except ValueError:
                    return 0
        return 0

    @staticmethod
    def choose_column(header: Sequence[str], *names: str) -> str | None:
        for name in names:
            if name in header:
                return name
        return None

    def validate_projections(self) -> None:
        expected_status = (
            "active"
            if self.current_checkpoint_id == CHECKPOINT_ID
            else "retired"
        )
        for branch_id, facts in BRANCH_FACTS.items():
            projection_id = facts["projection"]
            path = self.phase_dir / f"projections/{projection_id}.json"
            projection = self.read_json(path, self.relative(path))
            if projection is None:
                continue
            for key, expected in {
                "schema_version": 1,
                "record_kind": "baseline_projection",
                "phase_id": PHASE_ID,
                "projection_id": projection_id,
                "wave_id": facts["wave"],
                "base_checkpoint_id": CHECKPOINT_ID,
                "status": expected_status,
            }.items():
                self.problems.require(
                    projection.get(key) == expected,
                    f"{projection_id}.{key}",
                    f"expected {expected!r}",
                )
            selector = projection.get("selector")
            selector_artifact = None
            if not isinstance(selector, dict) or selector.get("kind") != "module_path_tsv":
                self.problems.add(f"{projection_id}.selector", "expected module_path_tsv selector")
            else:
                selector_artifact = self.artifact(
                    selector.get("artifact"), f"{projection_id}.selector.artifact"
                )
            expected_selector = self.relative(
                self.phase_dir / f"selectors/{facts['wave']}.tsv"
            )
            if selector_artifact is not None:
                self.problems.require(
                    selector_artifact.path == expected_selector,
                    f"{projection_id}.selector.artifact.path",
                    f"expected {expected_selector}",
                )
            graph = self.artifact(
                projection.get("projection_graph"), f"{projection_id}.projection_graph"
            )
            if graph is not None:
                counts = self.parse_projection_graph(self.root / graph.path, projection_id)
                declared = projection.get("expected_counts")
                if not isinstance(declared, dict):
                    self.problems.add(f"{projection_id}.expected_counts", "expected an object")
                else:
                    for key, actual in counts.items():
                        self.problems.require(
                            declared.get(key) == actual,
                            f"{projection_id}.expected_counts.{key}",
                            f"expected actual graph count {actual}, found {declared.get(key)!r}",
                        )
                    self.problems.require(
                        counts.get("signature_edges", 0) > 0 and counts.get("body_edges", 0) > 0,
                        f"{projection_id}.projection_graph",
                        "format-2 graph must contain signature and body/proof edges",
                    )
            combined = self.artifact(
                projection.get("combined_baseline"), f"{projection_id}.combined_baseline"
            )
            if combined is not None and "C0000-combined" not in combined.path:
                self.problems.add(
                    f"{projection_id}.combined_baseline.path",
                    "projection must be rooted in C0000 combined baseline",
                )

    def parse_projection_graph(self, path: Path, context: str) -> dict[str, int]:
        declarations = 0
        signature = 0
        body = 0
        union: set[tuple[str, str]] = set()
        try:
            with gzip.open(path, "rt", encoding="utf-8", newline="") as handle:
                first = handle.readline().rstrip("\n")
                if first != "format\t2":
                    self.problems.add(context, "projection graph must start with format<TAB>2")
                for number, line in enumerate(handle, 2):
                    fields = line.rstrip("\n").split("\t")
                    if not fields or fields == [""]:
                        continue
                    if fields[0] == "declaration" and len(fields) == 5:
                        declarations += 1
                    elif fields[0] == "edge" and len(fields) == 4:
                        kind, source, target = fields[1:]
                        if kind == "signature":
                            signature += 1
                        elif kind == "body":
                            body += 1
                        else:
                            self.problems.add(context, f"unknown edge kind {kind!r} at line {number}")
                        union.add((source, target))
                    else:
                        self.problems.add(context, f"malformed format-2 row at line {number}")
        except (OSError, UnicodeError, gzip.BadGzipFile) as error:
            self.problems.add(context, f"cannot parse projection graph: {error}")
        return {
            "declarations": declarations,
            "signature_edges": signature,
            "body_edges": body,
            "union_edges": len(union),
        }

    def validate_overlap_reviews(self) -> None:
        for branch_id in BRANCH_FACTS:
            filename = f"{branch_id}-overlap-review.md"
            artifact = self.evidence_for(branch_id, filename)
            path = self.phase_dir / "branches" / filename
            try:
                text = path.read_text(encoding="utf-8")
            except OSError as error:
                self.problems.add(self.relative(path), f"cannot read overlap review: {error}")
                continue
            folded = " ".join(text.casefold().replace("_", "-").split())
            has_directions = (
                ("r01" in folded and "r02" in folded)
                and (
                    "either direction" in folded
                    or "both directions" in folded
                    or (
                        "ordered comparison" in folded
                        and folded.count("r01") >= 2
                        and folded.count("r02") >= 2
                    )
                    or ("r01 -> r02" in folded and "r02 -> r01" in folded)
                    or ("r01 → r02" in folded and "r02 → r01" in folded)
                    or ("r01-to-r02" in folded and "r02-to-r01" in folded)
                )
            )
            self.problems.require(
                has_directions,
                self.relative(path),
                "must prove R01/R02 results in both directions",
            )
            for name, tokens in OVERLAP_CATEGORIES.items():
                token_positions = [folded.find(token) for token in tokens]
                present = all(position >= 0 for position in token_positions)
                zero_near = False
                if present:
                    start = max(0, min(token_positions) - 80)
                    end = min(len(folded), max(token_positions) + 180)
                    window = folded[start:end]
                    zero_near = bool(re.search(r"\bzero\b|(?:^|\D)0(?:\D|$)", window))
                self.problems.require(
                    present and zero_near,
                    self.relative(path),
                    f"must explicitly declare zero {name} result",
                )
            for token in ("matrixalgebra", "c0000", "reviewed union"):
                if token not in folded.replace("/", "").replace(" ", "") and token not in folded:
                    self.problems.add(self.relative(path), f"missing joint-review token {token!r}")

    def validate_requests_and_postimages(self) -> None:
        request_dir = self.phase_dir / "requests"
        expected_status = (
            "active"
            if self.current_checkpoint_id == CHECKPOINT_ID
            else "applied"
        )
        request_specs = [
            ("R0001", "B0001"),
            ("R0002", "B0002"),
            ("R0002T", "B0002"),
        ]
        for request_id, branch_id in request_specs:
            path = request_dir / f"{request_id}.json"
            request = self.read_json(path, self.relative(path))
            if request is None:
                continue
            self.requests[request_id] = request
            facts = BRANCH_FACTS[branch_id]
            for key, expected in {
                "schema_version": 1,
                "record_kind": "shared_file_request",
                "phase_id": PHASE_ID,
                "request_id": request_id,
                "lane_id": facts["lane"],
                "wave_id": facts["wave"],
                "requester_id": (
                    "primary-human" if request_id == "R0002T" else facts["operator"]
                ),
                "target_checkpoint_id": CHECKPOINT_ID,
                "target_base_sha": CODE_SHA,
                "valid_through_checkpoint_id": CHECKPOINT_ID,
                "status": expected_status,
            }.items():
                self.problems.require(
                    request.get(key) == expected,
                    f"{request_id}.{key}",
                    f"expected {expected!r}, found {request.get(key)!r}",
                )
            paths = request.get("paths") if isinstance(request.get("paths"), list) else []
            if paths != sorted(set(paths)):
                self.problems.add(f"{request_id}.paths", "paths must be sorted and unique")
            self.problems.require(
                (
                    set(paths) == R0002T_PATHS
                    if request_id == "R0002T"
                    else facts["consumers"] <= set(paths)
                ),
                f"{request_id}.paths",
                (
                    f"must equal exact supplemental paths {sorted(R0002T_PATHS)}"
                    if request_id == "R0002T"
                    else "must include every required clean consumer postimage"
                ),
            )
            preimages = request.get("preimage_blobs") if isinstance(request.get("preimage_blobs"), list) else []
            parsed_preimages: dict[str, str | None] = {}
            for index, item in enumerate(preimages):
                if not isinstance(item, dict) or set(item) != {"path", "blob_oid"}:
                    self.problems.add(f"{request_id}.preimage_blobs[{index}]", "expected exactly path/blob_oid")
                    continue
                item_path, blob = item.get("path"), item.get("blob_oid")
                if isinstance(item_path, str) and (blob is None or isinstance(blob, str)):
                    parsed_preimages[item_path] = blob
                else:
                    self.problems.add(f"{request_id}.preimage_blobs[{index}]", "invalid preimage")
            self.problems.require(
                set(parsed_preimages) == set(paths),
                f"{request_id}.preimage_blobs",
                "preimage paths must exactly equal request paths",
            )
            for item_path, expected_blob in parsed_preimages.items():
                actual_blob = self.git_blob(CODE_SHA, item_path)
                self.problems.require(
                    actual_blob == expected_blob,
                    f"{request_id}.preimage_blobs[{item_path}]",
                    f"expected C0000 blob {actual_blob!r}, found {expected_blob!r}",
                )
            patch = self.artifact(request.get("patch"), f"{request_id}.patch")
            patch_path: Path | None = None
            if patch is not None:
                expected_patch = self.relative(request_dir / f"{request_id}.patch")
                self.problems.require(
                    patch.path == expected_patch,
                    f"{request_id}.patch.path",
                    f"expected {expected_patch}",
                )
                patch_path = self.root / patch.path
            post_name = f"{request_id}-postimages.tsv"
            post_path = request_dir / post_name
            post_digest = sha256_path(post_path) if post_path.is_file() else None
            post_header, post_rows = self.read_tsv(post_path, self.relative(post_path))
            postimages = self.validate_postimage_rows(
                post_header,
                post_rows,
                self.relative(post_path),
                set(paths),
                "postimage_sha256",
            )
            if patch_path is not None:
                self.materialize_patch_postimages(
                    request_id,
                    patch_path,
                    set(paths),
                    postimages,
                )
            rationale = request.get("rationale") if isinstance(request.get("rationale"), str) else ""
            if post_digest is not None:
                self.problems.require(
                    post_digest in rationale.upper(),
                    f"{request_id}.rationale",
                    f"must hash-pin {post_name} at SHA-256 {post_digest}",
                )
            self.validate_request_lifecycle(request_id, request)
        expected_links = {
            "B0001": ["R0001"],
            "B0002": ["R0002", "R0002T"],
        }
        for branch_id, expected in expected_links.items():
            branch = self.branch_records.get(branch_id, {})
            linked = (
                branch.get("shared_request_ids")
                if isinstance(branch.get("shared_request_ids"), list)
                else []
            )
            self.problems.require(
                linked == expected,
                f"{branch_id}.shared_request_ids",
                f"expected exactly {expected}",
            )
        if {"R0001", "R0002"} <= set(self.requests):
            first, second = self.requests["R0001"], self.requests["R0002"]
            first_pre = {item["path"]: item["blob_oid"] for item in first.get("preimage_blobs", []) if isinstance(item, dict) and "path" in item and "blob_oid" in item}
            second_pre = {item["path"]: item["blob_oid"] for item in second.get("preimage_blobs", []) if isinstance(item, dict) and "path" in item and "blob_oid" in item}
            overlap = set(first_pre) & set(second_pre)
            expected_overlap = {"NumStability/Algorithms.lean"}
            self.problems.require(
                overlap == expected_overlap,
                "request overlap",
                "independent request overlap must be exactly "
                f"{sorted(expected_overlap)}, found {sorted(overlap)}",
            )
            for path in overlap:
                if first_pre[path] != second_pre[path]:
                    self.problems.add(
                        "request overlap",
                        f"{path} is not independently based on the same C0000 blob",
                    )
            union_path = request_dir / "R0001-R0002-union-postimages.tsv"
            header, rows = self.read_tsv(union_path, self.relative(union_path))
            union_expected = set(first.get("paths", [])) | set(second.get("paths", []))
            union_postimages = self.validate_postimage_rows(
                header,
                rows,
                self.relative(union_path),
                union_expected,
                "union_postimage_sha256",
            )
            union_patch_path = request_dir / "R0001-R0002-union.patch"
            union_patch_context = self.relative(union_patch_path)
            union_patch_digest = (
                sha256_path(union_patch_path) if union_patch_path.is_file() else ""
            )
            if not union_patch_digest:
                self.problems.add(
                    union_patch_context,
                    "missing reviewed-union patch rooted at exact C0000",
                )
            else:
                self.materialize_patch_postimages(
                    "R0001-R0002 reviewed union",
                    union_patch_path,
                    union_expected,
                    union_postimages,
                )
                for branch_id in ("B0001", "B0002"):
                    matches = [
                        item
                        for item in self.branch_evidence.get(branch_id, [])
                        if item.path == union_patch_context
                    ]
                    self.problems.require(
                        len(matches) == 1
                        and matches[0].sha256 == union_patch_digest,
                        f"{branch_id}.refresh.evidence",
                        "must hash-pin exactly one reviewed-union patch at SHA-256 "
                        f"{union_patch_digest}",
                    )
            review_path = request_dir / "R0001-R0002-union-review.md"
            review = ""
            try:
                review = review_path.read_text(encoding="utf-8")
            except OSError as error:
                self.problems.add(self.relative(review_path), f"cannot read union review: {error}")
            else:
                folded = " ".join(review.casefold().split())
                for token in ("r0001", "r0002", "c0000", CODE_SHA):
                    if token.casefold() not in folded:
                        self.problems.add(self.relative(review_path), f"missing union evidence token {token!r}")
                self.problems.require(
                    ("reviewed union" in folded)
                    or ("union postimage" in folded and "reconcil" in folded),
                    self.relative(review_path),
                    "must explicitly record the reviewed/reconciled union postimage",
                )
                for path in sorted(overlap):
                    if path.casefold() not in folded:
                        self.problems.add(self.relative(review_path), f"union review omits overlap path {path}")
                if union_patch_digest and union_patch_digest.casefold() not in folded:
                    self.problems.add(
                        self.relative(review_path),
                        "union review must hash-pin reviewed-union patch SHA-256 "
                        f"{union_patch_digest}",
                    )
            union_manifest_digest = sha256_path(union_path) if union_path.is_file() else ""
            review_digest = sha256_path(review_path) if review_path.is_file() else ""
            for request_id in ("R0001", "R0002"):
                request = self.requests[request_id]
                rationale = str(request.get("rationale", "")).upper()
                for digest, label in (
                    (union_manifest_digest, "union postimages"),
                    (review_digest, "union review"),
                    (union_patch_digest, "reviewed-union patch"),
                ):
                    if digest and digest not in rationale:
                        self.problems.add(
                            f"{request_id}.rationale",
                            f"must hash-pin {label} SHA-256 {digest}",
                        )

    def validate_request_lifecycle(
        self, request_id: str, request: dict[str, Any]
    ) -> None:
        context = f"{request_id}.resolution"
        resolution = request.get("resolution")
        empty = {
            "checkpoint_id": None,
            "commit_sha": None,
            "reason": None,
            "resolved_at": None,
            "resolved_by": None,
            "validation_evidence": [],
        }
        if self.current_checkpoint_id == CHECKPOINT_ID:
            self.problems.require(
                resolution == empty,
                context,
                f"active C0000 request requires exact empty resolution {empty!r}",
            )
            return
        if not isinstance(resolution, dict):
            self.problems.add(context, "expected an object")
            return
        self.problems.require(
            set(resolution) == set(empty),
            context,
            f"expected exactly the resolution keys {sorted(empty)}",
        )
        for key, expected in {
            "checkpoint_id": SUCCESSOR_CHECKPOINT_ID,
            "commit_sha": INTEGRATED_CODE_SHA,
            "resolved_by": "primary-human",
        }.items():
            self.problems.require(
                resolution.get(key) == expected,
                f"{context}.{key}",
                f"expected {expected!r}, found {resolution.get(key)!r}",
            )
        reason = resolution.get("reason")
        self.problems.require(
            isinstance(reason, str) and bool(reason.strip()),
            f"{context}.reason",
            "applied request requires a nonempty reason",
        )
        resolved_at = resolution.get("resolved_at")
        self.problems.require(
            isinstance(resolved_at, str)
            and RFC3339_RE.fullmatch(resolved_at) is not None,
            f"{context}.resolved_at",
            "expected an RFC3339 resolution timestamp with timezone",
        )
        evidence = resolution.get("validation_evidence")
        artifacts: list[Artifact] = []
        if not isinstance(evidence, list) or not evidence:
            self.problems.add(
                f"{context}.validation_evidence",
                "applied request requires nonempty hash-pinned validation evidence",
            )
        else:
            for index, item in enumerate(evidence):
                artifact = self.artifact(
                    item, f"{context}.validation_evidence[{index}]"
                )
                if artifact is not None:
                    artifacts.append(artifact)
        expected_path, expected_digest = REQUEST_RESOLUTION_EVIDENCE[request_id]
        matches = [
            artifact
            for artifact in artifacts
            if artifact.path == expected_path
            and artifact.sha256 == expected_digest
        ]
        self.problems.require(
            len(matches) == 1,
            f"{context}.validation_evidence",
            "must contain exactly one immutable acceptance pin "
            f"{expected_path} at SHA-256 {expected_digest}",
        )

    def validate_postimage_rows(
        self,
        header: Sequence[str],
        rows: list[dict[str, str]],
        context: str,
        expected_paths: set[str],
        post_column: str,
    ) -> dict[str, str]:
        path_column = self.choose_column(header, "path", "shared_path")
        pre_column = self.choose_column(header, "preimage_blob_oid", "c0000_blob_oid", "base_blob_oid")
        pre_sha_column = self.choose_column(header, "preimage_sha256")
        if (
            path_column is None
            or pre_column is None
            or pre_sha_column is None
            or post_column not in header
        ):
            self.problems.add(
                context,
                "postimage TSV requires path, C0000 preimage blob/SHA-256, and exact "
                f"{post_column} column",
            )
            return {}
        paths = [row.get(path_column, "") for row in rows]
        self.problems.require(
            paths == sorted(set(paths)),
            context,
            "postimage rows must be sorted and unique by path",
        )
        self.problems.require(
            set(paths) == expected_paths,
            context,
            f"postimage paths must equal request union; missing={sorted(expected_paths-set(paths))}, extra={sorted(set(paths)-expected_paths)}",
        )
        postimages: dict[str, str] = {}
        for index, row in enumerate(rows):
            path = row.get(path_column, "")
            actual_pre = self.git_blob(CODE_SHA, path)
            self.problems.require(
                row.get(pre_column) == (actual_pre or "-"),
                f"{context}[{index}].{pre_column}",
                f"expected C0000 blob {(actual_pre or '-')!r}",
            )
            if actual_pre is not None:
                preimage = self.git_bytes(
                    "cat-file", "blob", actual_pre, check=False
                )
                if preimage.returncode:
                    detail = (preimage.stderr or preimage.stdout).decode(
                        "utf-8", errors="replace"
                    ).strip()
                    self.problems.add(
                        f"{context}[{index}].{pre_sha_column}",
                        f"cannot read C0000 preimage blob {actual_pre}: {detail}",
                    )
                else:
                    actual_pre_sha = hashlib.sha256(preimage.stdout).hexdigest().upper()
                    self.problems.require(
                        row.get(pre_sha_column, "").upper() == actual_pre_sha,
                        f"{context}[{index}].{pre_sha_column}",
                        f"expected C0000 content SHA-256 {actual_pre_sha}",
                    )
            post_digest = row.get(post_column, "")
            if not SHA256_RE.fullmatch(post_digest):
                self.problems.add(
                    f"{context}[{index}].{post_column}",
                    "postimage SHA-256 must be exactly 64 hexadecimal characters",
                )
            elif path:
                postimages[path] = post_digest.upper()
        return postimages

    def git_blob(self, revision: str, path: str) -> str | None:
        process = self.git("rev-parse", f"{revision}:{normalize_path(path)}", check=False)
        if process.returncode:
            return None
        value = process.stdout.strip()
        return value if SHA1_RE.fullmatch(value) else None

    def materialize_patch_postimages(
        self,
        context: str,
        patch: Path,
        expected_paths: set[str],
        expected_sha256: dict[str, str],
    ) -> None:
        """Apply *patch* to a disposable C0000 index and hash every result."""

        with tempfile.TemporaryDirectory(prefix="completion-phase-index-") as directory:
            index = Path(directory) / "index"
            env = os.environ.copy()
            env["GIT_INDEX_FILE"] = str(index)
            read = self.git("read-tree", CODE_SHA, check=False, env=env)
            if read.returncode:
                self.problems.add(
                    f"{context}.patch",
                    f"cannot initialize exact C0000 index: {read.stderr.strip()}",
                )
                return
            applied = self.git(
                "apply",
                "--cached",
                "--whitespace=nowarn",
                str(patch),
                check=False,
                env=env,
            )
            if applied.returncode:
                self.problems.add(
                    f"{context}.patch",
                    "does not materialize independently from exact C0000: "
                    f"{applied.stderr.strip() or applied.stdout.strip()}",
                )
                return
            changed_process = self.git(
                "diff",
                "--cached",
                "--name-only",
                "-z",
                CODE_SHA,
                "--",
                check=False,
                env=env,
            )
            if changed_process.returncode:
                self.problems.add(
                    f"{context}.patch",
                    "cannot enumerate materialized postimages: "
                    f"{changed_process.stderr.strip() or changed_process.stdout.strip()}",
                )
                return
            changed_paths = {
                normalize_path(path)
                for path in changed_process.stdout.split("\0")
                if path
            }
            self.problems.require(
                changed_paths == expected_paths,
                f"{context}.patch",
                "materialized changed paths must exactly equal manifest paths; "
                f"missing={sorted(expected_paths-changed_paths)}, "
                f"extra={sorted(changed_paths-expected_paths)}",
            )
            self.problems.require(
                set(expected_sha256) == expected_paths,
                f"{context}.postimages",
                "must provide exactly one valid SHA-256 for every manifest path; "
                f"missing={sorted(expected_paths-set(expected_sha256))}, "
                f"extra={sorted(set(expected_sha256)-expected_paths)}",
            )
            for path in sorted(expected_paths):
                expected = expected_sha256.get(path)
                if expected is None:
                    continue
                resolved = self.git(
                    "rev-parse",
                    "--verify",
                    f":{path}",
                    check=False,
                    env=env,
                )
                oid = resolved.stdout.strip()
                if resolved.returncode or not SHA1_RE.fullmatch(oid):
                    self.problems.add(
                        f"{context}.postimages[{path}]",
                        "cannot resolve materialized stage-0 blob: "
                        f"{resolved.stderr.strip() or resolved.stdout.strip()}",
                    )
                    continue
                content = self.git_bytes(
                    "cat-file", "blob", oid, check=False, env=env
                )
                if content.returncode:
                    detail = (content.stderr or content.stdout).decode(
                        "utf-8", errors="replace"
                    ).strip()
                    self.problems.add(
                        f"{context}.postimages[{path}]",
                        f"cannot read materialized blob {oid}: {detail}",
                    )
                    continue
                actual = hashlib.sha256(content.stdout).hexdigest().upper()
                self.problems.require(
                    actual == expected,
                    f"{context}.postimages[{path}]",
                    f"materialized SHA-256 mismatch: manifest {expected}, actual {actual}",
                )

    def validate_milestone_dag(self) -> None:
        path = self.phase_dir / "reviews/milestone-dag.tsv"
        header, rows = self.read_tsv(path, self.relative(path))
        edge_columns = {
            "importer_wave",
            "imported_wave",
            "direct_module_edges",
            "milestone_dependency",
            "reviewed_ordering_decision",
        }
        summary_columns = {
            "milestone_id",
            "wave_id",
            "depends_on",
            "direct_import_quotient_edges",
            "reviewed_ordering_decision",
        }
        edge_mode = edge_columns <= set(header)
        summary_mode = summary_columns <= set(header)
        if not edge_mode and not summary_mode:
            self.problems.add(
                self.relative(path),
                "milestone DAG requires either the edge-level or milestone-summary schema",
            )
            return
        scope_waves = {
            row.get("wave_id", "")
            for row in self.scope
            if row.get("phase_scope") == "in_scope"
        }
        worker_waves = scope_waves - {"I01"}
        phase_milestones = self.phase.get("milestones")
        if not isinstance(phase_milestones, list):
            self.problems.add("phase.json.milestones", "expected a list")
            return
        wave_to_milestone: dict[str, str] = {}
        dependencies: dict[str, set[str]] = {}
        for index, item in enumerate(phase_milestones):
            if not isinstance(item, dict):
                self.problems.add(f"phase.json.milestones[{index}]", "expected an object")
                continue
            milestone = item.get("milestone_id")
            waves = item.get("wave_ids")
            deps = item.get("depends_on")
            if not isinstance(milestone, str) or not isinstance(waves, list) or not isinstance(deps, list):
                self.problems.add(
                    f"phase.json.milestones[{index}]",
                    "requires milestone_id, wave_ids, and depends_on",
                )
                continue
            dependencies[milestone] = {value for value in deps if isinstance(value, str)}
            for wave in waves:
                if not isinstance(wave, str) or wave in wave_to_milestone:
                    self.problems.add(
                        f"phase.json.milestones[{index}]",
                        f"invalid or duplicate wave {wave!r}",
                    )
                else:
                    wave_to_milestone[wave] = milestone
        self.problems.require(
            set(wave_to_milestone) == scope_waves,
            "phase.json.milestones",
            f"milestones must cover every in-scope wave; missing={sorted(scope_waves-set(wave_to_milestone))}, extra={sorted(set(wave_to_milestone)-scope_waves)}",
        )
        known_milestones = set(dependencies)
        for milestone, deps in dependencies.items():
            unknown = deps - known_milestones
            if unknown:
                self.problems.add(self.relative(path), f"{milestone} has unknown dependencies {sorted(unknown)}")
        self.check_acyclic(dependencies, self.relative(path))
        live_edges = self.live_wave_import_edges(worker_waves)
        declared_edges: Counter[tuple[str, str]] = Counter()
        if edge_mode:
            edge_rows = [
                (index, row)
                for index, row in enumerate(rows)
                if row.get("importer_wave", "") not in {"", "-"}
            ]
            for index, row in edge_rows:
                importer = row.get("importer_wave", "")
                imported = row.get("imported_wave", "")
                context = f"{self.relative(path)}[{index}]"
                try:
                    count = int(row.get("direct_module_edges", ""))
                except ValueError:
                    count = 0
                self.record_dag_edge(
                    declared_edges,
                    importer,
                    imported,
                    count,
                    row.get("reviewed_ordering_decision", ""),
                    context,
                    worker_waves,
                    wave_to_milestone,
                    dependencies,
                    row.get("milestone_dependency", ""),
                )
        else:
            for index, row in enumerate(rows):
                context = f"{self.relative(path)}[{index}]"
                decision = row.get("reviewed_ordering_decision", "")
                if not decision or DEFERRED_RE.search(decision):
                    self.problems.add(context, "ordering decision must be explicit before activation")
                value = row.get("direct_import_quotient_edges", "")
                if value in {"", "-"}:
                    continue
                for encoded in split_values(value):
                    match = re.fullmatch(r"(R\d{2})->(R\d{2}):(\d+)", encoded)
                    if match is None:
                        self.problems.add(
                            context,
                            f"invalid direct-import quotient edge {encoded!r}",
                        )
                        continue
                    importer, imported, count_text = match.groups()
                    importer_milestone = wave_to_milestone.get(importer)
                    imported_milestone = wave_to_milestone.get(imported)
                    dependency_text = ""
                    if (
                        imported_milestone
                        and importer_milestone in dependencies.get(imported_milestone, set())
                    ):
                        dependency_text = f"{imported_milestone} depends on {importer_milestone}"
                    elif (
                        importer_milestone
                        and imported_milestone in dependencies.get(importer_milestone, set())
                    ):
                        dependency_text = f"{importer_milestone} depends on {imported_milestone}"
                    self.record_dag_edge(
                        declared_edges,
                        importer,
                        imported,
                        int(count_text),
                        decision,
                        context,
                        worker_waves,
                        wave_to_milestone,
                        dependencies,
                        dependency_text,
                    )
        if declared_edges != live_edges:
            self.problems.add(
                self.relative(path),
                "edge ledger must exactly equal live direct-import quotient; "
                f"missing={sorted((live_edges-declared_edges).items())}, "
                f"extra={sorted((declared_edges-live_edges).items())}",
            )
        milestone_columns = {"milestone_id", "wave_id", "depends_on"}
        if milestone_columns <= set(header):
            declared_milestones: dict[str, tuple[str, set[str]]] = {}
            for index, row in enumerate(rows):
                milestone = row.get("milestone_id", "")
                if milestone in {"", "-"}:
                    continue
                wave = row.get("wave_id", "")
                if milestone in declared_milestones or wave in {"", "-"}:
                    self.problems.add(
                        f"{self.relative(path)}[{index}]",
                        "milestone summary rows require unique milestone_id and wave_id",
                    )
                    continue
                declared_milestones[milestone] = (
                    wave,
                    set(split_values(row.get("depends_on", ""))),
                )
            expected_milestones = {
                milestone: (
                    next(wave for wave, owner in wave_to_milestone.items() if owner == milestone),
                    deps,
                )
                for milestone, deps in dependencies.items()
            }
            self.problems.require(
                declared_milestones == expected_milestones,
                self.relative(path),
                "milestone summary rows must exactly reproduce phase.json",
            )
        for wave in ("R01", "R02"):
            milestone = wave_to_milestone.get(wave)
            if milestone is not None and dependencies.get(milestone):
                self.problems.add(
                    self.relative(path),
                    f"activation wave {wave} must have no unaccepted successor dependencies",
                )

    def record_dag_edge(
        self,
        declared_edges: Counter[tuple[str, str]],
        importer: str,
        imported: str,
        count: int,
        decision: str,
        context: str,
        worker_waves: set[str],
        wave_to_milestone: dict[str, str],
        dependencies: dict[str, set[str]],
        dependency_text: str,
    ) -> None:
        if importer not in worker_waves or imported not in worker_waves or importer == imported:
            self.problems.add(context, "edge waves must be distinct known worker waves")
            return
        if count < 1:
            self.problems.add(context, "direct module-edge count must be positive")
            return
        declared_edges[importer, imported] += count
        if not decision or DEFERRED_RE.search(decision):
            self.problems.add(context, "ordering decision must be explicit before activation")
        match = re.fullmatch(r"(M\d{2}) depends on (M\d{2})", dependency_text)
        if match is None:
            self.problems.add(
                context,
                "direct-import endpoints must have a reviewed milestone dependency in one direction",
            )
            return
        milestone, dependency = match.groups()
        if dependency not in dependencies.get(milestone, set()):
            self.problems.add(
                context,
                f"{dependency_text} is absent from phase.json milestone dependencies",
            )
        endpoint_milestones = {
            wave_to_milestone.get(importer),
            wave_to_milestone.get(imported),
        }
        if {milestone, dependency} != endpoint_milestones:
            self.problems.add(
                context,
                "milestone dependency must order the two direct-import endpoint waves",
            )

    def check_acyclic(self, graph: dict[str, set[str]], context: str) -> None:
        visiting: set[str] = set()
        visited: set[str] = set()

        def visit(node: str) -> None:
            if node in visiting:
                self.problems.add(context, f"milestone dependency cycle includes {node}")
                return
            if node in visited:
                return
            visiting.add(node)
            for dependency in graph.get(node, set()):
                if dependency in graph:
                    visit(dependency)
            visiting.remove(node)
            visited.add(node)

        for node in graph:
            visit(node)

    def live_wave_import_edges(
        self, worker_waves: set[str]
    ) -> Counter[tuple[str, str]]:
        path_to_wave = {
            row["path"]: row["wave_id"]
            for row in self.scope
            if row.get("phase_scope") == "in_scope" and row.get("wave_id") in worker_waves
        }
        module_to_path = {module_from_path(path): path for path in path_to_wave}
        quotient: Counter[tuple[str, str]] = Counter()
        for path, wave in path_to_wave.items():
            source = self.root / path
            try:
                text = source.read_text(encoding="utf-8-sig", errors="replace")
            except OSError as error:
                self.problems.add("milestone import graph", f"cannot read {path}: {error}")
                continue
            for imported in IMPORT_RE.findall(remove_lean_comments(text)):
                target = module_to_path.get(imported)
                if target is None:
                    continue
                target_wave = path_to_wave[target]
                if target_wave != wave:
                    quotient[wave, target_wave] += 1
        return quotient


def run_self_test() -> int:
    problems = Problems()
    exact = PathRule("NumStability/A.lean", "exact")
    same = PathRule("numstability/a.lean", "exact")
    prefix = PathRule("NumStability", "prefix")
    distant = PathRule("NumStability/B", "prefix")
    problems.require(exact.intersects(same), "self-test", "casefold exact collision missed")
    problems.require(exact.intersects(prefix), "self-test", "exact/prefix collision missed")
    problems.require(exact.matches("NumStability/A.lean"), "self-test", "exact path match missed")
    problems.require(prefix.matches("NumStability/A.lean"), "self-test", "prefix path match missed")
    problems.require(not exact.intersects(distant), "self-test", "false path collision")
    problems.require(len(R01_PATHS) == 16, "self-test", "R01 constant drift")
    problems.require(len(R02_PATHS) == 28, "self-test", "R02 constant drift")
    problems.require(len(SHARED_CONSUMERS) == 11, "self-test", "shared consumer constant drift")
    problems.require(R01_PATHS.isdisjoint(R02_PATHS), "self-test", "selector constants overlap")
    problems.require(
        BRANCH_FACTS["B0001"]["changed_paths"] == 98
        and BRANCH_FACTS["B0002"]["changed_paths"] == 145,
        "self-test",
        "immutable delivery-scope counts drifted",
    )
    problems.require(
        R01_MERGE_PARENTS[1] == BRANCH_FACTS["B0001"]["delivery_sha"]
        and R02_MERGE_PARENTS
        == (R01_MERGE_SHA, BRANCH_FACTS["B0002"]["delivery_sha"]),
        "self-test",
        "exact merge-parent pins drifted from immutable deliveries",
    )
    problems.require(
        len(SUCCESSOR_GATE_IDS) == 12
        and SUCCESSOR_METRICS["production_modules"] == 2631
        and SUCCESSOR_MILESTONES == ["M01", "M02"],
        "self-test",
        "exact C0001 checkpoint contract drifted",
    )
    problems.require(
        RFC3339_RE.fullmatch("2026-08-11T22:00:00Z") is not None
        and RFC3339_RE.fullmatch("2026-08-11") is None,
        "self-test",
        "RFC3339 lifecycle timestamp matcher drifted",
    )
    with tempfile.TemporaryDirectory(prefix="completion-validator-self-test-") as directory:
        tsv = Path(directory) / "sample.tsv"
        tsv.write_text("module\tpath\nA\tA.lean\n", encoding="utf-8", newline="\n")
        digest = sha256_path(tsv)
        problems.require(SHA256_RE.fullmatch(digest) is not None, "self-test", "SHA-256 helper failed")
        raw = gzip.compress(
            b"format\t2\ndeclaration\tA.x\tA\ttheorem\tprivate\n"
            b"declaration\tB.y\tB\ttheorem\tpublic\n"
            b"edge\tsignature\tA.x\tB.y\nedge\tbody\tA.x\tB.y\n",
            mtime=0,
        )
        graph = Path(directory) / "graph.tsv.gz"
        graph.write_bytes(raw)
        validator = CompletionValidator(ROOT, DEFAULT_PHASE_DIR)
        counts = validator.parse_projection_graph(graph, "self-test graph")
        problems.require(
            counts
            == {
                "declarations": 2,
                "signature_edges": 1,
                "body_edges": 1,
                "union_edges": 1,
            },
            "self-test",
            f"projection counts drifted: {counts}",
        )
        cyclic_problems = Problems()
        validator.problems = cyclic_problems
        validator.check_acyclic({"M1": {"M2"}, "M2": {"M1"}}, "self-test cycle")
        problems.require(
            any("cycle" in message for message in cyclic_problems.messages),
            "self-test",
            "cycle was not rejected",
        )
    if problems.messages:
        for message in problems.messages:
            print(f"completion phase self-test failure: {message}", file=sys.stderr)
        return 1
    print(
        "completion phase self-test passed: exact selector constants, shared consumers, "
        "path collisions, SHA pins, format-2 signature/body parsing, and DAG cycle rejection"
    )
    return 0


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--phase-dir",
        type=Path,
        default=DEFAULT_PHASE_DIR,
        help=f"successor phase directory (default: {DEFAULT_PHASE_DIR.as_posix()})",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="run isolated positive/negative helper tests without phase artifacts",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    if args.self_test:
        return run_self_test()
    validator = CompletionValidator(ROOT, args.phase_dir)
    problems = validator.run()
    if problems.messages:
        for message in problems.messages:
            print(f"completion phase violation: {message}", file=sys.stderr)
        print(
            f"completion phase failed with {len(problems.messages)} violation(s)",
            file=sys.stderr,
        )
        return 1
    print(
        f"completion phase passed: {validator.current_checkpoint_id} control state, "
        "C0000-pinned 2,593-row freeze, 492-row scope, exact R01/R02 98/145-path "
        "delivery evidence, projections, routes, private closure, tests, "
        "overlap proofs, postimages, reviewed union, and milestone DAG"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
