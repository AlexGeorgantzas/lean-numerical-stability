#!/usr/bin/env python3
"""Validate the tracked repository-reorganization operating contract.

The contract is intentionally independent of Lean.  It ties an immutable,
complete production-module snapshot to reviewed Git checkpoints and validates
the phase, branch, request, projection, and completion state using only the
Python standard library and read-only Git commands.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path, PurePosixPath
from typing import Any, Iterable, Sequence

try:
    from check_phase_projection import InputError as ProjectionInputError
    from check_phase_projection import parse_projection
except ModuleNotFoundError:  # Support import as tools.architecture.check_phase.
    from tools.architecture.check_phase_projection import (
        InputError as ProjectionInputError,
    )
    from tools.architecture.check_phase_projection import parse_projection


ROOT = Path(__file__).resolve().parents[2]
PHASES_ROOT = Path("docs/architecture/phases")
ACTIVE_PHASE_POINTER = PHASES_ROOT / "active-phase.json"
LEGACY_DEFAULT_PHASE_DIR = PHASES_ROOT / "2026-08-repository-reorganization"

SCHEMA_VERSION = 1
SHA1_RE = re.compile(r"^[0-9a-f]{40}$")
SHA256_RE = re.compile(r"^[0-9A-Fa-f]{64}$")
ID_RE = re.compile(r"^[A-Za-z][A-Za-z0-9_-]*$")
CHECKPOINT_ID_RE = re.compile(r"^C[0-9]{4}$")
RECORD_FILE_RE = {
    "branches": re.compile(r"^B[0-9]{4}\.json$"),
    "checkpoints": re.compile(r"^C[0-9]{4}\.json$"),
    "projections": re.compile(r"^P[0-9]{4}\.json$"),
    "requests": re.compile(r"^R[0-9]{4}[A-Z]?\.json$"),
}

PHASE_STATUSES = {"draft", "active", "integration", "closed", "superseded", "cancelled"}
TERMINAL_PHASE_STATUSES = {"closed", "superseded", "cancelled"}
MILESTONE_STATUSES = {"planned", "ready", "accepted", "superseded", "cancelled"}
BRANCH_STATUSES = {
    "planned",
    "active",
    "delivered",
    "accepted",
    "retired",
    "superseded",
    "cancelled",
}
REQUEST_STATUSES = {
    "draft",
    "active",
    "applied",
    "rejected",
    "superseded",
    "expired",
    "withdrawn",
}
INTEGRATION_AMENDMENT_KIND = "integration_amendment"
INTEGRATION_AMENDMENT_MANIFEST_HEADER = (
    "path",
    "preimage_blob_oid",
    "preimage_sha256",
    "postimage_sha256",
)
PROJECTION_STATUSES = {"active", "retired", "superseded"}
GATE_STATUSES = {"PASS", "FAIL", "NOT_RUN", "NOT_APPLICABLE"}
COMPLETION_STATUSES = {"incomplete", "complete"}
PRINCIPAL_KINDS = {"human", "agent", "service"}
PATH_RULE_KINDS = {"exact", "prefix"}
REFRESH_DECISIONS = {"current", "rebased", "validated_no_overlap"}
RETIREMENT_STATUSES = {"not_due", "due", "retired", "preserved"}
INTEGRATION_METHODS = {"merge", "cherry_pick", "fast_forward", "squash", "manual_reconciliation"}
SCOPE_DISPOSITIONS = {"in_scope", "excluded", "deferred", "already_complete"}
TIERS = {"reusable", "source", "internal", "upstream", "mixed", "compatibility", "aggregate"}
PLANNED_ACTIONS = {
    "aggregate_cleanup",
    "classify",
    "compatibility_cleanup",
    "document",
    "entrypoint_cleanup",
    "migrate",
    "outlier_review",
    "provenance_review",
    "rename",
    "split",
}
LEGACY_KEYS = (
    "unclassified_modules",
    "mixed_modules",
    "missing_module_docstrings",
    "noncanonical_modules",
    "declaration_bearing_umbrellas",
    "unsorted_aggregate_imports",
)
METRIC_KEYS = (
    "production_modules",
    "unclassified_modules",
    "mixed_modules",
    "missing_module_docstrings",
    "noncanonical_modules",
    "declaration_bearing_umbrellas",
    "unsorted_aggregate_imports",
)
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

REQUIRED_REFRESH_ITEMS = {
    "baseline_projection",
    "inventory_snapshot",
    "overlap_review",
}
REQUIRED_BOUNDED_CONDITIONS = {
    "all_in_scope_waves_accepted",
    "all_required_milestones_satisfied",
    "current_checkpoint_gates_pass",
    "no_active_requests",
    "no_open_branches",
}
REQUIRED_REPOSITORY_GATES = {
    "architecture",
    "build_profiles",
    "canonical_layout",
    "classification_complete",
    "compatibility",
    "documentation_current",
    "entrypoint_reachability",
    "forbidden_reachability_zero",
    "full_build",
    "full_tests",
    "generated_artifacts_absent",
    "module_documentation",
    "outlier_review",
    "provenance",
}
REQUIRED_CHECKPOINT_GATES = {
    "architecture",
    "combined_baseline",
    "compatibility",
    "full_build",
    "full_tests",
    "layout",
    "provenance",
    "strict_source",
}
DECLARATION_FORMAT_VERSION = 2
SELECTOR_HEADER = ("module", "path")
UNCLASSIFIED_QUEUE_HEADER = (
    "module",
    "path",
    "wave_id",
    "lane_id",
    "inventory_source",
    "frozen_proposed_tier",
    "frozen_proposed_family",
    "review_status",
)
SEMANTIC_REVIEW_HEADER = (
    "module",
    "frozen_suggestion",
    "current_review_status",
    "required_correction",
)
QUEUE_REVIEW_STATUSES = {
    "confirmed_bad_route",
    "confirmed_source",
    "family_migration_required",
    "frozen_proposal_requires_refresh",
    "semantic_review_required",
}
SEMANTIC_REVIEW_STATUSES = {
    "confirmed_bad_route",
    "confirmed_source",
    "semantic_review_required",
}


class DuplicateKeyError(ValueError):
    """Raised when a JSON object repeats a key."""


@dataclass(frozen=True)
class Artifact:
    path: str
    sha256: str


@dataclass(frozen=True, order=True)
class PathRule:
    match: str
    path: str

    def matches(self, candidate: str) -> bool:
        if self.match == "exact":
            return candidate == self.path
        return candidate.startswith(self.path)

    def intersects(self, other: "PathRule") -> bool:
        if self.match == "exact" and other.match == "exact":
            return self.path == other.path
        if self.match == "exact":
            return other.matches(self.path)
        if other.match == "exact":
            return self.matches(other.path)
        return self.path.startswith(other.path) or other.path.startswith(self.path)


@dataclass
class ScopeSnapshot:
    metrics: dict[str, int]
    in_scope_waves: set[str]
    rows: list[dict[str, str]]


class Problems:
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
            print(f"error: malformed contract: {message}", file=sys.stderr)
        for message in sorted(set(self.contract_errors)):
            print(f"error: contract violation: {message}", file=sys.stderr)


def duplicate_safe_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise DuplicateKeyError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def is_rfc3339(value: str) -> bool:
    try:
        parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError:
        return False
    return parsed.tzinfo is not None


def is_repo_path(value: str, *, directory_prefix: bool = False) -> bool:
    if not value or "\\" in value or value.startswith("/"):
        return False
    if directory_prefix != value.endswith("/"):
        return False
    trimmed = value[:-1] if directory_prefix else value
    if not trimmed:
        return False
    path = PurePosixPath(trimmed)
    return not path.is_absolute() and all(part not in {"", ".", ".."} for part in path.parts)


def sorted_unique_strings(
    value: Any, context: str, problems: Problems, *, allow_empty: bool = True
) -> list[str]:
    if not isinstance(value, list) or not all(isinstance(item, str) and item for item in value):
        problems.malformed(context, "expected a list of nonempty strings")
        return []
    if not allow_empty and not value:
        problems.malformed(context, "list must not be empty")
    if len(value) != len(set(value)):
        problems.malformed(context, "list contains duplicate values")
    if value != sorted(value):
        problems.violation(context, "list must be sorted")
    return list(value)


def require_keys(
    value: Any,
    context: str,
    problems: Problems,
    required: Iterable[str],
    optional: Iterable[str] = (),
) -> dict[str, Any] | None:
    if not isinstance(value, dict):
        problems.malformed(context, "expected a JSON object")
        return None
    required_set = set(required)
    allowed = required_set | set(optional)
    missing = sorted(required_set - set(value))
    unexpected = sorted(set(value) - allowed)
    if missing:
        problems.malformed(context, "missing key(s): " + ", ".join(missing))
    if unexpected:
        problems.malformed(context, "unexpected key(s): " + ", ".join(unexpected))
    return value


def required_string(
    obj: dict[str, Any], key: str, context: str, problems: Problems, *, nullable: bool = False
) -> str | None:
    value = obj.get(key)
    if nullable and value is None:
        return None
    if not isinstance(value, str) or not value:
        problems.malformed(f"{context}.{key}", "expected a nonempty string" + (" or null" if nullable else ""))
        return None
    return value


class PhaseValidator:
    def __init__(self, root: Path, phase_dir: Path) -> None:
        self.root = root.resolve()
        self.phase_dir = phase_dir.resolve()
        self.problems = Problems()
        self.phase: dict[str, Any] = {}
        self.phase_id = ""
        self.principals: dict[str, dict[str, Any]] = {}
        self.lanes: dict[str, dict[str, Any]] = {}
        self.shared_paths: list[PathRule] = []
        self.milestones: dict[str, dict[str, Any]] = {}
        self.checkpoints: dict[str, dict[str, Any]] = {}
        self.checkpoint_inventory: dict[str, ScopeSnapshot] = {}
        self.projections: dict[str, dict[str, Any]] = {}
        self.branches: dict[str, dict[str, Any]] = {}
        self.requests: dict[str, dict[str, Any]] = {}
        self.scope_snapshot: ScopeSnapshot | None = None
        self._hash_cache: dict[Path, str] = {}
        self._snapshot_cache: dict[str, tuple[dict[str, tuple[str, str]], dict[str, str], dict[str, set[str]]]] = {}
        self._ancestor_cache: dict[tuple[str, str], bool] = {}

    def relative_context(self, path: Path) -> str:
        try:
            return path.resolve().relative_to(self.root).as_posix()
        except ValueError:
            return str(path)

    def resolve_repo_path(self, value: str, context: str) -> Path | None:
        if not is_repo_path(value):
            self.problems.malformed(context, "expected a normalized repository-relative POSIX file path")
            return None
        resolved = (self.root / PurePosixPath(value)).resolve()
        try:
            resolved.relative_to(self.root)
        except ValueError:
            self.problems.malformed(context, "path escapes the repository")
            return None
        return resolved

    def read_json_file(self, path: Path, context: str | None = None) -> dict[str, Any] | None:
        label = context or self.relative_context(path)
        try:
            text = path.read_text(encoding="utf-8")
            value = json.loads(text, object_pairs_hook=duplicate_safe_object)
        except (OSError, UnicodeError, json.JSONDecodeError, DuplicateKeyError) as error:
            self.problems.malformed(label, f"cannot read JSON: {error}")
            return None
        if not isinstance(value, dict):
            self.problems.malformed(label, "top-level JSON value must be an object")
            return None
        return value

    def artifact(self, value: Any, context: str, *, nullable: bool = False) -> Artifact | None:
        if nullable and value is None:
            return None
        obj = require_keys(value, context, self.problems, {"path", "sha256"})
        if obj is None:
            return None
        path_value = required_string(obj, "path", context, self.problems)
        digest = required_string(obj, "sha256", context, self.problems)
        if path_value is None or digest is None:
            return None
        if not SHA256_RE.fullmatch(digest):
            self.problems.malformed(f"{context}.sha256", "expected 64 hexadecimal characters")
            return None
        path = self.resolve_repo_path(path_value, f"{context}.path")
        if path is None:
            return None
        if not path.is_file():
            self.problems.malformed(context, f"referenced artifact is missing: {path_value}")
            return Artifact(path_value, digest.upper())
        actual = self._hash_cache.get(path)
        if actual is None:
            actual = hashlib.sha256(path.read_bytes()).hexdigest().upper()
            self._hash_cache[path] = actual
        if actual != digest.upper():
            self.problems.violation(context, f"SHA-256 mismatch for {path_value}: recorded {digest.upper()}, actual {actual}")
        return Artifact(path_value, digest.upper())

    def path_rules(self, value: Any, context: str) -> list[PathRule]:
        if not isinstance(value, list):
            self.problems.malformed(context, "expected a list of path-rule objects")
            return []
        result: list[PathRule] = []
        for index, item in enumerate(value):
            item_context = f"{context}[{index}]"
            obj = require_keys(item, item_context, self.problems, {"match", "path"})
            if obj is None:
                continue
            match = required_string(obj, "match", item_context, self.problems)
            path = required_string(obj, "path", item_context, self.problems)
            if match not in PATH_RULE_KINDS:
                self.problems.malformed(f"{item_context}.match", f"expected one of {sorted(PATH_RULE_KINDS)}")
                continue
            if path is None or not is_repo_path(path, directory_prefix=match == "prefix"):
                self.problems.malformed(f"{item_context}.path", "prefix paths must end in '/', exact paths must not, and all paths must be normalized repository-relative POSIX paths")
                continue
            result.append(PathRule(match, path))
        if len(result) != len(set(result)):
            self.problems.malformed(context, "contains duplicate path rules")
        if result != sorted(result):
            self.problems.violation(context, "path rules must be sorted by match and path")
        return result

    def patch_paths(
        self,
        artifact: Artifact | None,
        context: str,
        *,
        require_sorted: bool = True,
    ) -> list[str]:
        if artifact is None:
            return []
        path = self.resolve_repo_path(artifact.path, f"{context}.path")
        if path is None or not path.is_file():
            return []
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except (OSError, UnicodeError) as error:
            self.problems.malformed(context, f"cannot read patch: {error}")
            return []
        changed: list[str] = []
        for line_number, line in enumerate(lines, start=1):
            if not line.startswith("diff --git "):
                continue
            match = re.fullmatch(r"diff --git a/(\S+) b/(\S+)", line)
            if match is None:
                self.problems.malformed(
                    f"{context}:{line_number}",
                    "expected an unquoted `diff --git a/<path> b/<path>` header",
                )
                continue
            old_path, new_path = match.groups()
            if old_path != new_path:
                self.problems.violation(
                    f"{context}:{line_number}",
                    "shared-file requests must not rename files",
                )
                continue
            if not is_repo_path(old_path):
                self.problems.malformed(
                    f"{context}:{line_number}",
                    f"invalid patch path {old_path!r}",
                )
                continue
            changed.append(old_path)
        if not changed:
            self.problems.malformed(context, "patch contains no `diff --git` file header")
        if len(changed) != len(set(changed)):
            self.problems.malformed(context, "patch repeats a file diff")
        if require_sorted and changed != sorted(changed):
            self.problems.violation(context, "file diffs must be sorted by path")
        return changed

    def run_git(self, args: Sequence[str], context: str) -> bytes | None:
        try:
            completed = subprocess.run(
                ["git", *args],
                cwd=self.root,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
            )
        except OSError as error:
            self.problems.malformed(context, f"cannot run git: {error}")
            return None
        if completed.returncode != 0:
            detail = completed.stderr.decode("utf-8", errors="replace").strip()
            self.problems.violation(context, f"git {' '.join(args)} failed" + (f": {detail}" if detail else ""))
            return None
        return completed.stdout

    def commit_exists(self, sha: str, context: str) -> bool:
        if not SHA1_RE.fullmatch(sha):
            self.problems.malformed(context, "expected a lowercase 40-hex Git commit SHA")
            return False
        return self.run_git(["cat-file", "-e", f"{sha}^{{commit}}"], context) is not None

    def is_ancestor(self, ancestor: str, descendant: str, context: str) -> bool:
        key = (ancestor, descendant)
        if key in self._ancestor_cache:
            return self._ancestor_cache[key]
        try:
            completed = subprocess.run(
                ["git", "merge-base", "--is-ancestor", ancestor, descendant],
                cwd=self.root,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
            )
        except OSError as error:
            self.problems.malformed(context, f"cannot run git: {error}")
            return False
        if completed.returncode not in {0, 1}:
            detail = completed.stderr.decode("utf-8", errors="replace").strip()
            self.problems.violation(context, f"cannot compare Git ancestry: {detail}")
            return False
        answer = completed.returncode == 0
        self._ancestor_cache[key] = answer
        return answer

    def git_json_at(self, commit: str, path: str, context: str) -> dict[str, Any] | None:
        raw = self.run_git(["show", f"{commit}:{path}"], context)
        if raw is None:
            return None
        try:
            value = json.loads(raw.decode("utf-8"), object_pairs_hook=duplicate_safe_object)
        except (UnicodeError, json.JSONDecodeError, DuplicateKeyError) as error:
            self.problems.malformed(context, f"historical JSON is invalid: {error}")
            return None
        if not isinstance(value, dict):
            self.problems.malformed(context, "historical JSON must be an object")
            return None
        return value

    def snapshot_metadata(
        self, commit: str
    ) -> tuple[dict[str, tuple[str, str]], dict[str, str], dict[str, set[str]]] | None:
        if commit in self._snapshot_cache:
            return self._snapshot_cache[commit]
        context = f"snapshot {commit}"
        if not self.commit_exists(commit, context):
            return None
        raw = self.run_git(
            ["ls-tree", "-r", "-z", commit, "--", "NumStability.lean", "NumStability"],
            context,
        )
        if raw is None:
            return None
        modules: dict[str, tuple[str, str]] = {}
        for entry in raw.split(b"\0"):
            if not entry:
                continue
            try:
                metadata, path_raw = entry.split(b"\t", 1)
                _mode, kind, oid = metadata.decode("ascii").split()
                path = path_raw.decode("utf-8")
            except (ValueError, UnicodeError) as error:
                self.problems.malformed(context, f"cannot parse git ls-tree output: {error}")
                return None
            if kind != "blob" or not path.endswith(".lean"):
                continue
            module = ".".join(PurePosixPath(path).with_suffix("").parts)
            modules[module] = (path, oid)

        tiers = self.git_json_at(commit, "docs/architecture/tiers.json", context)
        layout = self.git_json_at(commit, "docs/architecture/layout-exceptions.json", context)
        if tiers is None or layout is None:
            return None
        if tiers.get("schema_version") != 1:
            self.problems.malformed(context, "historical tiers.json must use schema_version 1")
            return None
        allowed_tiers = tiers.get("tiers")
        exact = tiers.get("exact")
        prefixes = tiers.get("prefixes")
        if (
            not isinstance(allowed_tiers, list)
            or set(allowed_tiers) != TIERS
            or not isinstance(exact, dict)
            or not isinstance(prefixes, list)
        ):
            self.problems.malformed(context, "historical tiers.json has an unsupported structure")
            return None
        parsed_prefixes: list[tuple[str, str]] = []
        for rule in prefixes:
            if not isinstance(rule, dict) or set(rule) != {"prefix", "tier"}:
                self.problems.malformed(context, "historical tier prefix rule is malformed")
                return None
            prefix, tier = rule.get("prefix"), rule.get("tier")
            if not isinstance(prefix, str) or not prefix or tier not in TIERS:
                self.problems.malformed(context, "historical tier prefix rule is invalid")
                return None
            parsed_prefixes.append((prefix.rstrip("."), tier))
        parsed_prefixes.sort(key=lambda item: (-len(item[0]), item[0]))
        assignments: dict[str, str] = {}
        for module in sorted(modules):
            if module in exact:
                tier = exact[module]
                if tier not in TIERS:
                    self.problems.malformed(context, f"unknown tier {tier!r} for {module}")
                    return None
                assignments[module] = tier
                continue
            for prefix, tier in parsed_prefixes:
                if module == prefix or module.startswith(prefix + "."):
                    assignments[module] = tier
                    break

        if layout.get("schema_version") != 1 or not isinstance(layout.get("legacy"), dict):
            self.problems.malformed(context, "historical layout-exceptions.json has an unsupported structure")
            return None
        debt: dict[str, set[str]] = {module: set() for module in modules}
        legacy = layout["legacy"]
        for key in LEGACY_KEYS:
            values = legacy.get(key)
            if not isinstance(values, list) or not all(isinstance(item, str) for item in values):
                self.problems.malformed(context, f"historical legacy.{key} must be a list of module names")
                return None
            for module in values:
                if module not in modules:
                    self.problems.violation(context, f"historical legacy.{key} names missing module {module}")
                    continue
                debt[module].add(key)
        result = (modules, assignments, debt)
        self._snapshot_cache[commit] = result
        return result

    def validate_scope_snapshot(
        self,
        artifact: Artifact | None,
        commit: str,
        context: str,
    ) -> ScopeSnapshot | None:
        if artifact is None:
            return None
        path = self.resolve_repo_path(artifact.path, f"{context}.path")
        metadata = self.snapshot_metadata(commit)
        if path is None or metadata is None or not path.is_file():
            return None
        try:
            raw = path.read_bytes()
            text = raw.decode("utf-8")
        except (OSError, UnicodeError) as error:
            self.problems.malformed(context, f"cannot read TSV: {error}")
            return None
        if b"\r" in raw:
            self.problems.violation(context, "TSV must use LF line endings")
        if raw and not raw.endswith(b"\n"):
            self.problems.violation(context, "TSV must end with a newline")
        try:
            reader = csv.DictReader(text.splitlines(), delimiter="\t", strict=True)
            if tuple(reader.fieldnames or ()) != SCOPE_HEADER:
                self.problems.malformed(context, "TSV header must be exactly: " + "\t".join(SCOPE_HEADER))
                return None
            rows = list(reader)
        except csv.Error as error:
            self.problems.malformed(context, f"cannot parse TSV: {error}")
            return None
        modules_at_commit, tiers_at_commit, debt_at_commit = metadata
        seen: set[str] = set()
        modules_in_order: list[str] = []
        in_scope_waves: set[str] = set()
        for line_number, row in enumerate(rows, start=2):
            row_context = f"{context}:{line_number}"
            if None in row or any(value is None for value in row.values()):
                self.problems.malformed(row_context, "row has the wrong number of tab-separated fields")
                continue
            module = row["module"]
            modules_in_order.append(module)
            if not module or module in seen:
                self.problems.malformed(row_context, f"duplicate or empty module {module!r}")
                continue
            seen.add(module)
            expected = modules_at_commit.get(module)
            if expected is None:
                self.problems.violation(row_context, f"module is not a production module at {commit}: {module}")
                continue
            expected_path, expected_blob = expected
            if row["path"] != expected_path:
                self.problems.violation(row_context, f"path mismatch for {module}: expected {expected_path}, found {row['path']}")
            if row["base_blob_oid"] != expected_blob:
                self.problems.violation(row_context, f"blob mismatch for {module}: expected {expected_blob}, found {row['base_blob_oid']}")
            expected_tier = tiers_at_commit.get(module, "unclassified")
            if row["current_tier"] != expected_tier:
                self.problems.violation(row_context, f"tier mismatch for {module}: expected {expected_tier}, found {row['current_tier']}")
            debt_items = [] if row["debt_flags"] == "-" else row["debt_flags"].split(";")
            if debt_items != sorted(set(debt_items)) or any(item not in LEGACY_KEYS for item in debt_items):
                self.problems.malformed(row_context, "debt_flags must be '-' or a sorted unique semicolon-separated list of layout legacy keys")
            expected_debt = sorted(debt_at_commit[module])
            if debt_items != expected_debt:
                self.problems.violation(row_context, f"debt mismatch for {module}: expected {expected_debt or ['-']}, found {debt_items or ['-']}")
            disposition = row["phase_scope"]
            if disposition not in SCOPE_DISPOSITIONS:
                self.problems.malformed(row_context, f"phase_scope must be one of {sorted(SCOPE_DISPOSITIONS)}")
                continue
            lane, wave = row["lane_id"], row["wave_id"]
            actions = [] if row["planned_actions"] == "-" else row["planned_actions"].split(";")
            if actions != sorted(set(actions)) or any(action not in PLANNED_ACTIONS for action in actions):
                self.problems.malformed(row_context, "planned_actions must be '-' or a sorted unique semicolon-separated list of supported actions")
            if disposition == "in_scope":
                if lane == "-" or wave == "-" or not actions:
                    self.problems.malformed(row_context, "in_scope rows require lane_id, wave_id, and at least one planned action")
                else:
                    in_scope_waves.add(wave)
                    if lane not in self.lanes:
                        self.problems.violation(row_context, f"unknown lane_id {lane}")
            else:
                if lane != "-" or wave != "-":
                    self.problems.malformed(row_context, f"{disposition} rows must use '-' for lane_id and wave_id")
                if disposition == "already_complete" and actions:
                    self.problems.malformed(row_context, "already_complete rows must use '-' for planned_actions")
                if disposition in {"excluded", "deferred"} and row["rationale"] == "-":
                    self.problems.malformed(row_context, f"{disposition} rows require a rationale")
                if disposition == "already_complete" and expected_debt:
                    self.problems.violation(row_context, "a module with recorded architecture debt cannot be already_complete")
            if not row["rationale"]:
                self.problems.malformed(row_context, "rationale must not be empty; use '-' when not applicable")
        expected_modules = set(modules_at_commit)
        missing = sorted(expected_modules - seen)
        extra = sorted(seen - expected_modules)
        if missing:
            self.problems.violation(context, f"snapshot omits {len(missing)} production module(s): " + ", ".join(missing))
        if extra:
            self.problems.violation(context, f"snapshot has {len(extra)} extra module(s): " + ", ".join(extra))
        if modules_in_order != sorted(modules_in_order):
            self.problems.violation(context, "rows must be sorted by module")
        metrics = {"production_modules": len(modules_at_commit)}
        metrics.update(
            {
                key: sum(key in flags for flags in debt_at_commit.values())
                for key in LEGACY_KEYS
            }
        )
        return ScopeSnapshot(metrics=metrics, in_scope_waves=in_scope_waves, rows=rows)

    def parse_selector(
        self, artifact: Artifact | None, context: str
    ) -> list[dict[str, str]]:
        if artifact is None:
            return []
        path = self.resolve_repo_path(artifact.path, f"{context}.path")
        if path is None or not path.is_file():
            return []
        try:
            raw = path.read_bytes()
            text = raw.decode("utf-8")
        except (OSError, UnicodeError) as error:
            self.problems.malformed(context, f"cannot read selector TSV: {error}")
            return []
        if b"\r" in raw:
            self.problems.violation(context, "selector TSV must use LF line endings")
        if raw and not raw.endswith(b"\n"):
            self.problems.violation(context, "selector TSV must end with a newline")
        try:
            reader = csv.DictReader(text.splitlines(), delimiter="\t", strict=True)
            if tuple(reader.fieldnames or ()) != SELECTOR_HEADER:
                self.problems.malformed(
                    context,
                    "selector header must be exactly: " + "\t".join(SELECTOR_HEADER),
                )
                return []
            rows = list(reader)
        except csv.Error as error:
            self.problems.malformed(context, f"cannot parse selector TSV: {error}")
            return []
        modules: list[str] = []
        for line_number, row in enumerate(rows, start=2):
            row_context = f"{context}:{line_number}"
            if None in row or any(value is None for value in row.values()):
                self.problems.malformed(
                    row_context, "row has the wrong number of tab-separated fields"
                )
                continue
            module, module_path = row["module"], row["path"]
            if not module:
                self.problems.malformed(row_context, "module must not be empty")
            if not is_repo_path(module_path) or not module_path.endswith(".lean"):
                self.problems.malformed(
                    row_context,
                    "path must be a normalized repository-relative Lean file path",
                )
            modules.append(module)
        if not rows:
            self.problems.malformed(context, "selector must contain at least one row")
        if len(modules) != len(set(modules)):
            self.problems.malformed(context, "selector contains duplicate modules")
        if modules != sorted(modules):
            self.problems.violation(context, "selector rows must be sorted by module")
        return rows

    def parse_phase_tsv(
        self,
        artifact: Artifact | None,
        header: tuple[str, ...],
        context: str,
    ) -> list[dict[str, str]]:
        if artifact is None:
            return []
        path = self.resolve_repo_path(artifact.path, f"{context}.path")
        if path is None or not path.is_file():
            return []
        try:
            raw = path.read_bytes()
            text = raw.decode("utf-8")
        except (OSError, UnicodeError) as error:
            self.problems.malformed(context, f"cannot read TSV: {error}")
            return []
        if b"\r" in raw:
            self.problems.violation(context, "TSV must use LF line endings")
        if raw and not raw.endswith(b"\n"):
            self.problems.violation(context, "TSV must end with a newline")
        try:
            reader = csv.DictReader(text.splitlines(), delimiter="\t", strict=True)
            if tuple(reader.fieldnames or ()) != header:
                self.problems.malformed(
                    context, "TSV header must be exactly: " + "\t".join(header)
                )
                return []
            rows = list(reader)
        except csv.Error as error:
            self.problems.malformed(context, f"cannot parse TSV: {error}")
            return []
        modules: list[str] = []
        for line_number, row in enumerate(rows, start=2):
            row_context = f"{context}:{line_number}"
            if None in row or any(value is None for value in row.values()):
                self.problems.malformed(
                    row_context, "row has the wrong number of tab-separated fields"
                )
                continue
            empty_fields = sorted(key for key, value in row.items() if not value)
            if empty_fields:
                self.problems.malformed(
                    row_context,
                    "required field(s) must not be empty: " + ", ".join(empty_fields),
                )
            modules.append(row["module"])
        if len(modules) != len(set(modules)):
            self.problems.malformed(context, "TSV contains duplicate module rows")
        if modules != sorted(modules):
            self.problems.violation(context, "TSV rows must be sorted by module")
        return rows

    def validate_operational_queues(self) -> None:
        if self.scope_snapshot is None:
            return
        queue_context = "phase.json.unclassified_queue"
        queue_rows = self.parse_phase_tsv(
            self.phase.get("_unclassified_queue_artifact"),
            UNCLASSIFIED_QUEUE_HEADER,
            queue_context,
        )
        queue_by_module = {row["module"]: row for row in queue_rows if row["module"]}
        for line_number, row in enumerate(queue_rows, start=2):
            row_context = f"{queue_context}:{line_number}"
            if not is_repo_path(row["path"]) or not row["path"].endswith(".lean"):
                self.problems.malformed(
                    row_context,
                    "path must be a normalized repository-relative Lean file path",
                )
            if row["review_status"] not in QUEUE_REVIEW_STATUSES:
                self.problems.malformed(
                    f"{row_context}.review_status",
                    "expected one of " + ", ".join(sorted(QUEUE_REVIEW_STATUSES)),
                )
        expected_queue = {
            row["module"]: row
            for row in self.scope_snapshot.rows
            if row["current_tier"] == "unclassified"
        }
        missing = sorted(set(expected_queue) - set(queue_by_module))
        extra = sorted(set(queue_by_module) - set(expected_queue))
        if missing:
            self.problems.violation(
                queue_context,
                f"queue omits {len(missing)} immutable unclassified module(s): "
                + ", ".join(missing),
            )
        if extra:
            self.problems.violation(
                queue_context,
                f"queue contains {len(extra)} module(s) absent from immutable unclassified scope: "
                + ", ".join(extra),
            )
        for module in sorted(set(expected_queue) & set(queue_by_module)):
            expected = expected_queue[module]
            actual = queue_by_module[module]
            for key in ("path", "wave_id", "lane_id"):
                if actual[key] != expected[key]:
                    self.problems.violation(
                        f"{queue_context}.{module}.{key}",
                        f"expected {expected[key]!r} from immutable scope, found {actual[key]!r}",
                    )

        semantic_context = "phase.json.semantic_review"
        semantic_rows = self.parse_phase_tsv(
            self.phase.get("_semantic_review_artifact"),
            SEMANTIC_REVIEW_HEADER,
            semantic_context,
        )
        semantic_by_module = {
            row["module"]: row for row in semantic_rows if row["module"]
        }
        for line_number, row in enumerate(semantic_rows, start=2):
            if row["current_review_status"] not in SEMANTIC_REVIEW_STATUSES:
                self.problems.malformed(
                    f"{semantic_context}:{line_number}.current_review_status",
                    "expected one of " + ", ".join(sorted(SEMANTIC_REVIEW_STATUSES)),
                )
        expected_semantic = {
            module: row["review_status"]
            for module, row in queue_by_module.items()
            if row["review_status"] in SEMANTIC_REVIEW_STATUSES
        }
        missing_semantic = sorted(set(expected_semantic) - set(semantic_by_module))
        extra_semantic = sorted(set(semantic_by_module) - set(expected_semantic))
        if missing_semantic:
            self.problems.violation(
                semantic_context,
                f"semantic review omits {len(missing_semantic)} exceptional queue module(s): "
                + ", ".join(missing_semantic),
            )
        if extra_semantic:
            self.problems.violation(
                semantic_context,
                f"semantic review contains {len(extra_semantic)} module(s) without an exceptional queue status: "
                + ", ".join(extra_semantic),
            )
        for module in sorted(set(expected_semantic) & set(semantic_by_module)):
            actual_status = semantic_by_module[module]["current_review_status"]
            if actual_status != expected_semantic[module]:
                self.problems.violation(
                    f"{semantic_context}.{module}.current_review_status",
                    f"expected {expected_semantic[module]!r} from unclassified queue, found {actual_status!r}",
                )

    def validate_combined_baseline(
        self,
        checkpoint_id: str,
        commit: str,
        format_version: Any,
        artifact: Artifact | None,
        summary_artifact: Artifact | None,
    ) -> None:
        context = f"checkpoint {checkpoint_id} combined baseline"
        if artifact is None:
            return
        expected_path = self.relative_context(
            self.phase_dir / "baselines" / f"{checkpoint_id}-combined.json"
        )
        if artifact.path != expected_path:
            self.problems.violation(
                context,
                f"combined baseline must be {expected_path}",
            )
        expected_summary_path = self.relative_context(
            self.phase_dir / "baselines" / f"{checkpoint_id}-combined.md"
        )
        if summary_artifact is not None:
            if summary_artifact.path != expected_summary_path:
                self.problems.violation(
                    context,
                    f"combined baseline summary must be {expected_summary_path}",
                )
            summary_path = self.resolve_repo_path(
                summary_artifact.path, f"{context}.summary_artifact.path"
            )
            if summary_path is not None and summary_path.is_file():
                try:
                    summary_text = summary_path.read_text(encoding="utf-8")
                except (OSError, UnicodeError) as error:
                    self.problems.malformed(
                        context, f"cannot read combined baseline summary: {error}"
                    )
                else:
                    if f"- Commit: `{commit}`" not in summary_text:
                        self.problems.violation(
                            context,
                            "combined baseline summary must name the checkpoint commit",
                        )
        path = self.resolve_repo_path(artifact.path, f"{context}.path")
        if path is None or not path.is_file():
            return
        baseline = self.read_json_file(path, context)
        if baseline is None:
            return
        if baseline.get("schema_version") != 1:
            self.problems.malformed(context, "baseline schema_version must be 1")
        metadata = baseline.get("metadata")
        if not isinstance(metadata, dict):
            self.problems.malformed(context, "baseline metadata must be an object")
        else:
            if metadata.get("commit") != commit:
                self.problems.violation(
                    context,
                    "baseline metadata.commit must equal the checkpoint commit",
                )
            if metadata.get("library_source_clean") is not True:
                self.problems.violation(
                    context,
                    "baseline must be generated from a clean library source tree",
                )
            if metadata.get("library_source_dirty_paths") != []:
                self.problems.violation(
                    context,
                    "baseline metadata must record no dirty library source paths",
                )
        declarations = baseline.get("declarations")
        if not isinstance(declarations, dict):
            self.problems.malformed(
                context, "baseline must contain compiled declaration graph metadata"
            )
        elif declarations.get("format_version") != format_version:
            self.problems.violation(
                context,
                "baseline declaration format_version must match the checkpoint record",
            )

    def validate_projection_graph(
        self,
        projection_id: str,
        artifact: Artifact | None,
        expected_counts: Any,
        selector_rows: list[dict[str, str]],
    ) -> None:
        context = f"projection {projection_id}.projection_graph"
        if artifact is None:
            return
        expected_prefix = self.relative_context(
            self.phase_dir / "projections" / projection_id
        )
        if artifact.path not in {f"{expected_prefix}.tsv", f"{expected_prefix}.tsv.gz"}:
            self.problems.violation(
                context,
                f"projection graph must be {expected_prefix}.tsv or {expected_prefix}.tsv.gz",
            )
        path = self.resolve_repo_path(artifact.path, f"{context}.path")
        if path is None or not path.is_file():
            return
        try:
            graph = parse_projection(path)
        except ProjectionInputError as error:
            self.problems.malformed(context, str(error))
            return
        actual_counts = {
            "declarations": graph.declaration_count,
            "signature_edges": sum(
                edge.kind == "signature" for edge in graph.incident_edges
            ),
            "body_edges": sum(edge.kind == "body" for edge in graph.incident_edges),
            "union_edges": len(
                {(edge.source, edge.target) for edge in graph.incident_edges}
            ),
        }
        if isinstance(expected_counts, dict):
            for key, actual in actual_counts.items():
                if expected_counts.get(key) != actual:
                    self.problems.violation(
                        f"projection {projection_id}.expected_counts.{key}",
                        f"expected {actual} from projection graph, found {expected_counts.get(key)!r}",
                    )
        selected_modules = {row["module"] for row in selector_rows}
        unexpected_owners = sorted(
            {
                declaration.module
                for declaration in graph.declarations.values()
                if declaration.module not in selected_modules
            }
        )
        if unexpected_owners:
            self.problems.violation(
                context,
                "selected declarations have owners absent from the selector: "
                + ", ".join(unexpected_owners),
            )

    def load_phase(self) -> None:
        if not self.phase_dir.is_dir():
            self.problems.malformed(
                self.relative_context(self.phase_dir),
                "phase directory does not exist; create the phase contract or pass --phase-dir",
            )
            return
        phase_path = self.phase_dir / "phase.json"
        value = self.read_json_file(phase_path)
        if value is None:
            return
        required = {
            "schema_version",
            "record_kind",
            "phase_id",
            "title",
            "status",
            "created_at",
            "origin_checkpoint_id",
            "current_checkpoint_id",
            "scope",
            "unclassified_queue",
            "semantic_review",
            "base_policy",
            "authority",
            "shared_paths",
            "milestones",
            "completion",
        }
        obj = require_keys(value, "phase.json", self.problems, required)
        if obj is None:
            return
        self.phase = obj
        if obj.get("schema_version") != SCHEMA_VERSION:
            self.problems.malformed("phase.json.schema_version", f"expected {SCHEMA_VERSION}")
        if obj.get("record_kind") != "reorganization_phase":
            self.problems.malformed("phase.json.record_kind", "expected 'reorganization_phase'")
        phase_id = required_string(obj, "phase_id", "phase.json", self.problems)
        if phase_id is not None:
            if not ID_RE.fullmatch(phase_id):
                self.problems.malformed("phase.json.phase_id", "expected a stable slug identifier")
            self.phase_id = phase_id
        required_string(obj, "title", "phase.json", self.problems)
        if obj.get("status") not in PHASE_STATUSES:
            self.problems.malformed("phase.json.status", f"expected one of {sorted(PHASE_STATUSES)}")
        created_at = required_string(obj, "created_at", "phase.json", self.problems)
        if created_at is not None and not is_rfc3339(created_at):
            self.problems.malformed("phase.json.created_at", "expected an RFC3339 timestamp with timezone")
        for key in ("origin_checkpoint_id", "current_checkpoint_id"):
            value_id = required_string(obj, key, "phase.json", self.problems)
            if value_id is not None and not CHECKPOINT_ID_RE.fullmatch(value_id):
                self.problems.malformed(f"phase.json.{key}", "expected C followed by four digits")
        scope_artifact = self.artifact(obj.get("scope"), "phase.json.scope")
        expected_scope = self.relative_context(self.phase_dir / "scope.tsv")
        if scope_artifact is not None and scope_artifact.path != expected_scope:
            self.problems.violation(
                "phase.json.scope.path",
                f"immutable phase scope must be {expected_scope}",
            )
        for key, filename in (
            ("unclassified_queue", "unclassified-queue.tsv"),
            ("semantic_review", "semantic-review.tsv"),
        ):
            artifact = self.artifact(obj.get(key), f"phase.json.{key}")
            obj[f"_{key}_artifact"] = artifact
            expected = self.relative_context(self.phase_dir / filename)
            if artifact is not None and artifact.path != expected:
                self.problems.violation(
                    f"phase.json.{key}.path",
                    f"phase artifact must be {expected}",
                )
        self.load_base_policy(obj.get("base_policy"))
        self.load_authority(obj.get("authority"))
        self.shared_paths = self.path_rules(obj.get("shared_paths"), "phase.json.shared_paths")
        self.load_milestones(obj.get("milestones"))
        self.load_completion(obj.get("completion"))

    def load_base_policy(self, value: Any) -> None:
        context = "phase.json.base_policy"
        obj = require_keys(
            value,
            context,
            self.problems,
            {
                "immutable_origin_sha",
                "new_branch_must_use_current_checkpoint",
                "combined_baseline_after_each_accepted_checkpoint",
                "refresh_requires",
            },
        )
        if obj is None:
            return
        origin = required_string(obj, "immutable_origin_sha", context, self.problems)
        if origin is not None:
            self.commit_exists(origin, f"{context}.immutable_origin_sha")
        for key in ("new_branch_must_use_current_checkpoint", "combined_baseline_after_each_accepted_checkpoint"):
            if not isinstance(obj.get(key), bool):
                self.problems.malformed(f"{context}.{key}", "expected a boolean")
        refresh = sorted_unique_strings(obj.get("refresh_requires"), f"{context}.refresh_requires", self.problems, allow_empty=False)
        missing = sorted(REQUIRED_REFRESH_ITEMS - set(refresh))
        if missing:
            self.problems.violation(f"{context}.refresh_requires", "missing required refresh item(s): " + ", ".join(missing))

    def load_authority(self, value: Any) -> None:
        context = "phase.json.authority"
        obj = require_keys(
            value,
            context,
            self.problems,
            {
                "principals",
                "integration_authority_id",
                "release_manager_id",
                "main_push_authority_ids",
                "shared_path_authority_ids",
                "branch_registry_authority_ids",
                "build_lock_name",
                "lanes",
            },
        )
        if obj is None:
            return
        principals = obj.get("principals")
        if not isinstance(principals, list):
            self.problems.malformed(f"{context}.principals", "expected a list")
            principals = []
        principal_order: list[str] = []
        for index, value_principal in enumerate(principals):
            item_context = f"{context}.principals[{index}]"
            principal = require_keys(value_principal, item_context, self.problems, {"principal_id", "display_name", "kind"})
            if principal is None:
                continue
            principal_id = required_string(principal, "principal_id", item_context, self.problems)
            required_string(principal, "display_name", item_context, self.problems)
            if principal.get("kind") not in PRINCIPAL_KINDS:
                self.problems.malformed(f"{item_context}.kind", f"expected one of {sorted(PRINCIPAL_KINDS)}")
            if principal_id is not None:
                if principal_id in self.principals:
                    self.problems.malformed(item_context, f"duplicate principal_id {principal_id}")
                self.principals[principal_id] = principal
                principal_order.append(principal_id)
        if principal_order != sorted(principal_order):
            self.problems.violation(f"{context}.principals", "principals must be sorted by principal_id")
        for key in ("integration_authority_id", "release_manager_id"):
            principal_id = required_string(obj, key, context, self.problems)
            if principal_id is not None and principal_id not in self.principals:
                self.problems.violation(f"{context}.{key}", f"unknown principal {principal_id}")
            elif principal_id is not None and self.principals[principal_id].get("kind") != "human":
                self.problems.violation(f"{context}.{key}", "must name a human principal")
        for key in ("main_push_authority_ids", "shared_path_authority_ids", "branch_registry_authority_ids"):
            identifiers = sorted_unique_strings(obj.get(key), f"{context}.{key}", self.problems, allow_empty=False)
            for identifier in identifiers:
                if identifier not in self.principals:
                    self.problems.violation(f"{context}.{key}", f"unknown principal {identifier}")
                elif self.principals[identifier].get("kind") != "human":
                    self.problems.violation(f"{context}.{key}", f"authority {identifier} must be human")
        required_string(obj, "build_lock_name", context, self.problems)
        lanes = obj.get("lanes")
        if not isinstance(lanes, list):
            self.problems.malformed(f"{context}.lanes", "expected a list")
            lanes = []
        lane_order: list[str] = []
        for index, lane_value in enumerate(lanes):
            item_context = f"{context}.lanes[{index}]"
            lane = require_keys(lane_value, item_context, self.problems, {"lane_id", "owner_id", "operator_ids"})
            if lane is None:
                continue
            lane_id = required_string(lane, "lane_id", item_context, self.problems)
            owner = required_string(lane, "owner_id", item_context, self.problems)
            operators = sorted_unique_strings(lane.get("operator_ids"), f"{item_context}.operator_ids", self.problems, allow_empty=False)
            if owner is not None and owner not in self.principals:
                self.problems.violation(f"{item_context}.owner_id", f"unknown principal {owner}")
            elif owner is not None and self.principals[owner].get("kind") != "human":
                self.problems.violation(f"{item_context}.owner_id", "lane owner must be human")
            for operator in operators:
                if operator not in self.principals:
                    self.problems.violation(f"{item_context}.operator_ids", f"unknown principal {operator}")
            if lane_id is not None:
                if lane_id in self.lanes:
                    self.problems.malformed(item_context, f"duplicate lane_id {lane_id}")
                self.lanes[lane_id] = lane
                lane_order.append(lane_id)
        if lane_order != sorted(lane_order):
            self.problems.violation(f"{context}.lanes", "lanes must be sorted by lane_id")

    def load_milestones(self, value: Any) -> None:
        context = "phase.json.milestones"
        if not isinstance(value, list):
            self.problems.malformed(context, "expected a list")
            return
        order: list[str] = []
        required = {
            "milestone_id",
            "status",
            "depends_on",
            "wave_ids",
            "acceptance_gate_ids",
            "accepted_checkpoint_id",
            "unblocks",
            "superseded_by",
        }
        for index, milestone_value in enumerate(value):
            item_context = f"{context}[{index}]"
            milestone = require_keys(milestone_value, item_context, self.problems, required)
            if milestone is None:
                continue
            milestone_id = required_string(milestone, "milestone_id", item_context, self.problems)
            status = milestone.get("status")
            if status not in MILESTONE_STATUSES:
                self.problems.malformed(f"{item_context}.status", f"expected one of {sorted(MILESTONE_STATUSES)}")
            for key in ("depends_on", "wave_ids", "acceptance_gate_ids", "unblocks"):
                sorted_unique_strings(milestone.get(key), f"{item_context}.{key}", self.problems)
            accepted_checkpoint = required_string(milestone, "accepted_checkpoint_id", item_context, self.problems, nullable=True)
            superseded_by = required_string(milestone, "superseded_by", item_context, self.problems, nullable=True)
            if status == "accepted" and accepted_checkpoint is None:
                self.problems.malformed(item_context, "accepted milestones require accepted_checkpoint_id")
            if status != "accepted" and accepted_checkpoint is not None:
                self.problems.violation(item_context, "only accepted milestones may name accepted_checkpoint_id")
            if status == "superseded" and superseded_by is None:
                self.problems.malformed(item_context, "superseded milestones require superseded_by")
            if status != "superseded" and superseded_by is not None:
                self.problems.violation(item_context, "only superseded milestones may name superseded_by")
            if milestone_id is not None:
                if milestone_id in self.milestones:
                    self.problems.malformed(item_context, f"duplicate milestone_id {milestone_id}")
                self.milestones[milestone_id] = milestone
                order.append(milestone_id)
        if order != sorted(order):
            self.problems.violation(context, "milestones must be sorted by milestone_id")

    def load_completion(self, value: Any) -> None:
        context = "phase.json.completion"
        obj = require_keys(value, context, self.problems, {"bounded_phase", "repository_wide"})
        if obj is None:
            return
        bounded = require_keys(
            obj.get("bounded_phase"),
            f"{context}.bounded_phase",
            self.problems,
            {"status", "required_condition_ids", "evidence_checkpoint_id"},
        )
        repository = require_keys(
            obj.get("repository_wide"),
            f"{context}.repository_wide",
            self.problems,
            {"status", "required_gate_ids", "evidence_checkpoint_id"},
        )
        if bounded is not None:
            status = bounded.get("status")
            if status not in COMPLETION_STATUSES:
                self.problems.malformed(f"{context}.bounded_phase.status", f"expected one of {sorted(COMPLETION_STATUSES)}")
            conditions = sorted_unique_strings(bounded.get("required_condition_ids"), f"{context}.bounded_phase.required_condition_ids", self.problems)
            missing = sorted(REQUIRED_BOUNDED_CONDITIONS - set(conditions))
            if missing:
                self.problems.violation(f"{context}.bounded_phase", "missing required condition(s): " + ", ".join(missing))
            evidence = required_string(bounded, "evidence_checkpoint_id", f"{context}.bounded_phase", self.problems, nullable=True)
            if (status == "complete") != (evidence is not None):
                self.problems.violation(f"{context}.bounded_phase", "evidence_checkpoint_id must be present exactly when status is complete")
        if repository is not None:
            status = repository.get("status")
            if status not in COMPLETION_STATUSES:
                self.problems.malformed(f"{context}.repository_wide.status", f"expected one of {sorted(COMPLETION_STATUSES)}")
            gates = sorted_unique_strings(repository.get("required_gate_ids"), f"{context}.repository_wide.required_gate_ids", self.problems)
            missing = sorted(REQUIRED_REPOSITORY_GATES - set(gates))
            if missing:
                self.problems.violation(f"{context}.repository_wide", "missing required repository gate(s): " + ", ".join(missing))
            evidence = required_string(repository, "evidence_checkpoint_id", f"{context}.repository_wide", self.problems, nullable=True)
            if (status == "complete") != (evidence is not None):
                self.problems.violation(f"{context}.repository_wide", "evidence_checkpoint_id must be present exactly when status is complete")

    def load_records(self) -> None:
        self.load_checkpoint_records()
        self.load_projection_records()
        self.load_branch_records()
        self.load_request_records()

    def json_files(self, name: str) -> list[Path]:
        directory = self.phase_dir / name
        if not directory.is_dir():
            self.problems.malformed(self.relative_context(directory), "required record directory is missing")
            return []
        pattern = RECORD_FILE_RE.get(name)
        if pattern is None:
            self.problems.malformed(
                self.relative_context(directory),
                f"unknown record directory {name!r}",
            )
            return []
        return sorted(
            (path for path in directory.glob("*.json") if pattern.fullmatch(path.name)),
            key=lambda path: path.name,
        )

    def load_checkpoint_records(self) -> None:
        for path in self.json_files("checkpoints"):
            context = self.relative_context(path)
            record = self.read_json_file(path, context)
            if record is None:
                continue
            required = {
                "schema_version",
                "record_kind",
                "phase_id",
                "checkpoint_id",
                "parent_checkpoint_id",
                "commit_sha",
                "accepted_at",
                "accepted_by",
                "milestones_satisfied",
                "unblocks",
                "inventory",
                "combined_baseline",
                "metrics",
                "gates",
            }
            obj = require_keys(record, context, self.problems, required)
            if obj is None:
                continue
            if obj.get("schema_version") != SCHEMA_VERSION or obj.get("record_kind") != "phase_checkpoint":
                self.problems.malformed(context, "expected schema_version 1 and record_kind 'phase_checkpoint'")
            if obj.get("phase_id") != self.phase_id:
                self.problems.violation(context, "phase_id does not match phase.json")
            checkpoint_id = required_string(obj, "checkpoint_id", context, self.problems)
            if checkpoint_id is None:
                continue
            if not CHECKPOINT_ID_RE.fullmatch(checkpoint_id) or path.stem != checkpoint_id:
                self.problems.malformed(context, "checkpoint_id must match the Cdddd filename stem")
            if checkpoint_id in self.checkpoints:
                self.problems.malformed(context, f"duplicate checkpoint_id {checkpoint_id}")
                continue
            parent = required_string(obj, "parent_checkpoint_id", context, self.problems, nullable=True)
            if parent is not None and not CHECKPOINT_ID_RE.fullmatch(parent):
                self.problems.malformed(f"{context}.parent_checkpoint_id", "expected C followed by four digits or null")
            commit = required_string(obj, "commit_sha", context, self.problems)
            if commit is not None:
                self.commit_exists(commit, f"{context}.commit_sha")
            accepted_at = required_string(obj, "accepted_at", context, self.problems)
            if accepted_at is not None and not is_rfc3339(accepted_at):
                self.problems.malformed(f"{context}.accepted_at", "expected an RFC3339 timestamp with timezone")
            accepted_by = required_string(obj, "accepted_by", context, self.problems)
            if accepted_by is not None and accepted_by not in self.principals:
                self.problems.violation(f"{context}.accepted_by", f"unknown principal {accepted_by}")
            elif accepted_by is not None:
                authority = self.phase.get("authority", {})
                allowed = {authority.get("integration_authority_id"), authority.get("release_manager_id")}
                if accepted_by not in allowed:
                    self.problems.violation(f"{context}.accepted_by", "checkpoint must be accepted by the integration authority or release manager")
            for key in ("milestones_satisfied", "unblocks"):
                sorted_unique_strings(obj.get(key), f"{context}.{key}", self.problems)
            inventory = self.artifact(obj.get("inventory"), f"{context}.inventory")
            expected_inventory = self.relative_context(
                self.phase_dir / "checkpoints" / f"{checkpoint_id}-inventory.tsv"
            )
            if inventory is not None and inventory.path != expected_inventory:
                self.problems.violation(
                    f"{context}.inventory.path",
                    f"checkpoint inventory must be {expected_inventory}",
                )
            baseline = require_keys(
                obj.get("combined_baseline"),
                f"{context}.combined_baseline",
                self.problems,
                {"format_version", "artifact", "summary_artifact", "generation_command"},
            )
            baseline_artifact = None
            baseline_summary_artifact = None
            baseline_format_version = None
            if baseline is not None:
                baseline_format_version = baseline.get("format_version")
                if baseline_format_version != DECLARATION_FORMAT_VERSION:
                    self.problems.malformed(
                        f"{context}.combined_baseline.format_version",
                        f"expected declaration format version {DECLARATION_FORMAT_VERSION}",
                    )
                baseline_artifact = self.artifact(baseline.get("artifact"), f"{context}.combined_baseline.artifact")
                baseline_summary_artifact = self.artifact(
                    baseline.get("summary_artifact"),
                    f"{context}.combined_baseline.summary_artifact",
                )
                required_string(baseline, "generation_command", f"{context}.combined_baseline", self.problems)
            metrics = obj.get("metrics")
            metrics_obj = require_keys(metrics, f"{context}.metrics", self.problems, METRIC_KEYS)
            if metrics_obj is not None:
                for key in METRIC_KEYS:
                    if not isinstance(metrics_obj.get(key), int) or metrics_obj.get(key, -1) < 0:
                        self.problems.malformed(f"{context}.metrics.{key}", "expected a nonnegative integer")
            gate_map: dict[str, dict[str, Any]] = {}
            gates = obj.get("gates")
            if not isinstance(gates, list):
                self.problems.malformed(f"{context}.gates", "expected a list")
                gates = []
            gate_order: list[str] = []
            for index, gate_value in enumerate(gates):
                gate_context = f"{context}.gates[{index}]"
                gate = require_keys(
                    gate_value,
                    gate_context,
                    self.problems,
                    {"gate_id", "command", "status", "commit_sha", "executor_id", "requires_large_build_lock", "lock_name", "evidence"},
                )
                if gate is None:
                    continue
                gate_id = required_string(gate, "gate_id", gate_context, self.problems)
                required_string(gate, "command", gate_context, self.problems)
                if gate.get("status") not in GATE_STATUSES:
                    self.problems.malformed(f"{gate_context}.status", f"expected one of {sorted(GATE_STATUSES)}")
                if commit is not None and gate.get("commit_sha") != commit:
                    self.problems.violation(f"{gate_context}.commit_sha", "gate evidence must be recorded at the checkpoint commit")
                executor = required_string(gate, "executor_id", gate_context, self.problems)
                if executor is not None and executor not in self.principals:
                    self.problems.violation(f"{gate_context}.executor_id", f"unknown principal {executor}")
                requires_lock = gate.get("requires_large_build_lock")
                if not isinstance(requires_lock, bool):
                    self.problems.malformed(f"{gate_context}.requires_large_build_lock", "expected a boolean")
                lock_name = required_string(gate, "lock_name", gate_context, self.problems, nullable=True)
                expected_lock = self.phase.get("authority", {}).get("build_lock_name")
                if requires_lock and lock_name != expected_lock:
                    self.problems.violation(gate_context, "large-build gate must name the phase build lock")
                if not requires_lock and lock_name is not None:
                    self.problems.violation(gate_context, "non-large gate must use null lock_name")
                self.artifact(gate.get("evidence"), f"{gate_context}.evidence", nullable=True)
                if gate_id is not None:
                    if gate_id in gate_map:
                        self.problems.malformed(gate_context, f"duplicate gate_id {gate_id}")
                    gate_map[gate_id] = gate
                    gate_order.append(gate_id)
            if gate_order != sorted(gate_order):
                self.problems.violation(f"{context}.gates", "gates must be sorted by gate_id")
            obj["_inventory_artifact"] = inventory
            obj["_baseline_artifact"] = baseline_artifact
            obj["_baseline_summary_artifact"] = baseline_summary_artifact
            obj["_baseline_format_version"] = baseline_format_version
            obj["_gate_map"] = gate_map
            self.checkpoints[checkpoint_id] = obj

    def load_projection_records(self) -> None:
        for path in self.json_files("projections"):
            context = self.relative_context(path)
            record = self.read_json_file(path, context)
            if record is None:
                continue
            required = {
                "schema_version",
                "record_kind",
                "phase_id",
                "projection_id",
                "wave_id",
                "base_checkpoint_id",
                "status",
                "combined_baseline",
                "selector",
                "projection_graph",
                "expected_counts",
                "checker",
                "superseded_by",
            }
            obj = require_keys(record, context, self.problems, required)
            if obj is None:
                continue
            if obj.get("schema_version") != SCHEMA_VERSION or obj.get("record_kind") != "baseline_projection":
                self.problems.malformed(context, "expected schema_version 1 and record_kind 'baseline_projection'")
            if obj.get("phase_id") != self.phase_id:
                self.problems.violation(context, "phase_id does not match phase.json")
            projection_id = required_string(obj, "projection_id", context, self.problems)
            if projection_id is None:
                continue
            if not ID_RE.fullmatch(projection_id) or path.stem != projection_id:
                self.problems.malformed(context, "projection_id must be a slug matching the filename stem")
            required_string(obj, "wave_id", context, self.problems)
            required_string(obj, "base_checkpoint_id", context, self.problems)
            if obj.get("status") not in PROJECTION_STATUSES:
                self.problems.malformed(f"{context}.status", f"expected one of {sorted(PROJECTION_STATUSES)}")
            obj["_combined_artifact"] = self.artifact(obj.get("combined_baseline"), f"{context}.combined_baseline")
            selector = require_keys(obj.get("selector"), f"{context}.selector", self.problems, {"kind", "artifact"})
            if selector is not None:
                if selector.get("kind") != "module_path_tsv":
                    self.problems.malformed(
                        f"{context}.selector.kind", "expected 'module_path_tsv'"
                    )
                obj["_selector_artifact"] = self.artifact(selector.get("artifact"), f"{context}.selector.artifact")
                obj["_selector_rows"] = self.parse_selector(
                    obj.get("_selector_artifact"), f"{context}.selector.artifact"
                )
            obj["_projection_graph_artifact"] = self.artifact(
                obj.get("projection_graph"), f"{context}.projection_graph"
            )
            counts = require_keys(
                obj.get("expected_counts"),
                f"{context}.expected_counts",
                self.problems,
                {"declarations", "signature_edges", "body_edges", "union_edges"},
            )
            if counts is not None:
                for key in ("declarations", "signature_edges", "body_edges", "union_edges"):
                    if not isinstance(counts.get(key), int) or counts.get(key, -1) < 0:
                        self.problems.malformed(f"{context}.expected_counts.{key}", "expected a nonnegative integer")
            checker = require_keys(obj.get("checker"), f"{context}.checker", self.problems, {"artifact", "arguments"})
            if checker is not None:
                obj["_checker_artifact"] = self.artifact(checker.get("artifact"), f"{context}.checker.artifact")
                sorted_unique_strings(checker.get("arguments"), f"{context}.checker.arguments", self.problems)
            superseded_by = required_string(obj, "superseded_by", context, self.problems, nullable=True)
            if obj.get("status") == "superseded" and superseded_by is None:
                self.problems.malformed(context, "superseded projections require superseded_by")
            if obj.get("status") != "superseded" and superseded_by is not None:
                self.problems.violation(context, "only superseded projections may name superseded_by")
            if projection_id in self.projections:
                self.problems.malformed(context, f"duplicate projection_id {projection_id}")
            self.projections[projection_id] = obj

    def load_branch_records(self) -> None:
        for path in self.json_files("branches"):
            context = self.relative_context(path)
            record = self.read_json_file(path, context)
            if record is None:
                continue
            required = {
                "schema_version", "record_kind", "phase_id", "branch_id", "lane_id", "wave_id",
                "branch_name", "owner_id", "operator_ids", "base_checkpoint_id", "base_sha",
                "owned_paths", "destination_prefixes", "forbidden_paths", "baseline_projection_id", "shared_request_ids",
                "status", "refresh", "delivery", "integration", "retirement",
            }
            obj = require_keys(record, context, self.problems, required)
            if obj is None:
                continue
            if obj.get("schema_version") != SCHEMA_VERSION or obj.get("record_kind") != "phase_branch":
                self.problems.malformed(context, "expected schema_version 1 and record_kind 'phase_branch'")
            if obj.get("phase_id") != self.phase_id:
                self.problems.violation(context, "phase_id does not match phase.json")
            branch_id = required_string(obj, "branch_id", context, self.problems)
            if branch_id is None:
                continue
            if not ID_RE.fullmatch(branch_id) or path.stem != branch_id:
                self.problems.malformed(context, "branch_id must be a slug matching the filename stem")
            for key in ("lane_id", "wave_id", "branch_name", "owner_id", "base_checkpoint_id", "base_sha", "baseline_projection_id"):
                required_string(obj, key, context, self.problems)
            if obj.get("branch_name") in {"main", "master"}:
                self.problems.violation(f"{context}.branch_name", "worker branch must not be main or master")
            sorted_unique_strings(obj.get("operator_ids"), f"{context}.operator_ids", self.problems, allow_empty=False)
            obj["_owned_rules"] = self.path_rules(obj.get("owned_paths"), f"{context}.owned_paths")
            obj["_destination_rules"] = self.path_rules(
                obj.get("destination_prefixes"), f"{context}.destination_prefixes"
            )
            for rule in obj["_destination_rules"]:
                if rule.match not in {"prefix", "exact"}:
                    self.problems.malformed(
                        f"{context}.destination_prefixes",
                        "destination rules must use match 'prefix' or 'exact'",
                    )
            obj["_forbidden_rules"] = self.path_rules(obj.get("forbidden_paths"), f"{context}.forbidden_paths")
            sorted_unique_strings(obj.get("shared_request_ids"), f"{context}.shared_request_ids", self.problems)
            if obj.get("status") not in BRANCH_STATUSES:
                self.problems.malformed(f"{context}.status", f"expected one of {sorted(BRANCH_STATUSES)}")
            refresh = require_keys(obj.get("refresh"), f"{context}.refresh", self.problems, {"reviewed_checkpoint_id", "decision", "evidence"})
            if refresh is not None:
                required_string(refresh, "reviewed_checkpoint_id", f"{context}.refresh", self.problems)
                if refresh.get("decision") not in REFRESH_DECISIONS:
                    self.problems.malformed(f"{context}.refresh.decision", f"expected one of {sorted(REFRESH_DECISIONS)}")
                evidence = refresh.get("evidence")
                if not isinstance(evidence, list):
                    self.problems.malformed(f"{context}.refresh.evidence", "expected a list")
                    evidence = []
                refresh["_evidence"] = [self.artifact(item, f"{context}.refresh.evidence[{index}]") for index, item in enumerate(evidence)]
            delivery = require_keys(obj.get("delivery"), f"{context}.delivery", self.problems, {"commit_sha", "report", "scope_evidence"})
            if delivery is not None:
                required_string(delivery, "commit_sha", f"{context}.delivery", self.problems, nullable=True)
                delivery["_report"] = self.artifact(delivery.get("report"), f"{context}.delivery.report", nullable=True)
                delivery["_scope_evidence"] = self.artifact(delivery.get("scope_evidence"), f"{context}.delivery.scope_evidence", nullable=True)
            integration = require_keys(obj.get("integration"), f"{context}.integration", self.problems, {"method", "accepted_checkpoint_id", "accepted_sha"})
            if integration is not None:
                method = required_string(integration, "method", f"{context}.integration", self.problems, nullable=True)
                if method is not None and method not in INTEGRATION_METHODS:
                    self.problems.malformed(f"{context}.integration.method", f"expected one of {sorted(INTEGRATION_METHODS)} or null")
                required_string(integration, "accepted_checkpoint_id", f"{context}.integration", self.problems, nullable=True)
                required_string(integration, "accepted_sha", f"{context}.integration", self.problems, nullable=True)
            retirement = require_keys(obj.get("retirement"), f"{context}.retirement", self.problems, {"remote_ref", "rule", "status", "retired_at", "retired_by", "ancestry_checkpoint_id"})
            if retirement is not None:
                remote_ref = required_string(retirement, "remote_ref", f"{context}.retirement", self.problems)
                if remote_ref is not None and not remote_ref.startswith("refs/heads/"):
                    self.problems.malformed(f"{context}.retirement.remote_ref", "expected refs/heads/<branch>")
                if retirement.get("rule") != "delivery_ancestor_of_green_checkpoint":
                    self.problems.malformed(f"{context}.retirement.rule", "expected 'delivery_ancestor_of_green_checkpoint'")
                if retirement.get("status") not in RETIREMENT_STATUSES:
                    self.problems.malformed(f"{context}.retirement.status", f"expected one of {sorted(RETIREMENT_STATUSES)}")
                retired_at = required_string(retirement, "retired_at", f"{context}.retirement", self.problems, nullable=True)
                if retired_at is not None and not is_rfc3339(retired_at):
                    self.problems.malformed(f"{context}.retirement.retired_at", "expected an RFC3339 timestamp with timezone")
                required_string(retirement, "retired_by", f"{context}.retirement", self.problems, nullable=True)
                required_string(retirement, "ancestry_checkpoint_id", f"{context}.retirement", self.problems, nullable=True)
            if branch_id in self.branches:
                self.problems.malformed(context, f"duplicate branch_id {branch_id}")
            obj["_context"] = context
            self.branches[branch_id] = obj

    def load_request_records(self) -> None:
        for path in self.json_files("requests"):
            context = self.relative_context(path)
            record = self.read_json_file(path, context)
            if record is None:
                continue
            if record.get("record_kind") == INTEGRATION_AMENDMENT_KIND:
                self.load_integration_amendment_record(path, context, record)
                continue
            required = {
                "schema_version", "record_kind", "phase_id", "request_id", "lane_id", "wave_id",
                "requester_id", "created_at", "target_checkpoint_id", "target_base_sha", "paths",
                "preimage_blobs", "rationale", "patch", "depends_on", "blocks",
                "valid_through_checkpoint_id", "status", "supersedes", "superseded_by", "resolution",
            }
            obj = require_keys(record, context, self.problems, required)
            if obj is None:
                continue
            if obj.get("schema_version") != SCHEMA_VERSION or obj.get("record_kind") != "shared_file_request":
                self.problems.malformed(context, "expected schema_version 1 and record_kind 'shared_file_request'")
            if obj.get("phase_id") != self.phase_id:
                self.problems.violation(context, "phase_id does not match phase.json")
            request_id = required_string(obj, "request_id", context, self.problems)
            if request_id is None:
                continue
            if not ID_RE.fullmatch(request_id) or path.stem != request_id:
                self.problems.malformed(context, "request_id must be a slug matching the filename stem")
            for key in ("lane_id", "wave_id", "requester_id", "created_at", "target_checkpoint_id", "target_base_sha", "rationale", "valid_through_checkpoint_id"):
                required_string(obj, key, context, self.problems)
            if isinstance(obj.get("created_at"), str) and not is_rfc3339(obj["created_at"]):
                self.problems.malformed(f"{context}.created_at", "expected an RFC3339 timestamp with timezone")
            paths = sorted_unique_strings(obj.get("paths"), f"{context}.paths", self.problems, allow_empty=False)
            for affected in paths:
                if not is_repo_path(affected):
                    self.problems.malformed(f"{context}.paths", f"invalid repository-relative path {affected!r}")
            preimages = obj.get("preimage_blobs")
            if not isinstance(preimages, list):
                self.problems.malformed(f"{context}.preimage_blobs", "expected a list")
                preimages = []
            parsed_preimages: dict[str, str | None] = {}
            preimage_order: list[str] = []
            for index, preimage_value in enumerate(preimages):
                item_context = f"{context}.preimage_blobs[{index}]"
                preimage = require_keys(preimage_value, item_context, self.problems, {"path", "blob_oid"})
                if preimage is None:
                    continue
                preimage_path = required_string(preimage, "path", item_context, self.problems)
                blob = preimage.get("blob_oid")
                if blob is not None and (not isinstance(blob, str) or not SHA1_RE.fullmatch(blob)):
                    self.problems.malformed(f"{item_context}.blob_oid", "expected lowercase 40-hex blob OID or null")
                if preimage_path is not None:
                    if preimage_path in parsed_preimages:
                        self.problems.malformed(item_context, f"duplicate preimage path {preimage_path}")
                    parsed_preimages[preimage_path] = blob
                    preimage_order.append(preimage_path)
            if preimage_order != sorted(preimage_order):
                self.problems.violation(f"{context}.preimage_blobs", "preimage rows must be sorted by path")
            if set(parsed_preimages) != set(paths):
                self.problems.violation(f"{context}.preimage_blobs", "preimage paths must exactly equal request paths")
            obj["_preimages"] = parsed_preimages
            obj["_patch"] = self.artifact(obj.get("patch"), f"{context}.patch")
            expected_patch = self.relative_context(
                self.phase_dir / "requests" / f"{request_id}.patch"
            )
            if isinstance(obj.get("_patch"), Artifact) and obj["_patch"].path != expected_patch:
                self.problems.violation(
                    f"{context}.patch.path",
                    f"request patch must be {expected_patch}",
                )
            changed_paths = self.patch_paths(obj.get("_patch"), f"{context}.patch")
            if changed_paths != paths:
                self.problems.violation(
                    f"{context}.patch",
                    f"patch paths must exactly equal request paths: expected {paths}, found {changed_paths}",
                )
            for key in ("depends_on", "blocks"):
                sorted_unique_strings(obj.get(key), f"{context}.{key}", self.problems)
            if obj.get("status") not in REQUEST_STATUSES:
                self.problems.malformed(f"{context}.status", f"expected one of {sorted(REQUEST_STATUSES)}")
            required_string(obj, "supersedes", context, self.problems, nullable=True)
            required_string(obj, "superseded_by", context, self.problems, nullable=True)
            resolution = require_keys(
                obj.get("resolution"),
                f"{context}.resolution",
                self.problems,
                {"commit_sha", "checkpoint_id", "resolved_at", "resolved_by", "validation_evidence", "reason"},
            )
            if resolution is not None:
                for key in ("commit_sha", "checkpoint_id", "resolved_at", "resolved_by", "reason"):
                    required_string(resolution, key, f"{context}.resolution", self.problems, nullable=True)
                if resolution.get("resolved_at") is not None and not is_rfc3339(resolution["resolved_at"]):
                    self.problems.malformed(f"{context}.resolution.resolved_at", "expected an RFC3339 timestamp with timezone")
                evidence = resolution.get("validation_evidence")
                if not isinstance(evidence, list):
                    self.problems.malformed(f"{context}.resolution.validation_evidence", "expected a list")
                    evidence = []
                resolution["_evidence"] = [self.artifact(item, f"{context}.resolution.validation_evidence[{index}]") for index, item in enumerate(evidence)]
            if request_id in self.requests:
                self.problems.malformed(context, f"duplicate request_id {request_id}")
            obj["_context"] = context
            self.requests[request_id] = obj

    def load_integration_amendment_record(
        self, path: Path, context: str, record: dict[str, Any]
    ) -> None:
        """Load a reviewed repair rooted in an in-flight integration index.

        Unlike a ``shared_file_request``, an integration amendment is not
        falsely projected back onto an accepted checkpoint.  Its exact
        preimages live in the hash-pinned postimage manifest, and its target
        commit records the HEAD whose staged index the amendment repaired.
        """

        required = {
            "schema_version",
            "record_kind",
            "phase_id",
            "request_id",
            "lane_id",
            "requester_id",
            "created_at",
            "target_branch",
            "target_head_sha",
            "target_index_staged_paths",
            "paths",
            "preimage_blobs",
            "rationale",
            "patch",
            "postimages",
            "predecessor_postimages",
            "review",
            "approval",
            "depends_on",
            "blocks",
            "status",
            "supersedes",
            "superseded_by",
            "resolution",
        }
        obj = require_keys(record, context, self.problems, required)
        if obj is None:
            return
        if obj.get("schema_version") != SCHEMA_VERSION:
            self.problems.malformed(context, f"expected schema_version {SCHEMA_VERSION}")
        if obj.get("phase_id") != self.phase_id:
            self.problems.violation(context, "phase_id does not match phase.json")
        request_id = required_string(obj, "request_id", context, self.problems)
        if request_id is None:
            return
        if not ID_RE.fullmatch(request_id) or path.stem != request_id:
            self.problems.malformed(
                context, "request_id must be a slug matching the filename stem"
            )
        for key in (
            "lane_id",
            "requester_id",
            "created_at",
            "target_branch",
            "target_head_sha",
            "rationale",
        ):
            required_string(obj, key, context, self.problems)
        if isinstance(obj.get("created_at"), str) and not is_rfc3339(obj["created_at"]):
            self.problems.malformed(
                f"{context}.created_at", "expected an RFC3339 timestamp with timezone"
            )
        target_head = obj.get("target_head_sha")
        if isinstance(target_head, str):
            self.commit_exists(target_head, f"{context}.target_head_sha")
        staged_paths = obj.get("target_index_staged_paths")
        if not isinstance(staged_paths, int) or isinstance(staged_paths, bool) or staged_paths < 1:
            self.problems.malformed(
                f"{context}.target_index_staged_paths", "expected a positive integer"
            )

        paths = sorted_unique_strings(
            obj.get("paths"), f"{context}.paths", self.problems, allow_empty=False
        )
        for affected in paths:
            if not is_repo_path(affected):
                self.problems.malformed(
                    f"{context}.paths", f"invalid repository-relative path {affected!r}"
                )
        preimages = obj.get("preimage_blobs")
        if not isinstance(preimages, list):
            self.problems.malformed(f"{context}.preimage_blobs", "expected a list")
            preimages = []
        parsed_preimages: dict[str, str] = {}
        preimage_order: list[str] = []
        for index, preimage_value in enumerate(preimages):
            item_context = f"{context}.preimage_blobs[{index}]"
            preimage = require_keys(
                preimage_value, item_context, self.problems, {"path", "blob_oid"}
            )
            if preimage is None:
                continue
            preimage_path = required_string(preimage, "path", item_context, self.problems)
            blob = preimage.get("blob_oid")
            if not isinstance(blob, str) or not SHA1_RE.fullmatch(blob):
                self.problems.malformed(
                    f"{item_context}.blob_oid",
                    "integration-amendment preimages require a lowercase 40-hex blob OID",
                )
                continue
            if preimage_path is not None:
                if preimage_path in parsed_preimages:
                    self.problems.malformed(
                        item_context, f"duplicate preimage path {preimage_path}"
                    )
                parsed_preimages[preimage_path] = blob
                preimage_order.append(preimage_path)
        if preimage_order != sorted(preimage_order):
            self.problems.violation(
                f"{context}.preimage_blobs", "preimage rows must be sorted by path"
            )
        if set(parsed_preimages) != set(paths):
            self.problems.violation(
                f"{context}.preimage_blobs",
                "preimage paths must exactly equal amendment paths",
            )
        obj["_preimages"] = parsed_preimages

        obj["_patch"] = self.artifact(obj.get("patch"), f"{context}.patch")
        obj["_postimages_artifact"] = self.artifact(
            obj.get("postimages"), f"{context}.postimages"
        )
        obj["_review_artifact"] = self.artifact(obj.get("review"), f"{context}.review")
        obj["_approval_artifact"] = self.artifact(
            obj.get("approval"), f"{context}.approval"
        )
        predecessor_values = obj.get("predecessor_postimages")
        if not isinstance(predecessor_values, list):
            self.problems.malformed(
                f"{context}.predecessor_postimages", "expected a list"
            )
            predecessor_values = []
        predecessor_artifacts = [
            self.artifact(value, f"{context}.predecessor_postimages[{index}]")
            for index, value in enumerate(predecessor_values)
        ]
        predecessor_paths = [
            artifact.path
            for artifact in predecessor_artifacts
            if artifact is not None
        ]
        if predecessor_paths != sorted(set(predecessor_paths)):
            self.problems.violation(
                f"{context}.predecessor_postimages",
                "artifacts must be unique and sorted by path",
            )
        request_prefix = self.relative_context(self.phase_dir / "requests") + "/"
        own_manifest = self.relative_context(
            self.phase_dir / "requests" / f"{request_id}-postimages.tsv"
        )
        for index, artifact in enumerate(predecessor_artifacts):
            if artifact is not None and (
                not artifact.path.startswith(request_prefix)
                or not artifact.path.endswith("-postimages.tsv")
                or artifact.path == own_manifest
            ):
                self.problems.violation(
                    f"{context}.predecessor_postimages[{index}].path",
                    "must name a different request postimage manifest in this phase",
                )
        obj["_predecessor_postimages_artifacts"] = predecessor_artifacts
        expected_artifact_paths = {
            "_patch": self.relative_context(
                self.phase_dir / "requests" / f"{request_id}.patch"
            ),
            "_postimages_artifact": self.relative_context(
                self.phase_dir / "requests" / f"{request_id}-postimages.tsv"
            ),
            "_review_artifact": self.relative_context(
                self.phase_dir / "requests" / f"{request_id}-review.md"
            ),
            "_approval_artifact": self.relative_context(
                self.phase_dir / "requests" / f"{request_id}-approval.md"
            ),
        }
        for key, expected in expected_artifact_paths.items():
            artifact = obj.get(key)
            if isinstance(artifact, Artifact) and artifact.path != expected:
                self.problems.violation(
                    f"{context}.{key.removeprefix('_').removesuffix('_artifact')}.path",
                    f"artifact must be {expected}",
                )
        changed_paths = self.patch_paths(
            obj.get("_patch"), f"{context}.patch", require_sorted=False
        )
        if len(changed_paths) != len(paths) or set(changed_paths) != set(paths):
            self.problems.violation(
                f"{context}.patch",
                "patch paths must uniquely and exactly equal amendment paths: "
                f"expected {paths}, found {changed_paths}",
            )
        obj["_postimages"], preimage_digests = self.validate_integration_amendment_manifest(
            obj.get("_postimages_artifact"),
            context,
            paths,
            parsed_preimages,
            obj.get("status"),
            (
                obj.get("resolution", {}).get("commit_sha")
                if isinstance(obj.get("resolution"), dict)
                else None
            ),
        )
        self.validate_integration_amendment_predecessors(
            predecessor_artifacts,
            context,
            obj.get("target_head_sha"),
            paths,
            parsed_preimages,
            preimage_digests,
        )

        for key in ("depends_on", "blocks"):
            obj[f"_{key}"] = sorted_unique_strings(
                obj.get(key), f"{context}.{key}", self.problems, allow_empty=False
            )
        if obj.get("status") not in REQUEST_STATUSES:
            self.problems.malformed(
                f"{context}.status", f"expected one of {sorted(REQUEST_STATUSES)}"
            )
        required_string(obj, "supersedes", context, self.problems, nullable=True)
        required_string(obj, "superseded_by", context, self.problems, nullable=True)
        resolution = require_keys(
            obj.get("resolution"),
            f"{context}.resolution",
            self.problems,
            {
                "commit_sha",
                "checkpoint_id",
                "resolved_at",
                "resolved_by",
                "validation_evidence",
                "reason",
            },
        )
        if resolution is not None:
            for key in ("commit_sha", "checkpoint_id", "resolved_at", "resolved_by", "reason"):
                required_string(
                    resolution,
                    key,
                    f"{context}.resolution",
                    self.problems,
                    nullable=True,
                )
            if resolution.get("resolved_at") is not None and not is_rfc3339(
                resolution["resolved_at"]
            ):
                self.problems.malformed(
                    f"{context}.resolution.resolved_at",
                    "expected an RFC3339 timestamp with timezone",
                )
            evidence = resolution.get("validation_evidence")
            if not isinstance(evidence, list):
                self.problems.malformed(
                    f"{context}.resolution.validation_evidence", "expected a list"
                )
                evidence = []
            resolution["_evidence"] = [
                self.artifact(item, f"{context}.resolution.validation_evidence[{index}]")
                for index, item in enumerate(evidence)
            ]
        if request_id in self.requests:
            self.problems.malformed(context, f"duplicate request_id {request_id}")
        obj["_context"] = context
        self.requests[request_id] = obj

    def validate_integration_amendment_manifest(
        self,
        artifact: Artifact | None,
        context: str,
        expected_paths: list[str],
        expected_preimages: dict[str, str],
        status: Any,
        resolution_commit: Any,
    ) -> tuple[dict[str, str], dict[str, str]]:
        if artifact is None:
            return {}, {}
        manifest_path = self.resolve_repo_path(
            artifact.path, f"{context}.postimages.path"
        )
        if manifest_path is None or not manifest_path.is_file():
            return {}, {}
        try:
            raw = manifest_path.read_bytes()
        except OSError as error:
            self.problems.malformed(
                f"{context}.postimages", f"cannot read postimage manifest: {error}"
            )
            return {}, {}
        if b"\r" in raw:
            self.problems.violation(
                f"{context}.postimages", "postimage manifest must use LF line endings"
            )
        if raw and not raw.endswith(b"\n"):
            self.problems.violation(
                f"{context}.postimages", "postimage manifest must end with a newline"
            )
        try:
            reader = csv.DictReader(
                raw.decode("utf-8-sig").splitlines(), delimiter="\t", strict=True
            )
            header = tuple(reader.fieldnames or ())
            rows = [dict(row) for row in reader]
        except (UnicodeError, csv.Error) as error:
            self.problems.malformed(
                f"{context}.postimages", f"cannot parse postimage manifest: {error}"
            )
            return {}, {}
        if header != INTEGRATION_AMENDMENT_MANIFEST_HEADER:
            self.problems.malformed(
                f"{context}.postimages",
                "header must be exactly: "
                + "\t".join(INTEGRATION_AMENDMENT_MANIFEST_HEADER),
            )
        if any(None in row or any(value is None for value in row.values()) for row in rows):
            self.problems.malformed(
                f"{context}.postimages", "malformed row or wrong column count"
            )
        manifest_paths = [row.get("path", "") for row in rows]
        if manifest_paths != expected_paths:
            self.problems.violation(
                f"{context}.postimages",
                "manifest rows must be sorted, unique, and exactly equal amendment paths",
            )
        postimages: dict[str, str] = {}
        preimage_digests: dict[str, str] = {}
        for index, row in enumerate(rows):
            row_context = f"{context}.postimages[{index}]"
            affected_value = row.get("path", "")
            oid_value = row.get("preimage_blob_oid", "")
            pre_digest_value = row.get("preimage_sha256", "")
            post_digest_value = row.get("postimage_sha256", "")
            affected = affected_value if isinstance(affected_value, str) else ""
            oid = oid_value if isinstance(oid_value, str) else ""
            pre_digest = (
                pre_digest_value if isinstance(pre_digest_value, str) else ""
            )
            post_digest = (
                post_digest_value if isinstance(post_digest_value, str) else ""
            )
            if oid != expected_preimages.get(affected):
                self.problems.violation(
                    f"{row_context}.preimage_blob_oid",
                    "manifest preimage OID must equal the request record",
                )
            if not SHA256_RE.fullmatch(pre_digest):
                self.problems.malformed(
                    f"{row_context}.preimage_sha256", "expected 64 hexadecimal characters"
                )
            elif affected:
                preimage_digests[affected] = pre_digest.upper()
            if not SHA256_RE.fullmatch(post_digest):
                self.problems.malformed(
                    f"{row_context}.postimage_sha256", "expected 64 hexadecimal characters"
                )
            if affected and SHA256_RE.fullmatch(post_digest):
                postimages[affected] = post_digest.upper()
                source: str | None = None
                source_label: str | None = None
                if status == "active":
                    source = f":{affected}"
                    source_label = "current index"
                elif (
                    status == "applied"
                    and isinstance(resolution_commit, str)
                    and SHA1_RE.fullmatch(resolution_commit)
                ):
                    source = f"{resolution_commit}:{affected}"
                    source_label = f"resolution commit {resolution_commit}"
                if source is not None and source_label is not None:
                    payload = self.run_git(
                        ["show", source], f"{row_context}.postimage_sha256"
                    )
                    if payload is not None:
                        actual = hashlib.sha256(payload).hexdigest().upper()
                        if actual != post_digest.upper():
                            self.problems.violation(
                                f"{row_context}.postimage_sha256",
                                f"{source_label} hashes to {actual}, not "
                                f"{post_digest.upper()}",
                            )
        return postimages, preimage_digests

    def validate_integration_amendment_predecessors(
        self,
        artifacts: list[Artifact | None],
        context: str,
        target_head: Any,
        expected_paths: list[str],
        expected_preimages: dict[str, str],
        expected_preimage_sha256: dict[str, str],
    ) -> None:
        """Prove each amendment preimage from HEAD or a pinned predecessor."""

        predecessor_overlaps: set[str] = set()
        chained: set[str] = set()
        for artifact_index, artifact in enumerate(artifacts):
            if artifact is None:
                continue
            predecessor_context = (
                f"{context}.predecessor_postimages[{artifact_index}]"
            )
            path = self.resolve_repo_path(
                artifact.path, f"{predecessor_context}.path"
            )
            if path is None or not path.is_file():
                continue
            try:
                raw = path.read_bytes()
                reader = csv.DictReader(
                    raw.decode("utf-8-sig").splitlines(), delimiter="\t", strict=True
                )
                header = tuple(reader.fieldnames or ())
                rows = [dict(row) for row in reader]
            except (OSError, UnicodeError, csv.Error) as error:
                self.problems.malformed(
                    predecessor_context,
                    f"cannot parse predecessor manifest: {error}",
                )
                continue
            if b"\r" in raw or (raw and not raw.endswith(b"\n")):
                self.problems.violation(
                    predecessor_context,
                    "predecessor manifest must use LF and end with a newline",
                )
            if header != INTEGRATION_AMENDMENT_MANIFEST_HEADER:
                self.problems.malformed(
                    predecessor_context,
                    "header must be exactly: "
                    + "\t".join(INTEGRATION_AMENDMENT_MANIFEST_HEADER),
                )
            if any(
                None in row or any(value is None for value in row.values())
                for row in rows
            ):
                self.problems.malformed(
                    predecessor_context, "malformed row or wrong column count"
                )
            predecessor_paths = [
                value if isinstance(value := row.get("path", ""), str) else ""
                for row in rows
            ]
            if predecessor_paths != sorted(set(predecessor_paths)):
                self.problems.violation(
                    predecessor_context, "rows must be unique and sorted by path"
                )
            artifact_chains = 0
            for row_index, row in enumerate(rows):
                affected_value = row.get("path", "")
                affected = (
                    affected_value if isinstance(affected_value, str) else ""
                )
                if affected not in expected_paths:
                    continue
                artifact_chains += 1
                row_context = f"{predecessor_context}[{row_index}]"
                if affected in predecessor_overlaps:
                    self.problems.violation(
                        row_context,
                        "amendment path appears in more than one predecessor manifest",
                    )
                predecessor_overlaps.add(affected)
                predecessor_post_value = row.get("postimage_sha256", "")
                predecessor_post = (
                    predecessor_post_value.upper()
                    if isinstance(predecessor_post_value, str)
                    else ""
                )
                expected_pre = expected_preimage_sha256.get(affected)
                if (
                    not SHA256_RE.fullmatch(predecessor_post)
                    or predecessor_post != expected_pre
                ):
                    self.problems.violation(
                        f"{row_context}.postimage_sha256",
                        "predecessor postimage must equal amendment preimage SHA-256",
                    )
                else:
                    chained.add(affected)
            if artifact_chains == 0:
                self.problems.violation(
                    predecessor_context,
                    "pinned predecessor manifest does not chain any amendment path",
                )

        if not isinstance(target_head, str) or not SHA1_RE.fullmatch(target_head):
            return
        for affected in expected_paths:
            output = self.run_git(
                ["rev-parse", f"{target_head}:{affected}"],
                f"{context}.preimage_blobs[{affected}]",
            )
            actual = (
                output.decode("ascii", errors="replace").strip()
                if output is not None
                else None
            )
            expected_oid = expected_preimages.get(affected)
            if actual == expected_oid:
                if affected in predecessor_overlaps:
                    self.problems.violation(
                        f"{context}.preimage_blobs[{affected}]",
                        "target-HEAD preimage must not also be claimed from a "
                        "predecessor manifest",
                    )
                payload = self.run_git(
                    ["show", f"{target_head}:{affected}"],
                    f"{context}.preimage_blobs[{affected}]",
                )
                expected_digest = expected_preimage_sha256.get(affected)
                if payload is not None and expected_digest is not None:
                    actual_digest = hashlib.sha256(payload).hexdigest().upper()
                    if actual_digest != expected_digest:
                        self.problems.violation(
                            f"{context}.preimage_blobs[{affected}]",
                            "target-HEAD blob hashes to "
                            f"{actual_digest}, not {expected_digest}",
                        )
                continue
            if affected not in chained:
                self.problems.violation(
                    f"{context}.preimage_blobs[{affected}]",
                    "preimage must equal the target-HEAD blob or chain from an "
                    "exact pinned predecessor postimage; "
                    f"target HEAD has {actual!r}, amendment records {expected_oid!r}",
                )

    def validate_cross_references(self) -> None:
        if not self.phase:
            return
        origin_id = self.phase.get("origin_checkpoint_id")
        current_id = self.phase.get("current_checkpoint_id")
        origin = self.checkpoints.get(origin_id)
        current = self.checkpoints.get(current_id)
        if origin is None:
            self.problems.violation("phase.json.origin_checkpoint_id", f"unknown checkpoint {origin_id}")
        if current is None:
            self.problems.violation("phase.json.current_checkpoint_id", f"unknown checkpoint {current_id}")
        if origin is not None:
            if origin.get("parent_checkpoint_id") is not None:
                self.problems.violation(f"checkpoint {origin_id}", "origin checkpoint must have null parent_checkpoint_id")
            if origin.get("commit_sha") != self.phase.get("base_policy", {}).get("immutable_origin_sha"):
                self.problems.violation("phase.json.base_policy.immutable_origin_sha", "must equal the origin checkpoint commit")
        self.validate_checkpoint_chain(origin_id, current_id)
        self.validate_milestone_graph()
        self.validate_checkpoint_evidence()

        scope_artifact = self.artifact(self.phase.get("scope"), "phase.json.scope")
        origin_sha = self.phase.get("base_policy", {}).get("immutable_origin_sha")
        if isinstance(origin_sha, str):
            self.scope_snapshot = self.validate_scope_snapshot(scope_artifact, origin_sha, "phase scope snapshot")
        known_waves = {wave for milestone in self.milestones.values() for wave in milestone.get("wave_ids", [])}
        if self.scope_snapshot is not None:
            missing_waves = sorted(self.scope_snapshot.in_scope_waves - known_waves)
            if missing_waves:
                self.problems.violation("phase scope snapshot", "in-scope wave(s) absent from milestones: " + ", ".join(missing_waves))
            self.validate_operational_queues()
        for milestone_id, milestone in sorted(self.milestones.items()):
            for wave in milestone.get("unblocks", []):
                if wave not in known_waves:
                    self.problems.violation(f"milestone {milestone_id}.unblocks", f"unknown wave {wave}")
        self.validate_projections()
        self.validate_branches(current_id)
        self.validate_requests(current_id)
        self.validate_completion(current_id)
        if self.phase.get("status") == "closed" and self.phase.get("completion", {}).get("bounded_phase", {}).get("status") != "complete":
            self.problems.violation("phase.json.status", "a closed phase must have complete bounded-phase evidence")
        if self.phase.get("completion", {}).get("repository_wide", {}).get("status") == "complete" and self.phase.get("status") != "closed":
            self.problems.violation("phase.json.status", "repository-wide completion requires phase status closed")

    def validate_checkpoint_chain(self, origin_id: str, current_id: str) -> None:
        for checkpoint_id, checkpoint in sorted(self.checkpoints.items()):
            parent_id = checkpoint.get("parent_checkpoint_id")
            if parent_id is not None and parent_id not in self.checkpoints:
                self.problems.violation(f"checkpoint {checkpoint_id}", f"unknown parent checkpoint {parent_id}")
            elif parent_id is not None:
                parent_sha = self.checkpoints[parent_id].get("commit_sha")
                child_sha = checkpoint.get("commit_sha")
                if isinstance(parent_sha, str) and isinstance(child_sha, str) and not self.is_ancestor(parent_sha, child_sha, f"checkpoint {checkpoint_id}"):
                    self.problems.violation(f"checkpoint {checkpoint_id}", f"parent commit {parent_sha} is not an ancestor of {child_sha}")
        visiting: set[str] = set()
        visited: set[str] = set()

        def visit(checkpoint_id: str) -> None:
            if checkpoint_id in visiting:
                self.problems.violation("checkpoints", f"parent cycle includes {checkpoint_id}")
                return
            if checkpoint_id in visited or checkpoint_id not in self.checkpoints:
                return
            visiting.add(checkpoint_id)
            parent = self.checkpoints[checkpoint_id].get("parent_checkpoint_id")
            if isinstance(parent, str):
                visit(parent)
            visiting.remove(checkpoint_id)
            visited.add(checkpoint_id)

        for checkpoint_id in sorted(self.checkpoints):
            visit(checkpoint_id)
        if current_id in self.checkpoints:
            cursor: str | None = current_id
            seen: set[str] = set()
            while cursor is not None and cursor in self.checkpoints and cursor not in seen:
                seen.add(cursor)
                cursor = self.checkpoints[cursor].get("parent_checkpoint_id")
            if origin_id not in seen:
                self.problems.violation("phase.json.current_checkpoint_id", "current checkpoint does not descend from the origin checkpoint")

    def validate_milestone_graph(self) -> None:
        visiting: set[str] = set()
        visited: set[str] = set()

        def visit(milestone_id: str) -> None:
            if milestone_id in visiting:
                self.problems.violation("phase.json.milestones", f"dependency cycle includes {milestone_id}")
                return
            if milestone_id in visited:
                return
            milestone = self.milestones.get(milestone_id)
            if milestone is None:
                return
            visiting.add(milestone_id)
            for dependency in milestone.get("depends_on", []):
                if dependency not in self.milestones:
                    self.problems.violation(f"milestone {milestone_id}", f"unknown dependency {dependency}")
                else:
                    visit(dependency)
            visiting.remove(milestone_id)
            visited.add(milestone_id)

        for milestone_id in sorted(self.milestones):
            visit(milestone_id)
        for milestone_id, milestone in sorted(self.milestones.items()):
            superseded_by = milestone.get("superseded_by")
            if superseded_by is not None and superseded_by not in self.milestones:
                self.problems.violation(f"milestone {milestone_id}", f"unknown superseding milestone {superseded_by}")
        for milestone_id in sorted(self.milestones):
            cursor: str | None = milestone_id
            seen: set[str] = set()
            while cursor is not None and cursor in self.milestones:
                if cursor in seen:
                    self.problems.violation("phase.json.milestones", f"supersession cycle includes {cursor}")
                    break
                seen.add(cursor)
                cursor = self.milestones[cursor].get("superseded_by")
        wave_owner: dict[str, str] = {}
        for milestone_id, milestone in sorted(self.milestones.items()):
            if milestone.get("status") == "superseded":
                continue
            for wave in milestone.get("wave_ids", []):
                if wave in wave_owner:
                    self.problems.violation("phase.json.milestones", f"wave {wave} is owned by both {wave_owner[wave]} and {milestone_id}")
                wave_owner[wave] = milestone_id

        def dependency_closure(milestone_id: str) -> set[str]:
            result: set[str] = set()
            pending = [milestone_id]
            while pending:
                cursor = pending.pop()
                if cursor in result or cursor not in self.milestones:
                    continue
                result.add(cursor)
                pending.extend(self.milestones[cursor].get("depends_on", []))
            return result

        for milestone_id, milestone in sorted(self.milestones.items()):
            if milestone.get("status") == "superseded":
                continue
            implied_accepted = dependency_closure(milestone_id)
            for wave in milestone.get("unblocks", []):
                target_id = wave_owner.get(wave)
                if target_id is None:
                    continue
                target_dependencies = set(
                    self.milestones[target_id].get("depends_on", [])
                )
                if not target_dependencies or not target_dependencies <= implied_accepted:
                    missing = sorted(target_dependencies - implied_accepted)
                    detail = (
                        "target wave has no dependencies"
                        if not target_dependencies
                        else "acceptance does not imply " + ", ".join(missing)
                    )
                    self.problems.violation(
                        f"milestone {milestone_id}.unblocks",
                        f"cannot safely unblock {wave}: {detail}",
                    )

    def validate_checkpoint_evidence(self) -> None:
        known_waves = {
            wave
            for milestone in self.milestones.values()
            for wave in milestone.get("wave_ids", [])
        }
        for checkpoint_id, checkpoint in sorted(self.checkpoints.items()):
            commit = checkpoint.get("commit_sha")
            if isinstance(commit, str):
                self.validate_combined_baseline(
                    checkpoint_id,
                    commit,
                    checkpoint.get("_baseline_format_version"),
                    checkpoint.get("_baseline_artifact"),
                    checkpoint.get("_baseline_summary_artifact"),
                )
                snapshot = self.validate_scope_snapshot(checkpoint.get("_inventory_artifact"), commit, f"checkpoint {checkpoint_id} inventory")
                if snapshot is not None:
                    self.checkpoint_inventory[checkpoint_id] = snapshot
                    unknown_waves = sorted(snapshot.in_scope_waves - known_waves)
                    if unknown_waves:
                        self.problems.violation(
                            f"checkpoint {checkpoint_id} inventory",
                            "in-scope wave(s) absent from milestones: " + ", ".join(unknown_waves),
                        )
                    recorded_metrics = checkpoint.get("metrics", {})
                    for key, expected in snapshot.metrics.items():
                        if recorded_metrics.get(key) != expected:
                            self.problems.violation(f"checkpoint {checkpoint_id}.metrics.{key}", f"expected {expected} from inventory, found {recorded_metrics.get(key)!r}")
            gate_map = checkpoint.get("_gate_map", {})
            missing_or_unpassed = sorted(
                gate_id
                for gate_id in REQUIRED_CHECKPOINT_GATES
                if gate_map.get(gate_id, {}).get("status") != "PASS"
            )
            if missing_or_unpassed:
                self.problems.violation(
                    f"checkpoint {checkpoint_id}.gates",
                    "mandatory checkpoint gate(s) are absent or not PASS: "
                    + ", ".join(missing_or_unpassed),
                )
            failed_gates = sorted(
                gate_id
                for gate_id, gate in checkpoint.get("_gate_map", {}).items()
                if gate.get("status") == "FAIL"
            )
            if failed_gates:
                self.problems.violation(
                    f"checkpoint {checkpoint_id}.gates",
                    "accepted checkpoints must not record failed gates: " + ", ".join(failed_gates),
                )
            named = set(checkpoint.get("milestones_satisfied", []))
            unknown = sorted(named - set(self.milestones))
            if unknown:
                self.problems.violation(f"checkpoint {checkpoint_id}.milestones_satisfied", "unknown milestone(s): " + ", ".join(unknown))
        for milestone_id, milestone in sorted(self.milestones.items()):
            status = milestone.get("status")
            accepted_id = milestone.get("accepted_checkpoint_id")
            if status != "accepted":
                continue
            checkpoint = self.checkpoints.get(accepted_id)
            if checkpoint is None:
                self.problems.violation(f"milestone {milestone_id}", f"unknown accepted checkpoint {accepted_id}")
                continue
            if milestone_id not in checkpoint.get("milestones_satisfied", []):
                self.problems.violation(f"milestone {milestone_id}", f"checkpoint {accepted_id} does not list the milestone as satisfied")
            for dependency in milestone.get("depends_on", []):
                dependency_record = self.milestones.get(dependency)
                if dependency_record is not None and dependency_record.get("status") != "accepted":
                    self.problems.violation(f"milestone {milestone_id}", f"dependency {dependency} is not accepted")
                elif dependency_record is not None and isinstance(dependency_record.get("accepted_checkpoint_id"), str):
                    if not self.checkpoint_descends(accepted_id, dependency_record["accepted_checkpoint_id"]):
                        self.problems.violation(f"milestone {milestone_id}", f"accepted checkpoint {accepted_id} does not descend from dependency {dependency}'s checkpoint")
            gate_map = checkpoint.get("_gate_map", {})
            for gate_id in milestone.get("acceptance_gate_ids", []):
                gate = gate_map.get(gate_id)
                if gate is None or gate.get("status") != "PASS":
                    self.problems.violation(f"milestone {milestone_id}", f"acceptance gate {gate_id} did not pass at checkpoint {accepted_id}")
        for checkpoint_id, checkpoint in sorted(self.checkpoints.items()):
            expected = {
                milestone_id
                for milestone_id, milestone in self.milestones.items()
                if milestone.get("status") == "accepted"
                and isinstance(milestone.get("accepted_checkpoint_id"), str)
                and self.checkpoint_descends(checkpoint_id, milestone["accepted_checkpoint_id"])
            }
            recorded = set(checkpoint.get("milestones_satisfied", []))
            if recorded != expected:
                self.problems.violation(f"checkpoint {checkpoint_id}.milestones_satisfied", f"expected {sorted(expected)}, found {sorted(recorded)}")
            expected_unblocks = sorted(
                {
                    wave
                    for milestone_id in recorded
                    for wave in self.milestones[milestone_id].get("unblocks", [])
                }
            )
            if checkpoint.get("unblocks", []) != expected_unblocks:
                self.problems.violation(f"checkpoint {checkpoint_id}.unblocks", f"expected {expected_unblocks}, found {checkpoint.get('unblocks', [])}")

    def checkpoint_descends(self, descendant_id: str, ancestor_id: str) -> bool:
        cursor: str | None = descendant_id
        seen: set[str] = set()
        while cursor is not None and cursor in self.checkpoints and cursor not in seen:
            if cursor == ancestor_id:
                return True
            seen.add(cursor)
            cursor = self.checkpoints[cursor].get("parent_checkpoint_id")
        return False

    def validate_projections(self) -> None:
        scope_rows = self.scope_snapshot.rows if self.scope_snapshot is not None else []
        for projection_id, projection in sorted(self.projections.items()):
            context = f"projection {projection_id}"
            checkpoint_id = projection.get("base_checkpoint_id")
            checkpoint = self.checkpoints.get(checkpoint_id)
            if checkpoint is None:
                self.problems.violation(context, f"unknown base checkpoint {checkpoint_id}")
            else:
                expected = checkpoint.get("_baseline_artifact")
                actual = projection.get("_combined_artifact")
                if isinstance(expected, Artifact) and isinstance(actual, Artifact) and expected != actual:
                    self.problems.violation(context, "combined_baseline must exactly match the base checkpoint artifact")
            if (
                projection.get("status") == "active"
                and checkpoint_id != self.phase.get("current_checkpoint_id")
            ):
                self.problems.violation(
                    context,
                    "active projection must be tied to the current checkpoint",
                )
            wave_id = projection.get("wave_id")
            selector_artifact = projection.get("_selector_artifact")
            if isinstance(wave_id, str) and isinstance(selector_artifact, Artifact):
                expected_selector_path = self.relative_context(
                    self.phase_dir / "selectors" / f"{wave_id}.tsv"
                )
                if selector_artifact.path != expected_selector_path:
                    self.problems.violation(
                        f"{context}.selector.artifact.path",
                        f"wave selector must be {expected_selector_path}",
                    )
            selector_rows = projection.get("_selector_rows", [])
            expected_rows = sorted(
                (
                    {"module": row["module"], "path": row["path"]}
                    for row in scope_rows
                    if row["phase_scope"] == "in_scope" and row["wave_id"] == wave_id
                ),
                key=lambda row: row["module"],
            )
            if not expected_rows:
                self.problems.violation(
                    context,
                    f"wave {wave_id!r} has no immutable in-scope rows",
                )
            if selector_rows != expected_rows:
                self.problems.violation(
                    f"{context}.selector",
                    "selector rows must exactly equal the immutable scope rows for the wave",
                )
            self.validate_projection_graph(
                projection_id,
                projection.get("_projection_graph_artifact"),
                projection.get("expected_counts"),
                selector_rows,
            )
            superseded_by = projection.get("superseded_by")
            if superseded_by is not None and superseded_by not in self.projections:
                self.problems.violation(context, f"unknown superseding projection {superseded_by}")

    def validate_branches(self, current_id: str) -> None:
        live_statuses = {"planned", "active", "delivered"}
        branch_names: dict[str, str] = {}
        live: list[tuple[str, dict[str, Any]]] = []
        known_waves = {wave for milestone in self.milestones.values() for wave in milestone.get("wave_ids", [])}
        scope_rows = self.scope_snapshot.rows if self.scope_snapshot is not None else []
        for branch_id, branch in sorted(self.branches.items()):
            context = branch.get("_context", f"branch {branch_id}")
            status = branch.get("status")
            name = branch.get("branch_name")
            if isinstance(name, str):
                if name in branch_names:
                    self.problems.violation(context, f"branch_name duplicates {branch_names[name]}")
                branch_names[name] = branch_id
            lane_id = branch.get("lane_id")
            lane = self.lanes.get(lane_id)
            branch_operators = branch.get("operator_ids", [])
            for operator in branch_operators:
                if operator not in self.principals:
                    self.problems.violation(
                        context, f"operator {operator} is an unknown principal"
                    )
            if lane is None:
                self.problems.violation(context, f"unknown lane_id {lane_id}")
            else:
                if branch.get("owner_id") != lane.get("owner_id"):
                    self.problems.violation(context, "owner_id must equal the lane owner")
                if status in live_statuses:
                    allowed_operators = set(lane.get("operator_ids", []))
                    for operator in branch_operators:
                        if operator not in allowed_operators:
                            self.problems.violation(context, f"operator {operator} is not authorized for lane {lane_id}")
            if branch.get("wave_id") not in known_waves:
                self.problems.violation(context, f"unknown wave_id {branch.get('wave_id')}")
            wave_rows = [
                row
                for row in scope_rows
                if row["phase_scope"] == "in_scope"
                and row["wave_id"] == branch.get("wave_id")
            ]
            wave_lanes = {row["lane_id"] for row in wave_rows}
            if len(wave_lanes) != 1 or branch.get("lane_id") not in wave_lanes:
                self.problems.violation(
                    context,
                    "branch lane_id must equal the unique lane assigned to its wave in immutable scope",
                )
            base_id = branch.get("base_checkpoint_id")
            base = self.checkpoints.get(base_id)
            if base is None:
                self.problems.violation(context, f"unknown base checkpoint {base_id}")
            elif branch.get("base_sha") != base.get("commit_sha"):
                self.problems.violation(context, "base_sha must equal the base checkpoint commit")
            projection_id = branch.get("baseline_projection_id")
            projection = self.projections.get(projection_id)
            if projection is None:
                self.problems.violation(context, f"unknown baseline projection {projection_id}")
            else:
                if status in live_statuses and projection.get("status") != "active":
                    self.problems.violation(context, "live branch must reference an active baseline projection")
                if status not in live_statuses and projection.get("status") == "active":
                    self.problems.violation(context, "terminal branch must not keep its baseline projection active")
                if projection.get("wave_id") != branch.get("wave_id"):
                    self.problems.violation(context, "projection wave_id does not match branch wave_id")
            owned = branch.get("_owned_rules", [])
            destinations = branch.get("_destination_rules", [])
            forbidden = branch.get("_forbidden_rules", [])
            if not owned:
                self.problems.malformed(context, "owned_paths must not be empty")
            expected_owned = sorted(
                PathRule("exact", row["path"]) for row in wave_rows
            )
            if owned != expected_owned:
                self.problems.violation(
                    f"{context}.owned_paths",
                    "owned_paths must be exact rules for every and only immutable scope path assigned to the wave",
                )
            for own in owned:
                for shared in self.shared_paths:
                    if own.intersects(shared):
                        self.problems.violation(context, f"owned path {own.path} overlaps integrator-owned shared path {shared.path}")
                for blocked in forbidden:
                    if own.intersects(blocked):
                        self.problems.violation(context, f"owned path {own.path} overlaps forbidden path {blocked.path}")
            other_existing = [
                PathRule("exact", row["path"])
                for row in scope_rows
                if row["path"] not in {wave_row["path"] for wave_row in wave_rows}
            ]
            # An exact destination rule authorizes creating exactly one new
            # file, which is strictly narrower than any prefix rule. To keep it
            # from ever claiming an existing module it must name a path that is
            # absent at the branch's base commit.
            base_sha_for_destinations = branch.get("base_sha")
            for destination in destinations:
                if destination.match == "exact":
                    if not isinstance(base_sha_for_destinations, str) or not SHA1_RE.fullmatch(
                        base_sha_for_destinations
                    ):
                        self.problems.malformed(
                            f"{context}.destination_prefixes",
                            "exact destination rules require a valid base_sha to"
                            " prove the path is new",
                        )
                    else:
                        probe = subprocess.run(
                            [
                                "git",
                                "cat-file",
                                "-e",
                                f"{base_sha_for_destinations}:{destination.path}",
                            ],
                            cwd=self.root,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE,
                            check=False,
                        )
                        if probe.returncode == 0:
                            self.problems.violation(
                                context,
                                "exact destination "
                                f"{destination.path} already exists at base "
                                f"{base_sha_for_destinations}; exact destination"
                                " rules may only create new files",
                            )
                for own in owned:
                    if destination.intersects(own):
                        self.problems.violation(
                            context,
                            f"destination prefix {destination.path} overlaps existing owned path {own.path}",
                        )
                for shared in self.shared_paths:
                    if destination.intersects(shared):
                        self.problems.violation(
                            context,
                            f"destination prefix {destination.path} overlaps integrator-owned shared path {shared.path}",
                        )
                for blocked in forbidden:
                    if destination.intersects(blocked):
                        self.problems.violation(
                            context,
                            f"destination prefix {destination.path} overlaps forbidden path {blocked.path}",
                        )
                overlaps = sorted(
                    rule.path for rule in other_existing if destination.intersects(rule)
                )
                if overlaps:
                    self.problems.violation(
                        context,
                        f"destination prefix {destination.path} overlaps existing paths outside the wave: "
                        + ", ".join(overlaps),
                    )
            refresh = branch.get("refresh", {})
            if status in live_statuses:
                live.append((branch_id, branch))
                if refresh.get("reviewed_checkpoint_id") != current_id:
                    self.problems.violation(context, "live branch refresh must be reviewed against the current checkpoint")
                if base_id == current_id and refresh.get("decision") == "validated_no_overlap":
                    self.problems.violation(context, "validated_no_overlap is only for a branch retained on an older base")
                if base_id != current_id:
                    if status == "planned" and self.phase.get("base_policy", {}).get("new_branch_must_use_current_checkpoint"):
                        self.problems.violation(context, "planned branch must start from the current checkpoint")
                    if refresh.get("decision") != "validated_no_overlap" or not refresh.get("_evidence"):
                        self.problems.violation(context, "live branch on an older base requires validated_no_overlap and hashed refresh evidence")
                elif refresh.get("decision") not in {"current", "rebased"}:
                    self.problems.violation(context, "branch on current base must use refresh decision current or rebased")
                if projection is not None and projection.get("base_checkpoint_id") != current_id:
                    self.problems.violation(context, "live branch projection must be refreshed against the current checkpoint")
                milestone_records = [
                    milestone
                    for milestone in self.milestones.values()
                    if branch.get("wave_id") in milestone.get("wave_ids", [])
                    and milestone.get("status") != "superseded"
                ]
                if status in live_statuses:
                    for milestone in milestone_records:
                        for dependency in milestone.get("depends_on", []):
                            if self.milestones.get(dependency, {}).get("status") != "accepted":
                                self.problems.violation(context, f"branch cannot be {status} before dependency milestone {dependency} is accepted")
            delivery = branch.get("delivery", {})
            delivery_sha = delivery.get("commit_sha")
            delivery_required = status in {"delivered", "accepted", "retired"}
            if delivery_required and not isinstance(delivery_sha, str):
                self.problems.malformed(context, f"{status} branch requires delivery.commit_sha")
            if delivery_required and (delivery.get("_report") is None or delivery.get("_scope_evidence") is None):
                self.problems.malformed(context, f"{status} branch requires hash-pinned delivery report and scope evidence")
            if not delivery_required and delivery_sha is not None and status not in {"superseded", "cancelled"}:
                self.problems.violation(context, "delivery.commit_sha is premature for this status")
            if isinstance(delivery_sha, str):
                if self.commit_exists(delivery_sha, f"{context}.delivery.commit_sha") and isinstance(branch.get("base_sha"), str):
                    if not self.is_ancestor(branch["base_sha"], delivery_sha, context):
                        self.problems.violation(context, "delivery commit does not descend from branch base")
                    self.validate_branch_diff(branch, delivery_sha, context)
            integration = branch.get("integration", {})
            integrated_required = status in {"accepted", "retired"}
            integration_values = [integration.get("method"), integration.get("accepted_checkpoint_id"), integration.get("accepted_sha")]
            if integrated_required and any(value is None for value in integration_values):
                self.problems.malformed(context, f"{status} branch requires complete integration metadata")
            if not integrated_required and any(value is not None for value in integration_values) and status not in {"superseded", "cancelled"}:
                self.problems.violation(context, "integration metadata is premature for this status")
            accepted_id = integration.get("accepted_checkpoint_id")
            if isinstance(accepted_id, str):
                accepted = self.checkpoints.get(accepted_id)
                if accepted is None:
                    self.problems.violation(context, f"unknown accepted checkpoint {accepted_id}")
                else:
                    if integration.get("accepted_sha") != accepted.get("commit_sha"):
                        self.problems.violation(context, "integration.accepted_sha must equal the accepted checkpoint commit")
                    if isinstance(delivery_sha, str) and not self.is_ancestor(delivery_sha, accepted["commit_sha"], context):
                        self.problems.violation(context, "delivery commit must be an ancestor of the accepted checkpoint before branch acceptance or retirement")
            retirement = branch.get("retirement", {})
            if name is not None and retirement.get("remote_ref") != f"refs/heads/{name}":
                self.problems.violation(context, "retirement.remote_ref must correspond to branch_name")
            retired_fields = [retirement.get("retired_at"), retirement.get("retired_by"), retirement.get("ancestry_checkpoint_id")]
            if status == "retired":
                if retirement.get("status") != "retired" or any(value is None for value in retired_fields):
                    self.problems.malformed(context, "retired branch requires retired status, timestamp, authority, and ancestry checkpoint")
                if retirement.get("retired_by") not in self.phase.get("authority", {}).get("branch_registry_authority_ids", []):
                    self.problems.violation(context, "branch retirement must be recorded by branch-registry authority")
                if retirement.get("ancestry_checkpoint_id") != accepted_id:
                    self.problems.violation(context, "retirement ancestry checkpoint must equal integration accepted checkpoint")
            elif retirement.get("status") == "retired" or any(value is not None for value in retired_fields):
                self.problems.violation(context, "retirement evidence may appear only when branch status is retired")
        for index, (left_id, left) in enumerate(live):
            for right_id, right in live[index + 1 :]:
                left_rules = left.get("_owned_rules", []) + left.get("_destination_rules", [])
                right_rules = right.get("_owned_rules", []) + right.get("_destination_rules", [])
                for left_rule in left_rules:
                    for right_rule in right_rules:
                        if left_rule.intersects(right_rule):
                            self.problems.violation("branch ownership", f"live branches {left_id} and {right_id} overlap at {left_rule.path!r} / {right_rule.path!r}")

    def validate_branch_diff(self, branch: dict[str, Any], delivery_sha: str, context: str) -> None:
        base_sha = branch.get("base_sha")
        if not isinstance(base_sha, str):
            return
        raw = self.run_git(["diff", "--name-only", "-z", f"{base_sha}..{delivery_sha}"], context)
        if raw is None:
            return
        paths = sorted(item.decode("utf-8", errors="replace") for item in raw.split(b"\0") if item)
        owned = branch.get("_owned_rules", []) + branch.get("_destination_rules", [])
        forbidden = branch.get("_forbidden_rules", [])
        for path in paths:
            if not any(rule.matches(path) for rule in owned):
                self.problems.violation(context, f"delivery changed unowned path {path}")
            if any(rule.matches(path) for rule in forbidden):
                self.problems.violation(context, f"delivery changed forbidden path {path}")
            if any(rule.matches(path) for rule in self.shared_paths):
                self.problems.violation(context, f"delivery changed integrator-owned shared path {path}")

    def blob_at(self, commit: str, path: str, context: str) -> str | None:
        raw = self.run_git(["ls-tree", "-z", commit, "--", path], context)
        if raw is None or not raw:
            return None
        entries = [entry for entry in raw.split(b"\0") if entry]
        if len(entries) != 1:
            self.problems.violation(context, f"expected at most one tree entry for {path}")
            return None
        try:
            metadata, returned_path = entries[0].split(b"\t", 1)
            _mode, kind, oid = metadata.decode("ascii").split()
            decoded_path = returned_path.decode("utf-8")
        except (ValueError, UnicodeError) as error:
            self.problems.malformed(context, f"cannot parse git ls-tree output: {error}")
            return None
        return oid if kind == "blob" and decoded_path == path else None

    def validate_requests(self, current_id: str) -> None:
        for request_id, request in sorted(self.requests.items()):
            if request.get("record_kind") == INTEGRATION_AMENDMENT_KIND:
                self.validate_integration_amendment(request_id, request)
                continue
            context = request.get("_context", f"request {request_id}")
            status = request.get("status")
            lane_id = request.get("lane_id")
            lane = self.lanes.get(lane_id)
            if lane is None:
                self.problems.violation(context, f"unknown lane_id {lane_id}")
            else:
                allowed = {lane.get("owner_id"), *lane.get("operator_ids", [])}
                if request.get("requester_id") not in allowed:
                    self.problems.violation(context, "requester is not the lane owner or an authorized operator")
            target_id = request.get("target_checkpoint_id")
            target = self.checkpoints.get(target_id)
            if target is None:
                self.problems.violation(context, f"unknown target checkpoint {target_id}")
            elif request.get("target_base_sha") != target.get("commit_sha"):
                self.problems.violation(context, "target_base_sha must equal target checkpoint commit")
            if request.get("valid_through_checkpoint_id") != target_id:
                self.problems.violation(context, "valid_through_checkpoint_id must equal target_checkpoint_id; refresh by superseding the request")
            for path in request.get("paths", []):
                # Shared ownership is a live reservation, not a permanent claim.
                # Terminal requests preserve their historical contract through
                # immutable preimages, the hash-pinned patch, and resolution
                # evidence, while allowing a later checkpoint to release the
                # path to a new branch owner.
                if status in {"draft", "active"} and not any(
                    rule.matches(path) for rule in self.shared_paths
                ):
                    self.problems.violation(context, f"requested path is not integrator-owned shared state: {path}")
                if isinstance(request.get("target_base_sha"), str):
                    actual = self.blob_at(request["target_base_sha"], path, context)
                    expected = request.get("_preimages", {}).get(path)
                    if actual != expected:
                        self.problems.violation(context, f"preimage blob mismatch for {path}: expected {actual!r}, found {expected!r}")
            for dependency in request.get("depends_on", []):
                milestone = self.milestones.get(dependency)
                if milestone is None:
                    self.problems.violation(context, f"unknown dependency milestone {dependency}")
                elif milestone.get("status") != "accepted":
                    self.problems.violation(context, f"dependency milestone {dependency} is not accepted")
                elif target_id in self.checkpoints and isinstance(milestone.get("accepted_checkpoint_id"), str):
                    if not self.checkpoint_descends(target_id, milestone["accepted_checkpoint_id"]):
                        self.problems.violation(context, f"target checkpoint does not include dependency milestone {dependency}")
            known_waves = {wave for milestone in self.milestones.values() for wave in milestone.get("wave_ids", [])}
            if request.get("wave_id") not in known_waves:
                self.problems.violation(context, f"unknown wave_id {request.get('wave_id')}")
            for wave in request.get("blocks", []):
                if wave not in known_waves:
                    self.problems.violation(context, f"blocks names unknown wave {wave}")
            if status in {"draft", "active"} and target_id != current_id:
                self.problems.violation(
                    context,
                    f"{status} request is expired because it does not target the current checkpoint",
                )
            supersedes = request.get("supersedes")
            superseded_by = request.get("superseded_by")
            if supersedes is not None and supersedes not in self.requests:
                self.problems.violation(context, f"unknown superseded request {supersedes}")
            if status == "superseded":
                if superseded_by is None or superseded_by not in self.requests:
                    self.problems.violation(context, "superseded request must name an existing superseding request")
                elif self.requests[superseded_by].get("supersedes") != request_id:
                    self.problems.violation(context, "superseding request does not point back through supersedes")
            elif superseded_by is not None:
                self.problems.violation(context, "only superseded requests may name superseded_by")
            resolution = request.get("resolution", {})
            resolution_values = [resolution.get("commit_sha"), resolution.get("checkpoint_id"), resolution.get("resolved_at"), resolution.get("resolved_by")]
            if status in {"draft", "active"}:
                if any(value is not None for value in resolution_values) or resolution.get("reason") is not None or resolution.get("_evidence"):
                    self.problems.violation(context, f"{status} request must have an empty resolution")
            elif status == "applied":
                if any(value is None for value in resolution_values) or not resolution.get("_evidence"):
                    self.problems.malformed(context, "applied request requires commit, checkpoint, timestamp, resolver, and validation evidence")
                self.validate_request_resolution(request, context, require_commit=True)
            else:
                if resolution.get("resolved_at") is None or resolution.get("resolved_by") is None or resolution.get("reason") is None:
                    self.problems.malformed(context, f"{status} request requires resolver, timestamp, and reason")
                self.validate_request_resolution(request, context, require_commit=False)
        for request_id, request in sorted(self.requests.items()):
            seen: set[str] = set()
            cursor: str | None = request_id
            while cursor is not None and cursor in self.requests:
                if cursor in seen:
                    self.problems.violation("shared requests", f"supersession cycle includes {cursor}")
                    break
                seen.add(cursor)
                cursor = self.requests[cursor].get("superseded_by")
        for branch_id, branch in sorted(self.branches.items()):
            for request_id in branch.get("shared_request_ids", []):
                request = self.requests.get(request_id)
                if request is None:
                    self.problems.violation(f"branch {branch_id}", f"unknown shared request {request_id}")
                elif request.get("record_kind") != "shared_file_request":
                    self.problems.violation(
                        f"branch {branch_id}",
                        f"shared_request_ids may name only shared_file_request records, not {request_id}",
                    )
                elif request.get("lane_id") != branch.get("lane_id") or request.get("wave_id") != branch.get("wave_id"):
                    self.problems.violation(f"branch {branch_id}", f"shared request {request_id} belongs to another lane or wave")

    def validate_integration_amendment(
        self, request_id: str, request: dict[str, Any]
    ) -> None:
        context = request.get("_context", f"request {request_id}")
        status = request.get("status")
        lane_id = request.get("lane_id")
        lane = self.lanes.get(lane_id)
        if lane is None:
            self.problems.violation(context, f"unknown lane_id {lane_id}")
        else:
            allowed = {lane.get("owner_id"), *lane.get("operator_ids", [])}
            if request.get("requester_id") not in allowed:
                self.problems.violation(
                    context, "requester is not the lane owner or an authorized operator"
                )
        authority = self.phase.get("authority", {})
        if lane_id != "integration-lane":
            self.problems.violation(
                context, "integration amendments must use integration-lane"
            )
        if request.get("requester_id") != authority.get("integration_authority_id"):
            self.problems.violation(
                context, "integration amendment must be issued by integration authority"
            )
        if request.get("requester_id") not in authority.get(
            "shared_path_authority_ids", []
        ):
            self.problems.violation(
                context, "integration amendment issuer must also hold shared-path authority"
            )
        target_head = request.get("target_head_sha")
        if isinstance(target_head, str) and self.commit_exists(
            target_head, f"{context}.target_head_sha"
        ):
            current = self.run_git(["rev-parse", "HEAD"], f"{context}.target_head_sha")
            if current is not None:
                current_sha = current.decode("ascii", errors="replace").strip()
                if SHA1_RE.fullmatch(current_sha) and not self.is_ancestor(
                    target_head, current_sha, f"{context}.target_head_sha"
                ):
                    self.problems.violation(
                        context, "target_head_sha must remain an ancestor of current HEAD"
                    )
        for dependency in request.get("_depends_on", []):
            dependency_record = self.requests.get(dependency)
            if dependency_record is None:
                self.problems.violation(
                    context, f"unknown dependency request {dependency}"
                )
            elif dependency_record.get("status") not in {"active", "applied"}:
                self.problems.violation(
                    context,
                    f"dependency request {dependency} must be active or applied",
                )
        known_waves = {
            wave
            for milestone in self.milestones.values()
            for wave in milestone.get("wave_ids", [])
        }
        for wave in request.get("_blocks", []):
            if wave not in known_waves:
                self.problems.violation(context, f"blocks names unknown wave {wave}")
        expected_evidence_paths = {
            self.relative_context(
                self.phase_dir / "requests" / f"{request_id}{suffix}"
            )
            for suffix in (
                ".json",
                ".patch",
                "-postimages.tsv",
                "-review.md",
                "-approval.md",
            )
        }
        blocked_waves = set(request.get("_blocks", []))
        for branch_id, branch in sorted(self.branches.items()):
            evidence = (branch.get("refresh") or {}).get("_evidence", [])
            evidence_paths = [
                artifact.path for artifact in evidence if artifact is not None
            ]
            counts = {
                path: evidence_paths.count(path) for path in expected_evidence_paths
            }
            if branch.get("wave_id") in blocked_waves:
                for path, count in sorted(counts.items()):
                    if count != 1:
                        self.problems.violation(
                            f"branch {branch_id}.refresh.evidence",
                            f"blocked branch must hash-pin exactly one {path}",
                        )
            elif any(counts.values()):
                self.problems.violation(
                    f"branch {branch_id}.refresh.evidence",
                    f"non-blocked branch must not pin {request_id} amendment artifacts",
                )
        supersedes = request.get("supersedes")
        superseded_by = request.get("superseded_by")
        if supersedes is not None and supersedes not in self.requests:
            self.problems.violation(context, f"unknown superseded request {supersedes}")
        if status == "superseded":
            if superseded_by is None or superseded_by not in self.requests:
                self.problems.violation(
                    context, "superseded amendment must name an existing successor"
                )
            elif self.requests[superseded_by].get("supersedes") != request_id:
                self.problems.violation(
                    context, "superseding request does not point back through supersedes"
                )
        elif superseded_by is not None:
            self.problems.violation(
                context, "only superseded amendments may name superseded_by"
            )
        resolution = request.get("resolution", {})
        resolution_values = [
            resolution.get("commit_sha"),
            resolution.get("checkpoint_id"),
            resolution.get("resolved_at"),
            resolution.get("resolved_by"),
        ]
        if status in {"draft", "active"}:
            if (
                any(value is not None for value in resolution_values)
                or resolution.get("reason") is not None
                or resolution.get("_evidence")
            ):
                self.problems.violation(
                    context, f"{status} amendment must have an empty resolution"
                )
        elif status == "applied":
            if any(value is None for value in resolution_values) or not resolution.get(
                "_evidence"
            ):
                self.problems.malformed(
                    context,
                    "applied amendment requires commit, checkpoint, timestamp, resolver, and validation evidence",
                )
            self.validate_request_resolution(request, context, require_commit=True)
        else:
            if (
                resolution.get("resolved_at") is None
                or resolution.get("resolved_by") is None
                or resolution.get("reason") is None
            ):
                self.problems.malformed(
                    context, f"{status} amendment requires resolver, timestamp, and reason"
                )
            self.validate_request_resolution(request, context, require_commit=False)

    def validate_request_resolution(self, request: dict[str, Any], context: str, *, require_commit: bool) -> None:
        resolution = request.get("resolution", {})
        resolved_by = resolution.get("resolved_by")
        if resolved_by is not None and resolved_by not in self.phase.get("authority", {}).get("shared_path_authority_ids", []):
            self.problems.violation(context, "request resolution must be recorded by shared-path authority")
        checkpoint_id = resolution.get("checkpoint_id")
        checkpoint = self.checkpoints.get(checkpoint_id) if isinstance(checkpoint_id, str) else None
        if checkpoint_id is not None and checkpoint is None:
            self.problems.violation(context, f"unknown resolution checkpoint {checkpoint_id}")
        commit = resolution.get("commit_sha")
        if require_commit and isinstance(commit, str):
            if self.commit_exists(commit, f"{context}.resolution.commit_sha") and checkpoint is not None:
                if not self.is_ancestor(commit, checkpoint["commit_sha"], context):
                    self.problems.violation(context, "resolution commit is not an ancestor of the resolution checkpoint")
        elif not require_commit and commit is not None:
            self.problems.violation(context, "non-applied terminal request must use null resolution.commit_sha")

    def validate_completion(self, current_id: str) -> None:
        completion = self.phase.get("completion", {})
        bounded = completion.get("bounded_phase", {})
        repository = completion.get("repository_wide", {})
        current = self.checkpoints.get(current_id)
        if bounded.get("status") == "complete":
            if bounded.get("evidence_checkpoint_id") != current_id:
                self.problems.violation("bounded completion", "evidence must name the current checkpoint")
            unsatisfied: list[str] = []
            for milestone_id, milestone in sorted(self.milestones.items()):
                if milestone.get("status") == "accepted":
                    continue
                if milestone.get("status") == "superseded":
                    cursor = milestone.get("superseded_by")
                    seen: set[str] = set()
                    while isinstance(cursor, str) and cursor in self.milestones and cursor not in seen:
                        seen.add(cursor)
                        replacement = self.milestones[cursor]
                        if replacement.get("status") == "accepted":
                            break
                        cursor = replacement.get("superseded_by")
                    else:
                        unsatisfied.append(milestone_id)
                    continue
                unsatisfied.append(milestone_id)
            if unsatisfied:
                self.problems.violation("bounded completion", "required milestones are not satisfied: " + ", ".join(unsatisfied))
            accepted_waves = {wave for milestone in self.milestones.values() if milestone.get("status") == "accepted" for wave in milestone.get("wave_ids", [])}
            if self.scope_snapshot is not None:
                missing = sorted(self.scope_snapshot.in_scope_waves - accepted_waves)
                if missing:
                    self.problems.violation("bounded completion", "in-scope waves not accepted: " + ", ".join(missing))
            open_branches = sorted(branch_id for branch_id, branch in self.branches.items() if branch.get("status") in {"planned", "active", "delivered"})
            if open_branches:
                self.problems.violation("bounded completion", "open branches remain: " + ", ".join(open_branches))
            open_requests = sorted(request_id for request_id, request in self.requests.items() if request.get("status") in {"draft", "active"})
            if open_requests:
                self.problems.violation("bounded completion", "open requests remain: " + ", ".join(open_requests))
            if current is not None:
                required_gate_ids = {gate for milestone in self.milestones.values() for gate in milestone.get("acceptance_gate_ids", [])}
                failed = sorted(gate_id for gate_id in required_gate_ids if current.get("_gate_map", {}).get(gate_id, {}).get("status") != "PASS")
                if failed:
                    self.problems.violation("bounded completion", "current checkpoint lacks passing milestone gate(s): " + ", ".join(failed))
        if repository.get("status") == "complete":
            if bounded.get("status") != "complete":
                self.problems.violation("repository completion", "bounded phase must be complete first")
            if repository.get("evidence_checkpoint_id") != current_id:
                self.problems.violation("repository completion", "evidence must name the current checkpoint")
            if current is None:
                return
            metrics = current.get("metrics", {})
            for key in LEGACY_KEYS:
                if metrics.get(key) != 0:
                    self.problems.violation("repository completion", f"{key} must be zero, found {metrics.get(key)!r}")
            gate_map = current.get("_gate_map", {})
            for gate_id in repository.get("required_gate_ids", []):
                if gate_map.get(gate_id, {}).get("status") != "PASS":
                    self.problems.violation("repository completion", f"required gate {gate_id} did not pass at the current checkpoint")

    def validate(self) -> Problems:
        self.load_phase()
        if self.phase:
            self.load_records()
            self.validate_cross_references()
        return self.problems

    def summary(self) -> str:
        return (
            f"phase contract passed: {len(self.checkpoints)} checkpoint(s), "
            f"{len(self.milestones)} milestone(s), {len(self.branches)} branch record(s), "
            f"{len(self.requests)} shared request(s), and {len(self.projections)} baseline projection(s)"
        )


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def write_json(path: Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")


def run_self_test() -> int:
    with tempfile.TemporaryDirectory(prefix="numstability-phase-selftest-") as temporary:
        root = Path(temporary)
        (root / "NumStability").mkdir()
        (root / "docs/architecture").mkdir(parents=True)
        (root / "NumStability.lean").write_text("/-! Test root. -/\nimport NumStability.Foo\n", encoding="utf-8", newline="\n")
        (root / "NumStability/Foo.lean").write_text("/-! Test leaf. -/\ntheorem foo : True := by trivial\n", encoding="utf-8", newline="\n")
        tiers = {
            "schema_version": 1,
            "tiers": sorted(TIERS),
            "reusable_entrypoints": [],
            "exact": {"NumStability": "aggregate"},
            "prefixes": [],
        }
        layout = {
            "schema_version": 1,
            "policy": "self-test",
            "direct_import_ceilings": {},
            "complete_aggregates": {},
            "legacy": {
                key: (["NumStability.Foo"] if key == "unclassified_modules" else [])
                for key in LEGACY_KEYS
            },
        }
        write_json(root / "docs/architecture/tiers.json", tiers)
        write_json(root / "docs/architecture/layout-exceptions.json", layout)
        subprocess.run(["git", "init", "-q"], cwd=root, check=True)
        subprocess.run(["git", "config", "core.autocrlf", "false"], cwd=root, check=True)
        subprocess.run(["git", "config", "user.email", "self-test@example.invalid"], cwd=root, check=True)
        subprocess.run(["git", "config", "user.name", "Phase Self Test"], cwd=root, check=True)
        subprocess.run(["git", "add", "."], cwd=root, check=True)
        subprocess.run(["git", "commit", "-qm", "self-test base"], cwd=root, check=True)
        commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
        tree_raw = subprocess.check_output(
            ["git", "ls-tree", "-r", "-z", commit, "--", "NumStability.lean", "NumStability"],
            cwd=root,
        )
        blobs: dict[str, str] = {}
        for entry in tree_raw.split(b"\0"):
            if not entry:
                continue
            metadata, path_raw = entry.split(b"\t", 1)
            blobs[path_raw.decode()] = metadata.decode().split()[2]

        phase_rel = LEGACY_DEFAULT_PHASE_DIR
        phase_dir = root / phase_rel
        for name in (
            "baselines",
            "branches",
            "checkpoints",
            "projections",
            "requests",
            "selectors",
        ):
            (phase_dir / name).mkdir(parents=True, exist_ok=True)
        scope_path = phase_dir / "scope.tsv"
        scope_rows = [
            ["NumStability", "NumStability.lean", blobs["NumStability.lean"], "aggregate", "-", "already_complete", "-", "-", "-", "-"],
            ["NumStability.Foo", "NumStability/Foo.lean", blobs["NumStability/Foo.lean"], "unclassified", "unclassified_modules", "in_scope", "lane-a", "W1", "migrate", "bounded self-test wave"],
        ]
        with scope_path.open("w", encoding="utf-8", newline="") as handle:
            writer = csv.writer(handle, delimiter="\t", lineterminator="\n")
            writer.writerow(SCOPE_HEADER)
            writer.writerows(scope_rows)
        inventory_path = phase_dir / "checkpoints/C0000-inventory.tsv"
        inventory_path.write_bytes(scope_path.read_bytes())
        unclassified_queue_path = phase_dir / "unclassified-queue.tsv"
        unclassified_queue_path.write_text(
            "module\tpath\twave_id\tlane_id\tinventory_source\t"
            "frozen_proposed_tier\tfrozen_proposed_family\treview_status\n"
            "NumStability.Foo\tNumStability/Foo.lean\tW1\tlane-a\t"
            "frozen-proposal\treusable\tNumStability.Foo\t"
            "semantic_review_required\n",
            encoding="utf-8",
            newline="\n",
        )
        semantic_review_path = phase_dir / "semantic-review.tsv"
        semantic_review_path.write_text(
            "module\tfrozen_suggestion\tcurrent_review_status\trequired_correction\n"
            "NumStability.Foo\treusable\tsemantic_review_required\t"
            "review the self-test source correspondence\n",
            encoding="utf-8",
            newline="\n",
        )
        baseline_path = phase_dir / "baselines/C0000-combined.json"
        write_json(
            baseline_path,
            {
                "schema_version": 1,
                "metadata": {
                    "commit": commit,
                    "library_source_clean": True,
                    "library_source_dirty_paths": [],
                },
                "declarations": {"format_version": DECLARATION_FORMAT_VERSION},
            },
        )
        baseline_summary_path = phase_dir / "baselines/C0000-combined.md"
        baseline_summary_path.write_text(
            "# Self-test baseline\n\n"
            f"- Commit: `{commit}`\n",
            encoding="utf-8",
            newline="\n",
        )
        selector_path = phase_dir / "selectors/W1.tsv"
        selector_path.write_text(
            "module\tpath\nNumStability.Foo\tNumStability/Foo.lean\n",
            encoding="utf-8",
            newline="\n",
        )
        projection_graph_path = phase_dir / "projections/P0001.tsv"
        projection_graph_path.write_text(
            "format\t2\n"
            "declaration\tNumStability.foo\tNumStability.Foo\ttheorem\tpublic\n",
            encoding="utf-8",
            newline="\n",
        )
        checker_path = phase_dir / "projection-checker.py"
        checker_path.write_text("print('self-test')\n", encoding="utf-8", newline="\n")
        patch_path = phase_dir / "requests/R0001.patch"
        patch_path.write_text(
            "diff --git a/NumStability.lean b/NumStability.lean\n"
            "--- a/NumStability.lean\n"
            "+++ b/NumStability.lean\n"
            "@@ -1,1 +1,1 @@\n"
            "-/-! Test root. -/\n"
            "+/-! Test root updated by integrator. -/\n",
            encoding="utf-8",
            newline="\n",
        )

        artifact = lambda path: {
            "path": path.relative_to(root).as_posix(),
            "sha256": sha256_file(path),
        }
        phase = {
            "schema_version": 1,
            "record_kind": "reorganization_phase",
            "phase_id": "repository-reorganization-2026-08",
            "title": "Self-test phase",
            "status": "active",
            "created_at": "2026-08-01T00:00:00Z",
            "origin_checkpoint_id": "C0000",
            "current_checkpoint_id": "C0000",
            "scope": artifact(scope_path),
            "unclassified_queue": artifact(unclassified_queue_path),
            "semantic_review": artifact(semantic_review_path),
            "base_policy": {
                "immutable_origin_sha": commit,
                "new_branch_must_use_current_checkpoint": True,
                "combined_baseline_after_each_accepted_checkpoint": True,
                "refresh_requires": sorted(REQUIRED_REFRESH_ITEMS),
            },
            "authority": {
                "principals": [
                    {"principal_id": "integrator", "display_name": "Integrator", "kind": "human"},
                    {"principal_id": "worker", "display_name": "Worker", "kind": "agent"},
                ],
                "integration_authority_id": "integrator",
                "release_manager_id": "integrator",
                "main_push_authority_ids": ["integrator"],
                "shared_path_authority_ids": ["integrator"],
                "branch_registry_authority_ids": ["integrator"],
                "build_lock_name": "self-test-lock",
                "lanes": [
                    {
                        "lane_id": "integration-lane",
                        "owner_id": "integrator",
                        "operator_ids": ["integrator"],
                    },
                    {
                        "lane_id": "lane-a",
                        "owner_id": "integrator",
                        "operator_ids": ["worker"],
                    },
                ],
            },
            "shared_paths": [{"match": "exact", "path": "NumStability.lean"}],
            "milestones": [
                {
                    "milestone_id": "M1",
                    "status": "planned",
                    "depends_on": [],
                    "wave_ids": ["W1"],
                    "acceptance_gate_ids": ["architecture"],
                    "accepted_checkpoint_id": None,
                    "unblocks": [],
                    "superseded_by": None,
                }
            ],
            "completion": {
                "bounded_phase": {
                    "status": "incomplete",
                    "required_condition_ids": sorted(REQUIRED_BOUNDED_CONDITIONS),
                    "evidence_checkpoint_id": None,
                },
                "repository_wide": {
                    "status": "incomplete",
                    "required_gate_ids": sorted(REQUIRED_REPOSITORY_GATES),
                    "evidence_checkpoint_id": None,
                },
            },
        }
        write_json(phase_dir / "phase.json", phase)
        checkpoint = {
            "schema_version": 1,
            "record_kind": "phase_checkpoint",
            "phase_id": phase["phase_id"],
            "checkpoint_id": "C0000",
            "parent_checkpoint_id": None,
            "commit_sha": commit,
            "accepted_at": "2026-08-01T00:00:00Z",
            "accepted_by": "integrator",
            "milestones_satisfied": [],
            "unblocks": [],
            "inventory": artifact(inventory_path),
            "combined_baseline": {
                "format_version": 2,
                "artifact": artifact(baseline_path),
                "summary_artifact": artifact(baseline_summary_path),
                "generation_command": "self-test baseline",
            },
            "metrics": {
                key: (
                    2
                    if key == "production_modules"
                    else 1 if key == "unclassified_modules" else 0
                )
                for key in METRIC_KEYS
            },
            "gates": [
                {
                    "gate_id": gate_id,
                    "command": f"self-test {gate_id}",
                    "status": "PASS",
                    "commit_sha": commit,
                    "executor_id": "worker",
                    "requires_large_build_lock": False,
                    "lock_name": None,
                    "evidence": None,
                }
                for gate_id in sorted(REQUIRED_CHECKPOINT_GATES)
            ],
        }
        write_json(phase_dir / "checkpoints/C0000.json", checkpoint)
        projection = {
            "schema_version": 1,
            "record_kind": "baseline_projection",
            "phase_id": phase["phase_id"],
            "projection_id": "P0001",
            "wave_id": "W1",
            "base_checkpoint_id": "C0000",
            "status": "active",
            "combined_baseline": artifact(baseline_path),
            "selector": {"kind": "module_path_tsv", "artifact": artifact(selector_path)},
            "projection_graph": artifact(projection_graph_path),
            "expected_counts": {
                "declarations": 1,
                "signature_edges": 0,
                "body_edges": 0,
                "union_edges": 0,
            },
            "checker": {"artifact": artifact(checker_path), "arguments": ["--self-test"]},
            "superseded_by": None,
        }
        write_json(phase_dir / "projections/P0001.json", projection)
        branch = {
            "schema_version": 1,
            "record_kind": "phase_branch",
            "phase_id": phase["phase_id"],
            "branch_id": "B0001",
            "lane_id": "lane-a",
            "wave_id": "W1",
            "branch_name": "codex/reorganization-self-test",
            "owner_id": "integrator",
            "operator_ids": ["worker"],
            "base_checkpoint_id": "C0000",
            "base_sha": commit,
            "owned_paths": [{"match": "exact", "path": "NumStability/Foo.lean"}],
            "destination_prefixes": [
                {"match": "prefix", "path": "NumStability/FooCanonical/"},
                {
                    "match": "prefix",
                    "path": "NumStabilityTest/Reorganization/W1/",
                },
                {
                    "match": "prefix",
                    "path": "docs/architecture/deliveries/W1/",
                },
            ],
            "forbidden_paths": [{"match": "exact", "path": "NumStability.lean"}],
            "baseline_projection_id": "P0001",
            "shared_request_ids": ["R0001"],
            "status": "planned",
            "refresh": {"reviewed_checkpoint_id": "C0000", "decision": "current", "evidence": []},
            "delivery": {"commit_sha": None, "report": None, "scope_evidence": None},
            "integration": {"method": None, "accepted_checkpoint_id": None, "accepted_sha": None},
            "retirement": {
                "remote_ref": "refs/heads/codex/reorganization-self-test",
                "rule": "delivery_ancestor_of_green_checkpoint",
                "status": "not_due",
                "retired_at": None,
                "retired_by": None,
                "ancestry_checkpoint_id": None,
            },
        }
        write_json(phase_dir / "branches/B0001.json", branch)
        request = {
            "schema_version": 1,
            "record_kind": "shared_file_request",
            "phase_id": phase["phase_id"],
            "request_id": "R0001",
            "lane_id": "lane-a",
            "wave_id": "W1",
            "requester_id": "worker",
            "created_at": "2026-08-01T00:00:00Z",
            "target_checkpoint_id": "C0000",
            "target_base_sha": commit,
            "paths": ["NumStability.lean"],
            "preimage_blobs": [{"path": "NumStability.lean", "blob_oid": blobs["NumStability.lean"]}],
            "rationale": "Wire the bounded self-test leaf.",
            "patch": artifact(patch_path),
            "depends_on": [],
            "blocks": ["W1"],
            "valid_through_checkpoint_id": "C0000",
            "status": "active",
            "supersedes": None,
            "superseded_by": None,
            "resolution": {
                "commit_sha": None,
                "checkpoint_id": None,
                "resolved_at": None,
                "resolved_by": None,
                "validation_evidence": [],
                "reason": None,
            },
        }
        write_json(phase_dir / "requests/R0001.json", request)
        for sidecar in (
            phase_dir / "branches/B0001-overlap-review.json",
            phase_dir / "checkpoints/C0000-acceptance-control-ci.json",
            phase_dir / "projections/P0001-review.json",
            phase_dir / "requests/R0001-render-review.json",
        ):
            write_json(sidecar, {"record_kind": "evidence_sidecar"})

        valid = PhaseValidator(root, phase_dir)
        valid_result = valid.validate()
        if not valid_result.ok:
            valid_result.render()
            print("self-test failure: valid synthetic contract was rejected", file=sys.stderr)
            return 1

        # Current lane membership governs live execution authority. Terminal
        # records retain the operator attribution that was valid during their
        # execution epoch even if the lane's current operator set has changed.
        branch["operator_ids"] = ["integrator"]
        write_json(phase_dir / "branches/B0001.json", branch)
        unauthorized_live_operator = PhaseValidator(root, phase_dir).validate()
        if not any(
            "operator integrator is not authorized for lane lane-a" in message
            for message in unauthorized_live_operator.contract_errors
        ):
            unauthorized_live_operator.render()
            print(
                "self-test failure: unauthorized live branch operator was accepted",
                file=sys.stderr,
            )
            return 1
        branch["status"] = "cancelled"
        projection["status"] = "retired"
        write_json(phase_dir / "branches/B0001.json", branch)
        write_json(phase_dir / "projections/P0001.json", projection)
        terminal_historical_operator = PhaseValidator(root, phase_dir).validate()
        if not terminal_historical_operator.ok:
            terminal_historical_operator.render()
            print(
                "self-test failure: terminal branch historical operator attribution was rejected",
                file=sys.stderr,
            )
            return 1
        branch["operator_ids"] = ["unknown-terminal-operator"]
        write_json(phase_dir / "branches/B0001.json", branch)
        unknown_terminal_operator = PhaseValidator(root, phase_dir).validate()
        if not any(
            "operator unknown-terminal-operator is an unknown principal" in message
            for message in unknown_terminal_operator.contract_errors
        ):
            unknown_terminal_operator.render()
            print(
                "self-test failure: terminal branch accepted an unknown operator principal",
                file=sys.stderr,
            )
            return 1
        branch["operator_ids"] = ["worker"]
        branch["status"] = "planned"
        projection["status"] = "active"
        write_json(phase_dir / "branches/B0001.json", branch)
        write_json(phase_dir / "projections/P0001.json", projection)

        # A live request must retain its current shared-path reservation, but
        # an applied request is historical evidence and must not prevent a
        # later checkpoint from assigning that path to a branch owner.
        phase["shared_paths"] = []
        write_json(phase_dir / "phase.json", phase)
        released_live = PhaseValidator(root, phase_dir).validate()
        if not any(
            "requested path is not integrator-owned shared state" in message
            for message in released_live.contract_errors
        ):
            released_live.render()
            print(
                "self-test failure: a live request without a shared-path reservation was accepted",
                file=sys.stderr,
            )
            return 1
        request["status"] = "applied"
        request["resolution"] = {
            "commit_sha": commit,
            "checkpoint_id": "C0000",
            "resolved_at": "2026-08-01T00:01:00Z",
            "resolved_by": "integrator",
            "validation_evidence": [artifact(patch_path)],
            "reason": "Self-test terminal shared-path release.",
        }
        write_json(phase_dir / "requests/R0001.json", request)
        released_terminal = PhaseValidator(root, phase_dir).validate()
        if not released_terminal.ok:
            released_terminal.render()
            print(
                "self-test failure: an applied request retained a permanent shared-path reservation",
                file=sys.stderr,
            )
            return 1
        phase["shared_paths"] = [
            {"match": "exact", "path": "NumStability.lean"}
        ]
        request["status"] = "active"
        request["resolution"] = {
            "commit_sha": None,
            "checkpoint_id": None,
            "resolved_at": None,
            "resolved_by": None,
            "validation_evidence": [],
            "reason": None,
        }
        write_json(phase_dir / "phase.json", phase)
        write_json(phase_dir / "requests/R0001.json", request)

        queue_text = unclassified_queue_path.read_text(encoding="utf-8")
        unclassified_queue_path.write_text(
            queue_text.replace("\tW1\tlane-a\t", "\tW9\tlane-a\t"),
            encoding="utf-8",
            newline="\n",
        )
        phase["unclassified_queue"] = artifact(unclassified_queue_path)
        write_json(phase_dir / "phase.json", phase)
        queue_drift = PhaseValidator(root, phase_dir).validate()
        if not any(
            "unclassified_queue.NumStability.Foo.wave_id" in message
            for message in queue_drift.contract_errors
        ):
            queue_drift.render()
            print("self-test failure: queue scope drift was not rejected", file=sys.stderr)
            return 1
        unclassified_queue_path.write_text(
            queue_text, encoding="utf-8", newline="\n"
        )
        phase["unclassified_queue"] = artifact(unclassified_queue_path)
        write_json(phase_dir / "phase.json", phase)

        semantic_text = semantic_review_path.read_text(encoding="utf-8")
        semantic_review_path.write_text(
            semantic_text.replace(
                "\tsemantic_review_required\t", "\tconfirmed_source\t"
            ),
            encoding="utf-8",
            newline="\n",
        )
        phase["semantic_review"] = artifact(semantic_review_path)
        write_json(phase_dir / "phase.json", phase)
        status_mismatch = PhaseValidator(root, phase_dir).validate()
        if not any(
            "semantic_review.NumStability.Foo.current_review_status" in message
            for message in status_mismatch.contract_errors
        ):
            status_mismatch.render()
            print(
                "self-test failure: semantic review status mismatch was not rejected",
                file=sys.stderr,
            )
            return 1
        semantic_review_path.write_text(
            semantic_text, encoding="utf-8", newline="\n"
        )
        phase["semantic_review"] = artifact(semantic_review_path)
        write_json(phase_dir / "phase.json", phase)

        branch["owned_paths"] = [{"match": "exact", "path": "NumStability.lean"}]
        write_json(phase_dir / "branches/B0001.json", branch)
        wrong_scope = PhaseValidator(root, phase_dir).validate()
        if not any(
            "owned_paths must be exact rules" in message
            for message in wrong_scope.contract_errors
        ):
            wrong_scope.render()
            print("self-test failure: wrong-wave ownership was not rejected", file=sys.stderr)
            return 1
        branch["owned_paths"] = [
            {"match": "exact", "path": "NumStability/Foo.lean"}
        ]
        write_json(phase_dir / "branches/B0001.json", branch)

        branch["destination_prefixes"] = [
            {"match": "prefix", "path": "NumStability/"}
        ]
        write_json(phase_dir / "branches/B0001.json", branch)
        overlapping_destination = PhaseValidator(root, phase_dir).validate()
        if not any(
            "overlaps existing owned path" in message
            for message in overlapping_destination.contract_errors
        ):
            overlapping_destination.render()
            print(
                "self-test failure: destination/owned overlap was not rejected",
                file=sys.stderr,
            )
            return 1
        branch["destination_prefixes"] = [
            {"match": "prefix", "path": "NumStability/FooCanonical/"},
            {
                "match": "prefix",
                "path": "NumStabilityTest/Reorganization/W1/",
            },
            {
                "match": "prefix",
                "path": "docs/architecture/deliveries/W1/",
            },
        ]
        write_json(phase_dir / "branches/B0001.json", branch)

        baseline_document = json.loads(baseline_path.read_text(encoding="utf-8"))
        baseline_document["metadata"]["commit"] = "0" * 40
        write_json(baseline_path, baseline_document)
        checkpoint["combined_baseline"]["artifact"] = artifact(baseline_path)
        write_json(phase_dir / "checkpoints/C0000.json", checkpoint)
        stale_baseline = PhaseValidator(root, phase_dir).validate()
        if not any(
            "metadata.commit must equal" in message
            for message in stale_baseline.contract_errors
        ):
            stale_baseline.render()
            print("self-test failure: stale baseline metadata was not rejected", file=sys.stderr)
            return 1
        baseline_document["metadata"]["commit"] = commit
        write_json(baseline_path, baseline_document)
        checkpoint["combined_baseline"]["artifact"] = artifact(baseline_path)
        write_json(phase_dir / "checkpoints/C0000.json", checkpoint)

        full_test_gate = next(
            gate for gate in checkpoint["gates"] if gate["gate_id"] == "full_tests"
        )
        full_test_gate["status"] = "NOT_RUN"
        write_json(phase_dir / "checkpoints/C0000.json", checkpoint)
        unpassed_checkpoint = PhaseValidator(root, phase_dir).validate()
        if not any(
            "mandatory checkpoint gate" in message
            for message in unpassed_checkpoint.contract_errors
        ):
            unpassed_checkpoint.render()
            print("self-test failure: unpassed checkpoint gate was not rejected", file=sys.stderr)
            return 1
        full_test_gate["status"] = "PASS"
        write_json(phase_dir / "checkpoints/C0000.json", checkpoint)

        projection["expected_counts"]["declarations"] = 2
        write_json(phase_dir / "projections/P0001.json", projection)
        wrong_projection_count = PhaseValidator(root, phase_dir).validate()
        if not any(
            "expected_counts.declarations" in message
            for message in wrong_projection_count.contract_errors
        ):
            wrong_projection_count.render()
            print("self-test failure: projection count drift was not rejected", file=sys.stderr)
            return 1
        projection["expected_counts"]["declarations"] = 1
        write_json(phase_dir / "projections/P0001.json", projection)

        phase["milestones"][0]["depends_on"] = ["M1"]
        write_json(phase_dir / "phase.json", phase)
        cyclic = PhaseValidator(root, phase_dir).validate()
        if not any("dependency cycle" in message for message in cyclic.contract_errors):
            cyclic.render()
            print("self-test failure: milestone cycle was not rejected", file=sys.stderr)
            return 1
        phase["milestones"][0]["depends_on"] = []
        write_json(phase_dir / "phase.json", phase)

        phase["milestones"][0]["unblocks"] = ["W1"]
        write_json(phase_dir / "phase.json", phase)
        premature_unblock = PhaseValidator(root, phase_dir).validate()
        if not any(
            "cannot safely unblock W1" in message
            for message in premature_unblock.contract_errors
        ):
            premature_unblock.render()
            print("self-test failure: premature unblock was not rejected", file=sys.stderr)
            return 1
        phase["milestones"][0]["unblocks"] = []
        write_json(phase_dir / "phase.json", phase)

        phase["completion"]["bounded_phase"]["status"] = "complete"
        phase["completion"]["bounded_phase"]["evidence_checkpoint_id"] = "C0000"
        write_json(phase_dir / "phase.json", phase)
        premature = PhaseValidator(root, phase_dir).validate()
        if not any("bounded completion" in message for message in premature.contract_errors):
            premature.render()
            print("self-test failure: premature bounded completion was not rejected", file=sys.stderr)
            return 1
        phase["completion"]["bounded_phase"]["status"] = "incomplete"
        phase["completion"]["bounded_phase"]["evidence_checkpoint_id"] = None
        write_json(phase_dir / "phase.json", phase)

        # Exercise integration amendments end to end.  One preimage comes
        # from target HEAD; the other exists only as a SHA-256-chained
        # predecessor postimage, so the fixture also protects clean-clone
        # validation from accidentally requiring a loose predecessor blob.
        amendment_patch_path = phase_dir / "requests/R0002.patch"
        amendment_postimages_path = phase_dir / "requests/R0002-postimages.tsv"
        amendment_review_path = phase_dir / "requests/R0002-review.md"
        amendment_approval_path = phase_dir / "requests/R0002-approval.md"
        predecessor_postimages_path = phase_dir / "requests/R0001-postimages.tsv"
        amendment_record_path = phase_dir / "requests/R0002.json"
        root_path = root / "NumStability.lean"
        foo_path = root / "NumStability/Foo.lean"
        base_root = subprocess.check_output(
            ["git", "show", f"{commit}:NumStability.lean"], cwd=root
        )
        base_foo = subprocess.check_output(
            ["git", "show", f"{commit}:NumStability/Foo.lean"], cwd=root
        )
        predecessor_root = (
            b"/-! Test root after predecessor. -/\nimport NumStability.Foo\n"
        )
        final_root = b"/-! Test root after amendment. -/\nimport NumStability.Foo\n"
        final_foo = (
            b"/-! Test leaf after amendment. -/\n"
            b"theorem foo : True := by trivial\n"
        )

        def blob_oid(payload: bytes) -> str:
            header = f"blob {len(payload)}\0".encode("ascii")
            return hashlib.sha1(header + payload).hexdigest()

        predecessor_root_oid = blob_oid(predecessor_root)
        # Deliberately do not write predecessor_root_oid into the object
        # database.  A portable validator must prove it from the pinned
        # predecessor SHA-256 chain instead of `git cat-file`.
        if subprocess.run(
            ["git", "cat-file", "-e", predecessor_root_oid],
            cwd=root,
            check=False,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        ).returncode == 0:
            print(
                "self-test failure: predecessor-only blob unexpectedly exists",
                file=sys.stderr,
            )
            return 1

        predecessor_postimages_path.write_text(
            "\t".join(INTEGRATION_AMENDMENT_MANIFEST_HEADER)
            + "\n"
            + "\t".join(
                (
                    "NumStability.lean",
                    blobs["NumStability.lean"],
                    hashlib.sha256(base_root).hexdigest().upper(),
                    hashlib.sha256(predecessor_root).hexdigest().upper(),
                )
            )
            + "\n",
            encoding="utf-8",
            newline="\n",
        )
        predecessor_postimages_bytes = predecessor_postimages_path.read_bytes()
        amendment_postimages_path.write_text(
            "\t".join(INTEGRATION_AMENDMENT_MANIFEST_HEADER)
            + "\n"
            + "\t".join(
                (
                    "NumStability.lean",
                    predecessor_root_oid,
                    hashlib.sha256(predecessor_root).hexdigest().upper(),
                    hashlib.sha256(final_root).hexdigest().upper(),
                )
            )
            + "\n"
            + "\t".join(
                (
                    "NumStability/Foo.lean",
                    blobs["NumStability/Foo.lean"],
                    hashlib.sha256(base_foo).hexdigest().upper(),
                    hashlib.sha256(final_foo).hexdigest().upper(),
                )
            )
            + "\n",
            encoding="utf-8",
            newline="\n",
        )
        amendment_postimages_bytes = amendment_postimages_path.read_bytes()
        amendment_patch_path.write_text(
            "diff --git a/NumStability.lean b/NumStability.lean\n"
            "--- a/NumStability.lean\n"
            "+++ b/NumStability.lean\n"
            "@@ -1 +1 @@\n"
            "-/-! Test root after predecessor. -/\n"
            "+/-! Test root after amendment. -/\n"
            "diff --git a/NumStability/Foo.lean b/NumStability/Foo.lean\n"
            "--- a/NumStability/Foo.lean\n"
            "+++ b/NumStability/Foo.lean\n"
            "@@ -1 +1 @@\n"
            "-/-! Test leaf. -/\n"
            "+/-! Test leaf after amendment. -/\n",
            encoding="utf-8",
            newline="\n",
        )
        amendment_review_path.write_text(
            "# Reviewed self-test amendment\n",
            encoding="utf-8",
            newline="\n",
        )
        amendment_approval_path.write_text(
            "# Approved self-test amendment\n",
            encoding="utf-8",
            newline="\n",
        )
        delivery_test_path = (
            root / "NumStabilityTest/Reorganization/W1/Smoke.lean"
        )
        delivery_report_path = root / "docs/architecture/deliveries/W1/DELIVERY.md"
        delivery_scope_path = (
            root / "docs/architecture/deliveries/W1/CHANGED_PATHS.md"
        )
        delivery_test_path.parent.mkdir(parents=True, exist_ok=True)
        delivery_report_path.parent.mkdir(parents=True, exist_ok=True)
        delivery_test_path.write_text(
            "import NumStability.Foo\n",
            encoding="utf-8",
            newline="\n",
        )
        delivery_report_path.write_text(
            "# Self-test delivery\n", encoding="utf-8", newline="\n"
        )
        delivery_scope_path.write_text(
            "# Self-test changed paths\n", encoding="utf-8", newline="\n"
        )
        subprocess.run(
            [
                "git",
                "add",
                "--",
                "NumStabilityTest/Reorganization/W1/Smoke.lean",
                "docs/architecture/deliveries/W1/DELIVERY.md",
                "docs/architecture/deliveries/W1/CHANGED_PATHS.md",
            ],
            cwd=root,
            check=True,
        )
        subprocess.run(
            ["git", "commit", "-qm", "self-test worker evidence"],
            cwd=root,
            check=True,
        )
        delivery_commit = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, text=True
        ).strip()
        cross_wave_test_path = (
            root / "NumStabilityTest/Reorganization/W2/Intrusion.lean"
        )
        cross_wave_test_path.parent.mkdir(parents=True, exist_ok=True)
        cross_wave_test_path.write_text(
            "import NumStability.Foo\n",
            encoding="utf-8",
            newline="\n",
        )
        subprocess.run(
            [
                "git",
                "add",
                "--",
                "NumStabilityTest/Reorganization/W2/Intrusion.lean",
            ],
            cwd=root,
            check=True,
        )
        subprocess.run(
            ["git", "commit", "-qm", "self-test cross-wave intrusion"],
            cwd=root,
            check=True,
        )
        cross_wave_delivery_commit = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, text=True
        ).strip()
        root_path.write_bytes(final_root)
        foo_path.write_bytes(final_foo)
        subprocess.run(
            ["git", "add", "--", "NumStability.lean", "NumStability/Foo.lean"],
            cwd=root,
            check=True,
        )
        amendment = {
            "schema_version": 1,
            "record_kind": INTEGRATION_AMENDMENT_KIND,
            "phase_id": phase["phase_id"],
            "request_id": "R0002",
            "lane_id": "integration-lane",
            "requester_id": "integrator",
            "created_at": "2026-08-01T00:02:00Z",
            "target_branch": "main",
            "target_head_sha": commit,
            "target_index_staged_paths": 2,
            "paths": ["NumStability.lean", "NumStability/Foo.lean"],
            "preimage_blobs": [
                {
                    "path": "NumStability.lean",
                    "blob_oid": predecessor_root_oid,
                },
                {
                    "path": "NumStability/Foo.lean",
                    "blob_oid": blobs["NumStability/Foo.lean"],
                },
            ],
            "rationale": "Exercise reviewed integration-amendment provenance.",
            "patch": artifact(amendment_patch_path),
            "postimages": artifact(amendment_postimages_path),
            "predecessor_postimages": [artifact(predecessor_postimages_path)],
            "review": artifact(amendment_review_path),
            "approval": artifact(amendment_approval_path),
            "depends_on": ["R0001"],
            "blocks": ["W1"],
            "status": "active",
            "supersedes": None,
            "superseded_by": None,
            "resolution": {
                "commit_sha": None,
                "checkpoint_id": None,
                "resolved_at": None,
                "resolved_by": None,
                "validation_evidence": [],
                "reason": None,
            },
        }

        amendment_evidence_paths = (
            amendment_approval_path,
            amendment_postimages_path,
            amendment_review_path,
            amendment_record_path,
            amendment_patch_path,
        )

        def write_amendment_and_branch() -> None:
            write_json(amendment_record_path, amendment)
            branch["refresh"]["evidence"] = [
                artifact(path)
                for path in sorted(
                    amendment_evidence_paths,
                    key=lambda candidate: candidate.relative_to(root).as_posix(),
                )
            ]
            write_json(phase_dir / "branches/B0001.json", branch)

        write_amendment_and_branch()
        active_amendment = PhaseValidator(root, phase_dir).validate()
        if not active_amendment.ok:
            active_amendment.render()
            print(
                "self-test failure: valid active integration amendment was rejected",
                file=sys.stderr,
            )
            return 1

        foo_path.write_text(
            "/-! Divergent live index. -/\ntheorem foo : True := by trivial\n",
            encoding="utf-8",
            newline="\n",
        )
        subprocess.run(
            ["git", "add", "--", "NumStability/Foo.lean"], cwd=root, check=True
        )
        wrong_active_postimage = PhaseValidator(root, phase_dir).validate()
        if not any(
            "current index hashes to" in message
            for message in wrong_active_postimage.contract_errors
        ):
            wrong_active_postimage.render()
            print(
                "self-test failure: active amendment ignored current-index drift",
                file=sys.stderr,
            )
            return 1
        foo_path.write_bytes(final_foo)
        subprocess.run(
            ["git", "add", "--", "NumStability/Foo.lean"], cwd=root, check=True
        )

        predecessor_postimages_path.write_text(
            predecessor_postimages_bytes.decode("utf-8").replace(
                hashlib.sha256(predecessor_root).hexdigest().upper(), "0" * 64
            ),
            encoding="utf-8",
            newline="\n",
        )
        amendment["predecessor_postimages"] = [
            artifact(predecessor_postimages_path)
        ]
        write_amendment_and_branch()
        broken_predecessor = PhaseValidator(root, phase_dir).validate()
        if not any(
            "predecessor postimage must equal amendment preimage" in message
            for message in broken_predecessor.contract_errors
        ):
            broken_predecessor.render()
            print(
                "self-test failure: broken amendment predecessor chain was accepted",
                file=sys.stderr,
            )
            return 1
        predecessor_postimages_path.write_bytes(predecessor_postimages_bytes)
        amendment["predecessor_postimages"] = [
            artifact(predecessor_postimages_path)
        ]
        write_amendment_and_branch()

        amendment["depends_on"] = None
        amendment["blocks"] = None
        write_amendment_and_branch()
        malformed_lists = PhaseValidator(root, phase_dir).validate()
        if not all(
            any(f"R0002.json.{key}" in message for message in malformed_lists.format_errors)
            for key in ("depends_on", "blocks")
        ):
            malformed_lists.render()
            print(
                "self-test failure: malformed amendment lists were not diagnosed",
                file=sys.stderr,
            )
            return 1
        amendment["depends_on"] = ["R0001"]
        amendment["blocks"] = ["W1"]
        write_amendment_and_branch()

        amendment_postimages_path.write_text(
            "\t".join(INTEGRATION_AMENDMENT_MANIFEST_HEADER)
            + "\nNumStability.lean\t"
            + predecessor_root_oid
            + "\n",
            encoding="utf-8",
            newline="\n",
        )
        amendment["postimages"] = artifact(amendment_postimages_path)
        write_amendment_and_branch()
        malformed_postimages = PhaseValidator(root, phase_dir).validate()
        if not any(
            "malformed row or wrong column count" in message
            for message in malformed_postimages.format_errors
        ):
            malformed_postimages.render()
            print(
                "self-test failure: malformed amendment postimages were not diagnosed",
                file=sys.stderr,
            )
            return 1
        amendment_postimages_path.write_bytes(amendment_postimages_bytes)
        amendment["postimages"] = artifact(amendment_postimages_path)
        write_amendment_and_branch()

        predecessor_postimages_path.write_text(
            "\t".join(INTEGRATION_AMENDMENT_MANIFEST_HEADER)
            + "\nNumStability.lean\n",
            encoding="utf-8",
            newline="\n",
        )
        amendment["predecessor_postimages"] = [
            artifact(predecessor_postimages_path)
        ]
        write_amendment_and_branch()
        malformed_predecessor = PhaseValidator(root, phase_dir).validate()
        if not any(
            "malformed row or wrong column count" in message
            for message in malformed_predecessor.format_errors
        ):
            malformed_predecessor.render()
            print(
                "self-test failure: malformed predecessor rows were not diagnosed",
                file=sys.stderr,
            )
            return 1
        predecessor_postimages_path.write_bytes(predecessor_postimages_bytes)
        amendment["predecessor_postimages"] = [
            artifact(predecessor_postimages_path)
        ]
        write_amendment_and_branch()

        # Commit the reviewed postimages, then advance the synthetic phase so
        # the amendment can be validated as applied.  A deliberately divergent
        # current index below must not affect this historical check.
        subprocess.run(
            ["git", "commit", "-qm", "self-test amendment postimages"],
            cwd=root,
            check=True,
        )
        applied_commit = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, text=True
        ).strip()
        applied_blobs = {
            path: subprocess.check_output(
                ["git", "rev-parse", f"{applied_commit}:{path}"],
                cwd=root,
                text=True,
            ).strip()
            for path in ("NumStability.lean", "NumStability/Foo.lean")
        }
        inventory_c1_path = phase_dir / "checkpoints/C0001-inventory.tsv"
        with inventory_c1_path.open("w", encoding="utf-8", newline="") as handle:
            writer = csv.writer(handle, delimiter="\t", lineterminator="\n")
            writer.writerow(SCOPE_HEADER)
            writer.writerows(
                [
                    [
                        "NumStability",
                        "NumStability.lean",
                        applied_blobs["NumStability.lean"],
                        "aggregate",
                        "-",
                        "already_complete",
                        "-",
                        "-",
                        "-",
                        "-",
                    ],
                    [
                        "NumStability.Foo",
                        "NumStability/Foo.lean",
                        applied_blobs["NumStability/Foo.lean"],
                        "unclassified",
                        "unclassified_modules",
                        "in_scope",
                        "lane-a",
                        "W1",
                        "migrate",
                        "bounded self-test wave",
                    ],
                ]
            )
        baseline_c1_path = phase_dir / "baselines/C0001-combined.json"
        write_json(
            baseline_c1_path,
            {
                "schema_version": 1,
                "metadata": {
                    "commit": applied_commit,
                    "library_source_clean": True,
                    "library_source_dirty_paths": [],
                },
                "declarations": {"format_version": DECLARATION_FORMAT_VERSION},
            },
        )
        baseline_c1_summary_path = phase_dir / "baselines/C0001-combined.md"
        baseline_c1_summary_path.write_text(
            f"# Self-test successor baseline\n\n- Commit: `{applied_commit}`\n",
            encoding="utf-8",
            newline="\n",
        )
        checkpoint_c1 = json.loads(json.dumps(checkpoint))
        checkpoint_c1.update(
            {
                "checkpoint_id": "C0001",
                "parent_checkpoint_id": "C0000",
                "commit_sha": applied_commit,
                "accepted_at": "2026-08-01T00:03:00Z",
                "milestones_satisfied": ["M1"],
                "inventory": artifact(inventory_c1_path),
                "combined_baseline": {
                    "format_version": 2,
                    "artifact": artifact(baseline_c1_path),
                    "summary_artifact": artifact(baseline_c1_summary_path),
                    "generation_command": "self-test successor baseline",
                },
            }
        )
        for gate in checkpoint_c1["gates"]:
            gate["commit_sha"] = applied_commit
        write_json(phase_dir / "checkpoints/C0001.json", checkpoint_c1)
        phase["current_checkpoint_id"] = "C0001"
        phase["milestones"][0]["status"] = "accepted"
        phase["milestones"][0]["accepted_checkpoint_id"] = "C0001"
        write_json(phase_dir / "phase.json", phase)
        projection["status"] = "retired"
        write_json(phase_dir / "projections/P0001.json", projection)
        request["status"] = "applied"
        request["resolution"] = {
            "commit_sha": applied_commit,
            "checkpoint_id": "C0001",
            "resolved_at": "2026-08-01T00:03:00Z",
            "resolved_by": "integrator",
            "validation_evidence": [artifact(patch_path)],
            "reason": "Applied in the synthetic successor checkpoint.",
        }
        write_json(phase_dir / "requests/R0001.json", request)
        branch["status"] = "accepted"
        branch["delivery"] = {
            "commit_sha": delivery_commit,
            "report": artifact(delivery_report_path),
            "scope_evidence": artifact(delivery_scope_path),
        }
        branch["integration"] = {
            "method": "merge",
            "accepted_checkpoint_id": "C0001",
            "accepted_sha": applied_commit,
        }
        amendment["status"] = "applied"
        amendment["resolution"] = {
            "commit_sha": applied_commit,
            "checkpoint_id": "C0001",
            "resolved_at": "2026-08-01T00:03:00Z",
            "resolved_by": "integrator",
            "validation_evidence": [artifact(amendment_approval_path)],
            "reason": "Applied in the synthetic successor checkpoint.",
        }
        write_amendment_and_branch()
        foo_path.write_text(
            "/-! Later live-index edit. -/\ntheorem foo : True := by trivial\n",
            encoding="utf-8",
            newline="\n",
        )
        subprocess.run(
            ["git", "add", "--", "NumStability/Foo.lean"], cwd=root, check=True
        )
        applied_amendment = PhaseValidator(root, phase_dir).validate()
        if not applied_amendment.ok:
            applied_amendment.render()
            print(
                "self-test failure: applied amendment remained coupled to live index",
                file=sys.stderr,
            )
            return 1

        branch["delivery"]["commit_sha"] = cross_wave_delivery_commit
        write_amendment_and_branch()
        cross_wave_delivery = PhaseValidator(root, phase_dir).validate()
        if not any(
            "delivery changed unowned path "
            "NumStabilityTest/Reorganization/W2/Intrusion.lean" in message
            for message in cross_wave_delivery.contract_errors
        ):
            cross_wave_delivery.render()
            print(
                "self-test failure: cross-wave delivery evidence was accepted",
                file=sys.stderr,
            )
            return 1
        branch["delivery"]["commit_sha"] = delivery_commit
        write_amendment_and_branch()

        amendment["resolution"]["commit_sha"] = commit
        write_amendment_and_branch()
        wrong_applied_postimage = PhaseValidator(root, phase_dir).validate()
        if not any(
            f"resolution commit {commit} hashes to" in message
            for message in wrong_applied_postimage.contract_errors
        ):
            wrong_applied_postimage.render()
            print(
                "self-test failure: applied amendment ignored resolution-commit drift",
                file=sys.stderr,
            )
            return 1
        amendment["resolution"]["commit_sha"] = applied_commit
        write_amendment_and_branch()

        patch_path.write_text("tampered\n", encoding="utf-8", newline="\n")
        tampered = PhaseValidator(root, phase_dir).validate()
        if not any("SHA-256 mismatch" in message for message in tampered.contract_errors):
            tampered.render()
            print("self-test failure: artifact tampering was not rejected", file=sys.stderr)
            return 1

        fleet_root = Path(temporary) / "fleet"
        fleet_phases = fleet_root / PHASES_ROOT
        pred_dir = fleet_phases / "2026-01-alpha"
        succ_dir = fleet_phases / "2026-02-beta"
        review_relative = "docs/architecture/reviews/fleet-decision.md"
        review_path = fleet_root / Path(*PurePosixPath(review_relative).parts)
        review_path.parent.mkdir(parents=True, exist_ok=True)
        review_path.write_text("fleet fixture decision review\n", encoding="utf-8", newline="\n")
        write_json(pred_dir / "phase.json", {"phase_id": "alpha-phase", "status": "active"})
        write_json(succ_dir / "phase.json", {"phase_id": "beta-phase", "status": "active"})

        def fleet_record(**overrides: object) -> dict[str, Any]:
            record: dict[str, Any] = {
                "decided_at": "2026-08-30T20:00:00Z",
                "decision_review": review_relative,
                "effective_status": "superseded",
                "phase_id": "alpha-phase",
                "preserved_phase_sha256": sha256_file(pred_dir / "phase.json"),
                "record_kind": "phase_supersession",
                "reviewer": "primary-human",
                "schema_version": 1,
                "successor_phase_id": "beta-phase",
                "successor_path": (succ_dir.relative_to(fleet_root)).as_posix(),
            }
            record.update(overrides)
            return record

        fleet_dirs = [pred_dir, succ_dir]

        def fleet_case(expected: str | None, label: str) -> bool:
            result = validate_all_phases(fleet_root, fleet_dirs, succ_dir.resolve())
            if expected is None:
                if result.ok:
                    return True
                result.render()
                print(f"self-test failure: {label}", file=sys.stderr)
                return False
            if any(expected in message for message in result.contract_errors):
                return True
            result.render()
            print(f"self-test failure: {label}", file=sys.stderr)
            return False

        write_json(pred_dir / "supersession.json", fleet_record())
        if not fleet_case(None, "valid supersession fleet rejected"):
            return 1
        (pred_dir / "supersession.json").unlink()
        if not fleet_case(
            "exactly one retained phase must be effectively active",
            "two effectively active phases accepted",
        ):
            return 1
        write_json(pred_dir / "supersession.json", fleet_record())
        pointer_result = validate_all_phases(fleet_root, fleet_dirs, pred_dir.resolve())
        if not any(
            "must select the effectively active phase" in message
            for message in pointer_result.contract_errors
        ):
            pointer_result.render()
            print("self-test failure: pointer to terminal phase accepted", file=sys.stderr)
            return 1
        write_json(
            pred_dir / "supersession.json",
            fleet_record(successor_phase_id="gamma-phase", successor_path="docs/architecture/phases/2026-03-gamma"),
        )
        if not fleet_case(
            "existing distinct successor",
            "missing supersession successor accepted",
        ):
            return 1
        write_json(pred_dir / "supersession.json", fleet_record())
        write_json(
            succ_dir / "supersession.json",
            fleet_record(
                phase_id="beta-phase",
                preserved_phase_sha256=sha256_file(succ_dir / "phase.json"),
                successor_phase_id="alpha-phase",
                successor_path=(pred_dir.relative_to(fleet_root)).as_posix(),
            ),
        )
        if not fleet_case("supersession cycle includes", "successor cycle accepted"):
            return 1
        (succ_dir / "supersession.json").unlink()
        write_json(
            pred_dir / "supersession.json",
            fleet_record(preserved_phase_sha256="0" * 64),
        )
        if not fleet_case(
            "preserved_phase_sha256 must match the live phase.json bytes",
            "preserved-hash mismatch accepted",
        ):
            return 1
        write_json(pred_dir / "supersession.json", fleet_record())
        if not fleet_case(None, "restored supersession fleet rejected"):
            return 1

    print(
        "phase contract self-test passed: valid fixture accepted; queue drift, semantic "
        "status mismatch, wrong ownership, destination overlap, stale baseline metadata, "
        "unpassed gates, projection count drift, cycle, premature unblock, premature "
        "completion, unauthorized live operator, live shared-path release, and hash "
        "tampering and unknown terminal operators rejected; known terminal historical "
        "operator attribution and terminal shared-path release accepted; integration "
        "amendment active-index, applied-commit, predecessor-chain, approval, and "
        "malformed-input lifecycle cases verified; supersession fleet single-active, "
        "pointer-agreement, terminal-nonpointer, missing-successor, successor-cycle, "
        "and preserved-hash cases verified"
    )
    return 0


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--phase-dir",
        type=Path,
        default=None,
        help=(
            "phase contract directory, absolute or repository-relative "
            f"(default: path named by {ACTIVE_PHASE_POINTER.as_posix()})"
        ),
    )
    parser.add_argument(
        "--all-phases",
        action="store_true",
        help="validate every retained phase directory and the active-phase pointer",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="run an isolated positive/negative validator self-test without requiring phase artifacts",
    )
    return parser.parse_args(argv)


def active_phase_dir() -> tuple[Path | None, list[str]]:
    """Resolve and validate the repository's explicit active-phase pointer."""

    pointer_path = ROOT / ACTIVE_PHASE_POINTER
    errors: list[str] = []
    if not pointer_path.is_file():
        if (ROOT / LEGACY_DEFAULT_PHASE_DIR).is_dir():
            errors.append(
                f"missing active-phase pointer: {ACTIVE_PHASE_POINTER.as_posix()}"
            )
        return None, errors
    try:
        pointer = json.loads(
            pointer_path.read_text(encoding="utf-8"),
            object_pairs_hook=duplicate_safe_object,
        )
    except (OSError, UnicodeError, json.JSONDecodeError, DuplicateKeyError) as error:
        return None, [f"cannot read active-phase pointer: {error}"]
    required = {"schema_version", "record_kind", "phase_id", "path"}
    if not isinstance(pointer, dict):
        return None, ["active-phase pointer must be a JSON object"]
    missing = sorted(required - set(pointer))
    unexpected = sorted(set(pointer) - required)
    if missing:
        errors.append("active-phase pointer missing key(s): " + ", ".join(missing))
    if unexpected:
        errors.append(
            "active-phase pointer has unexpected key(s): " + ", ".join(unexpected)
        )
    if pointer.get("schema_version") != 1:
        errors.append("active-phase pointer schema_version must be 1")
    if pointer.get("record_kind") != "active_reorganization_phase":
        errors.append(
            "active-phase pointer record_kind must be 'active_reorganization_phase'"
        )
    phase_id = pointer.get("phase_id")
    if not isinstance(phase_id, str) or not ID_RE.fullmatch(phase_id):
        errors.append("active-phase pointer phase_id must be a stable slug")
    relative = pointer.get("path")
    if not isinstance(relative, str) or not is_repo_path(relative):
        errors.append("active-phase pointer path must be a repository-relative directory")
        return None, errors
    phase_dir = (ROOT / relative).resolve()
    phases_root = (ROOT / PHASES_ROOT).resolve()
    try:
        phase_dir.relative_to(phases_root)
    except ValueError:
        errors.append("active-phase pointer escapes docs/architecture/phases")
        return None, errors
    phase_path = phase_dir / "phase.json"
    if not phase_path.is_file():
        errors.append(f"active-phase pointer target lacks phase.json: {relative}")
        return phase_dir, errors
    try:
        phase = json.loads(
            phase_path.read_text(encoding="utf-8"),
            object_pairs_hook=duplicate_safe_object,
        )
    except (OSError, UnicodeError, json.JSONDecodeError, DuplicateKeyError) as error:
        errors.append(f"cannot read active phase.json: {error}")
    else:
        if not isinstance(phase, dict) or phase.get("phase_id") != phase_id:
            errors.append("active-phase pointer phase_id differs from target phase.json")
    return phase_dir, errors


SUPERSESSION_REQUIRED_KEYS = {
    "decided_at",
    "decision_review",
    "effective_status",
    "phase_id",
    "preserved_phase_sha256",
    "record_kind",
    "reviewer",
    "schema_version",
    "successor_phase_id",
    "successor_path",
}


def load_phase_identity(
    phase_dir: Path, context: str, problems: Problems
) -> tuple[str | None, str | None]:
    """Read (phase_id, stored status) from one retained phase.json."""

    try:
        phase = json.loads(
            (phase_dir / "phase.json").read_text(encoding="utf-8"),
            object_pairs_hook=duplicate_safe_object,
        )
    except (OSError, UnicodeError, json.JSONDecodeError, DuplicateKeyError) as error:
        problems.malformed(context, f"cannot read phase.json: {error}")
        return None, None
    phase_id = phase.get("phase_id") if isinstance(phase, dict) else None
    status = phase.get("status") if isinstance(phase, dict) else None
    if not isinstance(phase_id, str) or not ID_RE.fullmatch(phase_id):
        problems.malformed(context, "phase.json phase_id must be a stable slug")
        phase_id = None
    if status not in PHASE_STATUSES:
        problems.malformed(context, "phase.json status is not a known phase status")
        status = None
    return phase_id, status


def validate_all_phases(
    root: Path, phase_dirs: Sequence[Path], active_dir: Path | None
) -> Problems:
    """Enforce the retained-phase fleet invariants.

    A phase's stored status is overridden only by a valid terminal
    supersession record (supersession.json beside its phase.json): exactly
    one phase is effectively active, the active-phase pointer selects it,
    every other retained phase is effectively terminal, each supersession
    names an existing successor, successor chains are acyclic and reach the
    active phase, and the preserved-phase hash matches the live phase.json.
    """

    problems = Problems()
    effective: dict[str, str] = {}
    successors: dict[str, str] = {}
    dirs_by_id: dict[str, Path] = {}
    for phase_dir in phase_dirs:
        context = phase_dir.relative_to(root).as_posix()
        phase_id, status = load_phase_identity(phase_dir, context, problems)
        if phase_id is None or status is None:
            continue
        if phase_id in dirs_by_id:
            problems.violation(context, f"duplicate retained phase_id {phase_id}")
            continue
        dirs_by_id[phase_id] = phase_dir
        record_path = phase_dir / "supersession.json"
        if not record_path.is_file():
            effective[phase_id] = status
            continue
        record_context = f"{context}/supersession.json"
        try:
            record = json.loads(
                record_path.read_text(encoding="utf-8"),
                object_pairs_hook=duplicate_safe_object,
            )
        except (OSError, UnicodeError, json.JSONDecodeError, DuplicateKeyError) as error:
            problems.malformed(record_context, f"cannot read supersession record: {error}")
            effective[phase_id] = status
            continue
        if not isinstance(record, dict):
            problems.malformed(record_context, "supersession record must be a JSON object")
            effective[phase_id] = status
            continue
        missing = sorted(SUPERSESSION_REQUIRED_KEYS - set(record))
        unexpected = sorted(set(record) - SUPERSESSION_REQUIRED_KEYS)
        if missing:
            problems.malformed(record_context, "missing key(s): " + ", ".join(missing))
        if unexpected:
            problems.malformed(record_context, "unexpected key(s): " + ", ".join(unexpected))
        valid = not missing and not unexpected
        if valid and record.get("schema_version") != SCHEMA_VERSION:
            problems.malformed(record_context, "schema_version must be 1")
            valid = False
        if valid and record.get("record_kind") != "phase_supersession":
            problems.malformed(record_context, "record_kind must be 'phase_supersession'")
            valid = False
        if valid and record.get("effective_status") != "superseded":
            problems.violation(
                record_context,
                "a stored status is overridden only by a terminal supersession "
                "record with effective_status 'superseded'",
            )
            valid = False
        if valid and record.get("phase_id") != phase_id:
            problems.violation(record_context, "supersession phase_id differs from phase.json")
            valid = False
        if valid and not (
            isinstance(record.get("decided_at"), str) and is_rfc3339(record["decided_at"])
        ):
            problems.malformed(record_context, "decided_at must be an RFC 3339 instant")
            valid = False
        if valid and not (
            isinstance(record.get("reviewer"), str) and record["reviewer"]
        ):
            problems.malformed(record_context, "reviewer must be a nonempty string")
            valid = False
        if valid:
            review = record.get("decision_review")
            if not (
                isinstance(review, str)
                and is_repo_path(review)
                and (root / Path(*PurePosixPath(review).parts)).is_file()
            ):
                problems.violation(
                    record_context, "decision_review must name an existing repository file"
                )
                valid = False
        if valid:
            pinned = record.get("preserved_phase_sha256")
            if not (
                isinstance(pinned, str)
                and SHA256_RE.fullmatch(pinned)
                and pinned.upper() == sha256_file(phase_dir / "phase.json")
            ):
                problems.violation(
                    record_context,
                    "preserved_phase_sha256 must match the live phase.json bytes",
                )
                valid = False
        if valid:
            successor_id = record.get("successor_phase_id")
            successor_path = record.get("successor_path")
            successor_ok = (
                isinstance(successor_id, str)
                and ID_RE.fullmatch(successor_id)
                and successor_id != phase_id
                and isinstance(successor_path, str)
                and is_repo_path(successor_path)
                and (root / Path(*PurePosixPath(successor_path).parts) / "phase.json").is_file()
            )
            if not successor_ok:
                problems.violation(
                    record_context,
                    "supersession must name an existing distinct successor phase",
                )
                valid = False
            else:
                successors[phase_id] = successor_id
        effective[phase_id] = "superseded" if valid else status
    active_ids = sorted(
        phase_id for phase_id, status in effective.items() if status == "active"
    )
    fleet_context = PHASES_ROOT.as_posix()
    if len(active_ids) != 1:
        problems.violation(
            fleet_context,
            "exactly one retained phase must be effectively active, found "
            + (", ".join(active_ids) if active_ids else "none"),
        )
    active_id = active_ids[0] if len(active_ids) == 1 else None
    if active_id is not None and active_dir is not None:
        if dirs_by_id.get(active_id, Path()).resolve() != active_dir:
            problems.violation(
                fleet_context,
                "the active-phase pointer must select the effectively active phase",
            )
    for phase_id, status in sorted(effective.items()):
        if phase_id == active_id:
            continue
        if status not in TERMINAL_PHASE_STATUSES:
            problems.violation(
                fleet_context,
                f"retained nonpointer phase {phase_id} must be effectively "
                f"terminal, found status {status}",
            )
    for phase_id in sorted(successors):
        successor_id = successors[phase_id]
        if successor_id not in dirs_by_id:
            problems.violation(
                fleet_context,
                f"supersession successor {successor_id} is not a retained phase",
            )
            continue
        visited = {phase_id}
        cursor = successor_id
        while cursor in successors:
            if cursor in visited:
                problems.violation(
                    fleet_context, f"supersession cycle includes {cursor}"
                )
                break
            visited.add(cursor)
            cursor = successors[cursor]
        else:
            if active_id is not None and cursor != active_id:
                problems.violation(
                    fleet_context,
                    f"supersession chain from {phase_id} ends at {cursor}, "
                    "not the effectively active phase",
                )
    return problems


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    if args.self_test:
        return run_self_test()
    if args.phase_dir is not None and args.all_phases:
        print("error: --phase-dir and --all-phases are mutually exclusive", file=sys.stderr)
        return 2

    active_dir, pointer_errors = active_phase_dir()
    if pointer_errors and args.phase_dir is None:
        for error in pointer_errors:
            print(f"phase contract malformed: {error}", file=sys.stderr)
        return 2

    if args.all_phases:
        phase_root = ROOT / PHASES_ROOT
        phase_dirs = sorted(
            path for path in phase_root.iterdir()
            if path.is_dir() and (path / "phase.json").is_file()
        )
        if not phase_dirs:
            print("phase contract malformed: no retained phase directories found", file=sys.stderr)
            return 2
        exit_code = 0
        for phase_dir in phase_dirs:
            validator = PhaseValidator(ROOT, phase_dir)
            problems = validator.validate()
            if problems.ok:
                marker = " [active]" if active_dir == phase_dir.resolve() else ""
                print(validator.summary() + marker)
                continue
            print(f"phase validation failed: {phase_dir.relative_to(ROOT).as_posix()}", file=sys.stderr)
            problems.render()
            exit_code = max(exit_code, 2 if problems.format_errors else 1)
        fleet = validate_all_phases(ROOT, phase_dirs, active_dir)
        if not fleet.ok:
            print("phase fleet validation failed", file=sys.stderr)
            fleet.render()
            exit_code = max(exit_code, 2 if fleet.format_errors else 1)
        return exit_code

    phase_dir = args.phase_dir
    if phase_dir is None:
        if active_dir is None:
            print("phase contract malformed: active phase could not be resolved", file=sys.stderr)
            return 2
        phase_dir = active_dir
    elif not phase_dir.is_absolute():
        phase_dir = ROOT / phase_dir
    validator = PhaseValidator(ROOT, phase_dir)
    problems = validator.validate()
    if problems.ok:
        print(validator.summary())
        return 0
    problems.render()
    return 2 if problems.format_errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
