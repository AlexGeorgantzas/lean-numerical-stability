#!/usr/bin/env python3
"""Materialize the reviewed R07 worker-owned production and test postimages.

This script is deliberately R07-specific and fail-closed.  It reads the
hash-pinned B0010 controls from the exact activation-control checkout, reads
all source bytes from immutable C0005 code, copies whole Lean commands without
editing them, and writes only the paths authorized by B0010's scope rules.

The 32 declaration-free historical owners remain byte-identical.  The 13
declaration-bearing owners become import-only wrappers, 194 commands move to
30 semantic leaves, and the exact 102-row test plan is rendered under the R07
test prefix.  Shared R0011 paths are never written here.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import re
import subprocess
import tempfile
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path


BASE_CODE_SHA = "ad92bbfae62d538f3e52829a269a846688a8e213"
CONTROL_HEAD_SHA = "35cb1a7c5f136f291398dddd99d8012dcf38f967"
CONTROL_CONTRACT_SHA256 = (
    "387FCF34A62D1C07E1EBB41E96D0BC57E7BF17B099396F7A87C797B52BA13D7C"
)
ACTIVATION_SHA256 = (
    "80D91BFD25A8A255883FBA36AFD03B1E4119E1893DA741F8D325A49147D290A4"
)
ACTIVE_BRANCH_SHA256 = (
    "007CD9A2CF7A886B0789CCD0BE3CCF42A35EFC2D310B8EA3C1A20177C21231D2"
)
WORKER_BRANCH = "codex/reorg-completion-2026-08-r07-matrix-functions-powers-ch18"
PHASE = Path(
    "docs/architecture/phases/2026-08-repository-reorganization-completion"
)
BRANCHES = PHASE / "branches"
REVIEWS = PHASE / "reviews"

EXPECTED_OWNERS = 45
EXPECTED_BEARING_OWNERS = 13
EXPECTED_DECLARATIONS = 194
EXPECTED_DESTINATIONS = 30
EXPECTED_PRIVATE = 44
EXPECTED_CLOSURE = 77
EXPECTED_TESTS = 102

REQUIRED_CONTROL_PATHS = (
    BRANCHES / "B0010-declaration-routes.tsv",
    BRANCHES / "B0010-destinations.tsv",
    BRANCHES / "B0010-module-routes.tsv",
    BRANCHES / "B0010-post-move-import-manifest.tsv",
    BRANCHES / "B0010-private-closure.tsv",
    BRANCHES / "B0010-private-normalization.tsv",
    BRANCHES / "B0010-scope-rules.tsv",
    BRANCHES / "B0010-source-commands.tsv",
    BRANCHES / "B0010-test-plan.tsv",
    BRANCHES / "B0010-wrapper-imports.tsv",
)


class MaterializationError(RuntimeError):
    pass


@dataclass(frozen=True)
class Command:
    owner: str
    name: str
    ordinal: int
    start_line: int
    start_column: int
    end_line: int
    end_column: int
    command_sha256: str
    destination: str


def run_git(root: Path, *args: str, binary: bool = False) -> str | bytes:
    result = subprocess.run(
        ["git", *args],
        cwd=root,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=not binary,
    )
    return result.stdout if binary else result.stdout.strip()


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def git_blob_oid(payload: bytes) -> str:
    header = f"blob {len(payload)}\0".encode("ascii")
    return hashlib.sha1(header + payload).hexdigest()


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8-sig", newline="") as stream:
        return list(csv.DictReader(stream, delimiter="\t"))


def split_semicolon(value: str) -> list[str]:
    return [] if value == "-" else value.split(";")


def module_path(module: str) -> Path:
    return Path(*module.split(".")).with_suffix(".lean")


def utf16_offset0(
    lines: list[str], starts: list[int], line0: int, column: int
) -> int:
    if line0 == len(lines) and column == 0:
        return sum(len(line) for line in lines)
    if line0 < 0 or line0 >= len(lines):
        raise MaterializationError(f"source line out of range: {line0}:{column}")
    content = lines[line0]
    if content.endswith("\n"):
        content = content[:-1]
    if content.endswith("\r"):
        content = content[:-1]
    units = 0
    for index, character in enumerate(content):
        if units == column:
            return starts[line0] + index
        units += 2 if ord(character) > 0xFFFF else 1
        if units > column:
            raise MaterializationError(
                f"coordinate splits UTF-16 surrogate pair: {line0}:{column}"
            )
    if units == column:
        return starts[line0] + len(content)
    raise MaterializationError(f"source column out of range: {line0}:{column}")


def expanded_doc_start(source: str, start: int) -> int:
    cursor = start
    while cursor and source[cursor - 1].isspace():
        cursor -= 1
    if cursor < 2 or source[cursor - 2 : cursor] != "-/":
        return start
    opening = source.rfind("/-", 0, cursor - 2)
    if opening >= 0 and source.startswith("/--", opening):
        return opening
    return start


def expanded_wrapper_start(source: str, start: int) -> int:
    """Attach standalone ``... in`` command wrappers to the next command."""

    cursor = start
    while True:
        while cursor and source[cursor - 1].isspace():
            cursor -= 1
        previous_start = source.rfind("\n", 0, cursor) + 1
        previous = source[previous_start:cursor].strip()
        wrapped = (
            re.fullmatch(r"(?:open|omit|include)\s+.+\s+in", previous)
            or re.fullmatch(r"set_option\s+.+\s+in", previous)
            or re.fullmatch(r"attribute\s+.+\s+in", previous)
        )
        if not wrapped:
            return start
        start = previous_start
        cursor = previous_start


def blank_region(characters: list[str], start: int, end: int) -> None:
    for index in range(start, end):
        if characters[index] not in "\r\n":
            characters[index] = " "


def blank_comments_outside_ranges(
    source: str,
    characters: list[str],
    protected_ranges: list[tuple[int, int]],
) -> None:
    """Remove historical prose while preserving routed command/doc bytes.

    The source owners contain large file-level narratives and sectional prose
    describing their old mixed role.  Those comments are not ambient Lean
    scaffolding and become false when duplicated into semantic leaves.  Lean
    supports nested block comments, so scan them explicitly.  Routed command
    ranges (including their `/-- ... -/` declaration docs and proof comments)
    are protected byte-for-byte.
    """

    protected = iter(sorted(protected_ranges))
    current = next(protected, None)
    index = 0
    while index < len(source):
        while current is not None and index >= current[1]:
            current = next(protected, None)
        if current is not None and current[0] <= index < current[1]:
            index = current[1]
            continue
        if source[index] == '"':
            cursor = index + 1
            escaped = False
            while cursor < len(source):
                character = source[cursor]
                cursor += 1
                if escaped:
                    escaped = False
                elif character == "\\":
                    escaped = True
                elif character == '"':
                    break
            else:
                raise MaterializationError("unterminated string in frozen source")
            index = cursor
            continue
        if source[index] == "«":
            cursor = source.find("»", index + 1)
            if cursor < 0:
                raise MaterializationError("unterminated quoted identifier in frozen source")
            index = cursor + 1
            continue
        if source.startswith("--", index):
            end = source.find("\n", index)
            if end < 0:
                end = len(source)
            blank_region(characters, index, end)
            index = end
            continue
        if source.startswith("/-", index):
            depth = 1
            cursor = index + 2
            while cursor < len(source) and depth:
                if source.startswith("/-", cursor):
                    depth += 1
                    cursor += 2
                elif source.startswith("-/", cursor):
                    depth -= 1
                    cursor += 2
                else:
                    cursor += 1
            if depth:
                raise MaterializationError("unterminated block comment in frozen source")
            blank_region(characters, index, cursor)
            index = cursor
            continue
        index += 1


def compact_unprotected_lines(
    source: str,
    characters: list[str],
    protected_ranges: list[tuple[int, int]],
) -> str:
    """Collapse masked ambient gaps without changing protected command lines."""

    rendered: list[str] = []
    previous_blank = False
    offset = 0
    for line in source.splitlines(keepends=True):
        end = offset + len(line)
        protected = any(start < end and offset < stop for start, stop in protected_ranges)
        masked = "".join(characters[offset:end])
        if protected:
            rendered.append(masked)
            previous_blank = False
        else:
            newline = "\n" if masked.endswith(("\n", "\r")) else ""
            content = masked.rstrip(" \t\r\n")
            if content:
                rendered.append(content + newline)
                previous_blank = False
            elif not previous_blank:
                rendered.append(newline or "\n")
                previous_blank = True
        offset = end
    return "".join(rendered).rstrip(" \t\r\n") + "\n"


IMPORT_RE = re.compile(
    r"(?m)^(?:(?:public|private|meta)[ \t]+)*import[ \t]+[^\r\n]+(?:\r?\n|$)"
)


def render_subset(source: str, commands: list[Command], keep: set[str]) -> str:
    """Mask non-routed commands while preserving ambient Lean scaffolding."""

    lines = source.splitlines(keepends=True)
    starts: list[int] = []
    offset = 0
    for line in lines:
        starts.append(offset)
        offset += len(line)
    characters = list(source)
    protected_ranges: list[tuple[int, int]] = []
    for match in IMPORT_RE.finditer(source):
        blank_region(characters, match.start(), match.end())
    prior_end = -1
    for command in sorted(
        commands,
        key=lambda item: (
            item.start_line,
            item.start_column,
            item.end_line,
            item.end_column,
        ),
    ):
        start = utf16_offset0(
            lines, starts, command.start_line, command.start_column
        )
        end = utf16_offset0(lines, starts, command.end_line, command.end_column)
        raw = source[start:end].encode("utf-8")
        if sha256_bytes(raw) != command.command_sha256:
            raise MaterializationError(
                f"{command.owner}/{command.name}: frozen command hash mismatch"
            )
        start = expanded_wrapper_start(source, expanded_doc_start(source, start))
        if start < prior_end:
            raise MaterializationError(
                f"{command.owner}/{command.name}: expanded command spans overlap"
            )
        prior_end = end
        if command.name in keep:
            protected_ranges.append((start, end))
        else:
            blank_region(characters, start, end)
    blank_comments_outside_ranges(source, characters, protected_ranges)
    return compact_unprotected_lines(source, characters, protected_ranges)


def canonical_doc(
    module: str, tier: str, rationale: str, contributors: list[str]
) -> str:
    title = module.removeprefix("NumStability.")
    sources = ", ".join(f"`{owner}`" for owner in contributors)
    return (
        f"/-!\n# {title}\n\n"
        f"R07 canonical `{tier}` leaf. {rationale}\n\n"
        f"Whole declaration commands are copied byte-for-byte from {sources}. "
        "Declaration names, visibility, namespaces, signatures, and proofs are "
        "unchanged; authored-private names are re-mangled only by their reviewed "
        "destination module.\n-/\n"
    )


def wrapper_doc(owner: str, destinations: list[str], imports: list[str]) -> str:
    title = owner.removeprefix("NumStability.")
    exported = [destination for destination in destinations if destination in imports]
    if exported:
        disposition = (
            "Its declaration block moved to "
            + ", ".join(f"`{item}`" for item in exported)
            + ", imported above."
        )
    else:
        disposition = (
            "Its only routed material is private support in an internal leaf, "
            "which is intentionally not re-exported from this historical path."
        )
    return (
        f"/-!\n# {title} (compatibility wrapper)\n\n"
        f"Import-only historical R07 path. {disposition} The exact C0005 direct "
        "import sequence remains available so existing imports preserve their "
        "supported public surface. This module declares nothing.\n-/\n"
    )


def test_doc(test_class: str, purpose: str) -> str:
    return f"/-!\n# R07 {test_class} test\n\n{purpose}\n-/\n"


def lean_string(value: str) -> str:
    return json.dumps(value, ensure_ascii=False)


def split_private_name(full_name: str, module: str) -> tuple[int, str]:
    prefix = f"_private.{module}."
    if not full_name.startswith(prefix):
        raise MaterializationError(
            f"private name {full_name!r} does not use module {module!r}"
        )
    remainder = full_name[len(prefix) :]
    ordinal_text, separator, logical = remainder.partition(".")
    if not separator or not ordinal_text.isdigit() or not logical:
        raise MaterializationError(f"malformed private name: {full_name}")
    # Lean's Name pretty-printer quotes identifier components such as
    # `term↑ₐ` as `«term↑ₐ»`.  The guillemets are parser syntax, not
    # bytes in the underlying `Lean.Name.str` component constructed below.
    logical_parts = logical.split(".")
    logical = ".".join(
        part[1:-1] if part.startswith("«") and part.endswith("»") else part
        for part in logical_parts
    )
    return int(ordinal_text), logical


def private_test_payload(
    imports: list[str],
    normalization_rows: list[dict[str, str]],
    closure_rows: list[dict[str, str]],
    owner_by_name: dict[str, str],
) -> bytes:
    lines = [f"import {module}" for module in imports]
    lines += [
        "",
        "/-!",
        "# R07 private normalization (exhaustive)",
        "",
        "Requires every one of the 44 approved destination-private names to be",
        "present, every historical private name to be absent, and every public",
        "member of the reviewed 77-row private reverse closure to elaborate.",
        "-/",
        "",
        "private def appendNameParts (baseName : Lean.Name) (parts : List String) : Lean.Name :=",
        "  parts.foldl (fun name part => .str name part) baseName",
        "",
        "private def mangledPrivateName (moduleName declarationName : String)",
        "    (ordinal : Nat) : Lean.Name :=",
        "  let modulePrefix := appendNameParts .anonymous (\"_private\" :: moduleName.splitOn \".\")",
        "  appendNameParts (.num modulePrefix ordinal) (declarationName.splitOn \".\")",
        "",
        "private def approvedPrivateNames : List Lean.Name := [",
    ]
    for row in normalization_rows:
        ordinal, logical = split_private_name(
            row["new_private"], row["destination_module"]
        )
        lines.append(
            "  mangledPrivateName "
            f"{lean_string(row['destination_module'])} {lean_string(logical)} {ordinal},"
        )
    lines += ["]", "", "private def retiredPrivateNames : List Lean.Name := ["]
    for row in normalization_rows:
        owner = owner_by_name[row["old_private"]]
        ordinal, logical = split_private_name(row["old_private"], owner)
        lines.append(
            "  mangledPrivateName "
            f"{lean_string(owner)} {lean_string(logical)} {ordinal},"
        )
    lines += [
        "]",
        "",
        "run_cmd do",
        "  let environment ← Lean.getEnv",
        "  for name in approvedPrivateNames do",
        "    unless Lean.Environment.contains environment name do",
        '      throwError "R07 private normalization: missing approved name {name}"',
        "  for name in retiredPrivateNames do",
        "    if Lean.Environment.contains environment name then",
        '      throwError "R07 private normalization: retired name {name} still present"',
        "",
    ]
    for row in sorted(closure_rows, key=lambda item: item["declaration"]):
        if row["visibility"] == "public":
            lines.append(f"#check @{row['declaration']}")
    lines.append("")
    return "\n".join(lines).encode("utf-8")


def verify_control(control_root: Path) -> dict[str, str]:
    head = run_git(control_root, "rev-parse", "HEAD")
    if head != CONTROL_HEAD_SHA:
        raise MaterializationError(
            f"control checkout HEAD {head} != activation control {CONTROL_HEAD_SHA}"
        )
    contract_path = control_root / REVIEWS / "R07-planned-control-contract.json"
    if sha256_path(contract_path) != CONTROL_CONTRACT_SHA256:
        raise MaterializationError("planned-control contract hash mismatch")
    activation_path = control_root / REVIEWS / "R07-activation.json"
    if sha256_path(activation_path) != ACTIVATION_SHA256:
        raise MaterializationError("activation evidence hash mismatch")
    active_branch_path = control_root / BRANCHES / "B0010.json"
    if sha256_path(active_branch_path) != ACTIVE_BRANCH_SHA256:
        raise MaterializationError("active B0010 hash mismatch")
    active_branch = json.loads(active_branch_path.read_text(encoding="utf-8"))
    if (
        active_branch.get("status") != "active"
        or active_branch.get("base_sha") != BASE_CODE_SHA
        or active_branch.get("branch_name") != WORKER_BRANCH
    ):
        raise MaterializationError("active B0010 identity/lifecycle mismatch")
    contract = json.loads(contract_path.read_text(encoding="utf-8"))
    if (
        contract.get("base_checkpoint_id") != "C0005"
        or contract.get("base_code_sha") != BASE_CODE_SHA
        or contract.get("branch_id") != "B0010"
        or contract.get("wave_id") != "R07"
    ):
        raise MaterializationError("planned-control contract identity mismatch")
    artifacts = {row["path"]: row["sha256"] for row in contract["artifacts"]}
    for relative in REQUIRED_CONTROL_PATHS:
        key = relative.as_posix()
        expected = artifacts.get(key)
        if expected is None:
            raise MaterializationError(f"contract omits required artifact {key}")
        if sha256_path(control_root / relative) != expected:
            raise MaterializationError(f"required control hash mismatch: {key}")
    return artifacts


def allowed_scope(scope_rows: list[dict[str, str]]) -> tuple[set[str], tuple[str, ...]]:
    exact = {
        row["path"]
        for row in scope_rows
        if row["scope"] == "worker_owned" and row["match"] == "exact"
    }
    prefixes = tuple(
        row["path"]
        for row in scope_rows
        if row["scope"] == "worker_destination" and row["match"] == "prefix"
    )
    if len(exact) != EXPECTED_OWNERS or len(prefixes) != 17:
        raise MaterializationError("worker scope census mismatch")
    return exact, prefixes


def atomic_write(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as stream:
        temporary = Path(stream.name)
        stream.write(payload)
    try:
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--project-root", type=Path, default=Path.cwd())
    parser.add_argument("--control-root", type=Path, required=True)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    root = args.project_root.resolve()
    control = args.control_root.resolve()
    if run_git(root, "rev-parse", "HEAD") != BASE_CODE_SHA:
        raise MaterializationError("worker HEAD is not the exact C0005 code base")
    if run_git(root, "branch", "--show-current") != WORKER_BRANCH:
        raise MaterializationError("wrong worker branch")
    verify_control(control)

    def rows(name: str) -> list[dict[str, str]]:
        return read_tsv(control / BRANCHES / name)

    module_rows = rows("B0010-module-routes.tsv")
    destination_rows = rows("B0010-destinations.tsv")
    source_rows = rows("B0010-source-commands.tsv")
    declaration_rows = rows("B0010-declaration-routes.tsv")
    manifest_rows = rows("B0010-post-move-import-manifest.tsv")
    test_rows = rows("B0010-test-plan.tsv")
    normalization_rows = rows("B0010-private-normalization.tsv")
    closure_rows = rows("B0010-private-closure.tsv")
    scope_rows = rows("B0010-scope-rules.tsv")
    exact_scope, prefix_scope = allowed_scope(scope_rows)

    bearing = [row for row in module_rows if int(row["declaration_count"]) > 0]
    if (
        len(module_rows) != EXPECTED_OWNERS
        or len(bearing) != EXPECTED_BEARING_OWNERS
        or len(destination_rows) != EXPECTED_DESTINATIONS
        or len(source_rows) != EXPECTED_DECLARATIONS
        or len(declaration_rows) != EXPECTED_DECLARATIONS
        or len(normalization_rows) != EXPECTED_PRIVATE
        or len(closure_rows) != EXPECTED_CLOSURE
        or len(test_rows) != EXPECTED_TESTS
    ):
        raise MaterializationError("reviewed control census mismatch")

    module_by_owner = {row["owner_module"]: row for row in module_rows}
    route_by_name = {row["baseline_declaration_name"]: row for row in declaration_rows}
    if len(route_by_name) != EXPECTED_DECLARATIONS:
        raise MaterializationError("declaration route names are not unique")
    commands_by_owner: dict[str, list[Command]] = defaultdict(list)
    owner_by_name: dict[str, str] = {}
    frozen_sources: dict[str, str] = {}
    for row in source_rows:
        name = row["baseline_declaration_name"]
        route = route_by_name.get(name)
        if route is None or route["baseline_owner_module"] != row["owner_module"]:
            raise MaterializationError(f"source/route mismatch for {name}")
        owner_by_name[name] = row["owner_module"]
        commands_by_owner[row["owner_module"]].append(
            Command(
                owner=row["owner_module"],
                name=name,
                ordinal=int(row["source_ordinal"]),
                start_line=int(row["start_line_0"]),
                start_column=int(row["start_column_0"]),
                end_line=int(row["end_line_0"]),
                end_column=int(row["end_column_0"]),
                command_sha256=row["command_sha256"],
                destination=route["destination_module"],
            )
        )
    if set(commands_by_owner) != {row["owner_module"] for row in bearing}:
        raise MaterializationError("bearing-owner/source-command partition mismatch")

    for row in module_rows:
        owner = row["owner_module"]
        relative = row["path"]
        payload = run_git(root, "show", f"{BASE_CODE_SHA}:{relative}", binary=True)
        assert isinstance(payload, bytes)
        if git_blob_oid(payload) != row["base_blob_oid"]:
            raise MaterializationError(f"base blob mismatch for {owner}")
        if owner in commands_by_owner:
            frozen_sources[owner] = payload.decode("utf-8")

    imports_by_module: dict[str, list[str]] = defaultdict(list)
    for row in sorted(
        manifest_rows,
        key=lambda item: (item["module"], int(item["import_order"])),
    ):
        line = row["lean_import_line"]
        if not line.startswith("import "):
            raise MaterializationError(f"non-import manifest line: {line}")
        imports_by_module[row["module"]].append(line.removeprefix("import "))
    if any(len(values) != len(set(values)) for values in imports_by_module.values()):
        raise MaterializationError("post-move manifest contains duplicate imports")

    outputs: dict[Path, bytes] = {}
    destination_by_module = {row["module"]: row for row in destination_rows}
    commands_by_destination: dict[str, list[Command]] = defaultdict(list)
    for commands in commands_by_owner.values():
        for command in commands:
            commands_by_destination[command.destination].append(command)
    if set(commands_by_destination) != set(destination_by_module):
        raise MaterializationError("destination command coverage mismatch")

    special_owner_order = {
        "NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.NormalCharacterization.Schur": [
            "NumStability.Analysis.MatrixPowersSchur",
            "NumStability.Analysis.MatrixPowersHenriciNormal",
        ]
    }
    for module in sorted(destination_by_module):
        destination = destination_by_module[module]
        routed = commands_by_destination[module]
        contributors = sorted({command.owner for command in routed})
        order = special_owner_order.get(module, contributors)
        if set(order) != set(contributors):
            raise MaterializationError(f"{module}: incomplete contributor order")
        import_lines = imports_by_module[module]
        payload = "".join(f"import {item}\n" for item in import_lines) + "\n"
        payload += canonical_doc(
            module, destination["tier"], destination["rationale"], order
        )
        by_owner: dict[str, set[str]] = defaultdict(set)
        for command in routed:
            by_owner[command.owner].add(command.name)
        for owner in order:
            payload += "\n" + render_subset(
                frozen_sources[owner], commands_by_owner[owner], by_owner[owner]
            )
        outputs[module_path(module)] = payload.encode("utf-8")

    for row in bearing:
        owner = row["owner_module"]
        imports = imports_by_module[owner]
        destinations = split_semicolon(row["destination_modules"])
        payload = "".join(f"import {item}\n" for item in imports) + "\n"
        payload += wrapper_doc(owner, destinations, imports)
        outputs[Path(row["path"])] = payload.encode("utf-8")

    for row in test_rows:
        relative = Path(row["target"])
        imports = split_semicolon(row["imports"])
        forbidden = set(split_semicolon(row["forbidden_imports"]))
        if set(imports) & forbidden:
            raise MaterializationError(f"{relative}: direct forbidden test import")
        if row["test_class"] == "private_normalization":
            payload = private_test_payload(
                imports, normalization_rows, closure_rows, owner_by_name
            )
        else:
            lines = [f"import {module}" for module in imports]
            lines += ["", test_doc(row["test_class"], row["purpose"]).rstrip(), ""]
            expected = split_semicolon(row["expected_declarations"])
            if expected and all(name.startswith("NumStability.") for name in expected):
                lines.extend(f"#check @{name}" for name in expected)
            lines.append("")
            payload = ("\n".join(lines).rstrip("\n") + "\n").encode("utf-8")
        outputs[relative] = payload

    if len(outputs) != EXPECTED_DESTINATIONS + EXPECTED_BEARING_OWNERS + EXPECTED_TESTS:
        raise MaterializationError("rendered worker output count mismatch")
    for relative in outputs:
        posix = relative.as_posix()
        if posix not in exact_scope and not any(posix.startswith(prefix) for prefix in prefix_scope):
            raise MaterializationError(f"rendered path is outside worker scope: {posix}")

    materialization = {
        "base_code_sha": BASE_CODE_SHA,
        "control_head_sha": CONTROL_HEAD_SHA,
        "record_kind": "r07_worker_materialization",
        "schema_version": 1,
        "files": [
            {
                "path": relative.as_posix(),
                "sha256": sha256_bytes(payload),
            }
            for relative, payload in sorted(outputs.items(), key=lambda item: item[0].as_posix())
        ],
        "counts": {
            "destinations": EXPECTED_DESTINATIONS,
            "historical_wrappers_rewritten": EXPECTED_BEARING_OWNERS,
            "historical_wrappers_unchanged": EXPECTED_OWNERS - EXPECTED_BEARING_OWNERS,
            "source_commands": EXPECTED_DECLARATIONS,
            "tests": EXPECTED_TESTS,
        },
    }
    materialization_path = Path(
        "docs/architecture/deliveries/R07/MATERIALIZATION.json"
    )
    materialization_payload = (
        json.dumps(materialization, indent=1, sort_keys=True, ensure_ascii=False) + "\n"
    ).encode("utf-8")

    if not args.write:
        print(
            json.dumps(
                {
                    "production_destinations": EXPECTED_DESTINATIONS,
                    "rewritten_wrappers": EXPECTED_BEARING_OWNERS,
                    "unchanged_wrappers": EXPECTED_OWNERS - EXPECTED_BEARING_OWNERS,
                    "tests": EXPECTED_TESTS,
                    "rendered_files": len(outputs),
                    "materialization_sha256": sha256_bytes(materialization_payload),
                },
                indent=1,
            )
        )
        return 0

    for relative, payload in sorted(outputs.items(), key=lambda item: item[0].as_posix()):
        atomic_write(root / relative, payload)
    atomic_write(root / materialization_path, materialization_payload)

    status = run_git(
        root, "status", "--porcelain=v1", "-z", "--untracked-files=all", binary=True
    )
    assert isinstance(status, bytes)
    changed = []
    for entry in status.split(b"\0"):
        if entry:
            changed.append(entry[3:].decode("utf-8"))
    unauthorized = sorted(
        path
        for path in changed
        if path not in exact_scope and not any(path.startswith(prefix) for prefix in prefix_scope)
    )
    if unauthorized:
        raise MaterializationError(
            "worker status contains unauthorized paths: " + ", ".join(unauthorized)
        )
    print(
        f"wrote {EXPECTED_DESTINATIONS} destinations, {EXPECTED_BEARING_OWNERS} wrappers, "
        f"{EXPECTED_TESTS} tests, and MATERIALIZATION.json; status paths={len(changed)}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (MaterializationError, OSError, ValueError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=os.sys.stderr)
        raise SystemExit(2)
