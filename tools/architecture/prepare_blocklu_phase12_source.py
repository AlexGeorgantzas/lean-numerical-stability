#!/usr/bin/env python3
"""Prepare deterministic Phase 12 BlockLU source-leaf drafts.

This tool is intentionally a *preparation* tool.  It reads the immutable
pre-migration ``BlockLU.lean`` blob and its matching Lean information file,
checks the reviewed format-2 ownership contract, and emits a command ledger.
With ``--output-dir`` it can additionally create 66 non-collision source-leaf
drafts in a new, explicitly supplied directory outside the repository.  It
never edits or overwrites a repository file.

The three commands that used private recursive-factorization helpers need
reviewed post-RecursiveFactorization replacements.  Draft generation therefore
requires ``--overlay-manifest`` with this LF-terminated TSV shape::

    format\t1
    logical_command_root\tpath\tSHA256

Relative overlay paths are resolved from the overlay manifest.  Each supplied
hash is checked before the replacement is read.  Ledger-only dry runs do not
need overlays and always describe the frozen source commands.

Example (ledger-only dry run)::

    python tools/architecture/prepare_blocklu_phase12_source.py \
      --project-root . \
      --baseline-repo C:/worktrees/phase12-v2-baseline \
      --ilean C:/worktrees/phase12-v2-baseline/.lake/build/lib/lean/\
NumStability/Algorithms/LU/BlockLU.ilean \
      --dependency-tsv C:/worktrees/phase12-v2-baseline/benchmark-results/\
architecture/phase11b2-declarations-v2.tsv \
      --ledger C:/temp/phase12-source-command-ledger.tsv

The generator uses individual top-level command spans from ``.ilean``.  It
does not slice or concatenate the reviewed route ranges.
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
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Iterator


BASE_REVISION = "b36b4154d296cacb651ba31332f208b421b77ecc"
BLOCKLU_MODULE = "NumStability.Algorithms.LU.BlockLU"
BLOCKLU_SOURCE_PATH = "NumStability/Algorithms/LU/BlockLU.lean"
BLOCKLU_BLOB = "722dff73bcd4713ff1129a42653aa30c67ab4a22"
BLOCKLU_FILE_SHA256 = (
    "6794693991CBCF7ABBDC3C6C2D31A362746609C0CBC14210486191E44A3E80E7"
)
BLOCKLU_ILEAN_SHA256 = (
    "6A25C1A27E5DDDA63D44A2668D5E601C151E2181CC6A882261CD028197B6B609"
)
MANIFEST_SHA256 = (
    "90F28D568A611035DE20839F2C30CB2800B75F2FC1DF2CE1373E9FFDD3D11287"
)
DEPENDENCY_TSV_SHA256 = (
    "FD37F73D83F0206E40291576E1F9496185F09C21928ABED147B5CE2A6EF83AED"
)

EXPECTED_MANIFEST_ROWS = 1_990
EXPECTED_BLOCKLU_ROOTS = 1_715
EXPECTED_SOURCE_OWNERS = 68
EXPECTED_SOURCE_COMMANDS = 1_532
EXPECTED_SOURCE_DECLARATIONS = 1_695
EXPECTED_SOURCE_PUBLIC_DECLARATIONS = 1_678
EXPECTED_SOURCE_PRIVATE_DECLARATIONS = 17
EXPECTED_ALREADY_MOVED_COMMANDS = 183
EXPECTED_DIRECT_SOURCE_COMMANDS = 1_529
EXPECTED_OVERLAY_COMMANDS = 3
EXPECTED_DAG_EDGES = 215
EXPECTED_DAG_LEVELS = 13
EXPECTED_PROJECT_IMPORT_PAIRS = 505
EXPECTED_BANNER_GAPS = 24
EXPECTED_CROSS_OWNER_BANNER_GAPS = 22

# Filled from the pinned artifacts and checked on every real run.  Keeping
# these aggregate hashes here makes span/trivia policy changes explicit.
EXPECTED_COMMAND_BODY_SHA256 = (
    "D6174A84EB36D0E7CC52A02BCF770685ECE61EB13495D06A9BC0E23CAB5672CB"
)
EXPECTED_LEDGER_SHA256 = (
    "3CC7AFF9436549B67C8CD74638DB32C56D8E3E985AF392023028C9FCE143C254"
)
EXPECTED_IMPORT_WITNESSES_SHA256 = (
    "AE8BA7EE88D050CF787DA4944FA4C8E2ABE8C13F15477ABE6497F1CA4C178777"
)

RECURRENCES = "NumStability.Source.Higham.Chapter13.Theorem05.Recurrences"
SOURCE_PREFIX = "NumStability.Source.Higham.Chapter13."

SELECTED_REUSABLE_DESTINATIONS = {
    "NumStability.Algorithms.LinearSystems.LU.BlockLU.BlockMatrices",
    "NumStability.Algorithms.LinearSystems.LU.BlockLU.DiagonalDominance",
    "NumStability.Algorithms.LinearSystems.LU.BlockLU.Factorization",
    "NumStability.Algorithms.LinearSystems.LU.BlockLU.FirstOrderModels",
    "NumStability.Algorithms.LinearSystems.LU.BlockLU.GrowthBounds",
    "NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefinite",
    "NumStability.Algorithms.LinearSystems.LU.BlockLU.RecursiveFactorization",
    "NumStability.Algorithms.LinearSystems.LU.BlockLU.ResidualLifting",
    "NumStability.Algorithms.LinearSystems.LU.BlockLU.SchurComplement",
    "NumStability.Algorithms.LinearSystems.LU.BlockLU.SolveError",
    "NumStability.Analysis.FirstOrder.FixedPrecision",
    "NumStability.Analysis.MatrixNorms.EntrywiseMaximum",
}

EXTERNAL_PROJECT_MODULES = {
    "NumStability.Algorithms.Cholesky.CholeskySpec",
    "NumStability.Algorithms.LU.GaussianElimination",
    "NumStability.Algorithms.LU.GrowthFactor",
    "NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution",
    "NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution",
    "NumStability.Algorithms.MatMul",
    "NumStability.Analysis.MatrixAlgebra",
    "NumStability.Analysis.MatrixSpectral",
    "NumStability.Analysis.PerturbationTheory",
    "NumStability.Analysis.Rounding",
    "NumStability.FloatingPoint.Model",
}

EXPECTED_MATHLIB_IMPORTS = {
    "Mathlib.Algebra.BigOperators.Group.Finset.Basic",
    "Mathlib.Algebra.BigOperators.Ring.Finset",
    "Mathlib.Algebra.Order.BigOperators.Group.Finset",
    "Mathlib.Analysis.Asymptotics.Lemmas",
    "Mathlib.Data.Real.Basic",
    "Mathlib.Data.Real.Sqrt",
    "Mathlib.LinearAlgebra.Matrix.SchurComplement",
    "Mathlib.Logic.Equiv.Fin.Basic",
    "Mathlib.Tactic.Abel",
    "Mathlib.Tactic.FieldSimp",
    "Mathlib.Tactic.FinCases",
    "Mathlib.Tactic.Linarith",
    "Mathlib.Tactic.NormNum",
    "Mathlib.Tactic.Ring",
}

FORBIDDEN_IMPORTS = {
    BLOCKLU_MODULE,
    "NumStability.Algorithms.LU",
    "NumStability.Algorithms",
    "NumStability.Source",
    "NumStability.Source.Higham",
    "NumStability.Source.Higham.Chapter13",
}

OVERLAY_ROOTS = {
    "NumStability.block_lu_one_step_explicit": (
        "6049333C1F9D830C7AC3F4248A2AFF2FC281307814FBC4D19F7E42C486B7A357"
    ),
    "NumStability.BlockLUFactSpec.firstRow_eq": (
        "0DB78B5B9DCCEBBBF102CBC0EF680D8E4C39BD71FD7FA73BCB03C81107810033"
    ),
    "NumStability.BlockLUFactSpec.firstColumnBelow_eq_of_right_inverse": (
        "A264541AF8E39FE65F76F80DFA0E4EE83B9BE2E97FF18C2BB0BDF12EA931A9E0"
    ),
}

PRIVATE_SOURCE_COUNTS = {
    "NumStability.Source.Higham.Chapter13.Theorem02.Factorization": 2,
    "NumStability.Source.Higham.Chapter13.Theorem02.Uniqueness": 15,
}

COLLISIONS = {
    "NumStability.Source.Higham.Chapter13.Equation25": {
        "path": "NumStability/Source/Higham/Chapter13/Equation25.lean",
        "blob": "66283f458a6e903dd37c99eeed74dafc49b47c74",
        "sha256": (
            "4B94BC8DF2746A563ED0FDAD22876AAC0D9728B7A72E17E1E1AA9E3F44B5DAA8"
        ),
        "mapped_declarations": 2,
        "mapped_commands": 2,
        "apis": (
            "higham13_eq13_25_implementation1_spd_family_from_"
            "partitioned_computation",
        ),
    },
    "NumStability.Source.Higham.Chapter13.Table01": {
        "path": "NumStability/Source/Higham/Chapter13/Table01.lean",
        "blob": "ddabf35f443a0723e565cb3d02a42fb8ce4f4071",
        "sha256": (
            "B7CEC66EB258B4CDA9BF3B816FCF293A7524585BF2C0564F549E9663B3ABB1B7"
        ),
        "mapped_declarations": 22,
        "mapped_commands": 22,
        "apis": (
            "higham13_table13_1_col_bdd_product_family_from_source_norms",
            "higham13_table13_1_point_col_bdd_product_family_from_source_norms",
            "higham13_table13_1_arbitrary_product_family_from_"
            "eq13_22_source_norms",
            "higham13_table13_1_point_row_product_family_from_"
            "eq13_23_source_norms",
            "higham13_table13_1_spd_product_family_from_eq13_24_source_norms",
            "higham13_table13_1_implementation1_family_from_"
            "partitioned_computation_and_product_transfer",
        ),
    },
}

HEX_SHA256 = re.compile(r"^[0-9A-Fa-f]{64}$")
MODULE_NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$")


@dataclass(frozen=True)
class ManifestRow:
    logical_name: str
    historical_module: str
    destination_module: str
    kind: str
    visibility: str


@dataclass(frozen=True)
class Declaration:
    name: str
    module: str
    kind: str
    visibility: str


@dataclass(frozen=True)
class Edge:
    kind: str
    source: str
    target: str


@dataclass(frozen=True)
class CommandSpan:
    root: str
    logical_root: str
    start_line: int
    start_column: int
    end_line: int
    end_column: int
    start_offset: int
    end_offset: int
    owner: str
    declarations: tuple[str, ...]
    private_declarations: int


@dataclass(frozen=True)
class CommandPayload:
    span: CommandSpan
    leading_trivia: str
    command: str
    trailing_trivia: str

    @property
    def payload(self) -> str:
        return self.leading_trivia + self.command + self.trailing_trivia


@dataclass(frozen=True)
class ImportWitness:
    source_owner: str
    target_module: str
    source_name: str
    target_name: str
    detail: str


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def git_blob_sha1(payload: bytes) -> str:
    header = f"blob {len(payload)}\0".encode("ascii")
    return hashlib.sha1(header + payload).hexdigest()


def run_git(repo: Path, *arguments: str, text: bool = True) -> str | bytes:
    result = subprocess.run(
        ["git", "-C", str(repo), *arguments],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=text,
        encoding="utf-8" if text else None,
    )
    if result.returncode != 0:
        stderr = result.stderr if text else result.stderr.decode("utf-8", "replace")
        raise ValueError(
            f"git {' '.join(arguments)} failed in {repo}: {stderr.strip()}"
        )
    return result.stdout


def require_hash(path: Path, expected: str, description: str) -> None:
    actual = sha256_file(path)
    if actual != expected:
        raise ValueError(
            f"{description} SHA-256 differs: expected {expected}, found {actual}"
        )


def read_frozen_source(baseline_repo: Path) -> tuple[bytes, str]:
    revision = str(
        run_git(baseline_repo, "rev-parse", "--verify", f"{BASE_REVISION}^{{commit}}")
    ).strip()
    if revision != BASE_REVISION:
        raise ValueError(
            f"base revision resolved to {revision}, expected {BASE_REVISION}"
        )
    blob = str(
        run_git(baseline_repo, "rev-parse", f"{BASE_REVISION}:{BLOCKLU_SOURCE_PATH}")
    ).strip()
    if blob != BLOCKLU_BLOB:
        raise ValueError(
            f"frozen BlockLU blob differs: expected {BLOCKLU_BLOB}, found {blob}"
        )
    payload = run_git(baseline_repo, "cat-file", "blob", BLOCKLU_BLOB, text=False)
    assert isinstance(payload, bytes)
    if git_blob_sha1(payload) != BLOCKLU_BLOB:
        raise ValueError("git returned bytes that do not hash to the pinned BlockLU blob")
    digest = sha256_bytes(payload)
    if digest != BLOCKLU_FILE_SHA256:
        raise ValueError(
            f"frozen BlockLU file SHA-256 differs: expected {BLOCKLU_FILE_SHA256}, "
            f"found {digest}"
        )
    try:
        source = payload.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ValueError("frozen BlockLU source is not UTF-8") from error
    if "\r" in source:
        raise ValueError("frozen BlockLU source unexpectedly contains CR characters")
    return payload, source


def logical_name(actual_name: str, actual_module: str) -> str:
    if not actual_name.startswith("_private."):
        return actual_name
    prefix = f"_private.{actual_module}."
    if not actual_name.startswith(prefix):
        raise ValueError(
            f"private name {actual_name!r} does not encode owner {actual_module!r}"
        )
    ordinal, separator, suffix = actual_name[len(prefix) :].partition(".")
    if not separator or not ordinal.isdigit() or not suffix:
        raise ValueError(f"unexpected private name {actual_name!r}")
    return f"_private.<module>.{suffix}"


def read_manifest(path: Path) -> dict[str, ManifestRow]:
    require_hash(path, MANIFEST_SHA256, "Phase 12 format-2 manifest")
    records: dict[str, ManifestRow] = {}
    with path.open(encoding="utf-8", newline="") as stream:
        rows = csv.reader(stream, delimiter="\t")
        if next(rows, None) != ["format", "1"]:
            raise ValueError(f"{path}: manifest must begin with format\\t1")
        for line_number, row in enumerate(rows, 2):
            if len(row) != 5 or not all(row):
                raise ValueError(f"{path}:{line_number}: malformed manifest row")
            record = ManifestRow(*row)
            if record.logical_name in records:
                raise ValueError(
                    f"{path}:{line_number}: duplicate {record.logical_name}"
                )
            if not MODULE_NAME.fullmatch(record.destination_module):
                raise ValueError(
                    f"{path}:{line_number}: invalid destination module"
                )
            if record.visibility not in {"public", "private"}:
                raise ValueError(
                    f"{path}:{line_number}: unexpected visibility "
                    f"{record.visibility!r}"
                )
            records[record.logical_name] = record
    if len(records) != EXPECTED_MANIFEST_ROWS:
        raise ValueError(
            f"expected {EXPECTED_MANIFEST_ROWS} manifest rows, found {len(records)}"
        )
    return records


def read_dependency_declarations(path: Path) -> dict[str, Declaration]:
    require_hash(path, DEPENDENCY_TSV_SHA256, "Phase 11B2 format-2 graph")
    declarations: dict[str, Declaration] = {}
    saw_format = False
    with path.open(encoding="utf-8", newline="") as stream:
        for line_number, row in enumerate(csv.reader(stream, delimiter="\t"), 1):
            if not row:
                continue
            if row == ["format", "2"]:
                if saw_format or line_number != 1:
                    raise ValueError(f"{path}:{line_number}: misplaced format row")
                saw_format = True
            elif len(row) == 5 and row[0] == "declaration":
                if not saw_format or not all(row[1:]):
                    raise ValueError(
                        f"{path}:{line_number}: malformed declaration row"
                    )
                declaration = Declaration(*row[1:])
                if declaration.name in declarations:
                    raise ValueError(
                        f"{path}:{line_number}: duplicate declaration "
                        f"{declaration.name}"
                    )
                declarations[declaration.name] = declaration
            elif len(row) == 4 and row[0] == "edge":
                if not saw_format or row[1] not in {"signature", "body"}:
                    raise ValueError(f"{path}:{line_number}: malformed edge row")
            else:
                raise ValueError(f"{path}:{line_number}: malformed graph row")
    if not saw_format:
        raise ValueError(f"{path}: graph lacks format\\t2")
    return declarations


def iter_dependency_edges(path: Path) -> Iterator[Edge]:
    with path.open(encoding="utf-8", newline="") as stream:
        for row in csv.reader(stream, delimiter="\t"):
            if len(row) == 4 and row[0] == "edge":
                yield Edge(*row[1:])


def selected_actual_names(
    declarations: dict[str, Declaration], manifest: dict[str, ManifestRow]
) -> dict[str, ManifestRow]:
    selected: dict[str, ManifestRow] = {}
    found_logicals: set[str] = set()
    for actual, declaration in declarations.items():
        try:
            logical = logical_name(actual, declaration.module)
        except ValueError:
            continue
        record = manifest.get(logical)
        if record is None or record.historical_module != declaration.module:
            continue
        metadata = (declaration.kind, declaration.visibility)
        expected = (record.kind, record.visibility)
        if metadata != expected:
            raise ValueError(
                f"{logical}: graph metadata {metadata} differs from manifest "
                f"metadata {expected}"
            )
        selected[actual] = record
        found_logicals.add(logical)
    missing = sorted(set(manifest) - found_logicals)
    if missing:
        raise ValueError(
            "dependency graph does not realize every manifest row: "
            + ", ".join(missing[:20])
        )
    return selected


def read_ilean(path: Path) -> dict[str, object]:
    require_hash(path, BLOCKLU_ILEAN_SHA256, "frozen BlockLU .ilean")
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as error:
        raise ValueError(f"invalid .ilean JSON: {error}") from error
    if not isinstance(payload, dict):
        raise ValueError(".ilean root must be an object")
    if payload.get("module") != BLOCKLU_MODULE:
        raise ValueError(
            f".ilean owner is {payload.get('module')!r}, expected {BLOCKLU_MODULE}"
        )
    if payload.get("version") != 5:
        raise ValueError(f"unexpected .ilean version {payload.get('version')!r}")
    if not isinstance(payload.get("decls"), dict):
        raise ValueError(".ilean lacks a declaration map")
    if not isinstance(payload.get("references"), dict):
        raise ValueError(".ilean lacks a reference map")
    if not isinstance(payload.get("directImports"), list):
        raise ValueError(".ilean lacks direct imports")
    return payload


def source_offsets(source: str) -> tuple[list[str], list[int]]:
    lines = source.splitlines(keepends=True)
    starts: list[int] = []
    offset = 0
    for line in lines:
        starts.append(offset)
        offset += len(line)
    if offset != len(source):
        raise ValueError("source line accounting failed")
    return lines, starts


def coordinate_offset(
    lines: list[str], starts: list[int], line: int, column: int
) -> int:
    if line < 0 or line >= len(lines) or column < 0:
        raise ValueError(f"invalid source coordinate {line}:{column}")
    physical = lines[line]
    content = physical[:-1] if physical.endswith("\n") else physical
    if column > len(content):
        raise ValueError(
            f"source coordinate {line}:{column} exceeds Unicode line length "
            f"{len(content)}"
        )
    return starts[line] + column


def assign_roots(
    ilean: dict[str, object],
    manifest: dict[str, ManifestRow],
    source: str,
) -> list[CommandSpan]:
    decls = ilean["decls"]
    assert isinstance(decls, dict)
    if len(decls) != EXPECTED_BLOCKLU_ROOTS:
        raise ValueError(
            f"expected {EXPECTED_BLOCKLU_ROOTS} BlockLU roots, found {len(decls)}"
        )
    roots: dict[str, tuple[str, list[int]]] = {}
    for actual_root, raw_span in decls.items():
        if not isinstance(actual_root, str) or not isinstance(raw_span, list):
            raise ValueError("malformed .ilean declaration span")
        if len(raw_span) != 8 or any(not isinstance(value, int) for value in raw_span):
            raise ValueError(f"{actual_root}: expected an eight-integer .ilean span")
        logical_root = logical_name(actual_root, BLOCKLU_MODULE)
        if logical_root in roots:
            raise ValueError(f"duplicate logical command root {logical_root}")
        roots[logical_root] = (actual_root, raw_span)

    assigned: dict[str, list[str]] = {logical: [] for logical in roots}
    blocklu_records = {
        logical: record
        for logical, record in manifest.items()
        if record.historical_module == BLOCKLU_MODULE
    }
    for logical in blocklu_records:
        candidates = [
            root
            for root in roots
            if logical == root or logical.startswith(root + ".")
        ]
        if not candidates:
            raise ValueError(f"manifest declaration {logical} has no command root")
        longest = max(len(candidate) for candidate in candidates)
        winners = [candidate for candidate in candidates if len(candidate) == longest]
        if len(winners) != 1:
            raise ValueError(f"ambiguous command root for {logical}: {winners}")
        assigned[winners[0]].append(logical)

    empty = sorted(root for root, names in assigned.items() if not names)
    if empty:
        raise ValueError(
            ".ilean roots without semantic manifest declarations: "
            + ", ".join(empty[:20])
        )

    lines, starts = source_offsets(source)
    spans: list[CommandSpan] = []
    for logical_root, (actual_root, raw_span) in roots.items():
        start_line, start_column, end_line, end_column = raw_span[:4]
        if start_column != 0:
            raise ValueError(f"{actual_root}: top-level command does not start at col 0")
        start = coordinate_offset(lines, starts, start_line, start_column)
        end = coordinate_offset(lines, starts, end_line, end_column)
        if end <= start:
            raise ValueError(f"{actual_root}: empty or reversed command span")
        end_content = lines[end_line]
        if end_content.endswith("\n"):
            end_content = end_content[:-1]
        if end_content[end_column:].strip():
            raise ValueError(f"{actual_root}: nonblank source follows recorded end")
        names = tuple(sorted(assigned[logical_root]))
        owners = {blocklu_records[name].destination_module for name in names}
        if len(owners) != 1:
            raise ValueError(f"{actual_root}: command declarations split across {owners}")
        private_count = sum(
            blocklu_records[name].visibility == "private" for name in names
        )
        spans.append(
            CommandSpan(
                actual_root,
                logical_root,
                start_line,
                start_column,
                end_line,
                end_column,
                start,
                end,
                next(iter(owners)),
                names,
                private_count,
            )
        )
    spans.sort(key=lambda span: (span.start_offset, span.end_offset, span.root))
    for previous, current in zip(spans, spans[1:]):
        if current.start_offset < previous.end_offset:
            raise ValueError(
                f"overlapping command spans: {previous.root} and {current.root}"
            )
    return spans


def trivia_only(text: str) -> bool:
    index = 0
    depth = 0
    while index < len(text):
        if depth:
            if text.startswith("/-", index):
                depth += 1
                index += 2
            elif text.startswith("-/", index):
                depth -= 1
                index += 2
            else:
                index += 1
            continue
        if text[index].isspace():
            index += 1
        elif text.startswith("--", index):
            newline = text.find("\n", index + 2)
            index = len(text) if newline < 0 else newline + 1
        elif text.startswith("/-", index):
            depth = 1
            index += 2
        else:
            return False
    return depth == 0


def matching_block_comment_end(text: str, start: int) -> int:
    depth = 0
    index = start
    while index < len(text):
        if text.startswith("/-", index):
            depth += 1
            index += 2
        elif text.startswith("-/", index):
            depth -= 1
            index += 2
            if depth == 0:
                return index
        else:
            index += 1
    raise ValueError("unterminated block comment in command gap")


def split_gap_trivia(gap: str) -> tuple[str, str]:
    """Return (trailing-for-previous, leading-for-next) trivia."""

    if not trivia_only(gap):
        preview = gap[:120].replace("\n", "\\n")
        raise ValueError(f"non-comment token in command gap: {preview!r}")
    newline = gap.find("\n")
    first_line = gap if newline < 0 else gap[:newline]
    stripped = first_line.lstrip(" \t")
    if not stripped:
        return "", gap
    comment_start = len(first_line) - len(stripped)
    if stripped.startswith("--"):
        cut = len(gap) if newline < 0 else newline + 1
        return gap[:cut], gap[cut:]
    if stripped.startswith("/-"):
        comment_end = matching_block_comment_end(gap, comment_start)
        next_newline = gap.find("\n", comment_end)
        cut = len(gap) if next_newline < 0 else next_newline + 1
        return gap[:cut], gap[cut:]
    raise ValueError("same-line gap contains something other than a comment")


def attach_trivia(source: str, spans: list[CommandSpan]) -> list[CommandPayload]:
    leading = [""] * len(spans)
    trailing = [""] * len(spans)
    banner_gaps = 0
    cross_owner_banners = 0
    for index, (previous, current) in enumerate(zip(spans, spans[1:])):
        gap = source[previous.end_offset : current.start_offset]
        # The frozen body has 23 divider banners and one attached section
        # doc-comment.  Treat both as banner/comment gaps for attachment
        # accounting; 22 of the 24 cross a destination boundary.
        if "--" in gap or "/-" in gap:
            banner_gaps += 1
            if previous.owner != current.owner:
                cross_owner_banners += 1
        previous_trailing, current_leading = split_gap_trivia(gap)
        trailing[index] = previous_trailing
        leading[index + 1] = current_leading
    if banner_gaps != EXPECTED_BANNER_GAPS:
        raise ValueError(
            f"expected {EXPECTED_BANNER_GAPS} banner gaps, found {banner_gaps}"
        )
    if cross_owner_banners != EXPECTED_CROSS_OWNER_BANNER_GAPS:
        raise ValueError(
            f"expected {EXPECTED_CROSS_OWNER_BANNER_GAPS} cross-owner banner gaps, "
            f"found {cross_owner_banners}"
        )
    payloads = [
        CommandPayload(
            span,
            leading[index],
            source[span.start_offset : span.end_offset],
            trailing[index],
        )
        for index, span in enumerate(spans)
    ]
    reconstructed = "".join(payload.payload for payload in payloads)
    body = source[spans[0].start_offset : spans[-1].end_offset]
    if reconstructed != body:
        raise ValueError("command spans and attached trivia do not exactly cover body")
    digest = sha256_bytes(body.encode("utf-8"))
    if EXPECTED_COMMAND_BODY_SHA256 and digest != EXPECTED_COMMAND_BODY_SHA256:
        raise ValueError(
            f"command body digest differs: expected {EXPECTED_COMMAND_BODY_SHA256}, "
            f"found {digest}"
        )
    return payloads


def source_owner_set(manifest: dict[str, ManifestRow]) -> set[str]:
    source_destinations = {
        row.destination_module
        for row in manifest.values()
        if row.destination_module.startswith(SOURCE_PREFIX)
    }
    if RECURRENCES not in source_destinations:
        raise ValueError("frozen manifest no longer contains the Recurrences leaf")
    owners = source_destinations - {RECURRENCES}
    if len(owners) != EXPECTED_SOURCE_OWNERS:
        raise ValueError(
            f"expected {EXPECTED_SOURCE_OWNERS} source owners, found {len(owners)}"
        )
    return owners


def validate_source_partition(
    payloads: list[CommandPayload],
    manifest: dict[str, ManifestRow],
    source_owners: set[str],
) -> None:
    source_payloads = [p for p in payloads if p.span.owner in source_owners]
    if len(source_payloads) != EXPECTED_SOURCE_COMMANDS:
        raise ValueError(
            f"expected {EXPECTED_SOURCE_COMMANDS} source commands, "
            f"found {len(source_payloads)}"
        )
    overlay_count = sum(
        payload.span.logical_root in OVERLAY_ROOTS for payload in source_payloads
    )
    direct_count = len(source_payloads) - overlay_count
    moved_count = len(payloads) - len(source_payloads)
    command_partition = (moved_count, direct_count, overlay_count)
    expected_command_partition = (
        EXPECTED_ALREADY_MOVED_COMMANDS,
        EXPECTED_DIRECT_SOURCE_COMMANDS,
        EXPECTED_OVERLAY_COMMANDS,
    )
    if command_partition != expected_command_partition:
        raise ValueError(
            "command partition differs: expected moved/direct/overlay "
            f"{expected_command_partition}, found {command_partition}"
        )
    source_rows = [
        row for row in manifest.values() if row.destination_module in source_owners
    ]
    if len(source_rows) != EXPECTED_SOURCE_DECLARATIONS:
        raise ValueError(
            f"expected {EXPECTED_SOURCE_DECLARATIONS} source declarations, "
            f"found {len(source_rows)}"
        )
    visibilities = Counter(row.visibility for row in source_rows)
    expected = Counter(
        {
            "public": EXPECTED_SOURCE_PUBLIC_DECLARATIONS,
            "private": EXPECTED_SOURCE_PRIVATE_DECLARATIONS,
        }
    )
    if visibilities != expected:
        raise ValueError(
            f"source visibility partition differs: expected {expected}, "
            f"found {visibilities}"
        )
    private_owners = Counter(
        row.destination_module for row in source_rows if row.visibility == "private"
    )
    if private_owners != Counter(PRIVATE_SOURCE_COUNTS):
        raise ValueError(
            f"private source owners differ: expected {PRIVATE_SOURCE_COUNTS}, "
            f"found {dict(private_owners)}"
        )
    private_commands = Counter(
        payload.span.owner
        for payload in source_payloads
        for _ in range(payload.span.private_declarations)
    )
    if private_commands != Counter(PRIVATE_SOURCE_COUNTS):
        raise ValueError(
            "private declaration-to-command assignment differs: "
            f"{dict(private_commands)}"
        )
    source_roots = {payload.span.logical_root for payload in source_payloads}
    missing_overlays = sorted(set(OVERLAY_ROOTS) - source_roots)
    if missing_overlays:
        raise ValueError(f"overlay command roots are not source-owned: {missing_overlays}")


def resolve_project_target(
    source_owner: str,
    target_name: str,
    declarations: dict[str, Declaration],
    selected_actual: dict[str, ManifestRow],
) -> str | None:
    selected = selected_actual.get(target_name)
    if selected is not None:
        target_module = selected.destination_module
    else:
        declaration = declarations.get(target_name)
        if declaration is None:
            return None
        target_module = declaration.module
    if not target_module.startswith("NumStability.") or target_module == source_owner:
        return None
    return target_module


def tsv_import_witnesses(
    dependency_tsv: Path,
    declarations: dict[str, Declaration],
    selected_actual: dict[str, ManifestRow],
    source_owners: set[str],
) -> dict[tuple[str, str], ImportWitness]:
    result: dict[tuple[str, str], ImportWitness] = {}
    for edge in iter_dependency_edges(dependency_tsv):
        source_record = selected_actual.get(edge.source)
        if source_record is None or source_record.destination_module not in source_owners:
            continue
        source_owner = source_record.destination_module
        target = resolve_project_target(
            source_owner, edge.target, declarations, selected_actual
        )
        if target is None:
            continue
        key = (source_owner, target)
        candidate = ImportWitness(
            source_owner, target, edge.source, edge.target, edge.kind
        )
        previous = result.get(key)
        if previous is None or (
            candidate.source_name,
            candidate.target_name,
            candidate.detail,
        ) < (previous.source_name, previous.target_name, previous.detail):
            result[key] = candidate
    return result


def ilean_import_witnesses(
    ilean: dict[str, object],
    root_owner: dict[str, str],
    declarations: dict[str, Declaration],
    selected_actual: dict[str, ManifestRow],
    source_owners: set[str],
) -> dict[tuple[str, str], ImportWitness]:
    references = ilean["references"]
    assert isinstance(references, dict)
    result: dict[tuple[str, str], ImportWitness] = {}
    for encoded_target, value in references.items():
        try:
            decoded = json.loads(encoded_target)
        except json.JSONDecodeError as error:
            raise ValueError(f"malformed .ilean reference key {encoded_target!r}") from error
        if (
            not isinstance(decoded, dict)
            or set(decoded) != {"c"}
            or not isinstance(decoded["c"], dict)
            or not isinstance(decoded["c"].get("n"), str)
        ):
            raise ValueError(f"unexpected .ilean reference key {decoded!r}")
        target_name = decoded["c"]["n"]
        if not isinstance(value, dict) or not isinstance(value.get("usages"), list):
            raise ValueError(f"malformed .ilean usages for {target_name}")
        for usage in value["usages"]:
            if (
                not isinstance(usage, list)
                or len(usage) != 5
                or not isinstance(usage[4], str)
            ):
                raise ValueError(f"malformed .ilean usage for {target_name}")
            root = usage[4]
            source_owner = root_owner.get(root)
            if source_owner not in source_owners:
                continue
            target = resolve_project_target(
                source_owner, target_name, declarations, selected_actual
            )
            if target is None:
                continue
            key = (source_owner, target)
            detail = f"{usage[0]}:{usage[1]}-{usage[2]}:{usage[3]}"
            candidate = ImportWitness(
                source_owner, target, root, target_name, detail
            )
            previous = result.get(key)
            if previous is None or (
                candidate.source_name,
                candidate.target_name,
                candidate.detail,
            ) < (previous.source_name, previous.target_name, previous.detail):
                result[key] = candidate
    return result


def classify_import_pairs(
    witnesses: dict[tuple[str, str], ImportWitness], source_owners: set[str]
) -> dict[str, int]:
    counts = Counter()
    unexpected: list[tuple[str, str]] = []
    for source, target in witnesses:
        if target in source_owners:
            counts["source"] += 1
        elif target == RECURRENCES:
            counts["recurrences"] += 1
        elif target in SELECTED_REUSABLE_DESTINATIONS:
            counts["reusable"] += 1
        elif target in EXTERNAL_PROJECT_MODULES:
            counts["external"] += 1
        else:
            unexpected.append((source, target))
    expected = {
        "source": EXPECTED_DAG_EDGES,
        "recurrences": 1,
        "reusable": 204,
        "external": 85,
    }
    if dict(counts) != expected:
        raise ValueError(
            f"project import categories differ: expected {expected}, "
            f"found {dict(counts)}; unexpected={unexpected[:20]}"
        )
    if len(witnesses) != EXPECTED_PROJECT_IMPORT_PAIRS:
        raise ValueError(
            f"expected {EXPECTED_PROJECT_IMPORT_PAIRS} project import pairs, "
            f"found {len(witnesses)}"
        )
    targets = {target for _, target in witnesses}
    expected_non_source = (
        {RECURRENCES}
        | SELECTED_REUSABLE_DESTINATIONS
        | EXTERNAL_PROJECT_MODULES
    )
    missing_targets = sorted(expected_non_source - targets)
    if missing_targets:
        raise ValueError(
            "expected project dependency modules lack a witness: "
            + ", ".join(missing_targets)
        )
    return expected


def import_witness_bytes(
    tsv: dict[tuple[str, str], ImportWitness],
    ilean: dict[tuple[str, str], ImportWitness],
) -> bytes:
    lines = [
        "format\t1",
        "source_owner\timport_module\ttsv_source\ttsv_target\ttsv_kind\t"
        "ilean_root\tilean_target\tilean_span",
    ]
    for key in sorted(tsv):
        left = tsv[key]
        right = ilean[key]
        lines.append(
            "\t".join(
                (
                    left.source_owner,
                    left.target_module,
                    left.source_name,
                    left.target_name,
                    left.detail,
                    right.source_name,
                    right.target_name,
                    right.detail,
                )
            )
        )
    return ("\n".join(lines) + "\n").encode("utf-8")


def dependency_levels(
    witnesses: dict[tuple[str, str], ImportWitness],
    source_owners: set[str],
    *,
    expected_edges: int = EXPECTED_DAG_EDGES,
    expected_levels: int = EXPECTED_DAG_LEVELS,
) -> dict[str, int]:
    graph = {owner: set() for owner in source_owners}
    for source, target in witnesses:
        if target in source_owners:
            graph[source].add(target)
    edge_count = sum(len(targets) for targets in graph.values())
    if edge_count != expected_edges:
        raise ValueError(
            f"source-owner dependency edge count differs: expected "
            f"{expected_edges}, found {edge_count}"
        )

    levels: dict[str, int] = {}
    visiting: list[str] = []

    def visit(owner: str) -> int:
        if owner in levels:
            return levels[owner]
        if owner in visiting:
            cycle = visiting[visiting.index(owner) :] + [owner]
            raise ValueError("source-owner dependency cycle: " + " -> ".join(cycle))
        visiting.append(owner)
        dependencies = graph[owner]
        level = 0 if not dependencies else 1 + max(visit(dep) for dep in dependencies)
        visiting.pop()
        levels[owner] = level
        return level

    for owner in sorted(source_owners):
        visit(owner)
    level_count = max(levels.values(), default=-1) + 1
    if level_count != expected_levels:
        raise ValueError(
            f"expected {expected_levels} DAG levels, found {level_count}"
        )
    for source, dependencies in graph.items():
        for dependency in dependencies:
            if levels[dependency] >= levels[source]:
                raise ValueError(
                    f"dependency {source} -> {dependency} is not earlier in DAG order"
                )
    return levels


def validate_overlay_hazards(payloads: list[CommandPayload]) -> None:
    expected_calls = {
        "NumStability.block_lu_one_step_explicit": (2, 1),
        "NumStability.BlockLUFactSpec.firstRow_eq": (1, 0),
        "NumStability.BlockLUFactSpec.firstColumnBelow_eq_of_right_inverse": (0, 1),
    }
    by_root = {payload.span.logical_root: payload for payload in payloads}
    for root, (left_expected, right_expected) in expected_calls.items():
        payload = by_root.get(root)
        if payload is None:
            raise ValueError(f"missing overlay hazard command {root}")
        text = payload.command
        left = len(re.findall(r"\bsum_ite_eq_val\b", text))
        right = len(re.findall(r"\bsum_ite_eq_val_right\b", text))
        if (left, right) != (left_expected, right_expected):
            raise ValueError(
                f"{root}: expected private-helper calls {(left_expected, right_expected)}, "
                f"found {(left, right)}"
            )
        digest = sha256_bytes(text.encode("utf-8"))
        expected_hash = OVERLAY_ROOTS[root]
        if expected_hash and digest != expected_hash:
            raise ValueError(
                f"{root}: frozen command hash differs: expected {expected_hash}, "
                f"found {digest}"
            )


def ledger_bytes(
    payloads: list[CommandPayload], source_owners: set[str], levels: dict[str, int]
) -> bytes:
    lines = [
        "format\t1",
        "index\troot\tstart_line_0\tstart_char_0\tend_line_0\tend_char_0\t"
        "destination\tcategory\tdag_level\tsemantic_declarations\t"
        "private_declarations\tcommand_sha256\tleading_trivia_sha256\t"
        "trailing_trivia_sha256\tpayload_sha256",
    ]
    for index, payload in enumerate(payloads, 1):
        span = payload.span
        if span.logical_root in OVERLAY_ROOTS:
            category = "overlay-required"
        elif span.owner in source_owners:
            category = "source-generated"
        else:
            category = "already-moved"
        level = str(levels[span.owner]) if span.owner in levels else "-"
        lines.append(
            "\t".join(
                (
                    str(index),
                    span.logical_root,
                    str(span.start_line),
                    str(span.start_column),
                    str(span.end_line),
                    str(span.end_column),
                    span.owner,
                    category,
                    level,
                    str(len(span.declarations)),
                    str(span.private_declarations),
                    sha256_bytes(payload.command.encode("utf-8")),
                    sha256_bytes(payload.leading_trivia.encode("utf-8")),
                    sha256_bytes(payload.trailing_trivia.encode("utf-8")),
                    sha256_bytes(payload.payload.encode("utf-8")),
                )
            )
        )
    return ("\n".join(lines) + "\n").encode("utf-8")


def parse_overlay_manifest(path: Path) -> dict[str, str]:
    overlays: dict[str, str] = {}
    with path.open(encoding="utf-8", newline="") as stream:
        rows = csv.reader(stream, delimiter="\t")
        if next(rows, None) != ["format", "1"]:
            raise ValueError(f"{path}: overlay manifest must begin with format\\t1")
        for line_number, row in enumerate(rows, 2):
            if len(row) != 3 or not all(row):
                raise ValueError(f"{path}:{line_number}: malformed overlay row")
            root, raw_path, expected_hash = row
            if root in overlays:
                raise ValueError(f"{path}:{line_number}: duplicate overlay {root}")
            if not HEX_SHA256.fullmatch(expected_hash):
                raise ValueError(f"{path}:{line_number}: invalid SHA-256")
            overlay_path = Path(raw_path)
            if not overlay_path.is_absolute():
                overlay_path = path.parent / overlay_path
            payload = overlay_path.read_bytes()
            actual_hash = sha256_bytes(payload)
            if actual_hash != expected_hash.upper():
                raise ValueError(
                    f"{root}: overlay hash differs: expected {expected_hash.upper()}, "
                    f"found {actual_hash}"
                )
            try:
                text = payload.decode("utf-8")
            except UnicodeDecodeError as error:
                raise ValueError(f"{root}: overlay is not UTF-8") from error
            if "\r" in text or not text.endswith("\n") or text.endswith("\n\n"):
                raise ValueError(
                    f"{root}: overlay must use LF and end in exactly one newline"
                )
            command = text[:-1]
            if not command or command[0].isspace():
                raise ValueError(f"{root}: overlay must begin at column zero")
            short_root = root.removeprefix("NumStability.")
            if short_root not in command:
                raise ValueError(f"{root}: overlay does not contain its command name")
            if re.search(r"\bsum_ite_eq_val(?:_right)?\b", command):
                raise ValueError(f"{root}: overlay still calls a moved private helper")
            uncommented = strip_lean_comments(command)
            if re.search(r"(?m)^\s*(?:import|namespace|end)\b", uncommented):
                raise ValueError(f"{root}: overlay contains a module-level command")
            overlays[root] = command
    if set(overlays) != set(OVERLAY_ROOTS):
        raise ValueError(
            "overlay manifest roots differ: missing="
            f"{sorted(set(OVERLAY_ROOTS) - set(overlays))}; extra="
            f"{sorted(set(overlays) - set(OVERLAY_ROOTS))}"
        )
    return overlays


def strip_lean_comments(source: str) -> str:
    output: list[str] = []
    index = 0
    depth = 0
    while index < len(source):
        if depth:
            if source.startswith("/-", index):
                depth += 1
                output.extend("  ")
                index += 2
            elif source.startswith("-/", index):
                depth -= 1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if source[index] == "\n" else " ")
                index += 1
        elif source.startswith("--", index):
            newline = source.find("\n", index + 2)
            if newline < 0:
                output.extend(" " * (len(source) - index))
                break
            output.extend(" " * (newline - index))
            output.append("\n")
            index = newline + 1
        elif source.startswith("/-", index):
            depth = 1
            output.extend("  ")
            index += 2
        else:
            output.append(source[index])
            index += 1
    if depth:
        raise ValueError("unterminated Lean block comment")
    return "".join(output)


def direct_mathlib_imports(ilean: dict[str, object]) -> tuple[str, ...]:
    direct_imports = ilean["directImports"]
    assert isinstance(direct_imports, list)
    mathlib: list[str] = []
    for row in direct_imports:
        if (
            not isinstance(row, list)
            or len(row) != 4
            or not isinstance(row[0], str)
        ):
            raise ValueError("malformed .ilean direct import")
        if row[0].startswith("Mathlib."):
            mathlib.append(row[0])
    if set(mathlib) != EXPECTED_MATHLIB_IMPORTS or len(mathlib) != len(set(mathlib)):
        raise ValueError(
            "frozen Mathlib direct imports differ: expected "
            f"{sorted(EXPECTED_MATHLIB_IMPORTS)}, found {mathlib}"
        )
    return tuple(sorted(mathlib))


def owner_imports(
    witnesses: dict[tuple[str, str], ImportWitness], source_owners: set[str]
) -> dict[str, tuple[str, ...]]:
    result = {owner: set() for owner in source_owners}
    for source, target in witnesses:
        result[source].add(target)
    for owner, imports in result.items():
        forbidden = sorted(imports & FORBIDDEN_IMPORTS)
        if forbidden:
            raise ValueError(f"{owner}: forbidden ancestor/historical imports {forbidden}")
        if owner in imports:
            raise ValueError(f"{owner}: self import")
    return {owner: tuple(sorted(imports)) for owner, imports in result.items()}


def validate_collision_recipes(
    project_root: Path,
    baseline_repo: Path,
    owner_payloads: dict[str, list[CommandPayload]],
    manifest: dict[str, ManifestRow],
) -> None:
    for owner, recipe in COLLISIONS.items():
        relative = str(recipe["path"])
        base_blob = str(
            run_git(baseline_repo, "rev-parse", f"{BASE_REVISION}:{relative}")
        ).strip()
        if base_blob != recipe["blob"]:
            raise ValueError(
                f"{owner}: collision base blob differs: expected {recipe['blob']}, "
                f"found {base_blob}"
            )
        path = project_root / relative
        payload = path.read_bytes()
        if git_blob_sha1(payload) != recipe["blob"]:
            raise ValueError(f"{owner}: current collision file differs from pinned blob")
        digest = sha256_bytes(payload)
        if digest != recipe["sha256"]:
            raise ValueError(
                f"{owner}: collision SHA-256 differs: expected {recipe['sha256']}, "
                f"found {digest}"
            )
        text = payload.decode("utf-8")
        apis = tuple(recipe["apis"])
        for api in apis:
            if not re.search(rf"\b{re.escape(api)}\b", text):
                raise ValueError(f"{owner}: existing API {api} is missing")
        mapped = [
            row for row in manifest.values() if row.destination_module == owner
        ]
        if len(mapped) != recipe["mapped_declarations"]:
            raise ValueError(
                f"{owner}: expected {recipe['mapped_declarations']} mapped "
                f"declarations, found {len(mapped)}"
            )
        mapped_commands = owner_payloads.get(owner, [])
        if len(mapped_commands) != recipe["mapped_commands"]:
            raise ValueError(
                f"{owner}: expected {recipe['mapped_commands']} mapped commands, "
                f"found {len(mapped_commands)}"
            )


def leaf_payloads(
    payloads: list[CommandPayload],
    source_owners: set[str],
) -> dict[str, list[CommandPayload]]:
    result = {owner: [] for owner in source_owners}
    for payload in payloads:
        if payload.span.owner in source_owners:
            result[payload.span.owner].append(payload)
    empty = sorted(owner for owner, commands in result.items() if not commands)
    if empty:
        raise ValueError(f"source owners without commands: {empty}")
    return result


def rendered_owner_payload(
    commands: Iterable[CommandPayload], overlays: dict[str, str]
) -> str:
    chunks: list[str] = []
    for payload in commands:
        command = overlays.get(payload.span.logical_root, payload.command)
        chunks.append(payload.leading_trivia + command + payload.trailing_trivia)
    return "".join(chunks)


def module_draft(
    owner: str,
    commands: list[CommandPayload],
    imports: tuple[str, ...],
    mathlib_imports: tuple[str, ...],
    overlays: dict[str, str],
) -> bytes:
    import_lines = [f"import {module}" for module in sorted(mathlib_imports + imports)]
    title = owner.removeprefix("NumStability.")
    header = (
        "\n".join(import_lines)
        + "\n\n"
        + "/-!\n"
        + f"# {title}\n\n"
        + "Generated Phase 12 source-preparation draft.  Review before moving "
        + "into the repository.\n"
        + "-/\n\n"
        + "namespace NumStability\n\n"
        + "open scoped BigOperators\n"
        + "open scoped Matrix\n"
        + "open Filter Asymptotics\n"
    )
    body = rendered_owner_payload(commands, overlays)
    rendered = header + body
    if not rendered.endswith("\n"):
        rendered += "\n"
    rendered += "\nend NumStability\n"
    return rendered.encode("utf-8")


def collision_recipe_bytes(
    owner_payloads: dict[str, list[CommandPayload]],
    imports: dict[str, tuple[str, ...]],
    overlays: dict[str, str],
) -> bytes:
    lines = [
        "format\t1",
        "module\trepository_path\texisting_blob\texisting_sha256\t"
        "existing_api_count\tmapped_commands\tmapped_declarations\t"
        "payload_sha256\trequired_imports\tmerge_action",
    ]
    for owner in sorted(COLLISIONS):
        recipe = COLLISIONS[owner]
        payload = rendered_owner_payload(owner_payloads[owner], overlays)
        lines.append(
            "\t".join(
                (
                    owner,
                    str(recipe["path"]),
                    str(recipe["blob"]),
                    str(recipe["sha256"]),
                    str(len(tuple(recipe["apis"]))),
                    str(len(owner_payloads[owner])),
                    str(recipe["mapped_declarations"]),
                    sha256_bytes(payload.encode("utf-8")),
                    ",".join(imports[owner]),
                    "preserve pinned file and APIs; add required imports; insert "
                    "fragment immediately before final end NumStability",
                )
            )
        )
    return ("\n".join(lines) + "\n").encode("utf-8")


def ensure_external_new_path(
    path: Path, forbidden_roots: Iterable[Path], description: str
) -> Path:
    resolved = path.resolve()
    for forbidden_root in forbidden_roots:
        root = forbidden_root.resolve()
        try:
            resolved.relative_to(root)
        except ValueError:
            continue
        raise ValueError(f"{description} must be outside repository {root}")
    if resolved.exists():
        raise ValueError(f"{description} already exists: {resolved}")
    return resolved


def write_new(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("xb") as stream:
        stream.write(payload)


def write_output(
    output_dir: Path,
    project_root: Path,
    baseline_repo: Path,
    owner_payloads: dict[str, list[CommandPayload]],
    imports: dict[str, tuple[str, ...]],
    mathlib_imports: tuple[str, ...],
    levels: dict[str, int],
    overlays: dict[str, str],
    ledger: bytes,
    witnesses: bytes,
) -> None:
    output = ensure_external_new_path(
        output_dir, (project_root, baseline_repo), "output directory"
    )
    output.mkdir(parents=True, exist_ok=False)
    noncollisions = sorted(set(owner_payloads) - set(COLLISIONS))
    if len(noncollisions) != 66:
        raise ValueError(f"expected 66 non-collision drafts, found {len(noncollisions)}")
    manifest_lines = [
        "format\t1",
        "dag_level\tmodule\tpath\tcommands\tsemantic_declarations\t"
        "private_declarations\tproject_imports\tfile_sha256",
    ]
    for owner in sorted(noncollisions, key=lambda item: (levels[item], item)):
        commands = owner_payloads[owner]
        rendered = module_draft(
            owner, commands, imports[owner], mathlib_imports, overlays
        )
        relative = Path(*owner.split(".")).with_suffix(".lean")
        write_new(output / relative, rendered)
        manifest_lines.append(
            "\t".join(
                (
                    str(levels[owner]),
                    owner,
                    relative.as_posix(),
                    str(len(commands)),
                    str(sum(len(command.span.declarations) for command in commands)),
                    str(sum(command.span.private_declarations for command in commands)),
                    str(len(imports[owner])),
                    sha256_bytes(rendered),
                )
            )
        )
    write_new(
        output / "draft-manifest.tsv",
        ("\n".join(manifest_lines) + "\n").encode("utf-8"),
    )
    write_new(output / "command-ledger.tsv", ledger)
    write_new(output / "project-import-witnesses.tsv", witnesses)
    write_new(
        output / "collision-recipes.tsv",
        collision_recipe_bytes(owner_payloads, imports, overlays),
    )
    collision_dir = output / "collision-fragments"
    for owner in sorted(COLLISIONS):
        fragment = rendered_owner_payload(owner_payloads[owner], overlays)
        if not fragment.endswith("\n"):
            fragment += "\n"
        name = owner.rsplit(".", 1)[-1] + ".lean.fragment"
        write_new(collision_dir / name, fragment.encode("utf-8"))


def run_self_test() -> None:
    unicode_source = "theorem α : True := by\n  trivial\n\n/- nested /- x -/ -/\nβ\n"
    lines, starts = source_offsets(unicode_source)
    assert coordinate_offset(lines, starts, 0, 8) == 8
    assert unicode_source[coordinate_offset(lines, starts, 0, 8)] == "α"
    assert trivia_only("\n -- line\n /- nested /- ok -/ -/ \n")
    assert not trivia_only("\n theorem bad")
    trailing, leading = split_gap_trivia(" -- tail\n\n-- banner\n")
    assert trailing == " -- tail\n"
    assert leading == "\n-- banner\n"
    trailing, leading = split_gap_trivia("\n/-! next -/\n")
    assert trailing == ""
    assert leading == "\n/-! next -/\n"
    owner_a = "NumStability.Source.Higham.Chapter13.A"
    owner_b = "NumStability.Source.Higham.Chapter13.B"
    graph = {
        (owner_a, owner_b): ImportWitness(owner_a, owner_b, "a", "b", "body")
    }
    levels = dependency_levels(
        graph,
        {owner_a, owner_b},
        expected_edges=1,
        expected_levels=2,
    )
    assert levels == {owner_a: 1, owner_b: 0}
    cyclic = dict(graph)
    cyclic[(owner_b, owner_a)] = ImportWitness(
        owner_b, owner_a, "b", "a", "body"
    )
    try:
        dependency_levels(
            cyclic,
            {owner_a, owner_b},
            expected_edges=2,
            expected_levels=2,
        )
    except ValueError as error:
        assert "cycle" in str(error)
    else:
        raise AssertionError("dependency cycle was accepted")
    assert logical_name(
        "_private.NumStability.Algorithms.LU.BlockLU.7.NumStability.helper",
        BLOCKLU_MODULE,
    ) == "_private.<module>.NumStability.helper"
    with tempfile.TemporaryDirectory(prefix="phase12-source-prep-") as raw_temp:
        temp = Path(raw_temp)
        rows = ["format\t1"]
        for index, root in enumerate(sorted(OVERLAY_ROOTS), 1):
            overlay = temp / f"overlay-{index}.lean"
            command = (
                f"theorem {root.removeprefix('NumStability.')} : True := by\n"
                "  trivial\n"
            )
            overlay.write_text(command, encoding="utf-8", newline="\n")
            rows.append(f"{root}\t{overlay.name}\t{sha256_file(overlay)}")
        overlay_manifest = temp / "overlays.tsv"
        overlay_manifest.write_text(
            "\n".join(rows) + "\n", encoding="utf-8", newline="\n"
        )
        overlays = parse_overlay_manifest(overlay_manifest)
        assert set(overlays) == set(OVERLAY_ROOTS)
        first_overlay = temp / "overlay-1.lean"
        first_overlay.write_text(
            first_overlay.read_text(encoding="utf-8") + "-- changed\n",
            encoding="utf-8",
            newline="\n",
        )
        try:
            parse_overlay_manifest(overlay_manifest)
        except ValueError as error:
            assert "hash differs" in str(error)
        else:
            raise AssertionError("modified overlay passed its hash guard")
        try:
            ensure_external_new_path(temp / "inside", (temp,), "self-test path")
        except ValueError as error:
            assert "outside repository" in str(error)
        else:
            raise AssertionError("in-repository output path was accepted")
    print("Phase 12 source-preparation generator self-test passed")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--project-root", type=Path, default=Path("."))
    parser.add_argument("--baseline-repo", type=Path)
    parser.add_argument("--ilean", type=Path)
    parser.add_argument("--dependency-tsv", type=Path)
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--ledger", type=Path)
    parser.add_argument(
        "--import-witnesses",
        type=Path,
        help="optional new external path for the deterministic 505-pair witness TSV",
    )
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--overlay-manifest", type=Path)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument(
        "--print-derived-hashes",
        action="store_true",
        help="print deterministic aggregate hashes after all validation",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.self_test:
        run_self_test()
        return 0
    required = {
        "--baseline-repo": args.baseline_repo,
        "--ilean": args.ilean,
        "--dependency-tsv": args.dependency_tsv,
    }
    missing = [name for name, value in required.items() if value is None]
    if missing:
        raise ValueError("required arguments missing: " + ", ".join(missing))

    project_root = args.project_root.resolve()
    baseline_repo = args.baseline_repo.resolve()
    manifest_path = (
        args.manifest
        if args.manifest is not None
        else project_root
        / "docs/architecture/declaration-ownership/blocklu-phase12-v2.tsv"
    )
    _, source = read_frozen_source(baseline_repo)
    manifest = read_manifest(manifest_path.resolve())
    declarations = read_dependency_declarations(args.dependency_tsv.resolve())
    selected_actual = selected_actual_names(declarations, manifest)
    ilean = read_ilean(args.ilean.resolve())
    spans = assign_roots(ilean, manifest, source)
    payloads = attach_trivia(source, spans)
    owners = source_owner_set(manifest)
    validate_source_partition(payloads, manifest, owners)
    validate_overlay_hazards(payloads)

    root_owner = {payload.span.root: payload.span.owner for payload in payloads}
    tsv_witnesses = tsv_import_witnesses(
        args.dependency_tsv.resolve(), declarations, selected_actual, owners
    )
    ilean_witnesses = ilean_import_witnesses(
        ilean, root_owner, declarations, selected_actual, owners
    )
    if set(tsv_witnesses) != set(ilean_witnesses):
        missing_ilean = sorted(set(tsv_witnesses) - set(ilean_witnesses))
        extra_ilean = sorted(set(ilean_witnesses) - set(tsv_witnesses))
        raise ValueError(
            "TSV and .ilean project import pairs differ: "
            f"missing_from_ilean={missing_ilean[:20]}; "
            f"extra_in_ilean={extra_ilean[:20]}"
        )
    categories = classify_import_pairs(tsv_witnesses, owners)
    levels = dependency_levels(tsv_witnesses, owners)
    witnesses_payload = import_witness_bytes(tsv_witnesses, ilean_witnesses)
    witnesses_hash = sha256_bytes(witnesses_payload)
    if (
        EXPECTED_IMPORT_WITNESSES_SHA256
        and witnesses_hash != EXPECTED_IMPORT_WITNESSES_SHA256
    ):
        raise ValueError(
            "import witness digest differs: expected "
            f"{EXPECTED_IMPORT_WITNESSES_SHA256}, found {witnesses_hash}"
        )

    ledger = ledger_bytes(payloads, owners, levels)
    ledger_hash = sha256_bytes(ledger)
    if EXPECTED_LEDGER_SHA256 and ledger_hash != EXPECTED_LEDGER_SHA256:
        raise ValueError(
            f"ledger digest differs: expected {EXPECTED_LEDGER_SHA256}, "
            f"found {ledger_hash}"
        )
    owner_payloads = leaf_payloads(payloads, owners)
    imports = owner_imports(tsv_witnesses, owners)
    mathlib_imports = direct_mathlib_imports(ilean)
    validate_collision_recipes(
        project_root, baseline_repo, owner_payloads, manifest
    )

    overlays: dict[str, str] = {}
    if args.overlay_manifest is not None:
        overlays = parse_overlay_manifest(args.overlay_manifest.resolve())
    if args.output_dir is not None and not overlays:
        raise ValueError(
            "source draft generation requires --overlay-manifest for all three "
            "post-RecursiveFactorization commands"
        )
    if args.output_dir is not None and (
        args.ledger is not None or args.import_witnesses is not None
    ):
        raise ValueError(
            "--output-dir already contains the ledger and import witnesses; "
            "do not combine it with separate output paths"
        )
    if (
        args.ledger is not None
        and args.import_witnesses is not None
        and args.ledger.resolve() == args.import_witnesses.resolve()
    ):
        raise ValueError("--ledger and --import-witnesses must be different paths")
    ledger_path: Path | None = None
    witness_path: Path | None = None
    if args.ledger is not None:
        ledger_path = ensure_external_new_path(
            args.ledger, (project_root, baseline_repo), "ledger output"
        )
    if args.import_witnesses is not None:
        witness_path = ensure_external_new_path(
            args.import_witnesses,
            (project_root, baseline_repo),
            "import-witness output",
        )
    if ledger_path is not None:
        write_new(ledger_path, ledger)
    if witness_path is not None:
        write_new(witness_path, witnesses_payload)
    if args.output_dir is not None:
        write_output(
            args.output_dir,
            project_root,
            baseline_repo,
            owner_payloads,
            imports,
            mathlib_imports,
            levels,
            overlays,
            ledger,
            witnesses_payload,
        )

    command_body_hash = sha256_bytes(
        source[spans[0].start_offset : spans[-1].end_offset].encode("utf-8")
    )
    if args.print_derived_hashes:
        print(f"command_body_sha256={command_body_hash}")
        print(f"ledger_sha256={ledger_hash}")
        print(f"import_witnesses_sha256={witnesses_hash}")
        for root in sorted(OVERLAY_ROOTS):
            payload = next(p for p in payloads if p.span.logical_root == root)
            print(
                "overlay_frozen_command_sha256["
                f"{root}]={sha256_bytes(payload.command.encode('utf-8'))}"
            )
    print(
        "Phase 12 source preparation passed: "
        f"{len(payloads)} roots "
        f"({EXPECTED_ALREADY_MOVED_COMMANDS} moved/"
        f"{EXPECTED_DIRECT_SOURCE_COMMANDS} direct-source/"
        f"{EXPECTED_OVERLAY_COMMANDS} overlay), "
        f"{len(owners)} owners, {EXPECTED_SOURCE_COMMANDS} source commands, "
        f"{EXPECTED_SOURCE_DECLARATIONS} declarations "
        f"({EXPECTED_SOURCE_PUBLIC_DECLARATIONS} public/"
        f"{EXPECTED_SOURCE_PRIVATE_DECLARATIONS} private), "
        f"{EXPECTED_DAG_EDGES} source edges, {EXPECTED_DAG_LEVELS} DAG levels, "
        f"{len(tsv_witnesses)} project import pairs "
        f"({categories['source']} source, {categories['recurrences']} Recurrences, "
        f"{categories['reusable']} reusable, {categories['external']} external), "
        f"{EXPECTED_BANNER_GAPS} comment/banner gaps "
        f"({EXPECTED_CROSS_OWNER_BANNER_GAPS} cross-owner), "
        f"ledger {ledger_hash}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"source preparation failed: {error}", file=sys.stderr)
        raise SystemExit(1)
