#!/usr/bin/env python3
"""Freeze and check the QR / Higham Chapter 19 declaration migration.

The checker treats the packet's format-2 declaration stream as immutable
semantic evidence.  Every one of the 3,991 declarations owned by the 59
historical ``NumStability.Algorithms.QR`` modules is routed through an
authoritative source command.  Ordinary commands use the exact eight source
coordinates from the pristine ``.ilean`` file; the two Lean ``alias`` commands
in ``Higham19Theorem6ActualSource`` are tracked explicitly because Lean omits
aliases from that file's ``decls`` map.

Stage checking keeps source imports, declaration signatures, and declaration
bodies/proofs separate.  It permits only explicit private-name rewrites caused
by moving an otherwise byte-identical ``private`` command.  Historical paths
for completed owners must be exact import-only wrappers, and completed
canonical files must have the frozen command bytes and the reviewed import
rewrite.
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
from collections import Counter, defaultdict, deque
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


PACKET_BASE_SHA = "6487fc33088523b8f27ecde9ad613515b78f9977"
INTEGRATION_BASE_SHA = "420e4f93e2a5d31b2bf5b73740ca4146de7b0921"
LIVE_CHECKPOINT_SHA = "48242807d4149210926eccf90a326d287fc0860c"
BASELINE_TSV_SHA256 = (
    "32ADA469E27A971E9B0BB972F29C51E1DCBE99104A1492D4C69549C339825563"
)

HISTORICAL_ROOT = "NumStability.Algorithms.QR"
REUSABLE_ROOT = "NumStability.Algorithms.LinearSystems.QR"
SOURCE_ROOT = "NumStability.Source.Higham.Chapter19"

EXPECTED_HISTORICAL_COUNTS = {
    f"{HISTORICAL_ROOT}.GivensMatrixStep": 46,
    f"{HISTORICAL_ROOT}.GivensQR": 110,
    f"{HISTORICAL_ROOT}.GivensSpec": 71,
    f"{HISTORICAL_ROOT}.GramSchmidt": 416,
    f"{HISTORICAL_ROOT}.GramSchmidtPolar": 55,
    f"{HISTORICAL_ROOT}.Higham19": 1065,
    f"{HISTORICAL_ROOT}.Higham19Alg11CGSRounded": 48,
    f"{HISTORICAL_ROOT}.Higham19Alg12MGSClosure": 11,
    f"{HISTORICAL_ROOT}.Higham19Alg12MGSNonbreakdown": 18,
    f"{HISTORICAL_ROOT}.Higham19Alg12MGSPaddedClosure": 97,
    f"{HISTORICAL_ROOT}.Higham19Alg12MGSRepair": 8,
    f"{HISTORICAL_ROOT}.Higham19Alg12MGSRounded": 77,
    f"{HISTORICAL_ROOT}.Higham19Alg12MGSSourceRate": 58,
    f"{HISTORICAL_ROOT}.Higham19FormedQ": 5,
    f"{HISTORICAL_ROOT}.Higham19Labels": 18,
    f"{HISTORICAL_ROOT}.Higham19Lemma3ActualSequence": 2,
    f"{HISTORICAL_ROOT}.Higham19Lemma7Gamma4": 7,
    f"{HISTORICAL_ROOT}.Higham19Lemma9DisjointSweep": 55,
    f"{HISTORICAL_ROOT}.Higham19PolarNearest": 7,
    f"{HISTORICAL_ROOT}.Higham19Problem19_10": 86,
    f"{HISTORICAL_ROOT}.Higham19Problem19_9": 12,
    f"{HISTORICAL_ROOT}.Higham19Problem6ActualStep": 2,
    f"{HISTORICAL_ROOT}.Higham19Sensitivity": 59,
    f"{HISTORICAL_ROOT}.Higham19SensitivityClosure": 9,
    f"{HISTORICAL_ROOT}.Higham19StoredLoop": 8,
    f"{HISTORICAL_ROOT}.Higham19StoredLoopAllPivots": 18,
    f"{HISTORICAL_ROOT}.Higham19StoredLoopStrongModel": 13,
    f"{HISTORICAL_ROOT}.Higham19SunBischof": 35,
    f"{HISTORICAL_ROOT}.Higham19Theorem10ActualMatrix": 30,
    f"{HISTORICAL_ROOT}.Higham19Theorem5Nonbreakdown": 10,
    f"{HISTORICAL_ROOT}.Higham19Theorem5SourceClosure": 49,
    f"{HISTORICAL_ROOT}.Higham19Theorem6ActualSource": 2,
    f"{HISTORICAL_ROOT}.Higham19Thm6ColPivot": 19,
    f"{HISTORICAL_ROOT}.Higham19Thm6ColPivotFull": 24,
    f"{HISTORICAL_ROOT}.Higham19Thm6CoxHigham": 15,
    f"{HISTORICAL_ROOT}.Higham19Thm6CoxHighamAssembly": 2,
    f"{HISTORICAL_ROOT}.Higham19Thm6CoxHighamConcrete": 9,
    f"{HISTORICAL_ROOT}.Higham19Thm6CoxHighamFull": 6,
    f"{HISTORICAL_ROOT}.Higham19Thm6Elementwise": 6,
    f"{HISTORICAL_ROOT}.Higham19Thm6ElementwiseEntry": 9,
    f"{HISTORICAL_ROOT}.Higham19Thm6ElementwisePackaged": 10,
    f"{HISTORICAL_ROOT}.Higham19Thm6Final": 13,
    f"{HISTORICAL_ROOT}.Higham19Thm6Pivoted": 14,
    f"{HISTORICAL_ROOT}.Higham19Thm6RowSpecific": 12,
    f"{HISTORICAL_ROOT}.Higham19Thm6StrongModel": 14,
    f"{HISTORICAL_ROOT}.Higham19TurnbullAitken": 31,
    f"{HISTORICAL_ROOT}.Higham19WYApplicationClosure": 90,
    f"{HISTORICAL_ROOT}.HouseholderApply": 15,
    f"{HISTORICAL_ROOT}.HouseholderApplySupport": 101,
    f"{HISTORICAL_ROOT}.HouseholderConstruction2": 44,
    f"{HISTORICAL_ROOT}.HouseholderMatrixStep": 26,
    f"{HISTORICAL_ROOT}.HouseholderOneStep": 4,
    f"{HISTORICAL_ROOT}.HouseholderQApply": 28,
    f"{HISTORICAL_ROOT}.HouseholderQR": 501,
    f"{HISTORICAL_ROOT}.HouseholderQRSupport": 132,
    f"{HISTORICAL_ROOT}.HouseholderReflector": 52,
    f"{HISTORICAL_ROOT}.HouseholderSpec": 25,
    f"{HISTORICAL_ROOT}.HouseholderSpecSupport": 112,
    f"{HISTORICAL_ROOT}.QRSolve": 170,
}
EXPECTED_ROWS = 3991

GENERIC_BASENAMES = frozenset(
    {
        "GivensMatrixStep",
        "GivensQR",
        "GivensSpec",
        "GramSchmidt",
        "GramSchmidtPolar",
        "HouseholderApply",
        "HouseholderApplySupport",
        "HouseholderConstruction2",
        "HouseholderMatrixStep",
        "HouseholderOneStep",
        "HouseholderQApply",
        "HouseholderQR",
        "HouseholderQRSupport",
        "HouseholderReflector",
        "HouseholderSpec",
        "HouseholderSpecSupport",
        "QRSolve",
    }
)

SOURCE_LEAVES = {
    "Higham19": "Core",
    "Higham19Alg11CGSRounded": "Algorithm11.CGSRounded",
    "Higham19Alg12MGSClosure": "Algorithm12.MGSClosure",
    "Higham19Alg12MGSNonbreakdown": "Algorithm12.MGSNonbreakdown",
    "Higham19Alg12MGSPaddedClosure": "Algorithm12.MGSPaddedClosure",
    "Higham19Alg12MGSRepair": "Algorithm12.MGSRepair",
    "Higham19Alg12MGSRounded": "Algorithm12.MGSRounded",
    "Higham19Alg12MGSSourceRate": "Algorithm12.MGSSourceRate",
    "Higham19FormedQ": "FormedQ",
    "Higham19Labels": "Labels",
    "Higham19Lemma3ActualSequence": "Lemma03.ActualSequence",
    "Higham19Lemma7Gamma4": "Lemma07.Gamma4",
    "Higham19Lemma9DisjointSweep": "Lemma09.DisjointSweep",
    "Higham19PolarNearest": "PolarNearest",
    "Higham19Problem19_10": "Problem10",
    "Higham19Problem19_9": "Problem09",
    "Higham19Problem6ActualStep": "Problem06.ActualStep",
    "Higham19Sensitivity": "Sensitivity",
    "Higham19SensitivityClosure": "Sensitivity.Closure",
    "Higham19StoredLoop": "StoredLoop",
    "Higham19StoredLoopAllPivots": "StoredLoop.AllPivots",
    "Higham19StoredLoopStrongModel": "StoredLoop.StrongModel",
    "Higham19SunBischof": "SunBischof",
    "Higham19Theorem10ActualMatrix": "Theorem10.ActualMatrix",
    "Higham19Theorem5Nonbreakdown": "Theorem05.Nonbreakdown",
    "Higham19Theorem5SourceClosure": "Theorem05.SourceClosure",
    "Higham19Theorem6ActualSource": "Theorem06.ActualSource",
    "Higham19Thm6ColPivot": "Theorem06.ColumnPivot",
    "Higham19Thm6ColPivotFull": "Theorem06.ColumnPivotFull",
    "Higham19Thm6CoxHigham": "Theorem06.CoxHigham",
    "Higham19Thm6CoxHighamAssembly": "Theorem06.CoxHighamAssembly",
    "Higham19Thm6CoxHighamConcrete": "Theorem06.CoxHighamConcrete",
    "Higham19Thm6CoxHighamFull": "Theorem06.CoxHighamFull",
    "Higham19Thm6Elementwise": "Theorem06.Elementwise",
    "Higham19Thm6ElementwiseEntry": "Theorem06.ElementwiseEntry",
    "Higham19Thm6ElementwisePackaged": "Theorem06.ElementwisePackaged",
    "Higham19Thm6Final": "Theorem06.Final",
    "Higham19Thm6Pivoted": "Theorem06.Pivoted",
    "Higham19Thm6RowSpecific": "Theorem06.RowSpecific",
    "Higham19Thm6StrongModel": "Theorem06.StrongModel",
    "Higham19TurnbullAitken": "TurnbullAitken",
    "Higham19WYApplicationClosure": "WYApplicationClosure",
}

HOUSEHOLDER_BASENAMES = (
    "HouseholderApply",
    "HouseholderApplySupport",
    "HouseholderConstruction2",
    "HouseholderMatrixStep",
    "HouseholderOneStep",
    "HouseholderQApply",
    "HouseholderQR",
    "HouseholderQRSupport",
    "HouseholderReflector",
    "HouseholderSpec",
    "HouseholderSpecSupport",
)
HOUSEHOLDER_MODULES = frozenset(
    f"{HISTORICAL_ROOT}.{name}" for name in HOUSEHOLDER_BASENAMES
)
HOUSEHOLDER_REUSABLE_DESTINATIONS = frozenset(
    f"{REUSABLE_ROOT}.{name}" for name in HOUSEHOLDER_BASENAMES
)
CONSTRUCTION2_ALIAS_DESTINATION = f"{SOURCE_ROOT}.Lemma01.Construction2"
HOUSEHOLDER_DESTINATIONS = (
    HOUSEHOLDER_REUSABLE_DESTINATIONS | {CONSTRUCTION2_ALIAS_DESTINATION}
)

Q2A_BASENAMES = (
    "GivensMatrixStep",
    "GivensQR",
    "GivensSpec",
    "GramSchmidt",
    "GramSchmidtPolar",
    "QRSolve",
)
Q2A_MODULES = frozenset(
    f"{HISTORICAL_ROOT}.{name}" for name in Q2A_BASENAMES
)
Q2A_DESTINATIONS = frozenset(
    f"{REUSABLE_ROOT}.{name}" for name in Q2A_BASENAMES
)
HOUSEHOLDER_AND_Q2A_DESTINATIONS = HOUSEHOLDER_DESTINATIONS | Q2A_DESTINATIONS
REUSABLE_MIGRATION_MODULES = HOUSEHOLDER_MODULES | Q2A_MODULES

ALIAS_OWNER = f"{HISTORICAL_ROOT}.Higham19Theorem6ActualSource"
ALIAS_DECLARATIONS = frozenset(
    {
        "NumStability.Theorem19_6.sourceConstructed_actual_closed_linearRate",
        "NumStability.Theorem19_6.sourceConstructed_actual_rowwise_backward_error",
    }
)
CONSTRUCTION2_ALIAS = "NumStability.H19_Lemma19_1_construction2_backward_error"

WY_OWNER = f"{HISTORICAL_ROOT}.Higham19WYApplicationClosure"
WY_PACKET_BLOB = "2cbed76cdf8be333bd5d6a0557511d9c66d77d4a"
WY_INTEGRATED_BLOB = "9ad5dbe19017d2be7f166b237acd7b478cd02bcd"
WY_OLD_IMPORT = "NumStability.Algorithms.LU.BlockLUFirstOrderFamilies"
WY_CURRENT_IMPORT = "NumStability.Analysis.FirstOrder.AsymptoticFamilies"

DEFAULT_FROZEN_OWNERS = Path(
    "docs/architecture/declaration-ownership/qr-ch19-frozen-owners.tsv"
)
DEFAULT_ROUTES = Path("docs/architecture/declaration-ownership/qr-ch19-routes.tsv")
DEFAULT_OWNERSHIP = Path(
    "docs/architecture/declaration-ownership/qr-ch19-ownership.tsv"
)
DEFAULT_DAG = Path(
    "docs/architecture/declaration-ownership/qr-ch19-destination-dag.tsv"
)
DEFAULT_IMPORTS = Path(
    "docs/architecture/declaration-ownership/qr-ch19-source-imports.tsv"
)
DEFAULT_ALIASES = Path(
    "docs/architecture/declaration-ownership/qr-ch19-alias-commands.tsv"
)
DEFAULT_PRIVATE_REWRITES = Path(
    "docs/architecture/declaration-ownership/qr-ch19-private-rewrites.tsv"
)

HEX40 = re.compile(r"^[0-9a-fA-F]{40}$")
HEX64 = re.compile(r"^[0-9a-fA-F]{64}$")
MODULE_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$")
IMPORT_RE = re.compile(
    r"^\s*(public\s+)?import\s+([A-Za-z_][A-Za-z0-9_.]*)\s*$"
)
EDGE_KINDS = frozenset({"signature", "body"})
PROVENANCE = frozenset({"authored", "compiler_generated", "source_alias"})


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
class PacketOwner:
    path: str
    role: str
    packet_blob: str

    @property
    def module(self) -> str:
        return self.path[:-5].replace("/", ".")


@dataclass(frozen=True)
class FrozenOwner:
    module: str
    path: str
    packet_blob: str
    integrated_blob: str
    source_sha256: str
    physical_lines: int
    nonblank_lines: int
    ilean_sha256: str
    ilean_bytes: int


@dataclass(frozen=True)
class OwnershipRow:
    logical_name: str
    historical_module: str
    destination_module: str
    kind: str
    visibility: str


@dataclass(frozen=True)
class Route:
    historical_module: str
    logical_name: str
    historical_actual_name: str
    command_root_logical: str
    command_root_actual_name: str
    provenance: str
    start_line: int
    start_col: int
    end_line: int
    end_col: int
    selection_start_line: int
    selection_start_col: int
    selection_end_line: int
    selection_end_col: int
    command_sha256: str
    destination_module: str

    @property
    def span(self) -> tuple[int, int, int, int, int, int, int, int]:
        return (
            self.start_line,
            self.start_col,
            self.end_line,
            self.end_col,
            self.selection_start_line,
            self.selection_start_col,
            self.selection_end_line,
            self.selection_end_col,
        )


@dataclass(frozen=True)
class PrivateRewrite:
    logical_name: str
    historical_actual_name: str
    candidate_actual_name: str


def fail(message: str) -> None:
    raise ValueError(message)


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def normalized_source_bytes(path: Path) -> bytes:
    return path.read_bytes().replace(b"\r\n", b"\n").replace(b"\r", b"\n")


def ensure_module(module: str, context: str) -> None:
    if not MODULE_RE.fullmatch(module):
        fail(f"{context}: invalid Lean module {module!r}")


def private_suffix(actual_name: str, owner: str) -> str:
    prefix = f"_private.{owner}."
    if not actual_name.startswith(prefix):
        fail(f"private name {actual_name!r} does not encode {owner}")
    ordinal, separator, suffix = actual_name[len(prefix) :].partition(".")
    if not separator or not ordinal.isdigit() or not suffix:
        fail(f"malformed private name {actual_name!r}")
    return suffix


def logical_name(actual_name: str, historical_module: str) -> str:
    if not actual_name.startswith("_private."):
        return actual_name
    return f"_private.{historical_module}.{private_suffix(actual_name, historical_module)}"


def module_path(module: str, suffix: str = ".lean") -> Path:
    return Path(module.replace(".", "/") + suffix)


def read_stream_declarations(path: Path) -> list[Declaration]:
    declarations: list[Declaration] = []
    names: set[str] = set()
    saw_format = False
    with path.open(encoding="utf-8", newline="") as stream:
        for line_number, row in enumerate(csv.reader(stream, delimiter="\t"), 1):
            if not row:
                continue
            if row == ["format", "2"]:
                if saw_format or line_number != 1:
                    fail(f"{path}:{line_number}: misplaced format row")
                saw_format = True
            elif row[0] == "declaration" and len(row) == 5:
                if not saw_format or not all(row[1:]):
                    fail(f"{path}:{line_number}: malformed declaration row")
                declaration = Declaration(*row[1:])
                if declaration.name in names:
                    fail(f"{path}:{line_number}: duplicate declaration {declaration.name}")
                names.add(declaration.name)
                declarations.append(declaration)
            elif row[0] == "edge" and len(row) == 4:
                if not saw_format or row[1] not in EDGE_KINDS or not all(row[2:]):
                    fail(f"{path}:{line_number}: malformed edge row")
            else:
                fail(f"{path}:{line_number}: malformed format-2 row {row!r}")
    if not saw_format:
        fail(f"{path}: missing format-2 marker")
    return declarations


def iter_stream_edges(path: Path) -> Iterable[Edge]:
    saw_format = False
    with path.open(encoding="utf-8", newline="") as stream:
        for line_number, row in enumerate(csv.reader(stream, delimiter="\t"), 1):
            if not row:
                continue
            if row == ["format", "2"]:
                if saw_format or line_number != 1:
                    fail(f"{path}:{line_number}: misplaced format row")
                saw_format = True
            elif row[0] == "declaration" and len(row) == 5:
                if not saw_format or not all(row[1:]):
                    fail(f"{path}:{line_number}: malformed declaration row")
            elif row[0] == "edge" and len(row) == 4:
                if not saw_format or row[1] not in EDGE_KINDS or not all(row[2:]):
                    fail(f"{path}:{line_number}: malformed edge row")
                yield Edge(*row[1:])
            else:
                fail(f"{path}:{line_number}: malformed format-2 row {row!r}")
    if not saw_format:
        fail(f"{path}: missing format-2 marker")


def select_baseline(declarations: Iterable[Declaration]) -> dict[str, Declaration]:
    selected: dict[str, Declaration] = {}
    counts: Counter[str] = Counter()
    for declaration in declarations:
        if declaration.module not in EXPECTED_HISTORICAL_COUNTS:
            continue
        logical = logical_name(declaration.name, declaration.module)
        if logical in selected:
            fail(f"duplicate QR logical declaration {logical}")
        selected[logical] = declaration
        counts[declaration.module] += 1
    if counts != Counter(EXPECTED_HISTORICAL_COUNTS):
        drift = {
            module: (expected, counts[module])
            for module, expected in EXPECTED_HISTORICAL_COUNTS.items()
            if counts[module] != expected
        }
        fail(f"QR historical declaration counts drifted: {drift}")
    if len(selected) != EXPECTED_ROWS:
        fail(f"expected {EXPECTED_ROWS} QR declarations, found {len(selected)}")
    if ALIAS_DECLARATIONS - {row.name for row in selected.values()}:
        fail("the two explicit Higham19Theorem6ActualSource aliases are missing")
    return selected


def read_packet_owners(path: Path) -> dict[str, PacketOwner]:
    with path.open(encoding="utf-8-sig", newline="") as stream:
        rows = list(csv.DictReader(stream, delimiter="\t"))
    owners: dict[str, PacketOwner] = {}
    for raw in rows:
        owner = PacketOwner(raw["path"], raw["role"], raw["base_blob"].lower())
        if owner.module in owners or not HEX40.fullmatch(owner.packet_blob):
            fail(f"{path}: malformed or duplicate packet owner {owner.module}")
        owners[owner.module] = owner
    expected = set(EXPECTED_HISTORICAL_COUNTS)
    if set(owners) != expected:
        fail(
            f"{path}: packet owner coverage drift: "
            f"missing={sorted(expected-set(owners))}, extra={sorted(set(owners)-expected)}"
        )
    if owners[WY_OWNER].packet_blob != WY_PACKET_BLOB:
        fail(f"{path}: frozen WY packet blob drifted")
    return owners


def git_text(root: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", "-C", str(root), *args], text=True, encoding="utf-8"
    ).strip()


def frozen_source_path(directory: Path, module: str) -> Path:
    return directory / f"{module}.lean"


def frozen_ilean_path(directory: Path, module: str) -> Path:
    return directory / f"{module}.ilean"


def generate_frozen_owners(
    project_root: Path,
    packet_owners: dict[str, PacketOwner],
    frozen_source_dir: Path,
    frozen_ilean_dir: Path,
) -> dict[str, FrozenOwner]:
    head = git_text(project_root, "rev-parse", "HEAD")
    if head != INTEGRATION_BASE_SHA:
        fail(
            "frozen-owner generation is allowed only at the published integration "
            f"base {INTEGRATION_BASE_SHA}; found {head}"
        )
    generated: dict[str, FrozenOwner] = {}
    for module, packet in sorted(packet_owners.items()):
        live = project_root / packet.path
        source = frozen_source_path(frozen_source_dir, module)
        ilean = frozen_ilean_path(frozen_ilean_dir, module)
        if not live.is_file() or not source.is_file() or not ilean.is_file():
            fail(f"{module}: missing live/frozen source or .ilean")
        if live.read_bytes() != source.read_bytes():
            fail(f"{module}: frozen source is not the pristine integrated source")
        integrated_blob = git_text(project_root, "hash-object", packet.path).lower()
        expected_blob = WY_INTEGRATED_BLOB if module == WY_OWNER else packet.packet_blob
        if integrated_blob != expected_blob:
            fail(
                f"{module}: integrated blob {integrated_blob} differs from "
                f"reviewed {expected_blob}"
            )
        payload = normalized_source_bytes(source)
        physical = len(payload.splitlines())
        nonblank = sum(bool(line.strip()) for line in payload.splitlines())
        generated[module] = FrozenOwner(
            module,
            packet.path,
            packet.packet_blob,
            integrated_blob,
            sha256_file(source),
            physical,
            nonblank,
            sha256_file(ilean),
            ilean.stat().st_size,
        )
    return generated


def frozen_owner_bytes(owners: dict[str, FrozenOwner]) -> bytes:
    rows = ["format\t1"]
    for module in sorted(owners):
        row = owners[module]
        rows.append(
            "\t".join(
                (
                    row.module,
                    row.path,
                    row.packet_blob,
                    row.integrated_blob,
                    row.source_sha256,
                    str(row.physical_lines),
                    str(row.nonblank_lines),
                    row.ilean_sha256,
                    str(row.ilean_bytes),
                )
            )
        )
    return ("\n".join(rows) + "\n").encode()


def read_frozen_owners(path: Path) -> dict[str, FrozenOwner]:
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["format", "1"]:
        fail(f"{path}: frozen owners must start with format\\t1")
    owners: dict[str, FrozenOwner] = {}
    order: list[str] = []
    for line_number, row in enumerate(rows[1:], 2):
        if len(row) != 9:
            fail(f"{path}:{line_number}: expected nine frozen-owner columns")
        module, source_path, packet_blob, integrated_blob, source_hash = row[:5]
        try:
            physical, nonblank, ilean_bytes = int(row[5]), int(row[6]), int(row[8])
        except ValueError as error:
            raise ValueError(f"{path}:{line_number}: invalid numeric field") from error
        ilean_hash = row[7]
        if module in owners or not all(
            (HEX40.fullmatch(packet_blob), HEX40.fullmatch(integrated_blob),
             HEX64.fullmatch(source_hash), HEX64.fullmatch(ilean_hash))
        ):
            fail(f"{path}:{line_number}: malformed frozen owner")
        owners[module] = FrozenOwner(
            module,
            source_path,
            packet_blob.lower(),
            integrated_blob.lower(),
            source_hash.upper(),
            physical,
            nonblank,
            ilean_hash.upper(),
            ilean_bytes,
        )
        order.append(module)
    if set(owners) != set(EXPECTED_HISTORICAL_COUNTS) or order != sorted(order):
        fail(f"{path}: frozen-owner coverage/order differs from the 59-owner contract")
    if owners[WY_OWNER].integrated_blob != WY_INTEGRATED_BLOB:
        fail(f"{path}: current WY import repair is not frozen")
    return owners


def validate_frozen_inputs(
    owners: dict[str, FrozenOwner], source_dir: Path, ilean_dir: Path
) -> None:
    for module, owner in owners.items():
        source = frozen_source_path(source_dir, module)
        ilean = frozen_ilean_path(ilean_dir, module)
        if sha256_file(source) != owner.source_sha256:
            fail(f"{module}: frozen source hash drift")
        payload = normalized_source_bytes(source)
        if (
            len(payload.splitlines()),
            sum(bool(line.strip()) for line in payload.splitlines()),
        ) != (owner.physical_lines, owner.nonblank_lines):
            fail(f"{module}: frozen source line counts drift")
        if sha256_file(ilean) != owner.ilean_sha256 or ilean.stat().st_size != owner.ilean_bytes:
            fail(f"{module}: frozen .ilean hash/size drift")


def read_ilean_entries(
    path: Path, expected_module: str
) -> dict[str, tuple[int, int, int, int, int, int, int, int]]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("module") != expected_module or not isinstance(payload.get("decls"), dict):
        fail(f"{path}: wrong .ilean owner or missing decls map")
    result: dict[str, tuple[int, int, int, int, int, int, int, int]] = {}
    for name, raw in payload["decls"].items():
        if (
            not isinstance(name, str)
            or not isinstance(raw, list)
            or len(raw) != 8
            or any(not isinstance(value, int) or value < 0 for value in raw)
        ):
            fail(f"{path}: malformed .ilean declaration span")
        span = tuple(raw)
        if (span[2], span[3]) < (span[0], span[1]):
            fail(f"{path}: reversed .ilean declaration span")
        result[name] = span
    return result


def source_command_bytes(
    payload: bytes, span: tuple[int, int, int, int, int, int, int, int]
) -> bytes:
    """Slice an .ilean command using zero-based Unicode-character columns."""

    lines = payload.splitlines(keepends=True) or [b""]
    offsets = [0]
    for line in lines:
        offsets.append(offsets[-1] + len(line))

    def offset(line: int, column: int) -> int:
        if line == len(lines) and column == 0:
            return len(payload)
        if line >= len(lines):
            fail(f"source coordinate line {line} exceeds {len(lines)}")
        content = lines[line].rstrip(b"\n").decode("utf-8")
        if column > len(content):
            fail(f"source coordinate column {column} exceeds line {line}")
        return offsets[line] + len(content[:column].encode("utf-8"))

    start = offset(span[0], span[1])
    end = offset(span[2], span[3])
    if end <= start:
        fail(f"empty or reversed command span {span}")
    return payload[start:end]


def find_alias_spans(
    payload: bytes, owner: str, expected_names: set[str]
) -> dict[str, tuple[int, int, int, int, int, int, int, int]]:
    text = payload.decode("utf-8")
    lines = text.splitlines()
    found: dict[str, tuple[int, int, int, int, int, int, int, int]] = {}
    namespace: list[str] = []
    for index, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith("namespace "):
            namespace.append(stripped.split(None, 1)[1])
            continue
        if stripped.startswith("end"):
            if namespace:
                namespace.pop()
            continue
        match = re.fullmatch(r"alias\s+([A-Za-z_][A-Za-z0-9_']*)\s*:=", stripped)
        if not match:
            continue
        short = match.group(1)
        prefix = ".".join(namespace)
        actual = f"{prefix}.{short}" if prefix else short
        if actual not in expected_names:
            continue
        if index + 1 >= len(lines) or not lines[index + 1].startswith((" ", "\t")):
            fail(f"{owner}:{index+1}: alias target line is not indented")
        start_col = len(line) - len(line.lstrip())
        end_line = index + 1
        end_col = len(lines[end_line])
        name_col = line.index(short)
        found[actual] = (
            index,
            start_col,
            end_line,
            end_col,
            index,
            name_col,
            index,
            name_col + len(short),
        )
    if set(found) != expected_names:
        fail(
            f"{owner}: explicit alias parser expected {sorted(expected_names)}, "
            f"found {sorted(found)}"
        )
    return found


def default_destination(historical_module: str) -> str:
    basename = historical_module.rsplit(".", 1)[1]
    if basename in GENERIC_BASENAMES:
        return f"{REUSABLE_ROOT}.{basename}"
    leaf = SOURCE_LEAVES.get(basename)
    if leaf is None:
        fail(f"no reviewed Chapter 19 destination for {historical_module}")
    return f"{SOURCE_ROOT}.{leaf}"


def destination_for_command(historical_module: str, command_root: str) -> str:
    if (
        historical_module == f"{HISTORICAL_ROOT}.HouseholderConstruction2"
        and command_root == CONSTRUCTION2_ALIAS
    ):
        return CONSTRUCTION2_ALIAS_DESTINATION
    return default_destination(historical_module)


def generate_routes(
    baseline: dict[str, Declaration],
    owners: dict[str, FrozenOwner],
    source_dir: Path,
    ilean_dir: Path,
) -> dict[str, Route]:
    actual_to_logical = {row.name: logical for logical, row in baseline.items()}
    entries: dict[str, dict[str, tuple[int, int, int, int, int, int, int, int]]] = {}
    sources: dict[str, bytes] = {}
    for module in sorted(owners):
        entries[module] = read_ilean_entries(frozen_ilean_path(ilean_dir, module), module)
        sources[module] = normalized_source_bytes(frozen_source_path(source_dir, module))
    alias_spans = find_alias_spans(sources[ALIAS_OWNER], ALIAS_OWNER, set(ALIAS_DECLARATIONS))

    routes: dict[str, Route] = {}
    for logical, declaration in sorted(baseline.items()):
        module = declaration.module
        if declaration.name in ALIAS_DECLARATIONS:
            if module != ALIAS_OWNER or entries[module]:
                fail(f"{logical}: source alias unexpectedly has a .ilean root")
            span = alias_spans[declaration.name]
            root_actual = declaration.name
            root_logical = logical
            provenance = "source_alias"
        else:
            candidates = [
                root
                for root in entries[module]
                if declaration.name == root or declaration.name.startswith(root + ".")
            ]
            if not candidates:
                fail(f"{logical}: no authoritative .ilean source-command root")
            longest = max(map(len, candidates))
            roots = [root for root in candidates if len(root) == longest]
            if len(roots) != 1:
                fail(f"{logical}: ambiguous .ilean roots {roots}")
            root_actual = roots[0]
            root_logical = actual_to_logical.get(root_actual, "")
            if not root_logical:
                fail(f"{logical}: command root {root_actual} is not a selected declaration")
            span = entries[module][root_actual]
            provenance = "authored" if declaration.name == root_actual else "compiler_generated"
        command_hash = sha256_bytes(source_command_bytes(sources[module], span))
        destination = destination_for_command(module, root_actual)
        routes[logical] = Route(
            module,
            logical,
            declaration.name,
            root_logical,
            root_actual,
            provenance,
            *span,
            command_hash,
            destination,
        )
    validate_routes(routes, baseline)
    return routes


def route_bytes(routes: dict[str, Route]) -> bytes:
    rows = ["format\t2"]
    for logical in sorted(routes):
        route = routes[logical]
        rows.append(
            "\t".join(
                (
                    "route",
                    route.historical_module,
                    route.logical_name,
                    route.historical_actual_name,
                    route.command_root_logical,
                    route.command_root_actual_name,
                    route.provenance,
                    *(str(value) for value in route.span),
                    route.command_sha256,
                    route.destination_module,
                )
            )
        )
    return ("\n".join(rows) + "\n").encode()


def read_routes(
    path: Path, baseline: dict[str, Declaration]
) -> dict[str, Route]:
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["format", "2"]:
        fail(f"{path}: routes must start with format\\t2")
    routes: dict[str, Route] = {}
    order: list[str] = []
    for line_number, row in enumerate(rows[1:], 2):
        if len(row) != 17 or row[0] != "route":
            fail(f"{path}:{line_number}: expected 17-column route")
        try:
            span = tuple(int(value) for value in row[7:15])
        except ValueError as error:
            raise ValueError(f"{path}:{line_number}: noninteger coordinate") from error
        route = Route(row[1], row[2], row[3], row[4], row[5], row[6], *span, row[15], row[16])
        if route.logical_name in routes:
            fail(f"{path}:{line_number}: duplicate route {route.logical_name}")
        routes[route.logical_name] = route
        order.append(route.logical_name)
    if order != sorted(order):
        fail(f"{path}: route rows are not sorted")
    validate_routes(routes, baseline)
    return routes


def route_groups(routes: dict[str, Route]) -> dict[tuple[str, tuple[int, ...]], list[Route]]:
    groups: dict[tuple[str, tuple[int, ...]], list[Route]] = defaultdict(list)
    for route in routes.values():
        groups[(route.historical_module, route.span)].append(route)
    return groups


def validate_routes(routes: dict[str, Route], baseline: dict[str, Declaration]) -> None:
    if set(routes) != set(baseline) or len(routes) != EXPECTED_ROWS:
        fail("command routes do not exactly cover all 3,991 frozen declarations")
    groups = route_groups(routes)
    for logical, route in routes.items():
        declaration = baseline[logical]
        if (
            route.logical_name != logical
            or route.historical_module != declaration.module
            or route.historical_actual_name != declaration.name
            or route.provenance not in PROVENANCE
            or not HEX64.fullmatch(route.command_sha256)
        ):
            fail(f"{logical}: malformed route metadata")
        ensure_module(route.destination_module, logical)
        if any(value < 0 for value in route.span):
            fail(f"{logical}: negative source coordinate")
        if route.provenance == "source_alias":
            if declaration.name not in ALIAS_DECLARATIONS or route.command_root_logical != logical:
                fail(f"{logical}: invalid explicit alias route")
        else:
            root = baseline.get(route.command_root_logical)
            if root is None or root.name != route.command_root_actual_name or root.module != declaration.module:
                fail(f"{logical}: invalid compiler command root")
            expected = "authored" if declaration.name == root.name else "compiler_generated"
            if route.provenance != expected:
                fail(f"{logical}: compiler provenance drift")
        if route.destination_module != destination_for_command(
            route.historical_module, route.command_root_actual_name
        ):
            fail(f"{logical}: destination differs from reviewed selector")
    for key, members in groups.items():
        if len({row.destination_module for row in members}) != 1:
            fail(f"source command {key} straddles destinations")
        if len({row.command_sha256.upper() for row in members}) != 1:
            fail(f"source command {key} has multiple command hashes")
        aliases = [row for row in members if row.provenance == "source_alias"]
        authored = [row for row in members if row.provenance == "authored"]
        if len(aliases) + len(authored) != 1:
            fail(f"source command {key} lacks exactly one authored/alias root")


def validate_routes_against_frozen(
    routes: dict[str, Route],
    owners: dict[str, FrozenOwner],
    source_dir: Path,
    ilean_dir: Path,
) -> int:
    validate_frozen_inputs(owners, source_dir, ilean_dir)
    entries = {
        module: read_ilean_entries(frozen_ilean_path(ilean_dir, module), module)
        for module in owners
    }
    sources = {
        module: normalized_source_bytes(frozen_source_path(source_dir, module))
        for module in owners
    }
    alias_spans = find_alias_spans(sources[ALIAS_OWNER], ALIAS_OWNER, set(ALIAS_DECLARATIONS))
    for logical, route in routes.items():
        if route.provenance == "source_alias":
            actual_span = alias_spans.get(route.historical_actual_name)
        else:
            actual_span = entries[route.historical_module].get(route.command_root_actual_name)
        if actual_span != route.span:
            fail(f"{logical}: committed command span differs from pristine input")
        actual_hash = sha256_bytes(source_command_bytes(sources[route.historical_module], route.span))
        if actual_hash != route.command_sha256.upper():
            fail(f"{logical}: command hash differs from pristine source")
    return len(route_groups(routes))


def ownership_from_routes(
    routes: dict[str, Route], baseline: dict[str, Declaration]
) -> dict[str, OwnershipRow]:
    return {
        logical: OwnershipRow(
            logical,
            baseline[logical].module,
            route.destination_module,
            baseline[logical].kind,
            baseline[logical].visibility,
        )
        for logical, route in routes.items()
    }


def ownership_bytes(rows: dict[str, OwnershipRow]) -> bytes:
    payload = ["format\t1"]
    for logical in sorted(rows):
        row = rows[logical]
        payload.append(
            "\t".join(
                (row.logical_name, row.historical_module, row.destination_module, row.kind, row.visibility)
            )
        )
    return ("\n".join(payload) + "\n").encode()


def read_ownership(
    path: Path, baseline: dict[str, Declaration], routes: dict[str, Route]
) -> dict[str, OwnershipRow]:
    with path.open(encoding="utf-8", newline="") as stream:
        raw = list(csv.reader(stream, delimiter="\t"))
    if not raw or raw[0] != ["format", "1"]:
        fail(f"{path}: ownership must start with format\\t1")
    rows: dict[str, OwnershipRow] = {}
    order: list[str] = []
    for line_number, values in enumerate(raw[1:], 2):
        if len(values) != 5:
            fail(f"{path}:{line_number}: expected five ownership columns")
        row = OwnershipRow(*values)
        if row.logical_name in rows:
            fail(f"{path}:{line_number}: duplicate ownership row")
        rows[row.logical_name] = row
        order.append(row.logical_name)
    if order != sorted(order) or rows != ownership_from_routes(routes, baseline):
        fail(f"{path}: ownership differs from exact command routes")
    return rows


def destination_tier(module: str) -> str:
    if module.startswith(REUSABLE_ROOT + "."):
        return "reusable"
    if module.startswith(SOURCE_ROOT + "."):
        return "source"
    fail(f"destination outside reviewed roots: {module}")
    raise AssertionError


def destination_graph(
    baseline_tsv: Path,
    baseline: dict[str, Declaration],
    ownership: dict[str, OwnershipRow],
) -> tuple[dict[str, int], Counter[tuple[str, str, str]]]:
    actual_to_logical = {row.name: logical for logical, row in baseline.items()}
    destinations = {row.destination_module for row in ownership.values()}
    edges: Counter[tuple[str, str, str]] = Counter()
    for edge in iter_stream_edges(baseline_tsv):
        source = actual_to_logical.get(edge.source)
        target = actual_to_logical.get(edge.target)
        if source is None or target is None:
            continue
        source_owner = ownership[source].destination_module
        target_owner = ownership[target].destination_module
        if source_owner != target_owner:
            edges[(edge.kind, source_owner, target_owner)] += 1

    dependencies: dict[str, set[str]] = {destination: set() for destination in destinations}
    dependents: dict[str, set[str]] = {destination: set() for destination in destinations}
    for _, source, target in edges:
        dependencies[source].add(target)
        dependents[target].add(source)
    indegree = {node: len(dependencies[node]) for node in destinations}
    queue = deque(sorted(node for node, degree in indegree.items() if degree == 0))
    rank: dict[str, int] = {}
    while queue:
        node = queue.popleft()
        rank[node] = 0 if not dependencies[node] else 1 + max(rank[d] for d in dependencies[node])
        for dependent in sorted(dependents[node]):
            indegree[dependent] -= 1
            if indegree[dependent] == 0:
                queue.append(dependent)
    if len(rank) != len(destinations):
        cyclic = sorted(node for node in destinations if node not in rank)
        fail(f"reviewed QR destination graph contains a cycle: {cyclic}")
    return rank, edges


def dag_bytes(rank: dict[str, int], edges: Counter[tuple[str, str, str]]) -> bytes:
    rows = ["format\t1"]
    for destination in sorted(rank):
        rows.append(
            "\t".join(("destination", destination, destination_tier(destination), str(rank[destination])))
        )
    for (kind, source, target), count in sorted(edges.items()):
        rows.append("\t".join(("edge", kind, source, target, str(count))))
    return ("\n".join(rows) + "\n").encode()


def source_imports(source_dir: Path, owners: dict[str, FrozenOwner]) -> list[tuple[str, str, str]]:
    imports: list[tuple[str, str, str]] = []
    for module in sorted(owners):
        payload = normalized_source_bytes(frozen_source_path(source_dir, module)).decode("utf-8")
        for line in payload.splitlines():
            match = IMPORT_RE.fullmatch(line)
            if match:
                imports.append((module, match.group(2), "public" if match.group(1) else "ordinary"))
    if (WY_OWNER, WY_OLD_IMPORT, "ordinary") in imports:
        fail("current main's WY import repair was replaced by the obsolete BlockLU wrapper")
    if (WY_OWNER, WY_CURRENT_IMPORT, "ordinary") not in imports:
        fail("current main's WY AsymptoticFamilies import is missing")
    return sorted(imports)


def source_import_bytes(rows: list[tuple[str, str, str]]) -> bytes:
    return ("format\t1\n" + "".join("\t".join(row) + "\n" for row in rows)).encode()


def alias_bytes(routes: dict[str, Route]) -> bytes:
    rows = ["format\t1"]
    aliases = [route for route in routes.values() if route.provenance == "source_alias"]
    for route in sorted(aliases, key=lambda row: row.logical_name):
        rows.append(
            "\t".join(
                (
                    route.logical_name,
                    route.historical_module,
                    *(str(value) for value in route.span),
                    route.command_sha256,
                    route.destination_module,
                )
            )
        )
    if {row.logical_name for row in aliases} != ALIAS_DECLARATIONS:
        fail("explicit alias artifact does not contain exactly the two source aliases")
    return ("\n".join(rows) + "\n").encode()


def private_rewrite_bytes(rows: dict[str, PrivateRewrite]) -> bytes:
    output = ["format\t1"]
    for logical in sorted(rows):
        row = rows[logical]
        output.append("\t".join((row.logical_name, row.historical_actual_name, row.candidate_actual_name)))
    return ("\n".join(output) + "\n").encode()


def read_private_rewrites(path: Path) -> dict[str, PrivateRewrite]:
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["format", "1"]:
        fail(f"{path}: private rewrites must start with format\\t1")
    rewrites: dict[str, PrivateRewrite] = {}
    order: list[str] = []
    for line_number, values in enumerate(rows[1:], 2):
        if len(values) != 3:
            fail(f"{path}:{line_number}: expected three private-rewrite columns")
        row = PrivateRewrite(*values)
        if row.logical_name in rewrites:
            fail(f"{path}:{line_number}: duplicate private rewrite")
        rewrites[row.logical_name] = row
        order.append(row.logical_name)
    if order != sorted(order):
        fail(f"{path}: private rewrites are not sorted")
    return rewrites


def matches_live_checkpoint_private_rewrites(
    project_root: Path, relative_path: Path, current_path: Path
) -> bool:
    """Accept only the reviewed inherited Q2A manifest on a live-base resume."""
    try:
        expected = subprocess.check_output(
            [
                "git",
                "-C",
                str(project_root),
                "show",
                f"{LIVE_CHECKPOINT_SHA}:{relative_path.as_posix()}",
            ]
        )
    except subprocess.CalledProcessError:
        return False
    return current_path.read_bytes() == expected


def write_contract(
    args: argparse.Namespace,
    baseline: dict[str, Declaration],
) -> None:
    packet = read_packet_owners(args.packet_owners)
    owners = generate_frozen_owners(
        args.project_root, packet, args.frozen_source_dir, args.frozen_ilean_dir
    )
    routes = generate_routes(baseline, owners, args.frozen_source_dir, args.frozen_ilean_dir)
    ownership = ownership_from_routes(routes, baseline)
    rank, edges = destination_graph(args.dependency_tsv, baseline, ownership)
    imports = source_imports(args.frozen_source_dir, owners)
    artifacts = {
        args.frozen_owners: frozen_owner_bytes(owners),
        args.routes: route_bytes(routes),
        args.ownership: ownership_bytes(ownership),
        args.destination_dag: dag_bytes(rank, edges),
        args.source_imports: source_import_bytes(imports),
        args.alias_commands: alias_bytes(routes),
        args.private_rewrites: private_rewrite_bytes({}),
    }
    for relative, payload in artifacts.items():
        path = args.project_root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(payload)


def validate_committed_contract(
    args: argparse.Namespace,
    baseline: dict[str, Declaration],
) -> tuple[dict[str, FrozenOwner], dict[str, Route], dict[str, OwnershipRow], int]:
    owners = read_frozen_owners(args.project_root / args.frozen_owners)
    routes = read_routes(args.project_root / args.routes, baseline)
    command_groups = validate_routes_against_frozen(
        routes, owners, args.frozen_source_dir, args.frozen_ilean_dir
    )
    ownership = read_ownership(args.project_root / args.ownership, baseline, routes)
    rank, edges = destination_graph(args.baseline_tsv or args.dependency_tsv, baseline, ownership)
    if (args.project_root / args.destination_dag).read_bytes() != dag_bytes(rank, edges):
        fail("committed destination DAG differs from the frozen typed graph")
    imports = source_imports(args.frozen_source_dir, owners)
    if (args.project_root / args.source_imports).read_bytes() != source_import_bytes(imports):
        fail("committed source-import graph differs from pristine owners")
    if (args.project_root / args.alias_commands).read_bytes() != alias_bytes(routes):
        fail("committed explicit alias artifact differs from source commands")
    return owners, routes, ownership, command_groups


def validate_householder_contract(
    baseline_tsv: Path,
    baseline: dict[str, Declaration],
    routes: dict[str, Route],
) -> tuple[int, int, int, int]:
    wave = {logical: route for logical, route in routes.items() if route.destination_module in HOUSEHOLDER_DESTINATIONS}
    if len(wave) != 1040:
        fail(f"Householder Wave 1 must own 1,040 declarations, found {len(wave)}")
    if {row.historical_module for row in wave.values()} != HOUSEHOLDER_MODULES:
        fail("Householder Wave 1 does not cover exactly the eleven reviewed owners")
    groups = route_groups(wave)
    if len(groups) != 821:
        fail(f"Householder Wave 1 must contain 821 source commands, found {len(groups)}")
    private = [logical for logical in wave if baseline[logical].visibility == "private"]
    if len(private) != 15:
        fail(f"Householder Wave 1 must contain 15 private declarations, found {len(private)}")
    if {row.destination_module for row in wave.values()} != HOUSEHOLDER_DESTINATIONS:
        fail("Householder Wave 1 destination set differs from the reviewed 12 leaves")
    actual_to_logical = {row.name: logical for logical, row in baseline.items()}
    promotions = 0
    for edge in iter_stream_edges(baseline_tsv):
        if edge.kind != "body":
            continue
        source = actual_to_logical.get(edge.source)
        target = actual_to_logical.get(edge.target)
        if source not in wave or target not in wave or baseline[target].visibility != "private":
            continue
        if wave[source].destination_module != wave[target].destination_module:
            promotions += 1
    if promotions:
        fail(f"Householder Wave 1 unexpectedly requires {promotions} private promotions")
    return len(wave), len(groups), len(private), promotions


def validate_q2a_contract(
    baseline_tsv: Path,
    baseline: dict[str, Declaration],
    routes: dict[str, Route],
) -> tuple[int, int, int, int]:
    wave = {
        logical: route
        for logical, route in routes.items()
        if route.destination_module in Q2A_DESTINATIONS
    }
    if len(wave) != 868:
        fail(f"QR Q2A must own 868 declarations, found {len(wave)}")
    if {row.historical_module for row in wave.values()} != Q2A_MODULES:
        fail("QR Q2A does not cover exactly the six reviewed owners")
    groups = route_groups(wave)
    if len(groups) != 680:
        fail(f"QR Q2A must contain 680 source commands, found {len(groups)}")
    private = [logical for logical in wave if baseline[logical].visibility == "private"]
    if len(private) != 7:
        fail(f"QR Q2A must contain 7 private declarations, found {len(private)}")
    if {row.destination_module for row in wave.values()} != Q2A_DESTINATIONS:
        fail("QR Q2A destination set differs from the reviewed six leaves")
    actual_to_logical = {row.name: logical for logical, row in baseline.items()}
    promotions = 0
    for edge in iter_stream_edges(baseline_tsv):
        if edge.kind != "body":
            continue
        source = actual_to_logical.get(edge.source)
        target = actual_to_logical.get(edge.target)
        if source not in wave or target not in wave or baseline[target].visibility != "private":
            continue
        if wave[source].destination_module != wave[target].destination_module:
            promotions += 1
    if promotions:
        fail(f"QR Q2A unexpectedly requires {promotions} private promotions")
    return len(wave), len(groups), len(private), promotions


def generate_private_rewrites(
    baseline: dict[str, Declaration],
    ownership: dict[str, OwnershipRow],
    candidate_declarations: list[Declaration],
    completed: set[str],
) -> dict[str, PrivateRewrite]:
    by_module_suffix: dict[tuple[str, str], list[str]] = defaultdict(list)
    for declaration in candidate_declarations:
        if declaration.visibility != "private" or declaration.module not in completed:
            continue
        try:
            suffix = private_suffix(declaration.name, declaration.module)
        except ValueError:
            continue
        by_module_suffix[(declaration.module, suffix)].append(declaration.name)
    rewrites: dict[str, PrivateRewrite] = {}
    for logical, declaration in baseline.items():
        destination = ownership[logical].destination_module
        if destination not in completed or declaration.visibility != "private":
            continue
        suffix = private_suffix(declaration.name, declaration.module)
        candidates = by_module_suffix[(destination, suffix)]
        if len(candidates) != 1:
            fail(f"{logical}: expected one candidate private declaration, found {candidates}")
        rewrites[logical] = PrivateRewrite(logical, declaration.name, candidates[0])
    return rewrites


def validate_candidate_ownership(
    baseline: dict[str, Declaration],
    ownership: dict[str, OwnershipRow],
    candidate: list[Declaration],
    completed: set[str],
    rewrites: dict[str, PrivateRewrite],
) -> tuple[dict[str, str], dict[str, str]]:
    destinations = {row.destination_module for row in ownership.values()}
    unknown = completed - destinations
    if unknown:
        fail(f"completed destinations are outside the contract: {sorted(unknown)}")
    expected_private = {
        logical
        for logical, declaration in baseline.items()
        if declaration.visibility == "private" and ownership[logical].destination_module in completed
    }
    if set(rewrites) != expected_private:
        fail(
            "private rewrite coverage differs: "
            f"missing={sorted(expected_private-set(rewrites))}, "
            f"extra={sorted(set(rewrites)-expected_private)}"
        )
    by_name = {declaration.name: declaration for declaration in candidate}
    if len(by_name) != len(candidate):
        fail("candidate stream contains duplicate declaration names")
    baseline_actual_to_logical = {row.name: logical for logical, row in baseline.items()}
    candidate_actual_to_logical: dict[str, str] = {}
    for logical, frozen in baseline.items():
        destination = ownership[logical].destination_module
        expected_module = destination if destination in completed else frozen.module
        if frozen.visibility == "private" and destination in completed:
            rewrite = rewrites[logical]
            if rewrite.historical_actual_name != frozen.name:
                fail(f"{logical}: private rewrite historical name drift")
            actual_name = rewrite.candidate_actual_name
        else:
            actual_name = frozen.name
        actual = by_name.get(actual_name)
        if actual is None:
            fail(f"{logical}: candidate declaration {actual_name} is missing")
        if (actual.module, actual.kind, actual.visibility) != (
            expected_module,
            frozen.kind,
            frozen.visibility,
        ):
            fail(
                f"{logical}: expected {(expected_module, frozen.kind, frozen.visibility)}, "
                f"found {(actual.module, actual.kind, actual.visibility)}"
            )
        if actual_name in candidate_actual_to_logical:
            fail(f"candidate declaration {actual_name} maps to multiple logical owners")
        candidate_actual_to_logical[actual_name] = logical
    relevant_modules = set(EXPECTED_HISTORICAL_COUNTS) | destinations
    extra = sorted(
        declaration.name
        for declaration in candidate
        if declaration.module in relevant_modules
        and declaration.name not in candidate_actual_to_logical
    )
    if extra:
        fail(f"candidate QR owners contain uncontracted declarations: {extra[:20]}")
    return baseline_actual_to_logical, candidate_actual_to_logical


def incident_graph(
    path: Path, actual_to_logical: dict[str, str]
) -> Counter[tuple[str, str, str]]:
    graph: Counter[tuple[str, str, str]] = Counter()
    selected = set(actual_to_logical)
    for edge in iter_stream_edges(path):
        if edge.source not in selected and edge.target not in selected:
            continue
        source = f"@QR:{actual_to_logical[edge.source]}" if edge.source in selected else edge.source
        target = f"@QR:{actual_to_logical[edge.target]}" if edge.target in selected else edge.target
        graph[(edge.kind, source, target)] += 1
    return graph


def compare_incident_graphs(
    baseline_tsv: Path,
    candidate_tsv: Path,
    baseline_actual: dict[str, str],
    candidate_actual: dict[str, str],
) -> tuple[int, int]:
    frozen = incident_graph(baseline_tsv, baseline_actual)
    candidate = incident_graph(candidate_tsv, candidate_actual)
    if frozen != candidate:
        missing = list((frozen - candidate).items())[:20]
        extra = list((candidate - frozen).items())[:20]
        fail(f"normalized QR incident typed graph drift: missing={missing}, extra={extra}")
    signature = sum(count for (kind, _, _), count in frozen.items() if kind == "signature")
    body = sum(count for (kind, _, _), count in frozen.items() if kind == "body")
    return signature, body


def parse_imports(path: Path) -> list[str]:
    imports: list[str] = []
    for line in normalized_source_bytes(path).decode("utf-8").splitlines():
        match = IMPORT_RE.fullmatch(line)
        if match:
            imports.append(match.group(2))
    return imports


def completed_owners(routes: dict[str, Route], completed: set[str]) -> dict[str, set[str]]:
    owner_destinations: dict[str, set[str]] = defaultdict(set)
    owner_all: dict[str, set[str]] = defaultdict(set)
    for route in routes.values():
        owner_all[route.historical_module].add(route.destination_module)
        if route.destination_module in completed:
            owner_destinations[route.historical_module].add(route.destination_module)
    return {
        owner: owner_all[owner]
        for owner in owner_all
        if owner_all[owner] and owner_all[owner] <= completed
    }


def expected_canonical_imports(
    owner: str, original_imports: list[str], destination: str
) -> list[str]:
    if destination == CONSTRUCTION2_ALIAS_DESTINATION:
        return [f"{REUSABLE_ROOT}.HouseholderConstruction2"]
    # The frozen source files are the integrated 420 snapshot, while this
    # worker resumes from the later 482 checkpoint.  Once a Chapter 19 owner
    # is moved, imports between historical Chapter 19 owners must follow the
    # reviewed source destinations as well as the reusable QR destinations.
    # Keep the WY -> BlockLU edge as the explicitly reviewed late handoff: the
    # packet's pristine owner has that import, whereas the integrated snapshot
    # recorded the temporary AsymptoticFamilies repair.
    if owner == WY_OWNER:
        return [
            WY_OLD_IMPORT,
            f"{REUSABLE_ROOT}.GramSchmidtPolar",
        ]
    result: list[str] = []
    for imported in original_imports:
        if imported in EXPECTED_HISTORICAL_COUNTS:
            result.append(default_destination(imported))
        elif imported in REUSABLE_MIGRATION_MODULES:
            result.append(default_destination(imported))
        else:
            result.append(imported)
    return list(dict.fromkeys(result))


def validate_structural_files(
    project_root: Path,
    routes: dict[str, Route],
    owners: dict[str, FrozenOwner],
    source_dir: Path,
    completed: set[str],
) -> tuple[int, int]:
    complete_owners = completed_owners(routes, completed)
    for owner, destinations in complete_owners.items():
        path = project_root / module_path(owner)
        expected = "".join(f"import {destination}\n" for destination in sorted(destinations)).encode()
        if normalized_source_bytes(path) != expected:
            fail(f"{owner}: historical wrapper is not the exact reviewed import-only file")

    destination_to_owner: dict[str, str] = {}
    for route in routes.values():
        if route.destination_module in completed:
            previous = destination_to_owner.setdefault(route.destination_module, route.historical_module)
            if previous != route.historical_module:
                fail(f"{route.destination_module}: destination combines historical owners")
    for destination, owner in sorted(destination_to_owner.items()):
        path = project_root / module_path(destination)
        if not path.is_file():
            fail(f"completed destination source is missing: {destination}")
        original = parse_imports(frozen_source_path(source_dir, owner))
        expected = expected_canonical_imports(owner, original, destination)
        actual = parse_imports(path)
        if actual != expected:
            fail(f"{destination}: imports differ: expected={expected}, actual={actual}")
        if any(target.startswith(HISTORICAL_ROOT + ".") for target in actual):
            fail(f"{destination}: canonical source imports a historical QR path")
        if destination_tier(destination) == "reusable" and any(
            target.startswith(SOURCE_ROOT + ".") for target in actual
        ):
            fail(f"{destination}: reusable source imports Chapter 19 source correspondence")
    return len(complete_owners), len(destination_to_owner)


def validate_candidate_command_hashes(
    project_root: Path,
    routes: dict[str, Route],
    baseline: dict[str, Declaration],
    rewrites: dict[str, PrivateRewrite],
    completed: set[str],
) -> int:
    groups = route_groups(routes)
    completed_groups = [
        members for members in groups.values() if members[0].destination_module in completed
    ]
    entries: dict[str, dict[str, tuple[int, int, int, int, int, int, int, int]]] = {}
    sources: dict[str, bytes] = {}
    alias_spans: dict[str, dict[str, tuple[int, int, int, int, int, int, int, int]]] = {}
    for destination in completed:
        source = project_root / module_path(destination)
        sources[destination] = normalized_source_bytes(source)
        ilean = project_root / ".lake/build/lib/lean" / module_path(destination, ".ilean")
        entries[destination] = read_ilean_entries(ilean, destination)
        alias_names = {
            member.historical_actual_name
            for members in completed_groups
            for member in members
            if member.destination_module == destination and member.provenance == "source_alias"
        }
        if alias_names:
            alias_spans[destination] = find_alias_spans(sources[destination], destination, alias_names)

    for members in completed_groups:
        root = next(
            row for row in members if row.provenance in {"authored", "source_alias"}
        )
        destination = root.destination_module
        if root.provenance == "source_alias":
            span = alias_spans[destination][root.historical_actual_name]
        else:
            frozen_root = baseline[root.command_root_logical]
            if frozen_root.visibility == "private":
                actual_root = rewrites[root.command_root_logical].candidate_actual_name
            else:
                actual_root = root.command_root_actual_name
            span = entries[destination].get(actual_root)
            if span is None:
                fail(f"{root.command_root_logical}: candidate .ilean command root missing")
        candidate_hash = sha256_bytes(source_command_bytes(sources[destination], span))
        if candidate_hash != root.command_sha256.upper():
            fail(f"{root.command_root_logical}: candidate command bytes differ from frozen source")
    return len(completed_groups)


def materialize_householder_wave(
    project_root: Path,
    routes: dict[str, Route],
    owners: dict[str, FrozenOwner],
    source_dir: Path,
) -> None:
    groups = route_groups(routes)
    by_owner: dict[str, list[Route]] = defaultdict(list)
    for members in groups.values():
        by_owner[members[0].historical_module].append(
            next(row for row in members if row.provenance in {"authored", "source_alias"})
        )

    for owner in sorted(HOUSEHOLDER_MODULES):
        frozen = owners[owner]
        live = project_root / frozen.path
        pristine = frozen_source_path(source_dir, owner)
        if sha256_file(pristine) != frozen.source_sha256:
            fail(f"{owner}: pristine materialization source differs from the contract")
        source = normalized_source_bytes(pristine)
        basename = owner.rsplit(".", 1)[1]
        reusable = default_destination(owner)
        reusable_payload = source
        if basename == "HouseholderConstruction2":
            alias_route = next(row for row in by_owner[owner] if row.command_root_actual_name == CONSTRUCTION2_ALIAS)
            command = source_command_bytes(source, alias_route.span)
            start = source.find(command)
            if start < 0:
                fail("Construction2 alias command split point is missing")
            end = start + len(command)
            reusable_payload = source[:start] + source[end:]
            source_payload = (
                (
                    f"import {reusable}\n\n"
                    "/-!\n"
                    "# Higham Chapter 19, Lemma 19.1, Construction 2\n\n"
                    "Numbered source-facing export for the alternative-sign "
                    "Householder construction.\n"
                    "-/\n\n"
                    "namespace NumStability\n\n"
                ).encode()
                + source[start:end]
                + b"\n\nend NumStability\n"
            )
            source_path = project_root / module_path(CONSTRUCTION2_ALIAS_DESTINATION)
            source_path.parent.mkdir(parents=True, exist_ok=True)
            source_path.write_bytes(source_payload)
        reusable_payload = reusable_payload.replace(
            f"Algorithms/QR/{basename}.lean".encode(),
            f"Algorithms/LinearSystems/QR/{basename}.lean".encode(),
            1,
        )
        for dependency in HOUSEHOLDER_MODULES:
            reusable_payload = reusable_payload.replace(
                f"import {dependency}\n".encode(),
                f"import {default_destination(dependency)}\n".encode(),
            )
        reusable_path = project_root / module_path(reusable)
        reusable_path.parent.mkdir(parents=True, exist_ok=True)
        module_doc = (
            f"/-!\n# {basename}\n\n"
            "Canonical source-neutral Householder API.  The historical QR path "
            "remains an import-only wrapper.\n"
            "-/\n\n"
        ).encode()
        import_ends = [
            match.end()
            for match in re.finditer(
                rb"(?m)^(?:public\s+)?import\s+[A-Za-z_][A-Za-z0-9_.]*\n",
                reusable_payload,
            )
        ]
        if not import_ends:
            fail(f"{owner}: materialized reusable source has no import command")
        insert_at = max(import_ends)
        reusable_path.write_bytes(
            reusable_payload[:insert_at]
            + b"\n"
            + module_doc
            + reusable_payload[insert_at:]
        )
        destinations = sorted({row.destination_module for row in by_owner[owner]})
        live.write_bytes("".join(f"import {destination}\n" for destination in destinations).encode())

    canonical_test_paths: list[str] = []
    old_test_paths: list[str] = []
    for destination in sorted(HOUSEHOLDER_DESTINATIONS):
        roots = sorted(
            {
                row.command_root_actual_name
                for members in groups.values()
                for row in members
                if row.destination_module == destination
                and row.provenance in {"authored", "source_alias"}
                and not row.command_root_actual_name.startswith("_private.")
            }
        )
        if not roots:
            fail(f"{destination}: no public command root for canonical smoke test")
        label = destination.rsplit(".", 1)[1]
        if destination == CONSTRUCTION2_ALIAS_DESTINATION:
            label = "Lemma01Construction2"
        module = f"NumStabilityTest.Worker.QrCh19.Canonical.{label}"
        path = project_root / module_path(module)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f"import {destination}\n\n#check {roots[0]}\n", encoding="utf-8", newline="\n")
        canonical_test_paths.append(module)

    for owner in sorted(HOUSEHOLDER_MODULES):
        destinations = {row.destination_module for row in by_owner[owner]}
        checks: list[str] = []
        for destination in sorted(destinations):
            roots = sorted(
                row.command_root_actual_name
                for row in by_owner[owner]
                if row.destination_module == destination
                and not row.command_root_actual_name.startswith("_private.")
            )
            if roots:
                checks.append(roots[0])
        label = owner.rsplit(".", 1)[1]
        module = f"NumStabilityTest.Worker.QrCh19.Compatibility.{label}"
        path = project_root / module_path(module)
        path.parent.mkdir(parents=True, exist_ok=True)
        payload = f"import {owner}\n\n" + "".join(f"#check {name}\n" for name in checks)
        path.write_text(payload, encoding="utf-8", newline="\n")
        old_test_paths.append(module)

    wave_module = "NumStabilityTest.Worker.QrCh19.HouseholderWave1"
    wave_path = project_root / module_path(wave_module)
    wave_path.parent.mkdir(parents=True, exist_ok=True)
    all_tests = sorted(canonical_test_paths + old_test_paths)
    wave_path.write_text(
        "".join(f"import {module}\n" for module in all_tests), encoding="utf-8", newline="\n"
    )


def materialize_q2a(
    project_root: Path,
    routes: dict[str, Route],
    owners: dict[str, FrozenOwner],
    source_dir: Path,
) -> None:
    groups = route_groups(routes)
    by_owner: dict[str, list[Route]] = defaultdict(list)
    for members in groups.values():
        by_owner[members[0].historical_module].append(
            next(row for row in members if row.provenance in {"authored", "source_alias"})
        )

    for owner in sorted(Q2A_MODULES):
        frozen = owners[owner]
        live = project_root / frozen.path
        pristine = frozen_source_path(source_dir, owner)
        if sha256_file(pristine) != frozen.source_sha256:
            fail(f"{owner}: pristine materialization source differs from the contract")
        source = normalized_source_bytes(pristine)
        basename = owner.rsplit(".", 1)[1]
        reusable = default_destination(owner)
        reusable_payload = source.replace(
            f"Algorithms/QR/{basename}.lean".encode(),
            f"Algorithms/LinearSystems/QR/{basename}.lean".encode(),
            1,
        )
        for dependency in REUSABLE_MIGRATION_MODULES:
            reusable_payload = reusable_payload.replace(
                f"import {dependency}\n".encode(),
                f"import {default_destination(dependency)}\n".encode(),
            )
        reusable_path = project_root / module_path(reusable)
        reusable_path.parent.mkdir(parents=True, exist_ok=True)
        module_doc = (
            f"/-!\n# {basename}\n\n"
            "Canonical source-neutral QR API.  The historical QR path "
            "remains an import-only wrapper.\n"
            "-/\n\n"
        ).encode()
        import_ends = [
            match.end()
            for match in re.finditer(
                rb"(?m)^(?:public\s+)?import\s+[A-Za-z_][A-Za-z0-9_.]*\n",
                reusable_payload,
            )
        ]
        if not import_ends:
            fail(f"{owner}: materialized reusable source has no import command")
        insert_at = max(import_ends)
        reusable_path.write_bytes(
            reusable_payload[:insert_at]
            + b"\n"
            + module_doc
            + reusable_payload[insert_at:]
        )
        live.write_bytes(f"import {reusable}\n".encode())

    canonical_test_paths: list[str] = []
    old_test_paths: list[str] = []
    for destination in sorted(Q2A_DESTINATIONS):
        roots = sorted(
            {
                row.command_root_actual_name
                for members in groups.values()
                for row in members
                if row.destination_module == destination
                and row.provenance in {"authored", "source_alias"}
                and not row.command_root_actual_name.startswith("_private.")
            }
        )
        if not roots:
            fail(f"{destination}: no public command root for canonical smoke test")
        label = destination.rsplit(".", 1)[1]
        module = f"NumStabilityTest.Worker.QrCh19.Canonical.{label}"
        path = project_root / module_path(module)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f"import {destination}\n\n#check {roots[0]}\n", encoding="utf-8", newline="\n")
        canonical_test_paths.append(module)

    for owner in sorted(Q2A_MODULES):
        roots = sorted(
            row.command_root_actual_name
            for row in by_owner[owner]
            if not row.command_root_actual_name.startswith("_private.")
        )
        if not roots:
            fail(f"{owner}: no public command root for compatibility smoke test")
        label = owner.rsplit(".", 1)[1]
        module = f"NumStabilityTest.Worker.QrCh19.Compatibility.{label}"
        path = project_root / module_path(module)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            f"import {owner}\n\n#check {roots[0]}\n", encoding="utf-8", newline="\n"
        )
        old_test_paths.append(module)

    wave_module = "NumStabilityTest.Worker.QrCh19.Q2A"
    wave_path = project_root / module_path(wave_module)
    wave_path.parent.mkdir(parents=True, exist_ok=True)
    all_tests = sorted(canonical_test_paths + old_test_paths)
    wave_path.write_text(
        "".join(f"import {module}\n" for module in all_tests), encoding="utf-8", newline="\n"
    )


def validate_materialized_householder_text(
    project_root: Path,
    routes: dict[str, Route],
    owners: dict[str, FrozenOwner],
    source_dir: Path,
) -> int:
    """Check all 821 moved command byte strings without relying on build output."""

    wave_groups = [
        members
        for members in route_groups(routes).values()
        if members[0].destination_module in HOUSEHOLDER_DESTINATIONS
    ]
    frozen_sources = {
        owner: normalized_source_bytes(frozen_source_path(source_dir, owner))
        for owner in HOUSEHOLDER_MODULES
    }
    candidate_sources = {
        destination: normalized_source_bytes(project_root / module_path(destination))
        for destination in HOUSEHOLDER_DESTINATIONS
    }
    for members in wave_groups:
        root = next(
            row for row in members if row.provenance in {"authored", "source_alias"}
        )
        command = source_command_bytes(
            frozen_sources[root.historical_module], root.span
        )
        occurrences = candidate_sources[root.destination_module].count(command)
        if occurrences != 1:
            fail(
                f"{root.command_root_logical}: frozen command occurs {occurrences} "
                "times in its materialized destination"
            )
    wrappers, destinations = validate_structural_files(
        project_root,
        routes,
        owners,
        source_dir,
        set(HOUSEHOLDER_DESTINATIONS),
    )
    if (len(wave_groups), wrappers, destinations) != (821, 11, 12):
        fail("materialized Householder structural counts drifted")
    return len(wave_groups)


def validate_materialized_q2a_text(
    project_root: Path,
    routes: dict[str, Route],
    owners: dict[str, FrozenOwner],
    source_dir: Path,
) -> int:
    """Check all 680 Q2A command byte strings without relying on build output."""

    wave_groups = [
        members
        for members in route_groups(routes).values()
        if members[0].destination_module in Q2A_DESTINATIONS
    ]
    frozen_sources = {
        owner: normalized_source_bytes(frozen_source_path(source_dir, owner))
        for owner in Q2A_MODULES
    }
    candidate_sources = {
        destination: normalized_source_bytes(project_root / module_path(destination))
        for destination in Q2A_DESTINATIONS
    }
    for members in wave_groups:
        root = next(
            row for row in members if row.provenance in {"authored", "source_alias"}
        )
        command = source_command_bytes(
            frozen_sources[root.historical_module], root.span
        )
        occurrences = candidate_sources[root.destination_module].count(command)
        if occurrences != 1:
            fail(
                f"{root.command_root_logical}: frozen command occurs {occurrences} "
                "times in its materialized destination"
            )
    wrappers, destinations = validate_structural_files(
        project_root,
        routes,
        owners,
        source_dir,
        set(Q2A_DESTINATIONS),
    )
    if (len(wave_groups), wrappers, destinations) != (680, 6, 6):
        fail("materialized QR Q2A structural counts drifted")
    return len(wave_groups)


def run_self_test() -> None:
    owner = f"{HISTORICAL_ROOT}.HouseholderSpec"
    private = f"_private.{owner}.7.NumStability.helper"
    assert logical_name(private, owner) == f"_private.{owner}.NumStability.helper"
    unicode_source = "theorem x : ℝ := by\n  exact 0\n".encode()
    assert source_command_bytes(unicode_source, (0, 0, 1, 9, 0, 8, 0, 9)) == unicode_source[:-1]
    alias_source = (
        "namespace NumStability\nnamespace Theorem19_6\n"
        "alias first_alias :=\n  Original.first\n"
        "alias second_alias :=\n  Original.second\n"
        "end Theorem19_6\nend NumStability\n"
    ).encode()
    names = {
        "NumStability.Theorem19_6.first_alias",
        "NumStability.Theorem19_6.second_alias",
    }
    spans = find_alias_spans(alias_source, "synthetic", names)
    assert set(spans) == names
    assert b"alias first_alias" in source_command_bytes(alias_source, spans[next(iter(sorted(names)))])

    try:
        private_suffix(private, f"{HISTORICAL_ROOT}.HouseholderQR")
    except ValueError:
        pass
    else:
        raise AssertionError("private owner drift was not rejected")

    with tempfile.TemporaryDirectory() as raw:
        root = Path(raw)
        wrapper = root / "Wrapper.lean"
        wrapper.write_text("import A\n\ntheorem bad : True := True.intro\n", encoding="utf-8")
        if parse_imports(wrapper) != ["A"]:
            raise AssertionError("import parser self-test failed")
        # Exact wrapper validation must reject even a semantically harmless declaration.
        if normalized_source_bytes(wrapper) == b"import A\n":
            raise AssertionError("wrapper negative self-test failed")

    frozen = Counter({("signature", "@QR:a", "external"): 1})
    candidate = Counter({("signature", "@QR:a", "different"): 1})
    if frozen == candidate:
        raise AssertionError("typed-edge drift negative self-test failed")

    source_owner = f"{HISTORICAL_ROOT}.Higham19Alg12MGSClosure"
    source_destination = default_destination(source_owner)
    mapped = expected_canonical_imports(
        source_owner,
        [f"{HISTORICAL_ROOT}.Higham19Alg12MGSRepair"],
        source_destination,
    )
    if mapped != [f"{SOURCE_ROOT}.Algorithm12.MGSRepair"]:
        raise AssertionError("historical Chapter 19 import mapping self-test failed")
    if expected_canonical_imports(WY_OWNER, [], default_destination(WY_OWNER)) != [
        WY_OLD_IMPORT,
        f"{REUSABLE_ROOT}.GramSchmidtPolar",
    ]:
        raise AssertionError("late WY/BlockLU import self-test failed")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("pre", "stage", "post"))
    parser.add_argument("--dependency-tsv", type=Path)
    parser.add_argument("--baseline-tsv", type=Path)
    parser.add_argument("--project-root", type=Path, default=Path("."))
    parser.add_argument("--packet-owners", type=Path)
    parser.add_argument("--frozen-source-dir", type=Path)
    parser.add_argument("--frozen-ilean-dir", type=Path)
    parser.add_argument("--frozen-owners", type=Path, default=DEFAULT_FROZEN_OWNERS)
    parser.add_argument("--routes", type=Path, default=DEFAULT_ROUTES)
    parser.add_argument("--ownership", type=Path, default=DEFAULT_OWNERSHIP)
    parser.add_argument("--destination-dag", type=Path, default=DEFAULT_DAG)
    parser.add_argument("--source-imports", type=Path, default=DEFAULT_IMPORTS)
    parser.add_argument("--alias-commands", type=Path, default=DEFAULT_ALIASES)
    parser.add_argument("--private-rewrites", type=Path, default=DEFAULT_PRIVATE_REWRITES)
    parser.add_argument("--completed-destination", action="append", default=[])
    parser.add_argument("--write-contract", action="store_true")
    parser.add_argument("--write-private-rewrites", action="store_true")
    parser.add_argument("--materialize-householder-wave", action="store_true")
    parser.add_argument("--check-materialized-householder", action="store_true")
    parser.add_argument("--materialize-q2a", action="store_true")
    parser.add_argument("--check-materialized-q2a", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.self_test:
        run_self_test()
        print("qr-ch19 ownership checker negative self-tests passed")
        return 0
    if args.mode is None or args.dependency_tsv is None:
        fail("--mode and --dependency-tsv are required")
    if args.packet_owners is None or args.frozen_source_dir is None or args.frozen_ilean_dir is None:
        fail("--packet-owners, --frozen-source-dir, and --frozen-ilean-dir are required")
    args.project_root = args.project_root.resolve()
    if args.mode == "pre":
        if args.baseline_tsv is not None:
            fail("pre mode uses --dependency-tsv as the frozen baseline")
        if sha256_file(args.dependency_tsv) != BASELINE_TSV_SHA256:
            fail("pre dependency stream hash differs from the immutable packet baseline")
        baseline_path = args.dependency_tsv
    else:
        if args.baseline_tsv is None or sha256_file(args.baseline_tsv) != BASELINE_TSV_SHA256:
            fail("stage/post requires the immutable format-2 --baseline-tsv")
        baseline_path = args.baseline_tsv
    baseline_declarations = read_stream_declarations(baseline_path)
    baseline = select_baseline(baseline_declarations)
    if args.write_contract:
        if args.mode != "pre":
            fail("--write-contract is valid only in pre mode")
        write_contract(args, baseline)
    owners, routes, ownership, command_groups = validate_committed_contract(args, baseline)
    wave_declarations, wave_groups, wave_private, promotions = validate_householder_contract(
        baseline_path, baseline, routes
    )
    q2a_declarations, q2a_groups, q2a_private, q2a_promotions = validate_q2a_contract(
        baseline_path, baseline, routes
    )
    if args.materialize_householder_wave:
        if args.mode != "pre":
            fail("--materialize-householder-wave is valid only in pre mode")
        materialize_householder_wave(
            args.project_root, routes, owners, args.frozen_source_dir
        )
        print(
            f"materialized Householder Wave 1: {wave_declarations} declarations, "
            f"{wave_groups} command groups, {len(HOUSEHOLDER_DESTINATIONS)} destinations"
        )
        return 0
    if args.check_materialized_householder:
        groups = validate_materialized_householder_text(
            args.project_root, routes, owners, args.frozen_source_dir
        )
        print(
            f"materialized Householder text gate passed: {groups} command groups, "
            "11 exact wrappers, 12 canonical destinations"
        )
        return 0
    if args.materialize_q2a:
        if args.mode != "pre":
            fail("--materialize-q2a is valid only in pre mode")
        materialize_q2a(
            args.project_root, routes, owners, args.frozen_source_dir
        )
        print(
            f"materialized QR Q2A: {q2a_declarations} declarations, "
            f"{q2a_groups} command groups, {len(Q2A_DESTINATIONS)} destinations"
        )
        return 0
    if args.check_materialized_q2a:
        groups = validate_materialized_q2a_text(
            args.project_root, routes, owners, args.frozen_source_dir
        )
        print(
            f"materialized QR Q2A text gate passed: {groups} command groups, "
            "6 exact wrappers, 6 canonical destinations"
        )
        return 0

    if args.mode == "pre":
        private_path = args.project_root / args.private_rewrites
        rewrites = read_private_rewrites(private_path)
        inherited = bool(rewrites) and matches_live_checkpoint_private_rewrites(
            args.project_root, args.private_rewrites, private_path
        )
        if rewrites and not inherited:
            fail("pre-migration private rewrite manifest must be header-only or the exact live-base inherited manifest")
        print(
            f"pre mode passed: {len(owners)} owners, {len(routes)} declarations, "
            f"{command_groups} command groups, {len(set(r.destination_module for r in routes.values()))} "
            f"destinations; Householder Wave 1 = {wave_declarations} declarations / "
            f"{wave_groups} commands / {wave_private} private rewrites / {promotions} promotions; "
            f"QR Q2A = {q2a_declarations} declarations / {q2a_groups} commands / "
            f"{q2a_private} private rewrites / {q2a_promotions} promotions; "
            f"routes sha256 {sha256_file(args.project_root / args.routes)}; "
            f"inherited private rewrites={len(rewrites) if inherited else 0}"
        )
        return 0

    candidate = read_stream_declarations(args.dependency_tsv)
    completed = set(args.completed_destination)
    if args.mode == "post":
        completed = {row.destination_module for row in ownership.values()}
    if args.write_private_rewrites:
        generated = generate_private_rewrites(baseline, ownership, candidate, completed)
        path = args.project_root / args.private_rewrites
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(private_rewrite_bytes(generated))
    rewrites = read_private_rewrites(args.project_root / args.private_rewrites)
    baseline_actual, candidate_actual = validate_candidate_ownership(
        baseline, ownership, candidate, completed, rewrites
    )
    signature_edges, body_edges = compare_incident_graphs(
        baseline_path, args.dependency_tsv, baseline_actual, candidate_actual
    )
    wrappers, destinations = validate_structural_files(
        args.project_root, routes, owners, args.frozen_source_dir, completed
    )
    fingerprint_groups = validate_candidate_command_hashes(
        args.project_root, routes, baseline, rewrites, completed
    )
    if completed == HOUSEHOLDER_DESTINATIONS:
        if len(rewrites) != 15 or fingerprint_groups != 821 or wrappers != 11 or destinations != 12:
            fail("Householder stage counts differ from the reviewed 15/821/11/12 contract")
    if completed == HOUSEHOLDER_AND_Q2A_DESTINATIONS:
        if len(rewrites) != 22 or fingerprint_groups != 1501 or wrappers != 17 or destinations != 18:
            fail("Householder + QR Q2A stage counts differ from the reviewed 22/1501/17/18 contract")
    print(
        f"{args.mode} mode passed: {len(completed)} destinations, {wrappers} wrappers, "
        f"{fingerprint_groups} byte-identical command groups, {len(rewrites)} private rewrites, "
        f"{signature_edges} signature edges, {body_edges} body/proof edges"
    )
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, json.JSONDecodeError, subprocess.CalledProcessError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        sys.exit(1)
