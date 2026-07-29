#!/usr/bin/env python3
"""Generate and check the least-squares / Chapter 20 semantic ownership partition.

The lane migrates the 42 historical ``NumStability.Algorithms.LeastSquares``
modules into three reviewed roots:

* ``NumStability.Algorithms.LinearSystems.LeastSquares`` — source-neutral
  least-squares specifications and algorithms;
* ``NumStability.Analysis.Perturbation.LeastSquares`` — source-neutral
  perturbation and error analysis;
* ``NumStability.Source.Higham.Chapter20`` — numbered results, named prose,
  printed examples, corrections, execution traces, and capstones.

The ownership manifest has the following tab-separated schema::

    format\t1
    logical_name\thistorical_module\tdestination_module\tkind\tvisibility

Manifest generation is driven by a separately reviewed route map.  A route map
starts with ``format\t1`` and accepts these row shapes::

    range\thistorical_module\tfirst_line\tlast_line\tdestination_module
    exact\thistorical_module\tlogical_name\t-\tdestination_module

Source lines are one-based and inclusive.  Range routing resolves compiled
declarations through source locations in the historical module's ``.ilean``
file.  Exact routes take precedence and cover reviewed declarations that have
no usable source declaration root.  The checker never invents a destination.

Lean private names encode their owning module and therefore necessarily change
when a declaration moves.  Stage and post modes require an explicit companion
map for every private declaration owned by a completed destination::

    format\t1
    logical_name\thistorical_actual_name\tcandidate_actual_name

Only those reviewed private-name rewrites are normalized during the exact
full-graph comparison.

The lane additionally freezes two cross-lane contracts that the QR lane owns on
the other side:

* the 19 ``LS_TO_QR`` module dependencies must survive owner normalization, so
  some destination that owns a declaration of the historical module keeps the
  QR target as a direct import;
* the four ``QR_TO_LS`` consumers must keep reaching lane declarations through
  the retained historical import paths.

Proposed tiers live in a lane-owned manifest because the global
``docs/architecture/tiers.json`` registration is integrator-owned::

    format\t1
    module\ttier

``tier`` is one of ``reusable``, ``source``, or ``compatibility``.  A lane
production module classified ``mixed`` is rejected outright.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import sys
import tempfile
from collections import Counter, defaultdict, deque
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterable

LS_PREFIX = "NumStability.Algorithms.LeastSquares"
REUSABLE_ALGORITHM_ROOT = "NumStability.Algorithms.LinearSystems.LeastSquares"
REUSABLE_ANALYSIS_ROOT = "NumStability.Analysis.Perturbation.LeastSquares"
SOURCE_ROOT = "NumStability.Source.Higham.Chapter20"
HIGHAM_COMPAT_ROOT = "NumStability.Higham.Chapter20"
CHAPTER_SEVEN = "NumStability.Analysis.HighamChapter7"

REUSABLE_DESTINATION_PREFIXES = (
    REUSABLE_ALGORITHM_ROOT + ".",
    REUSABLE_ANALYSIS_ROOT + ".",
)
SOURCE_DESTINATION_PREFIX = SOURCE_ROOT + "."

# Frozen historical declaration counts at base
# 6487fc33088523b8f27ecde9ad613515b78f9977.  Higham20SourceAliases is the
# already-compatibility member of the family and owns no declaration, so it is
# a structural module rather than a historical owner.
EXPECTED_HISTORICAL_COUNTS = {
    f"{LS_PREFIX}.Higham20Algorithms": 86,
    f"{LS_PREFIX}.Higham20AlternativeBound": 14,
    f"{LS_PREFIX}.Higham20CrossProductExample": 12,
    f"{LS_PREFIX}.Higham20EliminationActual": 63,
    f"{LS_PREFIX}.Higham20Equations": 26,
    f"{LS_PREFIX}.Higham20ExampleCondition": 9,
    f"{LS_PREFIX}.Higham20GeneralWedin": 32,
    f"{LS_PREFIX}.Higham20Lemma20_11": 20,
    f"{LS_PREFIX}.Higham20Lemma20_12": 8,
    f"{LS_PREFIX}.Higham20MGSStability": 31,
    f"{LS_PREFIX}.Higham20MPProse": 16,
    f"{LS_PREFIX}.Higham20MinimumNormBackwardError": 22,
    f"{LS_PREFIX}.Higham20NormalEquationsNorms": 15,
    f"{LS_PREFIX}.Higham20Problem20_3": 21,
    f"{LS_PREFIX}.Higham20Prose": 27,
    f"{LS_PREFIX}.Higham20QuantitativeProse": 6,
    f"{LS_PREFIX}.Higham20Refinement": 52,
    f"{LS_PREFIX}.Higham20Remaining": 15,
    f"{LS_PREFIX}.Higham20ResidualQuality": 27,
    f"{LS_PREFIX}.Higham20RowSorting": 78,
    f"{LS_PREFIX}.Higham20Theorem20_10": 23,
    f"{LS_PREFIX}.Higham20Theorem20_3": 8,
    f"{LS_PREFIX}.Higham20Theorem20_4Absorption": 21,
    f"{LS_PREFIX}.Higham20Theorem20_7": 150,
    f"{LS_PREFIX}.Higham20Theorem20_7ActualAssembly": 79,
    f"{LS_PREFIX}.Higham20Theorem20_7ActualBackSub": 34,
    f"{LS_PREFIX}.Higham20Theorem20_7ActualClosure": 30,
    f"{LS_PREFIX}.Higham20Theorem20_7ActualGrowth": 4,
    f"{LS_PREFIX}.Higham20Theorem20_7ActualRhs": 26,
    f"{LS_PREFIX}.Higham20Theorem20_7ActualTrace": 49,
    f"{LS_PREFIX}.Higham20Theorem20_7Contract": 143,
    f"{LS_PREFIX}.Higham20Theorem20_7QdR": 43,
    f"{LS_PREFIX}.Higham20Theorem20_7Runtime": 20,
    f"{LS_PREFIX}.Higham20Theorem20_7SourceTrace": 54,
    f"{LS_PREFIX}.Higham20Theorem20_8": 41,
    f"{LS_PREFIX}.Higham20WeightedLimit": 10,
    f"{LS_PREFIX}.Higham20ZeroDeltaB": 50,
    f"{LS_PREFIX}.LSE": 1982,
    f"{LS_PREFIX}.LSNormalEquations": 38,
    f"{LS_PREFIX}.LSPerturbation": 259,
    f"{LS_PREFIX}.LSQRSolve": 1485,
}
EXPECTED_MANIFEST_ROWS = sum(EXPECTED_HISTORICAL_COUNTS.values())
EXPECTED_PRIVATE_ROWS = 151

# The declaration-free members of the historical family and the pre-existing
# canonical Chapter 20 leaves.  These modules are checked as import-only
# wrappers or aggregates once the lane declares them complete.
DEFAULT_STRUCTURAL_MODULES = {
    f"{LS_PREFIX}.Higham20SourceAliases",
    f"{HIGHAM_COMPAT_ROOT}.SourceAliases",
    SOURCE_ROOT,
}

PRESERVED_SOURCE_LEAVES = {
    f"{SOURCE_ROOT}.Equation32",
    f"{SOURCE_ROOT}.Lemma06",
    f"{SOURCE_ROOT}.Theorem01",
}

# Exactly the 19 LS_TO_QR rows of KNOWN_CROSS_LANE_EDGES.tsv.
FROZEN_LS_TO_QR = frozenset(
    {
        (f"{LS_PREFIX}.Higham20MGSStability", "NumStability.Algorithms.QR.Higham19"),
        (
            f"{LS_PREFIX}.Higham20MGSStability",
            "NumStability.Algorithms.QR.Higham19Alg12MGSRounded",
        ),
        (
            f"{LS_PREFIX}.Higham20MGSStability",
            "NumStability.Algorithms.QR.Higham19Alg12MGSRepair",
        ),
        (f"{LS_PREFIX}.Higham20Theorem20_3", "NumStability.Algorithms.QR.Higham19"),
        (
            f"{LS_PREFIX}.Higham20Theorem20_7",
            "NumStability.Algorithms.QR.Higham19Thm6CoxHigham",
        ),
        (
            f"{LS_PREFIX}.Higham20Theorem20_7",
            "NumStability.Algorithms.QR.Higham19Thm6CoxHighamConcrete",
        ),
        (
            f"{LS_PREFIX}.Higham20Theorem20_7",
            "NumStability.Algorithms.QR.HouseholderApply",
        ),
        (
            f"{LS_PREFIX}.Higham20Theorem20_7",
            "NumStability.Algorithms.QR.HouseholderQRSupport",
        ),
        (
            f"{LS_PREFIX}.Higham20Theorem20_7Contract",
            "NumStability.Algorithms.QR.Higham19Thm6RowSpecific",
        ),
        (
            f"{LS_PREFIX}.Higham20ZeroDeltaB",
            "NumStability.Algorithms.QR.Higham19Labels",
        ),
        (f"{LS_PREFIX}.LSQRSolve", "NumStability.Algorithms.QR.QRSolve"),
        (f"{LS_PREFIX}.LSQRSolve", "NumStability.Algorithms.QR.HouseholderQRSupport"),
        (f"{LS_PREFIX}.LSE", "NumStability.Algorithms.QR.GramSchmidtPolar"),
        (f"{LS_PREFIX}.LSE", "NumStability.Algorithms.QR.Higham19"),
        (
            f"{LS_PREFIX}.LSE",
            "NumStability.Algorithms.QR.Higham19Thm6ElementwisePackaged",
        ),
        (f"{LS_PREFIX}.LSE", "NumStability.Algorithms.QR.Higham19Thm6RowSpecific"),
        (f"{LS_PREFIX}.LSE", "NumStability.Algorithms.QR.Higham19Thm6CoxHigham"),
        (
            f"{LS_PREFIX}.LSE",
            "NumStability.Algorithms.QR.Higham19Thm6CoxHighamConcrete",
        ),
        (f"{LS_PREFIX}.LSE", "NumStability.Algorithms.QR.Higham19Thm6ColPivot"),
    }
)

# Exactly the four QR_TO_LS rows of KNOWN_CROSS_LANE_EDGES.tsv.
FROZEN_QR_TO_LS = frozenset(
    {
        (
            "NumStability.Algorithms.QR.Higham19Alg12MGSSourceRate",
            f"{LS_PREFIX}.Higham20MPProse",
        ),
        (
            "NumStability.Algorithms.QR.Higham19Problem19_10",
            f"{LS_PREFIX}.Higham20CrossProductExample",
        ),
        (
            "NumStability.Algorithms.QR.Higham19Theorem5SourceClosure",
            f"{LS_PREFIX}.Higham20ZeroDeltaB",
        ),
        (
            "NumStability.Algorithms.QR.Higham19Theorem6ActualSource",
            f"{LS_PREFIX}.Higham20Theorem20_7ActualAssembly",
        ),
    }
)

BASELINE_TSV_SHA256 = (
    "32ADA469E27A971E9B0BB972F29C51E1DCBE99104A1492D4C69549C339825563"
)

OWNERSHIP_DIR = Path("docs/architecture/declaration-ownership")
DEFAULT_MANIFEST = OWNERSHIP_DIR / "lsq-ch20-ownership.tsv"
DEFAULT_ROUTES = OWNERSHIP_DIR / "lsq-ch20-routes.tsv"
DEFAULT_PRIVATE_REWRITES = OWNERSHIP_DIR / "lsq-ch20-private-rewrites.tsv"
DEFAULT_TIERS = OWNERSHIP_DIR / "lsq-ch20-tiers.tsv"

HEX_SHA256 = re.compile(r"^[0-9A-Fa-f]{64}$")
MODULE_NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$")
EDGE_KINDS = {"body", "signature"}
TIERS = {"reusable", "source", "compatibility"}
IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+([A-Za-z_][A-Za-z0-9_.]*)\s*$")


@dataclass(frozen=True)
class Declaration:
    name: str
    module: str
    kind: str
    visibility: str


@dataclass(frozen=True)
class ManifestRow:
    logical_name: str
    historical_module: str
    destination_module: str
    kind: str
    visibility: str


@dataclass(frozen=True)
class RangeRoute:
    historical_module: str
    first_line: int
    last_line: int
    destination_module: str


@dataclass(frozen=True)
class PrivateRewrite:
    logical_name: str
    historical_actual_name: str
    candidate_actual_name: str


@dataclass(frozen=True)
class DependencyEdge:
    kind: str
    source: str
    target: str


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def check_module_name(module: str, context: str) -> None:
    if not MODULE_NAME.fullmatch(module):
        raise ValueError(f"{context}: invalid Lean module name {module!r}")


def private_suffix(actual_name: str, actual_module: str) -> str:
    """Return the stable part of a Lean private name, dropping the ordinal.

    A Lean private name encodes both its owning module and an unstable
    per-scope ordinal.  Only the ordinal is genuinely volatile, so it is the
    only component removed here.
    """

    prefix = f"_private.{actual_module}."
    if not actual_name.startswith(prefix):
        raise ValueError(
            f"private name {actual_name!r} does not encode owner {actual_module!r}"
        )
    ordinal, separator, suffix = actual_name[len(prefix) :].partition(".")
    if not separator or not ordinal.isdigit() or not suffix:
        raise ValueError(f"unexpected Lean private name: {actual_name}")
    return suffix


def logical_name(actual_name: str, actual_module: str) -> str:
    """Normalize only the scope ordinal in a Lean private name.

    The owning module is retained.  This lane migrates 42 historical owners and
    the same private helper suffix occurs in more than one of them, so dropping
    the module would collapse distinct declarations onto one key.  Keeping the
    historical module makes the logical name both unique and stable, because a
    declaration's historical owner never changes.
    """

    if not actual_name.startswith("_private."):
        return actual_name
    return f"_private.{actual_module}.{private_suffix(actual_name, actual_module)}"


def read_dependency_declarations(path: Path) -> list[Declaration]:
    declarations: list[Declaration] = []
    names: set[str] = set()
    saw_format = False
    with path.open(encoding="utf-8", newline="") as stream:
        for line_number, row in enumerate(csv.reader(stream, delimiter="\t"), 1):
            if not row:
                continue
            if row == ["format", "2"]:
                if saw_format or declarations or line_number != 1:
                    raise ValueError(
                        f"{path}:{line_number}: misplaced or duplicate format row"
                    )
                saw_format = True
            elif row[0] == "declaration" and len(row) == 5:
                if not saw_format:
                    raise ValueError(f"{path}: declaration precedes format row")
                declaration = Declaration(*row[1:])
                if not all(
                    (
                        declaration.name,
                        declaration.module,
                        declaration.kind,
                        declaration.visibility,
                    )
                ):
                    raise ValueError(f"{path}:{line_number}: empty declaration field")
                if declaration.name in names:
                    raise ValueError(
                        f"{path}:{line_number}: duplicate declaration "
                        f"{declaration.name}"
                    )
                names.add(declaration.name)
                declarations.append(declaration)
            elif row[0] == "edge" and len(row) == 4:
                if not saw_format or row[1] not in EDGE_KINDS or not all(row[2:]):
                    raise ValueError(f"{path}:{line_number}: malformed edge row")
            else:
                raise ValueError(
                    f"{path}:{line_number}: malformed dependency row {row!r}"
                )
    if not saw_format:
        raise ValueError(f"{path}: dependency TSV must start with 'format\\t2'")
    return declarations


def iter_dependency_edges(path: Path) -> Iterable[DependencyEdge]:
    """Stream already schema-validated typed edges from a dependency TSV."""

    saw_format = False
    with path.open(encoding="utf-8", newline="") as stream:
        for line_number, row in enumerate(csv.reader(stream, delimiter="\t"), 1):
            if not row:
                continue
            if row == ["format", "2"]:
                if saw_format or line_number != 1:
                    raise ValueError(
                        f"{path}:{line_number}: misplaced or duplicate format row"
                    )
                saw_format = True
            elif row[0] == "declaration" and len(row) == 5:
                if not saw_format or not all(row[1:]):
                    raise ValueError(f"{path}:{line_number}: malformed declaration row")
            elif row[0] == "edge" and len(row) == 4:
                if not saw_format or row[1] not in EDGE_KINDS or not all(row[2:]):
                    raise ValueError(f"{path}:{line_number}: malformed edge row")
                yield DependencyEdge(*row[1:])
            else:
                raise ValueError(
                    f"{path}:{line_number}: malformed dependency row {row!r}"
                )
    if not saw_format:
        raise ValueError(f"{path}: dependency TSV must start with 'format\\t2'")


def selected_baseline_declarations(
    declarations: Iterable[Declaration],
    expected_counts: dict[str, int] | None = None,
) -> dict[str, Declaration]:
    counts = EXPECTED_HISTORICAL_COUNTS if expected_counts is None else expected_counts
    records: dict[str, Declaration] = {}
    raw_counts: Counter[str] = Counter()

    for declaration in declarations:
        if declaration.module not in counts:
            continue
        logical = logical_name(declaration.name, declaration.module)
        if logical in records:
            raise ValueError(f"duplicate selected logical name: {logical}")
        records[logical] = declaration
        raw_counts[declaration.module] += 1

    if raw_counts != Counter(counts):
        missing = {m: c for m, c in counts.items() if raw_counts[m] != c}
        raise ValueError(
            "historical declaration counts differ from the frozen lane selection: "
            f"{ {m: (counts[m], raw_counts[m]) for m in sorted(missing)} }"
        )
    if len(records) != sum(counts.values()):
        raise ValueError(
            f"expected {sum(counts.values())} selected declarations, found {len(records)}"
        )
    return records


def manifest_bytes(records: dict[str, ManifestRow]) -> bytes:
    rows = ["format\t1"]
    rows.extend(
        "\t".join(
            (
                row.logical_name,
                row.historical_module,
                row.destination_module,
                row.kind,
                row.visibility,
            )
        )
        for _, row in sorted(records.items())
    )
    return ("\n".join(rows) + "\n").encode("utf-8")


def destination_role(module: str) -> str:
    if module.startswith(REUSABLE_DESTINATION_PREFIXES):
        return "reusable"
    if module.startswith(SOURCE_DESTINATION_PREFIX):
        return "source"
    raise ValueError(
        "lane destination is outside the reviewed reusable/source roots: " f"{module}"
    )


def validate_manifest_shape(
    records: dict[str, ManifestRow],
    expected_counts: dict[str, int] | None = None,
) -> None:
    counts_contract = (
        EXPECTED_HISTORICAL_COUNTS if expected_counts is None else expected_counts
    )
    expected_rows = sum(counts_contract.values())
    if len(records) != expected_rows:
        raise ValueError(
            f"expected {expected_rows} ownership rows, found {len(records)}"
        )
    counts = Counter(row.historical_module for row in records.values())
    if counts != Counter(counts_contract):
        raise ValueError(
            f"manifest historical-owner counts differ: expected {counts_contract}, "
            f"found {dict(counts)}"
        )

    for logical, row in records.items():
        if logical != row.logical_name or not logical:
            raise ValueError(f"invalid manifest logical name: {logical!r}")
        check_module_name(row.historical_module, logical)
        check_module_name(row.destination_module, logical)
        if row.historical_module not in counts_contract:
            raise ValueError(
                f"{logical}: unexpected historical owner {row.historical_module}"
            )
        if row.destination_module in counts_contract:
            raise ValueError(
                f"{logical}: destination remains a historical owner: "
                f"{row.destination_module}"
            )
        if row.destination_module.startswith(LS_PREFIX + "."):
            raise ValueError(
                f"{logical}: destination stays inside the legacy family: "
                f"{row.destination_module}"
            )
        destination_role(row.destination_module)
        if not row.kind or not row.visibility:
            raise ValueError(f"{logical}: empty kind or visibility")
        if row.visibility == "private" and not logical.startswith(
            f"_private.{row.historical_module}."
        ):
            raise ValueError(
                f"{logical}: private declaration must be keyed by its historical owner "
                f"{row.historical_module}"
            )
        if row.visibility != "private" and logical.startswith("_private."):
            raise ValueError(
                f"{logical}: private-shaped name has visibility {row.visibility}"
            )


def read_manifest(
    path: Path, expected_counts: dict[str, int] | None = None
) -> dict[str, ManifestRow]:
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["format", "1"]:
        raise ValueError(f"{path}: manifest must start with 'format\\t1'")
    if any(not row for row in rows):
        raise ValueError(f"{path}: blank manifest rows are not allowed")

    records: dict[str, ManifestRow] = {}
    order: list[str] = []
    for line_number, row in enumerate(rows[1:], 2):
        if len(row) != 5:
            raise ValueError(
                f"{path}:{line_number}: expected five manifest columns, got {row!r}"
            )
        record = ManifestRow(*row)
        if record.logical_name in records:
            raise ValueError(
                f"{path}:{line_number}: duplicate logical name {record.logical_name}"
            )
        records[record.logical_name] = record
        order.append(record.logical_name)
    if order != sorted(order):
        raise ValueError(f"{path}: ownership rows must be sorted by logical name")
    validate_manifest_shape(records, expected_counts)
    return records


def write_manifest(
    path: Path,
    records: dict[str, ManifestRow],
    expected_counts: dict[str, int] | None = None,
) -> None:
    validate_manifest_shape(records, expected_counts)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(manifest_bytes(records))


def validate_manifest_against_baseline(
    records: dict[str, ManifestRow],
    baseline: dict[str, Declaration],
) -> None:
    if set(records) != set(baseline):
        missing = sorted(set(baseline) - set(records))
        extra = sorted(set(records) - set(baseline))
        raise ValueError(
            "manifest does not exactly cover the frozen selection: "
            f"missing={missing[:20]}; extra={extra[:20]}"
        )
    for logical, expected in records.items():
        actual = baseline[logical]
        expected_metadata = (
            expected.historical_module,
            expected.kind,
            expected.visibility,
        )
        actual_metadata = (actual.module, actual.kind, actual.visibility)
        if actual_metadata != expected_metadata:
            raise ValueError(
                f"{logical}: manifest expects {expected_metadata}, "
                f"baseline has {actual_metadata}"
            )


def read_routes(
    path: Path,
    historical_modules: set[str] | None = None,
) -> tuple[list[RangeRoute], dict[tuple[str, str], str]]:
    known = (
        set(EXPECTED_HISTORICAL_COUNTS)
        if historical_modules is None
        else historical_modules
    )
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["format", "1"]:
        raise ValueError(f"{path}: routes must start with 'format\\t1'")

    ranges: list[RangeRoute] = []
    exact: dict[tuple[str, str], str] = {}
    for line_number, row in enumerate(rows[1:], 2):
        if len(row) != 5:
            raise ValueError(f"{path}:{line_number}: route rows require five columns")
        route_kind, historical, third, fourth, destination = row
        if historical not in known:
            raise ValueError(
                f"{path}:{line_number}: unexpected historical module {historical}"
            )
        check_module_name(destination, f"{path}:{line_number}")
        if destination in known:
            raise ValueError(
                f"{path}:{line_number}: destination is historical: {destination}"
            )
        destination_role(destination)
        if route_kind == "range":
            try:
                first_line = int(third)
                last_line = int(fourth)
            except ValueError as error:
                raise ValueError(
                    f"{path}:{line_number}: non-integer range endpoint"
                ) from error
            if first_line < 1 or last_line < first_line:
                raise ValueError(
                    f"{path}:{line_number}: invalid inclusive range "
                    f"{first_line}-{last_line}"
                )
            ranges.append(RangeRoute(historical, first_line, last_line, destination))
        elif route_kind == "exact":
            if fourth != "-" or not third:
                raise ValueError(
                    f"{path}:{line_number}: exact route shape is "
                    "exact, historical, logical_name, -, destination"
                )
            key = (historical, third)
            if key in exact:
                raise ValueError(f"{path}:{line_number}: duplicate exact route {key}")
            exact[key] = destination
        else:
            raise ValueError(f"{path}:{line_number}: unknown route kind {route_kind!r}")

    by_module: dict[str, list[RangeRoute]] = defaultdict(list)
    for route in ranges:
        by_module[route.historical_module].append(route)
    for module, module_ranges in by_module.items():
        ordered = sorted(module_ranges, key=lambda route: route.first_line)
        for previous, current in zip(ordered, ordered[1:]):
            if current.first_line <= previous.last_line:
                raise ValueError(
                    f"{path}: overlapping {module} ranges "
                    f"{previous.first_line}-{previous.last_line} and "
                    f"{current.first_line}-{current.last_line}"
                )
    if not ranges and not exact:
        raise ValueError(f"{path}: route map is empty")
    return ranges, exact


def default_ilean_path(project_root: Path, module: str) -> Path:
    return project_root / ".lake/build/lib/lean" / (module.replace(".", "/") + ".ilean")


def parse_ilean_overrides(values: list[str]) -> dict[str, Path]:
    result: dict[str, Path] = {}
    for value in values:
        module, separator, raw_path = value.partition("=")
        if not separator or not module or not raw_path:
            raise ValueError(f"invalid --ilean {value!r}; expected HISTORICAL_MODULE=PATH")
        if module in result:
            raise ValueError(f"duplicate --ilean override for {module}")
        check_module_name(module, "--ilean")
        result[module] = Path(raw_path)
    return result


def read_ilean_roots(path: Path, expected_module: str) -> dict[str, int]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as error:
        raise ValueError(f"invalid .ilean JSON {path}: {error}") from error
    actual_module = payload.get("module")
    if actual_module != expected_module:
        raise ValueError(
            f"{path}: expected .ilean owner {expected_module}, found {actual_module!r}"
        )
    decls = payload.get("decls")
    if not isinstance(decls, dict):
        raise ValueError(f"{path}: .ilean lacks a declaration map")
    roots: dict[str, int] = {}
    for name, source_range in decls.items():
        if (
            not isinstance(name, str)
            or not isinstance(source_range, list)
            or not source_range
            or not isinstance(source_range[0], int)
        ):
            raise ValueError(f"{path}: malformed declaration source range")
        # Lean info-tree lines are zero-based; route files use editor-facing,
        # one-based inclusive source lines.
        roots[name] = source_range[0] + 1
    return roots


def generate_manifest(
    baseline: dict[str, Declaration],
    routes_path: Path,
    project_root: Path,
    ilean_overrides: dict[str, Path],
    expected_counts: dict[str, int] | None = None,
) -> dict[str, ManifestRow]:
    known = (
        set(EXPECTED_HISTORICAL_COUNTS)
        if expected_counts is None
        else set(expected_counts)
    )
    ranges, exact_routes = read_routes(routes_path, known)
    ranges_by_module: dict[str, list[RangeRoute]] = defaultdict(list)
    for route in ranges:
        ranges_by_module[route.historical_module].append(route)

    roots_by_module: dict[str, dict[str, int]] = {}
    for module in ranges_by_module:
        ilean_path = ilean_overrides.get(module, default_ilean_path(project_root, module))
        roots_by_module[module] = read_ilean_roots(ilean_path, module)

    exact_used: set[tuple[str, str]] = set()
    range_use: Counter[RangeRoute] = Counter()
    generated: dict[str, ManifestRow] = {}

    for logical, declaration in baseline.items():
        exact_key = (declaration.module, logical)
        if exact_key in exact_routes:
            destination = exact_routes[exact_key]
            exact_used.add(exact_key)
        else:
            candidates = [
                root
                for root in roots_by_module.get(declaration.module, {})
                if declaration.name == root or declaration.name.startswith(root + ".")
            ]
            if not candidates:
                raise ValueError(
                    f"unrouted semantic declaration {logical}; add an exact route"
                )
            root = max(candidates, key=len)
            source_line = roots_by_module[declaration.module][root]
            matching_ranges = [
                route
                for route in ranges_by_module[declaration.module]
                if route.first_line <= source_line <= route.last_line
            ]
            if len(matching_ranges) != 1:
                raise ValueError(
                    f"{logical}: source root {root} at line {source_line} "
                    f"matches {len(matching_ranges)} ranges"
                )
            route = matching_ranges[0]
            range_use[route] += 1
            destination = route.destination_module

        generated[logical] = ManifestRow(
            logical,
            declaration.module,
            destination,
            declaration.kind,
            declaration.visibility,
        )

    unused_exact = sorted(set(exact_routes) - exact_used)
    if unused_exact:
        raise ValueError(f"unused exact routes: {unused_exact[:20]}")
    unused_ranges = [route for route in ranges if not range_use[route]]
    if unused_ranges:
        raise ValueError(f"ranges route no selected declarations: {unused_ranges[:20]}")
    validate_manifest_shape(generated, expected_counts)
    return generated


def read_tiers(path: Path) -> dict[str, str]:
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["format", "1"]:
        raise ValueError(f"{path}: tier manifest must start with 'format\\t1'")
    tiers: dict[str, str] = {}
    order: list[str] = []
    for line_number, row in enumerate(rows[1:], 2):
        if len(row) != 2:
            raise ValueError(f"{path}:{line_number}: expected module and tier columns")
        module, tier = row
        check_module_name(module, f"{path}:{line_number}")
        if tier not in TIERS:
            raise ValueError(
                f"{path}:{line_number}: tier {tier!r} is not one of {sorted(TIERS)}"
            )
        if module in tiers:
            raise ValueError(f"{path}:{line_number}: duplicate tier row for {module}")
        tiers[module] = tier
        order.append(module)
    if order != sorted(order):
        raise ValueError(f"{path}: tier rows must be sorted by module")
    if not tiers:
        raise ValueError(f"{path}: tier manifest is empty")
    return tiers


def validate_tier_coverage(
    tiers: dict[str, str],
    records: dict[str, ManifestRow],
    structural_modules: set[str],
) -> None:
    """Require one proposed tier for every final lane production module."""

    destinations = {row.destination_module for row in records.values()}
    required = destinations | structural_modules | PRESERVED_SOURCE_LEAVES
    missing = sorted(required - set(tiers))
    extra = sorted(set(tiers) - required)
    if missing or extra:
        raise ValueError(
            f"proposed tier coverage is not exactly the lane surface: "
            f"missing={missing[:20]}; extra={extra[:20]}"
        )
    for module, tier in sorted(tiers.items()):
        if module in destinations:
            role = destination_role(module)
            if tier != role:
                raise ValueError(
                    f"{module}: proposed tier {tier} contradicts destination role {role}"
                )
        elif module in structural_modules:
            if module.startswith(SOURCE_DESTINATION_PREFIX) or module == SOURCE_ROOT:
                if tier != "source":
                    raise ValueError(
                        f"{module}: canonical source aggregate must propose tier source"
                    )
            elif tier != "compatibility":
                raise ValueError(
                    f"{module}: historical wrapper must propose tier compatibility"
                )
        elif tier != "source":
            raise ValueError(f"{module}: preserved Chapter 20 leaf must propose source")


def baseline_actual_to_logical(baseline: dict[str, Declaration]) -> dict[str, str]:
    result = {declaration.name: logical for logical, declaration in baseline.items()}
    if len(result) != len(baseline):
        raise ValueError("baseline selected-name map is not one-to-one")
    return result


def destination_sccs(graph: dict[str, set[str]]) -> list[list[str]]:
    """Return nontrivial strongly connected components deterministically."""

    next_index = 0
    indices: dict[str, int] = {}
    lowlinks: dict[str, int] = {}
    stack: list[str] = []
    on_stack: set[str] = set()
    components: list[list[str]] = []

    def visit(root: str) -> None:
        nonlocal next_index
        work: list[tuple[str, list[str]]] = [(root, sorted(graph[root]))]
        indices[root] = lowlinks[root] = next_index
        next_index += 1
        stack.append(root)
        on_stack.add(root)
        while work:
            owner, pending = work[-1]
            if pending:
                dependency = pending.pop()
                if dependency not in indices:
                    indices[dependency] = lowlinks[dependency] = next_index
                    next_index += 1
                    stack.append(dependency)
                    on_stack.add(dependency)
                    work.append((dependency, sorted(graph[dependency])))
                elif dependency in on_stack:
                    lowlinks[owner] = min(lowlinks[owner], indices[dependency])
                continue
            work.pop()
            if work:
                parent = work[-1][0]
                lowlinks[parent] = min(lowlinks[parent], lowlinks[owner])
            if lowlinks[owner] == indices[owner]:
                component: list[str] = []
                while True:
                    member = stack.pop()
                    on_stack.remove(member)
                    component.append(member)
                    if member == owner:
                        break
                if len(component) > 1:
                    components.append(sorted(component))

    for owner in sorted(graph):
        if owner not in indices:
            visit(owner)
    return sorted(components)


def validate_destination_graph(
    dependency_tsv: Path,
    declarations: list[Declaration],
    actual_to_logical: dict[str, str],
    records: dict[str, ManifestRow],
) -> tuple[int, int]:
    """Enforce the selected declaration DAG and the reusable/source boundary."""

    module_by_name = {
        declaration.name: declaration.module for declaration in declarations
    }
    owners = {row.destination_module for row in records.values()}
    graph: dict[str, set[str]] = {owner: set() for owner in owners}
    witnesses: dict[tuple[str, str], DependencyEdge] = {}
    forbidden: list[str] = []

    for edge in iter_dependency_edges(dependency_tsv):
        source_logical = actual_to_logical.get(edge.source)
        if source_logical is None:
            continue
        source_owner = records[source_logical].destination_module
        source_role = destination_role(source_owner)

        target_logical = actual_to_logical.get(edge.target)
        if target_logical is not None:
            target_owner = records[target_logical].destination_module
            target_role = destination_role(target_owner)
            if source_owner != target_owner:
                graph[source_owner].add(target_owner)
                witnesses.setdefault((source_owner, target_owner), edge)
            if source_role == "reusable" and target_role == "source":
                forbidden.append(
                    f"{source_owner} -> {target_owner} via {edge.kind} "
                    f"{edge.source} -> {edge.target}"
                )
            continue

        target_module = module_by_name.get(edge.target)
        if source_role != "reusable" or target_module is None:
            continue
        if (
            target_module.startswith(SOURCE_DESTINATION_PREFIX)
            or target_module == SOURCE_ROOT
            or target_module.startswith("NumStability.Source.")
            or target_module.startswith(HIGHAM_COMPAT_ROOT)
            or target_module.startswith("NumStability.Higham.")
            or target_module == CHAPTER_SEVEN
            or target_module.startswith(LS_PREFIX)
        ):
            forbidden.append(
                f"{source_owner} -> external {target_module} via {edge.kind} "
                f"{edge.source} -> {edge.target}"
            )

    if forbidden:
        raise ValueError(
            "reusable destinations depend on source, compatibility, legacy, or "
            "Chapter 7 declarations: " + "; ".join(sorted(forbidden)[:20])
        )

    components = destination_sccs(graph)
    if components:
        component = components[0]
        members = set(component)
        component_witnesses: list[str] = []
        for source in component:
            for target in sorted(graph[source] & members):
                edge = witnesses[(source, target)]
                component_witnesses.append(
                    f"{source} -> {target} via {edge.kind} {edge.source} -> {edge.target}"
                )
        raise ValueError(
            f"destination ownership graph contains a cycle among {component}: "
            + "; ".join(component_witnesses[:20])
        )

    return len(owners), sum(len(dependencies) for dependencies in graph.values())


def read_private_rewrites(
    path: Path,
    records: dict[str, ManifestRow],
    baseline: dict[str, Declaration],
    required_logicals: set[str] | None = None,
) -> dict[str, PrivateRewrite]:
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["format", "1"]:
        raise ValueError(f"{path}: private rewrites must start with 'format\\t1'")

    rewrites: dict[str, PrivateRewrite] = {}
    candidate_names: set[str] = set()
    order: list[str] = []
    for line_number, row in enumerate(rows[1:], 2):
        if len(row) != 3:
            raise ValueError(
                f"{path}:{line_number}: private rewrites require three columns"
            )
        rewrite = PrivateRewrite(*row)
        logical = rewrite.logical_name
        if logical in rewrites:
            raise ValueError(f"{path}:{line_number}: duplicate rewrite {logical}")
        if rewrite.candidate_actual_name in candidate_names:
            raise ValueError(
                f"{path}:{line_number}: duplicate candidate private name "
                f"{rewrite.candidate_actual_name}"
            )
        rewrites[logical] = rewrite
        candidate_names.add(rewrite.candidate_actual_name)
        order.append(logical)
    if order != sorted(order):
        raise ValueError(f"{path}: rewrite rows must be sorted by logical name")

    all_private_logicals = {
        logical for logical, row in records.items() if row.visibility == "private"
    }
    expected_logicals = (
        all_private_logicals
        if required_logicals is None
        else all_private_logicals & required_logicals
    )
    if set(rewrites) != expected_logicals:
        missing = sorted(expected_logicals - set(rewrites))
        extra = sorted(set(rewrites) - expected_logicals)
        raise ValueError(
            f"private rewrite coverage differs: missing={missing[:20]}; extra={extra[:20]}"
        )
    for logical, rewrite in rewrites.items():
        historical = baseline[logical]
        destination = records[logical].destination_module
        if rewrite.historical_actual_name != historical.name:
            raise ValueError(
                f"{logical}: expected historical private name {historical.name}, "
                f"found {rewrite.historical_actual_name}"
            )
        expected_suffix = private_suffix(historical.name, historical.module)
        try:
            candidate_suffix = private_suffix(
                rewrite.candidate_actual_name, destination
            )
        except ValueError as error:
            raise ValueError(
                f"{logical}: candidate private name does not encode destination "
                f"{destination}: {rewrite.candidate_actual_name}"
            ) from error
        if candidate_suffix != expected_suffix:
            raise ValueError(
                f"{logical}: candidate private name changes the declaration suffix: "
                f"expected {expected_suffix}, found {candidate_suffix}"
            )
    return rewrites


def check_candidate_ownership(
    records: dict[str, ManifestRow],
    baseline: dict[str, Declaration],
    declarations: list[Declaration],
    rewrites: dict[str, PrivateRewrite],
    completed_destinations: set[str] | None = None,
) -> dict[str, str]:
    completed = (
        {row.destination_module for row in records.values()}
        if completed_destinations is None
        else completed_destinations
    )
    declaration_by_name = {
        declaration.name: declaration for declaration in declarations
    }
    candidate_actual_to_logical: dict[str, str] = {}
    expected_actual_by_logical: dict[str, str] = {}

    for logical, expected in records.items():
        is_completed = expected.destination_module in completed
        if expected.visibility == "private" and is_completed:
            candidate_name = rewrites[logical].candidate_actual_name
        else:
            candidate_name = baseline[logical].name
        expected_actual_by_logical[logical] = candidate_name
        actual = declaration_by_name.get(candidate_name)
        if actual is None:
            raise ValueError(
                f"{logical}: candidate declaration is missing ({candidate_name})"
            )
        actual_metadata = (actual.module, actual.kind, actual.visibility)
        expected_metadata = (
            (
                expected.destination_module
                if is_completed
                else expected.historical_module
            ),
            expected.kind,
            expected.visibility,
        )
        if actual_metadata != expected_metadata:
            raise ValueError(
                f"{logical}: expected destination metadata {expected_metadata}, "
                f"found {actual_metadata}"
            )
        candidate_actual_to_logical[candidate_name] = logical

    # Reject alternate encodings: any declaration living in a selected module
    # whose actual name is not the stage-appropriate name of some record.  Public
    # names are global and already fail the exact metadata check above; this scan
    # is the one-to-one guard for module-encoded private declarations.
    selected_modules = set(EXPECTED_HISTORICAL_COUNTS) | {
        row.destination_module for row in records.values()
    }
    accepted = set(expected_actual_by_logical.values())
    suffix_owners: dict[tuple[str, str], str] = {}
    for logical, row in records.items():
        if row.visibility != "private":
            continue
        historical_name = baseline[logical].name
        suffix = private_suffix(historical_name, row.historical_module)
        suffix_owners[(row.historical_module, suffix)] = logical
        suffix_owners[(row.destination_module, suffix)] = logical

    alternates: list[str] = []
    for declaration in declarations:
        if declaration.module not in selected_modules:
            continue
        if not declaration.name.startswith("_private."):
            continue
        try:
            suffix = private_suffix(declaration.name, declaration.module)
        except ValueError:
            continue
        owner = suffix_owners.get((declaration.module, suffix))
        if owner is not None and declaration.name not in accepted:
            alternates.append(f"{declaration.module}:{declaration.name}")
    if alternates:
        raise ValueError(
            "selected declarations have alternate or stage-inappropriate owners: "
            + ", ".join(sorted(alternates)[:20])
        )
    if len(candidate_actual_to_logical) != len(records):
        raise ValueError("candidate selected-name map is not one-to-one")
    return candidate_actual_to_logical


def strip_lean_comments(lines: list[str]) -> list[str]:
    """Blank out block and line comments while preserving line structure."""

    result: list[str] = []
    depth = 0
    for line in lines:
        out: list[str] = []
        index = 0
        while index < len(line):
            if depth:
                if line.startswith("/-", index):
                    depth += 1
                    index += 2
                elif line.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
                continue
            if line.startswith("--", index):
                break
            if line.startswith("/-", index):
                depth += 1
                index += 2
                continue
            out.append(line[index])
            index += 1
        result.append("".join(out))
    if depth:
        raise ValueError("unterminated Lean block comment")
    return result


def module_path(project_root: Path, module: str) -> Path:
    return project_root / (module.replace(".", "/") + ".lean")


def has_top_level_module_docstring(source: str) -> bool:
    """Recognize a real top-level ``/-!`` comment, not text inside a comment."""

    depth = 0
    line_comment = False
    index = 0
    while index < len(source):
        if line_comment:
            if source[index] in "\r\n":
                line_comment = False
            index += 1
        elif depth:
            if source.startswith("/-", index):
                depth += 1
                index += 2
            elif source.startswith("-/", index):
                depth -= 1
                index += 2
            else:
                index += 1
        elif source.startswith("--", index):
            line_comment = True
            index += 2
        elif source.startswith("/-!", index):
            return True
        elif source.startswith("/-", index):
            depth = 1
            index += 2
        else:
            index += 1
    return False


def validate_import_sequence(
    path: Path, imports: list[str], expected: tuple[str, ...] | None
) -> tuple[str, ...]:
    actual = tuple(imports)
    duplicates = sorted(
        imported for imported, count in Counter(imports).items() if count > 1
    )
    if duplicates:
        raise ValueError(
            f"structural module has duplicate imports in {path}: {duplicates}"
        )
    ordered = tuple(sorted(imports))
    if actual != ordered:
        raise ValueError(
            f"structural module imports are not sorted in {path}: "
            f"found {actual}, expected {ordered}"
        )
    if expected is not None and actual != expected:
        raise ValueError(
            f"structural import contract differs for {path}: "
            f"expected {expected}, found {actual}"
        )
    return actual


def validate_import_only_module(
    project_root: Path,
    module: str,
    expected: tuple[str, ...] | None = None,
) -> tuple[str, ...]:
    path = module_path(project_root, module)
    if not path.is_file():
        raise ValueError(f"missing completed structural module: {path}")
    source = path.read_text(encoding="utf-8")
    if not has_top_level_module_docstring(source):
        raise ValueError(f"structural module lacks a module docstring: {path}")
    imports: list[str] = []
    source_lines = source.splitlines()
    for original, code in zip(
        source_lines, strip_lean_comments(source_lines), strict=True
    ):
        stripped = code.strip()
        if not stripped:
            continue
        fields = stripped.split()
        if len(fields) == 2 and fields[0] == "import":
            imported = fields[1]
        elif len(fields) == 3 and fields[:2] == ["public", "import"]:
            imported = fields[2]
        else:
            raise ValueError(
                f"structural module contains non-import code in {path}: {original!r}"
            )
        check_module_name(imported, f"{path}: import")
        imports.append(imported)
    if not imports:
        raise ValueError(f"structural module has no imports: {path}")
    return validate_import_sequence(path, imports, expected)


def read_structural_modules(path: Path) -> set[str]:
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["format", "1"]:
        raise ValueError(f"{path}: structural modules must start with 'format\\t1'")
    modules: set[str] = set()
    order: list[str] = []
    for line_number, row in enumerate(rows[1:], 2):
        if len(row) != 1:
            raise ValueError(
                f"{path}:{line_number}: expected one structural-module column"
            )
        module = row[0]
        check_module_name(module, f"{path}:{line_number}")
        if module in modules:
            raise ValueError(f"{path}:{line_number}: duplicate module {module}")
        modules.add(module)
        order.append(module)
    if order != sorted(order):
        raise ValueError(f"{path}: structural modules must be sorted")
    return modules


def read_completed_destinations(path: Path) -> set[str]:
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["format", "1"]:
        raise ValueError(f"{path}: completed destinations must start with 'format\\t1'")
    destinations: list[str] = []
    for line_number, row in enumerate(rows[1:], 2):
        if len(row) != 1:
            raise ValueError(f"{path}:{line_number}: expected one completed destination")
        destination = row[0]
        check_module_name(destination, f"{path}:{line_number}")
        destinations.append(destination)
    if not destinations:
        raise ValueError(f"{path}: completed destination set is empty")
    if len(destinations) != len(set(destinations)):
        raise ValueError(f"{path}: duplicate completed destination")
    if destinations != sorted(destinations):
        raise ValueError(f"{path}: completed destinations must be sorted")
    return set(destinations)


def validate_structural_modules(
    project_root: Path,
    declarations: list[Declaration],
    structural_modules: set[str],
    contract: dict[str, tuple[str, ...]] | None,
) -> None:
    offenders = [
        declaration
        for declaration in declarations
        if declaration.module in structural_modules
    ]
    if offenders:
        raise ValueError(
            "completed wrappers or aggregates own compiled declarations: "
            + ", ".join(
                f"{declaration.module}:{declaration.name}"
                for declaration in offenders[:20]
            )
        )
    for module in sorted(structural_modules):
        expected = contract[module] if contract is not None else None
        validate_import_only_module(project_root, module, expected)


def read_module_imports(project_root: Path) -> dict[str, list[str]]:
    """Read the direct-import graph of every tracked project Lean module."""

    graph: dict[str, list[str]] = {}
    for root in ("NumStability", "NumStabilityTest"):
        base = project_root / root
        if not base.is_dir():
            continue
        for path in sorted(base.rglob("*.lean")):
            module = (
                path.relative_to(project_root)
                .with_suffix("")
                .as_posix()
                .replace("/", ".")
            )
            lines = path.read_text(encoding="utf-8").splitlines()
            imports: list[str] = []
            for code in strip_lean_comments(lines):
                match = IMPORT_RE.match(code)
                if match:
                    imports.append(match.group(1))
            graph[module] = imports
        umbrella = project_root / f"{root}.lean"
        if umbrella.is_file():
            lines = umbrella.read_text(encoding="utf-8").splitlines()
            graph[root] = [
                match.group(1)
                for match in (IMPORT_RE.match(code) for code in strip_lean_comments(lines))
                if match
            ]
    return graph


def forbidden_for_reusable(module: str) -> bool:
    return (
        module == SOURCE_ROOT
        or module.startswith("NumStability.Source.")
        or module.startswith("NumStability.Higham.")
        or module == CHAPTER_SEVEN
        or module == LS_PREFIX
        or module.startswith(LS_PREFIX + ".")
    )


def validate_reusable_isolation(
    project_root: Path,
    records: dict[str, ManifestRow],
    import_graph: dict[str, list[str]] | None = None,
) -> int:
    """Require that no reusable destination transitively reaches forbidden roots."""

    graph = read_module_imports(project_root) if import_graph is None else import_graph
    reusable = sorted(
        {
            row.destination_module
            for row in records.values()
            if destination_role(row.destination_module) == "reusable"
        }
    )
    violations: list[str] = []
    for start in reusable:
        if start not in graph:
            raise ValueError(f"reusable destination has no source file: {start}")
        seen = {start}
        queue = deque([(start, [start])])
        while queue:
            module, path = queue.popleft()
            for imported in graph.get(module, []):
                if forbidden_for_reusable(imported):
                    violations.append(" -> ".join(path + [imported]))
                    continue
                if imported in seen or imported not in graph:
                    continue
                seen.add(imported)
                queue.append((imported, path + [imported]))
    if violations:
        raise ValueError(
            "reusable destinations transitively reach source, compatibility, "
            "legacy, or Chapter 7 modules: " + "; ".join(sorted(violations)[:20])
        )
    return len(reusable)


def transitive_imports(graph: dict[str, list[str]], start: str) -> set[str]:
    seen: set[str] = set()
    queue = deque(graph.get(start, []))
    while queue:
        module = queue.popleft()
        if module in seen:
            continue
        seen.add(module)
        queue.extend(graph.get(module, []))
    return seen


def validate_cross_lane_contract(
    project_root: Path,
    records: dict[str, ManifestRow],
    import_graph: dict[str, list[str]] | None = None,
    ls_to_qr: frozenset[tuple[str, str]] | None = None,
    qr_to_ls: frozenset[tuple[str, str]] | None = None,
) -> tuple[int, int]:
    """Require the frozen 19 LS-to-QR and four QR-to-LS dependencies."""

    graph = read_module_imports(project_root) if import_graph is None else import_graph
    forward = FROZEN_LS_TO_QR if ls_to_qr is None else ls_to_qr
    reverse = FROZEN_QR_TO_LS if qr_to_ls is None else qr_to_ls

    owners_by_historical: dict[str, set[str]] = defaultdict(set)
    for row in records.values():
        owners_by_historical[row.historical_module].add(row.destination_module)

    missing_forward: list[str] = []
    for historical, target in sorted(forward):
        owners = owners_by_historical.get(historical, set())
        if not owners:
            missing_forward.append(f"{historical} has no migrated owner for {target}")
            continue
        direct = [owner for owner in sorted(owners) if target in graph.get(owner, [])]
        if not direct:
            missing_forward.append(
                f"no destination of {historical} directly imports {target}"
            )
            continue
        if target not in transitive_imports(graph, historical) and historical in graph:
            missing_forward.append(
                f"historical path {historical} no longer reaches {target}"
            )
    if missing_forward:
        raise ValueError(
            "frozen LS-to-QR dependencies were not preserved after owner "
            "normalization: " + "; ".join(missing_forward[:20])
        )

    missing_reverse: list[str] = []
    for consumer, historical in sorted(reverse):
        if consumer not in graph:
            missing_reverse.append(f"missing QR consumer module {consumer}")
            continue
        if historical not in graph.get(consumer, []):
            missing_reverse.append(
                f"{consumer} no longer directly imports historical {historical}"
            )
    if missing_reverse:
        raise ValueError(
            "frozen QR-to-LS consumers lost their historical least-squares "
            "imports: " + "; ".join(missing_reverse[:20])
        )
    return len(forward), len(reverse)


def normalized_graph_delta(
    baseline_tsv: Path,
    candidate_tsv: Path,
    baseline: dict[str, Declaration],
    candidate_actual_to_logical: dict[str, str],
    records: dict[str, ManifestRow],
) -> Counter[str]:
    """Return baseline rows minus normalized candidate rows as a multiset."""

    candidate_to_baseline_name = {
        candidate: baseline[logical].name
        for candidate, logical in candidate_actual_to_logical.items()
    }
    candidate_to_historical_module = {
        candidate: records[logical].historical_module
        for candidate, logical in candidate_actual_to_logical.items()
    }

    delta: Counter[str] = Counter()
    with baseline_tsv.open(encoding="utf-8") as stream:
        for raw in stream:
            delta[raw.rstrip("\r\n")] += 1

    with candidate_tsv.open(encoding="utf-8") as stream:
        for raw in stream:
            fields = raw.rstrip("\r\n").split("\t")
            if (
                len(fields) == 5
                and fields[0] == "declaration"
                and fields[1] in candidate_to_baseline_name
            ):
                candidate_name = fields[1]
                fields[1] = candidate_to_baseline_name[candidate_name]
                fields[2] = candidate_to_historical_module[candidate_name]
            elif len(fields) == 4 and fields[0] == "edge":
                fields[2] = candidate_to_baseline_name.get(fields[2], fields[2])
                fields[3] = candidate_to_baseline_name.get(fields[3], fields[3])
            row = "\t".join(fields)
            delta[row] -= 1
            if delta[row] == 0:
                del delta[row]

    return delta


def validate_normalized_graph_delta(delta: Counter[str]) -> None:
    if not delta:
        return
    missing = sum(count for count in delta.values() if count > 0)
    extra = -sum(count for count in delta.values() if count < 0)
    details = "; ".join(f"{count:+d} {row}" for row, count in sorted(delta.items())[:20])
    raise ValueError(
        "normalized contracted graph differs from the frozen lane baseline: "
        f"missing={missing}, extra={extra}; {details}"
    )


def compare_full_graph(
    baseline_tsv: Path,
    candidate_tsv: Path,
    baseline: dict[str, Declaration],
    candidate_actual_to_logical: dict[str, str],
    records: dict[str, ManifestRow],
    expected_baseline_sha256: str | None = BASELINE_TSV_SHA256,
) -> None:
    """Require the exact contracted graph after ownership normalization."""

    if expected_baseline_sha256 is not None:
        if sha256_file(baseline_tsv) != expected_baseline_sha256:
            raise ValueError("baseline TSV hash differs from the frozen lane input")
    delta = normalized_graph_delta(
        baseline_tsv, candidate_tsv, baseline, candidate_actual_to_logical, records
    )
    validate_normalized_graph_delta(delta)


def validate_expected_manifest_digest(
    records: dict[str, ManifestRow], expected: str | None
) -> str:
    digest = sha256_bytes(manifest_bytes(records))
    if expected is not None:
        if not HEX_SHA256.fullmatch(expected):
            raise ValueError("--expected-manifest-sha256 must contain 64 hex digits")
        if digest != expected.upper():
            raise ValueError(
                f"canonical manifest hash differs: expected {expected.upper()}, "
                f"found {digest}"
            )
    return digest


# ----------------------------------------------------------------------------
# Self-test
# ----------------------------------------------------------------------------

SELF_HISTORICAL_A = f"{LS_PREFIX}.LSQRSolve"
SELF_HISTORICAL_B = f"{LS_PREFIX}.LSPerturbation"
SELF_REUSABLE = f"{REUSABLE_ALGORITHM_ROOT}.Residual"
SELF_ANALYSIS = f"{REUSABLE_ANALYSIS_ROOT}.Wedin"
SELF_SOURCE = f"{SOURCE_ROOT}.Theorem03"
SELF_COUNTS = {SELF_HISTORICAL_A: 3, SELF_HISTORICAL_B: 2}
SELF_PRIVATE_LOGICAL = f"_private.{SELF_HISTORICAL_A}.NumStability.lsHelper"


def _self_declarations() -> list[Declaration]:
    return [
        Declaration("NumStability.lsResidual", SELF_HISTORICAL_A, "definition", "public"),
        Declaration(
            "NumStability.lsResidual_permuteRows", SELF_HISTORICAL_A, "theorem", "public"
        ),
        Declaration(
            f"_private.{SELF_HISTORICAL_A}.0.NumStability.lsHelper",
            SELF_HISTORICAL_A,
            "theorem",
            "private",
        ),
        Declaration(
            "NumStability.wedinLemma20_11_bound", SELF_HISTORICAL_B, "theorem", "public"
        ),
        Declaration(
            "NumStability.theorem20_3_source", SELF_HISTORICAL_B, "theorem", "public"
        ),
        Declaration("NumStability.qrExternal", "NumStability.Algorithms.QR.QRSolve", "theorem", "public"),
    ]


def _self_stream(declarations: list[Declaration], edges: list[DependencyEdge]) -> str:
    rows = ["format\t2"]
    rows.extend(
        "\t".join(("declaration", d.name, d.module, d.kind, d.visibility))
        for d in declarations
    )
    rows.extend("\t".join(("edge", e.kind, e.source, e.target)) for e in edges)
    return "\n".join(rows) + "\n"


def _self_edges() -> list[DependencyEdge]:
    return [
        DependencyEdge("signature", "NumStability.lsResidual_permuteRows", "NumStability.lsResidual"),
        DependencyEdge(
            "body",
            "NumStability.lsResidual_permuteRows",
            f"_private.{SELF_HISTORICAL_A}.0.NumStability.lsHelper",
        ),
        DependencyEdge("body", "NumStability.theorem20_3_source", "NumStability.lsResidual"),
        DependencyEdge(
            "signature", "NumStability.wedinLemma20_11_bound", "NumStability.wedinLemma20_11_bound"
        ),
        DependencyEdge("body", "NumStability.lsResidual", "NumStability.qrExternal"),
    ]


def _self_manifest() -> dict[str, ManifestRow]:
    return {
        "NumStability.lsResidual": ManifestRow(
            "NumStability.lsResidual", SELF_HISTORICAL_A, SELF_REUSABLE, "definition", "public"
        ),
        "NumStability.lsResidual_permuteRows": ManifestRow(
            "NumStability.lsResidual_permuteRows",
            SELF_HISTORICAL_A,
            SELF_REUSABLE,
            "theorem",
            "public",
        ),
        SELF_PRIVATE_LOGICAL: ManifestRow(
            SELF_PRIVATE_LOGICAL,
            SELF_HISTORICAL_A,
            SELF_REUSABLE,
            "theorem",
            "private",
        ),
        "NumStability.wedinLemma20_11_bound": ManifestRow(
            "NumStability.wedinLemma20_11_bound",
            SELF_HISTORICAL_B,
            SELF_ANALYSIS,
            "theorem",
            "public",
        ),
        "NumStability.theorem20_3_source": ManifestRow(
            "NumStability.theorem20_3_source",
            SELF_HISTORICAL_B,
            SELF_SOURCE,
            "theorem",
            "public",
        ),
    }


def run_self_test() -> None:
    def expect_value_error(action: Callable[[], object], label: str) -> None:
        try:
            action()
        except ValueError:
            return
        raise AssertionError(f"self-test did not reject {label}")

    declarations = _self_declarations()
    edges = _self_edges()
    records = _self_manifest()
    baseline = selected_baseline_declarations(declarations, SELF_COUNTS)
    assert len(baseline) == 5, baseline
    validate_manifest_shape(records, SELF_COUNTS)
    validate_manifest_against_baseline(records, baseline)

    assert logical_name("NumStability.x", SELF_HISTORICAL_A) == "NumStability.x"
    assert (
        logical_name(f"_private.{SELF_HISTORICAL_A}.0.NumStability.lsHelper", SELF_HISTORICAL_A)
        == SELF_PRIVATE_LOGICAL
    )
    expect_value_error(
        lambda: logical_name(f"_private.{SELF_HISTORICAL_B}.0.NumStability.x", SELF_HISTORICAL_A),
        "a private name that does not encode its owner",
    )

    # 1. Missing declaration.
    expect_value_error(
        lambda: selected_baseline_declarations(declarations[:-2], SELF_COUNTS),
        "a missing historical declaration",
    )
    # 2. Duplicated declaration.
    expect_value_error(
        lambda: selected_baseline_declarations(declarations + [declarations[0]], SELF_COUNTS),
        "a duplicated historical declaration",
    )
    # 3. Public name drift.
    drifted_names = [
        Declaration("NumStability.lsResidualRenamed", d.module, d.kind, d.visibility)
        if d.name == "NumStability.lsResidual"
        else d
        for d in declarations
    ]
    expect_value_error(
        lambda: validate_manifest_against_baseline(
            records, selected_baseline_declarations(drifted_names, SELF_COUNTS)
        ),
        "public declaration name drift",
    )
    # 4. Kind (signature shape) drift.
    drifted_kind = [
        Declaration(d.name, d.module, "theorem" if d.kind == "definition" else d.kind, d.visibility)
        for d in declarations
    ]
    expect_value_error(
        lambda: validate_manifest_against_baseline(
            records, selected_baseline_declarations(drifted_kind, SELF_COUNTS)
        ),
        "declaration kind drift",
    )
    # 5. Visibility drift.
    drifted_visibility = dict(records)
    drifted_visibility["NumStability.lsResidual"] = ManifestRow(
        "NumStability.lsResidual", SELF_HISTORICAL_A, SELF_REUSABLE, "definition", "private"
    )
    expect_value_error(
        lambda: validate_manifest_shape(drifted_visibility, SELF_COUNTS),
        "a private visibility without a normalized private name",
    )
    # 6. Destination that stays in the legacy family.
    legacy_destination = dict(records)
    legacy_destination["NumStability.lsResidual"] = ManifestRow(
        "NumStability.lsResidual",
        SELF_HISTORICAL_A,
        f"{LS_PREFIX}.LSResidual",
        "definition",
        "public",
    )
    expect_value_error(
        lambda: validate_manifest_shape(legacy_destination, SELF_COUNTS),
        "a destination inside the legacy least-squares family",
    )

    with tempfile.TemporaryDirectory() as raw:
        root = Path(raw)
        baseline_tsv = root / "baseline.tsv"
        baseline_tsv.write_text(_self_stream(declarations, edges), encoding="utf-8")

        actual_to_logical = baseline_actual_to_logical(baseline)
        owners, edge_count = validate_destination_graph(
            baseline_tsv, declarations, actual_to_logical, records
        )
        assert owners == 3, owners
        assert edge_count >= 1, edge_count

        # 7. Forbidden reusable -> source declaration edge.
        inverted = dict(records)
        inverted["NumStability.theorem20_3_source"] = ManifestRow(
            "NumStability.theorem20_3_source",
            SELF_HISTORICAL_B,
            SELF_SOURCE,
            "theorem",
            "public",
        )
        inverted["NumStability.lsResidual"] = ManifestRow(
            "NumStability.lsResidual", SELF_HISTORICAL_A, SELF_REUSABLE, "definition", "public"
        )
        forbidden_tsv = root / "forbidden.tsv"
        forbidden_tsv.write_text(
            _self_stream(
                declarations,
                edges
                + [
                    DependencyEdge(
                        "body", "NumStability.lsResidual", "NumStability.theorem20_3_source"
                    )
                ],
            ),
            encoding="utf-8",
        )
        expect_value_error(
            lambda: validate_destination_graph(
                forbidden_tsv, declarations, actual_to_logical, inverted
            ),
            "a reusable destination depending on a source declaration",
        )

        # 8. Owner cycle.
        cyclic = dict(records)
        cyclic["NumStability.wedinLemma20_11_bound"] = ManifestRow(
            "NumStability.wedinLemma20_11_bound",
            SELF_HISTORICAL_B,
            SELF_ANALYSIS,
            "theorem",
            "public",
        )
        cycle_tsv = root / "cycle.tsv"
        cycle_tsv.write_text(
            _self_stream(
                declarations,
                edges
                + [
                    DependencyEdge(
                        "body", "NumStability.lsResidual", "NumStability.wedinLemma20_11_bound"
                    ),
                    DependencyEdge(
                        "body", "NumStability.wedinLemma20_11_bound", "NumStability.lsResidual"
                    ),
                ],
            ),
            encoding="utf-8",
        )
        expect_value_error(
            lambda: validate_destination_graph(
                cycle_tsv, declarations, actual_to_logical, cyclic
            ),
            "a destination ownership cycle",
        )

        # Candidate stream after a completed move of both reusable owners.
        moved = [
            Declaration("NumStability.lsResidual", SELF_REUSABLE, "definition", "public"),
            Declaration("NumStability.lsResidual_permuteRows", SELF_REUSABLE, "theorem", "public"),
            Declaration(
                f"_private.{SELF_REUSABLE}.0.NumStability.lsHelper",
                SELF_REUSABLE,
                "theorem",
                "private",
            ),
            Declaration("NumStability.wedinLemma20_11_bound", SELF_ANALYSIS, "theorem", "public"),
            Declaration("NumStability.theorem20_3_source", SELF_SOURCE, "theorem", "public"),
            Declaration(
                "NumStability.qrExternal", "NumStability.Algorithms.QR.QRSolve", "theorem", "public"
            ),
        ]
        moved_edges = [
            DependencyEdge(
                "signature", "NumStability.lsResidual_permuteRows", "NumStability.lsResidual"
            ),
            DependencyEdge(
                "body",
                "NumStability.lsResidual_permuteRows",
                f"_private.{SELF_REUSABLE}.0.NumStability.lsHelper",
            ),
            DependencyEdge("body", "NumStability.theorem20_3_source", "NumStability.lsResidual"),
            DependencyEdge(
                "signature",
                "NumStability.wedinLemma20_11_bound",
                "NumStability.wedinLemma20_11_bound",
            ),
            DependencyEdge("body", "NumStability.lsResidual", "NumStability.qrExternal"),
        ]
        rewrites_path = root / "rewrites.tsv"
        rewrites_path.write_text(
            "format\t1\n"
            f"{SELF_PRIVATE_LOGICAL}\t"
            f"_private.{SELF_HISTORICAL_A}.0.NumStability.lsHelper\t"
            f"_private.{SELF_REUSABLE}.0.NumStability.lsHelper\n",
            encoding="utf-8",
        )
        rewrites = read_private_rewrites(rewrites_path, records, baseline)
        assert set(rewrites) == {SELF_PRIVATE_LOGICAL}

        # 9. Unexplained private mapping.
        bad_rewrites = root / "bad-rewrites.tsv"
        bad_rewrites.write_text(
            "format\t1\n"
            f"{SELF_PRIVATE_LOGICAL}\t"
            f"_private.{SELF_HISTORICAL_A}.0.NumStability.lsHelper\t"
            f"_private.{SELF_ANALYSIS}.0.NumStability.lsHelper\n",
            encoding="utf-8",
        )
        expect_value_error(
            lambda: read_private_rewrites(bad_rewrites, records, baseline),
            "a private rewrite that does not normalize from its destination",
        )
        empty_rewrites = root / "empty-rewrites.tsv"
        empty_rewrites.write_text("format\t1\n", encoding="utf-8")
        expect_value_error(
            lambda: read_private_rewrites(empty_rewrites, records, baseline),
            "missing private rewrite coverage",
        )

        candidate_map = check_candidate_ownership(records, baseline, moved, rewrites)
        assert len(candidate_map) == 5, candidate_map

        candidate_tsv = root / "candidate.tsv"
        candidate_tsv.write_text(_self_stream(moved, moved_edges), encoding="utf-8")
        compare_full_graph(
            baseline_tsv, candidate_tsv, baseline, candidate_map, records, None
        )

        # 10. Lost typed edge.
        lost_tsv = root / "lost.tsv"
        lost_tsv.write_text(_self_stream(moved, moved_edges[1:]), encoding="utf-8")
        expect_value_error(
            lambda: compare_full_graph(
                baseline_tsv, lost_tsv, baseline, candidate_map, records, None
            ),
            "a lost typed edge",
        )
        # 11. Extra typed edge.
        extra_tsv = root / "extra.tsv"
        extra_tsv.write_text(
            _self_stream(
                moved,
                moved_edges
                + [
                    DependencyEdge(
                        "body", "NumStability.lsResidual", "NumStability.wedinLemma20_11_bound"
                    )
                ],
            ),
            encoding="utf-8",
        )
        expect_value_error(
            lambda: compare_full_graph(
                baseline_tsv, extra_tsv, baseline, candidate_map, records, None
            ),
            "an extra typed edge",
        )
        # 12. Lost self-edge.
        without_self = [
            e
            for e in moved_edges
            if not (e.source == e.target == "NumStability.wedinLemma20_11_bound")
        ]
        self_tsv = root / "selfedge.tsv"
        self_tsv.write_text(_self_stream(moved, without_self), encoding="utf-8")
        expect_value_error(
            lambda: compare_full_graph(
                baseline_tsv, self_tsv, baseline, candidate_map, records, None
            ),
            "a lost declaration self-edge",
        )
        # 13. Baseline digest drift.
        expect_value_error(
            lambda: compare_full_graph(
                baseline_tsv,
                candidate_tsv,
                baseline,
                candidate_map,
                records,
                "0" * 64,
            ),
            "a baseline stream whose digest changed",
        )

        # Structural wrapper and reusable-isolation checks on a synthetic tree.
        project = root / "project"
        (project / "NumStability/Algorithms/LinearSystems/LeastSquares").mkdir(
            parents=True, exist_ok=True
        )
        (project / "NumStability/Analysis/Perturbation/LeastSquares").mkdir(
            parents=True, exist_ok=True
        )
        (project / "NumStability/Source/Higham/Chapter20").mkdir(parents=True, exist_ok=True)
        (project / "NumStability/Algorithms/LeastSquares").mkdir(parents=True, exist_ok=True)
        (project / "NumStability/Algorithms/QR").mkdir(parents=True, exist_ok=True)

        residual = project / "NumStability/Algorithms/LinearSystems/LeastSquares/Residual.lean"
        residual.write_text(
            "/-! Residual API. -/\nimport NumStability.Algorithms.QR.QRSolve\n",
            encoding="utf-8",
        )
        (project / "NumStability/Analysis/Perturbation/LeastSquares/Wedin.lean").write_text(
            "/-! Wedin analysis. -/\n"
            "import NumStability.Algorithms.LinearSystems.LeastSquares.Residual\n",
            encoding="utf-8",
        )
        (project / "NumStability/Source/Higham/Chapter20/Theorem03.lean").write_text(
            "/-! Theorem 20.3. -/\n"
            "import NumStability.Algorithms.LinearSystems.LeastSquares.Residual\n",
            encoding="utf-8",
        )
        (project / "NumStability/Algorithms/QR/QRSolve.lean").write_text(
            "/-! QR solve. -/\n", encoding="utf-8"
        )
        wrapper = project / "NumStability/Algorithms/LeastSquares/LSQRSolve.lean"
        wrapper.write_text(
            "/-! Historical wrapper. -/\n"
            "import NumStability.Algorithms.LinearSystems.LeastSquares.Residual\n"
            "import NumStability.Algorithms.QR.QRSolve\n",
            encoding="utf-8",
        )
        (project / "NumStability/Algorithms/LeastSquares/LSPerturbation.lean").write_text(
            "/-! Historical wrapper. -/\n"
            "import NumStability.Analysis.Perturbation.LeastSquares.Wedin\n"
            "import NumStability.Source.Higham.Chapter20.Theorem03\n",
            encoding="utf-8",
        )

        graph = read_module_imports(project)
        assert SELF_REUSABLE in graph, sorted(graph)
        assert validate_reusable_isolation(project, records, graph) == 2

        # 14. Forbidden transitive reusable -> source import.
        bad_graph = dict(graph)
        bad_graph[SELF_REUSABLE] = graph[SELF_REUSABLE] + [SELF_SOURCE]
        expect_value_error(
            lambda: validate_reusable_isolation(project, records, bad_graph),
            "a reusable module importing a canonical source leaf",
        )
        ch7_graph = dict(graph)
        ch7_graph[SELF_REUSABLE] = graph[SELF_REUSABLE] + [CHAPTER_SEVEN]
        expect_value_error(
            lambda: validate_reusable_isolation(project, records, ch7_graph),
            "a reusable module reaching Analysis.HighamChapter7",
        )

        # 15. Cross-lane contract drift.
        self_forward = frozenset({(SELF_HISTORICAL_A, "NumStability.Algorithms.QR.QRSolve")})
        self_reverse = frozenset(
            {("NumStability.Algorithms.QR.Higham19Problem19_10", SELF_HISTORICAL_B)}
        )
        (project / "NumStability/Algorithms/QR/Higham19Problem19_10.lean").write_text(
            "/-! QR consumer. -/\nimport NumStability.Algorithms.LeastSquares.LSPerturbation\n",
            encoding="utf-8",
        )
        graph = read_module_imports(project)
        assert validate_cross_lane_contract(
            project, records, graph, self_forward, self_reverse
        ) == (1, 1)

        dropped = dict(graph)
        dropped[SELF_REUSABLE] = ["NumStability.Algorithms.QR.HouseholderQRSupport"]
        expect_value_error(
            lambda: validate_cross_lane_contract(
                project, records, dropped, self_forward, self_reverse
            ),
            "a dropped LS-to-QR dependency",
        )
        dropped_reverse = dict(graph)
        dropped_reverse["NumStability.Algorithms.QR.Higham19Problem19_10"] = []
        expect_value_error(
            lambda: validate_cross_lane_contract(
                project, records, dropped_reverse, self_forward, self_reverse
            ),
            "a QR consumer that lost its historical least-squares import",
        )

        # 16. Structural modules must be import-only and declaration-free.
        validate_structural_modules(project, moved, {SELF_HISTORICAL_A}, None)
        expect_value_error(
            lambda: validate_structural_modules(
                project,
                moved + [Declaration("NumStability.leftover", SELF_HISTORICAL_A, "theorem", "public")],
                {SELF_HISTORICAL_A},
                None,
            ),
            "a wrapper that still owns a compiled declaration",
        )
        unsorted_wrapper = project / "NumStability/Algorithms/LeastSquares/Unsorted.lean"
        unsorted_wrapper.write_text(
            "/-! Unsorted wrapper. -/\n"
            "import NumStability.Algorithms.QR.QRSolve\n"
            "import NumStability.Algorithms.LinearSystems.LeastSquares.Residual\n",
            encoding="utf-8",
        )
        expect_value_error(
            lambda: validate_import_only_module(project, f"{LS_PREFIX}.Unsorted"),
            "an unsorted wrapper import list",
        )
        code_wrapper = project / "NumStability/Algorithms/LeastSquares/WithCode.lean"
        code_wrapper.write_text(
            "/-! Wrapper with code. -/\n"
            "import NumStability.Algorithms.QR.QRSolve\n"
            "theorem leftover : True := trivial\n",
            encoding="utf-8",
        )
        expect_value_error(
            lambda: validate_import_only_module(project, f"{LS_PREFIX}.WithCode"),
            "a wrapper containing non-import code",
        )
        nodoc_wrapper = project / "NumStability/Algorithms/LeastSquares/NoDoc.lean"
        nodoc_wrapper.write_text(
            "import NumStability.Algorithms.QR.QRSolve\n", encoding="utf-8"
        )
        expect_value_error(
            lambda: validate_import_only_module(project, f"{LS_PREFIX}.NoDoc"),
            "a wrapper without a module docstring",
        )

        # 17. Proposed tier coverage.
        tiers_path = root / "tiers.tsv"
        tier_rows = {
            SELF_REUSABLE: "reusable",
            SELF_ANALYSIS: "reusable",
            SELF_SOURCE: "source",
            SELF_HISTORICAL_A: "compatibility",
            SOURCE_ROOT: "source",
            f"{SOURCE_ROOT}.Equation32": "source",
            f"{SOURCE_ROOT}.Lemma06": "source",
            f"{SOURCE_ROOT}.Theorem01": "source",
        }
        tiers_path.write_text(
            "format\t1\n"
            + "".join(f"{m}\t{t}\n" for m, t in sorted(tier_rows.items())),
            encoding="utf-8",
        )
        tiers = read_tiers(tiers_path)
        validate_tier_coverage(tiers, records, {SELF_HISTORICAL_A, SOURCE_ROOT})
        expect_value_error(
            lambda: validate_tier_coverage(tiers, records, {SOURCE_ROOT}),
            "tier rows that do not match the lane surface",
        )
        mixed_path = root / "mixed.tsv"
        mixed_path.write_text(
            "format\t1\n" + f"{SELF_REUSABLE}\tmixed\n", encoding="utf-8"
        )
        expect_value_error(
            lambda: read_tiers(mixed_path), "a mixed proposed tier"
        )
        contradicting = dict(tier_rows)
        contradicting[SELF_REUSABLE] = "source"
        contra_path = root / "contra.tsv"
        contra_path.write_text(
            "format\t1\n"
            + "".join(f"{m}\t{t}\n" for m, t in sorted(contradicting.items())),
            encoding="utf-8",
        )
        expect_value_error(
            lambda: validate_tier_coverage(
                read_tiers(contra_path), records, {SELF_HISTORICAL_A, SOURCE_ROOT}
            ),
            "a proposed tier contradicting its destination role",
        )

        # 18. Route map shapes.
        routes_path = root / "routes.tsv"
        routes_path.write_text(
            "format\t1\n"
            f"range\t{SELF_HISTORICAL_A}\t1\t100\t{SELF_REUSABLE}\n"
            f"exact\t{SELF_HISTORICAL_B}\tNumStability.wedinLemma20_11_bound\t-\t{SELF_ANALYSIS}\n"
            f"exact\t{SELF_HISTORICAL_B}\tNumStability.theorem20_3_source\t-\t{SELF_SOURCE}\n",
            encoding="utf-8",
        )
        ranges, exact_routes = read_routes(routes_path, set(SELF_COUNTS))
        assert len(ranges) == 1 and len(exact_routes) == 2

        overlap_path = root / "overlap.tsv"
        overlap_path.write_text(
            "format\t1\n"
            f"range\t{SELF_HISTORICAL_A}\t1\t100\t{SELF_REUSABLE}\n"
            f"range\t{SELF_HISTORICAL_A}\t50\t150\t{SELF_ANALYSIS}\n",
            encoding="utf-8",
        )
        expect_value_error(
            lambda: read_routes(overlap_path, set(SELF_COUNTS)),
            "overlapping route ranges",
        )

        ilean_dir = root / "ilean"
        ilean_dir.mkdir()
        ilean_path = ilean_dir / "LSQRSolve.ilean"
        ilean_path.write_text(
            json.dumps(
                {
                    "module": SELF_HISTORICAL_A,
                    "decls": {
                        "NumStability.lsResidual": [9, 0],
                        "NumStability.lsResidual_permuteRows": [19, 0],
                        f"_private.{SELF_HISTORICAL_A}.0.NumStability.lsHelper": [29, 0],
                    },
                }
            ),
            encoding="utf-8",
        )
        generated = generate_manifest(
            baseline,
            routes_path,
            project,
            {SELF_HISTORICAL_A: ilean_path},
            SELF_COUNTS,
        )
        assert generated == records, sorted(
            (k, v) for k, v in generated.items() if records.get(k) != v
        )

        outside_path = root / "outside.tsv"
        outside_path.write_text(
            "format\t1\n"
            f"range\t{SELF_HISTORICAL_A}\t1\t5\t{SELF_REUSABLE}\n"
            f"exact\t{SELF_HISTORICAL_B}\tNumStability.wedinLemma20_11_bound\t-\t{SELF_ANALYSIS}\n"
            f"exact\t{SELF_HISTORICAL_B}\tNumStability.theorem20_3_source\t-\t{SELF_SOURCE}\n",
            encoding="utf-8",
        )
        expect_value_error(
            lambda: generate_manifest(
                baseline, outside_path, project, {SELF_HISTORICAL_A: ilean_path}, SELF_COUNTS
            ),
            "a declaration outside every reviewed range",
        )

        digest = validate_expected_manifest_digest(records, None)
        assert HEX_SHA256.fullmatch(digest)
        expect_value_error(
            lambda: validate_expected_manifest_digest(records, "0" * 64),
            "a manifest digest mismatch",
        )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--mode", choices=("pre", "stage", "post"))
    parser.add_argument(
        "--dependency-tsv",
        type=Path,
        help="frozen baseline TSV in pre mode; freshly generated TSV in stage/post mode",
    )
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument(
        "--routes",
        type=Path,
        help="reviewed range/exact route map used to generate or recheck the manifest",
    )
    parser.add_argument(
        "--write-manifest",
        action="store_true",
        help="generate the manifest from --routes; valid only in pre mode",
    )
    parser.add_argument(
        "--ilean",
        action="append",
        default=[],
        metavar="HISTORICAL_MODULE=PATH",
        help="override a historical module's .ilean path (repeatable)",
    )
    parser.add_argument(
        "--baseline-tsv",
        type=Path,
        help="retained frozen lane baseline TSV; required in stage/post mode",
    )
    parser.add_argument(
        "--private-rewrites",
        type=Path,
        default=DEFAULT_PRIVATE_REWRITES,
        help="explicit private-name rewrite map required in stage/post mode",
    )
    parser.add_argument("--tiers", type=Path, default=DEFAULT_TIERS)
    parser.add_argument(
        "--expected-manifest-sha256",
        help="optional canonical LF-normalized manifest digest",
    )
    parser.add_argument(
        "--project-root",
        type=Path,
        default=Path("."),
        help="repository root for .ilean defaults and structural-module checks",
    )
    parser.add_argument(
        "--structural-module",
        action="append",
        default=[],
        help="additional completed import-only wrapper or aggregate (repeatable)",
    )
    parser.add_argument(
        "--structural-modules",
        type=Path,
        help="optional format-1 one-column file of additional structural modules",
    )
    parser.add_argument(
        "--completed-destination",
        action="append",
        default=[],
        help="destination fully moved in stage mode (repeatable)",
    )
    parser.add_argument(
        "--completed-destinations",
        type=Path,
        help="format-1 one-column completed-destination set for stage mode",
    )
    parser.add_argument(
        "--skip-cross-lane",
        action="store_true",
        help="skip the frozen cross-lane import contract (pre mode only)",
    )
    parser.add_argument(
        "--self-test", action="store_true", help="run checker unit smoke tests"
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.self_test:
        run_self_test()
        print("lsq-ch20 ownership checker self-test passed")
        return 0
    if args.mode is None or args.dependency_tsv is None:
        raise ValueError("--mode and --dependency-tsv are required")
    if args.write_manifest and args.mode != "pre":
        raise ValueError("--write-manifest is valid only in pre mode")
    if args.write_manifest and args.routes is None:
        raise ValueError("--write-manifest requires an explicit --routes file")
    if args.skip_cross_lane and args.mode != "pre":
        raise ValueError("--skip-cross-lane is valid only in pre mode")

    ilean_overrides = parse_ilean_overrides(args.ilean)
    structural_modules = set(DEFAULT_STRUCTURAL_MODULES)
    structural_modules.update(args.structural_module)
    if args.structural_modules is not None:
        structural_modules.update(read_structural_modules(args.structural_modules))

    if args.mode == "pre":
        if sha256_file(args.dependency_tsv) != BASELINE_TSV_SHA256:
            raise ValueError("pre-migration dependency TSV hash differs from the frozen base")
        declarations = read_dependency_declarations(args.dependency_tsv)
        baseline = selected_baseline_declarations(declarations)

        generated: dict[str, ManifestRow] | None = None
        if args.routes is not None:
            generated = generate_manifest(
                baseline, args.routes, args.project_root, ilean_overrides
            )
        if args.write_manifest:
            assert generated is not None
            write_manifest(args.manifest, generated)

        records = read_manifest(args.manifest)
        validate_manifest_against_baseline(records, baseline)
        if generated is not None and records != generated:
            raise ValueError(
                "committed manifest differs from the manifest generated by --routes"
            )
        digest = validate_expected_manifest_digest(records, args.expected_manifest_sha256)
        actual_to_logical = baseline_actual_to_logical(baseline)
        owners, owner_edges = validate_destination_graph(
            args.dependency_tsv, declarations, actual_to_logical, records
        )
        tiers = read_tiers(args.tiers)
        validate_tier_coverage(tiers, records, structural_modules)
        if not args.skip_cross_lane:
            forward, reverse = validate_cross_lane_contract(args.project_root, records)
            print(f"cross-lane contract: {forward} LS-to-QR, {reverse} QR-to-LS")
        print(
            f"pre mode passed: {len(records)} declarations, {owners} destinations, "
            f"{owner_edges} owner edges, manifest sha256 {digest}"
        )
        return 0

    if args.baseline_tsv is None:
        raise ValueError(f"--baseline-tsv is required in {args.mode} mode")
    baseline_declarations = read_dependency_declarations(args.baseline_tsv)
    baseline = selected_baseline_declarations(baseline_declarations)
    records = read_manifest(args.manifest)
    validate_manifest_against_baseline(records, baseline)
    digest = validate_expected_manifest_digest(records, args.expected_manifest_sha256)

    all_destinations = {row.destination_module for row in records.values()}
    if args.mode == "stage":
        completed: set[str] = set(args.completed_destination)
        if args.completed_destinations is not None:
            completed.update(read_completed_destinations(args.completed_destinations))
        unknown = sorted(completed - all_destinations)
        if unknown:
            raise ValueError(f"completed destinations are not lane owners: {unknown}")
    else:
        completed = all_destinations

    declarations = read_dependency_declarations(args.dependency_tsv)
    required_private = {
        logical
        for logical, row in records.items()
        if row.visibility == "private" and row.destination_module in completed
    }
    rewrites = read_private_rewrites(
        args.private_rewrites, records, baseline, required_private
    )
    if args.mode == "post" and len(rewrites) != EXPECTED_PRIVATE_ROWS:
        raise ValueError(
            f"post mode requires all {EXPECTED_PRIVATE_ROWS} reviewed private "
            f"rewrites, found {len(rewrites)}"
        )

    candidate_map = check_candidate_ownership(
        records, baseline, declarations, rewrites, completed
    )
    validate_structural_modules(
        args.project_root, declarations, structural_modules, None
    )
    compare_full_graph(
        args.baseline_tsv, args.dependency_tsv, baseline, candidate_map, records
    )
    actual_to_logical = {
        declaration.name: candidate_map[declaration.name]
        for declaration in declarations
        if declaration.name in candidate_map
    }
    owners, owner_edges = validate_destination_graph(
        args.dependency_tsv, declarations, actual_to_logical, records
    )
    tiers = read_tiers(args.tiers)
    validate_tier_coverage(tiers, records, structural_modules)
    import_graph = read_module_imports(args.project_root)
    forward, reverse = validate_cross_lane_contract(
        args.project_root, records, import_graph
    )

    if args.mode == "post":
        reusable = validate_reusable_isolation(args.project_root, records, import_graph)
        print(
            f"post mode passed: {len(records)} declarations, {owners} destinations, "
            f"{owner_edges} owner edges, {reusable} isolated reusable modules, "
            f"{forward} LS-to-QR, {reverse} QR-to-LS, manifest sha256 {digest}"
        )
    else:
        print(
            f"stage mode passed: {len(completed)}/{len(all_destinations)} destinations "
            f"complete, {owner_edges} owner edges, {forward} LS-to-QR, "
            f"{reverse} QR-to-LS, manifest sha256 {digest}"
        )
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except ValueError as error:
        print(f"error: {error}", file=sys.stderr)
        sys.exit(1)
