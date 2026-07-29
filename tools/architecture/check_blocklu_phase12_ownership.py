#!/usr/bin/env python3
"""Generate and check the BlockLU Phase 12 semantic ownership partition.

The ownership manifest has the following tab-separated schema::

    format\t1
    logical_name\thistorical_module\tdestination_module\tkind\tvisibility

Manifest generation is deliberately driven by a separately reviewed route
map.  A route map starts with ``format\t1`` and accepts these row shapes::

    range\thistorical_module\tfirst_line\tlast_line\tdestination_module
    exact\thistorical_module\tlogical_name\t-\tdestination_module

Source lines are one-based and inclusive.  Range routing resolves compiled
declarations through source locations in the historical module's
``.ilean`` file.  Exact routes take precedence and cover reviewed declarations
that have no usable source declaration root.  The declaration graph extractor
omits Lean-reserved and compiler-generated internal details and contracts paths
through them onto reachable authored project declarations.  This produces a
stable semantic graph whose rows must compare exactly after ownership and
private-name normalization.  The checker never invents a destination.

Lean private names encode their owning module and therefore necessarily change
when a declaration moves.  Post-migration mode requires an explicit companion
map for every selected private declaration::

    format\t1
    logical_name\thistorical_actual_name\tcandidate_actual_name

Only those reviewed private-name rewrites are normalized during the exact
full-graph comparison.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import sys
import tempfile
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterable


BLOCKLU = "NumStability.Algorithms.LU.BlockLU"
FIRST_ORDER = "NumStability.Analysis.FirstOrder"
GROWTH_FACTOR = "NumStability.Algorithms.LU.GrowthFactor"

ASYMPTOTIC_FAMILIES = "NumStability.Analysis.FirstOrder.AsymptoticFamilies"
ENTRYWISE_MAXIMUM = "NumStability.Analysis.MatrixNorms.EntrywiseMaximum"
RECURSIVE_FACTORIZATION = (
    "NumStability.Algorithms.LinearSystems.LU.BlockLU.RecursiveFactorization"
)

REVIEWED_BODY_EDGE_DROP_REASON = "private-helper-proof-inlined"
FROZEN_REVIEWED_BODY_EDGE_DROPS = frozenset(
    {
        (
            "NumStability.BlockLUFactSpec.firstColumnBelow_eq_of_right_inverse",
            "_private.<module>.NumStability.sum_ite_eq_val_right",
        ),
        (
            "NumStability.BlockLUFactSpec.firstRow_eq",
            "_private.<module>.NumStability.sum_ite_eq_val",
        ),
        (
            "NumStability.block_lu_one_step_explicit",
            "_private.<module>.NumStability.sum_ite_eq_val",
        ),
        (
            "NumStability.block_lu_one_step_explicit",
            "_private.<module>.NumStability.sum_ite_eq_val_right",
        ),
    }
)

HISTORICAL_MODULES = {BLOCKLU, FIRST_ORDER, GROWTH_FACTOR}
COMPLETE_HISTORICAL_MODULES = {BLOCKLU, FIRST_ORDER}
EXPECTED_HISTORICAL_COUNTS = {
    BLOCKLU: 1_942,
    FIRST_ORDER: 37,
    GROWTH_FACTOR: 11,
}
EXPECTED_MANIFEST_ROWS = sum(EXPECTED_HISTORICAL_COUNTS.values())

# GrowthFactor is intentionally a partial historical owner: Phase 12 extracts
# exactly this generic max-entry-norm family and leaves its other declarations
# in GrowthFactor.  BlockLU and FirstOrder are complete historical owners.
GROWTH_FACTOR_SELECTION = {
    "NumStability.entry_abs_le_infNorm",
    "NumStability.entry_le_maxEntryNorm",
    "NumStability.infNorm_le_card_mul_maxEntryNorm",
    "NumStability.maxEntryNorm",
    "NumStability.maxEntryNorm_le_infNorm",
    "NumStability.maxEntryNorm_le_of_entry_abs_le",
    "NumStability.maxEntryNorm_le_of_entry_le_bound",
    "NumStability.maxEntryNorm_le_of_entry_le_max",
    "NumStability.maxEntryNorm_matTranspose",
    "NumStability.maxEntryNorm_nonneg",
    "NumStability.maxEntryNorm_submatrix_le",
}

BASELINE_TSV_SHA256 = (
    "FD37F73D83F0206E40291576E1F9496185F09C21928ABED147B5CE2A6EF83AED"
)

DEFAULT_MANIFEST = Path(
    "docs/architecture/declaration-ownership/blocklu-phase12-v2.tsv"
)
DEFAULT_PRIVATE_REWRITES = Path(
    "docs/architecture/declaration-ownership/"
    "blocklu-phase12-private-rewrites.tsv"
)

# These modules are the Phase 12 structural surface.  The two historical
# implementation owners become forwarding/aggregate modules; the other paths
# are the canonical family and Problem 13.4 umbrellas committed by the phase.
# Additional completed structural modules can be supplied on the command line
# or in a one-column structural-module file.
DEFAULT_STRUCTURAL_MODULES = {
    BLOCKLU,
    FIRST_ORDER,
    "NumStability.Analysis.MatrixNorms",
    "NumStability.Algorithms.LinearSystems",
    "NumStability.Algorithms.LinearSystems.LU",
    "NumStability.Algorithms.LinearSystems.LU.BlockLU",
    "NumStability.Source.Higham.Chapter13",
    "NumStability.Source.Higham.Chapter13.BlockLU",
    "NumStability.Source.Higham.Chapter13.Problem04",
    "NumStability.Source.Higham.Chapter13.Problem04.FactorizationProducts",
    "NumStability.Source.Higham.Chapter13.Problem04.GlobalTableauProducts",
}

HEX_SHA256 = re.compile(r"^[0-9A-Fa-f]{64}$")
MODULE_NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$")
EDGE_KINDS = {"body", "signature"}
REUSABLE_DESTINATION_PREFIXES = (
    "NumStability.Analysis.",
    "NumStability.Algorithms.LinearSystems.",
)
SOURCE_DESTINATION_PREFIX = "NumStability.Source.Higham."

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
class ReviewedBodyEdgeDrop:
    action: str
    kind: str
    source_logical_name: str
    target_logical_name: str
    reason: str


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


def logical_name(actual_name: str, actual_module: str) -> str:
    """Normalize only the module and scope ordinal in a Lean private name."""

    prefix = f"_private.{actual_module}."
    if not actual_name.startswith("_private."):
        return actual_name
    if not actual_name.startswith(prefix):
        raise ValueError(
            f"private name {actual_name!r} does not encode owner {actual_module!r}"
        )
    ordinal, separator, suffix = actual_name[len(prefix) :].partition(".")
    if not separator or not ordinal.isdigit() or not suffix:
        raise ValueError(f"unexpected Lean private name: {actual_name}")
    return f"_private.<module>.{suffix}"


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
                if (
                    not saw_format
                    or row[1] not in EDGE_KINDS
                    or not all(row[2:])
                ):
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
                if (
                    not saw_format
                    or row[1] not in EDGE_KINDS
                    or not all(row[2:])
                ):
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
) -> dict[str, Declaration]:
    records: dict[str, Declaration] = {}
    growth_seen: set[str] = set()
    raw_counts: Counter[str] = Counter()

    for declaration in declarations:
        if declaration.module in COMPLETE_HISTORICAL_MODULES:
            selected = True
        elif declaration.module == GROWTH_FACTOR:
            selected = declaration.name in GROWTH_FACTOR_SELECTION
            if selected:
                growth_seen.add(declaration.name)
        else:
            selected = False
        if not selected:
            continue

        logical = logical_name(declaration.name, declaration.module)
        if logical in records:
            raise ValueError(f"duplicate selected logical name: {logical}")
        records[logical] = declaration
        raw_counts[declaration.module] += 1

    if growth_seen != GROWTH_FACTOR_SELECTION:
        missing = sorted(GROWTH_FACTOR_SELECTION - growth_seen)
        extra = sorted(growth_seen - GROWTH_FACTOR_SELECTION)
        raise ValueError(
            f"GrowthFactor selected family differs: missing={missing}; extra={extra}"
        )
    if raw_counts != Counter(EXPECTED_HISTORICAL_COUNTS):
        raise ValueError(
            "historical declaration counts differ from the frozen Phase 12 "
            f"selection: expected {EXPECTED_HISTORICAL_COUNTS}, found "
            f"{dict(raw_counts)}"
        )
    if len(records) != EXPECTED_MANIFEST_ROWS:
        raise ValueError(
            f"expected {EXPECTED_MANIFEST_ROWS} selected declarations, "
            f"found {len(records)}"
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
        f"Phase 12 destination is outside the reviewed reusable/source roots: {module}"
    )


def validate_manifest_shape(records: dict[str, ManifestRow]) -> None:
    if len(records) != EXPECTED_MANIFEST_ROWS:
        raise ValueError(
            f"expected {EXPECTED_MANIFEST_ROWS} ownership rows, found {len(records)}"
        )
    counts = Counter(row.historical_module for row in records.values())
    if counts != Counter(EXPECTED_HISTORICAL_COUNTS):
        raise ValueError(
            f"manifest historical-owner counts differ: expected "
            f"{EXPECTED_HISTORICAL_COUNTS}, found {dict(counts)}"
        )

    for logical, row in records.items():
        if logical != row.logical_name or not logical:
            raise ValueError(f"invalid manifest logical name: {logical!r}")
        check_module_name(row.historical_module, logical)
        check_module_name(row.destination_module, logical)
        if row.historical_module not in HISTORICAL_MODULES:
            raise ValueError(
                f"{logical}: unexpected historical owner {row.historical_module}"
            )
        if row.destination_module in HISTORICAL_MODULES:
            raise ValueError(
                f"{logical}: destination remains a historical owner: "
                f"{row.destination_module}"
            )
        destination_role(row.destination_module)
        if not row.kind or not row.visibility:
            raise ValueError(f"{logical}: empty kind or visibility")
        if row.visibility == "private" and not logical.startswith(
            "_private.<module>."
        ):
            raise ValueError(
                f"{logical}: private declaration lacks normalized private prefix"
            )
        if row.visibility != "private" and logical.startswith("_private."):
            raise ValueError(
                f"{logical}: private-shaped name has visibility {row.visibility}"
            )
        if row.historical_module == FIRST_ORDER and (
            row.destination_module != ASYMPTOTIC_FAMILIES
        ):
            raise ValueError(
                f"{logical}: Analysis.FirstOrder must move to "
                f"{ASYMPTOTIC_FAMILIES}"
            )
        if row.historical_module == GROWTH_FACTOR and (
            row.destination_module != ENTRYWISE_MAXIMUM
        ):
            raise ValueError(
                f"{logical}: selected GrowthFactor family must move to "
                f"{ENTRYWISE_MAXIMUM}"
            )


def read_manifest(path: Path) -> dict[str, ManifestRow]:
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
                f"{path}:{line_number}: duplicate logical name "
                f"{record.logical_name}"
            )
        records[record.logical_name] = record
        order.append(record.logical_name)
    if order != sorted(order):
        raise ValueError(f"{path}: ownership rows must be sorted by logical name")
    validate_manifest_shape(records)
    return records


def write_manifest(path: Path, records: dict[str, ManifestRow]) -> None:
    validate_manifest_shape(records)
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
) -> tuple[list[RangeRoute], dict[tuple[str, str], str]]:
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["format", "1"]:
        raise ValueError(f"{path}: routes must start with 'format\\t1'")

    ranges: list[RangeRoute] = []
    exact: dict[tuple[str, str], str] = {}
    for line_number, row in enumerate(rows[1:], 2):
        if len(row) != 5:
            raise ValueError(
                f"{path}:{line_number}: route rows require five columns"
            )
        route_kind, historical, third, fourth, destination = row
        if historical not in HISTORICAL_MODULES:
            raise ValueError(
                f"{path}:{line_number}: unexpected historical module {historical}"
            )
        check_module_name(destination, f"{path}:{line_number}")
        if destination in HISTORICAL_MODULES:
            raise ValueError(
                f"{path}:{line_number}: destination is historical: {destination}"
            )
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
            ranges.append(
                RangeRoute(historical, first_line, last_line, destination)
            )
        elif route_kind == "exact":
            if fourth != "-" or not third:
                raise ValueError(
                    f"{path}:{line_number}: exact route shape is "
                    "exact, historical, logical_name, -, destination"
                )
            key = (historical, third)
            if key in exact:
                raise ValueError(
                    f"{path}:{line_number}: duplicate exact route {key}"
                )
            exact[key] = destination
        else:
            raise ValueError(
                f"{path}:{line_number}: unknown route kind {route_kind!r}"
            )

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
    return (
        project_root
        / ".lake/build/lib/lean"
        / (module.replace(".", "/") + ".ilean")
    )


def parse_ilean_overrides(values: list[str]) -> dict[str, Path]:
    result: dict[str, Path] = {}
    for value in values:
        module, separator, raw_path = value.partition("=")
        if not separator or not module or not raw_path:
            raise ValueError(
                f"invalid --ilean {value!r}; expected HISTORICAL_MODULE=PATH"
            )
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
            f"{path}: expected .ilean owner {expected_module}, "
            f"found {actual_module!r}"
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
) -> dict[str, ManifestRow]:
    ranges, exact_routes = read_routes(routes_path)
    ranges_by_module: dict[str, list[RangeRoute]] = defaultdict(list)
    for route in ranges:
        ranges_by_module[route.historical_module].append(route)

    roots_by_module: dict[str, dict[str, int]] = {}
    for module in ranges_by_module:
        ilean_path = ilean_overrides.get(
            module, default_ilean_path(project_root, module)
        )
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
                if declaration.name == root
                or declaration.name.startswith(root + ".")
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
    validate_manifest_shape(generated)
    return generated


def baseline_actual_to_logical(
    baseline: dict[str, Declaration],
) -> dict[str, str]:
    result = {declaration.name: logical for logical, declaration in baseline.items()}
    if len(result) != EXPECTED_MANIFEST_ROWS:
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

    def visit(owner: str) -> None:
        nonlocal next_index
        indices[owner] = next_index
        lowlinks[owner] = next_index
        next_index += 1
        stack.append(owner)
        on_stack.add(owner)

        for dependency in sorted(graph[owner]):
            if dependency not in indices:
                visit(dependency)
                lowlinks[owner] = min(lowlinks[owner], lowlinks[dependency])
            elif dependency in on_stack:
                lowlinks[owner] = min(lowlinks[owner], indices[dependency])

        if lowlinks[owner] != indices[owner]:
            return
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
    """Enforce the selected declaration DAG and reusable/source boundary."""

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
        if (
            source_role == "reusable"
            and target_module is not None
            and target_module.startswith(SOURCE_DESTINATION_PREFIX)
        ):
            forbidden.append(
                f"{source_owner} -> external {target_module} via {edge.kind} "
                f"{edge.source} -> {edge.target}"
            )

    if forbidden:
        raise ValueError(
            "reusable destinations depend on source declarations: "
            + "; ".join(forbidden[:20])
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
                    f"{source} -> {target} via {edge.kind} "
                    f"{edge.source} -> {edge.target}"
                )
        raise ValueError(
            "destination ownership graph contains a cycle among "
            f"{component}: " + "; ".join(component_witnesses[:20])
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
        raise ValueError(
            f"{path}: private rewrites must start with 'format\\t1'"
        )

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
            f"private rewrite coverage differs: missing={missing[:20]}; "
            f"extra={extra[:20]}"
        )
    for logical, rewrite in rewrites.items():
        historical = baseline[logical]
        destination = records[logical].destination_module
        if rewrite.historical_actual_name != historical.name:
            raise ValueError(
                f"{logical}: expected historical private name {historical.name}, "
                f"found {rewrite.historical_actual_name}"
            )
        if logical_name(rewrite.candidate_actual_name, destination) != logical:
            raise ValueError(
                f"{logical}: candidate private name does not normalize from "
                f"destination {destination}: {rewrite.candidate_actual_name}"
            )
    return rewrites


def read_reviewed_body_edge_drops(
    path: Path,
    records: dict[str, ManifestRow],
    baseline: dict[str, Declaration],
    baseline_tsv: Path,
) -> frozenset[ReviewedBodyEdgeDrop]:
    """Read the fixed RecursiveFactorization body-edge amendment.

    These four edges disappear only because the historical private finite-sum
    helper proofs are inlined at their cross-owner call sites.  The file is a
    reviewed exception list, not a general graph-difference allowlist.
    """

    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["format", "1"]:
        raise ValueError(
            f"{path}: reviewed body-edge drops must start with 'format\\t1'"
        )

    drops: list[ReviewedBodyEdgeDrop] = []
    pairs: list[tuple[str, str]] = []
    seen_pairs: set[tuple[str, str]] = set()
    for line_number, row in enumerate(rows[1:], 2):
        if len(row) != 5:
            raise ValueError(
                f"{path}:{line_number}: reviewed body-edge drops require five columns"
            )
        drop = ReviewedBodyEdgeDrop(*row)
        if drop.action != "drop":
            raise ValueError(
                f"{path}:{line_number}: expected reviewed action 'drop'"
            )
        if drop.kind != "body":
            raise ValueError(
                f"{path}:{line_number}: only body edges may be reviewed drops"
            )
        if drop.reason != REVIEWED_BODY_EDGE_DROP_REASON:
            raise ValueError(
                f"{path}:{line_number}: expected reason "
                f"{REVIEWED_BODY_EDGE_DROP_REASON!r}"
            )
        pair = (drop.source_logical_name, drop.target_logical_name)
        if pair in seen_pairs:
            raise ValueError(
                f"{path}:{line_number}: duplicate reviewed body-edge drop {pair}"
            )
        seen_pairs.add(pair)
        pairs.append(pair)
        drops.append(drop)

    if pairs != sorted(pairs):
        raise ValueError(f"{path}: reviewed body-edge drop rows must be sorted")
    if set(pairs) != FROZEN_REVIEWED_BODY_EDGE_DROPS:
        missing = sorted(FROZEN_REVIEWED_BODY_EDGE_DROPS - set(pairs))
        extra = sorted(set(pairs) - FROZEN_REVIEWED_BODY_EDGE_DROPS)
        raise ValueError(
            "reviewed body-edge drop set differs from the frozen four: "
            f"missing={missing}; extra={extra}"
        )

    actual_pairs: set[tuple[str, str]] = set()
    for drop in drops:
        source_logical = drop.source_logical_name
        target_logical = drop.target_logical_name
        if source_logical not in records or target_logical not in records:
            raise ValueError(
                f"{path}: reviewed edge endpoints must both occur in the manifest: "
                f"{source_logical} -> {target_logical}"
            )
        target = records[target_logical]
        if (
            target.visibility != "private"
            or target.destination_module != RECURSIVE_FACTORIZATION
        ):
            raise ValueError(
                f"{path}: reviewed target must be private and owned by "
                f"{RECURSIVE_FACTORIZATION}: {target_logical}"
            )
        if source_logical not in baseline or target_logical not in baseline:
            raise ValueError(
                f"{path}: reviewed edge endpoints must both occur in the frozen "
                f"baseline: {source_logical} -> {target_logical}"
            )
        actual_pairs.add(
            (baseline[source_logical].name, baseline[target_logical].name)
        )

    occurrences: Counter[tuple[str, str]] = Counter()
    for edge in iter_dependency_edges(baseline_tsv):
        pair = (edge.source, edge.target)
        if edge.kind == "body" and pair in actual_pairs:
            occurrences[pair] += 1
    for pair in sorted(actual_pairs):
        if occurrences[pair] != 1:
            raise ValueError(
                f"{path}: frozen reviewed body edge must occur exactly once, "
                f"found {occurrences[pair]}: {pair[0]} -> {pair[1]}"
            )

    return frozenset(drops)


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
    declaration_by_name = {declaration.name: declaration for declaration in declarations}
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

    # Reject alternate private encodings and any selected logical declaration in
    # a module other than its stage-appropriate owner.  Public names are global
    # and therefore already fail the exact metadata check above; this scan is
    # primarily the one-to-one guard for module-encoded private declarations.
    selected_modules = HISTORICAL_MODULES | {
        row.destination_module for row in records.values()
    }
    alternates: list[str] = []
    for declaration in declarations:
        if declaration.module not in selected_modules:
            continue
        logical = logical_name(declaration.name, declaration.module)
        if (
            logical in records
            and declaration.name != expected_actual_by_logical[logical]
        ):
            alternates.append(f"{declaration.module}:{declaration.name}")
    if alternates:
        raise ValueError(
            "selected declarations have alternate or stage-inappropriate owners: "
            + ", ".join(alternates[:20])
        )
    if len(candidate_actual_to_logical) != EXPECTED_MANIFEST_ROWS:
        raise ValueError("candidate selected-name map is not one-to-one")
    return candidate_actual_to_logical


def strip_lean_comments(lines: list[str]) -> list[str]:
    result: list[str] = []
    depth = 0
    for source_line in lines:
        output: list[str] = []
        index = 0
        while index < len(source_line):
            if depth:
                if source_line.startswith("/-", index):
                    depth += 1
                    index += 2
                elif source_line.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            else:
                if source_line.startswith("--", index):
                    break
                if source_line.startswith("/-", index):
                    depth += 1
                    index += 2
                else:
                    output.append(source_line[index])
                    index += 1
        result.append("".join(output))
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
        raise ValueError(f"structural module has duplicate imports in {path}: {duplicates}")
    ordered = tuple(sorted(imports, key=str.casefold))
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
                f"structural module contains non-import code in {path}: "
                f"{original!r}"
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
        raise ValueError(
            f"{path}: structural modules must start with 'format\\t1'"
        )
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


def read_structural_contract(path: Path) -> dict[str, tuple[str, ...]]:
    """Read exact ``structural module -> direct import`` pairs."""

    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["format", "1"]:
        raise ValueError(
            f"{path}: structural contract must start with 'format\\t1'"
        )

    pairs: list[tuple[str, str]] = []
    seen: set[tuple[str, str]] = set()
    for line_number, row in enumerate(rows[1:], 2):
        if len(row) != 2:
            raise ValueError(
                f"{path}:{line_number}: expected structural module and direct import"
            )
        module, imported = row
        check_module_name(module, f"{path}:{line_number}")
        check_module_name(imported, f"{path}:{line_number}")
        pair = (module, imported)
        if pair in seen:
            raise ValueError(f"{path}:{line_number}: duplicate contract row {pair}")
        if module == imported:
            raise ValueError(f"{path}:{line_number}: structural module imports itself")
        pairs.append(pair)
        seen.add(pair)
    if not pairs:
        raise ValueError(f"{path}: structural contract is empty")
    if pairs != sorted(pairs, key=lambda pair: (pair[0], pair[1].casefold())):
        raise ValueError(f"{path}: structural contract rows must be sorted")

    imports_by_module: dict[str, list[str]] = defaultdict(list)
    for module, imported in pairs:
        imports_by_module[module].append(imported)
    return {
        module: tuple(imports)
        for module, imports in imports_by_module.items()
    }


def read_completed_destinations(path: Path) -> set[str]:
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["format", "1"]:
        raise ValueError(
            f"{path}: completed destinations must start with 'format\\t1'"
        )
    destinations: list[str] = []
    for line_number, row in enumerate(rows[1:], 2):
        if len(row) != 1:
            raise ValueError(
                f"{path}:{line_number}: expected one completed destination"
            )
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
            row = raw.rstrip("\r\n")
            delta[row] += 1

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


def reviewed_body_edge_drop_delta(
    baseline: dict[str, Declaration],
    reviewed_body_edge_drops: frozenset[ReviewedBodyEdgeDrop],
) -> Counter[str]:
    return Counter(
        "\t".join(
            (
                "edge",
                "body",
                baseline[drop.source_logical_name].name,
                baseline[drop.target_logical_name].name,
            )
        )
        for drop in reviewed_body_edge_drops
    )


def validate_normalized_graph_delta(
    delta: Counter[str], expected_delta: Counter[str]
) -> None:
    if delta == expected_delta:
        return

    unexpected = delta.copy()
    unexpected.subtract(expected_delta)
    unexpected = Counter(
        {row: count for row, count in unexpected.items() if count != 0}
    )
    missing = sum(count for count in unexpected.values() if count > 0)
    extra = -sum(count for count in unexpected.values() if count < 0)
    details = "; ".join(
        f"{count:+d} {row}" for row, count in sorted(unexpected.items())[:20]
    )
    raise ValueError(
        "normalized contracted graph differs after applying the exact reviewed "
        f"body-edge delta: missing={missing}, extra={extra}; {details}"
    )


def compare_full_graph(
    baseline_tsv: Path,
    candidate_tsv: Path,
    baseline: dict[str, Declaration],
    candidate_actual_to_logical: dict[str, str],
    records: dict[str, ManifestRow],
    reviewed_body_edge_drops: frozenset[ReviewedBodyEdgeDrop],
) -> None:
    """Require the exact contracted graph, modulo the fixed reviewed drops."""

    if sha256_file(baseline_tsv) != BASELINE_TSV_SHA256:
        raise ValueError("baseline TSV hash differs from frozen Phase 11B2 input")

    delta = normalized_graph_delta(
        baseline_tsv,
        candidate_tsv,
        baseline,
        candidate_actual_to_logical,
        records,
    )
    expected_delta = reviewed_body_edge_drop_delta(
        baseline, reviewed_body_edge_drops
    )
    validate_normalized_graph_delta(delta, expected_delta)


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


def run_self_test() -> None:
    def expect_value_error(action: Callable[[], object], label: str) -> None:
        try:
            action()
        except ValueError:
            pass
        else:
            raise AssertionError(f"invalid {label} was accepted")

    module = "NumStability.Example.Owner"
    private = "_private.NumStability.Example.Owner.7.NumStability.helper.eq_1"
    assert logical_name(private, module) == (
        "_private.<module>.NumStability.helper.eq_1"
    )
    assert logical_name("NumStability.publicName", module) == (
        "NumStability.publicName"
    )
    try:
        logical_name("_private.Other.Owner.0.NumStability.helper", module)
    except ValueError:
        pass
    else:
        raise AssertionError("foreign private owner was accepted")

    stripped = strip_lean_comments(
        ["import A -- tail", "/- outer /- nested -/ -/ public import B"]
    )
    assert stripped == ["import A ", " public import B"]

    row = ManifestRow(
        "NumStability.x", BLOCKLU, "NumStability.Target", "theorem", "public"
    )
    assert manifest_bytes({row.logical_name: row}).startswith(b"format\t1\n")

    assert has_top_level_module_docstring("-- /-! fake\n/-! real -/")
    assert not has_top_level_module_docstring("-- /-! fake\n/- outer /-! fake -/ -/")
    assert validate_import_sequence(Path("Mock.lean"), ["A", "B"], ("A", "B")) == (
        "A",
        "B",
    )
    for bad_imports in (["B", "A"], ["A", "A"]):
        expect_value_error(
            lambda bad_imports=bad_imports: validate_import_sequence(
                Path("Mock.lean"), bad_imports, None
            ),
            f"structural imports {bad_imports}",
        )

    source_destinations = {
        "NumStability.BlockLUFactSpec.firstColumnBelow_eq_of_right_inverse": (
            "NumStability.Source.Higham.Chapter13.Theorem02.Uniqueness"
        ),
        "NumStability.BlockLUFactSpec.firstRow_eq": (
            "NumStability.Source.Higham.Chapter13.Theorem02.Uniqueness"
        ),
        "NumStability.block_lu_one_step_explicit": (
            "NumStability.Source.Higham.Chapter13.Algorithm03"
        ),
    }
    private_actual_names = {
        "_private.<module>.NumStability.sum_ite_eq_val": (
            "_private.NumStability.Algorithms.LU.BlockLU.0."
            "NumStability.sum_ite_eq_val"
        ),
        "_private.<module>.NumStability.sum_ite_eq_val_right": (
            "_private.NumStability.Algorithms.LU.BlockLU.0."
            "NumStability.sum_ite_eq_val_right"
        ),
    }
    test_baseline: dict[str, Declaration] = {}
    test_records: dict[str, ManifestRow] = {}
    for logical, destination in source_destinations.items():
        test_baseline[logical] = Declaration(logical, BLOCKLU, "theorem", "public")
        test_records[logical] = ManifestRow(
            logical, BLOCKLU, destination, "theorem", "public"
        )
    for logical, actual in private_actual_names.items():
        test_baseline[logical] = Declaration(actual, BLOCKLU, "theorem", "private")
        test_records[logical] = ManifestRow(
            logical,
            BLOCKLU,
            RECURSIVE_FACTORIZATION,
            "theorem",
            "private",
        )

    drop_rows = [
        [
            "drop",
            "body",
            source,
            target,
            REVIEWED_BODY_EDGE_DROP_REASON,
        ]
        for source, target in sorted(FROZEN_REVIEWED_BODY_EDGE_DROPS)
    ]

    def dependency_text(rows: list[list[str]]) -> str:
        return "format\t2\n" + "".join("\t".join(row) + "\n" for row in rows)

    def drop_text(rows: list[list[str]], header: str = "format\t1\n") -> str:
        return header + "".join("\t".join(row) + "\n" for row in rows)

    reviewed_edge_rows = [
        [
            "edge",
            "body",
            test_baseline[source].name,
            test_baseline[target].name,
        ]
        for source, target in sorted(FROZEN_REVIEWED_BODY_EDGE_DROPS)
    ]
    block_lu = "NumStability.block_lu_one_step_explicit"
    first_row = "NumStability.BlockLUFactSpec.firstRow_eq"
    sum_left = private_actual_names[
        "_private.<module>.NumStability.sum_ite_eq_val"
    ]
    retained_rows = [
        ["edge", "body", first_row, block_lu],
        ["edge", "body", block_lu, block_lu],
        ["edge", "signature", block_lu, sum_left],
    ]

    with tempfile.TemporaryDirectory() as temp_directory:
        temp = Path(temp_directory)
        drops_path = temp / "drops.tsv"
        baseline_path = temp / "baseline.tsv"
        candidate_path = temp / "candidate.tsv"
        drops_path.write_text(drop_text(drop_rows), encoding="utf-8", newline="\n")
        baseline_path.write_text(
            dependency_text(reviewed_edge_rows + retained_rows),
            encoding="utf-8",
            newline="\n",
        )
        reviewed_drops = read_reviewed_body_edge_drops(
            drops_path, test_records, test_baseline, baseline_path
        )
        assert {
            (drop.source_logical_name, drop.target_logical_name)
            for drop in reviewed_drops
        } == FROZEN_REVIEWED_BODY_EDGE_DROPS

        def read_drops_with(
            rows: list[list[str]],
            *,
            header: str = "format\t1\n",
            dependency_path: Path = baseline_path,
            manifest_records: dict[str, ManifestRow] = test_records,
            baseline_records: dict[str, Declaration] = test_baseline,
        ) -> frozenset[ReviewedBodyEdgeDrop]:
            drops_path.write_text(
                drop_text(rows, header), encoding="utf-8", newline="\n"
            )
            return read_reviewed_body_edge_drops(
                drops_path,
                manifest_records,
                baseline_records,
                dependency_path,
            )

        malformed_rows = [row.copy() for row in drop_rows]
        malformed_rows[0] = malformed_rows[0][:-1]
        expect_value_error(
            lambda: read_drops_with(malformed_rows), "malformed drop row"
        )
        expect_value_error(
            lambda: read_drops_with(drop_rows, header="format\t2\n"),
            "drop format",
        )
        expect_value_error(
            lambda: read_drops_with(drop_rows + [drop_rows[-1].copy()]),
            "duplicate drop row",
        )
        expect_value_error(
            lambda: read_drops_with(list(reversed(drop_rows))),
            "unsorted drop rows",
        )
        wrong_action = [row.copy() for row in drop_rows]
        wrong_action[0][0] = "allow"
        expect_value_error(
            lambda: read_drops_with(wrong_action), "wrong drop action"
        )
        wrong_kind = [row.copy() for row in drop_rows]
        wrong_kind[0][1] = "signature"
        expect_value_error(lambda: read_drops_with(wrong_kind), "wrong edge kind")
        wrong_reason = [row.copy() for row in drop_rows]
        wrong_reason[0][4] = "unspecified"
        expect_value_error(
            lambda: read_drops_with(wrong_reason), "wrong drop reason"
        )
        expect_value_error(
            lambda: read_drops_with(drop_rows[:-1]), "missing frozen drop"
        )
        extra_rows = [row.copy() for row in drop_rows]
        extra_rows.append(
            [
                "drop",
                "body",
                "NumStability.block_lu_one_step_explicit",
                "_private.<module>.NumStability.unreviewed",
                REVIEWED_BODY_EDGE_DROP_REASON,
            ]
        )
        extra_rows.sort(key=lambda fields: (fields[2], fields[3]))
        expect_value_error(
            lambda: read_drops_with(extra_rows), "extra frozen drop"
        )

        missing_manifest_records = dict(test_records)
        missing_manifest_records.pop(first_row)
        expect_value_error(
            lambda: read_drops_with(
                drop_rows, manifest_records=missing_manifest_records
            ),
            "reviewed endpoint missing from manifest",
        )
        wrong_target_records = dict(test_records)
        target_logical = "_private.<module>.NumStability.sum_ite_eq_val"
        target_record = wrong_target_records[target_logical]
        wrong_target_records[target_logical] = ManifestRow(
            target_record.logical_name,
            target_record.historical_module,
            target_record.destination_module,
            target_record.kind,
            "public",
        )
        expect_value_error(
            lambda: read_drops_with(
                drop_rows, manifest_records=wrong_target_records
            ),
            "nonprivate reviewed target",
        )
        missing_baseline_records = dict(test_baseline)
        missing_baseline_records.pop(first_row)
        expect_value_error(
            lambda: read_drops_with(
                drop_rows, baseline_records=missing_baseline_records
            ),
            "reviewed endpoint missing from baseline",
        )

        missing_baseline_edge_path = temp / "missing-baseline-edge.tsv"
        missing_baseline_edge_path.write_text(
            dependency_text(reviewed_edge_rows[:-1] + retained_rows),
            encoding="utf-8",
            newline="\n",
        )
        expect_value_error(
            lambda: read_drops_with(
                drop_rows, dependency_path=missing_baseline_edge_path
            ),
            "absent frozen baseline body edge",
        )
        duplicate_baseline_edge_path = temp / "duplicate-baseline-edge.tsv"
        duplicate_baseline_edge_path.write_text(
            dependency_text(
                reviewed_edge_rows + [reviewed_edge_rows[0]] + retained_rows
            ),
            encoding="utf-8",
            newline="\n",
        )
        expect_value_error(
            lambda: read_drops_with(
                drop_rows, dependency_path=duplicate_baseline_edge_path
            ),
            "duplicate frozen baseline body edge",
        )

        candidate_map = {
            declaration.name: logical
            for logical, declaration in test_baseline.items()
        }
        expected_delta = reviewed_body_edge_drop_delta(
            test_baseline, reviewed_drops
        )

        def validate_candidate(rows: list[list[str]]) -> None:
            candidate_path.write_text(
                dependency_text(rows), encoding="utf-8", newline="\n"
            )
            delta = normalized_graph_delta(
                baseline_path,
                candidate_path,
                test_baseline,
                candidate_map,
                test_records,
            )
            validate_normalized_graph_delta(delta, expected_delta)

        validate_candidate(retained_rows)
        expect_value_error(
            lambda: validate_candidate(retained_rows + [reviewed_edge_rows[0]]),
            "candidate retaining one reviewed edge",
        )
        expect_value_error(
            lambda: validate_candidate(retained_rows[1:]),
            "fifth missing body edge",
        )
        expect_value_error(
            lambda: validate_candidate([retained_rows[0], retained_rows[2]]),
            "missing block_lu_one_step self-edge",
        )
        expect_value_error(
            lambda: validate_candidate(retained_rows[:2]),
            "missing signature edge",
        )
        expect_value_error(
            lambda: validate_candidate(
                retained_rows
                + [["edge", "body", block_lu, "NumStability.candidateOnly"]]
            ),
            "candidate-only edge",
        )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--mode", choices=("pre", "stage", "post"))
    parser.add_argument(
        "--dependency-tsv",
        type=Path,
        help=(
            "frozen baseline TSV in pre mode; freshly generated TSV in "
            "stage/post mode"
        ),
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
        help="retained frozen Phase 11B2 TSV; required in stage/post mode",
    )
    parser.add_argument(
        "--private-rewrites",
        type=Path,
        default=DEFAULT_PRIVATE_REWRITES,
        help="explicit private-name rewrite map required in stage/post mode",
    )
    parser.add_argument(
        "--reviewed-body-edge-drops",
        type=Path,
        help=(
            "fixed reviewed body-edge amendment; required exactly when "
            "RecursiveFactorization is complete"
        ),
    )
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
        "--structural-contract",
        type=Path,
        help=(
            "optional format-1 two-column file freezing every checked structural "
            "module's exact direct imports; contract modules may extend the defaults"
        ),
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
        "--self-test", action="store_true", help="run checker unit smoke tests"
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.self_test:
        run_self_test()
        print("BlockLU Phase 12 ownership checker self-test passed")
        return 0
    if args.mode is None or args.dependency_tsv is None:
        raise ValueError("--mode and --dependency-tsv are required")
    if args.write_manifest and args.mode != "pre":
        raise ValueError("--write-manifest is valid only in pre mode")
    if args.write_manifest and args.routes is None:
        raise ValueError("--write-manifest requires an explicit --routes file")
    if args.mode == "pre" and args.reviewed_body_edge_drops is not None:
        raise ValueError("--reviewed-body-edge-drops is invalid in pre mode")

    ilean_overrides = parse_ilean_overrides(args.ilean)

    if args.mode == "pre":
        if sha256_file(args.dependency_tsv) != BASELINE_TSV_SHA256:
            raise ValueError(
                "pre-migration dependency TSV hash differs from frozen Phase 11B2"
            )
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
                "tracked ownership manifest differs from reviewed route generation"
            )
        digest = validate_expected_manifest_digest(
            records, args.expected_manifest_sha256
        )
        destination_nodes, cross_edges = validate_destination_graph(
            args.dependency_tsv,
            declarations,
            baseline_actual_to_logical(baseline),
            records,
        )
        print(
            "BlockLU Phase 12 pre-migration ownership passed: "
            f"{len(records)} declarations, canonical manifest {digest}, "
            f"acyclic {destination_nodes}-destination graph with "
            f"{cross_edges} cross-owner edges"
        )
        return 0

    if args.baseline_tsv is None:
        raise ValueError("stage/post-migration mode requires --baseline-tsv")
    if sha256_file(args.baseline_tsv) != BASELINE_TSV_SHA256:
        raise ValueError("--baseline-tsv differs from frozen Phase 11B2 input")

    baseline_declarations = read_dependency_declarations(args.baseline_tsv)
    baseline = selected_baseline_declarations(baseline_declarations)
    records = read_manifest(args.manifest)
    validate_manifest_against_baseline(records, baseline)
    if args.routes is not None:
        generated = generate_manifest(
            baseline, args.routes, args.project_root, ilean_overrides
        )
        if records != generated:
            raise ValueError(
                "tracked ownership manifest differs from reviewed route generation"
            )
    digest = validate_expected_manifest_digest(records, args.expected_manifest_sha256)

    all_destinations = {row.destination_module for row in records.values()}
    if args.mode == "stage":
        completed_destinations: set[str] = set()
        for destination in args.completed_destination:
            check_module_name(destination, "--completed-destination")
            completed_destinations.add(destination)
        if args.completed_destinations is not None:
            completed_destinations.update(
                read_completed_destinations(args.completed_destinations)
            )
        if not completed_destinations:
            raise ValueError("stage mode requires a completed-destination set")
        unknown_destinations = sorted(completed_destinations - all_destinations)
        if unknown_destinations:
            raise ValueError(
                "stage mode names destinations outside the frozen manifest: "
                + ", ".join(unknown_destinations)
            )
    else:
        if args.completed_destination or args.completed_destinations is not None:
            raise ValueError(
                "completed-destination options are valid only in stage mode"
            )
        completed_destinations = all_destinations

    recursive_factorization_complete = (
        RECURSIVE_FACTORIZATION in completed_destinations
    )
    has_reviewed_body_edge_drops = args.reviewed_body_edge_drops is not None
    if args.mode == "stage":
        if recursive_factorization_complete and not has_reviewed_body_edge_drops:
            raise ValueError(
                "stage mode requires --reviewed-body-edge-drops when "
                "RecursiveFactorization is completed"
            )
        if has_reviewed_body_edge_drops and not recursive_factorization_complete:
            raise ValueError(
                "stage mode permits --reviewed-body-edge-drops only when "
                "RecursiveFactorization is completed"
            )
    elif not has_reviewed_body_edge_drops:
        raise ValueError("post mode requires --reviewed-body-edge-drops")

    # Recheck the final ownership design from the immutable input even in
    # stage/post invocations; a candidate cannot make a cyclic or improperly
    # layered route map acceptable.
    validate_destination_graph(
        args.baseline_tsv,
        baseline_declarations,
        baseline_actual_to_logical(baseline),
        records,
    )

    completed_logicals = {
        logical
        for logical, row in records.items()
        if row.destination_module in completed_destinations
    }
    rewrites = read_private_rewrites(
        args.private_rewrites,
        records,
        baseline,
        completed_logicals if args.mode == "stage" else None,
    )
    reviewed_body_edge_drops: frozenset[ReviewedBodyEdgeDrop] = frozenset()
    if args.reviewed_body_edge_drops is not None:
        reviewed_body_edge_drops = read_reviewed_body_edge_drops(
            args.reviewed_body_edge_drops,
            records,
            baseline,
            args.baseline_tsv,
        )
    candidate_declarations = read_dependency_declarations(args.dependency_tsv)
    candidate_map = check_candidate_ownership(
        records,
        baseline,
        candidate_declarations,
        rewrites,
        completed_destinations,
    )
    destination_nodes, cross_edges = validate_destination_graph(
        args.dependency_tsv,
        candidate_declarations,
        candidate_map,
        records,
    )

    required_structural_modules = (
        set() if args.mode == "stage" else set(DEFAULT_STRUCTURAL_MODULES)
    )
    for module in args.structural_module:
        check_module_name(module, "--structural-module")
        required_structural_modules.add(module)
    if args.structural_modules is not None:
        required_structural_modules.update(
            read_structural_modules(args.structural_modules)
        )
    structural_contract: dict[str, tuple[str, ...]] | None = None
    structural_modules = required_structural_modules
    if args.structural_contract is not None:
        structural_contract = read_structural_contract(args.structural_contract)
        missing_contracts = sorted(
            required_structural_modules - set(structural_contract)
        )
        if missing_contracts:
            raise ValueError(
                "structural contract omits required modules: "
                + ", ".join(missing_contracts)
            )
        structural_modules = set(structural_contract)
    validate_structural_modules(
        args.project_root,
        candidate_declarations,
        structural_modules,
        structural_contract,
    )

    compare_full_graph(
        args.baseline_tsv,
        args.dependency_tsv,
        baseline,
        candidate_map,
        records,
        reviewed_body_edge_drops,
    )
    graph_preservation = "exact normalized contracted graph preserved"
    if reviewed_body_edge_drops:
        graph_preservation += (
            " except for exactly four reviewed inlined-private-helper body edges"
        )
    if args.mode == "stage":
        print(
            "BlockLU Phase 12 staged ownership passed: "
            f"{len(completed_logicals)} of {len(records)} declarations moved across "
            f"{len(completed_destinations)} completed destinations, canonical "
            f"manifest {digest}, acyclic {destination_nodes}-destination graph "
            f"with {cross_edges} cross-owner edges, and {graph_preservation}"
        )
        return 0
    print(
        "BlockLU Phase 12 post-migration ownership passed: "
        f"{len(records)} declarations, canonical manifest {digest}, "
        f"acyclic {destination_nodes}-destination graph with "
        f"{cross_edges} cross-owner edges, and {graph_preservation}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError) as error:
        print(f"ownership check failed: {error}", file=sys.stderr)
        raise SystemExit(1)
