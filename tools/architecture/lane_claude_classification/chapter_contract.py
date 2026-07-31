#!/usr/bin/env python3
"""Format-2 migration-contract machinery shared by the Chapter 9/11 preparations.

"Format 2" is the repository's contracted semantic dependency stream: a
tab-separated file beginning ``format\t2`` whose rows are ::

    declaration\t<logical_name>\t<module>\t<kind>\t<visibility>
    edge\t<signature|body>\t<source_declaration>\t<target_declaration>

Signature edges and body/proof edges are kept strictly separate everywhere in
this module: they are loaded separately, compared separately, and hashed
separately.  Nothing here renames the reviewed route or ownership TSV headers,
which follow the repository's existing
``docs/architecture/declaration-ownership/`` schema:

    routes      format\t1  then  range\t<historical>\t<first>\t<last>\t<dest>
                           or    exact\t<historical>\t<logical>\t-\t<dest>
    ownership   format\t1  then  <logical>\t<historical>\t<dest>\t<kind>\t<vis>
    rewrites    format\t1  then  <logical>\t<historical_actual>\t<candidate_actual>

Source lines are one-based and inclusive.  Range routes are resolved through
source declaration anchors in the frozen sources; ``exact`` routes take
precedence and exist for reviewed declarations with no usable source anchor
(for example instances produced by a ``deriving`` clause).

This module is preparation-only.  It never writes a production Lean file and
never fabricates post-migration evidence.
"""

from __future__ import annotations

import hashlib
import re
import zipfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable, Iterator, Sequence

import module_evidence as me


FORMAT_ONE = ("format", "1")
FORMAT_TWO = ("format", "2")

SECTION_HEADER_RE = re.compile(r"(?m)^/-!\s*##[^\n]*")
PRIVATE_PREFIX = "_private."
LOGICAL_PRIVATE_TEMPLATE = "_private.<module>."


class ContractError(RuntimeError):
    pass


# ---------------------------------------------------------------------------
# routes
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class RangeRoute:
    historical: str
    first: int
    last: int
    destination: str


@dataclass(frozen=True)
class ExactRoute:
    historical: str
    logical_name: str
    destination: str


@dataclass
class RouteTable:
    ranges: list[RangeRoute] = field(default_factory=list)
    exacts: list[ExactRoute] = field(default_factory=list)

    def by_module(self) -> dict[str, list[RangeRoute]]:
        grouped: dict[str, list[RangeRoute]] = {}
        for route in self.ranges:
            grouped.setdefault(route.historical, []).append(route)
        for routes in grouped.values():
            routes.sort(key=lambda route: route.first)
        return grouped

    def destinations(self) -> list[str]:
        names = {route.destination for route in self.ranges}
        names.update(route.destination for route in self.exacts)
        return sorted(names)


def render_routes(table: RouteTable) -> str:
    lines = ["\t".join(FORMAT_ONE)]
    for route in sorted(table.ranges, key=lambda r: (r.historical, r.first)):
        lines.append(
            "\t".join(["range", route.historical, str(route.first), str(route.last),
                       route.destination])
        )
    for route in sorted(table.exacts, key=lambda r: (r.historical, r.logical_name)):
        lines.append("\t".join(["exact", route.historical, route.logical_name, "-",
                                route.destination]))
    return "\n".join(lines) + "\n"


def load_routes(path: Path) -> RouteTable:
    lines = path.read_text(encoding="utf-8").splitlines()
    if not lines or tuple(lines[0].split("\t")) != FORMAT_ONE:
        raise ContractError(f"{path.name}: missing 'format\\t1' header")
    table = RouteTable()
    for number, line in enumerate(lines[1:], start=2):
        if not line:
            continue
        fields = line.split("\t")
        if len(fields) != 5:
            raise ContractError(f"{path.name}:{number}: expected 5 fields")
        shape, historical, third, fourth, destination = fields
        if shape == "range":
            try:
                first, last = int(third), int(fourth)
            except ValueError as error:
                raise ContractError(f"{path.name}:{number}: non-integer range") from error
            if first < 1 or last < first:
                raise ContractError(f"{path.name}:{number}: invalid range {first}..{last}")
            table.ranges.append(RangeRoute(historical, first, last, destination))
        elif shape == "exact":
            if fourth != "-":
                raise ContractError(f"{path.name}:{number}: exact rows use '-' for the range")
            table.exacts.append(ExactRoute(historical, third, destination))
        else:
            raise ContractError(f"{path.name}:{number}: unknown route shape {shape!r}")
    return table


def route_coverage_failures(
    table: RouteTable, line_counts: dict[str, int]
) -> list[str]:
    """Every candidate line must be covered exactly once."""

    failures: list[str] = []
    grouped = table.by_module()
    for module, count in sorted(line_counts.items()):
        routes = grouped.get(module)
        if not routes:
            failures.append(f"{module}: no range route")
            continue
        cursor = 1
        for route in routes:
            if route.first < cursor:
                failures.append(
                    f"{module}: route {route.first}..{route.last} overlaps line {cursor - 1}"
                )
            elif route.first > cursor:
                failures.append(
                    f"{module}: lines {cursor}..{route.first - 1} are not routed"
                )
            cursor = max(cursor, route.last + 1)
        if cursor != count + 1:
            failures.append(
                f"{module}: routes cover {cursor - 1} of {count} lines"
            )
    for module in sorted(set(grouped) - set(line_counts)):
        failures.append(f"{module}: routed but not a candidate module")
    return failures


# ---------------------------------------------------------------------------
# command groups and source anchors
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class CommandGroup:
    module: str
    first: int
    last: int
    kind: str
    name: str
    is_private: bool


def _doc_block_start(lines: Sequence[str], anchor: int) -> int:
    """Extend an anchor backwards over its doc comment and attribute lines.

    A ``/-! ... -/`` module or section docstring is *not* absorbed: it is a
    command of its own and belongs to the section it introduces, so a
    declaration that follows one immediately keeps its own anchor.
    """

    index = anchor - 2  # zero-based index of the line above the anchor
    start = anchor
    while index >= 0:
        stripped = lines[index].strip()
        if not stripped:
            break
        if stripped.startswith("@[") or stripped.startswith("--"):
            start = index + 1
            index -= 1
            continue
        if stripped.endswith("-/"):
            opener = index
            while opener >= 0:
                candidate = lines[opener].lstrip()
                if candidate.startswith("/--") or candidate.startswith("/-!") \
                        or candidate.startswith("/-"):
                    break
                opener -= 1
            if opener < 0:
                break
            if lines[opener].lstrip().startswith("/-!"):
                break
            start = opener + 1
            index = opener - 1
            continue
        break
    return start


def command_groups(root: Path, relative_path: str) -> list[CommandGroup]:
    """Partition a candidate file into complete, non-overlapping command groups.

    The first group is the preamble (imports, module docstring, namespace
    opening).  Every later group starts at the first line of a top-level
    declaration's documentation/attribute block.
    """

    text = me.read_source(root / relative_path)
    lines = text.split("\n")
    module = ".".join(Path(relative_path).with_suffix("").parts)
    code, _ = me.strip_comments(text)
    declarations = me.declarations_of(code)
    anchors: list[tuple[int, str, str, bool]] = []
    for declaration in declarations:
        anchors.append((
            _doc_block_start(lines, declaration.line),
            declaration.kind,
            declaration.qualified_name or declaration.name,
            declaration.is_private,
        ))
    # A `/-! ## ... -/` section docstring is a command of its own, so a command
    # group can never straddle a reviewed semantic seam.
    for number, line in enumerate(lines, start=1):
        if line.startswith("/-! ##"):
            anchors.append((number, "section", "", False))
    anchors.sort(key=lambda item: item[0])

    total = len(lines)
    groups: list[CommandGroup] = []
    first_anchor = anchors[0][0] if anchors else total + 1
    groups.append(CommandGroup(module, 1, first_anchor - 1, "preamble", "", False))
    for index, (start, kind, name, is_private) in enumerate(anchors):
        end = anchors[index + 1][0] - 1 if index + 1 < len(anchors) else total
        groups.append(CommandGroup(module, start, end, kind, name, is_private))
    return groups


def line_count(root: Path, relative_path: str) -> int:
    return len(me.read_source(root / relative_path).split("\n"))


def section_blocks(root: Path, relative_path: str) -> list[tuple[int, int, str]]:
    """Reviewed semantic seams: the file's own ``/-! ## ... -/`` section blocks."""

    text = me.read_source(root / relative_path)
    lines = text.split("\n")
    starts = [index + 1 for index, line in enumerate(lines) if line.startswith("/-! ##")]
    blocks: list[tuple[int, int, str]] = []
    for position, start in enumerate(starts):
        end = starts[position + 1] - 1 if position + 1 < len(starts) else len(lines)
        blocks.append((start, end, lines[start - 1].strip()))
    return blocks


# ---------------------------------------------------------------------------
# format-2 baseline stream
# ---------------------------------------------------------------------------
@dataclass
class StreamSlice:
    declarations: dict[str, tuple[str, str, str]]        # name -> (module, kind, visibility)
    signature_edges: list[tuple[str, str]]
    body_edges: list[tuple[str, str]]
    all_modules: set[str]
    external_signature_targets: int = 0
    external_body_targets: int = 0


def iter_stream(zip_path: Path) -> Iterator[list[str]]:
    with zipfile.ZipFile(zip_path) as archive:
        names = [name for name in archive.namelist() if name.endswith(".tsv")]
        if len(names) != 1:
            raise ContractError(f"{zip_path.name}: expected exactly one TSV member")
        with archive.open(names[0]) as handle:
            header = handle.readline().decode("utf-8").rstrip("\n")
            if tuple(header.split("\t")) != FORMAT_TWO:
                raise ContractError(f"{zip_path.name}: missing 'format\\t2' header")
            for raw in handle:
                yield raw.decode("utf-8").rstrip("\n").split("\t")


def load_stream(zip_path: Path, modules: Iterable[str]) -> StreamSlice:
    wanted = set(modules)
    declarations: dict[str, tuple[str, str, str]] = {}
    owner_of: dict[str, str] = {}
    signature: list[tuple[str, str]] = []
    body: list[tuple[str, str]] = []
    all_modules: set[str] = set()
    pending: list[list[str]] = []
    for fields in iter_stream(zip_path):
        if fields[0] == "declaration":
            _, name, module, kind, visibility = fields
            all_modules.add(module)
            owner_of[name] = module
            if module in wanted:
                declarations[name] = (module, kind, visibility)
        elif fields[0] == "edge":
            pending.append(fields)
    external_signature = external_body = 0
    for _, edge_kind, source, target in pending:
        if source not in declarations:
            continue
        if target not in owner_of:
            if edge_kind == "signature":
                external_signature += 1
            else:
                external_body += 1
            continue
        if edge_kind == "signature":
            signature.append((source, target))
        elif edge_kind == "body":
            body.append((source, target))
        else:
            raise ContractError(f"unknown edge kind {edge_kind!r}")
    return StreamSlice(
        declarations=declarations,
        signature_edges=sorted(set(signature)),
        body_edges=sorted(set(body)),
        all_modules=all_modules,
        external_signature_targets=external_signature,
        external_body_targets=external_body,
    )


def module_of_declaration(zip_path: Path) -> dict[str, str]:
    mapping: dict[str, str] = {}
    for fields in iter_stream(zip_path):
        if fields[0] == "declaration":
            mapping[fields[1]] = fields[2]
    return mapping


# ---------------------------------------------------------------------------
# private-name normalization
# ---------------------------------------------------------------------------
def private_parts(actual: str) -> tuple[str, str] | None:
    """Split ``_private.<module>.<n>.<qualified>`` into ``(module, qualified)``."""

    if not actual.startswith(PRIVATE_PREFIX):
        return None
    rest = actual[len(PRIVATE_PREFIX):]
    match = re.match(r"^(?P<module>.+?)\.(?P<index>\d+)\.(?P<name>.+)$", rest)
    if match is None:
        return None
    return match.group("module"), match.group("name")


def logical_name(actual: str) -> str:
    parts = private_parts(actual)
    if parts is None:
        return actual
    return LOGICAL_PRIVATE_TEMPLATE + parts[1]


def candidate_private_name(destination: str, qualified: str) -> str:
    return f"{PRIVATE_PREFIX}{destination}.0.{qualified}"


# ---------------------------------------------------------------------------
# ownership
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class OwnershipRow:
    logical_name: str
    historical: str
    destination: str
    kind: str
    visibility: str


def render_ownership(rows: Iterable[OwnershipRow]) -> str:
    lines = ["\t".join(FORMAT_ONE)]
    for row in sorted(rows, key=lambda item: (item.historical, item.logical_name)):
        lines.append("\t".join([row.logical_name, row.historical, row.destination,
                                row.kind, row.visibility]))
    return "\n".join(lines) + "\n"


def load_ownership(path: Path) -> list[OwnershipRow]:
    lines = path.read_text(encoding="utf-8").splitlines()
    if not lines or tuple(lines[0].split("\t")) != FORMAT_ONE:
        raise ContractError(f"{path.name}: missing 'format\\t1' header")
    rows: list[OwnershipRow] = []
    for number, line in enumerate(lines[1:], start=2):
        if not line:
            continue
        fields = line.split("\t")
        if len(fields) != 5:
            raise ContractError(f"{path.name}:{number}: expected 5 fields")
        rows.append(OwnershipRow(*fields))
    return rows


def resolve_ownership(
    root: Path,
    table: RouteTable,
    stream: StreamSlice,
    candidates: dict[str, str],
) -> tuple[list[OwnershipRow], list[str]]:
    """Route every stream declaration of the candidate modules to one destination.

    Authored declarations resolve through their source command group; compiler
    satellites (constructors, recursors, projections, ``deriving`` output)
    resolve through their authored root or an explicit ``exact`` route.
    """

    failures: list[str] = []
    grouped = table.by_module()
    exact_by_module: dict[str, dict[str, str]] = {}
    for route in table.exacts:
        exact_by_module.setdefault(route.historical, {})[route.logical_name] = route.destination

    anchors: dict[str, dict[str, int]] = {}
    for module, relative in candidates.items():
        anchors[module] = {}
        for group in command_groups(root, relative):
            if group.kind == "preamble":
                continue
            anchors[module][group.name] = group.first

    def destination_for_line(module: str, line: int) -> str | None:
        for route in grouped.get(module, ()):
            if route.first <= line <= route.last:
                return route.destination
        return None

    rows: list[OwnershipRow] = []
    for name, (module, kind, visibility) in sorted(stream.declarations.items()):
        exact = exact_by_module.get(module, {}).get(name)
        logical = logical_name(name)
        if exact is None:
            exact = exact_by_module.get(module, {}).get(logical)
        if exact is not None:
            rows.append(OwnershipRow(logical, module, exact, kind, visibility))
            continue
        parts = private_parts(name)
        qualified = parts[1] if parts else name
        line = anchors[module].get(qualified)
        if line is None:
            root_name = None
            for candidate in anchors[module]:
                if qualified.startswith(candidate + ".") and (
                    root_name is None or len(candidate) > len(root_name)
                ):
                    root_name = candidate
            if root_name is not None:
                line = anchors[module][root_name]
        if line is None:
            failures.append(
                f"{module}: no source anchor or exact route for {name}"
            )
            continue
        destination = destination_for_line(module, line)
        if destination is None:
            failures.append(f"{module}: line {line} for {name} is not routed")
            continue
        rows.append(OwnershipRow(logical, module, destination, kind, visibility))
    return rows, failures


# ---------------------------------------------------------------------------
# destination graph
# ---------------------------------------------------------------------------
def destination_of_declaration(
    rows: Iterable[OwnershipRow], stream: StreamSlice
) -> dict[str, str]:
    by_logical: dict[tuple[str, str], str] = {}
    for row in rows:
        by_logical[(row.historical, row.logical_name)] = row.destination
    mapping: dict[str, str] = {}
    for name, (module, _kind, _visibility) in stream.declarations.items():
        destination = by_logical.get((module, logical_name(name)))
        if destination is not None:
            mapping[name] = destination
    return mapping


def owner_graph(
    edges: Iterable[tuple[str, str]],
    destination: dict[str, str],
    external_module: dict[str, str],
) -> dict[str, set[str]]:
    graph: dict[str, set[str]] = {}
    for source, target in edges:
        source_owner = destination.get(source)
        if source_owner is None:
            continue
        target_owner = destination.get(target) or external_module.get(target)
        if target_owner is None or target_owner == source_owner:
            continue
        graph.setdefault(source_owner, set()).add(target_owner)
    return graph


def cycles(graph: dict[str, set[str]], nodes: Iterable[str]) -> list[list[str]]:
    """Return one representative cycle per non-trivial strongly connected component."""

    index: dict[str, int] = {}
    low: dict[str, int] = {}
    on_stack: dict[str, bool] = {}
    stack: list[str] = []
    counter = [0]
    found: list[list[str]] = []

    def strongconnect(node: str) -> None:
        index[node] = low[node] = counter[0]
        counter[0] += 1
        stack.append(node)
        on_stack[node] = True
        for neighbour in sorted(graph.get(node, ())):
            if neighbour not in index:
                strongconnect(neighbour)
                low[node] = min(low[node], low[neighbour])
            elif on_stack.get(neighbour):
                low[node] = min(low[node], index[neighbour])
        if low[node] == index[node]:
            component = []
            while True:
                member = stack.pop()
                on_stack[member] = False
                component.append(member)
                if member == node:
                    break
            if len(component) > 1:
                found.append(sorted(component))

    for node in sorted(set(nodes) | set(graph)):
        if node not in index:
            strongconnect(node)
    return found


# ---------------------------------------------------------------------------
# hashing
# ---------------------------------------------------------------------------
def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest().upper()


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def normalized_edge_digest(
    edges: Iterable[tuple[str, str]], kind: str
) -> tuple[int, str]:
    """Hash a typed edge set after private-name normalization.

    The digest is the frozen format-2 contract for one edge kind: it must be
    reproducible from the packaged baseline and, after a migration, from a
    fresh candidate stream once the reviewed private rewrites are applied.
    """

    normalized = sorted({(kind, logical_name(source), logical_name(target))
                         for source, target in edges})
    payload = "\n".join("\t".join(row) for row in normalized) + "\n"
    return len(normalized), sha256_text(payload)


def normalized_declaration_digest(rows: Iterable[OwnershipRow]) -> tuple[int, str]:
    normalized = sorted(
        (row.logical_name, row.destination, row.kind, row.visibility) for row in rows
    )
    payload = "\n".join("\t".join(row) for row in normalized) + "\n"
    return len(normalized), sha256_text(payload)


# ---------------------------------------------------------------------------
# downstream consumers
# ---------------------------------------------------------------------------
# This lane's own isolated audit modules are evidence, not part of the
# repository's contract surface, so they are excluded from the consumer tables.
# A consumer table answers "what does the integrator have to keep working when
# these declarations move", and that question is about the tree as it stood at
# the frozen base.
LANE_TEST_PREFIX = "NumStabilityTest/Worker/ClassificationAudit/"


def consumer_rows(root: Path, historical: Iterable[str]) -> list[tuple[str, str, str]]:
    targets = set(historical)
    rows: list[tuple[str, str, str]] = []
    for relative in me.iter_repository_lean_paths(root):
        if relative.startswith(LANE_TEST_PREFIX):
            continue
        module = ".".join(Path(relative).with_suffix("").parts)
        if module in targets:
            continue
        code, _ = me.strip_comments(me.read_source(root / relative))
        imports = set(me.IMPORT_RE.findall(code))
        surface = (
            "test" if relative.startswith("NumStabilityTest")
            else "example" if relative.startswith("examples") else "production"
        )
        for target in sorted(imports & targets):
            rows.append((module, target, surface))
    return sorted(rows)


def render_consumers(rows: Iterable[tuple[str, str, str]]) -> str:
    lines = ["\t".join(FORMAT_ONE)]
    for consumer, target, surface in sorted(rows):
        lines.append("\t".join(["consumer", consumer, target, surface]))
    return "\n".join(lines) + "\n"


def render_direct_imports(planned: dict[str, list[str]]) -> str:
    lines = ["\t".join(FORMAT_ONE)]
    for destination in sorted(planned):
        for target in sorted(planned[destination]):
            lines.append("\t".join(["import", destination, target]))
    return "\n".join(lines) + "\n"


def render_private_rewrites(rows: Iterable[tuple[str, str, str]]) -> str:
    lines = ["\t".join(FORMAT_ONE)]
    for row in sorted(rows):
        lines.append("\t".join(row))
    return "\n".join(lines) + "\n"


def load_two_column_table(path: Path, shape: str, width: int) -> list[tuple[str, ...]]:
    lines = path.read_text(encoding="utf-8").splitlines()
    if not lines or tuple(lines[0].split("\t")) != FORMAT_ONE:
        raise ContractError(f"{path.name}: missing 'format\\t1' header")
    rows: list[tuple[str, ...]] = []
    for number, line in enumerate(lines[1:], start=2):
        if not line:
            continue
        fields = line.split("\t")
        if fields[0] != shape or len(fields) != width:
            raise ContractError(
                f"{path.name}:{number}: expected a {shape} row with {width} fields"
            )
        rows.append(tuple(fields[1:]))
    return rows
