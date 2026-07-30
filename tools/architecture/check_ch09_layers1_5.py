#!/usr/bin/env python3
"""Materialize and verify Chapter 9 destination-DAG layers 1--5.

The full Chapter 9 proposal remains the authoritative classification contract.
This tool derives a dependency-closed first implementation wave from it,
freezes the exact 1,675 declaration routes, and checks source-command bytes,
ownership, private-name rewrites, and normalized signature/body dependencies.
"""

from __future__ import annotations

import argparse
import collections
import csv
import hashlib
import json
import re
import subprocess
import sys
import tempfile
import zipfile
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parents[2]
LANE_TOOLS = ROOT / "tools/architecture/lane_claude_classification"
sys.path.insert(0, str(LANE_TOOLS))

from lane_common import (  # noqa: E402
    SourceCommandIndex,
    augment_entries_from_source,
    read_ilean_entries,
    sha256_bytes,
)


BASE_REVISION = "32771e355612a6fca1b6153733d3f0dc124d26e2"
EVIDENCE_REVISION = "9e7c8e32437d6ea28bf297fc4f08756288df9b26"
PACKET_REVISION = "6487fc33088523b8f27ecde9ad613515b78f9977"

FULL_CONTRACT = (
    ROOT / "docs/architecture/lane-proposals/claude-classification/ch09"
)
OWNERSHIP_ROOT = ROOT / "docs/architecture/declaration-ownership"
PREFIX = "ch09-layers1-5"
ACCEPTANCE = OWNERSHIP_ROOT / f"{PREFIX}-acceptance.json"
DESTINATIONS = OWNERSHIP_ROOT / f"{PREFIX}-destinations.tsv"
FROZEN_OWNERS = OWNERSHIP_ROOT / f"{PREFIX}-frozen-owners.tsv"
IMPORTS = OWNERSHIP_ROOT / f"{PREFIX}-imports.tsv"
OWNERSHIP = OWNERSHIP_ROOT / f"{PREFIX}-ownership.tsv"
PRIVATE_REWRITES = OWNERSHIP_ROOT / f"{PREFIX}-private-rewrites.tsv"
ROUTES = OWNERSHIP_ROOT / f"{PREFIX}-routes.tsv"

HISTORICAL_GIANT = "NumStability.Algorithms.HighamChapter9"
HISTORICAL_PRIMITIVE = "NumStability.Algorithms.HighamChapter9Theorem914Primitive"
HISTORICAL_CORRECTION = "NumStability.Algorithms.HighamChapter9ComputedCorrection"
HISTORICAL_OWNERS = {
    HISTORICAL_GIANT,
    HISTORICAL_PRIMITIVE,
    HISTORICAL_CORRECTION,
}

DESTINATION_LAYERS = {
    "NumStability.Source.Higham.Chapter09.Section01": 1,
    "NumStability.Source.Higham.Chapter09.Theorem914Primitive": 1,
    "NumStability.Source.Higham.Chapter09.Section02": 2,
    "NumStability.Source.Higham.Chapter09.ComputedCorrection": 3,
    "NumStability.Source.Higham.Chapter09.Section03": 3,
    "NumStability.Source.Higham.Chapter09.Section04": 3,
    "NumStability.Source.Higham.Chapter09.Section05": 4,
    "NumStability.Source.Higham.Chapter09.Section06": 5,
}
EXPECTED_DECLARATIONS = 1675
EXPECTED_COMMAND_GROUPS = 1494
EXPECTED_PRIVATE = 10

IMPORT_RE = re.compile(
    r"(?m)^\s*(?:(?:public|private)\s+)?import\s+([A-Za-z0-9_'.]+)\s*$"
)
MODULE_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*$")


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
class Route:
    historical_module: str
    name: str
    normalized_name: str
    command_root: str
    normalized_root: str
    provenance: str
    span: tuple[int, int, int, int, int, int, int, int]
    command_sha256: str
    destination: str

    @classmethod
    def parse(cls, row: list[str]) -> "Route":
        if len(row) != 17 or row[0] != "route":
            fail(f"malformed route row: {row[:4]}")
        try:
            span = tuple(int(value) for value in row[7:15])
        except ValueError as error:
            fail(f"noninteger route span for {row[2]}: {error}")
        if len(span) != 8:
            fail(f"wrong route span width for {row[2]}")
        return cls(*row[1:7], span, row[15], row[16])

    def fields(self) -> list[str]:
        return [
            "route",
            self.historical_module,
            self.name,
            self.normalized_name,
            self.command_root,
            self.normalized_root,
            self.provenance,
            *(str(value) for value in self.span),
            self.command_sha256,
            self.destination,
        ]


def fail(message: str) -> None:
    raise ValueError(message)


def module_path(module: str, suffix: str = ".lean") -> Path:
    if not MODULE_RE.fullmatch(module):
        fail(f"invalid Lean module name: {module}")
    return Path(*module.split(".")).with_suffix(suffix)


def git(*args: str, text: bool = True) -> str | bytes:
    return subprocess.check_output(["git", *args], cwd=ROOT, text=text)


def git_show(revision: str, path: Path) -> bytes:
    return subprocess.check_output(
        ["git", "show", f"{revision}:{path.as_posix()}"], cwd=ROOT
    )


def git_blob(revision: str, path: Path) -> str:
    return str(git("rev-parse", f"{revision}:{path.as_posix()}")).strip()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def stable_json(value: object) -> bytes:
    return (
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    ).encode("utf-8")


def tsv_bytes(rows: Iterable[Iterable[object]], version: int = 1) -> bytes:
    output = [f"format\t{version}"]
    output.extend("\t".join(str(cell) for cell in row) for row in rows)
    return ("\n".join(output) + "\n").encode("utf-8")


def read_format(path: Path, version: int, width: int) -> list[list[str]]:
    lines = path.read_text(encoding="utf-8").splitlines()
    if not lines or lines[0].split("\t") != ["format", str(version)]:
        fail(f"{path}: expected format {version}")
    rows = [line.split("\t") for line in lines[1:]]
    if any(len(row) != width for row in rows):
        fail(f"{path}: expected {width}-column rows")
    return rows


def read_graph(path: Path) -> tuple[dict[str, Declaration], list[Edge]]:
    if path.suffix.casefold() == ".zip":
        with zipfile.ZipFile(path) as archive:
            names = archive.namelist()
            if len(names) != 1:
                fail(f"{path}: expected exactly one archive member")
            payload = archive.read(names[0])
    else:
        payload = path.read_bytes()
    declarations: dict[str, Declaration] = {}
    edges: list[Edge] = []
    for number, line in enumerate(payload.decode("utf-8").splitlines(), 1):
        fields = line.split("\t")
        if number == 1:
            if fields != ["format", "2"]:
                fail(f"{path}: expected format 2")
        elif fields[:1] == ["declaration"] and len(fields) == 5:
            declaration = Declaration(*fields[1:])
            if declaration.name in declarations:
                fail(f"{path}:{number}: duplicate declaration {declaration.name}")
            declarations[declaration.name] = declaration
        elif fields[:1] == ["edge"] and len(fields) == 4:
            if fields[1] not in {"signature", "body"}:
                fail(f"{path}:{number}: unsupported edge kind")
            edges.append(Edge(*fields[1:]))
        else:
            fail(f"{path}:{number}: malformed format-2 row")
    return declarations, edges


def full_routes() -> dict[str, Route]:
    routes = {
        route.name: route
        for route in (
            Route.parse(row) for row in read_format(FULL_CONTRACT / "routes.tsv", 2, 17)
        )
        if route.destination in DESTINATION_LAYERS
    }
    if len(routes) != EXPECTED_DECLARATIONS:
        fail(
            f"layers 1--5 must contain {EXPECTED_DECLARATIONS} declarations, "
            f"found {len(routes)}"
        )
    if {route.historical_module for route in routes.values()} != HISTORICAL_OWNERS:
        fail("layers 1--5 historical owner set drifted")
    if {route.destination for route in routes.values()} != set(DESTINATION_LAYERS):
        fail("layers 1--5 destination set drifted")
    return routes


def route_groups(
    routes: dict[str, Route],
) -> dict[tuple[str, tuple[int, ...]], list[Route]]:
    groups: dict[tuple[str, tuple[int, ...]], list[Route]] = collections.defaultdict(list)
    for route in routes.values():
        groups[(route.historical_module, route.span)].append(route)
    for members in groups.values():
        if len({member.destination for member in members}) != 1:
            fail(f"compiler command split across destinations: {members[0].command_root}")
        authored = [member for member in members if member.provenance == "authored"]
        if len(authored) != 1 or authored[0].name != authored[0].command_root:
            fail(f"command group lacks one authored root: {members[0].command_root}")
    if len(groups) != EXPECTED_COMMAND_GROUPS:
        fail(
            f"layers 1--5 must contain {EXPECTED_COMMAND_GROUPS} command groups, "
            f"found {len(groups)}"
        )
    return groups


def command_root(members: list[Route]) -> Route:
    return next(member for member in members if member.provenance == "authored")


def parse_imports(payload: bytes) -> list[str]:
    return IMPORT_RE.findall(payload.decode("utf-8-sig"))


def full_dag() -> tuple[set[str], set[tuple[str, str]]]:
    all_destinations = {
        Route.parse(row).destination
        for row in read_format(FULL_CONTRACT / "routes.tsv", 2, 17)
    }
    edges = set()
    for row in read_format(FULL_CONTRACT / "owner-dag.tsv", 1, 5):
        if row[0] != "edge":
            fail("malformed full Chapter 9 owner DAG")
        edges.add((row[1], row[2]))
    return all_destinations, edges


def derived_layers() -> dict[str, int]:
    nodes, edges = full_dag()
    dependencies: dict[str, set[str]] = collections.defaultdict(set)
    for source, target in edges:
        dependencies[source].add(target)
    visiting: set[str] = set()
    memo: dict[str, int] = {}

    def level(node: str) -> int:
        if node in memo:
            return memo[node]
        if node in visiting:
            fail("cycle in full Chapter 9 owner DAG")
        visiting.add(node)
        result = 1 + max((level(item) for item in dependencies[node]), default=0)
        visiting.remove(node)
        memo[node] = result
        return result

    return {node: level(node) for node in nodes}


def wave_dependencies() -> dict[str, set[str]]:
    _, edges = full_dag()
    result: dict[str, set[str]] = collections.defaultdict(set)
    for source, target in edges:
        if source in DESTINATION_LAYERS and target in DESTINATION_LAYERS:
            result[source].add(target)
    return result


def verify_revision_stability() -> None:
    candidates = list(
        csv.DictReader(
            (FULL_CONTRACT / "candidate-modules.tsv").open(
                encoding="utf-8", newline=""
            ),
            delimiter="\t",
        )
    )
    if len(candidates) != 11:
        fail("full Chapter 9 candidate module count drifted")
    changed = []
    for row in candidates:
        path = Path(row["path"])
        evidence = git_blob(EVIDENCE_REVISION, path)
        base = git_blob(BASE_REVISION, path)
        if evidence != base:
            changed.append((path.as_posix(), evidence, base))
    if changed:
        fail(f"candidate production paths changed after evidence review: {changed}")


def owner_path(owner: str) -> Path:
    return module_path(owner)


def frozen_sources(revision: str = PACKET_REVISION) -> dict[str, bytes]:
    return {owner: git_show(revision, owner_path(owner)) for owner in HISTORICAL_OWNERS}


_SOURCE_INDEX_CACHE: dict[tuple[str, str], SourceCommandIndex] = {}
_COMMAND_CACHE: dict[tuple[str, str, tuple[int, ...]], bytes] = {}
_SOURCE_DIGEST_CACHE: dict[int, str] = {}


def command_bytes(route: Route, sources: dict[str, bytes]) -> bytes:
    payload = sources[route.historical_module]
    digest = _SOURCE_DIGEST_CACHE.get(id(payload))
    if digest is None:
        digest = sha256_bytes(payload)
        _SOURCE_DIGEST_CACHE[id(payload)] = digest
    source_key = (route.historical_module, digest)
    index = _SOURCE_INDEX_CACHE.get(source_key)
    if index is None:
        index = SourceCommandIndex(payload)
        _SOURCE_INDEX_CACHE[source_key] = index
    command_key = (*source_key, route.span)
    if command_key not in _COMMAND_CACHE:
        _COMMAND_CACHE[command_key] = index.command(route.span)
    return _COMMAND_CACHE[command_key]


def expected_imports() -> dict[str, list[str]]:
    common = parse_imports(git_show(BASE_REVISION, owner_path(HISTORICAL_GIANT)))
    if "NumStability.Algorithms.LU.BlockLU" in common:
        fail("base common import set reintroduced the retired BlockLU umbrella")
    dependencies = wave_dependencies()
    result: dict[str, list[str]] = {}
    for destination in DESTINATION_LAYERS:
        imports = list(common)
        if destination == "NumStability.Source.Higham.Chapter09.ComputedCorrection":
            imports.append("NumStability.Analysis.InstabilityWithoutCancellation")
        imports.extend(sorted(dependencies[destination], key=str.casefold))
        result[destination] = sorted(set(imports), key=str.casefold)
    return result


def private_rows(routes: dict[str, Route]) -> list[list[str]]:
    selected_private = {
        name for name in routes if name.startswith("_private.")
    }
    full = {
        row[0]: row
        for row in read_format(FULL_CONTRACT / "private-rewrites.tsv", 1, 3)
    }
    if set(full) & selected_private != selected_private:
        fail("full private-rewrite artifact does not cover the wave")
    rows = [full[name] for name in sorted(selected_private)]
    if len(rows) != EXPECTED_PRIVATE:
        fail(f"expected {EXPECTED_PRIVATE} private rewrites, found {len(rows)}")
    return rows


def normalized_incident_graph(
    edges: Iterable[Edge], actual_to_logical: dict[str, str]
) -> collections.Counter[tuple[str, str, str]]:
    selected = set(actual_to_logical)
    result: collections.Counter[tuple[str, str, str]] = collections.Counter()
    external_private_owners: dict[str, str] = {}

    def normalize(name: str) -> str:
        if name in selected:
            return f"@CH09:{actual_to_logical[name]}"
        if not name.startswith("_private."):
            return name
        marker = ".0."
        if marker not in name:
            fail(f"incident external private name lacks normalized owner index: {name}")
        suffix = name.split(marker, 1)[1]
        previous = external_private_owners.setdefault(suffix, name)
        if previous != name:
            fail(
                "incident external private normalization collision: "
                f"{previous} and {name}"
            )
        return f"@EXTERNAL_PRIVATE:{suffix}"

    for edge in edges:
        if edge.source not in selected and edge.target not in selected:
            continue
        source = normalize(edge.source)
        target = normalize(edge.target)
        result[(edge.kind, source, target)] += 1
    return result


def graph_sha256(graph: collections.Counter[tuple[str, str, str]]) -> str:
    payload = tsv_bytes(
        (
            ("edge", kind, source, target, count)
            for (kind, source, target), count in sorted(graph.items())
        )
    )
    return sha256_bytes(payload)


def generated_artifacts(
    baseline_path: Path,
) -> tuple[dict[Path, bytes], dict[str, object]]:
    verify_revision_stability()
    layers = derived_layers()
    actual_layers = {name: layers[name] for name in DESTINATION_LAYERS}
    if actual_layers != DESTINATION_LAYERS:
        fail(f"derived layer partition drifted: {actual_layers}")
    routes = full_routes()
    groups = route_groups(routes)
    declarations, edges = read_graph(baseline_path)
    if set(routes) - set(declarations):
        fail("frozen baseline lacks routed declarations")
    for name, route in routes.items():
        declaration = declarations[name]
        if declaration.module != route.historical_module:
            fail(f"{name}: baseline historical owner drift")

    route_payload = tsv_bytes(
        (routes[name].fields() for name in sorted(routes)), version=2
    )
    full_ownership = {
        row[0]: row
        for row in read_format(FULL_CONTRACT / "ownership.tsv", 1, 5)
    }
    ownership_rows = [full_ownership[name] for name in sorted(routes)]
    if len(ownership_rows) != len(routes):
        fail("full ownership artifact does not cover wave routes")
    ownership_payload = tsv_bytes(ownership_rows)

    destinations_rows = []
    for destination, layer in sorted(
        DESTINATION_LAYERS.items(), key=lambda item: (item[1], item[0].casefold())
    ):
        selected = [route for route in routes.values() if route.destination == destination]
        destination_groups = {
            (route.historical_module, route.span) for route in selected
        }
        owners = {route.historical_module for route in selected}
        if len(owners) != 1:
            fail(f"{destination}: destination combines historical owners")
        destinations_rows.append(
            [
                "destination",
                destination,
                layer,
                len(selected),
                len(destination_groups),
                next(iter(owners)),
            ]
        )
    destinations_payload = tsv_bytes(destinations_rows)

    owner_rows = []
    for owner in sorted(HISTORICAL_OWNERS):
        path = owner_path(owner)
        evidence_blob = git_blob(EVIDENCE_REVISION, path)
        base_blob = git_blob(BASE_REVISION, path)
        if evidence_blob != base_blob:
            fail(f"{owner}: evidence/base blob drift")
        payload = git_show(BASE_REVISION, path)
        owner_selected = [route for route in routes.values() if route.historical_module == owner]
        owner_groups = {
            route.span for route in owner_selected
        }
        full_owner_count = sum(
            Route.parse(row).historical_module == owner
            for row in read_format(FULL_CONTRACT / "routes.tsv", 2, 17)
        )
        owner_rows.append(
            [
                "owner",
                owner,
                path.as_posix(),
                evidence_blob,
                base_blob,
                sha256_bytes(payload),
                len(payload.decode("utf-8").splitlines()),
                len(owner_selected),
                len(owner_groups),
                "complete" if len(owner_selected) == full_owner_count else "partial",
            ]
        )
    frozen_payload = tsv_bytes(owner_rows)

    import_rows = []
    for destination, imports in sorted(expected_imports().items()):
        for imported in imports:
            reason = (
                "destination_dependency"
                if imported in wave_dependencies()[destination]
                else "frozen_owner_direct_import"
            )
            import_rows.append(["import", destination, imported, reason])
    imports_payload = tsv_bytes(import_rows)
    private_payload = tsv_bytes(private_rows(routes))

    baseline_map = {name: name for name in routes}
    incident = normalized_incident_graph(edges, baseline_map)
    signature_edges = sum(
        count for (kind, _, _), count in incident.items() if kind == "signature"
    )
    body_edges = sum(
        count for (kind, _, _), count in incident.items() if kind == "body"
    )
    internal_edges = sum(
        count
        for (_, source, target), count in incident.items()
        if source.startswith("@CH09:") and target.startswith("@CH09:")
    )

    artifacts = {
        DESTINATIONS: destinations_payload,
        FROZEN_OWNERS: frozen_payload,
        IMPORTS: imports_payload,
        OWNERSHIP: ownership_payload,
        PRIVATE_REWRITES: private_payload,
        ROUTES: route_payload,
    }
    acceptance = {
        "schema_version": 1,
        "chapter": "09",
        "wave": "destination_dag_layers_1_to_5",
        "base_revision": BASE_REVISION,
        "review_evidence_revision": EVIDENCE_REVISION,
        "packet_revision": PACKET_REVISION,
        "destinations": len(DESTINATION_LAYERS),
        "historical_owners": len(HISTORICAL_OWNERS),
        "routed_declarations": len(routes),
        "command_groups": len(groups),
        "private_rewrites": EXPECTED_PRIVATE,
        "baseline_incident_signature_edges": signature_edges,
        "baseline_incident_body_edges": body_edges,
        "baseline_internal_typed_edges": internal_edges,
        "baseline_normalized_incident_sha256": graph_sha256(incident),
        "baseline_format2_sha256": sha256_file(baseline_path),
        "full_contract_artifacts_sha256": {
            name: sha256_file(FULL_CONTRACT / name)
            for name in (
                "acceptance.json",
                "candidate-modules.tsv",
                "owner-dag.tsv",
                "ownership.tsv",
                "private-rewrites.tsv",
                "routes.tsv",
            )
        },
        "artifact_sha256": {
            path.name: sha256_bytes(payload)
            for path, payload in sorted(artifacts.items(), key=lambda item: item[0].name)
        },
    }
    artifacts[ACCEPTANCE] = stable_json(acceptance)
    return artifacts, acceptance


def write_contract(baseline_path: Path) -> None:
    artifacts, _ = generated_artifacts(baseline_path)
    for path, payload in artifacts.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(payload)


def validate_contract(baseline_path: Path) -> dict[str, object]:
    expected, acceptance = generated_artifacts(baseline_path)
    for path, payload in expected.items():
        if not path.is_file() or path.read_bytes() != payload:
            fail(f"tracked wave contract differs from deterministic output: {path}")
    return acceptance


def destination_routes(routes: dict[str, Route]) -> dict[str, list[Route]]:
    groups = route_groups(routes)
    result: dict[str, list[Route]] = collections.defaultdict(list)
    for members in groups.values():
        root = command_root(members)
        result[root.destination].append(root)
    for destination in result:
        result[destination].sort(
            key=lambda route: (route.historical_module, route.span, route.command_root)
        )
    return result


def read_import_contract() -> dict[str, list[str]]:
    result: dict[str, list[str]] = collections.defaultdict(list)
    for row in read_format(IMPORTS, 1, 4):
        if row[0] != "import" or row[1] not in DESTINATION_LAYERS:
            fail("malformed wave import row")
        result[row[1]].append(row[2])
    if set(result) != set(DESTINATION_LAYERS):
        fail("wave import artifact does not cover every destination")
    return result


def destination_payload(
    destination: str,
    routes: list[Route],
    sources: dict[str, bytes],
    imports: dict[str, list[str]],
) -> bytes:
    title = destination.rsplit(".", 1)[-1]
    header = "".join(f"import {item}\n" for item in imports[destination])
    header += (
        "\n/-!\n"
        f"# Higham Chapter 9: {title}\n\n"
        f"Canonical source-correspondence owner from Chapter 9 destination-DAG "
        f"layer {DESTINATION_LAYERS[destination]}.\n"
        "-/\n\n"
        "namespace NumStability\n\n"
        "open scoped BigOperators\n"
        "open ComplexConjugate\n"
        "open Matrix\n\n"
    )
    commands = []
    for route in routes:
        payload = command_bytes(route, sources)
        if sha256_bytes(payload) != route.command_sha256:
            fail(f"{route.command_root}: frozen command hash drift")
        commands.append(payload.rstrip(b"\n"))
    return header.encode("utf-8") + b"\n\n".join(commands) + b"\n\nend NumStability\n"


def inject_imports(payload: bytes, modules: Iterable[str]) -> bytes:
    modules = [module for module in modules if module not in parse_imports(payload)]
    if not modules:
        return payload
    matches = list(
        re.finditer(rb"(?m)^\s*(?:public\s+|private\s+)?import\s+[A-Za-z0-9_'.]+\s*\n", payload)
    )
    if not matches:
        fail("partial historical owner has no import block")
    offset = matches[-1].end()
    addition = "".join(f"import {module}\n" for module in sorted(modules)).encode()
    return payload[:offset] + addition + payload[offset:]


def source_offset(index: SourceCommandIndex, line: int, column: int) -> int:
    if line == len(index.lines) and column == 0:
        return len(index.payload)
    if line >= len(index.lines):
        fail(f"source coordinate line {line} exceeds {len(index.lines)}")
    content = index.lines[line].rstrip(b"\n").decode("utf-8")
    if column > len(content):
        fail(f"source coordinate column {column} exceeds line {line}")
    return index.offsets[line] + len(content[:column].encode("utf-8"))


def residual_giant_payload(
    routes: dict[str, Route], sources: dict[str, bytes]
) -> bytes:
    base = git_show(BASE_REVISION, owner_path(HISTORICAL_GIANT))
    frozen = sources[HISTORICAL_GIANT]
    marker = b"namespace NumStability\n"
    base_body = base.find(marker)
    frozen_body = frozen.find(marker)
    if min(base_body, frozen_body) < 0 or base[base_body:] != frozen[frozen_body:]:
        fail("integration-base Chapter 9 body differs from the frozen routed body")
    digest = sha256_bytes(frozen)
    index = _SOURCE_INDEX_CACHE.get((HISTORICAL_GIANT, digest))
    if index is None:
        index = SourceCommandIndex(frozen)
        _SOURCE_INDEX_CACHE[(HISTORICAL_GIANT, digest)] = index
    giant_groups = [
        members
        for (owner, _), members in route_groups(routes).items()
        if owner == HISTORICAL_GIANT
    ]
    ranges = []
    for members in giant_groups:
        root = command_root(members)
        command = command_bytes(root, sources)
        start = source_offset(index, root.span[0], root.span[1])
        end = source_offset(index, root.span[2], root.span[3])
        if frozen[start:end] != command:
            fail(f"{root.command_root}: route offsets disagree with command payload")
        ranges.append((start, end, root.command_root))
    ranges.sort()
    for previous, current in zip(ranges, ranges[1:]):
        if current[0] < previous[1]:
            fail(f"overlapping command ranges: {previous[2]} and {current[2]}")
    if ranges and ranges[0][0] < frozen_body:
        fail("a routed Chapter 9 command precedes the namespace body")
    pieces = []
    cursor = frozen_body
    for start, end, _ in ranges:
        pieces.append(frozen[cursor:start])
        cursor = end
    pieces.append(frozen[cursor:])
    live = base[:base_body] + b"".join(pieces)
    section_destinations = sorted(
        destination
        for destination in DESTINATION_LAYERS
        if destination.rsplit(".", 1)[-1].startswith("Section")
    )
    return inject_imports(live, section_destinations)


def public_roots_by_destination(
    routes: dict[str, Route], baseline: dict[str, Declaration]
) -> dict[str, list[str]]:
    result: dict[str, list[str]] = collections.defaultdict(list)
    for members in route_groups(routes).values():
        root = command_root(members)
        if baseline[root.name].visibility == "public":
            result[root.destination].append(root.name)
    for destination in result:
        result[destination].sort()
    if any(not result[destination] for destination in DESTINATION_LAYERS):
        fail("a wave destination lacks a public smoke-test root")
    return result


def test_payloads(
    routes: dict[str, Route], baseline: dict[str, Declaration]
) -> dict[Path, bytes]:
    roots = public_roots_by_destination(routes, baseline)
    result: dict[Path, bytes] = {}
    modules: list[str] = []
    for destination in sorted(DESTINATION_LAYERS):
        label = destination.rsplit(".", 1)[-1]
        module = f"NumStabilityTest.Worker.Ch09.Canonical.{label}"
        payload = f"import {destination}\n\n#check {roots[destination][0]}\n"
        result[ROOT / module_path(module)] = payload.encode()
        modules.append(module)

    by_owner: dict[str, list[str]] = collections.defaultdict(list)
    for destination in sorted(DESTINATION_LAYERS):
        owner = next(
            route.historical_module
            for route in routes.values()
            if route.destination == destination
        )
        by_owner[owner].append(roots[destination][0])
    for owner in sorted(by_owner):
        label = owner.rsplit(".", 1)[-1]
        module = f"NumStabilityTest.Worker.Ch09.Compatibility.{label}"
        payload = f"import {owner}\n\n" + "".join(
            f"#check {name}\n" for name in by_owner[owner]
        )
        result[ROOT / module_path(module)] = payload.encode()
        modules.append(module)

    aggregate = "NumStabilityTest.Worker.Ch09.Layers1To5"
    result[ROOT / module_path(aggregate)] = "".join(
        f"import {module}\n" for module in sorted(modules)
    ).encode()
    return result


def expected_materialization(
    baseline_path: Path,
) -> tuple[dict[Path, bytes], dict[str, Declaration]]:
    routes = full_routes()
    baseline, _ = read_graph(baseline_path)
    sources = frozen_sources()
    imports = read_import_contract()
    by_destination = destination_routes(routes)
    result = {
        ROOT / module_path(destination): destination_payload(
            destination, by_destination[destination], sources, imports
        )
        for destination in DESTINATION_LAYERS
    }
    result[ROOT / owner_path(HISTORICAL_GIANT)] = residual_giant_payload(routes, sources)
    result[ROOT / owner_path(HISTORICAL_PRIMITIVE)] = (
        "import NumStability.Source.Higham.Chapter09.Theorem914Primitive\n\n"
        "/-!\n"
        "# Historical Higham Chapter 9 Theorem 9.14 primitive import\n\n"
        "Compatibility wrapper for the canonical source-correspondence module.\n"
        "-/\n"
    ).encode()
    result[ROOT / owner_path(HISTORICAL_CORRECTION)] = (
        "import NumStability.Source.Higham.Chapter09.ComputedCorrection\n\n"
        "/-!\n"
        "# Historical Higham Chapter 9 computed-correction import\n\n"
        "Compatibility wrapper for the canonical source-correspondence module.\n"
        "-/\n"
    ).encode()
    result.update(test_payloads(routes, baseline))
    return result, baseline


def materialize(baseline_path: Path) -> None:
    for owner in HISTORICAL_OWNERS:
        path = ROOT / owner_path(owner)
        expected_blob = git_blob(BASE_REVISION, owner_path(owner))
        actual_blob = str(git("hash-object", path.as_posix())).strip()
        if actual_blob != expected_blob:
            fail(f"{owner}: production owner is not the exact integration-base blob")
    outputs, _ = expected_materialization(baseline_path)
    for path, payload in outputs.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(payload)


def validate_materialized_text(baseline_path: Path) -> dict[str, int]:
    expected, _ = expected_materialization(baseline_path)
    for path, payload in expected.items():
        if not path.is_file() or path.read_bytes() != payload:
            fail(f"materialized source/test differs from deterministic output: {path}")
    routes = full_routes()
    destinations = {
        destination: (ROOT / module_path(destination)).read_bytes()
        for destination in DESTINATION_LAYERS
    }
    for destination, payload in destinations.items():
        imports = parse_imports(payload)
        if any(imported in HISTORICAL_OWNERS for imported in imports):
            fail(f"{destination}: canonical source imports a historical Chapter 9 owner")
    return {
        "materialized_files": len(expected),
        "canonical_destinations": len(destinations),
        "command_groups": len(route_groups(routes)),
    }


def read_private_map() -> dict[str, str]:
    result = {row[0]: row[2] for row in read_format(PRIVATE_REWRITES, 1, 3)}
    if len(result) != EXPECTED_PRIVATE:
        fail("private-rewrite manifest count drifted")
    return result


def validate_candidate_command_hashes(routes: dict[str, Route]) -> int:
    private = read_private_map()
    sources: dict[str, bytes] = {}
    source_indices: dict[str, SourceCommandIndex] = {}
    entries: dict[str, dict[str, tuple[int, ...]]] = {}
    by_destination = destination_routes(routes)
    for destination in DESTINATION_LAYERS:
        path = ROOT / module_path(destination)
        source = path.read_bytes()
        sources[destination] = source
        source_indices[destination] = SourceCommandIndex(source)
        ilean = ROOT / ".lake/build/lib/lean" / module_path(destination, ".ilean")
        if not ilean.is_file():
            fail(f"missing compiled .ilean for {destination}")
        names = []
        for members in route_groups(routes).values():
            root = command_root(members)
            if root.destination != destination:
                continue
            names.append(private.get(root.name, root.name))
        entries[destination] = augment_entries_from_source(
            source,
            destination,
            names,
            read_ilean_entries(ilean, destination),
        )
    checked = 0
    for destination, roots in by_destination.items():
        for root in roots:
            actual_root = private.get(root.name, root.name)
            span = entries[destination].get(actual_root)
            if span is None:
                fail(f"{root.name}: candidate command root missing from .ilean")
            payload = source_indices[destination].command(span)
            if sha256_bytes(payload) != root.command_sha256:
                fail(f"{root.name}: candidate command bytes differ from frozen route")
            checked += 1
    return checked


def stage_check(baseline_path: Path, candidate_path: Path) -> dict[str, object]:
    acceptance = validate_contract(baseline_path)
    text = validate_materialized_text(baseline_path)
    routes = full_routes()
    baseline_declarations, baseline_edges = read_graph(baseline_path)
    candidate_declarations, candidate_edges = read_graph(candidate_path)
    private = read_private_map()

    baseline_actual = {name: name for name in routes}
    candidate_actual: dict[str, str] = {}
    for logical, route in routes.items():
        expected = baseline_declarations[logical]
        actual_name = private.get(logical, logical)
        actual = candidate_declarations.get(actual_name)
        if actual is None:
            fail(f"candidate graph lacks migrated declaration: {actual_name}")
        if (actual.module, actual.kind, actual.visibility) != (
            route.destination,
            expected.kind,
            expected.visibility,
        ):
            fail(f"{logical}: candidate ownership/kind/visibility drift")
        candidate_actual[actual_name] = logical
    expected_actual = set(candidate_actual)
    destination_actual = {
        declaration.name
        for declaration in candidate_declarations.values()
        if declaration.module in DESTINATION_LAYERS
    }
    if destination_actual != expected_actual:
        fail(
            "canonical destinations contain uncontracted declarations: "
            f"missing={sorted(expected_actual-destination_actual)[:20]}, "
            f"extra={sorted(destination_actual-expected_actual)[:20]}"
        )

    frozen_graph = normalized_incident_graph(baseline_edges, baseline_actual)
    candidate_graph = normalized_incident_graph(candidate_edges, candidate_actual)
    if frozen_graph != candidate_graph:
        missing = list((frozen_graph - candidate_graph).items())[:20]
        extra = list((candidate_graph - frozen_graph).items())[:20]
        fail(f"normalized incident typed graph drift: missing={missing}; extra={extra}")
    signature = sum(
        count for (kind, _, _), count in frozen_graph.items() if kind == "signature"
    )
    body = sum(
        count for (kind, _, _), count in frozen_graph.items() if kind == "body"
    )
    if signature != acceptance["baseline_incident_signature_edges"]:
        fail("acceptance signature-edge count drift")
    if body != acceptance["baseline_incident_body_edges"]:
        fail("acceptance body-edge count drift")
    if graph_sha256(frozen_graph) != acceptance["baseline_normalized_incident_sha256"]:
        fail("acceptance normalized-incident graph hash drift")
    hashes = validate_candidate_command_hashes(routes)
    return {
        "status": "PASS",
        "mode": "stage",
        "destinations": len(DESTINATION_LAYERS),
        "routed_declarations": len(routes),
        "command_groups": hashes,
        "private_rewrites": len(private),
        "incident_signature_edges": signature,
        "incident_body_edges": body,
        **text,
    }


def self_test() -> None:
    synthetic = b"theorem a : True := by\n  trivial\n\ntheorem b : True := by\n  trivial\n"
    first = SourceCommandIndex(synthetic).command((0, 0, 1, 9, 0, 8, 0, 9))
    assert first == b"theorem a : True := by\n  trivial"
    graph = normalized_incident_graph(
        [Edge("body", "old", "external")], {"old": "logical"}
    )
    assert graph == collections.Counter({("body", "@CH09:logical", "external"): 1})
    with tempfile.TemporaryDirectory() as raw:
        path = Path(raw) / "graph.tsv"
        path.write_text(
            "format\t2\ndeclaration\ta\tM\ttheorem\tpublic\n",
            encoding="utf-8",
            newline="\n",
        )
        declarations, edges = read_graph(path)
        assert set(declarations) == {"a"} and not edges
    levels = derived_layers()
    assert {name: levels[name] for name in DESTINATION_LAYERS} == DESTINATION_LAYERS
    assert len(full_routes()) == EXPECTED_DECLARATIONS
    assert len(route_groups(full_routes())) == EXPECTED_COMMAND_GROUPS
    assert len(private_rows(full_routes())) == EXPECTED_PRIVATE
    print("Chapter 9 layers 1--5 checker self-test: PASS")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("pre", "stage"), default="pre")
    parser.add_argument("--baseline-format2", type=Path)
    parser.add_argument("--candidate-format2", type=Path)
    parser.add_argument("--write-contract", action="store_true")
    parser.add_argument("--materialize", action="store_true")
    parser.add_argument("--check-materialized", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.self_test:
        self_test()
        return 0
    if args.baseline_format2 is None:
        fail("--baseline-format2 is required")
    baseline = args.baseline_format2.resolve()
    if args.write_contract:
        if args.mode != "pre":
            fail("--write-contract is valid only in pre mode")
        write_contract(baseline)
    acceptance = validate_contract(baseline)
    if args.materialize:
        if args.mode != "pre":
            fail("--materialize is valid only in pre mode")
        materialize(baseline)
        result = validate_materialized_text(baseline)
        print(json.dumps({"status": "PASS", "mode": "materialize", **result}, indent=2))
        return 0
    if args.mode == "stage":
        if args.candidate_format2 is None:
            fail("stage mode requires --candidate-format2")
        print(json.dumps(stage_check(baseline, args.candidate_format2.resolve()), indent=2))
        return 0
    result: dict[str, object] = {
        "status": "PASS",
        "mode": "pre",
        "destinations": acceptance["destinations"],
        "historical_owners": acceptance["historical_owners"],
        "routed_declarations": acceptance["routed_declarations"],
        "command_groups": acceptance["command_groups"],
        "private_rewrites": acceptance["private_rewrites"],
        "incident_signature_edges": acceptance["baseline_incident_signature_edges"],
        "incident_body_edges": acceptance["baseline_incident_body_edges"],
    }
    if args.check_materialized:
        result.update(validate_materialized_text(baseline))
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        sys.exit(1)
