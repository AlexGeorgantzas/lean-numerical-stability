#!/usr/bin/env python3
"""Freeze, materialize, and verify the final Chapter 9 closure tail.

The tail is integrated in dependency order:

* D1: four Problems-dependent closure destinations;
* D2: Theorem914Actual;
* E: the two final closures after their D1/D2 parents.

The checker derives every row from the immutable full Chapter 9 proposal and
packet graph, preserves compiler-command bytes and private visibility, and
proves the final 4,420-declaration reconciliation without requiring a Lean
build in pre/materialization mode.
"""

from __future__ import annotations

import argparse
import collections
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools/architecture"))

import check_ch09_layers1_5 as prior  # noqa: E402
import check_ch09_wave_abc as abc  # noqa: E402


# The Windows handoff pinned a historical pre-closure commit that is not
# present in the Linux clone.  Use the packet's frozen owner blobs for the
# deterministic recovery check; the live candidate remains the stage input.
BASE_REVISION = prior.PACKET_REVISION
PACKET_REVISION = prior.PACKET_REVISION
REVIEW_EVIDENCE_REVISION = prior.EVIDENCE_REVISION
FULL_CONTRACT = prior.FULL_CONTRACT
OWNERSHIP_ROOT = ROOT / "docs/architecture/declaration-ownership"
PREFIX = "ch09-closure-tail"
ACCEPTANCE = OWNERSHIP_ROOT / f"{PREFIX}-acceptance.json"
DESTINATIONS = OWNERSHIP_ROOT / f"{PREFIX}-destinations.tsv"
FROZEN_OWNERS = OWNERSHIP_ROOT / f"{PREFIX}-frozen-owners.tsv"
IMPORTS = OWNERSHIP_ROOT / f"{PREFIX}-imports.tsv"
OWNERSHIP = OWNERSHIP_ROOT / f"{PREFIX}-ownership.tsv"
PRIVATE_REWRITES = OWNERSHIP_ROOT / f"{PREFIX}-private-rewrites.tsv"
ROUTES = OWNERSHIP_ROOT / f"{PREFIX}-routes.tsv"

WAVE_DESTINATIONS: dict[str, dict[str, int]] = {
    "D1": {
        "NumStability.Source.Higham.Chapter09.CompletePivotSharpClosure": 10,
        "NumStability.Source.Higham.Chapter09.ComplexClosure": 10,
        "NumStability.Source.Higham.Chapter09.Theorem97Classification": 10,
        "NumStability.Source.Higham.Chapter09.Theorem99Closure": 10,
    },
    "D2": {
        "NumStability.Source.Higham.Chapter09.Theorem914Actual": 10,
    },
    "E": {
        "NumStability.Source.Higham.Chapter09.Theorem914DiagDominant": 11,
        "NumStability.Source.Higham.Chapter09.Theorem99ComplexClosure": 11,
    },
}
WAVE_ORDER = tuple(WAVE_DESTINATIONS)
DESTINATION_WAVE = {
    destination: wave
    for wave, destinations in WAVE_DESTINATIONS.items()
    for destination in destinations
}
DESTINATION_LAYERS = {
    destination: layer
    for destinations in WAVE_DESTINATIONS.values()
    for destination, layer in destinations.items()
}
# These two reviewed helper namespaces were restored after the original tail
# materializer was frozen, to keep their short internal names out of the
# public `NumStability` namespace.  The route contract already records the
# qualified declaration names; reproduce the source namespace in generated
# canonical text as well.
DIRECT_HELPER_NAMESPACES = {
    "NumStability.Source.Higham.Chapter09.Theorem99Closure":
        "Higham9Theorem99Direct",
    "NumStability.Source.Higham.Chapter09.Theorem99ComplexClosure":
        "Higham9Theorem99ComplexDirect",
}

HISTORICAL_OWNERS = {
    "NumStability.Algorithms.HighamChapter9CompletePivotSharpClosure",
    "NumStability.Algorithms.HighamChapter9ComplexClosure",
    "NumStability.Algorithms.HighamChapter9Theorem914Actual",
    "NumStability.Algorithms.HighamChapter9Theorem914DiagDominant",
    "NumStability.Algorithms.HighamChapter9Theorem97Classification",
    "NumStability.Algorithms.HighamChapter9Theorem99Closure",
    "NumStability.Algorithms.HighamChapter9Theorem99ComplexClosure",
}

EXPECTED_WAVES = {
    "D1": {
        "destinations": 4,
        "declarations": 189,
        "command_groups": 141,
        "private_rewrites": 0,
        "incident_signature_edges": 691,
        "incident_body_edges": 1088,
        "internal_typed_edges": 943,
        "normalized_incident_sha256": (
            "18D4D860976054EC0BF654937DE0EC779AF684D1E2D4C6BF783710F4C793354D"
        ),
        "command_payload_bytes": 154613,
        "command_payload_lines": 3327,
    },
    "D2": {
        "destinations": 1,
        "declarations": 127,
        "command_groups": 127,
        "private_rewrites": 11,
        "incident_signature_edges": 533,
        "incident_body_edges": 1030,
        "internal_typed_edges": 469,
        "normalized_incident_sha256": (
            "7F2E149BA7E9C07423D766F62A9DEDB5F0D97E364382B110C628D452648D3001"
        ),
        "command_payload_bytes": 143456,
        "command_payload_lines": 3253,
    },
    "E": {
        "destinations": 2,
        "declarations": 42,
        "command_groups": 42,
        "private_rewrites": 1,
        "incident_signature_edges": 102,
        "incident_body_edges": 236,
        "internal_typed_edges": 119,
        "normalized_incident_sha256": (
            "596AA5E23202542BBA17E31263FED8DF97632CECF355209B32699346AA568D4E"
        ),
        "command_payload_bytes": 58124,
        "command_payload_lines": 1300,
    },
}
EXPECTED_TOTALS = {
    "destinations": 7,
    "historical_owners": 7,
    "declarations": 358,
    "command_groups": 310,
    "private_rewrites": 12,
    "import_rows": 135,
}
EXPECTED_COMPLETE = {
    "canonical_destinations": 20,
    "declarations": 4420,
    "command_groups": 4108,
    "private_declarations": 28,
    "declaration_free_historical_owners": 11,
}

ALL_HISTORICAL_CH09 = abc.ALL_HISTORICAL_CH09
IMPORT_LINE_RE = re.compile(
    r"(?m)^\s*(?:(?:public|private)\s+)?import\s+[A-Za-z0-9_'.]+\s*$"
)
BLOCK_COMMENT_RE = re.compile(r"/-.*?-/", re.DOTALL)
LINE_COMMENT_RE = re.compile(r"(?m)--.*$")

ALLOWED_PATH_PATTERNS = (
    re.compile(
        r"^NumStability/Algorithms/HighamChapter9(?:CompletePivotSharpClosure|"
        r"ComplexClosure|Theorem914Actual|Theorem914DiagDominant|"
        r"Theorem97Classification|Theorem99Closure|Theorem99ComplexClosure)\.lean$"
    ),
    re.compile(
        r"^NumStability/Source/Higham/Chapter09/(?:CompletePivotSharpClosure|"
        r"ComplexClosure|Theorem914Actual|Theorem914DiagDominant|"
        r"Theorem97Classification|Theorem99Closure|Theorem99ComplexClosure)\.lean$"
    ),
    re.compile(r"^NumStabilityTest/Worker/Ch09/"),
    re.compile(r"^docs/architecture/declaration-ownership/ch09-closure-tail-"),
    re.compile(r"^docs/architecture/migrations/worker-ch09-closure-tail"),
    re.compile(r"^tools/architecture/check_ch09_closure_tail\.py$"),
)


def fail(message: str) -> None:
    raise ValueError(message)


def all_contract_routes() -> dict[str, prior.Route]:
    return {
        route.name: route
        for route in (
            prior.Route.parse(row)
            for row in prior.read_format(FULL_CONTRACT / "routes.tsv", 2, 17)
        )
    }


def full_routes() -> dict[str, prior.Route]:
    routes = {
        name: route
        for name, route in all_contract_routes().items()
        if route.destination in DESTINATION_LAYERS
    }
    if len(routes) != EXPECTED_TOTALS["declarations"]:
        fail("closure-tail declaration total drifted")
    if {route.historical_module for route in routes.values()} != HISTORICAL_OWNERS:
        fail("closure-tail historical owner set drifted")
    if {route.destination for route in routes.values()} != set(DESTINATION_LAYERS):
        fail("closure-tail destination set drifted")
    return routes


def route_groups(
    routes: Iterable[prior.Route],
) -> dict[tuple[str, tuple[int, ...]], list[prior.Route]]:
    groups: dict[tuple[str, tuple[int, ...]], list[prior.Route]] = (
        collections.defaultdict(list)
    )
    for route in routes:
        groups[(route.historical_module, route.span)].append(route)
    for members in groups.values():
        if len({member.destination for member in members}) != 1:
            fail(f"compiler command split across destinations: {members[0].command_root}")
        authored = [member for member in members if member.provenance == "authored"]
        if len(authored) != 1 or authored[0].name != authored[0].command_root:
            fail(f"command group lacks one authored root: {members[0].command_root}")
    return groups


def command_root(members: list[prior.Route]) -> prior.Route:
    return next(member for member in members if member.provenance == "authored")


def routes_for_wave(wave: str) -> dict[str, prior.Route]:
    destinations = set(WAVE_DESTINATIONS[wave])
    return {
        name: route
        for name, route in full_routes().items()
        if route.destination in destinations
    }


def routes_through(wave: str) -> dict[str, prior.Route]:
    stop = WAVE_ORDER.index(wave)
    destinations = {
        destination
        for item in WAVE_ORDER[: stop + 1]
        for destination in WAVE_DESTINATIONS[item]
    }
    return {
        name: route
        for name, route in full_routes().items()
        if route.destination in destinations
    }


def wave_dependencies() -> dict[str, set[str]]:
    _, edges = prior.full_dag()
    result: dict[str, set[str]] = collections.defaultdict(set)
    for source, target in edges:
        if source in DESTINATION_LAYERS:
            result[source].add(target)
    return result


def frozen_sources() -> dict[str, bytes]:
    return {
        owner: prior.git_show(PACKET_REVISION, prior.owner_path(owner))
        for owner in HISTORICAL_OWNERS
    }


def destination_routes(routes: Iterable[prior.Route]) -> dict[str, list[prior.Route]]:
    result: dict[str, list[prior.Route]] = collections.defaultdict(list)
    for members in route_groups(routes).values():
        root = command_root(members)
        result[root.destination].append(root)
    for destination in result:
        result[destination].sort(
            key=lambda route: (route.historical_module, route.span, route.command_root)
        )
    return result


def expected_imports() -> dict[str, list[str]]:
    common = prior.parse_imports(
        prior.git_show(prior.BASE_REVISION, prior.owner_path(prior.HISTORICAL_GIANT))
    )
    if any(item.startswith("NumStability.Source.Higham.Chapter09.") for item in common):
        fail("frozen common imports unexpectedly include Chapter 9 destinations")
    if "NumStability.Algorithms.LU.BlockLU" in common:
        fail("frozen common imports reintroduced the retired BlockLU umbrella")

    dependencies = wave_dependencies()
    sources = frozen_sources()
    result = {}
    by_destination = destination_routes(full_routes().values())
    for destination, roots in by_destination.items():
        owner = roots[0].historical_module
        original_imports = set(prior.parse_imports(sources[owner]))
        imported = set(dependencies[destination])
        if prior.HISTORICAL_GIANT in original_imports:
            imported.update(common)
        result[destination] = sorted(imported, key=str.casefold)
    return result


def private_rows(routes: dict[str, prior.Route]) -> list[list[str]]:
    selected = {name for name in routes if name.startswith("_private.")}
    full = {
        row[0]: row
        for row in prior.read_format(FULL_CONTRACT / "private-rewrites.tsv", 1, 3)
    }
    if not selected <= set(full):
        fail("full private-rewrite artifact does not cover the closure tail")
    return [full[name] for name in sorted(selected)]


def source_metrics(routes: dict[str, prior.Route]) -> tuple[int, int]:
    sources = frozen_sources()
    payloads = [
        prior.command_bytes(command_root(members), sources)
        for members in route_groups(routes.values()).values()
    ]
    return sum(map(len, payloads)), sum(len(payload.splitlines()) for payload in payloads)


def graph_metrics(
    routes: dict[str, prior.Route], edges: list[prior.Edge]
) -> dict[str, object]:
    incident = prior.normalized_incident_graph(edges, {name: name for name in routes})
    selected = set(routes)
    payload_bytes, payload_lines = source_metrics(routes)
    return {
        "destinations": len({route.destination for route in routes.values()}),
        "declarations": len(routes),
        "command_groups": len(route_groups(routes.values())),
        "private_rewrites": len(private_rows(routes)),
        "incident_signature_edges": sum(
            count
            for (kind, _, _), count in incident.items()
            if kind == "signature"
        ),
        "incident_body_edges": sum(
            count for (kind, _, _), count in incident.items() if kind == "body"
        ),
        "internal_typed_edges": sum(
            1
            for edge in edges
            if edge.source in selected and edge.target in selected
        ),
        "normalized_incident_sha256": prior.graph_sha256(incident),
        "command_payload_bytes": payload_bytes,
        "command_payload_lines": payload_lines,
    }


def check_private_boundaries(
    routes: dict[str, prior.Route], edges: list[prior.Edge]
) -> None:
    destinations = {name: route.destination for name, route in routes.items()}
    private_names = {row[0] for row in private_rows(routes)}
    violations = []
    for edge in edges:
        if edge.target not in private_names or edge.source not in destinations:
            continue
        if destinations[edge.source] != destinations[edge.target]:
            violations.append((edge.kind, edge.source, edge.target))
    if violations:
        fail(f"cross-destination consumer of a private helper: {violations[:20]}")


def generated_artifacts(
    baseline_path: Path,
) -> tuple[dict[Path, bytes], dict[str, object]]:
    abc.validate_contract(baseline_path)
    routes = full_routes()
    groups = route_groups(routes.values())
    baseline, edges = prior.read_graph(baseline_path)
    check_private_boundaries(routes, edges)
    ownership_full = {
        row[0]: row
        for row in prior.read_format(FULL_CONTRACT / "ownership.tsv", 1, 5)
    }
    layers = prior.derived_layers()
    if {name: layers[name] for name in DESTINATION_LAYERS} != DESTINATION_LAYERS:
        fail("full Chapter 9 DAG no longer yields the frozen tail layers")

    for name, route in routes.items():
        declaration = baseline.get(name)
        if declaration is None:
            fail(f"baseline graph lacks {name}")
        if (declaration.module, declaration.kind, declaration.visibility) != (
            route.historical_module,
            ownership_full[name][3],
            ownership_full[name][4],
        ):
            fail(f"baseline ownership metadata drift for {name}")

    destination_rows = []
    for destination in sorted(DESTINATION_LAYERS, key=lambda item: (DESTINATION_LAYERS[item], item)):
        selected = [route for route in routes.values() if route.destination == destination]
        destination_rows.append(
            [
                "destination",
                destination,
                DESTINATION_WAVE[destination],
                DESTINATION_LAYERS[destination],
                len(selected),
                len(route_groups(selected)),
                sum(ownership_full[route.name][4] == "private" for route in selected),
                ",".join(sorted({route.historical_module for route in selected})),
            ]
        )

    sources = frozen_sources()
    owner_rows = []
    for owner in sorted(HISTORICAL_OWNERS):
        selected = [route for route in routes.values() if route.historical_module == owner]
        path = prior.owner_path(owner)
        payload = sources[owner]
        owner_rows.append(
            [
                "owner",
                owner,
                path.as_posix(),
                prior.git_blob(BASE_REVISION, path),
                prior.git_blob(PACKET_REVISION, path),
                prior.sha256_bytes(payload),
                len(payload.decode("utf-8").splitlines()),
                len(selected),
                len(route_groups(selected)),
                "complete_in_tail",
            ]
        )

    import_rows = []
    dependencies = wave_dependencies()
    for destination, imports in sorted(expected_imports().items()):
        for imported in imports:
            reason = (
                "destination_dependency"
                if imported in dependencies[destination]
                else "frozen_giant_direct_import"
            )
            import_rows.append(["import", destination, imported, reason])

    waves = {
        wave: graph_metrics(routes_for_wave(wave), edges) for wave in WAVE_ORDER
    }
    if waves != EXPECTED_WAVES:
        fail(f"independently derived tail metrics drifted: {waves}")

    artifacts = {
        DESTINATIONS: prior.tsv_bytes(destination_rows),
        FROZEN_OWNERS: prior.tsv_bytes(owner_rows),
        IMPORTS: prior.tsv_bytes(import_rows),
        OWNERSHIP: prior.tsv_bytes(
            ownership_full[name] for name in sorted(routes)
        ),
        PRIVATE_REWRITES: prior.tsv_bytes(private_rows(routes)),
        ROUTES: prior.tsv_bytes(
            (route.fields() for route in sorted(routes.values(), key=lambda item: item.name)),
            version=2,
        ),
    }
    totals = {
        "destinations": len(DESTINATION_LAYERS),
        "historical_owners": len(HISTORICAL_OWNERS),
        "declarations": len(routes),
        "command_groups": len(groups),
        "private_rewrites": len(private_rows(routes)),
        "import_rows": len(import_rows),
    }
    if totals != EXPECTED_TOTALS:
        fail(f"closure-tail totals drifted: {totals}")

    acceptance = {
        "schema_version": 1,
        "chapter": "09",
        "sequence": "closure_tail_D1_D2_E",
        "base_revision": BASE_REVISION,
        "packet_revision": PACKET_REVISION,
        "review_evidence_revision": REVIEW_EVIDENCE_REVISION,
        "baseline_format2_sha256": prior.sha256_file(baseline_path),
        **totals,
        "waves": waves,
        "expected_complete_chapter": EXPECTED_COMPLETE,
        "full_contract_artifacts_sha256": {
            name: prior.sha256_file(FULL_CONTRACT / name)
            for name in (
                "acceptance.json",
                "candidate-modules.tsv",
                "owner-dag.tsv",
                "ownership.tsv",
                "private-rewrites.tsv",
                "routes.tsv",
            )
        },
        "abc_acceptance_sha256": prior.sha256_file(abc.ACCEPTANCE),
        "artifact_sha256": {
            path.name: prior.sha256_bytes(payload)
            for path, payload in sorted(artifacts.items(), key=lambda item: item[0].name)
        },
    }
    artifacts[ACCEPTANCE] = prior.stable_json(acceptance)
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
            fail(f"tracked closure-tail contract differs from deterministic output: {path}")
    return acceptance


def read_import_contract() -> dict[str, list[str]]:
    result: dict[str, list[str]] = collections.defaultdict(list)
    for row in prior.read_format(IMPORTS, 1, 4):
        if row[0] != "import" or row[1] not in DESTINATION_LAYERS:
            fail("malformed closure-tail import row")
        result[row[1]].append(row[2])
    if set(result) != set(DESTINATION_LAYERS):
        fail("closure-tail import artifact does not cover every destination")
    return result


def destination_payload(
    destination: str,
    routes: list[prior.Route],
    sources: dict[str, bytes],
    imports: dict[str, list[str]],
) -> bytes:
    title = destination.rsplit(".", 1)[-1]
    header = "".join(f"import {item}\n" for item in imports[destination])
    header += (
        "\n/-!\n"
        f"# Higham Chapter 9: {title}\n\n"
        "Canonical source-correspondence owner from Chapter 9 destination-DAG "
        f"layer {DESTINATION_LAYERS[destination]}.\n"
        "-/\n\n"
        "namespace NumStability\n\n"
        "open scoped BigOperators\n"
        "open ComplexConjugate\n"
        "open Matrix\n\n"
    )
    commands = []
    helper_namespace = DIRECT_HELPER_NAMESPACES.get(destination)
    helper_open = False
    for route in routes:
        payload = prior.command_bytes(route, sources)
        if prior.sha256_bytes(payload) != route.command_sha256:
            fail(f"{route.command_root}: frozen command hash drift")
        in_helper = bool(
            helper_namespace
            and f"NumStability.{helper_namespace}." in route.command_root
        )
        if in_helper and not helper_open:
            commands.append(f"namespace {helper_namespace}".encode())
            helper_open = True
        elif not in_helper and helper_open:
            commands.append(f"end {helper_namespace}".encode())
            helper_open = False
        commands.append(payload.rstrip(b"\n"))
    if helper_open:
        commands.append(f"end {helper_namespace}".encode())
    return header.encode("utf-8") + b"\n\n".join(commands) + b"\n\nend NumStability\n"


def wrapper_payload(owner: str, destination: str) -> bytes:
    label = owner.rsplit(".", 1)[-1]
    return (
        f"import {destination}\n\n"
        "/-!\n"
        f"# Historical {label} import\n\n"
        "Compatibility wrapper for the canonical Chapter 9 source module.\n"
        "-/\n"
    ).encode()


def public_roots(
    destinations: Iterable[str], baseline: dict[str, prior.Declaration]
) -> dict[str, list[str]]:
    wanted = set(destinations)
    roots: dict[str, list[str]] = collections.defaultdict(list)
    for members in route_groups(all_contract_routes().values()).values():
        root = command_root(members)
        if root.destination in wanted and baseline[root.name].visibility == "public":
            roots[root.destination].append(root.name)
    for destination in roots:
        roots[destination].sort()
    if set(roots) != wanted or any(not roots[item] for item in wanted):
        fail("a tail destination lacks a public smoke-test root")
    return roots


def canonical_test_path(destination: str) -> Path:
    label = destination.rsplit(".", 1)[-1]
    return ROOT / prior.module_path(f"NumStabilityTest.Worker.Ch09.Canonical.{label}")


def compatibility_test_path(owner: str) -> Path:
    label = owner.rsplit(".", 1)[-1]
    return ROOT / prior.module_path(f"NumStabilityTest.Worker.Ch09.Compatibility.{label}")


def test_payloads(
    through: str, baseline: dict[str, prior.Declaration]
) -> dict[Path, bytes]:
    stop = WAVE_ORDER.index(through)
    completed = WAVE_ORDER[: stop + 1]
    destinations = {
        destination
        for wave in completed
        for destination in WAVE_DESTINATIONS[wave]
    }
    roots = public_roots(destinations, baseline)
    by_destination = destination_routes(full_routes().values())
    result: dict[Path, bytes] = {}
    for destination in sorted(destinations):
        result[canonical_test_path(destination)] = (
            f"import {destination}\n\n#check {roots[destination][0]}\n"
        ).encode()
        owner = by_destination[destination][0].historical_module
        result[compatibility_test_path(owner)] = (
            f"import {owner}\n\n#check {roots[destination][0]}\n"
        ).encode()

    aggregate_modules = {
        wave: sorted(
            [
                f"NumStabilityTest.Worker.Ch09.Canonical.{destination.rsplit('.', 1)[-1]}"
                for destination in WAVE_DESTINATIONS[wave]
            ]
            + [
                "NumStabilityTest.Worker.Ch09.Compatibility."
                + by_destination[destination][0].historical_module.rsplit(".", 1)[-1]
                for destination in WAVE_DESTINATIONS[wave]
            ]
        )
        for wave in WAVE_ORDER
    }
    for wave in completed:
        aggregate = ROOT / prior.module_path(f"NumStabilityTest.Worker.Ch09.Wave{wave}")
        result[aggregate] = "".join(
            f"import {module}\n" for module in aggregate_modules[wave]
        ).encode()
    return result


def expected_materialization(
    through: str | None, baseline_path: Path
) -> tuple[dict[Path, bytes], dict[str, prior.Declaration]]:
    previous, baseline = abc.expected_materialization("C", baseline_path)
    if through is None:
        return previous, baseline

    stop = WAVE_ORDER.index(through)
    completed = WAVE_ORDER[: stop + 1]
    routes = {
        name: route
        for wave in completed
        for name, route in routes_for_wave(wave).items()
    }
    sources = frozen_sources()
    imports = read_import_contract()
    by_destination = destination_routes(routes.values())
    outputs = dict(previous)
    for destination in sorted(by_destination):
        outputs[ROOT / prior.module_path(destination)] = destination_payload(
            destination, by_destination[destination], sources, imports
        )
        owner = by_destination[destination][0].historical_module
        outputs[ROOT / prior.owner_path(owner)] = wrapper_payload(owner, destination)
    outputs.update(test_payloads(through, baseline))
    return outputs, baseline


def structural_only(payload: bytes) -> bool:
    text = payload.decode("utf-8-sig")
    text = BLOCK_COMMENT_RE.sub("", text)
    text = LINE_COMMENT_RE.sub("", text)
    text = IMPORT_LINE_RE.sub("", text)
    return not text.strip()


def complete_reconciliation(
    through: str, baseline_path: Path
) -> dict[str, int]:
    if through != "E":
        return {}
    all_routes = all_contract_routes()
    all_groups = route_groups(all_routes.values())
    all_private = {
        row[0]
        for row in prior.read_format(FULL_CONTRACT / "private-rewrites.tsv", 1, 3)
    }
    destinations = {route.destination for route in all_routes.values()}
    wrapper_count = 0
    for owner in ALL_HISTORICAL_CH09:
        path = ROOT / prior.owner_path(owner)
        if not path.is_file() or not structural_only(path.read_bytes()):
            fail(f"historical owner is not declaration-free structural text: {owner}")
        wrapper_count += 1
    result = {
        "canonical_destinations": len(destinations),
        "declarations": len(all_routes),
        "command_groups": len(all_groups),
        "private_declarations": len(all_private),
        "declaration_free_historical_owners": wrapper_count,
    }
    if result != EXPECTED_COMPLETE:
        fail(f"complete Chapter 9 reconciliation drifted: {result}")
    return result


def validate_materialized_text(
    through: str | None, baseline_path: Path
) -> dict[str, object]:
    expected, _ = expected_materialization(through, baseline_path)
    for path, payload in expected.items():
        if not path.is_file() or path.read_bytes() != payload:
            fail(f"materialized source/test differs from deterministic output: {path}")
    if through is None:
        return {"materialized_files": len(expected), "tail_destinations": 0}

    routes = routes_through(through)
    for destination in {route.destination for route in routes.values()}:
        payload = (ROOT / prior.module_path(destination)).read_bytes()
        forbidden = set(prior.parse_imports(payload)) & ALL_HISTORICAL_CH09
        if forbidden:
            fail(f"{destination}: canonical source imports historical owners {forbidden}")
    result: dict[str, object] = {
        "materialized_files": len(expected),
        "tail_destinations": len({route.destination for route in routes.values()}),
        "tail_declarations": len(routes),
        "tail_command_groups": len(route_groups(routes.values())),
    }
    complete = complete_reconciliation(through, baseline_path)
    if complete:
        result["complete_chapter"] = complete
    return result


def materialize(through: str, baseline_path: Path) -> None:
    index = WAVE_ORDER.index(through)
    precursor = None if index == 0 else WAVE_ORDER[index - 1]
    validate_materialized_text(precursor, baseline_path)
    outputs, _ = expected_materialization(through, baseline_path)
    for path, payload in outputs.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(payload)


def read_private_map() -> dict[str, str]:
    return {
        row[0]: row[2]
        for row in prior.read_format(PRIVATE_REWRITES, 1, 3)
    }


def validate_candidate_command_hashes(routes: dict[str, prior.Route]) -> int:
    private = read_private_map()
    indices: dict[str, prior.SourceCommandIndex] = {}
    entries: dict[str, dict[str, tuple[int, ...]]] = {}
    by_destination = destination_routes(routes.values())
    for destination, roots in by_destination.items():
        path = ROOT / prior.module_path(destination)
        source = path.read_bytes()
        indices[destination] = prior.SourceCommandIndex(source)
        ilean = ROOT / ".lake/build/lib/lean" / prior.module_path(destination, ".ilean")
        if not ilean.is_file():
            fail(f"missing compiled .ilean for {destination}")
        names = [private.get(root.name, root.name) for root in roots]
        entries[destination] = prior.augment_entries_from_source(
            source,
            destination,
            names,
            prior.read_ilean_entries(ilean, destination),
        )
    checked = 0
    for destination, roots in by_destination.items():
        for root in roots:
            actual = private.get(root.name, root.name)
            span = entries[destination].get(actual)
            if span is None:
                fail(f"{root.name}: candidate command root missing from .ilean")
            payload = indices[destination].command(span)
            if prior.sha256_bytes(payload) != root.command_sha256:
                fail(f"{root.name}: candidate command bytes differ from frozen route")
            checked += 1
    return checked


def stage_check(
    through: str, baseline_path: Path, candidate_path: Path
) -> dict[str, object]:
    acceptance = validate_contract(baseline_path)
    text = validate_materialized_text(through, baseline_path)
    baseline, baseline_edges = prior.read_graph(baseline_path)
    candidate, candidate_edges = prior.read_graph(candidate_path)
    private = read_private_map()
    cumulative = routes_through(through)

    candidate_actual: dict[str, str] = {}
    for logical, route in cumulative.items():
        expected = baseline[logical]
        actual_name = private.get(logical, logical)
        actual = candidate.get(actual_name)
        if actual is None:
            fail(f"candidate graph lacks migrated declaration: {actual_name}")
        if (actual.module, actual.kind, actual.visibility) != (
            route.destination,
            expected.kind,
            expected.visibility,
        ):
            fail(f"{logical}: candidate ownership/kind/visibility drift")
        candidate_actual[actual_name] = logical

    destination_actual = {
        declaration.name
        for declaration in candidate.values()
        if declaration.module in {route.destination for route in cumulative.values()}
    }
    if destination_actual != set(candidate_actual):
        fail("canonical tail destinations contain uncontracted declarations")

    checked = WAVE_ORDER[: WAVE_ORDER.index(through) + 1]
    for wave in checked:
        logical_routes = routes_for_wave(wave)
        frozen = prior.normalized_incident_graph(
            baseline_edges, {name: name for name in logical_routes}
        )
        actual = prior.normalized_incident_graph(
            candidate_edges,
            {private.get(name, name): name for name in logical_routes},
        )
        if frozen != actual:
            missing = list((frozen - actual).items())[:20]
            extra = list((actual - frozen).items())[:20]
            fail(f"wave {wave} normalized graph drift: missing={missing}; extra={extra}")
        if prior.graph_sha256(frozen) != acceptance["waves"][wave][
            "normalized_incident_sha256"
        ]:
            fail(f"wave {wave} normalized graph hash drift")

    hashes = validate_candidate_command_hashes(cumulative)
    return {
        "status": "PASS",
        "mode": "stage",
        "through": through,
        "waves": list(checked),
        "declarations": len(cumulative),
        "command_groups": hashes,
        **text,
    }


def changed_paths() -> set[str]:
    result = set(
        subprocess.check_output(
            ["git", "diff", "--name-only", f"{BASE_REVISION}..HEAD"],
            cwd=ROOT,
            text=True,
        ).splitlines()
    )
    result.update(
        subprocess.check_output(
            ["git", "diff", "--name-only"], cwd=ROOT, text=True
        ).splitlines()
    )
    for line in subprocess.check_output(
        ["git", "status", "--porcelain=v1", "--untracked-files=all"],
        cwd=ROOT,
        text=True,
    ).splitlines():
        if line.startswith("?? "):
            result.add(line[3:])
    return {path.replace("\\", "/") for path in result if path}


def validate_scope() -> dict[str, object]:
    paths = sorted(changed_paths())
    forbidden = [
        path
        for path in paths
        if not any(pattern.search(path) for pattern in ALLOWED_PATH_PATTERNS)
    ]
    if forbidden:
        fail(f"worker changed forbidden paths: {forbidden}")
    return {"scope": "PASS", "changed_paths": len(paths)}


def self_test() -> None:
    routes = full_routes()
    assert len(routes) == 358
    assert len(route_groups(routes.values())) == 310
    assert len(private_rows(routes)) == 12
    levels = prior.derived_layers()
    assert {name: levels[name] for name in DESTINATION_LAYERS} == DESTINATION_LAYERS
    imports = expected_imports()
    assert sum(map(len, imports.values())) == 135
    assert len(ALL_HISTORICAL_CH09) == 11
    print("Chapter 9 closure-tail checker self-test: PASS")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("pre", "stage"), default="pre")
    parser.add_argument("--through", choices=WAVE_ORDER)
    parser.add_argument("--baseline-format2", type=Path)
    parser.add_argument("--candidate-format2", type=Path)
    parser.add_argument("--write-contract", action="store_true")
    parser.add_argument("--materialize", action="store_true")
    parser.add_argument("--check-materialized", action="store_true")
    parser.add_argument("--check-scope", action="store_true")
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
        if args.mode != "pre" or args.materialize:
            fail("--write-contract is a standalone pre-mode operation")
        write_contract(baseline)
    acceptance = validate_contract(baseline)
    if args.materialize:
        if args.mode != "pre" or args.through is None:
            fail("--materialize requires pre mode and --through")
        materialize(args.through, baseline)
    if args.mode == "stage":
        if args.through is None or args.candidate_format2 is None:
            fail("stage mode requires --through and --candidate-format2")
        result = stage_check(args.through, baseline, args.candidate_format2.resolve())
    else:
        result: dict[str, object] = {
            "status": "PASS",
            "mode": "pre",
            "sequence": acceptance["sequence"],
            "destinations": acceptance["destinations"],
            "declarations": acceptance["declarations"],
            "command_groups": acceptance["command_groups"],
            "private_rewrites": acceptance["private_rewrites"],
            "waves": acceptance["waves"],
        }
        if args.check_materialized:
            result.update(validate_materialized_text(args.through, baseline))
    if args.check_scope:
        result.update(validate_scope())
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        sys.exit(1)
