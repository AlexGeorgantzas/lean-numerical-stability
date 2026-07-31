#!/usr/bin/env python3
"""Shared emit/validate driver for the Chapter 9 and Chapter 11 preparations.

The two chapter checkers are thin, reviewed configurations of this driver, so
both enforce exactly the same format-2 properties.  Preparation only: nothing
here writes a production Lean file, moves a declaration, rewrites a proof,
edits an import, or fabricates post-migration evidence.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from pathlib import Path

import chapter_contract as cc
import module_evidence as me


ARTIFACTS = (
    "routes.tsv",
    "ownership.tsv",
    "owner-dag.tsv",
    "direct-imports.tsv",
    "private-rewrites.tsv",
    "downstream-consumers.tsv",
)


@dataclass
class ChapterSpec:
    chapter: str                                  # "09"
    destination_prefix: str                       # NumStability.Source.Higham.Chapter09
    candidates: dict[str, str]                    # module -> repository-relative path
    sectioned_module: str                         # the giant owner routed by section seam
    section_seed: tuple[tuple[str, str], ...]     # (header regex, destination leaf)
    satellite_destinations: dict[str, str]        # module -> destination leaf
    exact_routes: tuple[tuple[str, str, str], ...] = ()   # (module, logical name, leaf)
    implementation_status: str = ""
    blocking_reason: str = ""
    cross_chapter_dependency_prefixes: tuple[str, ...] = ()
    required_gates: tuple[str, ...] = ()
    notes: tuple[str, ...] = ()

    def destination(self, leaf: str) -> str:
        return f"{self.destination_prefix}.{leaf}"


# ---------------------------------------------------------------------------
# route construction
# ---------------------------------------------------------------------------
def build_routes(root: Path, spec: ChapterSpec) -> tuple[cc.RouteTable, list[str]]:
    failures: list[str] = []
    table = cc.RouteTable()
    blocks = cc.section_blocks(root, spec.candidates[spec.sectioned_module])
    if not blocks:
        failures.append(f"{spec.sectioned_module}: no /-! ## section seams to route")
    matchers = [(re.compile(pattern), leaf) for pattern, leaf in spec.section_seed]

    # Preamble: lines before the first section seam stay with the historical
    # facade, which becomes an import-only compatibility wrapper.
    if blocks:
        first = blocks[0][0]
        if first > 1:
            table.ranges.append(
                cc.RangeRoute(spec.sectioned_module, 1, first - 1, spec.sectioned_module)
            )
    merged: list[cc.RangeRoute] = []
    for start, end, header in blocks:
        leaf = None
        for pattern, candidate in matchers:
            if pattern.search(header):
                leaf = candidate
                break
        if leaf is None:
            failures.append(f"{spec.sectioned_module}: unrouted section seam {header!r}")
            continue
        destination = spec.destination(leaf)
        if merged and merged[-1].destination == destination and merged[-1].last + 1 == start:
            merged[-1] = cc.RangeRoute(spec.sectioned_module, merged[-1].first, end, destination)
        else:
            merged.append(cc.RangeRoute(spec.sectioned_module, start, end, destination))
    table.ranges.extend(merged)

    for module, leaf in sorted(spec.satellite_destinations.items()):
        total = cc.line_count(root, spec.candidates[module])
        table.ranges.append(cc.RangeRoute(module, 1, total, spec.destination(leaf)))
    for module, logical, leaf in spec.exact_routes:
        table.exacts.append(cc.ExactRoute(module, logical, spec.destination(leaf)))

    # A destination must own one contiguous region of one historical module, so
    # that the destination dependency graph inherits Lean's forward-declaration
    # discipline and cannot become cyclic.
    seen: dict[str, cc.RangeRoute] = {}
    for route in table.ranges:
        if route.destination == spec.sectioned_module:
            continue
        previous = seen.get(route.destination)
        if previous is not None:
            failures.append(
                f"{route.destination}: owns two disjoint regions "
                f"({previous.historical} {previous.first}..{previous.last} and "
                f"{route.historical} {route.first}..{route.last})"
            )
        seen[route.destination] = route

    # A declaration-owning destination may not be a proper prefix of another
    # destination: that would make `<prefix>.lean` a declaration-bearing
    # umbrella beside a `<prefix>/` directory, which `check_layout.py` counts as
    # new legacy debt.
    owning = sorted(seen)
    for destination in owning:
        for other in owning:
            if other != destination and other.startswith(destination + "."):
                failures.append(
                    f"{destination}: owns declarations and is a prefix of {other}; "
                    "a declaration-bearing umbrella is forbidden"
                )
                break
    return table, failures


# ---------------------------------------------------------------------------
# contract construction
# ---------------------------------------------------------------------------
@dataclass
class Contract:
    routes: cc.RouteTable
    ownership: list[cc.OwnershipRow]
    signature_graph: dict[str, set[str]]
    body_graph: dict[str, set[str]]
    planned_imports: dict[str, list[str]]
    private_rewrites: list[tuple[str, str, str]]
    consumers: list[tuple[str, str, str]]
    stream: cc.StreamSlice
    failures: list[str] = field(default_factory=list)
    command_groups: dict[str, list[cc.CommandGroup]] = field(default_factory=dict)


def build_contract(root: Path, spec: ChapterSpec, baseline_zip: Path) -> Contract:
    routes, failures = build_routes(root, spec)
    line_counts = {
        module: cc.line_count(root, path) for module, path in spec.candidates.items()
    }
    failures.extend(cc.route_coverage_failures(routes, line_counts))

    groups = {
        module: cc.command_groups(root, path) for module, path in spec.candidates.items()
    }
    grouped_routes = routes.by_module()
    for module, module_groups in groups.items():
        for group in module_groups:
            covering = [
                route
                for route in grouped_routes.get(module, ())
                if route.first <= group.first and group.last <= route.last
            ]
            if len(covering) != 1:
                failures.append(
                    f"{module}: command group {group.first}..{group.last} "
                    f"({group.kind} {group.name or '-'}) is not inside exactly one route"
                )

    stream = cc.load_stream(baseline_zip, spec.candidates)
    ownership, ownership_failures = cc.resolve_ownership(root, routes, stream, spec.candidates)
    failures.extend(ownership_failures)

    external_module = cc.module_of_declaration(baseline_zip)
    destination = cc.destination_of_declaration(ownership, stream)
    signature_graph = cc.owner_graph(stream.signature_edges, destination, external_module)
    body_graph = cc.owner_graph(stream.body_edges, destination, external_module)

    planned: dict[str, list[str]] = {}
    for graph in (signature_graph, body_graph):
        for source, targets in graph.items():
            planned.setdefault(source, [])
            for target in targets:
                if target not in planned[source]:
                    planned[source].append(target)
    for source in planned:
        planned[source] = sorted(planned[source])
    for row in ownership:
        planned.setdefault(row.destination, [])

    rewrites: list[tuple[str, str, str]] = []
    for name, (module, _kind, visibility) in sorted(stream.declarations.items()):
        parts = cc.private_parts(name)
        if visibility != "private" or parts is None:
            continue
        logical = cc.logical_name(name)
        owner = next(
            (row.destination for row in ownership
             if row.historical == module and row.logical_name == logical),
            None,
        )
        if owner is None:
            failures.append(f"{module}: private declaration {name} has no owner")
            continue
        rewrites.append((logical, name, cc.candidate_private_name(owner, parts[1])))

    consumers = cc.consumer_rows(root, spec.candidates)
    return Contract(
        routes=routes,
        ownership=ownership,
        signature_graph=signature_graph,
        body_graph=body_graph,
        planned_imports=planned,
        private_rewrites=rewrites,
        consumers=consumers,
        stream=stream,
        failures=failures,
        command_groups=groups,
    )


def render_owner_dag(contract: Contract) -> str:
    lines = ["\t".join(cc.FORMAT_ONE)]
    for kind, graph in (("signature", contract.signature_graph), ("body", contract.body_graph)):
        for source in sorted(graph):
            for target in sorted(graph[source]):
                lines.append("\t".join(["edge", kind, source, target]))
    return "\n".join(lines) + "\n"


def acceptance(root: Path, spec: ChapterSpec, contract: Contract, directory: Path) -> dict:
    destinations = sorted({row.destination for row in contract.ownership})
    per_module = {}
    for module, path in sorted(spec.candidates.items()):
        module_groups = contract.command_groups[module]
        stream_rows = [
            name for name, (owner, _k, _v) in contract.stream.declarations.items()
            if owner == module
        ]
        per_module[module] = {
            "path": path,
            "lines": cc.line_count(root, path),
            "source_sha256": cc.sha256_file(root / path),
            "command_groups": len(module_groups),
            "authored_declaration_groups": sum(
                1 for group in module_groups if group.kind not in {"preamble", "section"}
            ),
            "section_seams": sum(1 for group in module_groups if group.kind == "section"),
            "baseline_declarations": len(stream_rows),
            "private_declarations": sum(
                1 for name in stream_rows
                if contract.stream.declarations[name][2] == "private"
            ),
        }
    signature_count, signature_digest = cc.normalized_edge_digest(
        contract.stream.signature_edges, "signature"
    )
    body_count, body_digest = cc.normalized_edge_digest(contract.stream.body_edges, "body")
    declaration_count, declaration_digest = cc.normalized_declaration_digest(contract.ownership)
    cross_chapter = sorted(
        [destination, target]
        for destination, targets in contract.planned_imports.items()
        for target in targets
        if spec.cross_chapter_dependency_prefixes
        and target.startswith(spec.cross_chapter_dependency_prefixes)
    )
    return {
        "schema_version": 1,
        "chapter": spec.chapter,
        "frozen_base_sha": "6487fc33088523b8f27ecde9ad613515b78f9977",
        "stream_format": 2,
        "implementation_status": spec.implementation_status,
        "blocking_reason": spec.blocking_reason,
        "preparation_only": True,
        "candidate_modules": len(spec.candidates),
        "destinations": destinations,
        "destination_count": len(destinations),
        "historical_facades": sorted(spec.candidates),
        "route_rows": {
            "range": len(contract.routes.ranges),
            "exact": len(contract.routes.exacts),
        },
        "counts": {
            "ownership_rows": len(contract.ownership),
            "baseline_declarations": len(contract.stream.declarations),
            "private_declarations": len(contract.private_rewrites),
            "signature_edges": signature_count,
            "body_edges": body_count,
            "external_signature_targets": contract.stream.external_signature_targets,
            "external_body_targets": contract.stream.external_body_targets,
            "downstream_consumer_rows": len(contract.consumers),
            "planned_import_rows": sum(len(v) for v in contract.planned_imports.values()),
        },
        "normalized_hashes": {
            "declarations": {"rows": declaration_count, "sha256": declaration_digest},
            "signature_edges": {"rows": signature_count, "sha256": signature_digest},
            "body_edges": {"rows": body_count, "sha256": body_digest},
        },
        "artifact_hashes": {
            name: cc.sha256_file(directory / name) for name in ARTIFACTS
            if (directory / name).is_file()
        },
        "per_module": per_module,
        "cross_chapter_dependencies": cross_chapter,
        "cross_chapter_dependency_count": len(cross_chapter),
        "required_gates": list(spec.required_gates),
        "notes": list(spec.notes),
    }


# ---------------------------------------------------------------------------
# emit / validate
# ---------------------------------------------------------------------------
def emit(root: Path, spec: ChapterSpec, directory: Path, baseline_zip: Path) -> list[str]:
    contract = build_contract(root, spec, baseline_zip)
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "routes.tsv").write_text(cc.render_routes(contract.routes), encoding="utf-8")
    (directory / "ownership.tsv").write_text(
        cc.render_ownership(contract.ownership), encoding="utf-8"
    )
    (directory / "owner-dag.tsv").write_text(render_owner_dag(contract), encoding="utf-8")
    (directory / "direct-imports.tsv").write_text(
        cc.render_direct_imports(contract.planned_imports), encoding="utf-8"
    )
    (directory / "private-rewrites.tsv").write_text(
        cc.render_private_rewrites(contract.private_rewrites), encoding="utf-8"
    )
    (directory / "downstream-consumers.tsv").write_text(
        cc.render_consumers(contract.consumers), encoding="utf-8"
    )
    (directory / "acceptance.json").write_text(
        json.dumps(acceptance(root, spec, contract, directory), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return contract.failures


def validate_pre(root: Path, spec: ChapterSpec, directory: Path, baseline_zip: Path) -> list[str]:
    """Pre-migration gate: the contract must be internally exact and acyclic."""

    contract = build_contract(root, spec, baseline_zip)
    failures = list(contract.failures)

    for name in (*ARTIFACTS, "acceptance.json"):
        if not (directory / name).is_file():
            failures.append(f"missing artifact {name}")
    if failures:
        return failures

    tracked_routes = cc.load_routes(directory / "routes.tsv")
    if cc.render_routes(tracked_routes) != cc.render_routes(contract.routes):
        failures.append("routes.tsv is not the deterministic route table")
    tracked_ownership = cc.load_ownership(directory / "ownership.tsv")
    if cc.render_ownership(tracked_ownership) != cc.render_ownership(contract.ownership):
        failures.append("ownership.tsv is not the deterministic ownership partition")
    if (directory / "owner-dag.tsv").read_text(encoding="utf-8") != render_owner_dag(contract):
        failures.append("owner-dag.tsv is not the deterministic destination graph")
    if (directory / "direct-imports.tsv").read_text(encoding="utf-8") != \
            cc.render_direct_imports(contract.planned_imports):
        failures.append("direct-imports.tsv is not the deterministic import plan")
    if (directory / "private-rewrites.tsv").read_text(encoding="utf-8") != \
            cc.render_private_rewrites(contract.private_rewrites):
        failures.append("private-rewrites.tsv is not the deterministic rewrite map")
    if (directory / "downstream-consumers.tsv").read_text(encoding="utf-8") != \
            cc.render_consumers(contract.consumers):
        failures.append("downstream-consumers.tsv is not the deterministic consumer set")

    # ownership completeness and uniqueness against the frozen baseline stream
    owned = [(row.historical, row.logical_name) for row in tracked_ownership]
    if len(set(owned)) != len(owned):
        failures.append("ownership.tsv has duplicate (historical, logical name) rows")
    expected = {
        (module, cc.logical_name(name))
        for name, (module, _kind, _visibility) in contract.stream.declarations.items()
    }
    missing = sorted(expected - set(owned))
    extra = sorted(set(owned) - expected)
    if missing:
        failures.append(
            f"{len(missing)} baseline declaration(s) unowned, e.g. {missing[:3]}"
        )
    if extra:
        failures.append(f"{len(extra)} ownership row(s) not in the baseline, e.g. {extra[:3]}")

    # visibility and kind preservation
    by_logical = {
        (module, cc.logical_name(name)): (kind, visibility)
        for name, (module, kind, visibility) in contract.stream.declarations.items()
    }
    for row in tracked_ownership:
        pair = by_logical.get((row.historical, row.logical_name))
        if pair is None:
            continue
        if (row.kind, row.visibility) != pair:
            failures.append(
                f"{row.logical_name}: ownership records {row.kind}/{row.visibility}, the "
                f"baseline has {pair[0]}/{pair[1]}"
            )

    # every private declaration must have exactly one reviewed rewrite
    private_logical = {
        cc.logical_name(name)
        for name, (_m, _k, visibility) in contract.stream.declarations.items()
        if visibility == "private"
    }
    rewrite_logical = [row[0] for row in contract.private_rewrites]
    if sorted(private_logical) != sorted(set(rewrite_logical)) or \
            len(rewrite_logical) != len(private_logical):
        failures.append(
            f"private-rewrites.tsv covers {len(rewrite_logical)} of "
            f"{len(private_logical)} private declarations"
        )
    for logical, historical, candidate in contract.private_rewrites:
        if not candidate.startswith(cc.PRIVATE_PREFIX) or ".0." not in candidate:
            failures.append(f"{logical}: malformed candidate private name {candidate}")
        if historical == candidate:
            failures.append(f"{logical}: private name did not change with the move")

    # destination DAG acyclicity, per edge kind and combined
    destinations = {row.destination for row in tracked_ownership}
    combined: dict[str, set[str]] = {}
    for graph in (contract.signature_graph, contract.body_graph):
        for source, targets in graph.items():
            combined.setdefault(source, set()).update(targets)
    for label, graph in (("signature", contract.signature_graph),
                         ("body", contract.body_graph),
                         ("combined", combined)):
        found = cc.cycles(graph, destinations)
        if found:
            failures.append(
                f"the {label} destination graph is cyclic: {found[0][:4]}"
            )

    # import allowlist: planned imports are exactly the referenced owners, and
    # no destination may import a historical facade it is extracted from
    for destination, targets in contract.planned_imports.items():
        referenced = set(contract.signature_graph.get(destination, set())) | \
            set(contract.body_graph.get(destination, set()))
        if set(targets) != referenced:
            failures.append(
                f"{destination}: planned imports {sorted(set(targets) ^ referenced)} "
                "differ from the referenced owners"
            )
        for target in targets:
            if target in spec.candidates:
                failures.append(
                    f"{destination}: may not import the historical facade {target}"
                )

    # the frozen acceptance record must be the deterministic derivation
    recorded = json.loads((directory / "acceptance.json").read_text(encoding="utf-8"))
    fresh = acceptance(root, spec, contract, directory)
    if recorded != fresh:
        differing = sorted(
            key for key in set(recorded) | set(fresh)
            if recorded.get(key) != fresh.get(key)
        )
        failures.append(f"acceptance.json is stale; differing keys: {differing}")
    if recorded.get("implementation_status") != spec.implementation_status:
        failures.append("acceptance.json does not record the blocked implementation status")
    if recorded.get("preparation_only") is not True:
        failures.append("acceptance.json must record preparation_only = true")
    if spec.cross_chapter_dependency_prefixes and not recorded.get("cross_chapter_dependencies"):
        failures.append(
            "acceptance.json records no cross-chapter dependency edges, but this chapter "
            f"declares dependencies on {spec.cross_chapter_dependency_prefixes}"
        )

    # preparation-only invariant: no destination file may exist yet
    for destination in sorted(destinations):
        candidate_path = root / (destination.replace(".", "/") + ".lean")
        if candidate_path.exists() and destination not in spec.candidates:
            failures.append(
                f"{destination}: a canonical destination file already exists; this lane "
                "must not create production modules"
            )
    return failures


# ---------------------------------------------------------------------------
# generic self-test over the contract primitives
# ---------------------------------------------------------------------------
def self_test() -> list[str]:
    problems: list[str] = []

    table = cc.RouteTable(ranges=[
        cc.RangeRoute("M", 1, 10, "D1"),
        cc.RangeRoute("M", 11, 20, "D2"),
    ])
    if cc.route_coverage_failures(table, {"M": 20}):
        problems.append("a complete route partition must be accepted")
    if not cc.route_coverage_failures(table, {"M": 25}):
        problems.append("routes that stop short of the file must be rejected")
    gapped = cc.RouteTable(ranges=[cc.RangeRoute("M", 1, 5, "D1"),
                                   cc.RangeRoute("M", 8, 20, "D2")])
    if not cc.route_coverage_failures(gapped, {"M": 20}):
        problems.append("a gap in the route partition must be rejected")
    overlapping = cc.RouteTable(ranges=[cc.RangeRoute("M", 1, 12, "D1"),
                                        cc.RangeRoute("M", 10, 20, "D2")])
    if not cc.route_coverage_failures(overlapping, {"M": 20}):
        problems.append("overlapping routes must be rejected")
    if not cc.route_coverage_failures(cc.RouteTable(), {"M": 20}):
        problems.append("a module with no route must be rejected")
    if not cc.route_coverage_failures(table, {"M": 20, "Other": 3}):
        problems.append("an unrouted candidate module must be rejected")
    if not cc.route_coverage_failures(cc.RouteTable(ranges=[cc.RangeRoute("Extra", 1, 2, "D")]),
                                     {}):
        problems.append("a route for a non-candidate module must be rejected")

    if cc.cycles({"a": {"b"}, "b": {"c"}}, ["a", "b", "c"]):
        problems.append("an acyclic destination graph must be accepted")
    if not cc.cycles({"a": {"b"}, "b": {"a"}}, ["a", "b"]):
        problems.append("a two-node cycle must be detected")
    if not cc.cycles({"a": {"b"}, "b": {"c"}, "c": {"a"}}, ["a", "b", "c"]):
        problems.append("a three-node cycle must be detected")

    mangled = "_private.NumStability.Algorithms.HighamChapter9.0.NumStability.helper"
    if cc.private_parts(mangled) != ("NumStability.Algorithms.HighamChapter9",
                                     "NumStability.helper"):
        problems.append("private-name splitting must recover the module and name")
    if cc.logical_name(mangled) != "_private.<module>.NumStability.helper":
        problems.append("private-name normalization must erase the owning module")
    if cc.logical_name("NumStability.public_thing") != "NumStability.public_thing":
        problems.append("public names must normalize to themselves")
    if cc.candidate_private_name("NumStability.Dest", "NumStability.helper") != \
            "_private.NumStability.Dest.0.NumStability.helper":
        problems.append("candidate private names must be rebuilt from the destination")

    left = cc.normalized_edge_digest([("a", "b"), ("a", "b")], "signature")
    right = cc.normalized_edge_digest([("a", "b")], "signature")
    if left != right:
        problems.append("edge digests must be duplicate-insensitive")
    if cc.normalized_edge_digest([("a", "b")], "signature") == \
            cc.normalized_edge_digest([("a", "b")], "body"):
        problems.append("signature and body digests must stay distinct")
    if cc.normalized_edge_digest([("a", "b")], "signature") == \
            cc.normalized_edge_digest([("b", "a")], "signature"):
        problems.append("edge digests must be direction-sensitive")

    rows = [cc.OwnershipRow("n", "H", "D", "theorem", "public")]
    if cc.normalized_declaration_digest(rows) == \
            cc.normalized_declaration_digest([cc.OwnershipRow("n", "H", "D2", "theorem",
                                                              "public")]):
        problems.append("declaration digests must depend on the destination")

    graph = cc.owner_graph([("s", "t")], {"s": "D1", "t": "D2"}, {})
    if graph != {"D1": {"D2"}}:
        problems.append("owner graph construction must map declarations to destinations")
    if cc.owner_graph([("s", "t")], {"s": "D1", "t": "D1"}, {}) != {}:
        problems.append("intra-destination edges must not appear in the owner graph")
    if cc.owner_graph([("s", "t")], {"s": "D1"}, {"t": "External.Module"}) != \
            {"D1": {"External.Module"}}:
        problems.append("external targets must resolve to their production module")
    return problems
