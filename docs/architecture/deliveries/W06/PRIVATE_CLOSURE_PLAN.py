#!/usr/bin/env python3
"""Compute W06's command-granular private-declaration retention plan.

This script reads the hash-pinned P0007 projection, exact C0005 owner blobs,
and C0005 ``.ilean`` command spans.  A complete Lean command is retained when
it declares a genuine private name or transitively depends on a retained
command.  The output is deterministic evidence and is also consumed by the
W06 migration generator.

Unlike the earlier W02/W05 front ends, this planner deliberately tolerates an
unselected physical command in an owner.  C0005 has one byte-identical legacy
copy of ``infNorm_add_le`` whose declaration is attributed to the accepted W02
canonical module.  The migration generator blanks that exact physical span
and imports the accepted canonical module; ``PRIVATE_CLOSURE.md`` records the
exception because it is intentionally not a P0007 row.  The planner also maps the five private declarations
created by ``local notation`` macro commands, whose `.ilean` roots are auxiliary
macro-rule names rather than the private declaration names.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import heapq
import importlib.util
import io
import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path


BASE = "240c0d041781385a647fbec461d6863537e562cb"
PROJECTION_SHA256 = "E1C2787CC0D0D8A08E016932CEBC1831FAD6929BF22FA757D12BFC49F8ADCF39"
SELECTOR_SHA256 = "5D482CF32C656C77AF3AABA674C3FE39AA5AEBD0FED6BC0C3E569DCDB328E484"
ENGINE_SHA256 = "E353E4BE155CE70D33E272414C4C41CC2E6B3A0C8A8C9618A96CD868558D0BFD"
EXPECTED_DECLARATIONS = 3_512
EXPECTED_SIGNATURE_EDGES = 15_044
EXPECTED_BODY_EDGES = 16_341
EXPECTED_UNION_EDGES = 22_079
EXPECTED_PRIVATE_DECLARATIONS = 94
EXPECTED_GRAPH_REVERSE_CLOSURE = 768
EXPECTED_COMMANDS = 3_450


class PlanError(RuntimeError):
    pass


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def load_engine(repo: Path):
    path = repo / "docs/architecture/deliveries/W02/PRIVATE_CLOSURE_PLAN.py"
    found = sha256_file(path)
    if found != ENGINE_SHA256:
        raise PlanError(
            f"private-closure engine hash differs: expected {ENGINE_SHA256}, found {found}"
        )
    spec = importlib.util.spec_from_file_location("w06_private_closure_engine", path)
    if spec is None or spec.loader is None:
        raise PlanError(f"cannot load private-closure engine at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    module.FROZEN_BASE = BASE
    module.P0002_SHA256 = PROJECTION_SHA256
    module.EXPECTED_DECLARATIONS = EXPECTED_DECLARATIONS
    module.EXPECTED_SIGNATURE_EDGES = EXPECTED_SIGNATURE_EDGES
    module.EXPECTED_BODY_EDGES = EXPECTED_BODY_EDGES
    module.EXPECTED_PHYSICAL_DECLARATIONS = EXPECTED_DECLARATIONS
    return module


def read_selector(path: Path) -> tuple[tuple[str, ...], dict[str, str]]:
    if sha256_file(path) != SELECTOR_SHA256:
        raise PlanError(f"selector hash differs: {path}")
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["module", "path"] or len(rows) != 68:
        raise PlanError("W06 selector must contain its exact header and 67 rows")
    owners = tuple(row[0] for row in rows[1:])
    paths = {row[0]: row[1] for row in rows[1:]}
    if len(paths) != 67 or owners != tuple(sorted(owners)):
        raise PlanError("W06 selector is duplicated or not sorted")
    return owners, paths


def command_text(command, sources: dict[str, str]) -> str:
    return sources[command.owner][command.start_offset:command.end_offset]


def map_declarations(engine, declarations, edges, commands, sources, owners):
    owner_set = set(owners)
    roots: dict[str, list[str]] = defaultdict(list)
    for owner, root in commands:
        roots[owner].append(root)
    for owner in roots:
        roots[owner].sort(key=lambda root: (-len(root), root))

    if {item.module for item in declarations.values()} != owner_set:
        unexpected = sorted({item.module for item in declarations.values()} - owner_set)
        missing = sorted(owner_set - {item.module for item in declarations.values()})
        raise PlanError(f"P0007 physical owners differ: unexpected={unexpected}, missing={missing}")

    mapped: dict[str, tuple[str, str]] = {}
    unmapped: list[str] = []
    for name, declaration in sorted(declarations.items()):
        candidates = [
            root for root in roots[declaration.module]
            if name == root or name.startswith(root + ".")
        ]
        if candidates:
            longest = len(candidates[0])
            winners = [root for root in candidates if len(root) == longest]
            if len(winners) != 1:
                raise PlanError(f"{name}: ambiguous command roots {winners}")
            mapped[name] = (declaration.module, winners[0])
        else:
            unmapped.append(name)

    still_unmapped: list[str] = []
    for name in unmapped:
        declaration = declarations[name]
        alias = engine.find_source_alias_command(
            declaration.module, name, sources[declaration.module]
        )
        if alias is None:
            still_unmapped.append(name)
            continue
        if alias.key in commands:
            raise PlanError(f"{name}: recovered alias collides with an .ilean command")
        commands[alias.key] = alias
        roots[declaration.module].append(alias.root)
        roots[declaration.module].sort(key=lambda root: (-len(root), root))
        mapped[name] = alias.key

    # Map private declarations generated by local-notation macro rules.  The
    # generated private leaf is `term<symbol>` and the command span contains the
    # corresponding notation symbol.  Require a unique, source-visible match.
    after_notation: list[str] = []
    for name in still_unmapped:
        declaration = declarations[name]
        leaf = name.rsplit(".", 1)[-1]
        # Lean encodes macro-generated syntax names between guillemet
        # sentinels in the environment (`«term…»`).  Some Windows consoles
        # display those code points as mojibake, so normalize the real UTF-8
        # characters here.
        macro_leaf = leaf.removeprefix("«").removesuffix("»")
        if declaration.visibility != "private" or not macro_leaf.startswith("term"):
            after_notation.append(name)
            continue
        symbol = macro_leaf.removeprefix("term")
        candidates = []
        for key, command in commands.items():
            if command.owner != declaration.module:
                continue
            payload = command_text(command, sources)
            if "notation" in payload and symbol in payload:
                candidates.append(key)
        if len(candidates) != 1:
            raise PlanError(f"{name}: expected one notation command, found {candidates}")
        mapped[name] = candidates[0]

    # Remaining omissions are deriving-generated declarations.  Reuse the
    # dependency-backed W02 rule but limit it to commands with `deriving`.
    outgoing: dict[str, set[str]] = defaultdict(set)
    for edge in edges:
        outgoing[edge.source].add(edge.target)
    unresolved: list[str] = []
    for name in after_notation:
        declaration = declarations[name]
        dependency_commands = {
            mapped[target]
            for target in outgoing.get(name, set())
            if target in mapped and mapped[target][0] == declaration.module
        }
        deriving_commands = {
            key for key in dependency_commands
            if re.search(r"\bderiving\b", command_text(commands[key], sources))
        }
        named = {key for key in deriving_commands if key[1].rsplit(".", 1)[-1] in name}
        candidates = named or deriving_commands
        if len(candidates) != 1:
            unresolved.append(name)
        else:
            mapped[name] = next(iter(candidates))
    if unresolved:
        raise PlanError("selected declarations without a validated command: " + ", ".join(unresolved))

    for name, key in mapped.items():
        commands[key].declarations.append(name)
    selected_commands = {key: command for key, command in commands.items() if command.declarations}
    for command in selected_commands.values():
        command.declarations.sort()
    if len(mapped) != EXPECTED_DECLARATIONS:
        raise PlanError(f"mapped {len(mapped)} declarations, expected {EXPECTED_DECLARATIONS}")
    return mapped, selected_commands


def compute_graph_floor(declarations, edges) -> set[str]:
    retained = {name for name, item in declarations.items() if item.visibility == "private"}
    reverse: dict[str, set[str]] = defaultdict(set)
    for edge in edges:
        if edge.source in declarations and edge.target in declarations:
            reverse[edge.target].add(edge.source)
    queue = list(sorted(retained))
    while queue:
        target = queue.pop()
        for source in sorted(reverse.get(target, ())):
            if source not in retained:
                retained.add(source)
                queue.append(source)
    if len(retained) != EXPECTED_GRAPH_REVERSE_CLOSURE:
        raise PlanError(
            f"graph reverse closure is {len(retained)}, expected {EXPECTED_GRAPH_REVERSE_CLOSURE}"
        )
    return retained


def compute_command_closure(declarations, edges, commands, declaration_commands):
    seeds = {
        key for key, command in commands.items()
        if any(declarations[name].visibility == "private" for name in command.declarations)
    }
    private_count = sum(item.visibility == "private" for item in declarations.values())
    if private_count != EXPECTED_PRIVATE_DECLARATIONS:
        raise PlanError(f"found {private_count} private declarations, expected 94")

    command_edges: dict[tuple[str, str], set[tuple[str, str]]] = defaultdict(set)
    witnesses = defaultdict(list)
    for edge in edges:
        source = declaration_commands.get(edge.source)
        target = declaration_commands.get(edge.target)
        if source is None or target is None or source == target:
            continue
        command_edges[source].add(target)
        witnesses[(source, target)].append((edge.kind, edge.source, edge.target))
    reverse: dict[tuple[str, str], set[tuple[str, str]]] = defaultdict(set)
    for source, targets in command_edges.items():
        for target in targets:
            reverse[target].add(source)

    depth = {seed: 0 for seed in seeds}
    queue = [(0, seed[0], seed[1]) for seed in seeds]
    heapq.heapify(queue)
    while queue:
        target_depth, owner, root = heapq.heappop(queue)
        target = (owner, root)
        if depth.get(target) != target_depth:
            continue
        for source in sorted(reverse.get(target, ())):
            candidate = target_depth + 1
            if candidate < depth.get(source, sys.maxsize):
                depth[source] = candidate
                heapq.heappush(queue, (candidate, source[0], source[1]))

    chosen_target = {}
    chosen_witness = {}
    for source, source_depth in sorted(depth.items()):
        if source_depth == 0:
            continue
        targets = sorted(
            target for target in command_edges.get(source, ())
            if depth.get(target) == source_depth - 1
        )
        if not targets:
            raise PlanError(f"{source}: retained command lacks a closure predecessor")
        target = targets[0]
        chosen_target[source] = target
        chosen_witness[(source, target)] = sorted(witnesses[(source, target)])[0]
    return depth, chosen_target, chosen_witness


def render_plan(base, declarations, commands, evidence, depth, chosen_target, chosen_witness, graph_floor):
    output = io.StringIO(newline="")
    writer = csv.writer(output, delimiter="\t", lineterminator="\n")
    retained_declarations = {
        name for key in depth for name in commands[key].declarations
    }
    writer.writerow(["format", "1"])
    metadata = (
        ("generated_by", "docs/architecture/deliveries/W06/PRIVATE_CLOSURE_PLAN.py"),
        ("base_revision", base),
        ("projection_id", "P0007"),
        ("projection_sha256", PROJECTION_SHA256),
        ("selector_sha256", SELECTOR_SHA256),
        ("owner_count", str(len(evidence))),
        ("selected_declaration_count", str(len(declarations))),
        ("command_count", str(len(commands))),
        ("private_declaration_count", str(EXPECTED_PRIVATE_DECLARATIONS)),
        ("private_seed_command_count", str(sum(value == 0 for value in depth.values()))),
        ("graph_reverse_closure_count", str(len(graph_floor))),
        ("retained_command_count", str(len(depth))),
        ("retained_declaration_count", str(len(retained_declarations))),
        ("move_candidate_command_count", str(len(commands) - len(depth))),
        ("move_candidate_declaration_count", str(len(declarations) - len(retained_declarations))),
        ("coordinate_convention", "lines=1-based; columns=UTF-16-code-units-0-based; end=half-open"),
    )
    for key, value in metadata:
        writer.writerow(["metadata", key, value])
    writer.writerow(["columns", "owner", "module", "source_path", "source_blob_sha1", "source_sha256", "ilean_path", "ilean_sha256", "command_count", "retained_command_count", "move_candidate_count", "private_declaration_count"])
    writer.writerow(["columns", "command", "owner_module", "command_root", "span_origin", "start_line", "start_column", "end_line", "end_column", "decision", "reason", "closure_depth", "witness_owner", "witness_root", "witness_edge_kind", "witness_source_declaration", "witness_target_declaration", "selected_declaration_count", "private_declaration_count", "selected_declarations_json"])

    for owner, item in evidence.items():
        owner_commands = [command for command in commands.values() if command.owner == owner]
        retained = sum(command.key in depth for command in owner_commands)
        private = sum(
            declarations[name].visibility == "private"
            for command in owner_commands for name in command.declarations
        )
        writer.writerow(["owner", owner, item.source_path, item.source_blob_sha1, item.source_sha256, item.ilean_path, item.ilean_sha256, str(len(owner_commands)), str(retained), str(len(owner_commands) - retained), str(private)])
    for owner in evidence:
        owner_commands = sorted(
            (command for command in commands.values() if command.owner == owner),
            key=lambda command: (command.start_line, command.start_column, command.end_line, command.end_column, command.root),
        )
        for command in owner_commands:
            key = command.key
            if key not in depth:
                decision, reason, closure_depth = "move_candidate", "closure_free", ""
                target_owner = target_root = witness_kind = witness_source = witness_target = ""
            elif depth[key] == 0:
                decision, reason, closure_depth = "retain_historical", "private_seed", "0"
                target_owner = target_root = witness_kind = witness_source = witness_target = ""
            else:
                decision, reason, closure_depth = "retain_historical", "depends_on_retained_command", str(depth[key])
                target_owner, target_root = chosen_target[key]
                witness_kind, witness_source, witness_target = chosen_witness[(key, chosen_target[key])]
            private = sum(declarations[name].visibility == "private" for name in command.declarations)
            writer.writerow(["command", owner, command.root, command.span_origin, str(command.start_line + 1), str(command.start_column), str(command.end_line + 1), str(command.end_column), decision, reason, closure_depth, target_owner, target_root, witness_kind, witness_source, witness_target, str(len(command.declarations)), str(private), json.dumps(command.declarations, ensure_ascii=False, separators=(",", ":"))])
    return output.getvalue()


def parse_arguments() -> argparse.Namespace:
    script = Path(__file__).resolve()
    repo = script.parents[4]
    parser = argparse.ArgumentParser(description="Compute the C0005/P0007 W06 command closure.")
    parser.add_argument("--repo-root", type=Path, default=repo)
    parser.add_argument("--control-root", type=Path, required=True)
    parser.add_argument("--ilean-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, default=script.with_name("PRIVATE_CLOSURE.tsv"))
    parser.add_argument("--check", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_arguments()
    repo = args.repo_root.resolve()
    control = args.control_root.resolve()
    delivery = repo / "docs/architecture/deliveries/W06"
    output = args.output.resolve()
    if output.parent != delivery.resolve():
        raise PlanError(f"output must remain inside {delivery}")
    phase = control / "docs/architecture/phases/2026-08-repository-reorganization"
    selector_path = phase / "selectors/W06.tsv"
    projection_path = phase / "projections/P0007.tsv.gz"
    owners, source_paths = read_selector(selector_path)

    engine = load_engine(repo)
    engine.PHYSICAL_OWNERS = owners
    resolved = str(engine.run_git(repo, "rev-parse", f"{BASE}^{{commit}}"))
    if resolved != BASE:
        raise PlanError(f"W06 base unavailable: {resolved}")
    declarations, edges = engine.read_projection(projection_path)
    edge_counts = Counter(edge.kind for edge in edges)
    union_count = len({(edge.source, edge.target) for edge in edges})
    if edge_counts != Counter(signature=EXPECTED_SIGNATURE_EDGES, body=EXPECTED_BODY_EDGES):
        raise PlanError(f"P0007 typed-edge counts differ: {dict(edge_counts)}")
    if union_count != EXPECTED_UNION_EDGES:
        raise PlanError(
            f"P0007 union-edge count is {union_count}, expected {EXPECTED_UNION_EDGES}"
        )
    sources = {}
    all_commands = {}
    evidence = {}
    for owner in owners:
        payload, source, blob = engine.read_base_source(repo, BASE, source_paths[owner])
        sources[owner] = source
        relative_ilean = engine.module_path(owner, ".ilean")
        ilean_path = args.ilean_root.resolve() / relative_ilean
        ilean, ilean_hash = engine.read_ilean(ilean_path, owner)
        owner_commands = engine.commands_from_ilean(owner, ilean, source)
        overlap = set(all_commands).intersection(owner_commands)
        if overlap:
            raise PlanError(f"duplicate command keys: {sorted(overlap)[:5]}")
        all_commands.update(owner_commands)
        evidence[owner] = engine.OwnerEvidence(
            module=owner,
            source_path=source_paths[owner],
            source_blob_sha1=blob,
            source_sha256=sha256_bytes(payload),
            ilean_path=(Path(".lake/build/lib/lean") / relative_ilean).as_posix(),
            ilean_sha256=ilean_hash,
        )

    declaration_commands, commands = map_declarations(
        engine, declarations, edges, all_commands, sources, owners
    )
    if len(commands) != EXPECTED_COMMANDS:
        raise PlanError(
            f"mapped {len(commands)} selected commands, expected {EXPECTED_COMMANDS}"
        )
    graph_floor = compute_graph_floor(declarations, edges)
    depth, chosen_target, chosen_witness = compute_command_closure(
        declarations, edges, commands, declaration_commands
    )
    rendered = render_plan(
        BASE, declarations, commands, evidence, depth, chosen_target, chosen_witness, graph_floor
    )
    if args.check:
        if not output.is_file() or output.read_text(encoding="utf-8") != rendered:
            raise PlanError(f"{output} is missing or stale")
        action = "verified"
    else:
        output.write_text(rendered, encoding="utf-8", newline="")
        action = "wrote"
    counts = Counter()
    for key, command in commands.items():
        counts["retained" if key in depth else "movable"] += len(command.declarations)
    print(
        f"{action} {output}: {len(commands)} selected commands; "
        f"{counts['retained']} declarations retained, {counts['movable']} movable; "
        f"{len(depth)} retained commands; sha256={sha256_bytes(rendered.encode('utf-8'))}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, PlanError, RuntimeError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
