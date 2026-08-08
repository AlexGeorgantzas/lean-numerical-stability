#!/usr/bin/env python3
"""Compute W04's command-granular private-declaration retention plan.

The implementation deliberately reuses the hash-pinned, accepted W06 front
end and W02 command-span engine.  It reads the immutable C0006 sources, the
P0009 typed graph, and freshly rebuilt C0006 ``.ilean`` files.  A whole Lean
command remains at its historical path exactly when it declares a private
name or lies in the reverse dependency closure of such a command.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import importlib.util
import sys
from collections import Counter
from pathlib import Path


BASE = "a32095e6e50189f7dcc39312bb4c6a36f421fab5"
PROJECTION_SHA256 = "EAA15F18127E7B77F8AF442760590687B66A8860485590F2EB13D57E3A6F3814"
SELECTOR_SHA256 = "92446B8EBF571733212239DBD471A377EA889FC2A7061F1500DE7B03DB96518F"
W06_FRONTEND_SHA256 = "A4F8758C85B1B076DE08CD3EFD2A41D3865A7EC857CA21C2C8F64F84E0538203"
EXPECTED_DECLARATIONS = 1_238
EXPECTED_SIGNATURE_EDGES = 5_684
EXPECTED_BODY_EDGES = 10_044
EXPECTED_UNION_EDGES = 10_624
EXPECTED_PRIVATE_DECLARATIONS = 40
EXPECTED_GRAPH_REVERSE_CLOSURE = 220
# Hash-pinned after the first extraction from the rebuilt C0006 ``.ilean`` files.
EXPECTED_COMMANDS = 1_073


class PlanError(RuntimeError):
    pass


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def load_frontend(repo: Path):
    path = repo / "docs/architecture/deliveries/W06/PRIVATE_CLOSURE_PLAN.py"
    found = sha256_file(path)
    if found != W06_FRONTEND_SHA256:
        raise PlanError(
            f"accepted W06 private-closure frontend hash differs: expected "
            f"{W06_FRONTEND_SHA256}, found {found}"
        )
    spec = importlib.util.spec_from_file_location("w04_private_closure_frontend", path)
    if spec is None or spec.loader is None:
        raise PlanError(f"cannot load accepted frontend at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    module.BASE = BASE
    module.PROJECTION_SHA256 = PROJECTION_SHA256
    module.SELECTOR_SHA256 = SELECTOR_SHA256
    module.EXPECTED_DECLARATIONS = EXPECTED_DECLARATIONS
    module.EXPECTED_SIGNATURE_EDGES = EXPECTED_SIGNATURE_EDGES
    module.EXPECTED_BODY_EDGES = EXPECTED_BODY_EDGES
    module.EXPECTED_UNION_EDGES = EXPECTED_UNION_EDGES
    module.EXPECTED_PRIVATE_DECLARATIONS = EXPECTED_PRIVATE_DECLARATIONS
    module.EXPECTED_GRAPH_REVERSE_CLOSURE = EXPECTED_GRAPH_REVERSE_CLOSURE
    module.EXPECTED_COMMANDS = EXPECTED_COMMANDS
    return module


def read_selector(path: Path) -> tuple[tuple[str, ...], dict[str, str]]:
    if sha256_file(path) != SELECTOR_SHA256:
        raise PlanError(f"selector hash differs: {path}")
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["module", "path"] or len(rows) != 30:
        raise PlanError("W04 selector must contain its exact header and 29 rows")
    owners = tuple(row[0] for row in rows[1:])
    paths = {row[0]: row[1] for row in rows[1:]}
    if len(paths) != 29 or owners != tuple(sorted(owners)):
        raise PlanError("W04 selector is duplicated or not sorted")
    return owners, paths


def parse_arguments() -> argparse.Namespace:
    script = Path(__file__).resolve()
    repo = script.parents[4]
    parser = argparse.ArgumentParser(
        description="Compute the C0006/P0009 W04 command-level private closure."
    )
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
    delivery = repo / "docs/architecture/deliveries/W04"
    output = args.output.resolve()
    if output.parent != delivery.resolve():
        raise PlanError(f"output must remain inside {delivery}")
    phase = control / "docs/architecture/phases/2026-08-repository-reorganization"
    owners, source_paths = read_selector(phase / "selectors/W04.tsv")

    frontend = load_frontend(repo)
    engine = frontend.load_engine(repo)
    engine.PHYSICAL_OWNERS = owners
    resolved = str(engine.run_git(repo, "rev-parse", f"{BASE}^{{commit}}"))
    if resolved != BASE:
        raise PlanError(f"W04 base unavailable: {resolved}")
    declarations, edges = engine.read_projection(phase / "projections/P0009.tsv.gz")
    edge_counts = Counter(edge.kind for edge in edges)
    union_count = len({(edge.source, edge.target) for edge in edges})
    if edge_counts != Counter(signature=EXPECTED_SIGNATURE_EDGES, body=EXPECTED_BODY_EDGES):
        raise PlanError(f"P0009 typed-edge counts differ: {dict(edge_counts)}")
    if union_count != EXPECTED_UNION_EDGES:
        raise PlanError(
            f"P0009 union-edge count is {union_count}, expected {EXPECTED_UNION_EDGES}"
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

    declaration_owners = tuple(sorted({item.module for item in declarations.values()}))
    declaration_commands, commands = frontend.map_declarations(
        engine, declarations, edges, all_commands, sources, declaration_owners
    )
    if EXPECTED_COMMANDS and len(commands) != EXPECTED_COMMANDS:
        raise PlanError(
            f"mapped {len(commands)} selected commands, expected {EXPECTED_COMMANDS}"
        )
    graph_floor = frontend.compute_graph_floor(declarations, edges)
    depth, chosen_target, chosen_witness = frontend.compute_command_closure(
        declarations, edges, commands, declaration_commands
    )
    rendered = frontend.render_plan(
        BASE,
        declarations,
        commands,
        evidence,
        depth,
        chosen_target,
        chosen_witness,
        graph_floor,
    )
    rendered = (
        rendered.replace("docs/architecture/deliveries/W06/PRIVATE_CLOSURE_PLAN.py", "docs/architecture/deliveries/W04/PRIVATE_CLOSURE_PLAN.py")
        .replace("\tP0007\n", "\tP0009\n")
    )
    if args.check:
        if not output.is_file() or output.read_text(encoding="utf-8") != rendered:
            raise PlanError(f"{output} is missing or stale")
        action = "verified"
    else:
        output.parent.mkdir(parents=True, exist_ok=True)
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
