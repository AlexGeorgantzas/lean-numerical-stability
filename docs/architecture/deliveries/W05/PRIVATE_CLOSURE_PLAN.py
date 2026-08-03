#!/usr/bin/env python3
"""Compute W05's command-granular private-declaration retention plan.

This W05-specific front end pins and reuses the audited command-span engine
delivered with W02.  It reads the exact P0006 projection, frozen C0004 source
blobs, and C0004 ``.ilean`` command coordinates.  Private declarations and
their reverse dependency closure remain in the historical module; every
other complete command is a relocation candidate.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import sys
from pathlib import Path


BASE = "b56f609f3bf66b5d7d0b677567cce82fee0c275b"
PROJECTION_SHA256 = "6A15BC343C895BCE66A92B09EC333300CA842BEC249DDF2DC723D0832098FFB5"
ENGINE_SHA256 = "E353E4BE155CE70D33E272414C4C41CC2E6B3A0C8A8C9618A96CD868558D0BFD"

OWNERS = (
    "NumStability.Algorithms.Sylvester.Higham16",
    "NumStability.Algorithms.Sylvester.Higham16Lyapunov",
    "NumStability.Algorithms.Sylvester.Higham16Psi",
    "NumStability.Algorithms.Sylvester.SylvesterBackward",
    "NumStability.Algorithms.Sylvester.SylvesterPerturbation",
    "NumStability.Algorithms.Sylvester.SylvesterSpec",
    "NumStability.Analysis.InverseOpNorm2",
    "NumStability.Analysis.RealInvariantSubspace",
    "NumStability.Analysis.RealQuasiSchur",
    "NumStability.Analysis.SchurTriangulation",
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def load_engine(repo: Path):
    path = repo / "docs/architecture/deliveries/W02/PRIVATE_CLOSURE_PLAN.py"
    found = sha256(path)
    if found != ENGINE_SHA256:
        raise RuntimeError(
            f"private-closure engine hash differs: expected {ENGINE_SHA256}, found {found}"
        )
    spec = importlib.util.spec_from_file_location("w05_private_closure_engine", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load private-closure engine at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    module.FROZEN_BASE = BASE
    module.P0002_SHA256 = PROJECTION_SHA256
    module.EXPECTED_DECLARATIONS = 921
    module.EXPECTED_SIGNATURE_EDGES = 8_562
    module.EXPECTED_BODY_EDGES = 6_894
    module.EXPECTED_PHYSICAL_DECLARATIONS = 921
    module.EXPECTED_ILEAN_COMMANDS = 670
    module.EXPECTED_SOURCE_ALIAS_COMMANDS = 251
    module.EXPECTED_PRIVATE_SEEDS = 3
    module.EXPECTED_RETAINED_COMMANDS = 138
    module.PHYSICAL_OWNERS = OWNERS
    return module


def parse_arguments() -> argparse.Namespace:
    script = Path(__file__).resolve()
    repo = script.parents[4]
    parser = argparse.ArgumentParser(
        description="Compute the frozen C0004/P0006 private-command reverse closure."
    )
    parser.add_argument("--repo-root", type=Path, default=repo)
    parser.add_argument("--base", default=BASE)
    parser.add_argument("--projection", type=Path, required=True)
    parser.add_argument("--ilean-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, default=script.with_name("PRIVATE_CLOSURE.tsv"))
    parser.add_argument("--check", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_arguments()
    repo = args.repo_root.resolve()
    delivery = repo / "docs/architecture/deliveries/W05"
    output = args.output.resolve()
    if output.parent != delivery.resolve():
        raise RuntimeError(f"output must remain inside {delivery}")
    if args.base != BASE:
        raise RuntimeError(f"W05 base differs: expected {BASE}, found {args.base}")

    engine = load_engine(repo)
    resolved_base = str(engine.run_git(repo, "rev-parse", f"{args.base}^{{commit}}"))
    if resolved_base != BASE:
        raise RuntimeError(f"W05 base is unavailable: expected {BASE}, found {resolved_base}")

    declarations, edges = engine.read_projection(args.projection.resolve())
    commands = {}
    sources = {}
    evidence = {}
    for owner in OWNERS:
        relative_source = engine.module_path(owner, ".lean").as_posix()
        source_payload, source, blob = engine.read_base_source(
            repo, resolved_base, relative_source
        )
        sources[owner] = source
        relative_ilean = engine.module_path(owner, ".ilean")
        ilean_path = args.ilean_root.resolve() / relative_ilean
        ilean, ilean_digest = engine.read_ilean(ilean_path, owner)
        owner_commands = engine.commands_from_ilean(owner, ilean, source)
        overlap = set(commands).intersection(owner_commands)
        if overlap:
            raise RuntimeError(f"duplicate command keys: {sorted(overlap)[:5]}")
        commands.update(owner_commands)
        evidence[owner] = engine.OwnerEvidence(
            module=owner,
            source_path=relative_source,
            source_blob_sha1=blob,
            source_sha256=engine.sha256_bytes(source_payload),
            ilean_path=(Path(".lake/build/lib/lean") / relative_ilean).as_posix(),
            ilean_sha256=ilean_digest,
        )

    if len(commands) != 670:
        raise RuntimeError(f"expected 670 .ilean commands, found {len(commands)}")
    declaration_commands = engine.build_command_map(declarations, edges, commands, sources)
    aliases = sum(command.span_origin == "source_alias" for command in commands.values())
    if aliases != 251:
        raise RuntimeError(f"expected 251 source aliases, found {aliases}")
    depth, chosen_target, chosen_witness = engine.compute_closure(
        declarations, edges, commands, declaration_commands
    )
    rendered = engine.render_plan(
        resolved_base,
        declarations,
        commands,
        evidence,
        depth,
        chosen_target,
        chosen_witness,
    )
    rendered = rendered.replace(
        "docs/architecture/deliveries/W02/PRIVATE_CLOSURE_PLAN.py",
        "docs/architecture/deliveries/W05/PRIVATE_CLOSURE_PLAN.py",
    ).replace("P0002", "P0006").replace(
        "the 19 physical W02 owners", "the 10 physical W05 owners"
    )

    if args.check:
        if not output.is_file() or output.read_text(encoding="utf-8") != rendered:
            raise RuntimeError(f"{output} is missing or stale")
        action = "verified"
    else:
        output.write_text(rendered, encoding="utf-8", newline="")
        action = "wrote"
    print(
        f"{action} {output}: {len(commands)} commands, {len(depth)} retained, "
        f"{len(commands) - len(depth)} movable"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
