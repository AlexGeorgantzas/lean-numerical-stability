#!/usr/bin/env python3
"""Replay active P0001 with exactly its recorded arguments except the candidate placeholder."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
ACTIVE_CONTROL = "daf5c92355e26c07ab0d219c20cd6ce6782b98f3"
BASE = "b1b18772d80185ec08f49c818919558645c330a1"
BRANCH = "codex/reorg-completion-2026-08-r01-stationary-semiconvergence"
PHASE = Path("docs/architecture/phases/2026-08-repository-reorganization-completion")
B_PATH = PHASE / "branches/B0001.json"
P_PATH = PHASE / "projections/P0001.json"
EXPECTED = {
    "docs/architecture/phases/2026-08-repository-reorganization-completion/baselines/C0000-combined.json":
        "2EA9D8C24D3E4D3EEA6B3A135FE195946BB8659C7E5FBF9452DADD89D1726A2F",
    "docs/architecture/phases/2026-08-repository-reorganization-completion/branches/B0001-declaration-routes.tsv":
        "1493383A571EFFDECCD2DF5D5C8DF2657139B2BA140D271B0706C86D32397A52",
    "docs/architecture/phases/2026-08-repository-reorganization-completion/branches/B0001-module-routes.tsv":
        "5BAF7963A4806F1A04931C25980C531BEE21B791255C76854E26BEF4149FE0FD",
    "docs/architecture/phases/2026-08-repository-reorganization-completion/branches/B0001-overlap-review.md":
        "CD1DB2CFC926A545D83D62E378CF38FF442E80D3A2560E2FE60A5082B40DBE7F",
    "docs/architecture/phases/2026-08-repository-reorganization-completion/branches/B0001-private-closure.tsv":
        "CB19F5F3C66C56CE5F688E5E310D64713834635AFDFB77D7CB24DC1EC9D88598",
    "docs/architecture/phases/2026-08-repository-reorganization-completion/branches/B0001-private-normalization.tsv":
        "0063E4B0E9C1DAD56F0CCD0A5B9D3897D6F18BEF860482AEB609B83DF6CD4F4A",
    "docs/architecture/phases/2026-08-repository-reorganization-completion/branches/B0001-test-plan.tsv":
        "993AC1CCA7022009454622249E6D35A4E327AD1EBB8B55C45CD52F7E25E4EA6C",
    "docs/architecture/phases/2026-08-repository-reorganization-completion/checkpoints/C0000-inventory.tsv":
        "05C2DFB3F1A99F928E90DB3E3EA0C2277320DD3985C476ACB1D529762410776F",
    "docs/architecture/phases/2026-08-repository-reorganization-completion/projections/P0001.tsv.gz":
        "DB8ACB22219D5C0C51E3F8F8D5296170FDF92C8C1166C0FDB2598EF6E11728D2",
    "docs/architecture/phases/2026-08-repository-reorganization-completion/selectors/R01.tsv":
        "6D839B9008474CD9CBECEF5EE35FE347B91FD50541F8E347AA8648FF55EF81EB",
    "tools/architecture/check_completion_phase_projection.py":
        "0F32935ED1EFDD2BD4D6A4C346F3E8300C86DB1D4A3551A17165479226109220",
}
EXPECTED_ARGUMENTS = 24
EXPECTED_ALLOW_MODULES = 16
EXPECTED_ALLOW_PREFIXES = 3
EXPECTED_PRIVATE_NORMALIZATIONS = 10
EXPECTED_CANDIDATE_DECLARATIONS = 56_903
EXPECTED_CANDIDATE_SIGNATURE_EDGES = 266_387
EXPECTED_CANDIDATE_BODY_EDGES = 382_872
EXPECTED_CANDIDATE_TYPED_EDGES = 649_259
EXPECTED_CANDIDATE_UNION_EDGES = 424_082
PROJECTION_SHA256 = EXPECTED[
    "docs/architecture/phases/2026-08-repository-reorganization-completion/"
    "projections/P0001.tsv.gz"
]
PRIVATE_MAP_SHA256 = EXPECTED[
    "docs/architecture/phases/2026-08-repository-reorganization-completion/"
    "branches/B0001-private-normalization.tsv"
]


class ProjectionError(RuntimeError):
    pass


def run(args: list[str], cwd: Path, *, check: bool = True) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        args, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT
    )
    if check and result.returncode:
        raise ProjectionError((result.stdout or "") + f"command failed: {' '.join(args)}")
    return result


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def default_control() -> Path:
    sibling = ROOT.parent / "final-main-audit"
    return sibling if sibling.is_dir() else ROOT


def validate_candidate_artifacts(candidate: Path) -> dict[str, tuple[Path, int, str]]:
    if candidate.suffix != ".tsv":
        raise ProjectionError("candidate must be the full format-2 TSV")
    artifacts = {
        "tsv": candidate,
        "json": candidate.with_suffix(".json"),
        "md": candidate.with_suffix(".md"),
    }
    summaries: dict[str, tuple[Path, int, str]] = {}
    for label, path in artifacts.items():
        if not path.is_file():
            raise ProjectionError(f"candidate {label.upper()} missing: {path}")
        if path.stat().st_size == 0:
            raise ProjectionError(f"candidate {label.upper()} is empty: {path}")
        try:
            relative = path.relative_to(ROOT).as_posix()
        except ValueError as error:
            raise ProjectionError(
                f"candidate {label.upper()} is outside the worker checkout: {path}"
            ) from error
        ignored = run(
            ["git", "check-ignore", "-q", "--", relative], ROOT, check=False
        )
        if ignored.returncode != 0:
            raise ProjectionError(
                f"candidate {label.upper()} is not ignored: {relative}"
            )
        tracked = run(["git", "ls-files", "--", relative], ROOT)
        if tracked.stdout.strip():
            raise ProjectionError(
                f"candidate {label.upper()} is tracked: {relative}"
            )
        summaries[label] = (path, path.stat().st_size, sha256(path))

    payload = json.loads(artifacts["json"].read_text(encoding="utf-8"))
    declarations = payload.get("declarations")
    if not isinstance(declarations, dict):
        raise ProjectionError("candidate JSON lacks declaration metrics")
    edge_counts = declarations.get("edge_counts")
    if not isinstance(edge_counts, dict):
        raise ProjectionError("candidate JSON lacks declaration edge counts")
    actual = {
        "format_version": declarations.get("format_version"),
        "declaration_count": declarations.get("declaration_count"),
        "signature_edges": edge_counts.get("signature"),
        "body_edges": edge_counts.get("body_or_proof"),
        "union_edges": edge_counts.get("union"),
    }
    expected = {
        "format_version": 2,
        "declaration_count": EXPECTED_CANDIDATE_DECLARATIONS,
        "signature_edges": EXPECTED_CANDIDATE_SIGNATURE_EDGES,
        "body_edges": EXPECTED_CANDIDATE_BODY_EDGES,
        "union_edges": EXPECTED_CANDIDATE_UNION_EDGES,
    }
    if actual != expected:
        raise ProjectionError(
            f"candidate JSON declaration totals differ: {actual} != {expected}"
        )
    if actual["signature_edges"] + actual["body_edges"] != EXPECTED_CANDIDATE_TYPED_EDGES:
        raise ProjectionError("candidate JSON typed-edge total differs")
    return summaries


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("candidate", type=Path)
    parser.add_argument("--control-root", type=Path, default=default_control())
    args = parser.parse_args()
    candidate = args.candidate.resolve()
    control = args.control_root.resolve()
    if not candidate.is_file():
        raise ProjectionError(f"candidate missing: {candidate}")
    candidate_artifacts = validate_candidate_artifacts(candidate)
    if run(["git", "rev-parse", "HEAD"], control).stdout.strip() != ACTIVE_CONTROL:
        raise ProjectionError("control checkout is not the green active-control commit")
    if run(["git", "status", "--porcelain", "--untracked-files=all"], control).stdout.strip():
        raise ProjectionError("control checkout is not clean")

    branch = json.loads((control / B_PATH).read_text(encoding="utf-8"))
    projection = json.loads((control / P_PATH).read_text(encoding="utf-8"))
    if not (
        branch["status"] == "active"
        and branch["branch_id"] == "B0001"
        and branch["branch_name"] == BRANCH
        and branch["operator_ids"] == ["codex-local"]
        and branch["base_checkpoint_id"] == "C0000"
        and branch["base_sha"] == BASE
        and branch["baseline_projection_id"] == "P0001"
    ):
        raise ProjectionError("B0001 authority differs")
    if not (
        projection["status"] == "active"
        and projection["projection_id"] == "P0001"
        and projection["wave_id"] == "R01"
        and projection["base_checkpoint_id"] == "C0000"
        and projection["expected_counts"] == {
            "body_edges": 1341,
            "declarations": 243,
            "signature_edges": 693,
            "union_edges": 1422,
        }
    ):
        raise ProjectionError("P0001 authority differs")

    for relative, expected in EXPECTED.items():
        path = control / relative
        actual = sha256(path)
        if actual != expected:
            raise ProjectionError(f"control artifact hash differs: {relative}: {actual}")

    recorded = list(projection["checker"]["arguments"])
    placeholder = "--candidate=<candidate-format2.tsv>"
    if (
        len(recorded) != EXPECTED_ARGUMENTS
        or recorded.count(placeholder) != 1
        or sum(item.startswith("--allow-module=") for item in recorded)
        != EXPECTED_ALLOW_MODULES
        or sum(item.startswith("--allow-prefix=") for item in recorded)
        != EXPECTED_ALLOW_PREFIXES
    ):
        raise ProjectionError("P0001 recorded argument vector differs")
    replay = [
        f"--candidate={candidate}" if argument == placeholder else argument
        for argument in recorded
    ]
    if len(replay) != len(recorded):
        raise ProjectionError("argument count differs")
    for old, new in zip(recorded, replay, strict=True):
        if old != placeholder and old != new:
            raise ProjectionError("an argument other than the candidate changed")

    checker = control / projection["checker"]["artifact"]["path"]
    result = run([sys.executable, "-B", str(checker), *replay], control)
    candidate_sha256 = candidate_artifacts["tsv"][2]
    expected_output = [
        "phase projection contract passed",
        f"projection_sha256: {PROJECTION_SHA256}",
        f"candidate_sha256: {candidate_sha256}",
        "selected_declarations: 243",
        "relocated_declarations: 243",
        "signature_edges: 693",
        "body_edges: 1341",
        f"candidate_declarations_scanned: {EXPECTED_CANDIDATE_DECLARATIONS}",
        f"candidate_edges_scanned: {EXPECTED_CANDIDATE_TYPED_EDGES}",
        f"allowed_exact_modules: {EXPECTED_ALLOW_MODULES}",
        f"allowed_prefixes: {EXPECTED_ALLOW_PREFIXES}",
        f"private_map_sha256: {PRIVATE_MAP_SHA256}",
        f"private_normalizations: {EXPECTED_PRIVATE_NORMALIZATIONS}",
    ]
    actual_output = result.stdout.splitlines()
    if actual_output != expected_output:
        raise ProjectionError(
            "P0001 replay output differs from the exact expected ledger:\n"
            + result.stdout
        )
    print(result.stdout, end="")
    print(
        "R01 P0001 replay passed: "
        f"arguments={len(replay)}, candidate_bytes={candidate.stat().st_size}, "
        f"candidate_sha256={candidate_sha256}, declarations=243, relocated=243, "
        "signature_edges=693, body_edges=1341, union_edges=1422"
    )
    for label in ("tsv", "json", "md"):
        _path, size, digest = candidate_artifacts[label]
        print(f"candidate_{label}_bytes: {size}")
        print(f"candidate_{label}_sha256: {digest}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ProjectionError, KeyError, ValueError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
