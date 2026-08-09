#!/usr/bin/env python3
"""Replay active P0012 with only its candidate placeholder replaced."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path


PLACEHOLDER = "--candidate=<candidate-format2.tsv>"
BASE = "9eb534a06db267203c2b9b88227edd44fc64f5db"
BRANCH = "codex/reorg-2026-08-w07-stationary-ch17"
PHASE_PREFIX = "docs/architecture/phases/2026-08-repository-reorganization/"
PINNED_CONTROL = {
    PHASE_PREFIX + "branches/B0011.json":
        "41EFB88CE76180E1C0BBD803A605F560D3B339B3BBC5B132B6003E88A520FFF2",
    PHASE_PREFIX + "branches/B0011-overlap-review.md":
        "67E704A1A8CA8FCDA43F20EB428FA0BE1423BAB7EAB4314CC7D5BF9BECEFD500",
    PHASE_PREFIX + "baselines/C0007-combined.json":
        "D9372A79DA159CEB50757F6581F650957D2868E738E41C0D5F892C121623CADD",
    PHASE_PREFIX + "baselines/C0007-combined.md":
        "A9C897F4E2EDCDE3B3CAFE5D297B11A05E5D20BA5CC2AF3BD746C90D02F5D3AC",
    PHASE_PREFIX + "checkpoints/C0007.json":
        "7D5E6E25CC1FBB96B3BC792DF79E9D39425DE26BFAF3523069BA210D8D3095D3",
    PHASE_PREFIX + "checkpoints/C0007-inventory.tsv":
        "56B08C666F4461BE2B425E12B2E250ACFCD4604A43F793A066AA086091365196",
    PHASE_PREFIX + "checkpoints/C0007-integrator-paths.tsv":
        "007FECE988156DE622788EA388CF4217FB71B560D6305436F560CA29E83A3C43",
    PHASE_PREFIX + "checkpoints/C0007-gates.md":
        "FD53B43E6D31EBDD2B4A2F62E3324E30747B2AE3E8DAA8D80333DD02B597054F",
    PHASE_PREFIX + "projections/P0012.json":
        "093C8F260B8303E112FE5DF5B3636473021365C2E81C3725B5BE2A3FBD2BB024",
    PHASE_PREFIX + "projections/P0012.tsv.gz":
        "9B683940DE4C94D17E48E200D1F10594EB26614CFD2AEF2BCB036F667BB5159C",
    PHASE_PREFIX + "selectors/W07.tsv":
        "478EFA94CE2311ECD54A7AA4A155336EF3DB8219BFA42E137BA7C37D0D97176A",
    "tools/architecture/check_phase_projection.py":
        "29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443",
    "tools/architecture/generate_baseline.py":
        "AD1B19090B75936C874E6762989E4F06C0C1434C7DC7078E13499570BA3B6A63",
    "tools/architecture/declaration_dependencies.lean":
        "04AE8E46F66A0B8D2FED1FDB83904D8A60398F9B61A3EC4A10ADB3DF2352D771",
    "benchmark-results/C0007-combined.tsv":
        "80AE3FBB3948104C60FF7EA80E899CC11CE542D0A772EA087375C00EB0ED9ED3",
}


class ProjectionError(RuntimeError):
    pass


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def main() -> int:
    script = Path(__file__).resolve()
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, default=script.parents[4])
    parser.add_argument("--control-root", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    args = parser.parse_args()
    repo = args.repo_root.resolve()
    control = args.control_root.resolve()
    candidate = args.candidate.resolve()
    if not candidate.is_file():
        raise ProjectionError(f"candidate is missing: {candidate}")
    for relative, expected in PINNED_CONTROL.items():
        path = control / relative
        if not path.is_file() or sha256(path) != expected:
            raise ProjectionError(f"pinned control artifact differs: {relative}")
    phase = control / "docs/architecture/phases/2026-08-repository-reorganization"
    branch = json.loads((phase / "branches/B0011.json").read_text(encoding="utf-8"))
    expected_branch = {
        "status": "active",
        "branch_id": "B0011",
        "wave_id": "W07",
        "lane_id": "local-lane",
        "owner_id": "primary-human",
        "branch_name": BRANCH,
        "base_checkpoint_id": "C0007",
        "base_sha": BASE,
        "baseline_projection_id": "P0012",
    }
    for key, expected in expected_branch.items():
        if branch.get(key) != expected:
            raise ProjectionError(f"B0011 field differs: {key}")
    if branch.get("operator_ids") != ["codex-local"]:
        raise ProjectionError("B0011 operator_ids differ")
    record = json.loads((phase / "projections/P0012.json").read_text(encoding="utf-8"))
    if record.get("status") != "active" or record.get("projection_id") != "P0012":
        raise ProjectionError("P0012 is not active")
    if record.get("expected_counts") != {
        "body_edges": 1400,
        "declarations": 252,
        "signature_edges": 800,
        "union_edges": 1474,
    }:
        raise ProjectionError("P0012 expected counts differ")
    if record.get("combined_baseline") != {
        "path": PHASE_PREFIX + "baselines/C0007-combined.json",
        "sha256": PINNED_CONTROL[PHASE_PREFIX + "baselines/C0007-combined.json"],
    }:
        raise ProjectionError("P0012 combined baseline differs")
    checker = control / record["checker"]["artifact"]["path"]
    projection = control / record["projection_graph"]["path"]
    recorded = list(record["checker"]["arguments"])
    if (
        len(recorded) != 42
        or recorded.count(PLACEHOLDER) != 1
        or recorded[39] != PLACEHOLDER
        or sum(item.startswith("--allow-module=") for item in recorded) != 5
        or sum(item.startswith("--allow-prefix=") for item in recorded) != 34
    ):
        raise ProjectionError("P0012 recorded argument vector differs")
    replacement = f"--candidate={candidate.as_posix()}"
    arguments = [replacement if item == PLACEHOLDER else item for item in recorded]
    command = [sys.executable, "-B", str(checker), *arguments]
    result = subprocess.run(command, cwd=control, text=True, capture_output=True)
    output = result.stdout + result.stderr
    if result.returncode:
        raise ProjectionError("P0012 replay failed:\n" + output)
    required = (
        "phase projection contract passed",
        "selected_declarations: 252",
        "relocated_declarations: 136",
        "signature_edges: 800",
        "body_edges: 1400",
        "candidate_declarations_scanned: 56903",
        "candidate_edges_scanned: 649259",
        "allowed_exact_modules: 5",
        "allowed_prefixes: 34",
    )
    if not all(line in output for line in required):
        raise ProjectionError("P0012 replay output lacks expected counts:\n" + output)
    print(output.rstrip())
    print(f"candidate_sha256={sha256(candidate)}")
    print("retained_declarations=116")
    print("union_edges=1474")
    print("P0012 argument vector preserved: 42 arguments; only candidate placeholder replaced")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ProjectionError, OSError, ValueError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
