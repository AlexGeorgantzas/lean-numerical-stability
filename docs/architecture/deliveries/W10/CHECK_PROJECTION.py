#!/usr/bin/env python3
"""Replay active P0013 with only its candidate placeholder replaced."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import subprocess
import sys
from pathlib import Path

BASE = "9eb534a06db267203c2b9b88227edd44fc64f5db"
PLACEHOLDER = "--candidate=<candidate-format2.tsv>"
PHASE = "docs/architecture/phases/2026-08-repository-reorganization/"
RAW_PROJECTION_SHA256 = "56B8FFD7024AE943C7E35AF3ACCC3106EFCEA068ED68C6AB7B42D0055DE479B0"
CANDIDATE_ARTIFACTS = {
    ".tsv": ("749CC6B1888CF99BA5A44AC74A55A51A1DC23FD2EC7BE11D533F0E34BE128E61", 116677351),
    ".json": ("86422CC6BFB76B0D3FF7CF0515232E4DAEB8487473964B628C5252F757C03653", 104847),
    ".md": ("74EC53E847199D2012E1BC344F8BD7E0118AE6B5065EA35BB7F5D6531C63C9E3", 17095),
}
PINS = {
    PHASE + "projections/P0013.tsv.gz": "B61F64FC0C2CEF8DF22DDA78C5F28BB8D6B64FC1B57392AA36A2E187F3396ABA",
    PHASE + "selectors/W10.tsv": "444AA9109E4990AD47E281D550EA7A80057A8DBC493D8AF1693760EE7434BBB0",
    PHASE + "baselines/C0007-combined.json": "D9372A79DA159CEB50757F6581F650957D2868E738E41C0D5F892C121623CADD",
    PHASE + "checkpoints/C0007-inventory.tsv": "56B08C666F4461BE2B425E12B2E250ACFCD4604A43F793A066AA086091365196",
    "tools/architecture/check_phase_projection.py": "29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443",
}


class ProjectionError(RuntimeError):
    pass


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def main() -> int:
    script = Path(__file__).resolve()
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, default=script.parents[4])
    parser.add_argument("--control-root", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    args = parser.parse_args()
    control, candidate = args.control_root.resolve(), args.candidate.resolve()
    if not candidate.is_file():
        raise ProjectionError(f"candidate missing: {candidate}")
    for suffix, (expected_sha, expected_size) in CANDIDATE_ARTIFACTS.items():
        artifact = candidate.with_suffix(suffix)
        if not artifact.is_file() or artifact.stat().st_size != expected_size or sha(artifact) != expected_sha:
            raise ProjectionError(f"final candidate artifact differs: {artifact}")
    for relative, expected in PINS.items():
        path = control / relative
        if not path.is_file() or sha(path) != expected:
            raise ProjectionError(f"pinned control artifact differs: {relative}")
    compressed_projection = control / (PHASE + "projections/P0013.tsv.gz")
    if hashlib.sha256(gzip.decompress(compressed_projection.read_bytes())).hexdigest().upper() != RAW_PROJECTION_SHA256:
        raise ProjectionError("decompressed P0013 raw projection differs")
    branch = json.loads((control / (PHASE + "branches/B0012.json")).read_text())
    if any(branch.get(k) != v for k, v in {
        "status": "active", "branch_id": "B0012", "wave_id": "W10",
        "base_checkpoint_id": "C0007", "base_sha": BASE, "baseline_projection_id": "P0013",
    }.items()):
        raise ProjectionError("active B0012 differs")
    record = json.loads((control / (PHASE + "projections/P0013.json")).read_text())
    if record.get("status") != "active" or record.get("expected_counts") != {
        "body_edges": 4844, "declarations": 1029, "signature_edges": 2394, "union_edges": 5075,
    }:
        raise ProjectionError("P0013 record/counts differ")
    arguments = list(record["checker"]["arguments"])
    if len(arguments) != 73 or arguments.count(PLACEHOLDER) != 1:
        raise ProjectionError("P0013 argument vector differs")
    if sum(x.startswith("--allow-module=") for x in arguments) != 27 or sum(x.startswith("--allow-prefix=") for x in arguments) != 43:
        raise ProjectionError("P0013 allow roster differs")
    arguments = [f"--candidate={candidate.as_posix()}" if x == PLACEHOLDER else x for x in arguments]
    result = subprocess.run(
        [sys.executable, "-B", str(control / record["checker"]["artifact"]["path"]), *arguments],
        cwd=control, text=True, capture_output=True,
    )
    output = result.stdout + result.stderr
    if result.returncode:
        raise ProjectionError("P0013 replay failed:\n" + output)
    for expected in (
        "phase projection contract passed", "selected_declarations: 1029", "relocated_declarations: 895",
        "signature_edges: 2394", "body_edges: 4844", "allowed_exact_modules: 27", "allowed_prefixes: 43",
        "candidate_declarations_scanned: 56903", "candidate_edges_scanned: 649259",
    ):
        if expected not in output:
            raise ProjectionError(f"replay output lacks {expected}")
    print(output.rstrip())
    print(f"candidate_sha256={sha(candidate)}")
    print("retained_declarations=134\nprivate_reverse_closure=132\nfull_graph_reentry_retention=2\nunion_edges=5075")
    print("P0013 argument vector preserved: 73 arguments; only candidate placeholder replaced")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ProjectionError, OSError, ValueError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
