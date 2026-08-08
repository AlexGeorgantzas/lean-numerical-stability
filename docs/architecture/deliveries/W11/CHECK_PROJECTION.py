#!/usr/bin/env python3
"""Hash-verify P0011 and replay its exact checker vector on a W11 candidate."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path


P0011_RECORD_SHA = "12E8250D43D6C543513B4317C235ACEB2E6B524559EE55EE20D19CFC0780E608"
CHECKER_SHA = "29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443"
PROJECTION_SHA = "0A13EF31C40C997E2A692AC595E96DD3416BA603C6EC4ED47AB60765E6EBB3E2"
SELECTOR_SHA = "24E3BD565946AECFDBAB9D2D21BF1201B86ECD16197F892E1B62A30162D9EE00"
COMBINED_JSON_SHA = "E9207AA896EAA547E791FB1CECAC7A6B4E6344E8DC8E15D2EF2372FF90570625"
COMBINED_RAW_SHA = "3BFEFF5663DA3FB5327B9D3AB22806654C9A79A48E1DDFE3C6E2E79073F9DE11"
INVENTORY_SHA = "5A8C01FE644CC2DD1190E2DDFEFBAD0EE16D01BD5F7863086E7D2DE5EE307FCC"
BATCH_SHA = "168B2D667E8A27DDE167B0691F4B31F1DEF2BD4F63CEC3B42E5912856195C206"
OVERLAP_SHA = "68C2A8B62D4DF1DC7F78CA9C3AD04405B6B0D25E74DC05372E6A0D3F697BC2F2"
BASELINE_GENERATOR_SHA = "AD1B19090B75936C874E6762989E4F06C0C1434C7DC7078E13499570BA3B6A63"
DEPENDENCY_EXTRACTOR_SHA = "04AE8E46F66A0B8D2FED1FDB83904D8A60398F9B61A3EC4A10ADB3DF2352D771"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest().upper()


def require_hash(path: Path, expected: str) -> None:
    actual = sha256(path)
    if actual != expected:
        raise RuntimeError(f"{path}: expected SHA-256 {expected}, found {actual}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--control-root", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    args = parser.parse_args()
    control = args.control_root.resolve()
    candidate = args.candidate.resolve()
    if not candidate.is_file():
        raise RuntimeError(f"candidate does not exist: {candidate}")

    phase = control / "docs/architecture/phases/2026-08-repository-reorganization"
    record_path = phase / "projections/P0011.json"
    require_hash(record_path, P0011_RECORD_SHA)
    record = json.loads(record_path.read_text(encoding="utf-8"))
    if (
        record.get("status") != "active"
        or record.get("base_checkpoint_id") != "C0006"
        or record.get("wave_id") != "W11"
        or record.get("expected_counts")
        != {
            "body_edges": 26201,
            "declarations": 3354,
            "signature_edges": 19096,
            "union_edges": 28652,
        }
    ):
        raise RuntimeError("P0011 is not the expected active W11/C0006 projection")

    checker = control / record["checker"]["artifact"]["path"]
    projection = control / record["projection_graph"]["path"]
    selector = control / record["selector"]["artifact"]["path"]
    combined_json = control / record["combined_baseline"]["path"]
    combined_raw = control / "benchmark-results/C0006-combined.tsv"
    inventory = phase / "checkpoints/C0006-inventory.tsv"
    batch = phase / "branches/B0010.json"
    overlap = phase / "branches/B0010-overlap-review.md"
    generator = control / "tools/architecture/generate_baseline.py"
    extractor = control / "tools/architecture/declaration_dependencies.lean"
    for path, expected in (
        (checker, CHECKER_SHA),
        (projection, PROJECTION_SHA),
        (selector, SELECTOR_SHA),
        (combined_json, COMBINED_JSON_SHA),
        (combined_raw, COMBINED_RAW_SHA),
        (inventory, INVENTORY_SHA),
        (batch, BATCH_SHA),
        (overlap, OVERLAP_SHA),
        (generator, BASELINE_GENERATOR_SHA),
        (extractor, DEPENDENCY_EXTRACTOR_SHA),
    ):
        require_hash(path, expected)

    recorded = list(record["checker"]["arguments"])
    placeholders = [
        index
        for index, item in enumerate(recorded)
        if item == "--candidate=<candidate-format2.tsv>"
    ]
    if len(recorded) != 54 or placeholders != [51]:
        raise RuntimeError(
            f"P0011 checker vector differs: length={len(recorded)}, "
            f"candidate placeholders={placeholders}"
        )
    if sum(item.startswith("--allow-module=") for item in recorded) != 18:
        raise RuntimeError("P0011 exact-module allowance count differs")
    if sum(item.startswith("--allow-prefix=") for item in recorded) != 33:
        raise RuntimeError("P0011 prefix allowance count differs")
    replay = list(recorded)
    replay[51] = f"--candidate={candidate}"
    if any(
        old != new
        for index, (old, new) in enumerate(zip(recorded, replay))
        if index != 51
    ):
        raise RuntimeError("checker argument vector changed beyond candidate replacement")

    completed = subprocess.run(
        [sys.executable, str(checker), *replay],
        cwd=control,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        encoding="utf-8",
        check=False,
    )
    print(completed.stdout, end="")
    expected_output = (
        "selected_declarations: 3354",
        "relocated_declarations: 3129",
        "signature_edges: 19096",
        "body_edges: 26201",
        "candidate_declarations_scanned: 56903",
        "candidate_edges_scanned: 649259",
        "allowed_exact_modules: 18",
        "allowed_prefixes: 33",
    )
    missing = [item for item in expected_output if item not in completed.stdout]
    if completed.returncode or missing:
        raise RuntimeError(
            f"P0011 replay failed: exit={completed.returncode}, missing={missing}"
        )
    print(f"candidate_sha256: {sha256(candidate)}")
    print("retained_declarations: 225")
    print("union_edges: 28652")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, ValueError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
