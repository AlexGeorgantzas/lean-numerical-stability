#!/usr/bin/env python3
"""Hash-verify P0007 and replay its exact checker vector on a W06 candidate."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path


CHECKER_SHA = "29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443"
PROJECTION_SHA = "E1C2787CC0D0D8A08E016932CEBC1831FAD6929BF22FA757D12BFC49F8ADCF39"
SELECTOR_SHA = "5D482CF32C656C77AF3AABA674C3FE39AA5AEBD0FED6BC0C3E569DCDB328E484"
COMBINED_JSON_SHA = "D961829AA197564A94193B9909695E6DA077D02B64F07EFC6FC531BB291EF190"
COMBINED_RAW_SHA = "1DA19910927D41F4B45266ABA3F5E1A1F165637F7E984F8A19E15DA4FBB4A8D0"
OVERLAP_SHA = "4A2CC83F6BFA8A31E97E1647D4BAB30421F16949E3AC38873A594807DBC7FCE5"


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
    record_path = phase / "projections/P0007.json"
    record = json.loads(record_path.read_text(encoding="utf-8"))
    if (
        record.get("status") != "active"
        or record.get("base_checkpoint_id") != "C0005"
        or record.get("expected_counts") != {
            "body_edges": 16341,
            "declarations": 3512,
            "signature_edges": 15044,
            "union_edges": 22079,
        }
    ):
        raise RuntimeError("P0007 is not the expected active C0005 projection")

    checker = control / record["checker"]["artifact"]["path"]
    projection = control / record["projection_graph"]["path"]
    selector = control / record["selector"]["artifact"]["path"]
    combined_json = control / record["combined_baseline"]["path"]
    combined_raw = control / "benchmark-results/C0005-combined.tsv"
    overlap = phase / "branches/B0006-overlap-review.md"
    for path, expected in (
        (checker, CHECKER_SHA),
        (projection, PROJECTION_SHA),
        (selector, SELECTOR_SHA),
        (combined_json, COMBINED_JSON_SHA),
        (combined_raw, COMBINED_RAW_SHA),
        (overlap, OVERLAP_SHA),
    ):
        require_hash(path, expected)

    recorded = list(record["checker"]["arguments"])
    placeholders = [index for index, item in enumerate(recorded) if item == "--candidate=<candidate-format2.tsv>"]
    if len(placeholders) != 1:
        raise RuntimeError(f"P0007 candidate placeholder count differs: {placeholders}")
    replay = list(recorded)
    replay[placeholders[0]] = f"--candidate={candidate}"
    if any(
        old != new for index, (old, new) in enumerate(zip(recorded, replay))
        if index != placeholders[0]
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
        "selected_declarations: 3512",
        "relocated_declarations: 2737",
        "signature_edges: 15044",
        "body_edges: 16341",
    )
    missing = [item for item in expected_output if item not in completed.stdout]
    if completed.returncode or missing:
        raise RuntimeError(
            f"P0007 replay failed: exit={completed.returncode}, missing={missing}"
        )
    print(f"candidate_sha256: {sha256(candidate)}")
    print("retained_declarations: 775")
    print("union_edges: 22079")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, ValueError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
