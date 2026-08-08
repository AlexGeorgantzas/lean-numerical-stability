#!/usr/bin/env python3
"""Hash-verify P0009 and replay its exact checker vector on a W04 candidate."""

from __future__ import annotations

import argparse
import csv
import gzip
import hashlib
import io
import json
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path


CHECKER_SHA = "29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443"
PROJECTION_SHA = "EAA15F18127E7B77F8AF442760590687B66A8860485590F2EB13D57E3A6F3814"
SELECTOR_SHA = "92446B8EBF571733212239DBD471A377EA889FC2A7061F1500DE7B03DB96518F"
COMBINED_JSON_SHA = "E9207AA896EAA547E791FB1CECAC7A6B4E6344E8DC8E15D2EF2372FF90570625"
OVERLAP_SHA = "B285FBD180581D715A208652B713D2A2B85C622F609C2BE3926D7339B133F4C9"
CANDIDATE_SHA = "6CA03A2F9F38963AA3DF0D40DC3F3A5ECF57A878F93BA4C9732F7DA3904E47D4"
CANDIDATE_BYTES = 116512944
PRIVATE_CLOSURE_SHA = "B55744FBEA898C63D34F7D4F81F7C75C65AF69DC5EDAFA359AAF023095FC4AB7"


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


def declaration_rows(path: Path) -> dict[str, tuple[str, str, str]]:
    opener = gzip.open if path.read_bytes()[:2] == b"\x1f\x8b" else open
    declarations = {}
    with opener(path, "rt", encoding="utf-8", newline="") as stream:
        for row in csv.reader(stream, delimiter="\t"):
            if len(row) == 5 and row[0] == "declaration":
                if row[1] in declarations:
                    raise RuntimeError(f"duplicate candidate declaration: {row[1]}")
                declarations[row[1]] = (row[2], row[3], row[4])
    return declarations


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--control-root", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    args = parser.parse_args()
    control = args.control_root.resolve()
    candidate = args.candidate.resolve()
    if not candidate.is_file():
        raise RuntimeError(f"candidate does not exist: {candidate}")
    require_hash(candidate, CANDIDATE_SHA)
    if candidate.stat().st_size != CANDIDATE_BYTES:
        raise RuntimeError(
            f"candidate size differs: {candidate.stat().st_size} != {CANDIDATE_BYTES}"
        )
    closure = Path(__file__).resolve().parent / "PRIVATE_CLOSURE.tsv"
    require_hash(closure, PRIVATE_CLOSURE_SHA)
    phase = control / "docs/architecture/phases/2026-08-repository-reorganization"
    record_path = phase / "projections/P0009.json"
    record = json.loads(record_path.read_text(encoding="utf-8"))
    expected_counts = {
        "body_edges": 10044,
        "declarations": 1238,
        "signature_edges": 5684,
        "union_edges": 10624,
    }
    if (
        record.get("status") != "active"
        or record.get("base_checkpoint_id") != "C0006"
        or record.get("wave_id") != "W04"
        or record.get("expected_counts") != expected_counts
    ):
        raise RuntimeError("P0009 is not the exact active C0006/W04 projection")

    checker = control / record["checker"]["artifact"]["path"]
    projection = control / record["projection_graph"]["path"]
    selector = control / record["selector"]["artifact"]["path"]
    combined_json = control / record["combined_baseline"]["path"]
    overlap = phase / "branches/B0008-overlap-review.md"
    for path, expected in (
        (checker, CHECKER_SHA),
        (projection, PROJECTION_SHA),
        (selector, SELECTOR_SHA),
        (combined_json, COMBINED_JSON_SHA),
        (overlap, OVERLAP_SHA),
    ):
        require_hash(path, expected)

    kinds, visibility, edge_kinds = Counter(), Counter(), Counter()
    union = set()
    with gzip.open(io.BytesIO(projection.read_bytes()), "rt", encoding="utf-8", newline="") as stream:
        for row in csv.reader(stream, delimiter="\t"):
            if len(row) == 5 and row[0] == "declaration":
                kinds[row[3]] += 1
                visibility[row[4]] += 1
            elif len(row) == 4 and row[0] == "edge":
                edge_kinds[row[1]] += 1
                union.add((row[2], row[3]))
    if kinds != Counter(theorem=904, definition=283, inductive=17, constructor=17, recursor=17):
        raise RuntimeError(f"P0009 declaration kinds differ: {dict(kinds)}")
    if visibility != Counter(public=1198, private=40):
        raise RuntimeError(f"P0009 visibility differs: {dict(visibility)}")
    if edge_kinds != Counter(signature=5684, body=10044) or len(union) != 10624:
        raise RuntimeError("P0009 typed or union edge counts differ")

    projected = declaration_rows(projection)
    candidate_declarations = declaration_rows(candidate)
    private_owner_errors = sorted(
        f"{name}: {candidate_declarations.get(name)} != {baseline}"
        for name, baseline in projected.items()
        if baseline[2] == "private" and candidate_declarations.get(name) != baseline
    )
    if len([item for item in projected.values() if item[2] == "private"]) != 40:
        raise RuntimeError("P0009 private declaration inventory differs")
    if private_owner_errors:
        raise RuntimeError(
            "private declaration identity/module drift: " + "; ".join(private_owner_errors)
        )

    recorded = list(record["checker"]["arguments"])
    if len(recorded) != 74:
        raise RuntimeError(f"P0009 checker argument count is {len(recorded)}, expected 74")
    if sum(item.startswith("--allow-module=") for item in recorded) != 29:
        raise RuntimeError("P0009 exact module argument count differs")
    if sum(item.startswith("--allow-prefix=") for item in recorded) != 42:
        raise RuntimeError("P0009 prefix argument count differs")
    placeholders = [
        index for index, item in enumerate(recorded)
        if item == "--candidate=<candidate-format2.tsv>"
    ]
    if len(placeholders) != 1:
        raise RuntimeError(f"P0009 candidate placeholder count differs: {placeholders}")
    replay = list(recorded)
    replay[placeholders[0]] = f"--candidate={candidate}"
    if any(
        old != new for index, (old, new) in enumerate(zip(recorded, replay))
        if index != placeholders[0]
    ):
        raise RuntimeError("checker vector changed beyond candidate replacement")

    started = time.perf_counter()
    completed = subprocess.run(
        [sys.executable, str(checker), *replay],
        cwd=control,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        encoding="utf-8",
        check=False,
    )
    elapsed = time.perf_counter() - started
    print(completed.stdout, end="")
    expected_output = (
        "selected_declarations: 1238",
        "relocated_declarations: 1018",
        "signature_edges: 5684",
        "body_edges: 10044",
        "candidate_declarations_scanned: 56903",
        "candidate_edges_scanned: 649259",
        "allowed_exact_modules: 29",
        "allowed_prefixes: 42",
    )
    missing = [item for item in expected_output if item not in completed.stdout]
    if completed.returncode or missing:
        raise RuntimeError(
            f"P0009 replay failed: exit={completed.returncode}, missing={missing}"
        )
    result = {
        "checker_sha256": CHECKER_SHA,
        "projection_sha256": PROJECTION_SHA,
        "selector_sha256": SELECTOR_SHA,
        "combined_json_sha256": COMBINED_JSON_SHA,
        "overlap_review_sha256": OVERLAP_SHA,
        "candidate_sha256": CANDIDATE_SHA,
        "candidate_bytes": CANDIDATE_BYTES,
        "private_closure_sha256": PRIVATE_CLOSURE_SHA,
        "checker_argument_count": len(recorded),
        "selected_declarations": 1238,
        "relocated_declarations": 1018,
        "retained_declarations": 220,
        "private_declarations_fixed_at_historical_owner": 40,
        "signature_edges": 5684,
        "body_edges": 10044,
        "union_edges": 10624,
        "checker_exit": completed.returncode,
        "checker_seconds": round(elapsed, 3),
    }
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, ValueError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
