#!/usr/bin/env python3
"""Replay active P0004 with exactly its recorded arguments."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import subprocess
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
CONTROL_SHA = "5e075b947a63e84c784afecd00e1f130e21ea659"
BASE = "117aa2bb7e61f41e1531a78452f9f7f6cd5b0771"
PHASE = Path("docs/architecture/phases/2026-08-repository-reorganization-completion")
B_PATH = PHASE / "branches/B0004.json"
P_PATH = PHASE / "projections/P0004.json"
PROJECTION_SHA = "E84302EC06E0215758B91F9B179D89E0A5E17931CF42734828F1253BB4C129D2"
PRIVATE_SHA = "3266EAFAE1CD51DCBF459760E1D24DC5F88E2E29AA3E633D3B313DCF96CA368C"
CHECKER_SHA = "0F32935ED1EFDD2BD4D6A4C346F3E8300C86DB1D4A3551A17165479226109220"
EXPECTED_GLOBAL = {
    "format_version": 2,
    "declaration_count": 56_903,
    "signature_edges": 266_387,
    "body_edges": 382_872,
    "union_edges": 424_082,
}


class ProjectionError(RuntimeError):
    pass


def run(args: list[str], cwd: Path, check: bool = True) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        args, cwd=cwd, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    if check and result.returncode:
        raise ProjectionError((result.stdout or "") + f"command failed: {' '.join(args)}")
    return result


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def default_control() -> Path:
    candidate = ROOT.parent / "completion-integrator-c0001"
    return candidate if candidate.is_dir() else ROOT


def candidate_artifacts(candidate: Path) -> dict[str, tuple[int, str]]:
    if candidate.suffix != ".tsv":
        raise ProjectionError("candidate must be a format-2 TSV")
    artifacts = {
        "tsv": candidate,
        "json": candidate.with_suffix(".json"),
        "md": candidate.with_suffix(".md"),
    }
    result: dict[str, tuple[int, str]] = {}
    for label, path in artifacts.items():
        if not path.is_file() or path.stat().st_size == 0:
            raise ProjectionError(f"candidate artifact missing/empty: {path}")
        try:
            relative = path.relative_to(ROOT).as_posix()
        except ValueError as error:
            raise ProjectionError("candidate artifacts must be inside worker checkout") from error
        if run(["git", "check-ignore", "-q", "--", relative], ROOT, False).returncode:
            raise ProjectionError(f"candidate artifact is not ignored: {relative}")
        if run(["git", "ls-files", "--", relative], ROOT).stdout.strip():
            raise ProjectionError(f"candidate artifact is tracked: {relative}")
        result[label] = (path.stat().st_size, sha(path))

    payload = json.loads(artifacts["json"].read_text(encoding="utf-8"))
    declarations = payload.get("declarations", {})
    edges = declarations.get("edge_counts", {})
    actual = {
        "format_version": declarations.get("format_version"),
        "declaration_count": declarations.get("declaration_count"),
        "signature_edges": edges.get("signature"),
        "body_edges": edges.get("body_or_proof"),
        "union_edges": edges.get("union"),
    }
    if actual != EXPECTED_GLOBAL:
        raise ProjectionError(f"candidate global totals differ: {actual}")
    if actual["signature_edges"] + actual["body_edges"] != 649_259:
        raise ProjectionError("candidate typed-edge total differs")
    return result


def verify_projection_graph(path: Path) -> None:
    counts = Counter()
    union: set[tuple[str, str]] = set()
    with gzip.open(path, "rt", encoding="utf-8", newline="") as stream:
        first = stream.readline()
        if first != "format\t2\n":
            raise ProjectionError("P0004 graph format differs")
        for line in stream:
            fields = line.rstrip("\n").split("\t")
            counts[fields[0]] += 1
            if fields[0] == "edge":
                if len(fields) != 4:
                    raise ProjectionError("malformed P0004 edge row")
                counts[fields[1]] += 1
                union.add((fields[2], fields[3]))
    if counts["declaration"] != 34 or counts["signature"] != 80 or counts[
        "body"] != 133 or len(union) != 139:
        raise ProjectionError(
            f"P0004 graph counts differ: declarations={counts['declaration']}, "
            f"signature={counts['signature']}, body={counts['body']}, "
            f"union={len(union)}"
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("candidate", type=Path)
    parser.add_argument("--control-root", type=Path, default=default_control())
    args = parser.parse_args()
    candidate = args.candidate.resolve()
    control = args.control_root.resolve()
    artifacts = candidate_artifacts(candidate)

    if run(["git", "rev-parse", "HEAD"], control).stdout.strip() != CONTROL_SHA:
        raise ProjectionError("control checkout is not exact active-control commit")
    if run(["git", "status", "--porcelain", "--untracked-files=all"], control).stdout.strip():
        raise ProjectionError("control checkout is not clean")

    branch = json.loads((control / B_PATH).read_text(encoding="utf-8"))
    projection = json.loads((control / P_PATH).read_text(encoding="utf-8"))
    if not (
        branch["branch_id"] == "B0004"
        and branch["wave_id"] == "R12"
        and branch["status"] == "active"
        and branch["operator_ids"] == ["codex-local"]
        and branch["base_sha"] == BASE
        and branch["baseline_projection_id"] == "P0004"
    ):
        raise ProjectionError("B0004 authority differs")
    if not (
        projection["projection_id"] == "P0004"
        and projection["status"] == "active"
        and projection["expected_counts"] == {
            "body_edges": 133, "declarations": 34,
            "signature_edges": 80, "union_edges": 139,
        }
    ):
        raise ProjectionError("P0004 authority differs")

    projection_path = control / projection["projection_graph"]["path"]
    private_path = control / PHASE / "branches/B0004-private-normalization.tsv"
    checker = control / projection["checker"]["artifact"]["path"]
    if sha(projection_path) != PROJECTION_SHA:
        raise ProjectionError("P0004 graph hash differs")
    if sha(private_path) != PRIVATE_SHA:
        raise ProjectionError("private-map hash differs")
    if sha(checker) != CHECKER_SHA:
        raise ProjectionError("projection-checker hash differs")
    verify_projection_graph(projection_path)

    recorded = list(projection["checker"]["arguments"])
    placeholder = "--candidate=<candidate-format2.tsv>"
    if (
        len(recorded) != 14
        or recorded.count(placeholder) != 1
        or sum(item.startswith("--allow-module=") for item in recorded) != 3
        or sum(item.startswith("--allow-prefix=") for item in recorded) != 6
    ):
        raise ProjectionError("recorded checker arguments differ")
    replay = [
        f"--candidate={candidate}" if argument == placeholder else argument
        for argument in recorded
    ]
    for before, after in zip(recorded, replay, strict=True):
        if before != placeholder and before != after:
            raise ProjectionError("non-candidate checker argument changed")

    result = run([sys.executable, "-B", str(checker), *replay], control)
    expected_output = [
        "phase projection contract passed",
        f"projection_sha256: {PROJECTION_SHA}",
        f"candidate_sha256: {artifacts['tsv'][1]}",
        "selected_declarations: 34",
        "relocated_declarations: 34",
        "signature_edges: 80",
        "body_edges: 133",
        "candidate_declarations_scanned: 56903",
        "candidate_edges_scanned: 649259",
        "allowed_exact_modules: 3",
        "allowed_prefixes: 6",
        f"private_map_sha256: {PRIVATE_SHA}",
        "private_normalizations: 0",
    ]
    if result.stdout.splitlines() != expected_output:
        raise ProjectionError("P0004 checker output differs:\n" + result.stdout)
    print(result.stdout, end="")
    print(
        "R12 P0004 replay OK: arguments=14; declarations=34; relocated=34; "
        "signature=80; body=133; union=139"
    )
    for label in ("tsv", "json", "md"):
        size, digest = artifacts[label]
        print(f"candidate_{label}_bytes: {size}")
        print(f"candidate_{label}_sha256: {digest}")


if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, ValueError, json.JSONDecodeError, ProjectionError) as error:
        print(f"R12 projection replay failed: {error}", file=sys.stderr)
        raise SystemExit(2)
