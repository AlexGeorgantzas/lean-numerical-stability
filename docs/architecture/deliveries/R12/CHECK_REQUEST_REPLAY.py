#!/usr/bin/env python3
"""Replay exact R0004 forward/reverse and validate a disposable integrated state."""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
BASE = "117aa2bb7e61f41e1531a78452f9f7f6cd5b0771"
CONTROL = "5e075b947a63e84c784afecd00e1f130e21ea659"
PHASE = "docs/architecture/phases/2026-08-repository-reorganization-completion"
REQUEST_PATH = f"{PHASE}/requests/R0004.json"
PATCH_PATH = f"{PHASE}/requests/R0004.patch"
MANIFEST_PATH = f"{PHASE}/requests/R0004-postimages.tsv"
UNION_PATCH_PATH = f"{PHASE}/requests/R0003-R0004-union.patch"
UNION_MANIFEST_PATH = f"{PHASE}/requests/R0003-R0004-union-postimages.tsv"
UNION_REVIEW_PATH = f"{PHASE}/requests/R0003-R0004-union-review.md"
REQUEST_SHA = "C2AC9E79A9B6937C4E155A7A50D6E4A74F1FAE45CCF698995359B171941A1701"
PATCH_SHA = "449E350993D72F8A38A894CAF8DA245E06ED66D48A176EAE66EC65364F8D7BEB"
MANIFEST_SHA = "6CC237E4F8F99328DAA098591F3551A8FF6A452AFF908E81B37C4AFABCF8900E"
UNION_PATCH_SHA = "A6AB1307D19CBF2BEDDA37EAC8C68FFB405292B405E068908E6E4F15406A3E3B"
UNION_MANIFEST_SHA = "7279EDF6AF7277C2A4DD45286AEE97878EBFD025A89B240A6A644EE6FB665701"
UNION_REVIEW_SHA = "5B43D44B16496CAEACB14DE98FB4472B1698E18C3708B3BCD058C64C119F59DB"
PATH_LIST_SHA = "D9BB4F3E7F383A45EB84DF97977D766925CCFD2FF85508077CEFE6F8F952049A"
EXPECTED_PATHS = [
    "NumStabilityTest.lean",
    "docs/architecture/layout-exceptions.json",
    "docs/architecture/tiers.json",
]


class ReplayError(RuntimeError):
    pass


def run(
    args: list[str], cwd: Path, check: bool = True,
    capture: bool = True,
) -> subprocess.CompletedProcess[str]:
    environment = os.environ.copy()
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    result = subprocess.run(
        args, cwd=cwd, text=True, encoding="utf-8", errors="replace",
        stdout=subprocess.PIPE if capture else None,
        stderr=subprocess.STDOUT if capture else None,
        env=environment,
    )
    if check and result.returncode:
        raise ReplayError((result.stdout or "") + f"command failed: {' '.join(args)}")
    return result


def git(repo: Path, *args: str, check: bool = True) -> str:
    return run(["git", *args], repo, check).stdout


def git_bytes(commit: str, path: str) -> bytes:
    return subprocess.check_output(["git", "show", f"{commit}:{path}"], cwd=ROOT)


def sha(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


def emit(payload: str) -> None:
    """Write captured command output safely on legacy Windows consoles."""
    encoding = sys.stdout.encoding or "utf-8"
    safe = payload.encode(encoding, errors="replace").decode(encoding)
    print(safe, end="", flush=True)


def verify_controls() -> tuple[bytes, list[dict[str, str]]]:
    pins = {
        REQUEST_PATH: REQUEST_SHA,
        PATCH_PATH: PATCH_SHA,
        MANIFEST_PATH: MANIFEST_SHA,
        UNION_PATCH_PATH: UNION_PATCH_SHA,
        UNION_MANIFEST_PATH: UNION_MANIFEST_SHA,
        UNION_REVIEW_PATH: UNION_REVIEW_SHA,
    }
    for path, expected in pins.items():
        if sha(git_bytes(CONTROL, path)) != expected:
            raise ReplayError(f"control hash differs: {path}")
    request = json.loads(git_bytes(CONTROL, REQUEST_PATH))
    if not (
        request["request_id"] == "R0004"
        and request["status"] == "active"
        and request["target_base_sha"] == BASE
        and request["target_checkpoint_id"] == "C0001"
        and request["requester_id"] == "primary-human"
        and request["paths"] == EXPECTED_PATHS
    ):
        raise ReplayError("R0004 authority differs")
    path_payload = ("\n".join(EXPECTED_PATHS) + "\n").encode()
    if sha(path_payload) != PATH_LIST_SHA:
        raise ReplayError("R0004 path-list hash differs")
    rows = list(csv.DictReader(
        io.StringIO(git_bytes(CONTROL, MANIFEST_PATH).decode("utf-8")),
        delimiter="\t",
    ))
    if len(rows) != 3 or [row["path"] for row in rows] != EXPECTED_PATHS:
        raise ReplayError("R0004 postimage manifest differs")
    patch = git_bytes(CONTROL, PATCH_PATH)
    patch_paths = [
        match.group(1) for match in re.finditer(
            r"(?m)^diff --git a/(.+?) b/\1$", patch.decode("utf-8"))
    ]
    if patch_paths != EXPECTED_PATHS:
        raise ReplayError("R0004 patch path order differs")
    for row in rows:
        payload = git_bytes(BASE, row["path"])
        if git(ROOT, "rev-parse", f"{BASE}:{row['path']}").strip() != row[
            "preimage_blob_oid"]:
            raise ReplayError(f"preimage blob differs: {row['path']}")
        if sha(payload) != row["preimage_sha256"]:
            raise ReplayError(f"preimage SHA differs: {row['path']}")
    return patch, rows


def changed_paths(repo: Path) -> set[str]:
    paths = set()
    for line in git(repo, "status", "--porcelain=v1", "--untracked-files=all").splitlines():
        paths.add(line[3:].replace("\\", "/"))
    return paths


def worker_overlay_paths() -> list[str]:
    paths = {
        line.replace("\\", "/")
        for line in git(ROOT, "diff", "--name-only", "--no-renames", BASE, "--").splitlines()
    }
    paths.update(
        line.replace("\\", "/")
        for line in git(ROOT, "ls-files", "--others", "--exclude-standard").splitlines()
    )
    allowed = [
        path for path in paths
        if path.startswith("NumStability/")
        or path.startswith("NumStabilityTest/Reorganization/R12/")
    ]
    if len(allowed) != 36:
        raise ReplayError(f"worker production/test overlay count differs: {len(allowed)}")
    return sorted(allowed)


def overlay(repo: Path) -> None:
    for relative in worker_overlay_paths():
        source = ROOT / relative
        target = repo / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)


def verify_postimages(repo: Path, rows: list[dict[str, str]]) -> None:
    for row in rows:
        if sha((repo / row["path"]).read_bytes()) != row["postimage_sha256"]:
            raise ReplayError(f"R0004 postimage differs: {row['path']}")


def attach_build_cache(repo: Path) -> Path:
    source = ROOT / ".lake"
    junction = repo / ".lake"
    if not source.is_dir() or junction.exists():
        raise ReplayError("shared ignored Lake cache is unavailable")
    if os.name == "nt":
        result = run(
            ["cmd", "/c", "mklink", "/J", str(junction), str(source)],
            repo, capture=True,
        )
        if not junction.is_dir():
            raise ReplayError("failed to create disposable Lake-cache junction")
    else:
        os.symlink(source, junction, target_is_directory=True)
    return junction


def full_gates(repo: Path) -> None:
    compile_tools = """
from pathlib import Path
paths = [
    'tools/architecture/generate_baseline.py',
    'tools/architecture/check_compatibility.py',
    'tools/architecture/check_layout.py',
    'tools/architecture/check_phase.py',
    'tools/architecture/check_phase_projection.py',
    'tools/architecture/check_completion_phase_projection.py',
    'tools/architecture/check_completion_phase.py',
    'tools/architecture/check_provenance.py',
]
for raw in paths:
    path = Path(raw)
    compile(path.read_text(encoding='utf-8'), str(path), 'exec')
print(f'compiled {len(paths)} architecture tools without bytecode')
"""
    commands = [
        ("compile_tools", [sys.executable, "-B", "-c", compile_tools]),
        ("phase_self_test", [sys.executable, "-B",
         "tools/architecture/check_phase.py", "--self-test"]),
        ("phase_projection_self_test", [sys.executable, "-B",
         "tools/architecture/check_phase_projection.py", "--self-test"]),
        ("completion_projection_self_test", [sys.executable, "-B",
         "tools/architecture/check_completion_phase_projection.py", "--self-test"]),
        ("completion_self_test", [sys.executable, "-B",
         "tools/architecture/check_completion_phase.py", "--self-test"]),
        ("all_phases", [sys.executable, "-B",
         "tools/architecture/check_phase.py", "--all-phases"]),
        ("completion_phase", [sys.executable, "-B",
         "tools/architecture/check_completion_phase.py"]),
        ("layout", [sys.executable, "-B", "tools/architecture/check_layout.py"]),
        ("compatibility", [sys.executable, "-B",
         "tools/architecture/check_compatibility.py"]),
        ("provenance", [sys.executable, "-B",
         "tools/architecture/check_provenance.py"]),
        ("strict_source", [sys.executable, "-B",
         "tools/architecture/generate_baseline.py",
         "--skip-declarations", "--strict-source",
         "--output-dir", "benchmark-results/R12-integrated-strict-source",
         "--name", "source"]),
        ("library_and_tests", ["lake", "build", "NumStability", "NumStabilityTest"]),
        ("lake_test", ["lake", "test"]),
        ("staged_diff_check", ["git", "diff", "--cached", "--check"]),
    ]
    for name, command in commands:
        started = time.perf_counter()
        result = run(command, repo, check=False)
        seconds = time.perf_counter() - started
        matches = re.findall(r"Build completed successfully \((\d+) jobs?\)", result.stdout)
        jobs = int(matches[-1]) if matches else 0
        print(
            f"R12_INTEGRATED_GATE\t{name}\t{result.returncode}\t"
            f"{seconds:.3f}\t{jobs}", flush=True
        )
        emit(result.stdout)
        if result.returncode:
            raise ReplayError(f"integrated gate failed: {name}")


def verify_worker_layout_deferred() -> None:
    result = run(
        [sys.executable, "tools/architecture/check_layout.py"], ROOT,
        check=False,
    )
    errors = [line for line in result.stdout.splitlines() if line.startswith("error: ")]
    if result.returncode != 1 or len(errors) != 2:
        raise ReplayError(
            "worker layout failure is not exactly the two R0004-deferred findings:\n"
            + result.stdout
        )
    if not (
        errors[0].startswith("error: NumStabilityTest does not reach 27 test module(s): ")
        and "NumStabilityTest.Reorganization.R12.All" in errors[0]
        and errors[1] ==
        "error: stale declaration bearing umbrellas baseline; review the improvement "
        "and run --write-baseline: "
        "NumStability.Source.Higham.Chapter13.Equation23, "
        "NumStability.Source.Higham.Chapter13.Equation25, "
        "NumStability.Source.Higham.Chapter13.Table01"
    ):
        raise ReplayError("worker layout findings differ from exact R0004 deferrals")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--full", action="store_true")
    args = parser.parse_args()
    patch, rows = verify_controls()
    if args.full:
        verify_worker_layout_deferred()

    with tempfile.TemporaryDirectory(prefix="r12-r0004-") as temp:
        repo = Path(temp) / "integrated"
        run(["git", "clone", "--shared", "--no-checkout", str(ROOT), str(repo)], ROOT)
        run(["git", "checkout", "--detach", BASE], repo)
        patch_file = Path(temp) / "R0004.patch"
        patch_file.write_bytes(patch)

        run(["git", "apply", "--check", str(patch_file)], repo)
        run(["git", "apply", str(patch_file)], repo)
        if changed_paths(repo) != set(EXPECTED_PATHS):
            raise ReplayError("R0004 forward changed-path roster differs")
        verify_postimages(repo, rows)
        run(["git", "apply", "--reverse", "--check", str(patch_file)], repo)
        run(["git", "apply", "--reverse", str(patch_file)], repo)
        if git(repo, "status", "--porcelain=v1").strip():
            raise ReplayError("R0004 reverse replay did not restore clean C0001")

        run(["git", "checkout", "--detach", CONTROL], repo)
        for row in rows:
            if git(repo, "rev-parse", f"HEAD:{row['path']}").strip() != row[
                "preimage_blob_oid"]:
                raise ReplayError("active-control shared preimage differs")
        run(["git", "apply", "--check", str(patch_file)], repo)
        run(["git", "apply", str(patch_file)], repo)
        overlay(repo)
        integrated_paths = set(EXPECTED_PATHS) | set(worker_overlay_paths())
        if changed_paths(repo) != integrated_paths:
            raise ReplayError("integrated overlay changed-path roster differs")
        verify_postimages(repo, rows)
        junction: Path | None = None
        try:
            if args.full:
                junction = attach_build_cache(repo)
                run(["git", "add", "-A"], repo)
                full_gates(repo)
                if git(repo, "diff", "--name-only").strip():
                    raise ReplayError("integrated gates left unstaged tracked changes")
                if changed_paths(repo) != integrated_paths:
                    raise ReplayError("integrated gate end-state roster differs")
        finally:
            if junction is not None and junction.exists():
                os.rmdir(junction)

    print(
        "R0004 replay OK: 3 exact paths; forward/reverse C0001 replay; "
        "active-control integrated overlay" + ("; all full gates green" if args.full else "")
    )


if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, ValueError, json.JSONDecodeError, ReplayError) as error:
        print(f"R0004 replay failed: {error}", file=sys.stderr)
        raise SystemExit(2)
