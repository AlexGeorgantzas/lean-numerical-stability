#!/usr/bin/env python3
"""Replay the exact five-path R01 integrator request in a disposable C0000 clone."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
DELIVERY = ROOT / "docs/architecture/deliveries/R01"
BASE = "b1b18772d80185ec08f49c818919558645c330a1"
PATCH = DELIVERY / "INTEGRATOR_REQUEST.patch"
MANIFEST = DELIVERY / "INTEGRATOR_POSTIMAGES.tsv"
PATCH_SIZE = 7033
PATCH_SHA256 = "E5A8F2C07CFE899B3F6B9C486989A92FF94CE99E16EF104278D52BADD0B8FA8C"
IMPORT_RE = re.compile(r"(?m)^import\s+([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\s*$")
OWNERS = {
    "NumStability.Algorithms.StationaryIteration",
    "NumStability.Algorithms.StationaryIterationDrazin",
    "NumStability.Algorithms.StationaryIterationRounded",
    "NumStability.Algorithms.StationaryIterationSemiconvergent",
    "NumStability.Algorithms.StationaryIterationSemiconvergentExistence",
    "NumStability.Analysis.SemiconvergentBlockFormExists",
    "NumStability.Analysis.SemiconvergentExistenceComplete",
    "NumStability.Analysis.SemiconvergentExistenceFull",
    "NumStability.Analysis.SemiconvergentLimitGeneral",
    "NumStability.Analysis.SemiconvergentRealSpectrumComplete",
    "NumStability.Source.Higham.Chapter17.Equation08",
    "NumStability.Source.Higham.Chapter17.Equation12",
    "NumStability.Source.Higham.Chapter17.Equation15",
    "NumStability.Source.Higham.Chapter17.Equation16",
    "NumStability.Source.Higham.Chapter17.Equation17",
    "NumStability.Source.Higham.Chapter17.Equation20",
}
CANONICAL_PREFIXES = (
    "NumStability.Algorithms.LinearSystems.Iterative.Stationary.Semiconvergence.",
    "NumStability.Analysis.LinearOperators.MatrixPowers.Semiconvergence.",
    "NumStability.Source.Higham.Chapter17.Results.",
)


class ReplayError(RuntimeError):
    pass


def run(args: list[str], cwd: Path, *, capture: bool = True) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        args, cwd=cwd, text=True,
        stdout=subprocess.PIPE if capture else None,
        stderr=subprocess.STDOUT if capture else None,
    )
    if result.returncode:
        raise ReplayError((result.stdout or "") + f"command failed: {' '.join(args)}")
    return result


def git(repo: Path, *args: str) -> str:
    return run(["git", *args], repo).stdout


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


def manifest() -> list[dict[str, str]]:
    with MANIFEST.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.DictReader(stream, delimiter="\t"))
    if len(rows) != 5 or len({row["path"] for row in rows}) != 5:
        raise ReplayError("integrator postimage manifest differs")
    return rows


def verify_request(rows: list[dict[str, str]]) -> None:
    if PATCH.stat().st_size != PATCH_SIZE or sha256_bytes(PATCH.read_bytes()) != PATCH_SHA256:
        raise ReplayError("integrator request patch bytes differ")
    paths = {
        match.group(1)
        for match in re.finditer(r"(?m)^diff --git a/(.+?) b/\1$", PATCH.read_text(encoding="utf-8"))
    }
    expected = {row["path"] for row in rows}
    if paths != expected:
        raise ReplayError(f"request path roster differs: {sorted(paths ^ expected)}")
    for row in rows:
        oid = git(ROOT, "rev-parse", f"{BASE}:{row['path']}").strip()
        if oid != row["preimage_blob_oid"]:
            raise ReplayError(f"C0000 blob preimage differs: {row['path']}")
        payload = subprocess.check_output(["git", "show", f"{BASE}:{row['path']}"], cwd=ROOT)
        if sha256_bytes(payload) != row["preimage_sha256"]:
            raise ReplayError(f"C0000 SHA-256 preimage differs: {row['path']}")


def changed_paths(repo: Path) -> set[str]:
    return {
        line[3:].replace("\\", "/")
        for line in git(repo, "status", "--porcelain", "--untracked-files=all").splitlines()
    }


def worker_changed_paths() -> set[str]:
    result = {
        line.replace("\\", "/")
        for line in git(ROOT, "diff", "--name-only", BASE, "--").splitlines()
    }
    result.update(
        line.replace("\\", "/")
        for line in git(ROOT, "ls-files", "--others", "--exclude-standard").splitlines()
    )
    return result


def overlay_worker(clone: Path) -> None:
    for relative in sorted(worker_changed_paths()):
        if not relative.startswith(("NumStability/", "NumStabilityTest/")):
            continue
        source = ROOT / relative
        if not source.is_file():
            raise ReplayError(f"worker overlay source missing: {relative}")
        target = clone / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)


def merge_imports(path: Path, additions: set[str]) -> None:
    lines = path.read_text(encoding="utf-8-sig").splitlines()
    imports = {
        line.removeprefix("import ")
        for line in lines
        if line.startswith("import ")
    } | additions
    body = [line for line in lines if not line.startswith("import ")]
    while body and not body[0]:
        body.pop(0)
    payload = "\n".join(
        f"import {module}" for module in sorted(imports, key=str.casefold)
    ) + "\n"
    if body:
        payload += "\n" + "\n".join(body) + "\n"
    path.write_text(payload, encoding="utf-8", newline="\n")


def write_import_aggregate(path: Path, modules: set[str], title: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = "\n".join(
        f"import {module}" for module in sorted(modules, key=str.casefold)
    )
    path.write_text(
        payload + f"\n\n/-!\n# {title}\n\n"
        "Declaration-free integrator-owned acceptance aggregate for R01.\n-/\n",
        encoding="utf-8",
        newline="\n",
    )


def patch_acceptance_wiring(clone: Path) -> set[str]:
    """Simulate routine shared acceptance wiring outside the frozen five-path R0001."""
    changed: set[str] = set()
    family_wiring = {
        "NumStability/Algorithms/LinearSystems.lean": {
            "NumStability.Algorithms.LinearSystems.Iterative.Stationary.Semiconvergence.All"
        },
        "NumStability/Analysis/LinearOperators.lean": {
            "NumStability.Analysis.LinearOperators.MatrixPowers.Semiconvergence.All"
        },
    }
    for relative, additions in family_wiring.items():
        merge_imports(clone / relative, additions)
        changed.add(relative)

    with (DELIVERY / "TEST_MATRIX.tsv").open(encoding="utf-8", newline="") as stream:
        tests = {row["test_module"] for row in csv.DictReader(stream, delimiter="\t")}
    test_aggregate = "NumStabilityTest/Reorganization/R01.lean"
    write_import_aggregate(
        clone / test_aggregate, tests, "R01 reorganization tests"
    )
    merge_imports(
        clone / "NumStabilityTest.lean",
        {"NumStabilityTest.Reorganization.R01"},
    )
    changed.update({test_aggregate, "NumStabilityTest.lean"})

    with (DELIVERY / "DECLARATION_ROUTES.tsv").open(
        encoding="utf-8", newline=""
    ) as stream:
        routes = list(csv.DictReader(stream, delimiter="\t"))
    by_owner: dict[str, list[str]] = {}
    for row in routes:
        by_owner.setdefault(row["baseline_owner_module"], [])
        if row["destination_module"] not in by_owner[row["baseline_owner_module"]]:
            by_owner[row["baseline_owner_module"]].append(row["destination_module"])

    tiers_path = clone / "docs/architecture/tiers.json"
    tiers = json.loads(tiers_path.read_text(encoding="utf-8"))
    for owner in by_owner:
        tiers["exact"][owner] = "compatibility"
    for aggregate in (
        "NumStability.Algorithms.LinearSystems.Iterative.Stationary.Semiconvergence.All",
        "NumStability.Analysis.LinearOperators.MatrixPowers.Semiconvergence.All",
        "NumStability.Source.Higham.Chapter17.Results.All",
        "NumStability.Source.Higham.Chapter17.Results.Series",
    ):
        tiers["exact"][aggregate] = "aggregate"
    wanted_prefixes = (
        {
            "prefix": "NumStability.Algorithms.LinearSystems.Iterative.Stationary.Semiconvergence.",
            "tier": "reusable",
        },
        {
            "prefix": "NumStability.Analysis.LinearOperators.MatrixPowers.Semiconvergence.",
            "tier": "reusable",
        },
        {
            "prefix": "NumStability.Source.Higham.Chapter17.Results.",
            "tier": "source",
        },
    )
    for item in wanted_prefixes:
        if item not in tiers["prefixes"]:
            tiers["prefixes"].append(item)
    tiers["exact"] = dict(sorted(tiers["exact"].items(), key=lambda item: item[0].casefold()))
    tiers["prefixes"] = sorted(tiers["prefixes"], key=lambda item: item["prefix"].casefold())
    tiers_path.write_text(
        json.dumps(tiers, indent=2) + "\n", encoding="utf-8", newline="\n"
    )
    changed.add("docs/architecture/tiers.json")

    layout_path = clone / "docs/architecture/layout-exceptions.json"
    layout = json.loads(layout_path.read_text(encoding="utf-8"))
    legacy = layout["legacy"]
    owner_set = set(by_owner)
    for key in (
        "unclassified_modules",
        "missing_module_docstrings",
        "mixed_modules",
        "noncanonical_modules",
        "declaration_bearing_umbrellas",
    ):
        legacy[key] = sorted(set(legacy.get(key, [])) - owner_set, key=str.casefold)
    layout_path.write_text(
        json.dumps(layout, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    changed.add("docs/architecture/layout-exceptions.json")

    compatibility_path = clone / "docs/architecture/COMPATIBILITY.md"
    compatibility = compatibility_path.read_text(encoding="utf-8")

    def compatibility_row(module: str) -> str:
        imports = IMPORT_RE.findall(
            (clone / Path(*module.split(".")).with_suffix(".lean")).read_text(
                encoding="utf-8-sig"
            )
        )
        canonical = ", ".join(f"`{target}`" for target in imports)
        return f"| `{module}` | {canonical} |"

    rows = [compatibility_row(owner) for owner in sorted(by_owner, key=str.casefold)]
    marker = "\n## Removal rule"
    if marker not in compatibility:
        raise ReplayError("compatibility policy insertion marker missing")
    compatibility = compatibility.replace(
        marker,
        "\n\n" + "\n".join(rows) + marker,
        1,
    )
    series = "NumStability.Algorithms.StationaryIterationSeries"
    series_pattern = re.compile(
        rf"(?m)^\| `{re.escape(series)}` \|.*\|$"
    )
    compatibility, count = series_pattern.subn(
        compatibility_row(series), compatibility, count=1
    )
    if count != 1:
        raise ReplayError("StationaryIterationSeries compatibility row missing")
    compatibility_path.write_text(
        compatibility, encoding="utf-8", newline="\n"
    )
    changed.add("docs/architecture/COMPATIBILITY.md")
    return changed


def import_graph(repo: Path) -> tuple[dict[str, Path], dict[str, set[str]]]:
    files = {
        ".".join(path.relative_to(repo).with_suffix("").parts): path
        for path in (repo / "NumStability").rglob("*.lean")
    }
    graph = {
        module: set(IMPORT_RE.findall(path.read_text(encoding="utf-8-sig")))
        for module, path in files.items()
    }
    missing = sorted(
        target for targets in graph.values() for target in targets
        if target.startswith("NumStability.") and target not in files
    )
    if missing:
        raise ReplayError(f"postimage unresolved import: {missing[0]}")
    return files, graph


def closure(graph: dict[str, set[str]], root: str) -> set[str]:
    seen: set[str] = set()
    todo = [root]
    while todo:
        for target in graph.get(todo.pop(), set()):
            if target not in seen:
                seen.add(target)
                todo.append(target)
    return seen


def verify_overlay(clone: Path, rows: list[dict[str, str]]) -> None:
    files, graph = import_graph(clone)
    canonical = {module for module in files if module.startswith(CANONICAL_PREFIXES)}
    for module in canonical:
        leaked = closure(graph, module) & OWNERS
        if leaked:
            raise ReplayError(f"canonical-to-historical postimage reachability: {module}")
    reusable = {
        module for module in canonical
        if module.startswith((
            "NumStability.Algorithms.LinearSystems.Iterative.Stationary.Semiconvergence.",
            "NumStability.Analysis.LinearOperators.MatrixPowers.Semiconvergence.",
        ))
    }
    for module in reusable:
        source = sorted(x for x in closure(graph, module) if x.startswith("NumStability.Source."))
        if source:
            raise ReplayError(f"reusable-to-Source postimage reachability: {module} -> {source[0]}")

    expected_imports = {
        "NumStability.Algorithms": {
            "NumStability.Algorithms.LinearSystems.Iterative.Stationary.Semiconvergence.All",
            "NumStability.Analysis.LinearOperators.MatrixPowers.Semiconvergence.All",
            "NumStability.Source.Higham.Chapter17.Results.All",
        },
        "NumStability.Algorithms.StationaryIterationSeries": {
            "NumStability.Source.Higham.Chapter17.Results.Series",
        },
        "NumStability.Analysis": {
            "NumStability.Analysis.LinearOperators.MatrixPowers.Semiconvergence.All",
        },
        "NumStability.Source.Higham.Chapter17": {
            "NumStability.Source.Higham.Chapter17.Results.All",
        },
        "NumStability.Source.Higham.Chapter17.Equation22": {
            "NumStability.Analysis.LinearOperators.MatrixPowers.Semiconvergence.Limits.General",
        },
    }
    for module, required in expected_imports.items():
        if not required <= graph[module]:
            raise ReplayError(f"protected consumer postimage import missing: {module}")
    for row in rows:
        actual = sha256_bytes((clone / row["path"]).read_bytes())
        if actual != row["postimage_sha256"]:
            raise ReplayError(f"protected consumer postimage hash differs after overlay: {row['path']}")


def full_gates(clone: Path) -> None:
    acceptance_paths = patch_acceptance_wiring(clone)
    print(
        "R01 disposable acceptance wiring: "
        f"{len(acceptance_paths)} integrator-owned paths outside frozen R0001"
    )
    for tool in ("check_layout.py", "check_compatibility.py", "check_provenance.py"):
        result = run([sys.executable, "-B", f"tools/architecture/{tool}"], clone)
        print(result.stdout, end="")
    result = run([
        sys.executable, "-B", "tools/architecture/generate_baseline.py",
        "--skip-declarations", "--strict-source",
        "--output-dir", "benchmark-results/R01-integrator-strict-source",
        "--name", "R01-integrator-strict-source",
    ], clone)
    print(result.stdout, end="")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--full", action="store_true")
    args = parser.parse_args()
    rows = manifest()
    verify_request(rows)
    expected_paths = {row["path"] for row in rows}
    with tempfile.TemporaryDirectory(prefix="R01-integrator-") as raw:
        clone = Path(raw) / "repo"
        run(["git", "clone", "--shared", "--no-checkout", str(ROOT), str(clone)], ROOT)
        run(["git", "checkout", "--detach", BASE], clone)
        run(["git", "apply", "--check", str(PATCH)], clone)
        run(["git", "apply", str(PATCH)], clone)
        if changed_paths(clone) != expected_paths:
            raise ReplayError("forward replay changed-path roster differs")
        for row in rows:
            actual = sha256_bytes((clone / row["path"]).read_bytes())
            if actual != row["postimage_sha256"]:
                raise ReplayError(f"forward postimage differs: {row['path']}")
        run(["git", "apply", "--reverse", "--check", str(PATCH)], clone)
        run(["git", "apply", "--reverse", str(PATCH)], clone)
        if changed_paths(clone):
            raise ReplayError("reverse replay did not restore exact C0000")
        run(["git", "apply", str(PATCH)], clone)
        overlay_worker(clone)
        verify_overlay(clone, rows)
        if args.full:
            full_gates(clone)
    print(
        "R01 request replay passed: exact C0000 preimages, paths=5, "
        f"patch_bytes={PATCH_SIZE}, patch_sha256={PATCH_SHA256}, "
        "forward=PASS, reverse=PASS, canonical-to-historical=0, reusable-to-Source=0"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ReplayError, UnicodeError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
