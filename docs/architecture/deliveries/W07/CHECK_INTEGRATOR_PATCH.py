#!/usr/bin/env python3
"""Replay the exact forbidden W07 integrator edits in a disposable clone."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[4]
BASE = "9eb534a06db267203c2b9b88227edd44fc64f5db"

SHARED_BLOBS = {
    "NumStability/Algorithms/LinearSystems.lean": "fd3b04b44f419223d6470c2609552f63e42868fd",
    "NumStability/Analysis/SemiconvergentBlockFormExists.lean": "02d24da8e5f17980651158048dcdbe3eebda3cef",
    "NumStability/Analysis/SemiconvergentExistenceComplete.lean": "175df8df8c72b4588bb120e444c0aea499ab85b3",
    "NumStability/Analysis/SemiconvergentExistenceFull.lean": "969c676d52f7b3fa2fe79da35df828ab3ff38321",
    "NumStability/Analysis/SemiconvergentLimitGeneral.lean": "e84fd5893d97fc6bdb3e34b9e1374733fcdd600d",
    "NumStability/Analysis/SemiconvergentRealSpectrumComplete.lean": "86ac278b764a1205d4df25268e7a8eec4f05f8bd",
    "NumStability/Source/Higham/Chapter17.lean": "be9b42ad5f8149dbc409e8c8fa6467443cf9da0e",
    "NumStability/Source/Higham/Chapter17/Equation08.lean": "8a6b464983a928162efc0c34fdff9941733585fc",
    "NumStability/Source/Higham/Chapter17/Equation12.lean": "14f8f1dfe120da42614623f3b2cd14b613fb409c",
    "NumStability/Source/Higham/Chapter17/Equation15.lean": "660a177e7eec6ee8fc36a7a4a2829a4d9b48f6fb",
    "NumStability/Source/Higham/Chapter17/Equation16.lean": "c03b252cd0349d5f0b232051730c3c3b7134bfa5",
    "NumStability/Source/Higham/Chapter17/Equation17.lean": "d4cd7c7f4f3441e960c1c7f65f18ef99e60a7732",
    "NumStability/Source/Higham/Chapter17/Equation20.lean": "95250de7f42e646a03150380b313ee31939b2e5d",
    "NumStabilityTest.lean": "a3e450a3790c414dfee8f2c6eb8f1fee7e9cec74",
    "NumStabilityTest/Reorganization/W06/Focused/ProtectedW07.lean": "9055c6cb9a48a0c227d2c0031d27c42a155d8b87",
    "docs/architecture/COMPATIBILITY.md": "3b95fff399efd299540efcc53ae99cacced95613",
    "docs/architecture/layout-exceptions.json": "bbedd2a796aa7b003f89193e746599140fb03524",
    "docs/architecture/tiers.json": "c1afc0ad364fc908364114bfd63c5e0a2058baee",
}

OWNERS = (
    "NumStability/Algorithms/StationaryIteration.lean",
    "NumStability/Algorithms/StationaryIterationDrazin.lean",
    "NumStability/Algorithms/StationaryIterationRounded.lean",
    "NumStability/Algorithms/StationaryIterationSemiconvergent.lean",
    "NumStability/Algorithms/StationaryIterationSemiconvergentExistence.lean",
)

OVERLAY_PREFIXES = (
    "NumStability/Algorithms/LinearSystems/Iterative/Stationary/",
    "NumStability/Source/Higham/Chapter17/Equation01/",
    "NumStability/Source/Higham/Chapter17/Equation02/",
    "NumStability/Source/Higham/Chapter17/Equation03/",
    "NumStability/Source/Higham/Chapter17/Equation04/",
    "NumStability/Source/Higham/Chapter17/Equation05/",
    "NumStability/Source/Higham/Chapter17/Equation06/",
    "NumStability/Source/Higham/Chapter17/Equation07/",
    "NumStability/Source/Higham/Chapter17/Equation08/",
    "NumStability/Source/Higham/Chapter17/Equation09/",
    "NumStability/Source/Higham/Chapter17/Equation10/",
    "NumStability/Source/Higham/Chapter17/Equation12/",
    "NumStability/Source/Higham/Chapter17/Equation13/",
    "NumStability/Source/Higham/Chapter17/Equation15/",
    "NumStability/Source/Higham/Chapter17/Equation16/",
    "NumStability/Source/Higham/Chapter17/Equation17/",
    "NumStability/Source/Higham/Chapter17/Equation18/",
    "NumStability/Source/Higham/Chapter17/Equation19/",
    "NumStability/Source/Higham/Chapter17/Equation20/",
    "NumStability/Source/Higham/Chapter17/Equation21/",
    "NumStability/Source/Higham/Chapter17/Equation27/",
    "NumStability/Source/Higham/Chapter17/Equation28/",
    "NumStability/Source/Higham/Chapter17/Equation29/",
    "NumStability/Source/Higham/Chapter17/Equation33/",
    "NumStability/Source/Higham/Chapter17/Section02/",
    "NumStability/Source/Higham/Chapter17/Section04/",
    "NumStabilityTest/Reorganization/W07/",
)

HISTORICAL_MIXED = {
    "NumStability.Algorithms.StationaryIteration",
    "NumStability.Algorithms.StationaryIterationDrazin",
    "NumStability.Algorithms.StationaryIterationRounded",
    "NumStability.Algorithms.StationaryIterationSemiconvergent",
    "NumStability.Algorithms.StationaryIterationSemiconvergentExistence",
}

ANALYSIS_MIXED = {
    "NumStability.Analysis.SemiconvergentBlockFormExists",
    "NumStability.Analysis.SemiconvergentExistenceComplete",
    "NumStability.Analysis.SemiconvergentExistenceFull",
    "NumStability.Analysis.SemiconvergentLimitGeneral",
    "NumStability.Analysis.SemiconvergentRealSpectrumComplete",
}

ALL_MIXED = HISTORICAL_MIXED | ANALYSIS_MIXED

DECLARATION_UMBRELLAS = {
    "NumStability.Source.Higham.Chapter17.Equation08",
    "NumStability.Source.Higham.Chapter17.Equation12",
    "NumStability.Source.Higham.Chapter17.Equation15",
    "NumStability.Source.Higham.Chapter17.Equation16",
    "NumStability.Source.Higham.Chapter17.Equation17",
    "NumStability.Source.Higham.Chapter17.Equation20",
}


def run(args: list[str], cwd: Path, *, capture: bool = False) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        args,
        cwd=cwd,
        check=True,
        text=True,
        stdout=subprocess.PIPE if capture else None,
        stderr=subprocess.STDOUT if capture else None,
    )


def git_blob(path: str) -> str:
    result = run(["git", "hash-object", "--", path], ROOT, capture=True)
    return result.stdout.strip()


def verify_shared_preimage() -> None:
    for path, expected in SHARED_BLOBS.items():
        actual = git_blob(path)
        if actual != expected:
            raise RuntimeError(f"shared preimage changed: {path}: {actual} != {expected}")
    aggregate = ROOT / "NumStabilityTest/Reorganization/W07.lean"
    if aggregate.exists():
        raise RuntimeError(f"shared preimage should be absent: {aggregate.relative_to(ROOT)}")


def import_names(path: Path) -> tuple[list[str], list[str]]:
    lines = path.read_text(encoding="utf-8-sig").splitlines()
    imports = [line.removeprefix("import ") for line in lines if line.startswith("import ")]
    body = [line for line in lines if not line.startswith("import ")]
    while body and not body[0]:
        body.pop(0)
    return imports, body


def write_imports(path: Path, additions: set[str]) -> None:
    imports, body = import_names(path)
    merged = sorted(set(imports) | additions, key=str.casefold)
    text = "\n".join(f"import {name}" for name in merged) + "\n"
    if body:
        text += "\n" + "\n".join(body) + "\n"
    path.write_text(text, encoding="utf-8")


def overlay_w07(clone: Path) -> None:
    paths = set(OWNERS)
    for prefix in OVERLAY_PREFIXES:
        source = ROOT / prefix
        if source.is_dir():
            paths.update(path.relative_to(ROOT).as_posix() for path in source.rglob("*.lean"))
    for relative in sorted(paths):
        source = ROOT / relative
        target = clone / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)


def route_modules() -> tuple[set[str], set[str]]:
    data = json.loads((ROOT / "docs/architecture/deliveries/W07/ROUTE_SUMMARY.json").read_text())
    modules = set(data["route_declaration_counts"])
    reusable = {
        name
        for name in modules
        if name.startswith("NumStability.Algorithms.LinearSystems.Iterative.Stationary.")
    }
    source = {name for name in modules if name.startswith("NumStability.Source.Higham.Chapter17.")}
    if len(reusable) != 9 or len(source) != 25:
        raise RuntimeError(f"unexpected route module counts: {len(reusable)} reusable, {len(source)} source")
    return reusable, source


def test_modules() -> set[str]:
    path = ROOT / "docs/architecture/deliveries/W07/TEST_MATRIX.tsv"
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.DictReader(stream, delimiter="\t"))
    modules = {row["test_module"] for row in rows}
    if len(rows) != 48 or len(modules) != 48:
        raise RuntimeError("TEST_MATRIX.tsv must contain 48 unique tests")
    return modules


def patch_shared(clone: Path) -> None:
    reusable, source = route_modules()

    write_imports(clone / "NumStability/Algorithms/LinearSystems.lean", reusable)
    write_imports(clone / "NumStability/Source/Higham/Chapter17.lean", source)

    aggregate = clone / "NumStabilityTest/Reorganization/W07.lean"
    aggregate.parent.mkdir(parents=True, exist_ok=True)
    imports = sorted(test_modules(), key=str.casefold)
    aggregate.write_text(
        "\n".join(f"import {name}" for name in imports)
        + "\n\n/-!\n# W07 reorganization tests\n\n"
        + "Declaration-free aggregate for the complete 48-module W07 delivery test matrix.\n-/\n",
        encoding="utf-8",
    )
    write_imports(clone / "NumStabilityTest.lean", {"NumStabilityTest.Reorganization.W07"})

    tiers_path = clone / "docs/architecture/tiers.json"
    tiers = json.loads(tiers_path.read_text(encoding="utf-8"))
    exact = tiers["exact"]
    for module in sorted(reusable):
        if module in exact:
            raise RuntimeError(f"new reusable module unexpectedly classified at C0007: {module}")
        exact[module] = "reusable"
    for module in sorted(HISTORICAL_MIXED):
        if module in exact:
            raise RuntimeError(f"historical W07 owner unexpectedly classified at C0007: {module}")
        exact[module] = "mixed"
    for module in sorted(ANALYSIS_MIXED):
        if exact.get(module) != "reusable":
            raise RuntimeError(f"accepted semiconvergence tier differs at C0007: {module}")
        exact[module] = "mixed"
    tiers["exact"] = dict(sorted(exact.items(), key=lambda item: item[0].casefold()))
    tiers_path.write_text(json.dumps(tiers, indent=2) + "\n", encoding="utf-8")

    layout_path = clone / "docs/architecture/layout-exceptions.json"
    layout = json.loads(layout_path.read_text(encoding="utf-8"))
    legacy = layout["legacy"]
    expected_changes = {
        "unclassified_modules": (HISTORICAL_MIXED, set()),
        "mixed_modules": (set(), ALL_MIXED),
        "missing_module_docstrings": (HISTORICAL_MIXED, set()),
        "declaration_bearing_umbrellas": (set(), DECLARATION_UMBRELLAS),
    }
    for key, (removals, additions) in expected_changes.items():
        current = set(legacy[key])
        if not removals <= current:
            raise RuntimeError(f"missing expected {key} removals: {sorted(removals - current)}")
        if additions & current:
            raise RuntimeError(f"unexpected existing {key} additions: {sorted(additions & current)}")
        legacy[key] = sorted((current - removals) | additions)
    layout_path.write_text(json.dumps(layout, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def check() -> None:
    verify_shared_preimage()
    with tempfile.TemporaryDirectory(prefix="W07-integrator-") as raw:
        clone = Path(raw) / "repo"
        run(["git", "clone", "--shared", "--no-checkout", str(ROOT), str(clone)], ROOT)
        run(["git", "checkout", "--detach", BASE], clone)
        overlay_w07(clone)
        patch_shared(clone)
        run(["git", "add", "-A", "--"], clone)
        result = run([sys.executable, "-B", "tools/architecture/check_layout.py"], clone, capture=True)
        print(result.stdout, end="")
        if "Layout contract satisfied; no legacy debt increased." not in result.stdout:
            raise RuntimeError("disposable integrator replay did not satisfy layout contract")
        strict_relative = Path("benchmark-results/W07-integrator-strict-source")
        strict_dir = clone / strict_relative
        strict = run(
            [
                sys.executable,
                "-B",
                "tools/architecture/generate_baseline.py",
                "--skip-declarations",
                "--strict-source",
                "--output-dir",
                strict_relative.as_posix(),
                "--name",
                "W07-integrator-strict-source",
            ],
            clone,
            capture=True,
        )
        print(strict.stdout, end="")
        baseline = json.loads(
            (strict_dir / "W07-integrator-strict-source.json").read_text(encoding="utf-8")
        )
        tier_audit = baseline["source"]["tier_audit"]
        expected_tiers = {
            "aggregate": 361,
            "compatibility": 337,
            "internal": 2,
            "mixed": 19,
            "reusable": 483,
            "source": 979,
            "upstream": 5,
        }
        if (
            baseline["source"]["module_count"] != 2490
            or tier_audit["classified_module_count"] != 2186
            or tier_audit["unclassified_module_count"] != 304
            or tier_audit["module_counts_by_tier"] != expected_tiers
            or tier_audit["forbidden_reusable_edge_count"] != 0
            or tier_audit["forbidden_reusable_reachability_count"] != 0
            or tier_audit["reusable_to_source_edge_count"] != 0
            or tier_audit["reusable_to_source_reachability_count"] != 0
            or tier_audit["reusable_to_mixed_edge_count"] != 0
            or tier_audit["reusable_to_mixed_reachability_count"] != 0
            or len(tier_audit["reusable_entrypoints"]) != 21
        ):
            raise RuntimeError("disposable strict-source replay totals differ")
        print(
            "W07 integrator strict-source replay: 2490 modules, 2186 classified, "
            "304 unclassified, 19 mixed, 504 reusable roots, zero forbidden "
            "edges and reachable pairs.\n"
        )
    verify_shared_preimage()
    print("W07 integrator patch replay passed in a disposable clone; worker shared paths unchanged.")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    check()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
