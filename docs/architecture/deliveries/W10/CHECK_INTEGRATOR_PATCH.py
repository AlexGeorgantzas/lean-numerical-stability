#!/usr/bin/env python3
"""Replay the exact 14-path R0011 W10 integration contract in a disposable clone."""

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
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
BASE = "9eb534a06db267203c2b9b88227edd44fc64f5db"
IMPORT_RE = re.compile(r"(?m)^(?:public\s+|private\s+)?import\s+([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\s*$")
SHARED_BLOBS = {
    "NumStability/Algorithms/NormEstimation.lean": "4b0177b71c16ef1b56f43a34bb8d1b1fa705a0c2",
    "NumStability/Algorithms/NormEstimation/OneNorm/All.lean": "143df085a9ff19500ae64311662f7549dd461c61",
    "NumStability/Source/Higham.lean": "8e8fe02ca14854d7c9193cd3673c0150aa538bc9",
    "NumStabilityTest.lean": "a3e450a3790c414dfee8f2c6eb8f1fee7e9cec74",
    "docs/architecture/tiers.json": "c1afc0ad364fc908364114bfd63c5e0a2058baee",
    "docs/architecture/layout-exceptions.json": "bbedd2a796aa7b003f89193e746599140fb03524",
}
ABSENT = {
    "NumStability/Algorithms/NormEstimation/PNorm.lean",
    "NumStability/Algorithms/NormEstimation/PNorm/All.lean",
    "NumStability/Algorithms/NormEstimation/PNorm/Boyd.lean",
    "NumStability/Algorithms/NormEstimation/TwoNorm.lean",
    "NumStability/Algorithms/NormEstimation/TwoNorm/All.lean",
    "NumStability/Algorithms/NormEstimation/TwoNorm/Dixon.lean",
    "NumStability/Source/Higham/Chapter15.lean",
    "NumStabilityTest/Reorganization/W10.lean",
}
PATCH_PATH = ROOT / "docs/architecture/deliveries/W10/R0011.patch"
PATCH_SIZE = 34111
PATCH_SHA256 = "6AA9A9070BDA882DB9AA482D695F74CB15C9379BB8147B52F89BDB05CD4AA97C"


class PatchError(RuntimeError):
    pass


def run(args: list[str], cwd: Path, *, capture: bool = False) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(args, cwd=cwd, text=True, stdout=subprocess.PIPE if capture else None,
                            stderr=subprocess.STDOUT if capture else None)
    if result.returncode:
        raise PatchError((result.stdout or "") + f"command failed ({result.returncode}): {' '.join(args)}")
    return result


def git(repo: Path, *args: str) -> str:
    return run(["git", *args], repo, capture=True).stdout


def read_routes() -> tuple[list[dict[str, str]], set[str], set[str], set[str]]:
    with (ROOT / "docs/architecture/deliveries/W10/DECLARATION_ROUTES.tsv").open(encoding="utf-8", newline="") as stream:
        rows = list(csv.DictReader(stream, delimiter="\t"))
    owners = {r["owner_module"] for r in rows}
    reusable = {r["destination_module"] for r in rows if r["tier"] == "reusable"}
    source = {r["destination_module"] for r in rows if r["tier"] == "source"}
    if (len(rows), len(owners), len(reusable), len(source)) != (1029, 27, 49, 46):
        raise PatchError("route roster differs")
    return rows, owners, reusable, source


def verify_preimages() -> None:
    expected = dict(SHARED_BLOBS)
    tree = {}
    for line in git(ROOT, "ls-tree", "-r", BASE).splitlines():
        metadata, path = line.split("\t", 1)
        tree[path] = metadata.split()[2]
    for path, blob in expected.items():
        actual = tree.get(path)
        if actual != blob:
            raise PatchError(f"C0007 preimage differs: {path}: {actual} != {blob}")
    for path in ABSENT:
        if path in tree:
            raise PatchError(f"new aggregate existed at C0007: {path}")


def verify_patch() -> None:
    if not PATCH_PATH.is_file() or PATCH_PATH.stat().st_size != PATCH_SIZE:
        raise PatchError(f"R0011.patch missing or wrong size (expected {PATCH_SIZE})")
    digest = hashlib.sha256(PATCH_PATH.read_bytes()).hexdigest().upper()
    if digest != PATCH_SHA256:
        raise PatchError(f"R0011.patch hash differs: {digest}")
    paths = {
        match.group(1)
        for match in re.finditer(r"(?m)^diff --git a/(.+?) b/\1$", PATCH_PATH.read_text(encoding="utf-8"))
    }
    expected = set(SHARED_BLOBS) | ABSENT
    if paths != expected or len(paths) != 14:
        raise PatchError(f"R0011.patch path roster differs: {len(paths)} paths")


def exact_postimages(clone: Path, paths: set[str]) -> dict[str, bytes]:
    result: dict[str, bytes] = {}
    for relative in paths:
        path = clone / relative
        if not path.is_file():
            raise PatchError(f"R0011 postimage missing: {relative}")
        result[relative] = path.read_bytes()
    return result


def changed_paths(clone: Path) -> set[str]:
    paths = set()
    for line in git(clone, "status", "--porcelain", "--untracked-files=all").splitlines():
        paths.add(line[3:].replace("\\", "/"))
    return paths


def render_patch(clone: Path, paths: set[str]) -> bytes:
    new_paths = sorted(path for path in paths if path in ABSENT and (clone / path).is_file())
    if new_paths:
        run(["git", "add", "-N", "--", *new_paths], clone)
    result = subprocess.run(
        ["git", "diff", "--no-ext-diff", "--no-renames", "--binary", "--unified=0", "--", *sorted(paths)],
        cwd=clone, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    if result.returncode:
        raise PatchError(result.stderr.decode(errors="replace") or "git diff failed")
    return result.stdout


def write_import_file(path: Path, modules: set[str], title: str, description: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = "\n".join(f"import {m}" for m in sorted(modules, key=str.casefold))
    path.write_text(payload + f"\n\n/-!\n# {title}\n\n{description}\n-/\n", encoding="utf-8", newline="\n")


def merge_imports(path: Path, additions: set[str]) -> None:
    lines = path.read_text(encoding="utf-8-sig").splitlines()
    imports = {line.removeprefix("import ") for line in lines if line.startswith("import ")} | additions
    body = [line for line in lines if not line.startswith("import ")]
    while body and not body[0]: body.pop(0)
    payload = "\n".join(f"import {m}" for m in sorted(imports, key=str.casefold)) + "\n"
    if body: payload += "\n" + "\n".join(body) + "\n"
    path.write_text(payload, encoding="utf-8", newline="\n")


def overlay_worker(clone: Path) -> None:
    names = git(ROOT, "diff", "--name-only", BASE, "--", "NumStability").splitlines()
    for relative in names:
        source, target = ROOT / relative, clone / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)


def patch_aggregates(clone: Path, reusable: set[str], source: set[str]) -> None:
    one = {m for m in reusable if ".OneNorm." in m}
    pnorm = {m for m in reusable if ".PNorm." in m}
    boyd = {m for m in pnorm if ".PNorm.Boyd." in m}
    two = {m for m in reusable if ".TwoNorm." in m}
    if (len(one), len(pnorm), len(boyd), len(two)) != (5, 38, 20, 6):
        raise PatchError("aggregate leaf partition differs")
    merge_imports(clone / "NumStability/Algorithms/NormEstimation.lean", {
        "NumStability.Algorithms.NormEstimation.OneNorm",
        "NumStability.Algorithms.NormEstimation.PNorm",
        "NumStability.Algorithms.NormEstimation.TwoNorm",
    })
    merge_imports(clone / "NumStability/Algorithms/NormEstimation/OneNorm/All.lean", one | {
        "NumStability.Algorithms.NormEstimation.OneNorm.GeneralIndex"
    })
    write_import_file(clone / "NumStability/Algorithms/NormEstimation/PNorm.lean", {"NumStability.Algorithms.NormEstimation.PNorm.All"}, "Algorithms.NormEstimation.PNorm", "Declaration-free W10 discovery aggregate for reusable p-norm estimation.")
    write_import_file(clone / "NumStability/Algorithms/NormEstimation/PNorm/All.lean", (pnorm - boyd) | {"NumStability.Algorithms.NormEstimation.PNorm.Boyd"}, "Algorithms.NormEstimation.PNorm.All", "Reviewed W10 discovery entry point for the reusable p-norm estimation family.")
    write_import_file(clone / "NumStability/Algorithms/NormEstimation/PNorm/Boyd.lean", boyd, "Algorithms.NormEstimation.PNorm.Boyd", "Reviewed W10 discovery entry point for the reusable Boyd p-norm family.")
    write_import_file(clone / "NumStability/Algorithms/NormEstimation/TwoNorm.lean", {"NumStability.Algorithms.NormEstimation.TwoNorm.All"}, "Algorithms.NormEstimation.TwoNorm", "Declaration-free W10 discovery aggregate for reusable two-norm estimation.")
    write_import_file(clone / "NumStability/Algorithms/NormEstimation/TwoNorm/All.lean", {"NumStability.Algorithms.NormEstimation.TwoNorm.Dixon"}, "Algorithms.NormEstimation.TwoNorm.All", "Reviewed W10 discovery entry point for the reusable two-norm estimation family.")
    write_import_file(clone / "NumStability/Algorithms/NormEstimation/TwoNorm/Dixon.lean", two, "Algorithms.NormEstimation.TwoNorm.Dixon", "Reviewed W10 discovery entry point for the reusable Dixon two-norm family.")
    source_with_wrapper = source | {
        "NumStability.Source.Higham.Chapter15.Section01.ConditionNumbers.CondEstimation"
    }
    if len(source_with_wrapper) != 47:
        raise PatchError("Chapter 15 source discovery roster differs")
    write_import_file(clone / "NumStability/Source/Higham/Chapter15.lean", source_with_wrapper, "Higham Chapter 15 source correspondence", "Complete canonical entry point for the Chapter 15 source-correspondence leaves\ncurrently migrated into `NumStability.Source.Higham`.")
    merge_imports(clone / "NumStability/Source/Higham.lean", {"NumStability.Source.Higham.Chapter15"})
    with (ROOT / "docs/architecture/deliveries/W10/TEST_MATRIX.tsv").open(encoding="utf-8", newline="") as stream:
        tests = {row["test_module"] for row in csv.DictReader(stream, delimiter="\t")}
    write_import_file(clone / "NumStabilityTest/Reorganization/W10.lean", tests, "W10 reorganization tests", "Declaration-free aggregate for the complete W10 delivery test matrix.")
    merge_imports(clone / "NumStabilityTest.lean", {"NumStabilityTest.Reorganization.W10"})


def patch_controls(clone: Path, owners: set[str]) -> None:
    tiers_path = clone / "docs/architecture/tiers.json"
    tiers = json.loads(tiers_path.read_text(encoding="utf-8"))
    reusable_in_place = "NumStability.Algorithms.CondEstimation"
    additions = {module: "mixed" for module in owners - {reusable_in_place}}
    additions[reusable_in_place] = "reusable"
    for module in (
        "NumStability.Algorithms.NormEstimation.PNorm", "NumStability.Algorithms.NormEstimation.PNorm.All",
        "NumStability.Algorithms.NormEstimation.PNorm.Boyd", "NumStability.Algorithms.NormEstimation.TwoNorm",
        "NumStability.Algorithms.NormEstimation.TwoNorm.All", "NumStability.Algorithms.NormEstimation.TwoNorm.Dixon",
        "NumStability.Source.Higham.Chapter15",
    ):
        additions[module] = "aggregate"
    tiers["exact"].update(dict(sorted(additions.items(), key=lambda item: item[0].casefold())))
    tiers["prefixes"].append({"prefix": "NumStability.Algorithms.NormEstimation.", "tier": "reusable"})
    tiers_path.write_text(json.dumps(tiers, indent=2) + "\n", encoding="utf-8", newline="\n")
    layout_path = clone / "docs/architecture/layout-exceptions.json"
    layout = json.loads(layout_path.read_text(encoding="utf-8"))
    legacy = layout["legacy"]
    for key in ("unclassified_modules", "missing_module_docstrings"):
        legacy[key] = sorted(set(legacy[key]) - owners)
    legacy["mixed_modules"] = sorted(set(legacy["mixed_modules"]) | (owners - {reusable_in_place}))
    legacy["noncanonical_modules"] = sorted(set(legacy["noncanonical_modules"]) | {
        "NumStability.Algorithms.NormEstimation.PNorm.Endpoints.ConvergenceStatements",
        "NumStability.Algorithms.NormEstimation.PNorm.Endpoints.PNormRectangular",
    })
    layout_path.write_text(json.dumps(layout, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")


def check_postimage(clone: Path, owners: set[str], reusable: set[str], canonical: set[str]) -> None:
    files = {".".join(p.relative_to(clone).with_suffix("").parts): p for p in (clone / "NumStability").rglob("*.lean")}
    graph = {m: set(IMPORT_RE.findall(p.read_text(encoding="utf-8"))) for m, p in files.items()}
    missing = {t for targets in graph.values() for t in targets if t.startswith("NumStability.") and t not in files}
    if missing: raise PatchError(f"unresolved project import: {sorted(missing)[0]}")
    def closure(module: str) -> set[str]:
        seen: set[str] = set(); todo = [module]
        while todo:
            for target in graph.get(todo.pop(), set()):
                if target not in seen: seen.add(target); todo.append(target)
        return seen
    reusable_in_place = {"NumStability.Algorithms.CondEstimation"}
    historical_facades = owners - reusable_in_place
    for module in canonical | reusable_in_place:
        if closure(module) & historical_facades:
            raise PatchError(f"canonical-to-historical after R0011: {module}")
    for module in reusable | reusable_in_place:
        if any(x.startswith("NumStability.Source.") for x in closure(module)):
            raise PatchError(f"reusable-to-Source after R0011: {module}")
    tiers = json.loads((clone / "docs/architecture/tiers.json").read_text())
    if len(tiers["exact"]) != 1403 or len(tiers["prefixes"]) != 24:
        raise PatchError("tier postimage totals differ")
    if Counter(tiers["exact"].values()) != Counter(aggregate=368, mixed=35, compatibility=337, reusable=378, source=283, internal=2):
        raise PatchError("tier postimage class totals differ")
    legacy = json.loads((clone / "docs/architecture/layout-exceptions.json").read_text())["legacy"]
    expected = {"unclassified_modules": 282, "missing_module_docstrings": 77, "mixed_modules": 35,
                "noncanonical_modules": 268, "declaration_bearing_umbrellas": 21, "unsorted_import_modules": 0}
    for key, count in expected.items():
        actual = len(legacy.get(key, []))
        if actual != count: raise PatchError(f"layout postimage {key} differs: {actual}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--full", action="store_true", help="also run layout, compatibility, provenance, and strict-source")
    parser.add_argument("--write-patch", action="store_true", help="regenerate the deterministic 14-path R0011.patch")
    args = parser.parse_args()
    rows, owners, reusable, source = read_routes()
    verify_preimages()
    request_paths = set(SHARED_BLOBS) | ABSENT
    with tempfile.TemporaryDirectory(prefix="W10-integrator-") as raw:
        clone = Path(raw) / "repo"
        run(["git", "clone", "--shared", "--no-checkout", str(ROOT), str(clone)], ROOT)
        run(["git", "checkout", "--detach", BASE], clone)
        if args.write_patch:
            patch_aggregates(clone, reusable, source)
            patch_controls(clone, owners)
            if changed_paths(clone) != request_paths:
                raise PatchError("deterministic constructor changed-path roster differs")
            payload = render_patch(clone, request_paths)
            PATCH_PATH.write_bytes(payload)
            print(f"wrote {PATCH_PATH}: {len(payload)} bytes, sha256={hashlib.sha256(payload).hexdigest().upper()}")
            return 0
        verify_patch()
        run(["git", "apply", "--unidiff-zero", "--check", str(PATCH_PATH)], clone)
        run(["git", "apply", "--unidiff-zero", str(PATCH_PATH)], clone)
        run(["git", "apply", "--unidiff-zero", "--reverse", "--check", str(PATCH_PATH)], clone)
        if changed_paths(clone) != request_paths:
            raise PatchError("R0011 forward changed-path roster differs")
        pinned_postimages = exact_postimages(clone, request_paths)
        run(["git", "apply", "--unidiff-zero", "--reverse", str(PATCH_PATH)], clone)
        if changed_paths(clone):
            raise PatchError("R0011 reverse replay did not restore the exact C0007 tree")
        patch_aggregates(clone, reusable, source)
        patch_controls(clone, owners)
        if changed_paths(clone) != request_paths:
            raise PatchError("deterministic constructor changed-path roster differs")
        constructed = exact_postimages(clone, request_paths)
        different = sorted(path for path in request_paths if constructed[path] != pinned_postimages[path])
        if different:
            first = different[0]
            left, right = constructed[first], pinned_postimages[first]
            raise PatchError(
                f"deterministic constructor differs from pinned patch: {first}; "
                f"constructed={len(left)} bytes/{left.count(bytes([13,10]))} CRLF, "
                f"pinned={len(right)} bytes/{right.count(bytes([13,10]))} CRLF, "
                f"LF-normalized-equal={left.replace(bytes([13,10]), bytes([10])) == right.replace(bytes([13,10]), bytes([10]))}"
            )
        overlay_worker(clone)
        canonical = reusable | source | {
            "NumStability.Source.Higham.Chapter15.Section01.ConditionNumbers.CondEstimation"
        }
        check_postimage(clone, owners, reusable, canonical)
        if args.full:
            for tool in ("check_layout.py", "check_compatibility.py", "check_provenance.py"):
                result = run([sys.executable, "-B", f"tools/architecture/{tool}"], clone, capture=True)
                print(result.stdout, end="")
            result = run([
                sys.executable, "-B", "tools/architecture/generate_baseline.py", "--skip-declarations",
                "--strict-source", "--output-dir", "benchmark-results/W10-integrator-strict-source",
                "--name", "W10-integrator-strict-source",
            ], clone, capture=True)
            print(result.stdout, end="")
            baseline = json.loads((clone / "benchmark-results/W10-integrator-strict-source/W10-integrator-strict-source.json").read_text())
            audit = baseline["source"]["tier_audit"]
            for key in ("forbidden_reusable_edge_count", "forbidden_reusable_reachability_count", "reusable_to_source_edge_count", "reusable_to_source_reachability_count"):
                if audit[key] != 0: raise PatchError(f"strict-source {key} is nonzero")
    print("W10 R0011 replay passed: exact C0007 preimages, 14 aggregate/control paths, preserved accepted-consumer and historical-root imports, zero reusable-to-Source and canonical-to-historical reachability")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (PatchError, OSError, ValueError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
