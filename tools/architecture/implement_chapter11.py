#!/usr/bin/env python3
"""Materialize the reviewed Chapter 11 source split.

The Chapter 11 lane contract is intentionally declarative.  This small
integrator-side renderer turns its reviewed ownership/import tables into
canonical modules and exact historical import facades; it never invents a
route or changes a declaration body.
"""

from __future__ import annotations

import csv
import re
import subprocess
from collections import defaultdict
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
CONTRACT = ROOT / "docs/architecture/lane-proposals/claude-classification/ch11"
CH09_CONTRACT = ROOT / "docs/architecture/lane-proposals/claude-classification/ch09"
OLD_CH9 = "NumStability.Algorithms.HighamChapter9"


def rows(path: Path):
    with path.open(encoding="utf-8", newline="") as stream:
        for row in csv.reader(stream, delimiter="\t"):
            if row and row[0] not in {"format", "module", "consumer", "import", "dependency", "route", "edge"}:
                yield row


def modules():
    result = []
    with (CONTRACT / "candidate-modules.tsv").open(encoding="utf-8") as stream:
        for row in csv.DictReader(stream, delimiter="\t"):
            result.append((row["module"], ROOT / row["path"]))
    return result


def ownership_map():
    result: dict[str, set[str]] = defaultdict(set)
    with (CONTRACT / "ownership.tsv").open(encoding="utf-8") as stream:
        for row in csv.reader(stream, delimiter="\t"):
            if not row or row[0] == "format":
                continue
            result[row[1]].add(row[2])
    return result


def ch09_owner_map():
    result = {}
    with (CH09_CONTRACT / "ownership.tsv").open(encoding="utf-8") as stream:
        for row in csv.reader(stream, delimiter="\t"):
            if row and row[0] != "format":
                result[row[0]] = row[2]
    return result


def direct_imports():
    result: dict[str, set[str]] = defaultdict(set)
    with (CONTRACT / "direct-imports.tsv").open(encoding="utf-8") as stream:
        for row in csv.reader(stream, delimiter="\t"):
            if not row or row[0] == "format" or row[2] != "canonical_destination":
                continue
            result[row[1]].add(row[3])
    return result


def ch09_dependencies():
    result: dict[str, set[str]] = defaultdict(set)
    with (CONTRACT / "chapter09-dependencies.tsv").open(encoding="utf-8") as stream:
        for row in csv.reader(stream, delimiter="\t"):
            if row and row[0] == "dependency":
                result[row[1]].add(row[3])
    return result


def module_for(destination: str) -> Path:
    return ROOT / (destination.replace(".", "/") + ".lean")


def historical_text(path: Path) -> str:
    relative = path.relative_to(ROOT).as_posix()
    return subprocess.check_output(
        ["git", "show", f"HEAD:{relative}"], cwd=ROOT
    ).decode("utf-8")


def import_name(destination: str) -> str:
    return f"import {destination}"


def canonical_dependencies(destination: str, old_to_destination: dict[str, str]) -> list[str]:
    ch9 = ch09_owner_map()
    dep_roots = ch09_dependencies()
    result: set[str] = set()
    for dependency in direct_imports()[destination]:
        if dependency in old_to_destination:
            result.add(old_to_destination[dependency])
        elif dependency == OLD_CH9:
            result.update(ch9[root] for root in dep_roots[destination] if root in ch9)
            if not dep_roots[destination]:
                result.add(dependency)
        else:
            result.add(dependency)
    return sorted(result)


def header(destination: str, dependencies: list[str], title: str) -> str:
    imports = "\n".join(import_name(item) for item in dependencies)
    return f"{imports}\n\n/-!\n# {title}\n\nCanonical owner materialized from the reviewed Chapter 11 route contract.\n-/\n\n"


def render_satellite_from_text(original: str, destination: str, dependencies: list[str]) -> str:
    # Preserve all documentation, opens, namespaces, and declarations while
    # replacing only the historical import block.  Import statements are
    # top-level in every reviewed satellite.
    original_imports = re.findall(r"(?m)^\s*import\s+([A-Za-z0-9_'.]+)", original)
    external_imports = sorted(item for item in original_imports if not item.startswith("NumStability"))
    all_dependencies = sorted(set(external_imports) | set(dependencies))
    body = re.sub(r"(?m)^\s*import\s+[^\n]+\n", "", original)
    return header(destination, all_dependencies, f"Higham Chapter 11: {destination.rsplit('.', 1)[-1]}") + body.lstrip()


def render_section(old_lines: list[str], start: int, end: int, destination: str, dependencies: list[str]) -> str:
    body = "".join(old_lines[start:end])
    return header(destination, dependencies, f"Higham Chapter 11: {destination.rsplit('.', 1)[-1]}") + \
        "namespace NumStability\n\nopen scoped BigOperators\n\n" + body + "\nend NumStability\n"


def main() -> None:
    candidates = modules()
    old_to_dest: dict[str, str] = {}
    by_old_path = {module: path for module, path in candidates}
    ownership = ownership_map()
    for module, _ in candidates:
        destinations = ownership[module]
        if module != "NumStability.Algorithms.HighamChapter11" and len(destinations) != 1:
            raise SystemExit(f"{module}: expected one reviewed destination, got {sorted(destinations)}")
        if module != "NumStability.Algorithms.HighamChapter11":
            old_to_dest[module] = next(iter(destinations))

    # Satellites become canonical declaration-bearing modules.
    for old_module, old_path in candidates:
        if old_module == "NumStability.Algorithms.HighamChapter11":
            continue
        destination = old_to_dest[old_module]
        target = module_for(destination)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(render_satellite_from_text(historical_text(old_path), destination, canonical_dependencies(destination, old_to_dest)), encoding="utf-8")

    old_path = by_old_path["NumStability.Algorithms.HighamChapter11"]
    old_lines = historical_text(old_path).splitlines(keepends=True)
    seams = [
        (14, "NumStability.Source.Higham.Chapter11.Section01.Basic"),
        (93, "NumStability.Source.Higham.Chapter11.Section01.CompletePivoting"),
        (545, "NumStability.Source.Higham.Chapter11.Section01.PartialPivoting"),
        (36435, "NumStability.Source.Higham.Chapter11.Section01.RookPivoting"),
        (36717, "NumStability.Source.Higham.Chapter11.Section01.Tridiagonal"),
        (94386, "NumStability.Source.Higham.Chapter11.Section02.Aasen"),
        (136546, "NumStability.Source.Higham.Chapter11.Section03.SkewSymmetric"),
        (136717, "NumStability.Source.Higham.Chapter11.Problems"),
    ]
    for index, (start, destination) in enumerate(seams):
        end = seams[index + 1][0] if index + 1 < len(seams) else len(old_lines) - 1
        target = module_for(destination)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(render_section(old_lines, start, end, destination, canonical_dependencies(destination, old_to_dest)), encoding="utf-8")

    # Historical candidate paths remain exact import-only compatibility facades.
    for old_module, old_path in candidates:
        if old_module == "NumStability.Algorithms.HighamChapter11":
            destinations = [destination for _, destination in seams]
        else:
            destinations = [old_to_dest[old_module]]
        old_path.write_text(
            "\n".join(import_name(destination) for destination in destinations)
            + "\n\n/-!\nCompatibility facade for the canonical Chapter 11 owner(s).\n-/\n",
            encoding="utf-8",
        )

    print(f"materialized {len(old_to_dest)} satellite owners and {len(seams)} section owners")


if __name__ == "__main__":
    main()
