#!/usr/bin/env python3
"""Static W06 import, isolation, and placeholder gates over the worker tree."""

from __future__ import annotations

import argparse
import csv
import json
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path


IMPORT_RE = re.compile(
    r"(?m)^(?:public[ \t]+|private[ \t]+)?import[ \t]+"
    r"([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)[ \t]*$"
)
PLACEHOLDER_RE = re.compile(r"\b(?:sorry|admit)\b")
AXIOM_RE = re.compile(r"(?m)^(?:axiom|constant)[ \t]+")
DECL_RE = re.compile(
    r"(?m)^\s*(?:(?:private|protected|noncomputable|unsafe|scoped|local)\s+)*"
    r"(?:def|theorem|lemma|abbrev|opaque|axiom|inductive|structure|class|instance)\b"
)
LOCAL_NOTATION_RE = re.compile(r"(?m)^\s*(?:local\s+)?notation\b")
EXPECTED_PENDING_FACADE_EDGE = (
    "NumStability.Analysis.Error.RoundingProducts.Core",
    "NumStability.Analysis.LiebTrace",
)
EXPECTED_PENDING_FACADE_PATHS = 53


def module_path(module: str) -> Path:
    return Path(*module.split(".")).with_suffix(".lean")


def git(root: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", "-C", str(root), *args],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
        check=False,
    )
    if result.returncode:
        raise RuntimeError(result.stderr.strip())
    return result.stdout


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--control-root", type=Path, required=True)
    args = parser.parse_args()
    root = args.repo_root.resolve()
    control = args.control_root.resolve()
    phase = control / "docs/architecture/phases/2026-08-repository-reorganization"
    record = json.loads((phase / "branches/B0006.json").read_text(encoding="utf-8"))
    if record.get("status") != "active" or record.get("operator_ids") != ["codex-remote"]:
        raise RuntimeError("B0006 is not the active singleton codex-remote contract")
    owners = {item["path"][:-5].replace("/", ".") for item in record["owned_paths"]}

    matrix_path = root / "docs/architecture/deliveries/W06/TEST_MATRIX.tsv"
    with matrix_path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.DictReader(stream, delimiter="\t"))
    kind_counts = Counter(row["kind"] for row in rows)
    if kind_counts != Counter(canonical=176, compatibility=67, focused=14):
        raise RuntimeError(f"test matrix counts differ: {dict(kind_counts)}")

    boundary_lines = (
        root / "docs/architecture/deliveries/W06/DEPENDENCY_BOUNDARY.tsv"
    ).read_text(encoding="utf-8").splitlines()
    boundary_rows = list(csv.DictReader(boundary_lines[1:], delimiter="\t"))
    observed_boundaries = {
        row["relationship"]: tuple(
            int(row[field])
            for field in ("direct_imports", "signature_edges", "body_edges", "union_pairs")
        )
        for row in boundary_rows
    }
    expected_boundaries = {
        "W06_to_W05": (13, 4943, 3218, 5777),
        "W06_to_W02": (6, 309, 217, 343),
        "W06_to_W10": (1, 0, 3, 3),
        "W07_to_W06": (3, 0, 4, 4),
        "W09_to_W06": (1, 3, 4, 4),
        "W11_to_W06": (3, 70, 180, 181),
    }
    if observed_boundaries != expected_boundaries:
        raise RuntimeError(
            f"dependency boundary evidence differs: {observed_boundaries}"
        )

    isolation_errors = []
    canonical_modules = set()
    for row in rows:
        path = root / row["test_path"]
        if not path.is_file():
            isolation_errors.append(f"missing test: {row['test_path']}")
            continue
        imports = IMPORT_RE.findall(path.read_text(encoding="utf-8"))
        expected = row["import_modules"].split(",") if row["import_modules"] else []
        if imports != sorted(expected):
            isolation_errors.append(
                f"{row['test_path']}: imports={imports}, expected={sorted(expected)}"
            )
        if row["kind"] == "canonical":
            if len(imports) != 1:
                isolation_errors.append(f"{row['test_path']}: canonical test is not isolated")
            else:
                canonical_modules.add(imports[0])
        if row["kind"] == "compatibility" and (
            len(imports) != 1 or imports[0] not in owners
        ):
            isolation_errors.append(f"{row['test_path']}: old-path test is not isolated")

    import_cache: dict[str, tuple[str, ...]] = {}
    unresolved = set()

    def imports_of(module: str) -> tuple[str, ...]:
        if module in import_cache:
            return import_cache[module]
        path = root / module_path(module)
        if not path.is_file():
            if module.startswith("NumStability."):
                unresolved.add(module)
            import_cache[module] = ()
            return ()
        found = tuple(IMPORT_RE.findall(path.read_text(encoding="utf-8")))
        import_cache[module] = found
        return found

    facade_reachability = []
    pending_integrator_facade_reachability = []
    reusable_source_reachability = []
    cycles = []
    for root_module in sorted(canonical_modules):
        reusable = not root_module.startswith("NumStability.Source.")
        state: dict[str, int] = {}
        stack: list[str] = []

        def visit(module: str) -> None:
            if state.get(module) == 2:
                return
            if state.get(module) == 1:
                cycles.append(stack[stack.index(module):] + [module])
                return
            state[module] = 1
            stack.append(module)
            if module in owners and module != root_module:
                evidence = (root_module, tuple(stack))
                if len(stack) >= 2 and (stack[-2], module) == EXPECTED_PENDING_FACADE_EDGE:
                    pending_integrator_facade_reachability.append(evidence)
                else:
                    facade_reachability.append(evidence)
                stack.pop()
                state[module] = 2
                return
            if reusable and module.startswith("NumStability.Source."):
                reusable_source_reachability.append((root_module, tuple(stack)))
            for target in imports_of(module):
                if target.startswith("NumStability."):
                    visit(target)
            stack.pop()
            state[module] = 2

        visit(root_module)

    changed = set()
    for line in git(root, "diff", "--name-only", "240c0d041781385a647fbec461d6863537e562cb", "--").splitlines():
        if line.strip():
            changed.add(line.strip().replace("\\", "/"))
    changed.update(
        line.strip().replace("\\", "/")
        for line in git(root, "ls-files", "--others", "--exclude-standard").splitlines()
        if line.strip()
    )
    lean_paths = sorted(path for path in changed if path.endswith(".lean"))
    placeholder_hits = []
    missing_docs = []
    unsorted_imports = []
    facade_shape_errors = []
    sys.path.insert(0, str(root / "tools/architecture"))
    from generate_baseline import remove_lean_comments
    for relative in lean_paths:
        payload = (root / relative).read_text(encoding="utf-8")
        uncommented = remove_lean_comments(payload)
        if PLACEHOLDER_RE.search(uncommented) or AXIOM_RE.search(uncommented):
            placeholder_hits.append(relative)
        if relative.startswith("NumStability/") and relative not in {
            item["path"] for item in record["owned_paths"]
        } and "/-!" not in payload:
            missing_docs.append(relative)
        imports = IMPORT_RE.findall(payload)
        if imports != sorted(set(imports)):
            unsorted_imports.append(relative)

    retention_lines = (
        root / "docs/architecture/deliveries/W06/RETENTION.tsv"
    ).read_text(encoding="utf-8").splitlines()
    retention_rows = list(csv.DictReader(retention_lines[1:], delimiter="\t"))
    if len(retention_rows) != 67:
        facade_shape_errors.append(f"RETENTION.tsv has {len(retention_rows)} owners")
    for row in retention_rows:
        module = row["historical_module"]
        payload = (root / module_path(module)).read_text(encoding="utf-8")
        uncommented = remove_lean_comments(payload)
        has_declaration = bool(
            DECL_RE.search(uncommented) or LOCAL_NOTATION_RE.search(uncommented)
        )
        if row["facade_kind"] == "pure_import_shim":
            residual = IMPORT_RE.sub("", uncommented).strip()
            if has_declaration or residual:
                facade_shape_errors.append(f"pure shim is not import-only: {module}")
        if row["facade_kind"] == "declaration_bearing" and not has_declaration:
            facade_shape_errors.append(f"retained facade lacks declarations: {module}")

    pending_edges = {
        (path[-2], path[-1])
        for _, path in pending_integrator_facade_reachability
        if len(path) >= 2
    }
    pending_integrator_errors = []
    if (
        len(pending_integrator_facade_reachability) != EXPECTED_PENDING_FACADE_PATHS
        or pending_edges != {EXPECTED_PENDING_FACADE_EDGE}
    ):
        pending_integrator_errors.append({
            "expected_edge": EXPECTED_PENDING_FACADE_EDGE,
            "expected_paths": EXPECTED_PENDING_FACADE_PATHS,
            "observed_edges": sorted(pending_edges),
            "observed_paths": len(pending_integrator_facade_reachability),
        })

    casefold_paths = {}
    casefold_collisions = []
    for path in sorted((root / "NumStability").rglob("*.lean")):
        relative = path.relative_to(root).as_posix()
        folded = relative.casefold()
        if folded in casefold_paths and casefold_paths[folded] != relative:
            casefold_collisions.append((casefold_paths[folded], relative))
        casefold_paths[folded] = relative

    result = {
        "tests": dict(kind_counts),
        "canonical_modules": len(canonical_modules),
        "changed_lean_paths": len(lean_paths),
        "isolation_errors": isolation_errors,
        "unresolved_project_imports": sorted(unresolved),
        "import_cycles": cycles[:10],
        "canonical_to_W06_facade_paths": facade_reachability[:10],
        "integrator_pending_facade_path_count": len(pending_integrator_facade_reachability),
        "integrator_pending_facade_paths": pending_integrator_facade_reachability[:10],
        "integrator_pending_facade_errors": pending_integrator_errors,
        "reusable_to_Source_paths": reusable_source_reachability[:10],
        "placeholder_or_axiom_paths": placeholder_hits,
        "missing_module_docstrings": missing_docs,
        "unsorted_or_duplicate_imports": unsorted_imports,
        "facade_shape_errors": facade_shape_errors,
        "casefold_path_collisions": casefold_collisions,
    }
    print(json.dumps(result, indent=2))
    return 1 if any((
        isolation_errors,
        unresolved,
        cycles,
        facade_reachability,
        pending_integrator_errors,
        reusable_source_reachability,
        placeholder_hits,
        missing_docs,
        unsorted_imports,
        facade_shape_errors,
        casefold_collisions,
    )) else 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, ValueError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
