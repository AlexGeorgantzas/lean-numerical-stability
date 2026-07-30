#!/usr/bin/env python3
"""Generate static, format-2 migration contracts for Higham Chapters 9 and 11."""

from __future__ import annotations

import argparse
import collections
import json
import re
from pathlib import Path

from generate_classification_proposal import MIXED, reviewed_tier, source_analysis_from_bytes
from lane_common import (
    BASE_SHA,
    EVIDENCE_HEAD,
    IMPORT_RE,
    PROPOSAL_ROOT,
    ROOT,
    SOURCE_NAME_RE,
    SourceCommandIndex,
    augment_entries_from_source,
    authoritative_root,
    git,
    git_show_bytes,
    module_from_path,
    read_format2_zip,
    read_ilean_entries,
    read_tsv,
    remove_lean_comments,
    sha256_bytes,
    sha256_file,
    source_analysis,
    source_command_bytes,
    stable_json,
    write_tsv,
)


BUILD_ROOT = Path(r"C:\Users\qed_s\OneDrive\Documents\QED 94\.lake\build\lib\lean")

CH09_SEAMS = [
    (344, "NumStability.Source.Higham.Chapter09.Section01"),
    (6485, "NumStability.Source.Higham.Chapter09.Section02"),
    (7969, "NumStability.Source.Higham.Chapter09.Section03"),
    (17601, "NumStability.Source.Higham.Chapter09.Section04"),
    (21288, "NumStability.Source.Higham.Chapter09.Section05"),
    (39021, "NumStability.Source.Higham.Chapter09.Section06"),
    (39320, "NumStability.Source.Higham.Chapter09.Section08"),
    (39505, "NumStability.Source.Higham.Chapter09.Section10"),
    (80815, "NumStability.Source.Higham.Chapter09.Section11"),
    (10**9, "NumStability.Source.Higham.Chapter09.Problems"),
]

CH11_SEAMS = [
    (93, "NumStability.Source.Higham.Chapter11.Section01.Basic"),
    (545, "NumStability.Source.Higham.Chapter11.Section01.CompletePivoting"),
    (36435, "NumStability.Source.Higham.Chapter11.Section01.PartialPivoting"),
    (36717, "NumStability.Source.Higham.Chapter11.Section01.RookPivoting"),
    (94386, "NumStability.Source.Higham.Chapter11.Section01.Tridiagonal"),
    (136546, "NumStability.Source.Higham.Chapter11.Section02.Aasen"),
    (136717, "NumStability.Source.Higham.Chapter11.Section03.SkewSymmetric"),
    (10**9, "NumStability.Source.Higham.Chapter11.Problems"),
]


def normalize_private(name: str, module: str) -> str:
    prefix = f"_private.{module}."
    if not name.startswith(prefix):
        return name
    rest = name[len(prefix) :]
    return name if rest.startswith("0.") else prefix + "0." + rest


def rewrite_private(name: str, module: str, destination: str) -> str:
    normalized = normalize_private(name, module)
    prefix = f"_private.{module}.0."
    if not normalized.startswith(prefix):
        raise ValueError(f"private declaration does not use owner prefix: {name}")
    return f"_private.{destination}.0.{normalized[len(prefix):]}"


def clean_leaf(leaf: str, chapter: str) -> str:
    if chapter == "09":
        leaf = re.sub(r"^HighamChapter9", "", leaf)
    else:
        leaf = re.sub(r"^HighamChapter11", "", leaf)
        leaf = re.sub(r"Ch11(?:Closure|Discrepancy)?$", "", leaf)
        leaf = re.sub(r"Higham11(?:Closure)?$", "", leaf)
    return leaf or "Core"


def destination_for_root(
    chapter: str, module: str, root: str, span: tuple[int, ...], tier: str
) -> str:
    leaf = module.rsplit(".", 1)[-1]
    if module == "NumStability.Algorithms.HighamChapter9":
        return next(destination for limit, destination in CH09_SEAMS if span[0] < limit)
    if module == "NumStability.Algorithms.HighamChapter11":
        return next(destination for limit, destination in CH11_SEAMS if span[0] < limit)

    cleaned = clean_leaf(leaf, chapter)
    if tier == "mixed_pending_split":
        source_root = bool(SOURCE_NAME_RE.search(root))
        if source_root:
            return f"NumStability.Source.Higham.Chapter{chapter}.{cleaned}"
        if chapter == "09":
            return f"NumStability.Algorithms.LinearSystems.LU.DiagonalDominance.{cleaned}"
        family = "Aasen" if cleaned.startswith("Aasen") else "BlockLDLT"
        return f"NumStability.Algorithms.LinearSystems.SymmetricIndefinite.{family}.{cleaned}"
    if tier == "reusable":
        family = "Aasen" if cleaned.startswith("Aasen") else "BlockLDLT"
        return f"NumStability.Algorithms.LinearSystems.SymmetricIndefinite.{family}.{cleaned}"
    return f"NumStability.Source.Higham.Chapter{chapter}.{cleaned}"


def candidate_paths(packet_root: Path, chapter: str) -> list[str]:
    name = "CH09_PREP_PATHS.tsv" if chapter == "09" else "CH11_PREP_PATHS.tsv"
    rows = read_tsv(packet_root / name)
    result = [row["path"] for row in rows if row["role"] == "candidate_production"]
    expected = 11 if chapter == "09" else 66
    if len(result) != expected:
        raise ValueError(f"Chapter {chapter}: expected {expected} candidates, got {len(result)}")
    if chapter == "11" and any("BunchTridiagonalCapstone" in path for path in result):
        raise ValueError("Chapter 11 capstone compatibility wrapper entered candidate set")
    return result


def source_imports(payload: bytes) -> list[str]:
    text = payload.decode("utf-8-sig")
    return [
        item
        for item in IMPORT_RE.findall(remove_lean_comments(text))
        if item.startswith("NumStability")
    ]


def assert_dag(edges: set[tuple[str, str]]) -> None:
    nodes = {item for edge in edges for item in edge}
    dependencies = {node: set() for node in nodes}
    for owner, dependency in edges:
        dependencies[owner].add(dependency)
    remaining = set(nodes)
    while remaining:
        ready = {node for node in remaining if not (dependencies[node] & remaining)}
        if not ready:
            cycle = sorted(remaining)[:8]
            raise ValueError(f"destination graph contains a cycle involving {cycle}")
        remaining -= ready


def generate_one(packet_root: Path, chapter: str, declarations, edges) -> None:
    contract_root = PROPOSAL_ROOT / f"ch{chapter}"
    contract_root.mkdir(parents=True, exist_ok=True)
    paths = candidate_paths(packet_root, chapter)
    modules = [module_from_path(path) for path in paths]
    module_set = set(modules)
    selected = {
        name: declaration
        for name, declaration in declarations.items()
        if declaration.module in module_set
    }

    route_rows: list[list[object]] = []
    ownership_rows: list[list[object]] = []
    private_rows: list[list[object]] = []
    frozen_rows: list[dict[str, object]] = []
    route_destination: dict[str, str] = {}
    route_module: dict[str, str] = {}
    route_root: dict[str, str] = {}
    roots_by_module: dict[str, dict[str, tuple[int, ...]]] = {}
    module_destinations: dict[str, set[str]] = collections.defaultdict(set)

    for path, module in zip(paths, modules):
        payload = git_show_bytes(BASE_SHA, path)
        ilean_path = BUILD_ROOT / Path(path).with_suffix(".ilean")
        if not ilean_path.exists():
            raise ValueError(f"missing authoritative .ilean metadata: {ilean_path}")
        module_declarations = [item for item in selected.values() if item.module == module]
        roots = augment_entries_from_source(
            payload,
            module,
            (item.name for item in module_declarations),
            read_ilean_entries(ilean_path, module),
        )
        roots_by_module[module] = roots
        source_index = SourceCommandIndex(payload)
        authored = {authoritative_root(item.name, roots) for item in module_declarations}
        frozen_rows.append(
            {
                "module": module,
                "path": path,
                "git_blob": git("rev-parse", f"{BASE_SHA}:{path}").strip(),
                "source_sha256": sha256_bytes(payload),
                "source_lines": len(payload.splitlines()),
                "format2_declarations": len(module_declarations),
                "authored_roots": len(authored),
                "ilean_sha256": sha256_file(ilean_path),
                "ilean_bytes": ilean_path.stat().st_size,
            }
        )

        analysis = source_analysis_from_bytes(git_show_bytes(EVIDENCE_HEAD, path))
        tier = reviewed_tier(module, analysis)
        root_destinations: dict[str, str] = {}
        for root in authored:
            span = roots[root]
            destination = destination_for_root(chapter, module, root, span, tier)
            root_destinations[root] = destination
            module_destinations[module].add(destination)

        for item in sorted(module_declarations, key=lambda value: value.name):
            root = authoritative_root(item.name, roots)
            span = roots[root]
            destination = root_destinations[root]
            normalized_name = normalize_private(item.name, module)
            normalized_root = normalize_private(root, module)
            command = source_index.command(span)
            if root.rsplit(".", 1)[-1].replace("`", "")[:16] not in command.decode(
                "utf-8", "replace"
            ):
                raise ValueError(f"{module}: .ilean span does not contain root {root}")
            route_rows.append(
                [
                    "route",
                    module,
                    item.name,
                    normalized_name,
                    root,
                    normalized_root,
                    "authored" if item.name == root else "compiler_generated",
                    *span,
                    sha256_bytes(command),
                    destination,
                ]
            )
            ownership_rows.append(
                [item.name, module, destination, item.kind, item.visibility]
            )
            route_destination[item.name] = destination
            route_module[item.name] = module
            route_root[item.name] = root

        for root in sorted(authored):
            declaration = selected.get(root)
            if declaration is not None and declaration.visibility == "private":
                private_rows.append(
                    [root, normalize_private(root, module), rewrite_private(root, module, root_destinations[root])]
                )

    dag_counts: dict[tuple[str, str], collections.Counter[str]] = collections.defaultdict(collections.Counter)
    ch09_dependencies: dict[tuple[str, str, str], collections.Counter[str]] = collections.defaultdict(collections.Counter)
    for edge in edges:
        if edge.source not in selected:
            continue
        source_destination = route_destination[edge.source]
        if edge.target in selected:
            target_destination = route_destination[edge.target]
            if source_destination != target_destination:
                dag_counts[(source_destination, target_destination)][edge.kind] += 1
        elif chapter == "11":
            target_declaration = declarations.get(edge.target)
            if target_declaration and (
                target_declaration.module.startswith("NumStability.Algorithms.HighamChapter9")
                or target_declaration.module.startswith("NumStability.Source.Higham.Chapter09")
            ):
                key = (source_destination, target_declaration.module, edge.target)
                ch09_dependencies[key][edge.kind] += 1

    assert_dag(set(dag_counts))

    exact_imports: set[tuple[str, str, str, str]] = set()
    for (owner, dependency), counts in dag_counts.items():
        exact_imports.add((owner, "canonical_destination", dependency, "selected_declaration_edge"))
    for path, module in zip(paths, modules):
        for destination in module_destinations[module]:
            exact_imports.add((module, "compatibility_wrapper", destination, "preserve_historical_import"))
        # Declaration commands remain frozen at BASE_SHA above, but the import
        # contract must describe the reviewed evidence head. Reusing packet-base
        # imports here silently resurrects compatibility umbrellas after their
        # canonical cutover.
        evidence_payload = git_show_bytes(EVIDENCE_HEAD, path)
        for dependency in source_imports(evidence_payload):
            if dependency in module_set:
                for owner in module_destinations[module]:
                    for target in module_destinations[dependency]:
                        if owner != target:
                            exact_imports.add((owner, "canonical_destination", target, "frozen_direct_import"))
            else:
                for owner in module_destinations[module]:
                    exact_imports.add((owner, "canonical_destination", dependency, "frozen_direct_import"))

    downstream: set[tuple[str, str, str]] = set()
    for relative in git("ls-tree", "-r", "--name-only", EVIDENCE_HEAD).splitlines():
        if not relative.endswith(".lean"):
            continue
        if relative in paths:
            continue
        if relative.startswith("NumStabilityTest/Worker/ClassificationAudit/"):
            # Lane-local evidence is not a production downstream consumer and
            # may be committed after the proposal is generated.
            continue
        text = git_show_bytes(EVIDENCE_HEAD, relative).decode(
            "utf-8-sig", errors="replace"
        )
        for dependency in IMPORT_RE.findall(remove_lean_comments(text)):
            if dependency in module_set:
                downstream.add((module_from_path(relative), dependency, relative))

    write_tsv(
        contract_root / "candidate-modules.tsv",
        ["module", "path", "role"],
        ({"module": module, "path": path, "role": "candidate_production"} for path, module in zip(paths, modules)),
    )
    write_tsv(
        contract_root / "frozen-owners.tsv",
        list(frozen_rows[0]),
        frozen_rows,
    )
    write_format(contract_root / "routes.tsv", 2, route_rows)
    write_format(contract_root / "ownership.tsv", 1, ownership_rows)
    write_format(contract_root / "private-rewrites.tsv", 1, private_rows)
    dag_rows = [
        ["edge", owner, dependency, counts["signature"], counts["body"]]
        for (owner, dependency), counts in sorted(dag_counts.items())
    ]
    write_format(contract_root / "owner-dag.tsv", 1, dag_rows)
    import_rows = [["import", *row] for row in sorted(exact_imports)]
    write_format(contract_root / "direct-imports.tsv", 1, import_rows)
    downstream_rows = [["consumer", *row] for row in sorted(downstream)]
    write_format(contract_root / "downstream-consumers.tsv", 1, downstream_rows)
    dependency_rows = [
        ["dependency", owner, module, name, counts["signature"], counts["body"]]
        for (owner, module, name), counts in sorted(ch09_dependencies.items())
    ]
    write_format(contract_root / "chapter09-dependencies.tsv", 1, dependency_rows)

    public = sum(item.visibility == "public" for item in selected.values())
    private = len(selected) - public
    status = "READY_AFTER_QR_INTEGRATION" if chapter == "09" else "BLOCKED_ON_CH09_INTEGRATION"
    artifacts = [
        "candidate-modules.tsv",
        "frozen-owners.tsv",
        "routes.tsv",
        "ownership.tsv",
        "private-rewrites.tsv",
        "owner-dag.tsv",
        "direct-imports.tsv",
        "downstream-consumers.tsv",
        "chapter09-dependencies.tsv",
    ]
    acceptance = {
        "schema_version": 1,
        "chapter": chapter,
        "packet_base_sha": BASE_SHA,
        "review_evidence_head": EVIDENCE_HEAD,
        "implementation_status": status,
        "integrated_main_refresh": (
            f"BLOCKLU_GLOBAL_GATES_PASSED_AT_{EVIDENCE_HEAD};"
            "QR_SHARED_INTEGRATION_PENDING"
            if chapter == "09"
            else "CHAPTER09_NOT_IMPLEMENTED;CURRENT_IMPORT_REFRESH_REQUIRED_BEFORE_IMPLEMENTATION"
        ),
        "candidate_modules": len(modules),
        "format2_declarations": len(selected),
        "public_declarations": public,
        "private_declarations": private,
        "route_rows": len(route_rows),
        "ownership_rows": len(ownership_rows),
        "authored_private_rewrites": len(private_rows),
        "canonical_destinations": len({value for value in route_destination.values()}),
        "destination_dag_edges": len(dag_rows),
        "exact_import_rows": len(import_rows),
        "downstream_consumer_rows": len(downstream_rows),
        "chapter09_dependency_rows": len(dependency_rows),
        "baseline_format2_zip_sha256": sha256_file(packet_root / "baseline/parallel-base-declarations-v2.zip"),
        "artifact_sha256": {name: sha256_file(contract_root / name) for name in artifacts},
        "post_and_stage_status": "NOT_RUN_PROPOSAL_ONLY_NO_PRODUCTION_MOVES",
    }
    (contract_root / "acceptance.json").write_text(
        stable_json(acceptance), encoding="utf-8", newline="\n"
    )
    (contract_root / "README.md").write_text(
        render_readme(acceptance), encoding="utf-8", newline="\n"
    )


def write_format(path: Path, version: int, rows: list[list[object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    lines = [f"format\t{version}"]
    lines.extend("\t".join(str(cell) for cell in row) for row in rows)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")


def render_readme(data: dict[str, object]) -> str:
    chapter = data["chapter"]
    return f"""# Chapter {chapter} migration contract

This is a proposal-only semantic contract. It moves no production declaration
and changes no shared manifest. The {data['candidate_modules']} frozen owners
account for exactly {data['format2_declarations']} format-2 declarations
({data['public_declarations']} public, {data['private_declarations']} private).

Every declaration has one authoritative source-span route and one proposed
owner. Compiler-generated declarations follow their longest authored `.ilean`
root. Private authored roots have explicit rewrites. `owner-dag.tsv` is
acyclic; `direct-imports.tsv` records canonical dependencies plus the imports
needed by historical wrappers; and downstream consumers are enumerated.

Implementation status: `{data['implementation_status']}`.

Run `check_ch{chapter}_contract.py --mode pre` before using the
contract. Post/stage comparison requires a fresh candidate format-2 graph and
is intentionally not claimed by this preparation lane.
"""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--packet-root", type=Path, required=True)
    args = parser.parse_args()
    packet_root = args.packet_root.resolve()
    declarations, edges, _, _ = read_format2_zip(
        packet_root / "baseline/parallel-base-declarations-v2.zip"
    )
    for chapter in ("09", "11"):
        print(f"generating Chapter {chapter} contract", flush=True)
        generate_one(packet_root, chapter, declarations, edges)
        print(f"generated Chapter {chapter} contract", flush=True)


if __name__ == "__main__":
    main()
