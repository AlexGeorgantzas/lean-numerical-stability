#!/usr/bin/env python3
"""Validate Chapter 9/11 pre-contracts and optional post/stage format-2 graphs."""

from __future__ import annotations

import argparse
import collections
import json
import tempfile
from pathlib import Path

from generate_chapter_contracts import (
    BUILD_ROOT,
    assert_dag,
    normalize_private,
    rewrite_private,
)
from lane_common import (
    BASE_SHA,
    SourceCommandIndex,
    augment_entries_from_source,
    authoritative_root,
    git_show_bytes,
    read_format2_zip,
    read_ilean_entries,
    read_tsv,
    sha256_bytes,
    sha256_file,
    source_command_bytes,
)


def read_format(path: Path, version: int, width: int | None = None) -> list[list[str]]:
    lines = path.read_text(encoding="utf-8").splitlines()
    if not lines or lines[0].split("\t") != ["format", str(version)]:
        raise ValueError(f"{path}: expected format {version}")
    rows = [line.split("\t") for line in lines[1:]]
    if width is not None and any(len(row) != width for row in rows):
        raise ValueError(f"{path}: expected {width}-column rows")
    return rows


def self_test() -> None:
    assert normalize_private("A", "M") == "A"
    assert normalize_private("_private.M.x", "M") == "_private.M.0.x"
    assert normalize_private("_private.M.0.x", "M") == "_private.M.0.x"
    assert rewrite_private("_private.M.x", "M", "N") == "_private.N.0.x"
    assert_dag({("C", "B"), ("B", "A")})
    try:
        assert_dag({("A", "B"), ("B", "A")})
    except ValueError:
        pass
    else:
        raise AssertionError("cycle was accepted")
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "format.tsv"
        path.write_text("format\t1\nx\ty\n", encoding="utf-8")
        assert read_format(path, 1, 2) == [["x", "y"]]
    print("check_chapter_contract self-test: PASS")


def pre_check(contract_root: Path, baseline_zip: Path) -> dict[str, object]:
    acceptance = json.loads((contract_root / "acceptance.json").read_text(encoding="utf-8"))
    candidates = read_tsv(contract_root / "candidate-modules.tsv")
    frozen = read_tsv(contract_root / "frozen-owners.tsv")
    routes = read_format(contract_root / "routes.tsv", 2, 17)
    ownership = read_format(contract_root / "ownership.tsv", 1, 5)
    private_rows = read_format(contract_root / "private-rewrites.tsv", 1, 3)
    dag_rows = read_format(contract_root / "owner-dag.tsv", 1, 5)
    import_rows = read_format(contract_root / "direct-imports.tsv", 1, 5)
    downstream_rows = read_format(contract_root / "downstream-consumers.tsv", 1, 4)
    dependency_rows = read_format(contract_root / "chapter09-dependencies.tsv", 1, 6)
    declarations, edges, _, _ = read_format2_zip(baseline_zip)

    candidate_modules = {row["module"] for row in candidates}
    selected = {
        name: declaration
        for name, declaration in declarations.items()
        if declaration.module in candidate_modules
    }
    route_by_name: dict[str, list[str]] = {}
    root_destinations: dict[tuple[str, str], str] = {}
    candidate_by_module = {row["module"]: row for row in candidates}
    source_indices: dict[str, SourceCommandIndex] = {}
    entries_by_module: dict[str, dict[str, tuple[int, ...]]] = {}
    for module, item in candidate_by_module.items():
        payload = git_show_bytes(BASE_SHA, item["path"])
        ilean = BUILD_ROOT / Path(item["path"]).with_suffix(".ilean")
        entries_by_module[module] = augment_entries_from_source(
            payload,
            module,
            (value.name for value in selected.values() if value.module == module),
            read_ilean_entries(ilean, module),
        )
        source_indices[module] = SourceCommandIndex(payload)
    for row in routes:
        if row[0] != "route":
            raise ValueError("non-route row in routes contract")
        module, name, normalized, root, normalized_root = row[1:6]
        if name in route_by_name:
            raise ValueError(f"duplicate route: {name}")
        if name not in selected or selected[name].module != module:
            raise ValueError(f"route outside selected baseline: {name}")
        entries = entries_by_module[module]
        expected_root = authoritative_root(name, entries)
        if root != expected_root:
            raise ValueError(f"{name}: authoritative root drift")
        if normalized != normalize_private(name, module):
            raise ValueError(f"{name}: normalized name drift")
        if normalized_root != normalize_private(root, module):
            raise ValueError(f"{name}: normalized root drift")
        span = tuple(int(value) for value in row[7:15])
        if span != entries[root]:
            raise ValueError(f"{name}: source span drift")
        if row[15] != sha256_bytes(source_indices[module].command(span)):
            raise ValueError(f"{name}: source-command hash drift")
        destination = row[16]
        key = (module, root)
        if key in root_destinations and root_destinations[key] != destination:
            raise ValueError(f"{root}: compiler-generated route split from root")
        root_destinations[key] = destination
        route_by_name[name] = row
    if set(route_by_name) != set(selected):
        raise ValueError("routes do not exactly cover selected baseline declarations")

    ownership_by_name = {row[0]: row for row in ownership}
    if len(ownership_by_name) != len(ownership) or set(ownership_by_name) != set(selected):
        raise ValueError("ownership does not exactly cover selected baseline declarations")
    for name, row in ownership_by_name.items():
        declaration = selected[name]
        route = route_by_name[name]
        if row[1:] != [declaration.module, route[16], declaration.kind, declaration.visibility]:
            raise ValueError(f"{name}: ownership/route mismatch")

    expected_private = {}
    for (module, root), destination in root_destinations.items():
        declaration = selected.get(root)
        if declaration and declaration.visibility == "private":
            expected_private[root] = [
                root,
                normalize_private(root, module),
                rewrite_private(root, module, destination),
            ]
    actual_private = {row[0]: row for row in private_rows}
    if actual_private != expected_private:
        raise ValueError("private-rewrite contract is not exact")

    dag_edges = set()
    for row in dag_rows:
        if row[0] != "edge" or int(row[3]) + int(row[4]) <= 0:
            raise ValueError("malformed destination DAG row")
        dag_edges.add((row[1], row[2]))
    assert_dag(dag_edges)
    if any(row[0] != "import" for row in import_rows):
        raise ValueError("malformed exact-import row")
    if any(row[0] != "consumer" for row in downstream_rows):
        raise ValueError("malformed downstream-consumer row")
    if any(row[0] != "dependency" for row in dependency_rows):
        raise ValueError("malformed Chapter 9 dependency row")

    artifacts = acceptance["artifact_sha256"]
    for name, expected_hash in artifacts.items():
        if sha256_file(contract_root / name) != expected_hash:
            raise ValueError(f"artifact hash drift: {name}")
    expected_counts = {
        "candidate_modules": len(candidates),
        "format2_declarations": len(selected),
        "route_rows": len(routes),
        "ownership_rows": len(ownership),
        "authored_private_rewrites": len(private_rows),
        "destination_dag_edges": len(dag_rows),
        "exact_import_rows": len(import_rows),
        "downstream_consumer_rows": len(downstream_rows),
        "chapter09_dependency_rows": len(dependency_rows),
    }
    for key, value in expected_counts.items():
        if acceptance[key] != value:
            raise ValueError(f"acceptance count drift: {key}")
    return {
        "status": "PASS",
        "mode": "pre",
        "chapter": acceptance["chapter"],
        **expected_counts,
        "public_declarations": sum(item.visibility == "public" for item in selected.values()),
        "private_declarations": sum(item.visibility == "private" for item in selected.values()),
        "baseline_internal_edges": sum(
            1 for edge in edges if edge.source in selected and edge.target in selected
        ),
    }


def migrated_name(name: str, route: list[str]) -> str:
    module, destination = route[1], route[16]
    return rewrite_private(name, module, destination) if name.startswith("_private.") else name


def post_check(contract_root: Path, baseline_zip: Path, candidate_zip: Path, mode: str) -> dict[str, object]:
    pre = pre_check(contract_root, baseline_zip)
    base_declarations, base_edges, _, _ = read_format2_zip(baseline_zip)
    candidate_declarations, candidate_edges, _, _ = read_format2_zip(candidate_zip)
    routes = {row[2]: row for row in read_format(contract_root / "routes.tsv", 2, 17)}
    expected_names = {name: migrated_name(name, route) for name, route in routes.items()}
    if len(set(expected_names.values())) != len(expected_names):
        raise ValueError("private normalization causes a declaration collision")
    for old, new in expected_names.items():
        if new not in candidate_declarations:
            raise ValueError(f"candidate graph lacks migrated declaration: {new}")
        expected = base_declarations[old]
        actual = candidate_declarations[new]
        if (actual.kind, actual.visibility, actual.module) != (
            expected.kind,
            expected.visibility,
            routes[old][16],
        ):
            raise ValueError(f"candidate ownership/signature metadata drift: {new}")

    expected_edge_counts: collections.Counter[tuple[str, str, str]] = collections.Counter()
    for edge in base_edges:
        if edge.source in expected_names and edge.target in expected_names:
            expected_edge_counts[(edge.kind, expected_names[edge.source], expected_names[edge.target])] += 1
    migrated = set(expected_names.values())
    actual_edge_counts = collections.Counter(
        (edge.kind, edge.source, edge.target)
        for edge in candidate_edges
        if edge.source in migrated and edge.target in migrated
    )
    if expected_edge_counts != actual_edge_counts:
        raise ValueError("candidate typed graph differs from the frozen selected graph")
    return {
        **pre,
        "mode": mode,
        "candidate_format2_sha256": sha256_file(candidate_zip),
        "typed_internal_edges": sum(expected_edge_counts.values()),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--chapter", choices=["09", "11"])
    parser.add_argument("--contract-root", type=Path)
    parser.add_argument("--baseline-format2", type=Path)
    parser.add_argument("--candidate-format2", type=Path)
    parser.add_argument("--mode", choices=["pre", "post", "stage"], default="pre")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return
    if not all((args.chapter, args.contract_root, args.baseline_format2)):
        parser.error("--chapter, --contract-root, and --baseline-format2 are required")
    if args.mode == "pre":
        result = pre_check(args.contract_root.resolve(), args.baseline_format2.resolve())
    else:
        if not args.candidate_format2:
            parser.error("--candidate-format2 is required for post/stage mode")
        result = post_check(
            args.contract_root.resolve(),
            args.baseline_format2.resolve(),
            args.candidate_format2.resolve(),
            args.mode,
        )
    if result["chapter"] != args.chapter:
        raise ValueError("requested chapter differs from contract")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
