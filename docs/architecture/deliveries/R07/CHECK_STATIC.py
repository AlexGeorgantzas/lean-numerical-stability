#!/usr/bin/env python3
"""Static semantic, retention, import-graph, and materialization checks for R07."""

from __future__ import annotations

import argparse
import csv
import gzip
import hashlib
import json
import re
import subprocess
import sys
from collections import Counter, defaultdict, deque
from pathlib import Path


BASE = "ad92bbfae62d538f3e52829a269a846688a8e213"
CONTROL_HEAD = "35cb1a7c5f136f291398dddd99d8012dcf38f967"
PHASE = Path("docs/architecture/phases/2026-08-repository-reorganization-completion")
BRANCH = PHASE / "branches"
DELIVERY = Path("docs/architecture/deliveries/R07")
MATERIALIZATION_SHA = "05C738043A6D990B7E2BBBE9B200E2A4B54AB8B042AFE9A308A6ACD1FF71A5FA"
MATERIALIZER_SHA = "1C45DEF702DB5DE58963D979AD3AD90ED66F16A3F69BF396C05F8DF2FBD12112"
COPIED = {
    "DECLARATION_ROUTES.tsv": ("B0010-declaration-routes.tsv", "03C9D117716ABC19F64F9304DDE169FE7691A9215C139A08C70681F180DD9C16"),
    "PRIVATE_CLOSURE.tsv": ("B0010-private-closure.tsv", "3D7B5DFFCEEE3C4F9AEB3AD6F3793F7457A7BE66BBF09F0C973D8195C7494C56"),
    "PRIVATE_NORMALIZATION.tsv": ("B0010-private-normalization.tsv", "CA0D8BF8C0FC6179A9DFD03F68B1BAA69A0D4EE78A0BEFCB0541B839EE755B16"),
    "REALIZED_IMPORTS.tsv": ("B0010-post-move-import-manifest.tsv", "788DC7987191EBF9325F8DE253DC793FAF3BF8AB1119F201B5E0918971C194E1"),
    "TEST_MATRIX.tsv": ("B0010-test-plan.tsv", "60CDF737B207BF571176378D40BF484004D8E61DF252C84C37CD8885830E804F"),
}
RAW_HISTORICAL_FRONTIER = {
    "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.FiniteDimensionalPowerBounds.Kreiss",
    "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarArcLength.Variation",
    "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarCrossingBounds.Polynomial",
    "NumStability.Analysis.LinearOperators.Pseudospectra.Resolvent.Internal.ScalarNotation",
    "NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.SpijkerKreissUnconditional.Bounds",
}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def rows(path: Path) -> list[dict[str, str]]:
    with path.open("r", encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def git(root: Path, *args: str, binary: bool = False) -> str | bytes:
    return subprocess.run(
        ["git", *args], cwd=root, check=True, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, text=not binary,
    ).stdout


def module_path(module: str) -> Path:
    return Path(module.replace(".", "/") + ".lean")


def import_lines(path: Path) -> list[str]:
    return [line.strip() for line in path.read_text(encoding="utf-8-sig").splitlines()
            if line.lstrip().startswith("import ")]


def strip_lean_comments(text: str) -> str:
    """Strip nested block and line comments, retaining strings conservatively."""
    output: list[str] = []
    i = 0
    depth = 0
    quoted = False
    escaped = False
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
            else:
                i += 1
            continue
        if quoted:
            output.append(text[i])
            if escaped:
                escaped = False
            elif text[i] == "\\":
                escaped = True
            elif text[i] == '"':
                quoted = False
            i += 1
            continue
        if pair == "/-":
            depth = 1
            i += 2
        elif pair == "--":
            newline = text.find("\n", i + 2)
            i = len(text) if newline < 0 else newline
        else:
            output.append(text[i])
            quoted = text[i] == '"'
            i += 1
    return "".join(output)


def build_graph(repo: Path) -> tuple[set[str], dict[str, list[str]], list[str]]:
    modules: dict[str, Path] = {}
    problems: list[str] = []
    for path in (repo / "NumStability").rglob("*.lean"):
        relative = path.relative_to(repo).as_posix()
        module = relative[:-5].replace("/", ".")
        modules[module] = path
    graph: dict[str, list[str]] = {}
    for module, path in modules.items():
        imports = [line.split(None, 1)[1] for line in import_lines(path)]
        graph[module] = [target for target in imports if target.startswith("NumStability.")]
        for target in graph[module]:
            if target not in modules:
                problems.append(f"unresolved production import {module} -> {target}")
    return set(modules), graph, problems


def cyclic_nodes(graph: dict[str, list[str]]) -> set[str]:
    indegree = {node: 0 for node in graph}
    reverse: dict[str, list[str]] = defaultdict(list)
    for source, targets in graph.items():
        for target in targets:
            if target in indegree:
                indegree[source] += 1
                reverse[target].append(source)
    queue = deque(node for node, degree in indegree.items() if degree == 0)
    seen = set(queue)
    while queue:
        node = queue.popleft()
        for consumer in reverse[node]:
            indegree[consumer] -= 1
            if indegree[consumer] == 0:
                seen.add(consumer)
                queue.append(consumer)
    return set(graph) - seen


def reaches(graph: dict[str, list[str]], start: str, targets: set[str]) -> bool:
    stack = list(graph.get(start, []))
    seen: set[str] = set()
    while stack:
        node = stack.pop()
        if node in targets:
            return True
        if node in seen:
            continue
        seen.add(node)
        stack.extend(graph.get(node, []))
    return False


def candidate_declarations(path: Path) -> dict[str, tuple[str, str, str]]:
    data = path.read_bytes()
    if data[:2] == b"\x1f\x8b":
        data = gzip.decompress(data)
    result: dict[str, tuple[str, str, str]] = {}
    for number, line in enumerate(data.decode("utf-8").splitlines(), 1):
        fields = line.split("\t")
        if fields and fields[0] == "declaration":
            if len(fields) != 5:
                raise ValueError(f"candidate declaration row {number} has {len(fields)} fields")
            _, name, module, kind, visibility = fields
            if name in result:
                raise ValueError(f"duplicate candidate declaration {name}")
            result[name] = (module, kind, visibility)
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--control-root", required=True, type=Path)
    parser.add_argument("--candidate", type=Path)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[4]
    control = args.control_root.resolve()
    problems: list[str] = []
    if git(control, "rev-parse", "HEAD").strip() != CONTROL_HEAD:
        problems.append("control checkout is not the activated R07 control commit")

    materialization = repo / DELIVERY / "MATERIALIZATION.json"
    materializer = repo / DELIVERY / "auditors" / "materialize_worker.py"
    if not materialization.is_file() or sha(materialization) != MATERIALIZATION_SHA:
        problems.append("MATERIALIZATION.json hash mismatch")
        materialized = {"files": [], "counts": {}}
    else:
        materialized = json.loads(materialization.read_text(encoding="utf-8"))
    if not materializer.is_file() or sha(materializer) != MATERIALIZER_SHA:
        problems.append("materialize_worker.py hash mismatch")
    expected_counts = {
        "destinations": 30, "historical_wrappers_rewritten": 13,
        "historical_wrappers_unchanged": 32, "source_commands": 194,
        "tests": 102,
    }
    if materialized.get("counts") != expected_counts or len(materialized.get("files", [])) != 145:
        problems.append("materialization cardinality/count contract mismatch")
    for item in materialized.get("files", []):
        path = repo / item["path"]
        actual = sha(path) if path.is_file() else "MISSING"
        if actual != item["sha256"]:
            problems.append(f"materialized postimage mismatch {item['path']}: {actual}")
    if materializer.is_file():
        dry = subprocess.run(
            [sys.executable, "-B", str(materializer), "--project-root", str(repo),
             "--control-root", str(control)], cwd=repo, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        if dry.returncode:
            problems.append("materializer dry replay failed:\n" + dry.stdout.rstrip())
        else:
            try:
                dry_payload = json.loads(dry.stdout)
                if dry_payload.get("materialization_sha256") != MATERIALIZATION_SHA:
                    problems.append("materializer dry replay produced a different manifest hash")
                if dry_payload.get("rendered_files") != 145:
                    problems.append("materializer dry replay did not render 145 files")
            except json.JSONDecodeError:
                problems.append("materializer dry replay did not emit JSON")

    branches = control / BRANCH
    for local, (source, expected_sha) in COPIED.items():
        local_path = repo / DELIVERY / local
        source_path = branches / source
        if not local_path.is_file() or sha(local_path) != expected_sha:
            problems.append(f"copied delivery ledger hash mismatch: {local}")
        elif local_path.read_bytes() != source_path.read_bytes():
            problems.append(f"copied delivery ledger differs bytewise: {local}")

    route_rows = rows(branches / "B0010-declaration-routes.tsv")
    closure_rows = rows(branches / "B0010-private-closure.tsv")
    normalization_rows = rows(branches / "B0010-private-normalization.tsv")
    destination_rows = rows(branches / "B0010-destinations.tsv")
    module_routes = rows(branches / "B0010-module-routes.tsv")
    manifest_rows = rows(branches / "B0010-post-move-import-manifest.tsv")
    test_rows = rows(branches / "B0010-test-plan.tsv")
    owner_modules = {row["owner_module"] for row in module_routes}
    destination_modules = {row["module"] for row in destination_rows}
    bearing = {row["owner_module"] for row in module_routes if int(row["declaration_count"]) > 0}
    if len(route_rows) != 194 or Counter(row["visibility"] for row in route_rows) != Counter({"public": 150, "private": 44}):
        problems.append("declaration-route counts differ from 194/150/44")
    if Counter(row["route_class"] for row in route_rows) != Counter({"relocate_split": 130, "relocate_whole": 64}):
        problems.append("declaration route-class counts differ from split=130/whole=64")
    if len(closure_rows) != 77 or Counter(row["closure_role"] for row in closure_rows) != Counter({"private_seed": 44, "reverse_dependent_boundary": 33}):
        problems.append("private closure differs from 77 = 44 seeds + 33 boundary")
    if len(normalization_rows) != 44:
        problems.append("private normalization map does not have 44 rows")
    if len(destination_rows) != 30 or Counter(row["tier"] for row in destination_rows) != Counter({"reusable": 26, "internal": 3, "source": 1}):
        problems.append("destination tiers differ from reusable=26/internal=3/source=1")
    if len(module_routes) != 45 or len(bearing) != 13:
        problems.append("historical owner partition differs from 45/13/32")
    if len(manifest_rows) != 760 or len({row["module"] for row in manifest_rows}) != 87:
        problems.append("realized import manifest differs from 760 rows/87 modules")
    if len(test_rows) != 102 or Counter(row["test_class"] for row in test_rows) != Counter({
        "canonical_only": 30, "old_only": 45, "consumer": 24,
        "dependency_boundary": 1, "private_normalization": 1, "all": 1,
    }):
        problems.append("test matrix class counts differ from the 102-test contract")

    wrapper_rows = {row["owner_module"]: row for row in rows(branches / "B0010-wrapper-imports.tsv")}
    manifest_by_module: dict[str, list[dict[str, str]]] = defaultdict(list)
    for row in manifest_rows:
        manifest_by_module[row["module"]].append(row)
    for module in sorted(owner_modules):
        path = repo / module_path(module)
        actual_imports = import_lines(path)
        expected_imports = [f"import {target}" for target in wrapper_rows[module]["post_imports"].split(";") if target != "-"]
        if actual_imports != expected_imports:
            problems.append(f"historical wrapper import sequence mismatch: {module}")
        if module in bearing:
            remainder = strip_lean_comments(path.read_text(encoding="utf-8-sig"))
            remainder = "\n".join(line for line in remainder.splitlines() if not line.lstrip().startswith("import ")).strip()
            if remainder:
                problems.append(f"historical wrapper is not import-only: {module}")
        else:
            base_bytes = git(repo, "show", f"{BASE}:{module_path(module).as_posix()}", binary=True)
            if path.read_bytes() != base_bytes:
                problems.append(f"zero-declaration wrapper differs from exact C0005: {module}")
    for module in sorted(destination_modules):
        path = repo / module_path(module)
        manifest_imports = [row["lean_import_line"] for row in sorted(
            (row for row in manifest_by_module[module] if row["role"] == "produced_destination"),
            key=lambda row: int(row["import_order"]),
        )]
        if import_lines(path) != manifest_imports:
            problems.append(f"canonical destination import sequence mismatch: {module}")

    _modules, graph, graph_problems = build_graph(repo)
    problems.extend(graph_problems)
    cycles = cyclic_nodes(graph)
    if cycles:
        problems.append("production import cycle(s): " + ";".join(sorted(cycles)[:20]))
    direct_backedges = {(module, target) for module in destination_modules for target in graph.get(module, []) if target in owner_modules}
    if direct_backedges:
        problems.append("canonical destination directly imports historical owner: " + repr(sorted(direct_backedges)))
    non_source = {row["module"] for row in destination_rows if row["tier"] in {"reusable", "internal"}}
    source_modules = {module for module in graph if module.startswith("NumStability.Source.")}
    source_reach = {module for module in non_source if reaches(graph, module, source_modules)}
    if source_reach:
        problems.append("reusable/internal destination reaches Source: " + ";".join(sorted(source_reach)))
    historical_reach = {module for module in destination_modules if reaches(graph, module, owner_modules)}
    if historical_reach != RAW_HISTORICAL_FRONTIER:
        problems.append("raw worker historical frontier mismatch: " + repr(sorted(historical_reach)))

    for test in test_rows:
        path = repo / test["target"]
        actual = [line.split(None, 1)[1] for line in import_lines(path)]
        expected = [] if test["imports"] == "-" else test["imports"].split(";")
        forbidden = set() if test["forbidden_imports"] == "-" else set(test["forbidden_imports"].split(";"))
        if actual != expected:
            problems.append(f"test import sequence mismatch: {test['target']}")
        overlap = forbidden & set(actual)
        if overlap:
            problems.append(f"test imports forbidden modules {test['target']}: {sorted(overlap)}")

    placeholder = re.compile(r"\b(sorry|admit)\b|^\s*(axiom|constant)\s", re.MULTILINE)
    for module in sorted(destination_modules):
        stripped = strip_lean_comments((repo / module_path(module)).read_text(encoding="utf-8-sig"))
        match = placeholder.search(stripped)
        if match:
            problems.append(f"placeholder/proof-bypass token in destination {module}: {match.group(0)!r}")

    overlap = json.loads((branches / "B0010-overlap-review.json").read_text(encoding="utf-8"))
    if overlap.get("projected_remaining_queue") != {"R09": 72, "R10": 18}:
        problems.append("projected remaining queue is not exactly R09=72, R10=18")

    if args.candidate is not None:
        try:
            candidate = candidate_declarations(args.candidate.resolve())
        except (OSError, UnicodeError, ValueError, gzip.BadGzipFile) as error:
            problems.append(f"cannot parse candidate declaration graph: {error}")
        else:
            private_map = {row["old_private"]: row["new_private"] for row in normalization_rows}
            expected: dict[str, tuple[str, str, str]] = {}
            for route in route_rows:
                old = route["baseline_declaration_name"]
                name = private_map.get(old, old)
                expected[name] = (route["destination_module"], route["kind"], route["visibility"])
            if len(expected) != 194:
                problems.append(f"candidate expectation collapsed to {len(expected)} declarations")
            for name, spec in expected.items():
                if candidate.get(name) != spec:
                    problems.append(f"candidate route mismatch {name}: {candidate.get(name)} != {spec}")

    if problems:
        print("R07 static check FAILED")
        for problem in problems:
            print(f"- {problem}")
        return 1
    print("R07 static check passed")
    print("materialized_files=145 owners=45 rewritten=13 retained=32 destinations=30 tests=102")
    print("declarations=194 public=150 private=44 closure=77 imports=760 modules=87")
    print("direct_backedges=0 reusable_internal_source_reach=0 raw_historical_frontier=5")
    if args.candidate is not None:
        print(f"candidate_sha256={sha(args.candidate.resolve())}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
