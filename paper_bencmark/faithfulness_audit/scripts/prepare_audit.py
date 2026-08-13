#!/usr/bin/env python3
"""Prepare reproducible source and Lean dossiers for one HighamBench audit."""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

try:
    from .common import (
        AUDIT_SCHEMA_VERSION,
        SEMANTIC_CHECKS,
        TASK_ID_PATTERN,
        sha256_file,
        sha256_text,
    )
except ImportError:  # Direct script execution.
    from common import (  # type: ignore
        AUDIT_SCHEMA_VERSION,
        SEMANTIC_CHECKS,
        TASK_ID_PATTERN,
        sha256_file,
        sha256_text,
    )


SCRIPT_DIR = Path(__file__).resolve().parent
AUDIT_ROOT = SCRIPT_DIR.parent
PAPER_BENCHMARK_ROOT = AUDIT_ROOT.parent
REPOSITORY_ROOT = PAPER_BENCHMARK_ROOT.parent
HIGHAMBENCH_ROOT = PAPER_BENCHMARK_ROOT / "highambench"
SHARED_ROOT = HIGHAMBENCH_ROOT / "shared"
DOSSIER_HELPER = SCRIPT_DIR / "declaration_dossier.lean"


class PreparationError(RuntimeError):
    """Raised when an audit input cannot be prepared without ambiguity."""


def load_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise PreparationError(f"cannot read JSON {path}: {error}") from error
    if not isinstance(value, dict):
        raise PreparationError(f"expected a JSON object in {path}")
    return value


def write_json(path: Path, value: Any) -> None:
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n",
        encoding="utf-8",
    )


def parse_task_id(task_id: str) -> tuple[str, str]:
    normalized = task_id.upper()
    if re.fullmatch(TASK_ID_PATTERN, normalized) is None:
        raise PreparationError(f"invalid task ID {task_id!r}; expected P01-T1")
    return tuple(normalized.split("-", 1))  # type: ignore[return-value]


def direct_imports(source: str) -> list[str]:
    imports: list[str] = []
    for line in source.splitlines():
        match = re.match(r"^\s*import\s+([A-Za-z0-9_'.]+)\s*$", line)
        if match:
            imports.append(match.group(1))
    return imports


def local_module_source(module: str) -> Path | None:
    candidate = SHARED_ROOT / (module.replace(".", "/") + ".lean")
    return candidate if candidate.is_file() else None


def collect_local_imports(target_source: str) -> tuple[list[str], dict[str, list[str]], set[str]]:
    order: list[str] = []
    graph: dict[str, list[str]] = {"AuditTarget": direct_imports(target_source)}
    external: set[str] = set()
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(module: str) -> None:
        if module in visited:
            return
        if module in visiting:
            raise PreparationError(f"cycle in local import graph at {module}")
        source_path = local_module_source(module)
        if source_path is None:
            external.add(module)
            return
        visiting.add(module)
        imports = direct_imports(source_path.read_text(encoding="utf-8"))
        graph[module] = imports
        for imported in imports:
            visit(imported)
        visiting.remove(module)
        visited.add(module)
        order.append(module)

    for module in graph["AuditTarget"]:
        visit(module)
    return order, graph, external


def theorem_source(source: str, theorem_name: str) -> str:
    start_match = re.search(rf"(?m)^theorem\s+{re.escape(theorem_name)}\b", source)
    if start_match is None:
        raise PreparationError(f"cannot find theorem declaration {theorem_name}")
    proof_match = re.search(r":=\s*by\b", source[start_match.start() :])
    if proof_match is None:
        raise PreparationError(f"cannot find proof boundary for {theorem_name}")
    end = start_match.start() + proof_match.start()
    return source[start_match.start() : end].rstrip()


def run_checked(command: list[str], *, env: dict[str, str] | None = None) -> str:
    completed = subprocess.run(
        command,
        cwd=REPOSITORY_ROOT,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if completed.returncode != 0:
        rendered = " ".join(command)
        raise PreparationError(f"command failed ({completed.returncode}): {rendered}\n{completed.stdout}")
    return completed.stdout


def lean_environment(build_root: Path) -> dict[str, str]:
    environment = os.environ.copy()
    existing = environment.get("LEAN_PATH", "")
    environment["LEAN_PATH"] = str(build_root) + ((":" + existing) if existing else "")
    return environment


def compile_module(
    source: Path, output: Path, environment: dict[str, str], module_root: Path
) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    run_checked(
        [
            "lake",
            "env",
            "lean",
            "--root",
            str(module_root),
            "-o",
            str(output),
            str(source),
        ],
        env=environment,
    )


def unescape_field(value: str) -> str:
    output: list[str] = []
    index = 0
    while index < len(value):
        if value[index] != "\\" or index + 1 >= len(value):
            output.append(value[index])
            index += 1
            continue
        marker = value[index + 1]
        output.append({"n": "\n", "r": "\r", "t": "\t", "\\": "\\"}.get(marker, marker))
        index += 2
    return "".join(output)


def parse_lean_report(output: str) -> dict[str, Any]:
    target_readable = ""
    target_explicit = ""
    environment_modules: list[str] = []
    dependencies: list[dict[str, Any]] = []
    edges: list[dict[str, str]] = []
    for raw_line in output.splitlines():
        fields = [unescape_field(field) for field in raw_line.split("\t")]
        if not fields:
            continue
        if fields[0] == "target-readable" and len(fields) == 2:
            target_readable = fields[1]
        elif fields[0] == "target-explicit" and len(fields) == 2:
            target_explicit = fields[1]
        elif fields[0] == "environment-module" and len(fields) == 2:
            environment_modules.append(fields[1])
        elif fields[0] == "dependency" and len(fields) == 9:
            dependencies.append(
                {
                    "role": fields[1],
                    "name": fields[2],
                    "owner_module": fields[3],
                    "distance": int(fields[4]),
                    "kind": fields[5],
                    "type_readable": fields[6],
                    "type_explicit": fields[7],
                    "body_readable": fields[8],
                }
            )
        elif fields[0] == "edge" and len(fields) == 4:
            edges.append({"parent": fields[1], "child": fields[2], "origin": fields[3]})
    if not target_readable or not target_explicit or not dependencies:
        raise PreparationError("Lean dossier helper returned an incomplete report")
    for index, dependency in enumerate(dependencies, start=1):
        dependency["id"] = f"D{index:03d}"
        dependency["semantic_sha256"] = dependency_fingerprint(dependency)
    return {
        "target_type_readable": target_readable,
        "target_type_explicit": target_explicit,
        "environment_modules": environment_modules,
        "dependencies": dependencies,
        "edges": edges,
    }


def dependency_fingerprint(dependency: dict[str, Any]) -> str:
    """Hash declaration semantics independently of task-local IDs and distance."""
    semantic_fields = {
        key: dependency.get(key, "")
        for key in (
            "role",
            "name",
            "owner_module",
            "kind",
            "type_readable",
            "type_explicit",
            "body_readable",
        )
    }
    return sha256_text(
        json.dumps(semantic_fields, sort_keys=True, ensure_ascii=True, separators=(",", ":"))
    )


def build_semantic_report(
    target_path: Path,
    theorem_full_name: str,
    local_order: list[str],
) -> dict[str, Any]:
    with tempfile.TemporaryDirectory(prefix="highambench-faithfulness-") as temporary:
        build_root = Path(temporary)
        environment = lean_environment(build_root)
        for module in local_order:
            source = local_module_source(module)
            if source is None:
                raise PreparationError(f"local module disappeared while preparing audit: {module}")
            staged_source = build_root / (module.replace(".", "/") + ".lean")
            staged_source.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, staged_source)
            output = staged_source.with_suffix(".olean")
            compile_module(staged_source, output, environment, build_root)

        staged_target = build_root / "AuditTarget.lean"
        shutil.copy2(target_path, staged_target)
        compile_module(
            staged_target, build_root / "AuditTarget.olean", environment, build_root
        )

        local_modules_file = build_root / "local-modules.txt"
        local_modules_file.write_text(
            "\n".join(["AuditTarget", *local_order]) + "\n", encoding="utf-8"
        )
        output = run_checked(
            [
                "lake",
                "env",
                "lean",
                "--run",
                str(DOSSIER_HELPER),
                "AuditTarget",
                theorem_full_name,
                str(local_modules_file),
            ],
            env=environment,
        )
        return parse_lean_report(output)


def fenced(value: str, language: str = "lean") -> str:
    return f"```{language}\n{value.rstrip()}\n```"


def dependency_section(dependency: dict[str, Any], *, explicit: bool) -> str:
    lines = [
        f"### {dependency['id']}: `{dependency['name']}`",
        "",
        f"- Role: `{dependency['role']}`",
        f"- Owner module: `{dependency['owner_module']}`",
        f"- Declaration kind: `{dependency['kind']}`",
        f"- Distance from target type: `{dependency['distance']}`",
        f"- Semantic SHA-256: `{dependency['semantic_sha256']}`",
        "",
        "Type:",
        "",
        fenced(dependency["type_readable"]),
    ]
    if explicit:
        lines.extend(["", "Fully explicit type:", "", fenced(dependency["type_explicit"])])
    if dependency["body_readable"]:
        lines.extend(["", "Definition body (one-level semantic boundary):", "", fenced(dependency["body_readable"])])
    return "\n".join(lines)


def blind_names(dependencies: list[dict[str, Any]]) -> dict[str, str]:
    local = [dependency for dependency in dependencies if dependency["role"] == "local"]
    return {
        dependency["name"]: f"LocalDef{index:03d}"
        for index, dependency in enumerate(local, start=1)
    }


def replace_names(value: str, replacements: dict[str, str]) -> str:
    for original in sorted(replacements, key=len, reverse=True):
        value = value.replace(original, replacements[original])
    return value


def blind_dependency(
    dependency: dict[str, Any],
    name_replacements: dict[str, str],
    module_replacements: dict[str, str],
) -> dict[str, Any]:
    rendered = dict(dependency)
    rendered["name"] = name_replacements.get(dependency["name"], dependency["name"])
    rendered["owner_module"] = module_replacements.get(
        dependency["owner_module"], dependency["owner_module"]
    )
    for key in ("type_readable", "type_explicit", "body_readable"):
        rendered[key] = replace_names(dependency[key], name_replacements)
    return rendered


def make_direct_dossier(
    task_id: str,
    declaration_source: str,
    semantic: dict[str, Any],
    local_order: list[str],
    graph: dict[str, list[str]],
    *,
    include_complete_sources: bool = True,
) -> str:
    lines = [
        f"# Declaration dossier for {task_id}",
        "",
        "This dossier describes the theorem statement only. Its proof is excluded.",
        "Judges must interpret every dependency entry and may not infer semantics from names.",
        "",
        "## Exact source declaration",
        "",
        fenced(declaration_source),
        "",
        "## Elaborated target type",
        "",
        fenced(semantic["target_type_readable"]),
        "",
        "## Fully explicit elaborated target type",
        "",
        fenced(semantic["target_type_explicit"]),
        "",
        "## Local import graph",
        "",
        f"- `AuditTarget` imports: {', '.join(f'`{item}`' for item in graph['AuditTarget'])}",
    ]
    for module in local_order:
        imports = graph.get(module, [])
        rendered = ", ".join(f"`{item}`" for item in imports) if imports else "none"
        lines.append(f"- `{module}` imports: {rendered}")
    lines.extend(
        [
            "",
            "## Semantic dependency inventory",
            "",
            (
                "`local` entries are recursively followed through their types and bodies. "
                "`external-frontier` entries are the exact Lean/mathlib declarations where "
                "that recursive traversal stops; their types and one-level bodies are still "
                "shown."
            ),
            "",
        ]
    )
    for dependency in semantic["dependencies"]:
        lines.extend([dependency_section(dependency, explicit=True), ""])
    if include_complete_sources:
        lines.extend(["## Complete local imported sources", ""])
        for module in local_order:
            source_path = local_module_source(module)
            assert source_path is not None
            source = source_path.read_text(encoding="utf-8")
            relative = source_path.relative_to(REPOSITORY_ROOT).as_posix()
            lines.extend(
                [
                    f"### `{module}`",
                    "",
                    f"Path: `{relative}`",
                    f"SHA-256: `{sha256_file(source_path)}`",
                    "",
                    fenced(source),
                    "",
                ]
            )
    return "\n".join(lines).rstrip() + "\n"


def write_dependency_inventories(
    inputs_dir: Path,
    semantic: dict[str, Any],
) -> tuple[Path, Path]:
    direct_path = inputs_dir / "dependency_inventory.json"
    blind_path = inputs_dir / "blind_dependency_inventory.json"
    name_replacements = blind_names(semantic["dependencies"])
    local_modules = sorted(
        {
            dependency["owner_module"]
            for dependency in semantic["dependencies"]
            if dependency["role"] == "local"
        }
    )
    module_replacements = {
        module: f"LocalImport{index:03d}"
        for index, module in enumerate(local_modules, start=1)
    }
    write_json(
        direct_path,
        {
            "schema_version": AUDIT_SCHEMA_VERSION,
            "dependencies": semantic["dependencies"],
        },
    )
    write_json(
        blind_path,
        {
            "schema_version": AUDIT_SCHEMA_VERSION,
            "dependencies": [
                blind_dependency(dependency, name_replacements, module_replacements)
                for dependency in semantic["dependencies"]
            ],
        },
    )
    return direct_path, blind_path


def make_blind_dossier(semantic: dict[str, Any]) -> str:
    name_replacements = blind_names(semantic["dependencies"])
    local_modules = sorted(
        {
            dependency["owner_module"]
            for dependency in semantic["dependencies"]
            if dependency["role"] == "local"
        }
    )
    module_replacements = {
        module: f"LocalImport{index:03d}"
        for index, module in enumerate(local_modules, start=1)
    }
    lines = [
        "# Blind Lean declaration dossier",
        "",
        "Translate only the mathematical proposition represented below. No paper identity,",
        "source prose, task metadata, theorem name, proof, or benchmark commentary is included.",
        "Do not use tools or inspect any filesystem content.",
        "",
        "## Elaborated target type",
        "",
        fenced(replace_names(semantic["target_type_readable"], name_replacements)),
        "",
        "## Fully explicit elaborated target type",
        "",
        fenced(replace_names(semantic["target_type_explicit"], name_replacements)),
        "",
        "## Complete semantic dependency inventory",
        "",
        "Account for every dependency ID in the translation output. Names are not definitions;",
        "use the supplied types and bodies to determine their exact meanings.",
        "",
    ]
    for dependency in semantic["dependencies"]:
        rendered = blind_dependency(
            dependency, name_replacements, module_replacements
        )
        lines.extend([dependency_section(rendered, explicit=False), ""])
    return "\n".join(lines).rstrip() + "\n"


def archive_existing_output(output_dir: Path) -> Path | None:
    children = [child for child in output_dir.iterdir() if child.name != "history"]
    if not children:
        return None
    history_root = output_dir / "history"
    timestamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    archive = history_root / timestamp
    suffix = 1
    while archive.exists():
        archive = history_root / f"{timestamp}-{suffix}"
        suffix += 1
    archive.mkdir(parents=True)
    for child in children:
        shutil.move(str(child), archive / child.name)
    return archive


def audit_setup_paths() -> list[Path]:
    fixed = [
        AUDIT_ROOT / "METHODOLOGY.md",
        SCRIPT_DIR / "common.py",
        SCRIPT_DIR / "declaration_dossier.lean",
        SCRIPT_DIR / "finalize_audit.py",
        SCRIPT_DIR / "apply_dependency_reuse.py",
        SCRIPT_DIR / "prepare_audit.py",
        SCRIPT_DIR / "prepare_paper_audit.py",
        SCRIPT_DIR / "split_paper_source_contract.py",
        SCRIPT_DIR / "validate_agent_output.py",
        SCRIPT_DIR / "validate_audit.py",
        AUDIT_ROOT / "templates" / "report.md",
        AUDIT_ROOT
        / "skill"
        / "highambench-faithfulness-audit"
        / "SKILL.md",
        AUDIT_ROOT
        / "skill"
        / "highambench-faithfulness-audit"
        / "agents"
        / "openai.yaml",
    ]
    discovered = [
        *sorted((AUDIT_ROOT / "prompts").glob("*.md")),
        *sorted((AUDIT_ROOT / "schemas").glob("*.json")),
    ]
    paths = [*fixed, *discovered]
    missing = [path for path in paths if not path.is_file()]
    if missing:
        raise PreparationError(
            "missing audit setup files: " + ", ".join(str(path) for path in missing)
        )
    return paths


def prepare(task_id: str, *, force: bool = False) -> Path:
    paper_id, tier = parse_task_id(task_id)
    task_dir = HIGHAMBENCH_ROOT / "tasks" / paper_id / tier
    target_path = task_dir / "Target.lean"
    task_json_path = task_dir / "task.json"
    context_path = task_dir / "context.md"
    for path in (target_path, task_json_path, context_path):
        if not path.is_file():
            raise PreparationError(f"missing task input: {path}")

    task = load_json(task_json_path)
    normalized_task_id = f"{paper_id}-{tier}"
    if task.get("task_id") != normalized_task_id:
        raise PreparationError(f"task.json ID does not match {normalized_task_id}")
    formal = task.get("formal_statement")
    if not isinstance(formal, dict):
        raise PreparationError("task.json has no formal_statement object")
    theorem_name = formal.get("theorem_name")
    namespace = formal.get("namespace")
    if not isinstance(theorem_name, str) or not isinstance(namespace, str):
        raise PreparationError("task.json lacks the theorem name or namespace")
    theorem_full_name = f"{namespace}.{theorem_name}"

    paper_source = task.get("paper_source")
    if not isinstance(paper_source, dict):
        raise PreparationError("task.json has no paper_source object")
    paper_relative = paper_source.get("local_path")
    paper_expected_hash = paper_source.get("sha256")
    if not isinstance(paper_relative, str) or not isinstance(paper_expected_hash, str):
        raise PreparationError("task.json has an incomplete paper_source")
    paper_path = REPOSITORY_ROOT / paper_relative
    if not paper_path.is_file():
        reference_root = PAPER_BENCHMARK_ROOT / "reference_papers"
        candidates = [
            candidate
            for candidate in reference_root.glob("*.pdf")
            if sha256_file(candidate) == paper_expected_hash
        ]
        if len(candidates) != 1:
            raise PreparationError(
                f"missing reference paper {paper_path}; found {len(candidates)} hash-matched alternatives"
            )
        paper_path = candidates[0]
        paper_relative = paper_path.relative_to(REPOSITORY_ROOT).as_posix()
    paper_actual_hash = sha256_file(paper_path)
    if paper_actual_hash != paper_expected_hash:
        raise PreparationError(
            f"reference paper hash mismatch: expected {paper_expected_hash}, got {paper_actual_hash}"
        )
    source_locations = task.get("source_locations")
    if not isinstance(source_locations, list) or not source_locations:
        raise PreparationError("task.json has no source locations")

    output_dir = task_dir / "faithfulness"
    existing_files: list[Path] = []
    if output_dir.exists():
        for child in output_dir.iterdir():
            if child.name == "history":
                continue
            if child.is_file():
                existing_files.append(child)
            elif child.is_dir():
                existing_files.extend(path for path in child.rglob("*") if path.is_file())
    if existing_files and not force:
        raise PreparationError(f"audit output already exists; use --force to refresh {output_dir}")
    inputs_dir = output_dir / "inputs"
    agent_outputs_dir = output_dir / "agent_outputs"

    target_source = target_path.read_text(encoding="utf-8")
    declaration_source = theorem_source(target_source, theorem_name)
    local_order, graph, external_imports = collect_local_imports(target_source)
    semantic = build_semantic_report(
        target_path, theorem_full_name, local_order
    )
    blind_name_by_actual = blind_names(semantic["dependencies"])
    for dependency in semantic["dependencies"]:
        dependency["blind_name"] = blind_name_by_actual.get(
            dependency["name"], dependency["name"]
        )

    if existing_files and force:
        archive_existing_output(output_dir)
    inputs_dir.mkdir(parents=True, exist_ok=True)
    agent_outputs_dir.mkdir(parents=True, exist_ok=True)

    direct_dossier = make_direct_dossier(
        normalized_task_id,
        declaration_source,
        semantic,
        local_order,
        graph,
    )
    direct_review_packet = make_direct_dossier(
        normalized_task_id,
        declaration_source,
        semantic,
        local_order,
        graph,
        include_complete_sources=False,
    )
    blind_dossier = make_blind_dossier(semantic)
    direct_path = inputs_dir / "declaration_dossier.md"
    blind_path = inputs_dir / "blind_dossier.md"
    direct_review_path = inputs_dir / "direct_review_packet.md"
    blind_review_path = inputs_dir / "blind_review_packet.md"
    source_locator_path = inputs_dir / "source_locator.json"
    direct_path.write_text(direct_dossier, encoding="utf-8")
    blind_path.write_text(blind_dossier, encoding="utf-8")
    direct_review_path.write_text(direct_review_packet, encoding="utf-8")
    blind_review_path.write_text(blind_dossier, encoding="utf-8")
    direct_inventory_path, blind_inventory_path = write_dependency_inventories(
        inputs_dir, semantic
    )

    source_locator = {
        "task_id": normalized_task_id,
        "paper_path": paper_relative,
        "paper_sha256": paper_actual_hash,
        "paper_version": task.get("paper_version"),
        "source_locations": source_locations,
        "evidence_policy": (
            "Use the referenced PDF and surrounding paper context as evidence. "
            "Do not use context.md or task.json paraphrases as semantic evidence."
        ),
    }
    write_json(source_locator_path, source_locator)

    local_sources = []
    for module in local_order:
        source_path = local_module_source(module)
        assert source_path is not None
        local_sources.append(
            {
                "module": module,
                "path": source_path.relative_to(REPOSITORY_ROOT).as_posix(),
                "sha256": sha256_file(source_path),
                "direct_imports": graph.get(module, []),
            }
        )
    manifest = {
        "schema_version": AUDIT_SCHEMA_VERSION,
        "task_id": normalized_task_id,
        "status": "prepared",
        "prepared_at_utc": datetime.now(timezone.utc).isoformat(),
        "target": {
            "path": target_path.relative_to(REPOSITORY_ROOT).as_posix(),
            "sha256": sha256_file(target_path),
            "declaration": theorem_full_name,
        },
        "task_metadata": {
            "path": task_json_path.relative_to(REPOSITORY_ROOT).as_posix(),
            "sha256": sha256_file(task_json_path),
            "semantic_evidence": False,
        },
        "context": {
            "path": context_path.relative_to(REPOSITORY_ROOT).as_posix(),
            "sha256": sha256_file(context_path),
            "semantic_evidence": False,
        },
        "paper": {
            "path": paper_relative,
            "sha256": paper_actual_hash,
            "source_locations": source_locations,
        },
        "audit_setup": [
            {
                "path": path.relative_to(REPOSITORY_ROOT).as_posix(),
                "sha256": sha256_file(path),
            }
            for path in audit_setup_paths()
        ],
        "lean_environment": {
            "toolchain": {
                "path": "lean-toolchain",
                "sha256": sha256_file(REPOSITORY_ROOT / "lean-toolchain"),
                "value": (REPOSITORY_ROOT / "lean-toolchain")
                .read_text(encoding="utf-8")
                .strip(),
            },
            "lake_manifest": {
                "path": "lake-manifest.json",
                "sha256": sha256_file(REPOSITORY_ROOT / "lake-manifest.json"),
            },
        },
        "local_import_sources": local_sources,
        "direct_external_imports": sorted(external_imports),
        "compiled_environment": {
            "module_count": len(semantic["environment_modules"]),
            "sorted_module_names_sha256": sha256_text(
                "\n".join(semantic["environment_modules"]) + "\n"
            ),
        },
        "dependencies": [
            {
                key: dependency[key]
                for key in (
                    "id",
                    "role",
                    "name",
                    "blind_name",
                    "owner_module",
                    "distance",
                    "kind",
                    "semantic_sha256",
                )
            }
            for dependency in semantic["dependencies"]
        ],
        "dependency_edges": semantic["edges"],
        "semantic_checks": [
            {"id": item_id, "name": name, "requirement": requirement}
            for item_id, name, requirement in SEMANTIC_CHECKS
        ],
        "inputs": {
            "declaration_dossier": {
                "path": direct_path.relative_to(REPOSITORY_ROOT).as_posix(),
                "sha256": sha256_file(direct_path),
            },
            "blind_dossier": {
                "path": blind_path.relative_to(REPOSITORY_ROOT).as_posix(),
                "sha256": sha256_file(blind_path),
            },
            "source_locator": {
                "path": source_locator_path.relative_to(REPOSITORY_ROOT).as_posix(),
                "sha256": sha256_file(source_locator_path),
            },
            "direct_review_packet": {
                "path": direct_review_path.relative_to(REPOSITORY_ROOT).as_posix(),
                "sha256": sha256_file(direct_review_path),
            },
            "blind_review_packet": {
                "path": blind_review_path.relative_to(REPOSITORY_ROOT).as_posix(),
                "sha256": sha256_file(blind_review_path),
            },
            "dependency_inventory": {
                "path": direct_inventory_path.relative_to(REPOSITORY_ROOT).as_posix(),
                "sha256": sha256_file(direct_inventory_path),
            },
            "blind_dependency_inventory": {
                "path": blind_inventory_path.relative_to(REPOSITORY_ROOT).as_posix(),
                "sha256": sha256_file(blind_inventory_path),
            },
        },
        "blindness": {
            "allowed_input": "inputs/blind_review_packet.md supplied inline",
            "forbidden": [
                "conversation history",
                "filesystem or tool access",
                "reference paper",
                "context.md",
                "task.json",
                "theorem proof",
                "other agent outputs",
            ],
        },
    }
    write_json(output_dir / "manifest.json", manifest)
    return output_dir


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("task_id", help="task ID such as P11-T1")
    parser.add_argument(
        "--force", action="store_true", help="replace prepared inputs in an existing audit folder"
    )
    return parser


def main() -> int:
    args = make_parser().parse_args()
    try:
        output = prepare(args.task_id, force=args.force)
    except (OSError, PreparationError, subprocess.SubprocessError, ValueError) as error:
        print(f"faithfulness preparation error: {error}", file=sys.stderr)
        return 2
    print(output.relative_to(REPOSITORY_ROOT).as_posix())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
