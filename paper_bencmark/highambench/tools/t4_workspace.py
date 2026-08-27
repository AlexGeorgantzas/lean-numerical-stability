#!/usr/bin/env python3
"""Initialize one isolated, paper-local HighamBench T4 workspace.

The descriptor is the generic hand-off between extraction, private proof,
packet, and review tooling.  It contains no paper-specific review geometry and
its write set is disjoint from every other paper's write set.  Historical P01
campaign scripts remain useful for auditing their immutable artifacts, but are
not generic workspace initializers and must not be copied for later papers.

Only ``scratch_pad/t4_source_faithfulness/P0X/workspace.json`` is written by
this tool.  Paper-owned paths are bindings for the paper's single writer; the
generic schema and template bindings are shared, hash-pinned, and read-only.
"""

from __future__ import annotations

import argparse
import copy
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import sys
from typing import Any, Iterator, Mapping, Sequence
import uuid

try:
    from .common import BenchmarkToolError, read_json, safe_relative_path, sha256_file
    from .validator import sanitize_lean
except ImportError:  # Direct script execution.
    from common import (  # type: ignore
        BenchmarkToolError,
        read_json,
        safe_relative_path,
        sha256_file,
    )
    from validator import sanitize_lean  # type: ignore


SCHEMA_VERSION = "highambench-t4-workspace-0.1"
KIND = "highambench-t4-workspace"
MODES = ("init", "check", "write-set")
PAPER_ID_RE = re.compile(r"^P[0-9]{2}$")
MODULE_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")
IMPORT_RE = re.compile(
    r"(?m)^\s*(?:(?:public|private|meta)\s+)*import\s+([^\r\n]+?)\s*$"
)
UPSTREAM_IMPORT_ROOTS = ("Batteries", "Lean", "Mathlib", "Std")
GENERIC_CONTRACT_FILES = (
    ("task_schema", "schemas/highambench-t4-task-0.4.schema.json"),
    (
        "source_inventory_schema",
        "schemas/highambench-t4-source-inventory-0.3.schema.json",
    ),
    ("task_template", "templates/T4/task.pending.template.json"),
    (
        "source_inventory_template",
        "templates/T4/source_inventory.pending.template.json",
    ),
)


@dataclass(frozen=True)
class WorkspaceLayout:
    benchmark_root: Path
    reference_root: Path
    scratch_root: Path
    paper_id: str
    source_pdf: Path

    @property
    def task_root(self) -> Path:
        return self.benchmark_root / "tasks" / self.paper_id / "T4"

    @property
    def definitions(self) -> Path:
        return (
            self.benchmark_root
            / "shared"
            / "HighamBench"
            / f"{self.paper_id}Definitions.lean"
        )

    @property
    def private_root(self) -> Path:
        return self.scratch_root / "private_gold" / self.paper_id

    @property
    def faithfulness_root(self) -> Path:
        return self.scratch_root / "t4_source_faithfulness" / self.paper_id

    @property
    def workspace_file(self) -> Path:
        return self.faithfulness_root / "workspace.json"


def _canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def descriptor_digest(value: Mapping[str, Any]) -> str:
    """Return the self-hash for a descriptor, excluding its hash field."""

    basis = dict(value)
    basis.pop("descriptor_sha256", None)
    payload = json.dumps(
        basis, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _bind_descriptor_digest(value: Mapping[str, Any]) -> dict[str, Any]:
    result = dict(value)
    result["descriptor_sha256"] = descriptor_digest(result)
    return result


def _validate_paper_id(paper_id: str) -> None:
    if PAPER_ID_RE.fullmatch(paper_id) is None:
        raise BenchmarkToolError(
            f"paper id must have canonical P0X form (for example P06): {paper_id!r}"
        )


def _existing_root(path: Path, label: str) -> Path:
    if path.is_symlink() or not path.is_dir():
        raise BenchmarkToolError(f"{label} must be a non-symlink directory: {path}")
    return path.resolve()


def _scratch_root(path: Path) -> Path:
    if path.is_symlink():
        raise BenchmarkToolError(f"scratch root may not be a symlink: {path}")
    if path.exists() and not path.is_dir():
        raise BenchmarkToolError(f"scratch root must be a directory: {path}")
    return path.resolve()


def _assert_below(root: Path, path: Path, label: str) -> None:
    root = root.resolve()
    cursor = root
    try:
        path.resolve().relative_to(root)
    except ValueError as error:
        raise BenchmarkToolError(f"{label} escapes {root}: {path}") from error
    for part in path.relative_to(root).parts:
        cursor = cursor / part
        if cursor.is_symlink():
            raise BenchmarkToolError(f"{label} contains a symlink component: {cursor}")


def _discover_source_pdf(reference_root: Path, paper_id: str) -> Path:
    matches = sorted(
        reference_root.glob(f"{paper_id}_*.pdf"), key=lambda path: path.name
    )
    if len(matches) != 1:
        names = [path.name for path in matches]
        raise BenchmarkToolError(
            f"expected exactly one {paper_id}_*.pdf below {reference_root}; "
            f"found {len(matches)}: {names}"
        )
    source = matches[0]
    if source.is_symlink() or not source.is_file():
        raise BenchmarkToolError(f"source PDF must be a regular non-symlink file: {source}")
    _assert_below(reference_root, source, "source PDF")
    return source


def _pdf_page_count(path: Path) -> tuple[int | None, str | None]:
    """Read an uncompressed page-tree count, with page-object fallback.

    This dependency-free probe deliberately returns ``None`` for PDFs whose
    page tree is available only in compressed object streams.  Packet builders
    may later replace that optional observation with a full PDF parser result.
    """

    data = path.read_bytes()
    if not data.lstrip().startswith(b"%PDF-"):
        return None, None
    page_tree_counts = [
        int(match)
        for match in re.findall(
            rb"/Type\s*/Pages\b(?:(?!endobj).){0,8192}?/Count\s+([0-9]+)\b",
            data,
            flags=re.DOTALL,
        )
    ]
    if page_tree_counts:
        return max(page_tree_counts), "pdf-page-tree-count"
    page_objects = len(re.findall(rb"/Type\s*/Page\b", data))
    if page_objects:
        return page_objects, "pdf-page-object-count"
    return None, None


def _path_ref(root: str, relative: str, *, kind: str) -> dict[str, str]:
    path = safe_relative_path(relative)
    return {"root": root, "path": path.as_posix(), "kind": kind}


def _extract_imports(path: Path) -> list[str]:
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as error:
        raise BenchmarkToolError(f"cannot read Lean source {path}: {error}") from error
    sanitized = sanitize_lean(text, erase_strings=True)
    imports: list[str] = []
    for match in IMPORT_RE.finditer(sanitized):
        modules = match.group(1).split()
        if not modules or not all(MODULE_RE.fullmatch(module) for module in modules):
            raise BenchmarkToolError(f"cannot safely parse import command in {path}")
        imports.extend(modules)
    return imports


def _validate_imports(path: Path, paper_id: str, *, target: bool) -> None:
    if path.is_symlink():
        raise BenchmarkToolError(f"paper-controlled Lean source may not be a symlink: {path}")
    if not path.exists():
        return
    if not path.is_file():
        raise BenchmarkToolError(f"paper-controlled Lean path is not a file: {path}")
    imports = _extract_imports(path)
    own_definitions = f"HighamBench.{paper_id}Definitions"
    for imported in imports:
        root = imported.split(".", 1)[0]
        if imported in ("HighamBench.Core", "HighamBench.SemanticCore"):
            raise BenchmarkToolError(f"forbidden shared import in {path}: {imported}")
        if imported.startswith("HighamBench.") and not (
            target and imported == own_definitions
        ):
            raise BenchmarkToolError(f"foreign HighamBench import in {path}: {imported}")
        if root not in UPSTREAM_IMPORT_ROOTS and imported != own_definitions:
            raise BenchmarkToolError(f"non-upstream import in {path}: {imported}")
    if target and own_definitions not in imports:
        raise BenchmarkToolError(f"T4 target must import {own_definitions}: {path}")


def _validate_bound_files(layout: WorkspaceLayout) -> None:
    _assert_below(layout.benchmark_root, layout.task_root, "T4 task root")
    _assert_below(layout.benchmark_root, layout.definitions, "definitions")
    _assert_below(layout.scratch_root, layout.private_root, "private proof root")
    _assert_below(
        layout.scratch_root, layout.faithfulness_root, "faithfulness root"
    )
    for name, relative in GENERIC_CONTRACT_FILES:
        path = layout.benchmark_root / relative
        _assert_below(layout.benchmark_root, path, f"generic contract {name}")
        if path.is_symlink() or not path.is_file():
            raise BenchmarkToolError(
                f"generic T4 contract must be a regular non-symlink file: {path}"
            )
    _validate_imports(layout.definitions, layout.paper_id, target=False)
    _validate_imports(layout.task_root / "Target.lean", layout.paper_id, target=True)
    for name in ("source_inventory.json", "task.json"):
        path = layout.task_root / name
        if path.is_symlink() or (path.exists() and not path.is_file()):
            raise BenchmarkToolError(f"bound T4 path must be a regular file: {path}")


def _make_layout(
    benchmark_root: Path,
    reference_root: Path,
    scratch_root: Path | None,
    paper_id: str,
) -> WorkspaceLayout:
    _validate_paper_id(paper_id)
    benchmark = _existing_root(benchmark_root, "benchmark root")
    reference = _existing_root(reference_root, "reference root")
    scratch = _scratch_root(
        scratch_root if scratch_root is not None else benchmark.parent / "scratch_pad"
    )
    source = _discover_source_pdf(reference, paper_id)
    layout = WorkspaceLayout(benchmark, reference, scratch, paper_id, source)
    _validate_bound_files(layout)
    return layout


def build_workspace_descriptor(layout: WorkspaceLayout) -> dict[str, Any]:
    page_count, page_count_method = _pdf_page_count(layout.source_pdf)
    source_relative = layout.source_pdf.relative_to(layout.reference_root).as_posix()
    paper_id = layout.paper_id
    task_relative = f"tasks/{paper_id}/T4"
    private_relative = f"private_gold/{paper_id}"
    faithfulness_relative = f"t4_source_faithfulness/{paper_id}"
    result: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "kind": KIND,
        "paper_id": paper_id,
        "task_id": f"{paper_id}-T4",
        "roots": {
            "benchmark": str(layout.benchmark_root),
            "reference": str(layout.reference_root),
            "scratch": str(layout.scratch_root),
        },
        "source_pdf": {
            **_path_ref("reference", source_relative, kind="file"),
            "sha256": sha256_file(layout.source_pdf),
            "bytes": layout.source_pdf.stat().st_size,
            "page_count": page_count,
            "page_count_method": page_count_method,
        },
        "generic_contract_files": {
            name: {
                **_path_ref("benchmark", relative, kind="file"),
                "sha256": sha256_file(layout.benchmark_root / relative),
                "bytes": (layout.benchmark_root / relative).stat().st_size,
            }
            for name, relative in GENERIC_CONTRACT_FILES
        },
        "controlled_files": {
            "definitions": _path_ref(
                "benchmark",
                f"shared/HighamBench/{paper_id}Definitions.lean",
                kind="file",
            ),
            "target": _path_ref(
                "benchmark", f"{task_relative}/Target.lean", kind="file"
            ),
            "source_inventory": _path_ref(
                "benchmark", f"{task_relative}/source_inventory.json", kind="file"
            ),
            "task_record": _path_ref(
                "benchmark", f"{task_relative}/task.json", kind="file"
            ),
        },
        "artifacts": {
            "workspace_file": _path_ref(
                "scratch", f"{faithfulness_relative}/workspace.json", kind="file"
            ),
            "private_proof_root": _path_ref(
                "scratch", private_relative, kind="tree"
            ),
            "private_solvability_gate": _path_ref(
                "scratch",
                f"{private_relative}/private_solvability_gate.json",
                kind="file",
            ),
            "evidence_fragment_root": _path_ref(
                "scratch", f"{faithfulness_relative}/evidence_fragments", kind="tree"
            ),
            "packet_root": _path_ref(
                "scratch", f"{faithfulness_relative}/packets", kind="tree"
            ),
            "candidate_root": _path_ref(
                "scratch", f"{faithfulness_relative}/candidates", kind="tree"
            ),
            "campaign_plan_root": _path_ref(
                "scratch", f"{faithfulness_relative}/campaign_plans", kind="tree"
            ),
            "campaign_root": _path_ref(
                "scratch", f"{faithfulness_relative}/review_campaigns", kind="tree"
            ),
        },
        "import_policy": {
            "definitions_allowed_roots": list(UPSTREAM_IMPORT_ROOTS),
            "target_required_import": f"HighamBench.{paper_id}Definitions",
            "forbidden_local_roots": ["HighamBench", "NumStability"],
            "shared_core_imports_forbidden": [
                "HighamBench.Core",
                "HighamBench.SemanticCore",
            ],
        },
        "ownership": {
            "single_writer": paper_id,
            "write_set": [
                _path_ref(
                    "benchmark",
                    f"shared/HighamBench/{paper_id}Definitions.lean",
                    kind="file",
                ),
                _path_ref(
                    "benchmark",
                    f"tasks/{paper_id}/paper.json",
                    kind="file",
                ),
                _path_ref("benchmark", task_relative, kind="tree"),
                _path_ref("scratch", private_relative, kind="tree"),
                _path_ref("scratch", faithfulness_relative, kind="tree"),
            ],
        },
    }
    return _bind_descriptor_digest(result)


def _iter_path_refs(descriptor: Mapping[str, Any]) -> Iterator[tuple[str, Mapping[str, Any]]]:
    source = descriptor.get("source_pdf")
    if isinstance(source, Mapping):
        yield "source_pdf", source
    for section_name in ("generic_contract_files", "controlled_files", "artifacts"):
        section = descriptor.get(section_name)
        if not isinstance(section, Mapping):
            raise BenchmarkToolError(f"workspace {section_name} must be an object")
        for name, value in section.items():
            if not isinstance(value, Mapping):
                raise BenchmarkToolError(f"workspace {section_name}.{name} must be an object")
            yield f"{section_name}.{name}", value
    ownership = descriptor.get("ownership")
    if not isinstance(ownership, Mapping) or not isinstance(
        ownership.get("write_set"), list
    ):
        raise BenchmarkToolError("workspace ownership.write_set must be a list")
    for index, value in enumerate(ownership["write_set"]):
        if not isinstance(value, Mapping):
            raise BenchmarkToolError(f"workspace write_set[{index}] must be an object")
        yield f"ownership.write_set[{index}]", value


def _validate_descriptor_ownership(
    observed: Mapping[str, Any], expected: Mapping[str, Any]
) -> None:
    _validate_descriptor_anchors(observed, expected)

    expected_refs = dict(_iter_path_refs(expected))
    observed_refs = dict(_iter_path_refs(observed))
    if observed_refs.keys() != expected_refs.keys():
        raise BenchmarkToolError("workspace path binding set changed")
    roots = expected["roots"]
    for label, reference in observed_refs.items():
        root_name = reference.get("root")
        raw_path = reference.get("path")
        if root_name not in roots or not isinstance(raw_path, str):
            raise BenchmarkToolError(f"workspace {label} has an invalid root/path")
        relative = safe_relative_path(raw_path)
        if PurePosixPath(relative.as_posix()).as_posix() != raw_path:
            raise BenchmarkToolError(f"workspace {label} path is not canonical")
        if reference != expected_refs[label]:
            raise BenchmarkToolError(
                f"workspace {label} differs from its expected binding"
            )


def _validate_descriptor_anchors(
    observed: Mapping[str, Any], expected: Mapping[str, Any]
) -> None:
    if observed.get("schema_version") != SCHEMA_VERSION or observed.get("kind") != KIND:
        raise BenchmarkToolError("workspace descriptor schema/kind is invalid")
    if observed.get("paper_id") != expected["paper_id"]:
        raise BenchmarkToolError("workspace descriptor belongs to another paper")
    digest = observed.get("descriptor_sha256")
    if not isinstance(digest, str) or digest != descriptor_digest(observed):
        raise BenchmarkToolError("workspace descriptor self-hash is stale")
    if observed.get("roots") != expected["roots"]:
        raise BenchmarkToolError("workspace root bindings changed")
    observed_ownership = observed.get("ownership")
    expected_ownership = expected["ownership"]
    if not isinstance(observed_ownership, Mapping) or (
        observed_ownership.get("single_writer")
        != expected_ownership["single_writer"]
    ):
        raise BenchmarkToolError("workspace single_writer binding changed")
    observed_artifacts = observed.get("artifacts")
    expected_artifacts = expected["artifacts"]
    if not isinstance(observed_artifacts, Mapping) or (
        observed_artifacts.get("workspace_file")
        != expected_artifacts["workspace_file"]
    ):
        raise BenchmarkToolError("workspace descriptor path binding changed")


def _validate_pre_contract_upgrade(
    observed: Mapping[str, Any], expected: Mapping[str, Any]
) -> None:
    """Accept only the exact authenticated descriptor shape preceding contracts."""

    _validate_descriptor_anchors(observed, expected)
    legacy = copy.deepcopy(dict(expected))
    legacy.pop("generic_contract_files")
    legacy = _bind_descriptor_digest(legacy)
    pre_paper_record = copy.deepcopy(legacy)
    pre_paper_record["ownership"]["write_set"] = [
        reference
        for reference in pre_paper_record["ownership"]["write_set"]
        if reference.get("path") != f"tasks/{expected['paper_id']}/paper.json"
    ]
    pre_paper_record = _bind_descriptor_digest(pre_paper_record)
    if observed not in (legacy, pre_paper_record):
        raise BenchmarkToolError(
            "workspace descriptor is not an authentic pre-contract descriptor"
        )


def _read_workspace(path: Path) -> Mapping[str, Any]:
    if path.is_symlink() or not path.is_file():
        raise BenchmarkToolError(f"workspace descriptor is missing or unsafe: {path}")
    value = read_json(path)
    if not isinstance(value, Mapping):
        raise BenchmarkToolError("workspace descriptor must be a JSON object")
    return value


def _fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _atomic_write(path: Path, payload: bytes) -> bool:
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.is_symlink() or (path.exists() and not path.is_file()):
        raise BenchmarkToolError(f"workspace destination is unsafe: {path}")
    if path.exists() and path.read_bytes() == payload:
        return False
    temporary = path.with_name(f".{path.name}.tmp-{os.getpid()}-{uuid.uuid4().hex}")
    descriptor = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
        _fsync_directory(path.parent)
    except BaseException:
        if temporary.exists() and not temporary.is_symlink():
            temporary.unlink()
        raise
    return True


def manage_workspace(
    benchmark_root: Path,
    reference_root: Path,
    paper_id: str,
    *,
    scratch_root: Path | None = None,
    mode: str = "init",
) -> dict[str, Any]:
    if mode not in MODES:
        raise BenchmarkToolError(f"unsupported T4 workspace mode: {mode!r}")
    layout = _make_layout(benchmark_root, reference_root, scratch_root, paper_id)
    expected = build_workspace_descriptor(layout)
    workspace = layout.workspace_file
    result = {
        "ok": True,
        "mode": mode,
        "paper_id": paper_id,
        "task_id": f"{paper_id}-T4",
        "workspace": str(workspace),
        "descriptor_sha256": expected["descriptor_sha256"],
        "write_set": expected["ownership"]["write_set"],
        "written": [],
    }
    if mode == "write-set":
        return result
    if mode == "check":
        observed = _read_workspace(workspace)
        _validate_descriptor_ownership(observed, expected)
        if observed != expected:
            raise BenchmarkToolError(
                f"workspace descriptor is stale for {paper_id}; rerun init"
            )
        return result

    if workspace.exists() or workspace.is_symlink():
        observed = _read_workspace(workspace)
        if "generic_contract_files" not in observed:
            _validate_pre_contract_upgrade(observed, expected)
        else:
            _validate_descriptor_ownership(observed, expected)
    if _atomic_write(workspace, _canonical_json_bytes(expected)):
        result["written"] = [str(workspace)]
    return result


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", nargs="?", choices=MODES, default="init")
    parser.add_argument(
        "--benchmark-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
    )
    parser.add_argument("--reference-root", type=Path, required=True)
    parser.add_argument("--scratch-root", type=Path)
    parser.add_argument("--paper-id", required=True)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = make_parser().parse_args(argv)
    try:
        result = manage_workspace(
            args.benchmark_root,
            args.reference_root,
            args.paper_id,
            scratch_root=args.scratch_root,
            mode=args.mode,
        )
    except (BenchmarkToolError, OSError, ValueError) as error:
        print(f"t4-workspace error: {error}", file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
