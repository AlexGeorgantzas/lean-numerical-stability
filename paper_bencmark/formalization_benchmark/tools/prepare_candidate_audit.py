#!/usr/bin/env python3
"""Prepare a pseudonymized semantic dossier for one generated candidate.

The control-side raw extraction is written only to a private manifest.  Audit
roles receive ``blind_semantic_dossier.json`` exclusively; that artifact omits
the candidate module inventory and replaces every reached Candidate or
NumStability declaration and owner module with deterministic neutral IDs.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
from typing import Any, Mapping, Sequence

try:
    from .formalization_validator import (
        DEFAULT_COMPILER_COMMAND,
        DEFAULT_MAX_SOURCE_BYTES,
        DEFAULT_TIMEOUT_SECONDS,
        TARGET_DECLARATION,
        ValidationInfrastructureError,
        canonical_json,
        compiled_candidate_workspace,
        inspect_candidate_source,
        parse_command_json,
        read_candidate_bytes,
        run_bounded_command,
        sha256_bytes,
        write_json_atomic,
    )
except ImportError:  # Direct script execution.
    from formalization_validator import (  # type: ignore
        DEFAULT_COMPILER_COMMAND,
        DEFAULT_MAX_SOURCE_BYTES,
        DEFAULT_TIMEOUT_SECONDS,
        TARGET_DECLARATION,
        ValidationInfrastructureError,
        canonical_json,
        compiled_candidate_workspace,
        inspect_candidate_source,
        parse_command_json,
        read_candidate_bytes,
        run_bounded_command,
        sha256_bytes,
        write_json_atomic,
    )


BLIND_SCHEMA_VERSION = "candidate-semantic-dossier-1"
PRIVATE_SCHEMA_VERSION = "candidate-semantic-private-1"
RESULT_SCHEMA_VERSION = "candidate-audit-preparation-result-1"
TARGET_MODULE = "Candidate"
DEFAULT_RECURSIVE_PREFIXES = ("NumStability",)
MAX_EXTRACTOR_OUTPUT_BYTES = 16 * 1024 * 1024
MAX_EXTRACTOR_REPORT_LINES = 100_000
MAX_BLIND_DOSSIER_BYTES = 32 * 1024 * 1024
MAX_PRIVATE_DOSSIER_BYTES = 64 * 1024 * 1024
HELPER = Path(__file__).resolve().with_name("declaration_dossier.lean")
DEFAULT_EXTRACTOR_COMMAND = (
    "lean",
    "--run",
    "{helper}",
    TARGET_MODULE,
    TARGET_DECLARATION,
    "{prefixes}",
)


class CandidateAuditError(RuntimeError):
    """Candidate or infrastructure failure while preparing an audit dossier."""

    def __init__(self, failure_code: str, message: str):
        super().__init__(message)
        self.failure_code = failure_code


def _unescape_field(value: str) -> str:
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
    """Parse and strictly validate format-2 output from the Lean helper."""

    format_version: str | None = None
    target_name: str | None = None
    target_readable: str | None = None
    target_explicit: str | None = None
    environment_modules: list[str] = []
    dependencies: list[dict[str, Any]] = []
    edges: list[dict[str, str]] = []
    summary: tuple[int, int] | None = None

    for line_number, raw_line in enumerate(output.splitlines(), start=1):
        if line_number > MAX_EXTRACTOR_REPORT_LINES:
            raise CandidateAuditError(
                "INFRASTRUCTURE_FAILURE", "semantic extractor report has too many entries"
            )
        if not raw_line:
            continue
        fields = [_unescape_field(field) for field in raw_line.split("\t")]
        tag = fields[0]
        try:
            if tag == "format" and len(fields) == 2:
                if format_version is not None:
                    raise ValueError("duplicate format row")
                format_version = fields[1]
            elif tag == "target" and len(fields) == 2:
                if target_name is not None:
                    raise ValueError("duplicate target row")
                target_name = fields[1]
            elif tag == "target-readable" and len(fields) == 2:
                if target_readable is not None:
                    raise ValueError("duplicate target-readable row")
                target_readable = fields[1]
            elif tag == "target-explicit" and len(fields) == 2:
                if target_explicit is not None:
                    raise ValueError("duplicate target-explicit row")
                target_explicit = fields[1]
            elif tag == "environment-module" and len(fields) == 2:
                environment_modules.append(fields[1])
            elif tag == "dependency" and len(fields) == 10:
                role = fields[1]
                if role not in {"local", "external-frontier"}:
                    raise ValueError(f"invalid dependency role {role!r}")
                distance = int(fields[4])
                if distance < 1:
                    raise ValueError("dependency distance must be positive")
                dependencies.append(
                    {
                        "role": role,
                        "name": fields[2],
                        "owner_module": fields[3],
                        "distance": distance,
                        "kind": fields[5],
                        "type_readable": fields[6],
                        "type_explicit": fields[7],
                        "body_readable": fields[8],
                        "body_explicit": fields[9],
                    }
                )
            elif tag == "edge" and len(fields) == 4:
                if fields[3] not in {"type", "body", "constructor"}:
                    raise ValueError(f"invalid edge origin {fields[3]!r}")
                edges.append(
                    {"parent": fields[1], "child": fields[2], "origin": fields[3]}
                )
            elif tag == "summary" and len(fields) == 3:
                if summary is not None:
                    raise ValueError("duplicate summary row")
                summary = (int(fields[1]), int(fields[2]))
            else:
                raise ValueError(f"unknown or malformed row {tag!r}")
        except ValueError as error:
            raise CandidateAuditError(
                "INFRASTRUCTURE_FAILURE",
                f"malformed Lean dossier output at line {line_number}: {error}",
            ) from error

    if format_version != "2":
        raise CandidateAuditError(
            "INFRASTRUCTURE_FAILURE",
            f"expected Lean dossier format 2, got {format_version!r}",
        )
    if target_name != TARGET_DECLARATION:
        raise CandidateAuditError(
            "INFRASTRUCTURE_FAILURE",
            f"Lean dossier reported unexpected target {target_name!r}",
        )
    if target_readable is None or target_explicit is None:
        raise CandidateAuditError(
            "INFRASTRUCTURE_FAILURE", "Lean dossier omitted the target type"
        )
    if summary != (len(dependencies), len(edges)):
        raise CandidateAuditError(
            "INFRASTRUCTURE_FAILURE",
            "Lean dossier summary does not match its dependency and edge rows",
        )
    dependency_names = [item["name"] for item in dependencies]
    if len(set(dependency_names)) != len(dependency_names):
        raise CandidateAuditError(
            "INFRASTRUCTURE_FAILURE", "Lean dossier contains duplicate dependencies"
        )
    known_names = {TARGET_DECLARATION, *dependency_names}
    for edge in edges:
        if edge["parent"] not in known_names or edge["child"] not in known_names:
            raise CandidateAuditError(
                "INFRASTRUCTURE_FAILURE",
                f"Lean dossier edge references an unknown declaration: {edge}",
            )
    for index, dependency in enumerate(dependencies, start=1):
        dependency["id"] = f"D{index:03d}"
    return {
        "target_name": target_name,
        "target_type_readable": target_readable,
        "target_type_explicit": target_explicit,
        "environment_modules": environment_modules,
        "dependencies": dependencies,
        "edges": edges,
    }


def _module_has_prefix(module: str, prefix: str) -> bool:
    return module == prefix or module.startswith(prefix + ".")


def _validate_local_roles(raw: Mapping[str, Any], recursive_prefixes: Sequence[str]) -> None:
    for dependency in raw["dependencies"]:
        expected_local = dependency["owner_module"] == TARGET_MODULE or any(
            _module_has_prefix(dependency["owner_module"], prefix)
            for prefix in recursive_prefixes
        )
        if (dependency["role"] == "local") != expected_local:
            raise CandidateAuditError(
                "INFRASTRUCTURE_FAILURE",
                "Lean dossier assigned an inconsistent recursive-closure role",
            )


_IDENTIFIER_EDGE = r"A-Za-z0-9_\u0080-\U0010ffff'"


def _replace_full_names(value: str, replacements: Mapping[str, str]) -> str:
    for original in sorted(replacements, key=len, reverse=True):
        pattern = re.compile(
            rf"(?<![{_IDENTIFIER_EDGE}.]){re.escape(original)}(?![{_IDENTIFIER_EDGE}])"
        )
        value = pattern.sub(replacements[original], value)
    return value


def _replace_short_names(value: str, replacements: Mapping[str, str]) -> str:
    for original in sorted(replacements, key=len, reverse=True):
        pattern = re.compile(
            rf"(?<![{_IDENTIFIER_EDGE}.]){re.escape(original)}(?![{_IDENTIFIER_EDGE}.])"
        )
        value = pattern.sub(replacements[original], value)
    return value


def _contains_lean_name(value: str, name: str) -> bool:
    pattern = re.compile(
        rf"(?<![{_IDENTIFIER_EDGE}.]){re.escape(name)}(?![{_IDENTIFIER_EDGE}])"
    )
    return pattern.search(value) is not None


def _blind_expression(
    value: str,
    full_names: Mapping[str, str],
    short_names: Mapping[str, str],
    sensitive_modules: Sequence[str],
) -> str:
    rendered = _replace_full_names(value, full_names)
    rendered = _replace_short_names(rendered, short_names)
    leaked = [name for name in full_names if _contains_lean_name(rendered, name)]
    leaked.extend(
        module
        for module in sensitive_modules
        if _contains_lean_name(rendered, module)
    )
    if leaked:
        raise CandidateAuditError(
            "INFRASTRUCTURE_FAILURE",
            "pseudonymization left local declaration or module provenance in an expression",
        )
    return rendered


def _semantic_hash(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode("utf-8")).hexdigest()


def build_blind_dossier(raw: Mapping[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
    """Return an auditor-safe dossier and a private pseudonym map."""

    local_dependencies = [
        dependency for dependency in raw["dependencies"] if dependency["role"] == "local"
    ]
    full_name_map = {
        dependency["name"]: f"LocalDef{index:03d}"
        for index, dependency in enumerate(local_dependencies, start=1)
    }
    local_modules = sorted({item["owner_module"] for item in local_dependencies})
    # Deliberately many-to-one: preserving how many local owner modules exist
    # would let an auditor infer that a candidate used the treatment library.
    module_map = {module: "LOCAL" for module in local_modules}

    all_basenames: dict[str, int] = {}
    for dependency in raw["dependencies"]:
        basename = dependency["name"].rsplit(".", 1)[-1]
        all_basenames[basename] = all_basenames.get(basename, 0) + 1
    short_name_map = {
        dependency["name"].rsplit(".", 1)[-1]: full_name_map[dependency["name"]]
        for dependency in local_dependencies
        if all_basenames[dependency["name"].rsplit(".", 1)[-1]] == 1
    }
    expression_name_map = {TARGET_DECLARATION: "TARGET", **full_name_map}
    sensitive_modules = [
        "HighamBenchCandidate",
        "HighamBench",
        "NumStability",
        TARGET_MODULE,
        *local_modules,
    ]

    def blind_expression(value: str) -> str:
        return _blind_expression(
            value, expression_name_map, short_name_map, sensitive_modules
        )

    dependencies: list[dict[str, Any]] = []
    for dependency in raw["dependencies"]:
        local = dependency["role"] == "local"
        rendered = {
            "id": dependency["id"],
            "role": dependency["role"],
            "name": (
                full_name_map[dependency["name"]]
                if local
                else dependency["name"]
            ),
            "owner_module": (
                module_map[dependency["owner_module"]]
                if local
                else dependency["owner_module"]
            ),
            "distance": dependency["distance"],
            "kind": dependency["kind"],
            "type_readable": blind_expression(dependency["type_readable"]),
            "type_explicit": blind_expression(dependency["type_explicit"]),
            "body_readable": blind_expression(dependency["body_readable"]),
            "body_explicit": blind_expression(dependency["body_explicit"]),
        }
        rendered["semantic_sha256"] = _semantic_hash(
            {
                key: rendered[key]
                for key in (
                    "role",
                    "name",
                    "owner_module",
                    "kind",
                    "type_explicit",
                    "body_explicit",
                )
            }
        )
        dependencies.append(rendered)

    edge_name_map = {TARGET_DECLARATION: "TARGET", **full_name_map}
    edges = [
        {
            "parent": edge_name_map.get(edge["parent"], edge["parent"]),
            "child": edge_name_map.get(edge["child"], edge["child"]),
            "origin": edge["origin"],
        }
        for edge in raw["edges"]
    ]
    target = {
        "name": "TARGET",
        "type_readable": blind_expression(raw["target_type_readable"]),
        "type_explicit": blind_expression(raw["target_type_explicit"]),
    }
    semantic_core = {
        "schema_version": "candidate-semantic-core-1",
        "target_type_explicit": target["type_explicit"],
        "dependencies": [
            {
                key: dependency[key]
                for key in (
                    "id",
                    "role",
                    "name",
                    "owner_module",
                    "kind",
                    "type_explicit",
                    "body_explicit",
                )
            }
            for dependency in dependencies
        ],
        "edges": edges,
    }
    semantic_sha256 = _semantic_hash(semantic_core)
    blind = {
        "schema_version": BLIND_SCHEMA_VERSION,
        "semantic_sha256": semantic_sha256,
        "target": target,
        "closure_policy": {
            "root": "target type only; target proof excluded",
            "recursive": "generated and treatment-library declaration types and bodies",
            "frontier": "other Lean/Mathlib declarations with one-level type and body",
        },
        "dependencies": dependencies,
        "edges": edges,
        "summary": {
            "dependency_count": len(dependencies),
            "edge_count": len(edges),
            "local_definition_count": len(local_dependencies),
        },
    }
    private_map = {
        "target": {TARGET_DECLARATION: "TARGET"},
        "declarations": full_name_map,
        "modules": module_map,
        "unqualified_display_names": short_name_map,
    }
    return blind, private_map


def _expand_command(command: Sequence[str], values: Mapping[str, str]) -> list[str]:
    try:
        return [argument.format_map(values) for argument in command]
    except KeyError as error:
        raise CandidateAuditError(
            "INFRASTRUCTURE_FAILURE",
            f"unknown extractor-command placeholder: {error.args[0]}",
        ) from error


def _run_extractor(
    workspace: Path,
    prefixes_file: Path,
    *,
    extractor_command: Sequence[str],
    extractor_cwd: Path | None,
    extractor_environment: Mapping[str, str] | None,
    timeout_seconds: float,
) -> tuple[str, dict[str, Any]]:
    values = {
        "helper": str(HELPER),
        "workspace": str(workspace),
        "prefixes": str(prefixes_file),
    }
    expanded = _expand_command(extractor_command, values)
    environment = os.environ.copy()
    if extractor_environment:
        environment.update(extractor_environment)
    inherited_lean_path = environment.get("LEAN_PATH", "")
    environment["LEAN_PATH"] = str(workspace) + (
        os.pathsep + inherited_lean_path if inherited_lean_path else ""
    )
    try:
        completed = run_bounded_command(
            expanded,
            cwd=extractor_cwd or workspace,
            environment=environment,
            timeout_seconds=timeout_seconds,
            maximum_output_bytes=MAX_EXTRACTOR_OUTPUT_BYTES,
        )
    except FileNotFoundError as error:
        raise CandidateAuditError(
            "INFRASTRUCTURE_FAILURE", f"extractor executable not found: {expanded[0]}"
        ) from error
    if completed["timed_out"]:
        raise CandidateAuditError(
            "INFRASTRUCTURE_FAILURE",
            f"semantic extractor exceeded {timeout_seconds:g} seconds",
        )
    if completed["output_limit_exceeded"]:
        raise CandidateAuditError(
            "INFRASTRUCTURE_FAILURE",
            f"semantic extractor output exceeded {MAX_EXTRACTOR_OUTPUT_BYTES} bytes",
        )
    if completed["resource_cgroup_join_failed"]:
        raise CandidateAuditError(
            "INFRASTRUCTURE_FAILURE",
            "semantic extractor could not enter the validation resource cgroup",
        )
    if completed["resource_limit_exceeded"]:
        raise CandidateAuditError(
            "INFRASTRUCTURE_FAILURE",
            "semantic extractor reached a validation resource ceiling",
        )
    output = completed["output"]
    metadata = {
        "pass": completed["returncode"] == 0,
        "returncode": completed["returncode"],
        "command_template": list(extractor_command),
        "output_sha256": completed["output_sha256"],
        "output_bytes_observed": completed["output_bytes_observed"],
        "output_limit_bytes": completed["output_limit_bytes"],
        "resource_limit_event_delta": completed["resource_limit_event_delta"],
    }
    if completed["returncode"] != 0:
        raise CandidateAuditError(
            "INFRASTRUCTURE_FAILURE",
            f"semantic extractor failed ({completed['returncode']}): {output[-4000:]}",
        )
    return output, metadata


def prepare_candidate_audit(
    candidate: Path,
    *,
    compiler_command: Sequence[str] = DEFAULT_COMPILER_COMMAND,
    extractor_command: Sequence[str] = DEFAULT_EXTRACTOR_COMMAND,
    compiler_cwd: Path | None = None,
    extractor_cwd: Path | None = None,
    compiler_environment: Mapping[str, str] | None = None,
    extractor_environment: Mapping[str, str] | None = None,
    scratch_root: Path | None = None,
    timeout_seconds: float = DEFAULT_TIMEOUT_SECONDS,
    max_source_bytes: int = DEFAULT_MAX_SOURCE_BYTES,
    recursive_prefixes: Sequence[str] = DEFAULT_RECURSIVE_PREFIXES,
    allow_single_target_sorry: bool = False,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Compile, extract, and blind one candidate; return blind and private JSON."""

    try:
        candidate_bytes = read_candidate_bytes(candidate, max_source_bytes)
    except (OSError, ValueError) as error:
        raise CandidateAuditError("RULE_VIOLATION", str(error)) from error
    source_check = inspect_candidate_source(
        candidate_bytes.decode("utf-8"),
        allow_single_target_sorry=allow_single_target_sorry,
    )
    if not source_check["pass"]:
        raise CandidateAuditError(
            "RULE_VIOLATION",
            "candidate does not satisfy the formalization source contract: "
            + canonical_json(source_check["issues"]),
        )
    if not HELPER.is_file():
        raise CandidateAuditError(
            "INFRASTRUCTURE_FAILURE", f"missing Lean dossier helper: {HELPER}"
        )
    if not recursive_prefixes or any(
        not isinstance(prefix, str) or not prefix for prefix in recursive_prefixes
    ):
        raise CandidateAuditError(
            "INFRASTRUCTURE_FAILURE", "recursive module prefixes must be nonempty strings"
        )

    try:
        with compiled_candidate_workspace(
            candidate_bytes,
            compiler_command=compiler_command,
            compiler_cwd=compiler_cwd,
            compiler_environment=compiler_environment,
            scratch_root=scratch_root,
            timeout_seconds=timeout_seconds,
        ) as (workspace, compile_result):
            if not compile_result["pass"]:
                raise CandidateAuditError(
                    "COMPILATION_FAILURE",
                    f"candidate compilation failed: {compile_result['output'][-4000:]}",
                )
            prefixes_file = workspace / "recursive-prefixes.txt"
            prefixes_file.write_text("\n".join(recursive_prefixes) + "\n", encoding="utf-8")
            raw_output, extractor_metadata = _run_extractor(
                workspace,
                prefixes_file,
                extractor_command=extractor_command,
                extractor_cwd=extractor_cwd,
                extractor_environment=extractor_environment,
                timeout_seconds=timeout_seconds,
            )
            raw = parse_lean_report(raw_output)
    except ValidationInfrastructureError as error:
        raise CandidateAuditError("INFRASTRUCTURE_FAILURE", str(error)) from error

    _validate_local_roles(raw, recursive_prefixes)
    blind, pseudonyms = build_blind_dossier(raw)
    private_without_hash = {
        "schema_version": PRIVATE_SCHEMA_VERSION,
        "candidate": {
            "basename": "Candidate.lean",
            "sha256": sha256_bytes(candidate_bytes),
            "bytes": len(candidate_bytes),
        },
        "target_declaration": TARGET_DECLARATION,
        "source_contract": source_check["source_contract"],
        "recursive_module_prefixes": list(recursive_prefixes),
        "compile": compile_result,
        "extractor": extractor_metadata,
        "raw_semantic_report": raw,
        "pseudonyms": pseudonyms,
        "blind_semantic_sha256": blind["semantic_sha256"],
    }
    private = {
        **private_without_hash,
        "private_payload_sha256": _semantic_hash(private_without_hash),
    }
    blind_bytes = canonical_json(blind).encode("utf-8")
    private_bytes = canonical_json(private).encode("utf-8")
    if len(blind_bytes) > MAX_BLIND_DOSSIER_BYTES or len(private_bytes) > MAX_PRIVATE_DOSSIER_BYTES:
        raise CandidateAuditError(
            "INFRASTRUCTURE_FAILURE", "semantic dossier exceeds its frozen byte ceiling"
        )
    return blind, private


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidate", type=Path, help="path to Candidate.lean")
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument(
        "--compiler-command-json",
        type=parse_command_json,
        default=DEFAULT_COMPILER_COMMAND,
        help="JSON argv array supporting {candidate}, {olean}, and {workspace}",
    )
    parser.add_argument(
        "--extractor-command-json",
        type=parse_command_json,
        default=DEFAULT_EXTRACTOR_COMMAND,
        help="JSON argv array supporting {helper}, {workspace}, and {prefixes}",
    )
    parser.add_argument("--compiler-cwd", type=Path)
    parser.add_argument("--extractor-cwd", type=Path)
    parser.add_argument("--scratch-root", type=Path)
    parser.add_argument(
        "--timeout-seconds", type=float, default=DEFAULT_TIMEOUT_SECONDS
    )
    parser.add_argument(
        "--max-source-bytes", type=int, default=DEFAULT_MAX_SOURCE_BYTES
    )
    parser.add_argument(
        "--recursive-module-prefix",
        action="append",
        dest="recursive_prefixes",
        help="module prefix whose reached declarations are recursively expanded",
    )
    parser.add_argument(
        "--allow-single-target-sorry",
        action="store_true",
        help="prepare a statement-only candidate whose final target proof is exactly sorry",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = make_parser().parse_args(argv)
    try:
        if args.output_dir.exists():
            if not args.output_dir.is_dir() or args.output_dir.is_symlink():
                raise OSError("output directory is not a regular directory")
        else:
            args.output_dir.mkdir(parents=True, mode=0o700)
    except OSError as error:
        result = {
            "schema_version": RESULT_SCHEMA_VERSION,
            "pass": False,
            "failure_code": "INFRASTRUCTURE_FAILURE",
            "error": f"cannot create safe output directory: {error}",
        }
        print(json.dumps(result, indent=2, sort_keys=True))
        return 2
    blind_path = args.output_dir / "blind_semantic_dossier.json"
    private_path = args.output_dir / "private_semantic_manifest.json"
    if blind_path.exists() or private_path.exists():
        result = {
            "schema_version": RESULT_SCHEMA_VERSION,
            "pass": False,
            "failure_code": "INFRASTRUCTURE_FAILURE",
            "error": "refusing to overwrite an existing candidate audit dossier",
        }
        print(json.dumps(result, indent=2, sort_keys=True))
        return 2
    try:
        blind, private = prepare_candidate_audit(
            args.candidate,
            compiler_command=args.compiler_command_json,
            extractor_command=args.extractor_command_json,
            compiler_cwd=args.compiler_cwd,
            extractor_cwd=args.extractor_cwd,
            scratch_root=args.scratch_root,
            timeout_seconds=args.timeout_seconds,
            max_source_bytes=args.max_source_bytes,
            recursive_prefixes=(
                tuple(args.recursive_prefixes)
                if args.recursive_prefixes
                else DEFAULT_RECURSIVE_PREFIXES
            ),
            allow_single_target_sorry=args.allow_single_target_sorry,
        )
        write_json_atomic(private_path, private)
        # Publish the only auditor-visible artifact last, after its private
        # provenance record is durable.
        write_json_atomic(blind_path, blind)
        os.chmod(private_path, 0o400, follow_symlinks=False)
        os.chmod(blind_path, 0o400, follow_symlinks=False)
    except CandidateAuditError as error:
        result = {
            "schema_version": RESULT_SCHEMA_VERSION,
            "pass": False,
            "failure_code": error.failure_code,
            "error": str(error),
        }
        print(json.dumps(result, indent=2, sort_keys=True))
        return 1 if error.failure_code in {"RULE_VIOLATION", "COMPILATION_FAILURE"} else 2
    result = {
        "schema_version": RESULT_SCHEMA_VERSION,
        "pass": True,
        "candidate_sha256": private["candidate"]["sha256"],
        "semantic_sha256": blind["semantic_sha256"],
        "blind_output": str(blind_path),
        "blind_output_sha256": sha256_bytes(blind_path.read_bytes()),
        "private_output": str(private_path),
        "private_output_sha256": sha256_bytes(private_path.read_bytes()),
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
