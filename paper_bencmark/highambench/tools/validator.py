#!/usr/bin/env python3
"""Validate one HighamBench proof in a fresh hidden workspace copy."""

from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import json
import os
from pathlib import Path
import re
import shutil
import tempfile
from typing import Any, Iterable, Sequence
import uuid

try:
    from .common import (
        BenchmarkToolError,
        command_display,
        parse_command_json,
        render_command,
        resolve_below,
        run_captured,
        truncate_text,
        write_json,
    )
    from .hashes import load_manifest, verify_manifest
except ImportError:  # Direct script execution.
    from common import (  # type: ignore
        BenchmarkToolError,
        command_display,
        parse_command_json,
        render_command,
        resolve_below,
        run_captured,
        truncate_text,
        write_json,
    )
    from hashes import load_manifest, verify_manifest  # type: ignore


LEAN_NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")
IMPORT_RE = re.compile(
    r"(?m)^\s*(?:(?:public|private|meta)\s+)*import\s+([A-Za-z0-9_'.]+)\s*$"
)
FORBIDDEN_TOKEN_PATTERNS = (
    ("sorry", re.compile(r"\bsorry\b")),
    ("admit", re.compile(r"\badmit\b")),
    ("sorryAx", re.compile(r"\bsorryAx\b")),
    ("axiom declaration", re.compile(r"\baxiom\b")),
    ("constant declaration", re.compile(r"\bconstant\b")),
    ("unsafe declaration or command", re.compile(r"\bunsafe\b")),
    # Opaque declarations with bodies are kernel-checked, but forbidding task-local
    # opacity makes an omitted body or hidden-proof workaround impossible.
    ("opaque declaration", re.compile(r"\bopaque\b")),
)
LOCAL_MODULES_FILENAME = ".highambench-validator-local-modules"


def sanitize_lean(text: str, *, erase_strings: bool = False) -> str:
    """Erase nested comments, and optionally strings, while preserving offsets."""

    output: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    escaped = False
    while index < len(text):
        pair = text[index : index + 2]
        char = text[index]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                output.extend("  ")
                index += 2
            elif pair == "-/":
                block_depth -= 1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if in_string:
            output.append(char if not erase_strings else ("\n" if char == "\n" else " "))
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if pair == "/-":
            block_depth = 1
            output.extend("  ")
            index += 2
        elif pair == "--":
            newline = text.find("\n", index + 2)
            if newline == -1:
                output.extend(" " * (len(text) - index))
                break
            output.extend(" " * (newline - index))
            output.append("\n")
            index = newline + 1
        else:
            output.append(char)
            if char == '"':
                in_string = True
            index += 1
    return "".join(output)


def extract_imports(text: str) -> list[str]:
    return IMPORT_RE.findall(sanitize_lean(text, erase_strings=True))


def forbidden_source_findings(path: Path, forbidden_import_prefixes: Sequence[str]) -> list[dict[str, Any]]:
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as error:
        return [{"path": str(path), "kind": "unreadable_source", "detail": str(error)}]
    sanitized = sanitize_lean(text, erase_strings=True)
    findings: list[dict[str, Any]] = []
    for label, pattern in FORBIDDEN_TOKEN_PATTERNS:
        match = pattern.search(sanitized)
        if match:
            line = sanitized.count("\n", 0, match.start()) + 1
            findings.append({"path": str(path), "kind": label, "line": line})
    imports = extract_imports(text)
    for imported in imports:
        for prefix in forbidden_import_prefixes:
            if imported == prefix or imported.startswith(prefix + "."):
                findings.append(
                    {
                        "path": str(path),
                        "kind": "forbidden import",
                        "import": imported,
                        "prefix": prefix,
                    }
                )
    return findings


def _workspace_relative(workspace: Path, path: Path) -> str:
    return path.relative_to(workspace).as_posix()


def _module_name_from_relative_source(relative: Path) -> str | None:
    parts = relative.with_suffix("").parts
    if not parts or not all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", part) for part in parts):
        return None
    return ".".join(parts)


def _path_parts_end_with(path: Path, suffix: Path) -> bool:
    path_parts = path.parts
    suffix_parts = suffix.parts
    return len(suffix_parts) <= len(path_parts) and path_parts[-len(suffix_parts) :] == suffix_parts


def controlled_module_identities(
    controlled_root: Path,
    manifest: dict[str, Any] | None,
) -> set[str]:
    """Return module names that candidate files must never redefine.

    A controlled source can sit below a source-root directory such as
    ``shared/``.  Every valid suffix is protected, and direct imports are
    protected too.  Trusted search paths are also placed before the candidate
    workspace, but this explicit rejection makes the rule independently
    auditable and prevents forged ownership records.
    """

    if manifest is None:
        return set()
    modules: set[str] = set()
    for entry in manifest["files"]:
        relative = Path(entry["path"])
        if relative.suffix != ".lean":
            continue
        parts = relative.with_suffix("").parts
        for start in range(len(parts)):
            suffix = parts[start:]
            if suffix and all(
                re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", part) for part in suffix
            ):
                modules.add(".".join(suffix))
        source = resolve_below(controlled_root, entry["path"])
        try:
            modules.update(extract_imports(source.read_text(encoding="utf-8")))
        except (OSError, UnicodeDecodeError):
            # Manifest verification and the later hidden copy still diagnose
            # an unreadable controlled file as a system failure.
            continue
    return modules


def inventory_candidate_lean(
    workspace: Path,
    controlled_root: Path,
    manifest: dict[str, Any] | None,
) -> dict[str, Any]:
    """Inventory candidate Lean artifacts without scanning released task files.

    The isolated runner mounts dependencies outside the workspace and stages all
    released task files through the controlled manifest. Therefore every other
    local ``.lean`` or ``.olean`` file is candidate-created. Exact manifest
    paths, rather than the whole controlled directory, are excluded so an extra
    file placed beside a released file cannot hide from this scan.
    """

    workspace = workspace.resolve()
    controlled_paths: set[Path] = set()
    if manifest is not None:
        controlled_paths = {
            resolve_below(controlled_root, entry["path"]) for entry in manifest["files"]
        }

    sources: list[Path] = []
    oleans: list[Path] = []
    findings: list[dict[str, Any]] = []

    def walk_error(error: OSError) -> None:
        filename = str(error.filename) if error.filename else str(workspace)
        findings.append(
            {
                "path": filename,
                "kind": "unreadable candidate directory",
                "detail": str(error),
            }
        )

    for directory, directory_names, file_names in os.walk(
        workspace, followlinks=False, onerror=walk_error
    ):
        base = Path(directory)
        retained_directories: list[str] = []
        for name in directory_names:
            path = base / name
            if path.is_symlink():
                findings.append(
                    {
                        "path": _workspace_relative(workspace, path),
                        "kind": "candidate symlink",
                        "detail": "symlinked directories can conceal unchecked Lean sources",
                    }
                )
                continue
            retained_directories.append(name)
        directory_names[:] = retained_directories

        for name in file_names:
            path = base / name
            if path.is_symlink():
                findings.append(
                    {
                        "path": _workspace_relative(workspace, path),
                        "kind": "candidate symlink",
                        "detail": "symlinked files are not accepted as candidate artifacts",
                    }
                )
                continue
            resolved = path.resolve()
            if resolved in controlled_paths:
                continue
            if path.suffix == ".lean":
                sources.append(path)
            elif path.suffix == ".olean":
                oleans.append(path)

    sources.sort(key=lambda path: _workspace_relative(workspace, path))
    oleans.sort(key=lambda path: _workspace_relative(workspace, path))
    source_stems = {path.relative_to(workspace).with_suffix("") for path in sources}
    for olean in oleans:
        olean_stem = olean.relative_to(workspace).with_suffix("")
        if olean_stem not in source_stems:
            findings.append(
                {
                    "path": _workspace_relative(workspace, olean),
                    "kind": "candidate olean without scanned source",
                    "detail": (
                        "candidate-created compiled Lean modules require a source file "
                        "with the exact same workspace-relative module path"
                    ),
                }
            )

    modules: set[str] = set()
    source_by_stem = {
        path.relative_to(workspace).with_suffix(""): path for path in sources
    }
    for source in sources:
        module_name = _module_name_from_relative_source(source.relative_to(workspace))
        if module_name is not None:
            modules.add(module_name)
    # A workspace may expose a source root below its top directory. Imports
    # reveal the actual module name in that case, so retain any imported name
    # whose path matches the end of a scanned candidate source path.
    for source in sources:
        try:
            imports = extract_imports(source.read_text(encoding="utf-8"))
        except (OSError, UnicodeDecodeError):
            continue
        for imported in imports:
            imported_path = Path(*imported.split("."))
            if any(_path_parts_end_with(stem, imported_path) for stem in source_by_stem):
                modules.add(imported)

    return {
        "controlled_file_count": len(controlled_paths),
        "scanned_sources": [
            _workspace_relative(workspace, path) for path in sources
        ],
        "candidate_oleans": [
            _workspace_relative(workspace, path) for path in oleans
        ],
        "local_modules": sorted(modules),
        "findings": findings,
    }


def _simple_target_name(target_theorem: str) -> str:
    if not LEAN_NAME_RE.fullmatch(target_theorem):
        raise BenchmarkToolError(f"unsupported Lean theorem name: {target_theorem!r}")
    return target_theorem.rsplit(".", 1)[-1]


def extract_theorem_signature(text: str, target_theorem: str) -> str:
    """Extract a whitespace-normalized declaration header through its top-level `:=`."""

    simple_name = re.escape(_simple_target_name(target_theorem))
    sanitized = sanitize_lean(text, erase_strings=False)
    pattern = re.compile(rf"(?m)^\s*(?:theorem|lemma)\s+{simple_name}\b")
    matches = list(pattern.finditer(sanitized))
    if len(matches) != 1:
        raise BenchmarkToolError(
            f"expected exactly one theorem/lemma named {_simple_target_name(target_theorem)!r}; "
            f"found {len(matches)}"
        )
    start = matches[0].start()
    index = matches[0].end()
    depths = {"(": 0, "[": 0, "{": 0}
    closing = {")": "(", "]": "[", "}": "{"}
    delimiter: int | None = None
    while index < len(sanitized) - 1:
        char = sanitized[index]
        if char in depths:
            depths[char] += 1
        elif char in closing:
            opener = closing[char]
            depths[opener] = max(0, depths[opener] - 1)
        elif sanitized[index : index + 2] == ":=" and all(value == 0 for value in depths.values()):
            delimiter = index
            break
        index += 1
    if delimiter is None:
        raise BenchmarkToolError(f"could not find top-level `:=` for {target_theorem}")
    signature = sanitized[start:delimiter]
    return re.sub(r"\s+", " ", signature).strip()


def compare_target_signature(
    submission: Path,
    canonical_source: Path,
    target_theorem: str,
) -> dict[str, Any]:
    try:
        submitted = extract_theorem_signature(
            submission.read_text(encoding="utf-8"), target_theorem
        )
        canonical = extract_theorem_signature(
            canonical_source.read_text(encoding="utf-8"), target_theorem
        )
    except (OSError, UnicodeDecodeError, BenchmarkToolError) as error:
        return {"ok": False, "error": str(error)}
    return {
        "ok": submitted == canonical,
        "submitted": submitted,
        "canonical": canonical,
    }


def renamed_canonical_source(
    text: str, target_theorem: str, expected_simple_name: str
) -> str:
    """Rename only the frozen theorem declaration, preserving its trusted syntax."""

    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", expected_simple_name):
        raise BenchmarkToolError("invalid generated expected theorem name")
    simple_name = re.escape(_simple_target_name(target_theorem))
    sanitized = sanitize_lean(text, erase_strings=False)
    pattern = re.compile(
        rf"(?m)^\s*(?:theorem|lemma)\s+(?P<name>{simple_name})\b"
    )
    matches = list(pattern.finditer(sanitized))
    if len(matches) != 1:
        raise BenchmarkToolError(
            f"expected exactly one canonical declaration for {target_theorem}; "
            f"found {len(matches)}"
        )
    match = matches[0]
    return text[: match.start("name")] + expected_simple_name + text[match.end("name") :]


def classify_lean_failure(output: str) -> str:
    lowered = output.lower()
    syntax_or_elab_markers = (
        "unexpected token",
        "unexpected end of input",
        "unknown identifier",
        "unknown constant",
        "unknown namespace",
        "unknown module",
        "failed to synthesize",
        "invalid field notation",
        "invalid 'end'",
        "declaration name expected",
        "application type mismatch",
    )
    proof_markers = (
        "unsolved goals",
        "tactic 'assumption' failed",
        "tactic 'exact' failed",
        "tactic 'rfl' failed",
        "tactic execution has not been implemented",
        "type mismatch",
        "declaration has metavariables",
    )
    if any(marker in lowered for marker in syntax_or_elab_markers):
        return "SYNTAX_OR_ELAB"
    if any(marker in lowered for marker in proof_markers):
        return "PROOF_ERROR"
    # Lean reached the submitted declaration but rejected it for an otherwise
    # unclassified reason. Treat that conservatively as a proof error.
    return "PROOF_ERROR"


def parse_dependency_audit(output: str) -> dict[str, Any]:
    library: list[dict[str, Any]] = []
    forbidden: list[dict[str, Any]] = []
    local_modules: list[str] = []
    target_seen = False
    format_version: int | None = None
    type_check: dict[str, Any] | None = None
    malformed: list[str] = []
    for raw_line in output.splitlines():
        fields = raw_line.split("\t")
        if fields[:1] == ["format"] and len(fields) == 2:
            try:
                format_version = int(fields[1])
            except ValueError:
                malformed.append(raw_line)
        elif fields[:1] == ["target"] and len(fields) >= 3:
            target_seen = True
        elif fields[:1] == ["typeeq"] and len(fields) == 4:
            if type_check is not None or fields[3] not in ("true", "false"):
                malformed.append(raw_line)
            else:
                type_check = {
                    "candidate": fields[1],
                    "expected": fields[2],
                    "equal": fields[3] == "true",
                }
        elif fields[:1] == ["localmodule"] and len(fields) == 2:
            if LEAN_NAME_RE.fullmatch(fields[1]):
                local_modules.append(fields[1])
            else:
                malformed.append(raw_line)
        elif fields[:1] == ["library"] and len(fields) == 4:
            try:
                distance = int(fields[3])
            except ValueError:
                malformed.append(raw_line)
                continue
            library.append({"name": fields[1], "module": fields[2], "distance": distance})
        elif fields[:1] == ["forbidden"] and len(fields) >= 3:
            forbidden.append({"name": fields[1], "kind": fields[2]})
        elif fields[:1] in (["visited"], ["summary"]):
            continue
        elif raw_line.strip():
            malformed.append(raw_line)
    return {
        "ok": (
            format_version == 2
            and target_seen
            and type_check is not None
            and type_check["equal"] is True
            and not malformed
        ),
        "format_version": format_version,
        "target_seen": target_seen,
        "type_check": type_check,
        "local_modules": sorted(set(local_modules)),
        "library_declarations": sorted(library, key=lambda item: (item["distance"], item["name"])),
        "forbidden_dependencies": forbidden,
        "malformed_lines": malformed,
    }


@dataclass(frozen=True)
class ValidationConfig:
    workspace: Path
    submission_relative: str
    canonical_relative: str
    target_theorem: str
    compile_command: Sequence[str]
    condition: str
    controlled_manifest: Path | None = None
    controlled_root_relative: str = "."
    local_source_relatives: Sequence[str] = field(default_factory=tuple)
    forbidden_import_prefixes: Sequence[str] = field(default_factory=tuple)
    audit_command: Sequence[str] | None = None
    submission_module: str | None = None
    audit_helper: Path | None = None
    hidden_parent: Path | None = None
    compile_timeout_seconds: float = 120.0
    audit_timeout_seconds: float = 120.0
    keep_hidden: bool = False


def validate(config: ValidationConfig) -> dict[str, Any]:
    workspace = config.workspace.resolve()
    if config.condition not in ("N", "L"):
        raise BenchmarkToolError("condition must be N or L")
    _simple_target_name(config.target_theorem)
    submission = resolve_below(workspace, config.submission_relative)
    canonical = resolve_below(workspace, config.canonical_relative)
    controlled_root = (
        workspace
        if config.controlled_root_relative in ("", ".")
        else resolve_below(workspace, config.controlled_root_relative)
    )
    result: dict[str, Any] = {
        "pass": False,
        "failure_code": None,
        "note": "",
        "condition": config.condition,
        "target_theorem": config.target_theorem,
        "submission": config.submission_relative,
        "controlled_before": None,
        "controlled_hidden": None,
        "controlled_after_compile": None,
        "controlled_after_expected_compile": None,
        "controlled_after_audit": None,
        "candidate_inventory": None,
        "static_findings": [],
        "statement_check": None,
        "semantic_statement_check": None,
        "compile": None,
        "expected_statement_compile": None,
        "local_modules_side_channel": None,
        "dependency_audit": None,
        "library_use": False if config.condition == "N" else None,
        "library_declarations": [],
        "library_audit_complete": config.condition == "N",
    }

    if not submission.is_file():
        result.update(failure_code="NO_SUBMISSION", note="submission file is absent")
        return result
    if not canonical.is_file():
        result.update(failure_code="SYSTEM_ERROR", note="canonical statement source is absent")
        return result

    manifest: dict[str, Any] | None = None
    if config.controlled_manifest is not None:
        try:
            manifest = load_manifest(config.controlled_manifest)
            controlled_before = verify_manifest(controlled_root, manifest)
        except BenchmarkToolError as error:
            result.update(failure_code="SYSTEM_ERROR", note=str(error))
            return result
        result["controlled_before"] = controlled_before
        if not controlled_before["ok"]:
            result.update(
                failure_code="RULE_VIOLATION",
                note="controlled files changed before validation",
            )
            return result

    protected_modules = controlled_module_identities(controlled_root, manifest)
    candidate_inventory = inventory_candidate_lean(workspace, controlled_root, manifest)
    result["candidate_inventory"] = candidate_inventory
    source_relatives = list(candidate_inventory["scanned_sources"])
    if config.submission_relative not in source_relatives:
        # The submission is always candidate-controlled even if a malformed
        # manifest accidentally lists it as a released file.
        source_relatives.append(config.submission_relative)
    prefixes = list(config.forbidden_import_prefixes)
    if config.condition == "N" and "NumStability" not in prefixes:
        prefixes.append("NumStability")
    findings: list[dict[str, Any]] = list(candidate_inventory["findings"])
    for relative in config.local_source_relatives:
        try:
            configured_source = resolve_below(workspace, relative)
        except BenchmarkToolError as error:
            findings.append(
                {"path": relative, "kind": "invalid local source", "detail": str(error)}
            )
            continue
        if not configured_source.is_file():
            findings.append({"path": relative, "kind": "missing local source"})
    for relative in source_relatives:
        try:
            source = resolve_below(workspace, relative)
        except BenchmarkToolError as error:
            findings.append({"path": relative, "kind": "invalid local source", "detail": str(error)})
            continue
        if not source.is_file():
            findings.append({"path": relative, "kind": "missing local source"})
            continue
        findings.extend(forbidden_source_findings(source, prefixes))
    local_modules = set(candidate_inventory["local_modules"])
    submission_module = config.submission_module
    if submission_module is None:
        submission_module = _module_name_from_relative_source(
            Path(config.submission_relative)
        )
    if submission_module is not None:
        if not LEAN_NAME_RE.fullmatch(submission_module):
            result.update(
                failure_code="SYSTEM_ERROR", note="invalid submission module name"
            )
            return result
        local_modules.add(submission_module)
    candidate_inventory["local_modules"] = sorted(local_modules)
    candidate_inventory["protected_modules"] = sorted(protected_modules)
    for module in sorted(local_modules):
        if module in protected_modules:
            findings.append(
                {
                    "path": module,
                    "kind": "protected module collision",
                    "module": module,
                    "detail": "candidate module would shadow a controlled or trusted import",
                }
            )
        if module == "NumStability" or module.startswith("NumStability."):
            findings.append(
                {
                    "path": module,
                    "kind": "reserved library module",
                    "module": module,
                    "detail": "candidate modules may not claim frozen NumStability ownership",
                }
            )
    result["static_findings"] = findings
    if findings:
        result.update(
            failure_code="RULE_VIOLATION",
            note="candidate source or compiled artifact violates validation rules",
        )
        return result

    statement_check = compare_target_signature(submission, canonical, config.target_theorem)
    result["statement_check"] = statement_check
    if not statement_check["ok"]:
        result.update(failure_code="RULE_VIOLATION", note="target theorem statement changed")
        return result

    hidden_parent = config.hidden_parent.resolve() if config.hidden_parent else None
    if hidden_parent:
        hidden_parent.mkdir(parents=True, exist_ok=True)
    hidden = Path(tempfile.mkdtemp(prefix="highambench-hidden-", dir=hidden_parent))
    hidden_workspace = hidden / "project"
    generated_id = uuid.uuid4().hex
    checked_relative = str(
        Path(config.submission_relative).with_name(
            f"HighamBenchChecked_{generated_id}.lean"
        )
    )
    checked_module = _module_name_from_relative_source(Path(checked_relative))
    if checked_module is None:
        raise BenchmarkToolError("generated checked module name is invalid")
    expected_simple = f"highamBenchExpected_{generated_id}"
    target_prefix = config.target_theorem.rsplit(".", 1)
    expected_theorem = (
        f"{target_prefix[0]}.{expected_simple}"
        if len(target_prefix) == 2
        else expected_simple
    )
    expected_relative = str(
        Path(config.submission_relative).with_name(
            f"HighamBenchExpected_{generated_id}.lean"
        )
    )
    expected_module = _module_name_from_relative_source(Path(expected_relative))
    if expected_module is None:
        raise BenchmarkToolError("generated expected module name is invalid")
    try:
        shutil.copytree(
            workspace,
            hidden_workspace,
            symlinks=False,
            ignore=shutil.ignore_patterns(
                ".git", "__pycache__", "private_gold", "benchmark-results", "results"
            ),
        )
        if manifest is not None:
            hidden_controlled_root = (
                hidden_workspace
                if config.controlled_root_relative in ("", ".")
                else resolve_below(hidden_workspace, config.controlled_root_relative)
            )
            controlled_hidden = verify_manifest(hidden_controlled_root, manifest)
            result["controlled_hidden"] = controlled_hidden
            if not controlled_hidden["ok"]:
                result.update(
                    failure_code="RULE_VIOLATION",
                    note="controlled files changed in hidden rebuild copy",
                )
                return result

        hidden_submission = resolve_below(hidden_workspace, config.submission_relative)
        checked_submission = resolve_below(hidden_workspace, checked_relative)
        local_modules_file = (
            hidden_workspace / f"{LOCAL_MODULES_FILENAME}-{generated_id}"
        )
        local_modules_payload = "".join(
            f"{module}\n" for module in sorted(local_modules)
        ).encode("utf-8")
        source_bytes = hidden_submission.read_bytes()
        checks = (
            f"\n\n-- Added only in the hidden validator copy.\n"
            f"#check {config.target_theorem}\n"
            f"#print axioms {config.target_theorem}\n"
        ).encode("utf-8")
        checked_submission.write_bytes(source_bytes + checks)

        values: dict[str, str | Path | int] = {
            "workspace": hidden_workspace,
            "submission": hidden_submission,
            "checked_submission": checked_submission,
            "checked_olean": checked_submission.with_suffix(".olean"),
            "target_theorem": config.target_theorem,
            "submission_module": checked_module,
            "audit_helper": config.audit_helper or "",
            "local_modules_file": local_modules_file,
        }
        compile_command = render_command(config.compile_command, values)
        compile_result = run_captured(
            compile_command,
            cwd=hidden_workspace,
            timeout_seconds=config.compile_timeout_seconds,
        )
        compile_output, compile_truncated = truncate_text(compile_result["output"])
        compile_result["output"] = compile_output
        compile_result["output_truncated"] = compile_truncated
        compile_result["display"] = command_display(compile_command)
        result["compile"] = compile_result

        if manifest is not None:
            controlled_after_compile = verify_manifest(hidden_controlled_root, manifest)
            result["controlled_after_compile"] = controlled_after_compile
            if not controlled_after_compile["ok"]:
                result.update(
                    failure_code="RULE_VIOLATION",
                    note="candidate compilation changed controlled files",
                )
                return result

        if compile_result["system_error"]:
            result.update(failure_code="SYSTEM_ERROR", note="Lean command could not start")
            return result
        if compile_result["timed_out"]:
            result.update(failure_code="SYSTEM_ERROR", note="hidden validation build timed out")
            return result
        if compile_result["exit_code"] != 0:
            result.update(
                failure_code=classify_lean_failure(compile_result["output"]),
                note="hidden Lean build rejected the submission",
            )
            return result
        if "sorryAx" in compile_result["output"] or "declaration uses 'sorry'" in compile_result[
            "output"
        ]:
            result.update(
                failure_code="RULE_VIOLATION",
                note="compiled target depends on a sorry placeholder",
            )
            return result
        checked_olean = checked_submission.with_suffix(".olean")
        if not checked_olean.is_file():
            result.update(
                failure_code="SYSTEM_ERROR",
                note="hidden compiler did not create the required checked olean",
            )
            return result

        # Compile a trusted copy of the frozen target under a fresh name.  It is
        # created only after candidate compilation, so candidate syntax cannot
        # change how this declaration is parsed or elaborated.
        hidden_canonical = resolve_below(hidden_workspace, config.canonical_relative)
        expected_submission = resolve_below(hidden_workspace, expected_relative)
        if expected_submission.exists():
            raise BenchmarkToolError("generated expected statement path already exists")
        canonical_text = hidden_canonical.read_text(encoding="utf-8")
        expected_submission.write_text(
            renamed_canonical_source(
                canonical_text, config.target_theorem, expected_simple
            ),
            encoding="utf-8",
        )
        expected_olean = expected_submission.with_suffix(".olean")
        expected_values = dict(values)
        expected_values.update(
            {
                "checked_submission": expected_submission,
                "checked_olean": expected_olean,
            }
        )
        expected_compile_command = render_command(
            config.compile_command, expected_values
        )
        expected_compile = run_captured(
            expected_compile_command,
            cwd=hidden_workspace,
            timeout_seconds=config.compile_timeout_seconds,
        )
        expected_output, expected_truncated = truncate_text(expected_compile["output"])
        expected_compile["output"] = expected_output
        expected_compile["output_truncated"] = expected_truncated
        expected_compile["display"] = command_display(expected_compile_command)
        result["expected_statement_compile"] = expected_compile

        if manifest is not None:
            controlled_after_expected = verify_manifest(hidden_controlled_root, manifest)
            result["controlled_after_expected_compile"] = controlled_after_expected
            if not controlled_after_expected["ok"]:
                result.update(
                    failure_code="RULE_VIOLATION",
                    note="expected-statement compilation changed controlled files",
                )
                return result
        if (
            expected_compile["system_error"]
            or expected_compile["timed_out"]
            or expected_compile["exit_code"] != 0
            or not expected_olean.is_file()
        ):
            result.update(
                failure_code="SYSTEM_ERROR",
                note="trusted frozen target type did not compile to an olean",
            )
            return result

        if config.audit_command is None:
            result["dependency_audit"] = {
                "note": "not configured; semantic and dependency checks are mandatory"
            }
            result.update(
                failure_code="SYSTEM_ERROR",
                note="trusted semantic/dependency audit is not configured",
            )
            return result

        # This trusted side channel is created after all candidate elaboration.
        # The audit imports the compiler-produced olean and never recompiles the
        # candidate source, so candidate stdout or `run_cmd` code cannot forge
        # helper-module ownership rows.
        local_modules_file.write_bytes(local_modules_payload)
        values.update(
            {
                "expected_submission": expected_submission,
                "expected_olean": expected_olean,
                "expected_module": expected_module,
                "expected_theorem": expected_theorem,
            }
        )
        audit_command = render_command(config.audit_command, values)
        audit_result = run_captured(
            audit_command,
            cwd=hidden_workspace,
            timeout_seconds=config.audit_timeout_seconds,
        )
        audit_output, audit_truncated = truncate_text(audit_result["output"])
        audit_result["output"] = audit_output
        audit_result["output_truncated"] = audit_truncated
        audit_result["display"] = command_display(audit_command)
        side_channel_unchanged = (
            local_modules_file.is_file()
            and local_modules_file.read_bytes() == local_modules_payload
        )
        result["local_modules_side_channel"] = {
            "created_after_candidate_compilation": True,
            "candidate_recompiled_during_audit": False,
            "unchanged_after_audit": side_channel_unchanged,
        }
        if not side_channel_unchanged:
            result.update(
                failure_code="RULE_VIOLATION",
                note="trusted local-module audit input changed during validation",
            )
            return result

        if manifest is not None:
            controlled_after_audit = verify_manifest(hidden_controlled_root, manifest)
            result["controlled_after_audit"] = controlled_after_audit
            if not controlled_after_audit["ok"]:
                result.update(
                    failure_code="RULE_VIOLATION",
                    note="semantic/dependency audit changed controlled files",
                )
                return result

        parsed = parse_dependency_audit(audit_result["output"])
        expected_helper_modules = sorted(
            local_modules - ({submission_module} if submission_module else set())
        )
        missing_helper_modules = sorted(
            set(expected_helper_modules) - set(parsed["local_modules"])
        )
        parsed["expected_helper_modules"] = expected_helper_modules
        parsed["missing_helper_modules"] = missing_helper_modules
        audit_result["parsed"] = parsed
        result["dependency_audit"] = audit_result
        semantic = parsed.get("type_check")
        result["semantic_statement_check"] = semantic
        if isinstance(semantic, dict) and semantic.get("equal") is False:
            result.update(
                failure_code="RULE_VIOLATION",
                note="target theorem text elaborated to a different Lean type",
            )
            return result
        if (
            not isinstance(semantic, dict)
            or semantic.get("candidate") != config.target_theorem
            or semantic.get("expected") != expected_theorem
            or semantic.get("equal") is not True
        ):
            result["library_audit_complete"] = False
            result.update(
                failure_code="SYSTEM_ERROR",
                note="trusted audit did not prove semantic equality with the frozen target",
            )
            return result
        if parsed["forbidden_dependencies"]:
            result["library_audit_complete"] = False
            result.update(
                failure_code="RULE_VIOLATION",
                note="dependency audit found a forbidden proof dependency",
            )
            return result
        if expected_helper_modules and (
            parsed["format_version"] != 2 or missing_helper_modules
        ):
            result["library_audit_complete"] = False
            result.update(
                failure_code="SYSTEM_ERROR",
                note="dependency audit did not cover every candidate helper module",
            )
            return result
        if (
            audit_result["system_error"]
            or audit_result["timed_out"]
            or audit_result["exit_code"] != 0
            or not parsed["ok"]
        ):
            result["library_audit_complete"] = False
            result.update(
                failure_code="SYSTEM_ERROR",
                note="trusted semantic/dependency audit was incomplete",
            )
            return result
        result["library_audit_complete"] = True
        result["library_declarations"] = parsed["library_declarations"]
        result["library_use"] = bool(parsed["library_declarations"])

        if config.condition == "N" and result["library_declarations"]:
            result.update(
                failure_code="RULE_VIOLATION",
                note="condition N proof depends on NumStability",
            )
            return result

        result.update(
            {"pass": True, "failure_code": None, "note": "accepted by hidden Lean validation"}
        )
        return result
    except (OSError, BenchmarkToolError) as error:
        result.update(failure_code="SYSTEM_ERROR", note=f"hidden validation failed: {error}")
        return result
    finally:
        if not config.keep_hidden:
            shutil.rmtree(hidden, ignore_errors=True)
        else:
            result["hidden_workspace"] = str(hidden_workspace)


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", type=Path, required=True)
    parser.add_argument("--condition", choices=("N", "L"), required=True)
    parser.add_argument("--submission-relative", required=True)
    parser.add_argument("--canonical-relative", required=True)
    parser.add_argument("--target-theorem", required=True)
    parser.add_argument(
        "--compile-command-json",
        required=True,
        help=(
            "JSON argv; placeholders: {workspace}, {submission}, {checked_submission}, "
            "{target_theorem}"
        ),
    )
    parser.add_argument("--controlled-manifest", type=Path)
    parser.add_argument("--controlled-root-relative", default=".")
    parser.add_argument("--local-source-relative", action="append", default=[])
    parser.add_argument("--forbidden-import-prefix", action="append", default=[])
    parser.add_argument("--audit-command-json")
    parser.add_argument("--submission-module")
    parser.add_argument("--audit-helper", type=Path)
    parser.add_argument("--hidden-parent", type=Path)
    parser.add_argument("--compile-timeout-seconds", type=float, default=120.0)
    parser.add_argument("--audit-timeout-seconds", type=float, default=120.0)
    parser.add_argument("--keep-hidden", action="store_true")
    parser.add_argument("--output", type=Path)
    return parser


def main() -> int:
    args = make_parser().parse_args()
    try:
        compile_command = parse_command_json(
            args.compile_command_json, option="--compile-command-json"
        )
        assert compile_command is not None
        audit_command = parse_command_json(
            args.audit_command_json, option="--audit-command-json"
        )
        result = validate(
            ValidationConfig(
                workspace=args.workspace,
                submission_relative=args.submission_relative,
                canonical_relative=args.canonical_relative,
                target_theorem=args.target_theorem,
                compile_command=compile_command,
                condition=args.condition,
                controlled_manifest=args.controlled_manifest,
                controlled_root_relative=args.controlled_root_relative,
                local_source_relatives=args.local_source_relative,
                forbidden_import_prefixes=args.forbidden_import_prefix,
                audit_command=audit_command,
                submission_module=args.submission_module,
                audit_helper=args.audit_helper,
                hidden_parent=args.hidden_parent,
                compile_timeout_seconds=args.compile_timeout_seconds,
                audit_timeout_seconds=args.audit_timeout_seconds,
                keep_hidden=args.keep_hidden,
            )
        )
    except BenchmarkToolError as error:
        result = {
            "pass": False,
            "failure_code": "SYSTEM_ERROR",
            "note": str(error),
        }
    if args.output:
        write_json(args.output, result)
    else:
        print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result.get("pass") else 1


if __name__ == "__main__":
    raise SystemExit(main())
