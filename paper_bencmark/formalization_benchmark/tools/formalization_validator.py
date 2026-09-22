#!/usr/bin/env python3
"""Validate one source-first HighamBench ``Candidate.lean`` submission.

The validator deliberately knows no gold Lean statement.  It enforces the
pilot's syntactic integrity contract, then compiles an immutable copy in a new
temporary workspace.  The caller is responsible for supplying the condition's
already-isolated Lean environment; only ``Candidate.lean`` is copied into the
fresh workspace.
"""

from __future__ import annotations

import argparse
from contextlib import contextmanager
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import select
import signal
import stat
import subprocess
import sys
import tempfile
import time
from typing import Any, Iterator, Mapping, Sequence

from common import BenchmarkError, bounded_tree_usage, sha256_file


SCHEMA_VERSION = "formalization-validator-1"
TARGET_DECLARATION = "HighamBenchCandidate.target"
DEFAULT_COMPILER_COMMAND = (
    "lean",
    "--root",
    "{workspace}",
    "-o",
    "{olean}",
    "{candidate}",
)
DEFAULT_MAX_SOURCE_BYTES = 2 * 1024 * 1024
DEFAULT_TIMEOUT_SECONDS = 300.0
MAX_COMPILER_OUTPUT_BYTES = 8 * 1024 * 1024
MAX_VALIDATION_WORKSPACE_ENTRIES = 10_000
MAX_VALIDATION_WORKSPACE_BYTES = 256 * 1024 * 1024
COMMAND_CGROUP_VARIABLE = "HIGHAMBENCH_COMMAND_CGROUP_PROCS"
CGROUP_JOIN_FAILURE_MARKER = "HIGHAMBENCH_COMMAND_CGROUP_JOIN_FAILED"

# These constructs either add unchecked assumptions or create declarations
# outside the ordinary kernel-checked definition/theorem path.  ``partial`` and
# the code-generation attributes are included as integrity-equivalent escapes.
FORBIDDEN_TOKENS: Mapping[str, str] = {
    "sorry": "proof hole",
    "admit": "additional proof hole",
    "axiom": "new axiom declaration",
    "constant": "new constant declaration",
    "opaque": "opaque declaration",
    "unsafe": "unsafe declaration or escape",
    "sorryAx": "direct use of Lean's sorry axiom",
    "partial": "partial declaration",
    "extern": "external implementation escape",
    "implemented_by": "implementation substitution escape",
    "elab": "source metaprogramming is not permitted in a candidate",
    "elab_rules": "source metaprogramming is not permitted in a candidate",
    "macro": "source metaprogramming is not permitted in a candidate",
    "macro_rules": "source metaprogramming is not permitted in a candidate",
    "run_cmd": "source metaprogramming is not permitted in a candidate",
    "run_tac": "source metaprogramming is not permitted in a candidate",
    "syntax": "custom syntax generation is not permitted in a candidate",
    "initialize": "module initialization is not permitted in a candidate",
    "builtin_initialize": "module initialization is not permitted in a candidate",
    "#": "compiler and interactive commands are not permitted in a candidate",
}

DECLARATION_KEYWORDS = {
    "abbrev",
    "class",
    "def",
    "inductive",
    "instance",
    "lemma",
    "structure",
    "theorem",
}


class ValidationInfrastructureError(RuntimeError):
    """The validator could not establish a trustworthy result."""


def run_bounded_command(
    command: Sequence[str],
    *,
    cwd: Path,
    environment: Mapping[str, str],
    timeout_seconds: float,
    maximum_output_bytes: int,
) -> dict[str, Any]:
    """Run a process group while retaining at most a fixed stdout/stderr prefix."""

    cgroup_procs = environment.get(COMMAND_CGROUP_VARIABLE)
    cgroup_root: Path | None = None
    cgroup_before: dict[str, int] = {}

    def resource_events(root: Path) -> dict[str, int]:
        result: dict[str, int] = {}
        for filename, keys in (
            ("memory.events", ("max", "oom", "oom_kill")),
            ("pids.events", ("max",)),
        ):
            try:
                lines = (root / filename).read_text(encoding="ascii").splitlines()
            except OSError as error:
                raise ValidationInfrastructureError(
                    f"cannot read validation resource counters: {filename}"
                ) from error
            parsed: dict[str, int] = {}
            for line in lines:
                fields = line.split()
                if len(fields) == 2 and fields[1].isdigit():
                    parsed[fields[0]] = int(fields[1])
            if any(key not in parsed for key in keys):
                raise ValidationInfrastructureError(
                    f"malformed validation resource counters: {filename}"
                )
            for key in keys:
                result[f"{filename}.{key}"] = parsed[key]
        return result

    expanded_command = list(command)
    if cgroup_procs:
        endpoint = Path(cgroup_procs)
        if endpoint.name != "cgroup.procs" or endpoint.is_symlink() or not endpoint.is_file():
            raise ValidationInfrastructureError(
                "validation command cgroup endpoint is missing or unsafe"
            )
        cgroup_root = endpoint.parent
        cgroup_before = resource_events(cgroup_root)
        bootstrap = (
            "import os,sys;"
            "p=sys.argv[1];c=sys.argv[2:];"
            "\ntry:\n open(p,'w',encoding='ascii').write('0')"
            "\nexcept OSError:\n os.write(2,b'" + CGROUP_JOIN_FAILURE_MARKER + "\\n');os._exit(125)"
            "\nos.execvpe(c[0],c,os.environ)"
        )
        expanded_command = [
            sys.executable,
            "-I",
            "-B",
            "-c",
            bootstrap,
            str(endpoint),
            *expanded_command,
        ]

    process = subprocess.Popen(
        expanded_command,
        cwd=str(cwd),
        env=dict(environment),
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        start_new_session=True,
    )
    assert process.stdout is not None
    descriptor = process.stdout.fileno()
    retained = bytearray()
    digest = hashlib.sha256()
    observed_bytes = 0
    exceeded = False
    timed_out = False
    deadline = time.monotonic() + timeout_seconds

    def terminate() -> None:
        # The process-group leader may exit while a descendant keeps the output
        # pipe open.  Signal the group independently of the leader's status so
        # timeout/output-limit enforcement cannot leave generated children alive.
        def group_exists() -> bool:
            try:
                os.killpg(process.pid, 0)
                return True
            except ProcessLookupError:
                return False
            except PermissionError:
                # Some platforms report EPERM for an already-dead leader's
                # empty process group. A live leader must remain controllable.
                return process.poll() is None

        try:
            os.killpg(process.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        except PermissionError as error:
            if process.poll() is None:
                raise ValidationInfrastructureError(
                    "cannot terminate validation process group"
                ) from error
        grace_deadline = time.monotonic() + 2.0
        while group_exists() and time.monotonic() < grace_deadline:
            time.sleep(0.02)
        if group_exists():
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            except PermissionError as error:
                if process.poll() is None:
                    raise ValidationInfrastructureError(
                        "cannot kill validation process group"
                    ) from error
        if process.poll() is None:
            try:
                process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                try:
                    process.kill()
                except ProcessLookupError:
                    pass
                process.wait()

    try:
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                timed_out = True
                terminate()
                break
            readable, _, _ = select.select([descriptor], [], [], min(0.1, remaining))
            if readable:
                chunk = os.read(descriptor, 64 * 1024)
                if not chunk:
                    break
                digest.update(chunk)
                observed_bytes += len(chunk)
                available = max(0, maximum_output_bytes - len(retained))
                retained.extend(chunk[:available])
                if observed_bytes > maximum_output_bytes:
                    exceeded = True
                    terminate()
                    break
            elif process.poll() is not None:
                # Drain the final pipe bytes on the next iteration.
                continue
        if process.poll() is None:
            process.wait()
    finally:
        process.stdout.close()
        if process.poll() is None:
            terminate()
    cgroup_after = resource_events(cgroup_root) if cgroup_root is not None else {}
    cgroup_delta: dict[str, int] = {}
    for key, current in cgroup_after.items():
        prior = cgroup_before.get(key)
        if prior is None or current < prior:
            raise ValidationInfrastructureError(
                "validation resource counters regressed"
            )
        cgroup_delta[key] = current - prior
    rendered_output = bytes(retained).decode("utf-8", errors="replace")
    return {
        "returncode": process.returncode,
        "output": rendered_output,
        "output_sha256": digest.hexdigest(),
        "output_bytes_observed": observed_bytes,
        "output_limit_bytes": maximum_output_bytes,
        "output_limit_exceeded": exceeded,
        "timed_out": timed_out,
        "resource_limit_event_delta": cgroup_delta,
        "resource_limit_exceeded": any(cgroup_delta.values()),
        "resource_cgroup_join_failed": CGROUP_JOIN_FAILURE_MARKER in rendered_output,
    }


@dataclass(frozen=True)
class Token:
    value: str
    offset: int


@dataclass(frozen=True)
class Declaration:
    kind: str
    full_name: str
    token_index: int


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def canonical_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=True, separators=(",", ":"), sort_keys=True)


def _line_column(source: str, offset: int) -> tuple[int, int]:
    line = source.count("\n", 0, offset) + 1
    prior_newline = source.rfind("\n", 0, offset)
    column = offset + 1 if prior_newline < 0 else offset - prior_newline
    return line, column


def _mask_noncode(source: str) -> str:
    """Replace comments and string contents with spaces, preserving offsets."""

    output = list(source)
    index = 0
    length = len(source)
    while index < length:
        if source.startswith("--", index):
            cursor = index
            while cursor < length and source[cursor] != "\n":
                output[cursor] = " "
                cursor += 1
            index = cursor
            continue
        if source.startswith("/-", index):
            depth = 1
            output[index] = output[index + 1] = " "
            cursor = index + 2
            while cursor < length and depth:
                if source.startswith("/-", cursor):
                    depth += 1
                    output[cursor] = output[cursor + 1] = " "
                    cursor += 2
                elif source.startswith("-/", cursor):
                    depth -= 1
                    output[cursor] = output[cursor + 1] = " "
                    cursor += 2
                else:
                    if source[cursor] != "\n":
                        output[cursor] = " "
                    cursor += 1
            index = cursor
            continue
        if source[index] == '"':
            triple = source.startswith('"""', index)
            width = 3 if triple else 1
            for cursor in range(index, min(index + width, length)):
                output[cursor] = " "
            cursor = index + width
            escaped = False
            while cursor < length:
                if triple and source.startswith('"""', cursor):
                    for closing in range(cursor, cursor + 3):
                        output[closing] = " "
                    cursor += 3
                    break
                character = source[cursor]
                if not triple and character == '"' and not escaped:
                    output[cursor] = " "
                    cursor += 1
                    break
                if character != "\n":
                    output[cursor] = " "
                if triple:
                    escaped = False
                elif character == "\\" and not escaped:
                    escaped = True
                else:
                    escaped = False
                cursor += 1
            index = cursor
            continue
        index += 1
    return "".join(output)


TOKEN_PATTERN = re.compile(
    r":=|[A-Za-z_\u0080-\U0010ffff][A-Za-z0-9_\u0080-\U0010ffff']*|\.|[^\s]"
)
IDENTIFIER_PATTERN = re.compile(
    r"^[A-Za-z_\u0080-\U0010ffff][A-Za-z0-9_\u0080-\U0010ffff']*$"
)


def _tokens(masked_source: str) -> list[Token]:
    return [Token(match.group(0), match.start()) for match in TOKEN_PATTERN.finditer(masked_source)]


def _is_identifier(value: str) -> bool:
    return IDENTIFIER_PATTERN.fullmatch(value) is not None


def _is_scope_closure_suffix(values: Sequence[str]) -> bool:
    """Accept only zero or more trailing `end` commands after the target proof."""

    cursor = 0
    while cursor < len(values):
        if values[cursor] != "end":
            return False
        cursor += 1
        if (
            cursor < len(values)
            and values[cursor] != "end"
            and _is_identifier(values[cursor])
        ):
            cursor += 1
    return True


def _read_name(tokens: Sequence[Token], start: int) -> tuple[str | None, int]:
    if start >= len(tokens) or not _is_identifier(tokens[start].value):
        return None, start
    parts = [tokens[start].value]
    cursor = start + 1
    while (
        cursor + 1 < len(tokens)
        and tokens[cursor].value == "."
        and _is_identifier(tokens[cursor + 1].value)
    ):
        parts.extend((".", tokens[cursor + 1].value))
        cursor += 2
    return "".join(parts), cursor


def _declarations(tokens: Sequence[Token]) -> list[Declaration]:
    scopes: list[str | None] = []
    declarations: list[Declaration] = []
    cursor = 0
    while cursor < len(tokens):
        value = tokens[cursor].value
        if value == "namespace":
            name, after = _read_name(tokens, cursor + 1)
            scopes.append(name)
            cursor = max(after, cursor + 1)
            continue
        if value in {"section", "mutual"}:
            scopes.append(None)
            cursor += 1
            continue
        if value == "end":
            if scopes:
                scopes.pop()
            cursor += 1
            continue
        if value in DECLARATION_KEYWORDS:
            declared_name, after = _read_name(tokens, cursor + 1)
            if declared_name is not None:
                namespace = ".".join(scope for scope in scopes if scope)
                if declared_name.startswith("_root_."):
                    full_name = declared_name.removeprefix("_root_.")
                elif namespace:
                    full_name = f"{namespace}.{declared_name}"
                else:
                    full_name = declared_name
                declarations.append(Declaration(value, full_name, cursor))
                cursor = after
                continue
        cursor += 1
    return declarations


def _issue(source: str, token: Token | None, code: str, message: str) -> dict[str, Any]:
    issue: dict[str, Any] = {"code": code, "message": message}
    if token is not None:
        line, column = _line_column(source, token.offset)
        issue.update({"line": line, "column": column})
    return issue


def inspect_candidate_source(
    source: str, *, allow_single_target_sorry: bool = False
) -> dict[str, Any]:
    """Check the narrow, deterministic source contract before compilation."""

    masked = _mask_noncode(source)
    tokens = _tokens(masked)
    declarations = _declarations(tokens)
    issues: list[dict[str, Any]] = []

    for token in tokens:
        if token.value in FORBIDDEN_TOKENS and not (
            allow_single_target_sorry and token.value == "sorry"
        ):
            issues.append(
                _issue(
                    source,
                    token,
                    "forbidden-construct",
                    FORBIDDEN_TOKENS[token.value],
                )
            )

    sorry_indices = [index for index, token in enumerate(tokens) if token.value == "sorry"]
    if allow_single_target_sorry and len(sorry_indices) != 1:
        token = tokens[sorry_indices[0]] if sorry_indices else None
        issues.append(
            _issue(
                source,
                token,
                "statement-hole-count",
                f"expected exactly one target `sorry`, found {len(sorry_indices)}",
            )
        )
    elif not allow_single_target_sorry and sorry_indices:
        issues.append(
            _issue(
                source,
                tokens[sorry_indices[0]],
                "proof-hole-count",
                f"expected a complete proof with no `sorry`, found {len(sorry_indices)}",
            )
        )

    roots = [item for item in declarations if item.full_name == TARGET_DECLARATION]
    if len(roots) != 1:
        token = tokens[roots[0].token_index] if roots else None
        issues.append(
            _issue(
                source,
                token,
                "root-declaration-count",
                f"expected exactly one declaration named {TARGET_DECLARATION}, found {len(roots)}",
            )
        )
    else:
        root = roots[0]
        root_token = tokens[root.token_index]
        if root.kind != "theorem":
            issues.append(
                _issue(
                    source,
                    root_token,
                    "root-declaration-kind",
                    "the audited root must be a theorem",
                )
            )
        later_declarations = [
            item for item in declarations if item.token_index > root.token_index
        ]
        if later_declarations:
            first = later_declarations[0]
            issues.append(
                _issue(
                    source,
                    tokens[first.token_index],
                    "root-not-final",
                    "all candidate declarations must appear before the audited root",
                )
            )
        if allow_single_target_sorry and len(sorry_indices) == 1:
            sorry_index = sorry_indices[0]
            prefix = [token.value for token in tokens[max(0, sorry_index - 2) : sorry_index]]
            suffix = [token.value for token in tokens[sorry_index + 1 :]]
            if (
                sorry_index <= root.token_index
                or prefix != [":=", "by"]
                or not _is_scope_closure_suffix(suffix)
            ):
                issues.append(
                    _issue(
                        source,
                        tokens[sorry_index],
                        "statement-hole-placement",
                        "the sole `sorry` must be the entire proof of the final audited target",
                    )
                )

    issue_key = lambda item: (
        int(item.get("line", 0)),
        int(item.get("column", 0)),
        str(item["code"]),
        str(item["message"]),
    )
    issues.sort(key=issue_key)
    return {
        "pass": not issues,
        "source_contract": (
            "statement-only-single-target-sorry"
            if allow_single_target_sorry
            else "complete-kernel-checked-proof"
        ),
        "target_declaration": TARGET_DECLARATION,
        "sorry_count": len(sorry_indices),
        "nonblank_code_lines": sum(
            1 for line in masked.splitlines() if line.strip()
        ),
        "imports": sorted(
            {
                module
                for match in re.finditer(r"^\s*import\s+([^\n]+)$", masked, re.MULTILINE)
                for module in match.group(1).split()
                if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", module)
            }
        ),
        "declarations": [
            {"kind": item.kind, "name": item.full_name} for item in declarations
        ],
        "issues": issues,
    }


def parse_command_json(value: str) -> tuple[str, ...]:
    try:
        parsed = json.loads(value)
    except json.JSONDecodeError as error:
        raise argparse.ArgumentTypeError(f"invalid command JSON: {error}") from error
    if not isinstance(parsed, list) or not parsed or not all(
        isinstance(item, str) and item for item in parsed
    ):
        raise argparse.ArgumentTypeError("command must be a nonempty JSON array of strings")
    return tuple(parsed)


def _expand_command(command: Sequence[str], values: Mapping[str, str]) -> list[str]:
    try:
        return [argument.format_map(values) for argument in command]
    except KeyError as error:
        raise ValidationInfrastructureError(
            f"unknown compiler-command placeholder: {error.args[0]}"
        ) from error


@contextmanager
def compiled_candidate_workspace(
    candidate_bytes: bytes,
    *,
    compiler_command: Sequence[str] = DEFAULT_COMPILER_COMMAND,
    compiler_cwd: Path | None = None,
    compiler_environment: Mapping[str, str] | None = None,
    scratch_root: Path | None = None,
    timeout_seconds: float = DEFAULT_TIMEOUT_SECONDS,
) -> Iterator[tuple[Path, dict[str, Any]]]:
    """Compile a probed candidate copy and retain its workspace for the caller."""

    if scratch_root is not None and not scratch_root.is_dir():
        raise ValidationInfrastructureError(f"scratch root is not a directory: {scratch_root}")
    temporary = tempfile.TemporaryDirectory(
        prefix="highambench-formalization-validate-",
        dir=str(scratch_root) if scratch_root is not None else None,
    )
    try:
        workspace = Path(temporary.name)
        staged_candidate = workspace / "Candidate.lean"
        staged_olean = workspace / "Candidate.olean"
        probe = b"\n" if candidate_bytes.endswith(b"\n") else b"\n\n"
        probe += b"#check _root_.HighamBenchCandidate.target\n"
        staged_candidate.write_bytes(candidate_bytes + probe)

        values = {
            "candidate": str(staged_candidate),
            "olean": str(staged_olean),
            "workspace": str(workspace),
        }
        expanded = _expand_command(compiler_command, values)
        environment = os.environ.copy()
        if compiler_environment:
            environment.update(compiler_environment)
        inherited_lean_path = environment.get("LEAN_PATH", "")
        environment["LEAN_PATH"] = str(workspace) + (
            os.pathsep + inherited_lean_path if inherited_lean_path else ""
        )
        try:
            completed = run_bounded_command(
                expanded,
                cwd=compiler_cwd or workspace,
                environment=environment,
                timeout_seconds=timeout_seconds,
                maximum_output_bytes=MAX_COMPILER_OUTPUT_BYTES,
            )
        except FileNotFoundError as error:
            raise ValidationInfrastructureError(
                f"compiler executable not found: {expanded[0]}"
            ) from error
        if completed["timed_out"]:
            raise ValidationInfrastructureError(
                f"compiler exceeded {timeout_seconds:g} seconds"
            )
        if completed["output_limit_exceeded"]:
            raise ValidationInfrastructureError(
                f"compiler output exceeded {MAX_COMPILER_OUTPUT_BYTES} bytes"
            )
        if completed["resource_cgroup_join_failed"]:
            raise ValidationInfrastructureError(
                "compiler could not enter the validation resource cgroup"
            )
        if completed["resource_limit_exceeded"]:
            raise ValidationInfrastructureError(
                "compiler reached a validation resource ceiling"
            )
        try:
            workspace_usage = bounded_tree_usage(
                workspace,
                maximum_entries=MAX_VALIDATION_WORKSPACE_ENTRIES,
                maximum_bytes=MAX_VALIDATION_WORKSPACE_BYTES,
            )
        except BenchmarkError as error:
            raise ValidationInfrastructureError(
                f"validation workspace exceeded its artifact envelope: {error}"
            ) from error

        output = completed["output"]
        compile_result: dict[str, Any] = {
            "pass": completed["returncode"] == 0,
            "returncode": completed["returncode"],
            "command_template": list(compiler_command),
            "output": output,
            "output_sha256": completed["output_sha256"],
            "output_bytes_observed": completed["output_bytes_observed"],
            "output_limit_bytes": completed["output_limit_bytes"],
            "resource_limit_event_delta": completed["resource_limit_event_delta"],
            "validation_workspace": workspace_usage,
            "fresh_workspace": True,
            "candidate_module": "Candidate",
        }
        if completed["returncode"] == 0:
            try:
                mode = staged_olean.stat().st_mode
            except FileNotFoundError as error:
                raise ValidationInfrastructureError(
                    "compiler returned success without creating Candidate.olean"
                ) from error
            if not stat.S_ISREG(mode) or staged_olean.is_symlink():
                raise ValidationInfrastructureError(
                    "compiler did not create a regular Candidate.olean"
                )
            if staged_olean.stat().st_size > MAX_VALIDATION_WORKSPACE_BYTES:
                raise ValidationInfrastructureError("Candidate.olean is oversized")
            compile_result["olean_sha256"] = sha256_file(staged_olean)
        yield workspace, compile_result
    finally:
        temporary.cleanup()


def read_candidate_bytes(candidate: Path, max_source_bytes: int) -> bytes:
    if candidate.name != "Candidate.lean":
        raise ValueError("candidate path must be named Candidate.lean")
    try:
        metadata = candidate.lstat()
    except OSError as error:
        raise ValueError(f"cannot stat candidate: {error}") from error
    if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode):
        raise ValueError("Candidate.lean must be a regular file, not a symlink")
    if metadata.st_size > max_source_bytes:
        raise ValueError(
            f"Candidate.lean exceeds the {max_source_bytes}-byte validation limit"
        )
    flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(candidate, flags)
    except OSError as error:
        raise ValueError(f"cannot open Candidate.lean safely: {error}") from error
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise ValueError("Candidate.lean changed into a non-regular file")
        if before.st_size > max_source_bytes:
            raise ValueError(
                f"Candidate.lean exceeds the {max_source_bytes}-byte validation limit"
            )
        first = bytearray()
        while len(first) <= max_source_bytes:
            chunk = os.read(descriptor, min(65536, max_source_bytes + 1 - len(first)))
            if not chunk:
                break
            first.extend(chunk)
        middle = os.fstat(descriptor)
        os.lseek(descriptor, 0, os.SEEK_SET)
        second = bytearray()
        while len(second) <= max_source_bytes:
            chunk = os.read(descriptor, min(65536, max_source_bytes + 1 - len(second)))
            if not chunk:
                break
            second.extend(chunk)
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    stable_fields = ("st_dev", "st_ino", "st_mode", "st_size", "st_mtime_ns", "st_ctime_ns")
    if (
        any(
            getattr(before, field) != getattr(middle, field)
            or getattr(before, field) != getattr(after, field)
            for field in stable_fields
        )
        or first != second
    ):
        raise ValueError("Candidate.lean changed while it was being read")
    value = bytes(first)
    if len(value) > max_source_bytes:
        raise ValueError(
            f"Candidate.lean exceeds the {max_source_bytes}-byte validation limit"
        )
    if b"\x00" in value:
        raise ValueError("Candidate.lean contains a NUL byte")
    try:
        value.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ValueError("Candidate.lean is not valid UTF-8") from error
    return value


def validate_candidate(
    candidate: Path,
    *,
    compiler_command: Sequence[str] = DEFAULT_COMPILER_COMMAND,
    compiler_cwd: Path | None = None,
    compiler_environment: Mapping[str, str] | None = None,
    scratch_root: Path | None = None,
    timeout_seconds: float = DEFAULT_TIMEOUT_SECONDS,
    max_source_bytes: int = DEFAULT_MAX_SOURCE_BYTES,
    allow_single_target_sorry: bool = False,
) -> dict[str, Any]:
    """Return a complete JSON-serializable validation decision."""

    base: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "pass": False,
        "failure_code": None,
        "target_declaration": TARGET_DECLARATION,
    }
    try:
        candidate_bytes = read_candidate_bytes(candidate, max_source_bytes)
    except (OSError, ValueError) as error:
        return {
            **base,
            "failure_code": "RULE_VIOLATION",
            "candidate": {"basename": candidate.name},
            "source_check": {
                "pass": False,
                "issues": [{"code": "candidate-file", "message": str(error)}],
            },
            "compile": None,
        }

    source = candidate_bytes.decode("utf-8")
    source_check = inspect_candidate_source(
        source, allow_single_target_sorry=allow_single_target_sorry
    )
    result = {
        **base,
        "candidate": {
            "basename": "Candidate.lean",
            "sha256": sha256_bytes(candidate_bytes),
            "bytes": len(candidate_bytes),
            "lines": len(source.splitlines()),
        },
        "source_check": source_check,
        "compile": None,
    }
    if not source_check["pass"]:
        result["failure_code"] = "RULE_VIOLATION"
        return result

    try:
        with compiled_candidate_workspace(
            candidate_bytes,
            compiler_command=compiler_command,
            compiler_cwd=compiler_cwd,
            compiler_environment=compiler_environment,
            scratch_root=scratch_root,
            timeout_seconds=timeout_seconds,
        ) as (_, compile_result):
            result["compile"] = compile_result
    except (OSError, ValidationInfrastructureError) as error:
        result["failure_code"] = "INFRASTRUCTURE_FAILURE"
        result["compile"] = {"pass": False, "infrastructure_error": str(error)}
        return result

    if not result["compile"]["pass"]:
        result["failure_code"] = "COMPILATION_FAILURE"
        return result
    result["pass"] = True
    return result


def write_json_atomic(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    encoded = json.dumps(value, indent=2, ensure_ascii=True, sort_keys=True) + "\n"
    descriptor, temporary_name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as stream:
            stream.write(encoded)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidate", type=Path, help="path to Candidate.lean")
    parser.add_argument(
        "--compiler-command-json",
        type=parse_command_json,
        default=DEFAULT_COMPILER_COMMAND,
        help=(
            "JSON argv array; supports {candidate}, {olean}, and {workspace} "
            "placeholders"
        ),
    )
    parser.add_argument("--compiler-cwd", type=Path)
    parser.add_argument("--scratch-root", type=Path)
    parser.add_argument(
        "--timeout-seconds", type=float, default=DEFAULT_TIMEOUT_SECONDS
    )
    parser.add_argument(
        "--max-source-bytes", type=int, default=DEFAULT_MAX_SOURCE_BYTES
    )
    parser.add_argument(
        "--allow-single-target-sorry",
        action="store_true",
        help="statement-only mode: require exactly one sorry as the final target proof",
    )
    parser.add_argument("--output", type=Path, help="also write the JSON result here")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = make_parser().parse_args(argv)
    result = validate_candidate(
        args.candidate,
        compiler_command=args.compiler_command_json,
        compiler_cwd=args.compiler_cwd,
        scratch_root=args.scratch_root,
        timeout_seconds=args.timeout_seconds,
        max_source_bytes=args.max_source_bytes,
        allow_single_target_sorry=args.allow_single_target_sorry,
    )
    if args.output is not None:
        write_json_atomic(args.output, result)
    print(json.dumps(result, indent=2, ensure_ascii=True, sort_keys=True))
    if result["pass"]:
        return 0
    return 2 if result["failure_code"] == "INFRASTRUCTURE_FAILURE" else 1


if __name__ == "__main__":
    raise SystemExit(main())
