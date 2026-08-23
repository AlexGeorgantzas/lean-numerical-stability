#!/usr/bin/env python3
"""Replay the hash-pinned P0010 format-2 declaration projection contract."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import tempfile
import subprocess
import sys
from pathlib import Path


CONTROL_HEAD = "35cb1a7c5f136f291398dddd99d8012dcf38f967"
WORKER_HEAD = "ad92bbfae62d538f3e52829a269a846688a8e213"
PHASE = Path("docs/architecture/phases/2026-08-repository-reorganization-completion")
P_RECORD_SHA = "DF459DA1FE80CC491C97CBDB2A55F03D82AC255BEA7DDE6D123CEBE151926AD1"
P_GZIP_SHA = "BFAF298CE8BFB295552D48C04DF8D74DD717A2EBAA701E396C9651C798671F97"
P_GZIP_SIZE = 8718
CHECKER_SHA = "0F32935ED1EFDD2BD4D6A4C346F3E8300C86DB1D4A3551A17165479226109220"
PRIVATE_SHA = "CA0D8BF8C0FC6179A9DFD03F68B1BAA69A0D4EE78A0BEFCB0541B839EE755B16"
GENERATOR_SHA = "AD1B19090B75936C874E6762989E4F06C0C1434C7DC7078E13499570BA3B6A63"
EXTRACTOR_SHA = "04AE8E46F66A0B8D2FED1FDB83904D8A60398F9B61A3EC4A10ADB3DF2352D771"
CLOSED_EXTRACTOR_SHA = "A13D69B60F899E39D75DF050518E57C1A05406CE18718ED7D84381D56EAC53BD"
WORKER_ROOT = Path(__file__).resolve().parents[4]
CANDIDATE_RELATIVE = Path("benchmark-results/R07-candidate.tsv")
CANDIDATE_STEM = "R07-candidate"
EXPECTED_DECLARATIONS = 56903
EXPECTED_MODULES = 1713
EXPECTED_SOURCE_TREE_SHA = "0F1DD883F3157535D059D3E7F60D80DDDC27638C0C34D926ADA5F0DFD6F5417A"
EXPECTED_EDGE_COUNTS = {
    "body_or_proof": 382872,
    "body_or_proof_only": 157695,
    "cross_module_body_or_proof": 235841,
    "cross_module_body_or_proof_only": 85173,
    "cross_module_signature": 177753,
    "cross_module_union": 262926,
    "signature": 266387,
    "signature_and_body_overlap": 225177,
    "union": 424082,
}
EXPECTED_VISIBILITY_COUNTS = {"internal": 4, "private": 1680, "public": 55219}
EXPECTED_KIND_COUNTS = {
    "constructor": 734,
    "definition": 11978,
    "inductive": 509,
    "recursor": 509,
    "theorem": 43173,
}
EXPECTED_GRAPH_METRICS = {
    "apparent_leaves_all": 14400,
    "apparent_leaves_public": 14349,
    "project_foundational_all": 3724,
    "project_isolated_all": 176,
    "project_isolated_public": 162,
}
EXTRACTION_MODULES = (
    "NumStability",
    "NumStability.Analysis.LinearOperators.NumericalRadius.Berger.Internal."
    "HermitianEuclideanSpaceNotation",
    "NumStability.Analysis.LinearOperators.NumericalRadius.Core.Internal."
    "EuclideanSpaceNotation",
    "NumStability.Analysis.LinearOperators.Pseudospectra.Resolvent.Internal."
    "ScalarNotation",
)
EXTRACTOR_LOAD_LINE = "  withImportModules #[{ module := `NumStability }] {} fun env => do"
EXPECTED_ISOLATED_ROWS = {
    "_private.NumStability.Analysis.LinearOperators.NumericalRadius.Berger.Internal."
    "HermitianEuclideanSpaceNotation.0.NumStability.term𝔼": (
        "NumStability.Analysis.LinearOperators.NumericalRadius.Berger.Internal."
        "HermitianEuclideanSpaceNotation"
    ),
    "_private.NumStability.Analysis.LinearOperators.NumericalRadius.Core.Internal."
    "EuclideanSpaceNotation.0.NumStability.term𝔼": (
        "NumStability.Analysis.LinearOperators.NumericalRadius.Core.Internal."
        "EuclideanSpaceNotation"
    ),
    "_private.NumStability.Analysis.LinearOperators.Pseudospectra.Resolvent.Internal."
    "ScalarNotation.0.NumStability.«term↑ₐ»": (
        "NumStability.Analysis.LinearOperators.Pseudospectra.Resolvent.Internal."
        "ScalarNotation"
    ),
}
SHA256_RE = re.compile(r"^[0-9a-fA-F]{64}$")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def git(control: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=control, check=True, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    ).stdout.strip()


def absolute_without_resolving(path: Path) -> Path:
    """Make an absolute path without allowing a final symlink to hide its spelling."""
    return Path(os.path.abspath(path))


def tracked_or_staged(root: Path, relative: Path) -> tuple[bool, bool]:
    tracked = bool(git(root, "ls-files", "--cached", "--", relative.as_posix()))
    staged = bool(git(root, "diff", "--cached", "--name-only", "--", relative.as_posix()))
    return tracked, staged


def is_ignored(root: Path, relative: Path) -> bool:
    result = subprocess.run(
        ["git", "check-ignore", "--quiet", "--", relative.as_posix()],
        cwd=root,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    return result.returncode == 0


def load_json_object(path: Path) -> dict[str, object]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise ValueError(f"cannot read JSON {path}: {error}") from error
    if not isinstance(value, dict):
        raise ValueError(f"JSON root is not an object: {path}")
    return value


def exact_declaration_summary(data: dict[str, object], label: str) -> dict[str, object]:
    declarations = data.get("declarations")
    if not isinstance(declarations, dict):
        raise ValueError(f"{label} lacks a declaration summary")
    edge_counts = declarations.get("edge_counts")
    graph_metrics = declarations.get("graph_metrics")
    if (
        type(declarations.get("format_version")) is not int
        or declarations.get("format_version") != 2
        or type(declarations.get("declaration_count")) is not int
        or declarations.get("declaration_count") != EXPECTED_DECLARATIONS
        or type(declarations.get("module_count")) is not int
        or declarations.get("module_count") != EXPECTED_MODULES
        or edge_counts != EXPECTED_EDGE_COUNTS
        or declarations.get("visibility_counts") != EXPECTED_VISIBILITY_COUNTS
        or declarations.get("kind_counts") != EXPECTED_KIND_COUNTS
        or not isinstance(graph_metrics, dict)
        or any(graph_metrics.get(key) != value for key, value in EXPECTED_GRAPH_METRICS.items())
    ):
        raise ValueError(
            f"{label} does not report the exact four-root format-2 census "
            f"({EXPECTED_DECLARATIONS} declarations, {EXPECTED_MODULES} modules, "
            f"{EXPECTED_EDGE_COUNTS['signature']} signature, "
            f"{EXPECTED_EDGE_COUNTS['body_or_proof']} body, and "
            f"{EXPECTED_EDGE_COUNTS['union']} union edges)"
        )
    return declarations


def validate_closed_tsv(path: Path) -> None:
    declarations: dict[str, tuple[str, str, str]] = {}
    incident: set[str] = set()
    try:
        stream = path.open(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        raise ValueError(f"cannot open four-root extractor output: {error}") from error
    try:
        for line_number, row in enumerate(stream, start=1):
            fields = row.rstrip("\r\n").split("\t")
            if fields[:1] == ["declaration"] and len(fields) == 5:
                if fields[1] in EXPECTED_ISOLATED_ROWS:
                    if fields[1] in declarations:
                        raise ValueError(
                            "four-root extractor duplicated isolated declaration "
                            f"{fields[1]} at line {line_number}"
                        )
                    declarations[fields[1]] = (fields[2], fields[3], fields[4])
            elif fields[:1] == ["edge"] and len(fields) in {4, 6}:
                for endpoint in (fields[2], fields[3]):
                    if endpoint in EXPECTED_ISOLATED_ROWS:
                        incident.add(endpoint)
    except UnicodeError as error:
        raise ValueError(f"four-root extractor output is not UTF-8: {error}") from error
    finally:
        stream.close()
    for name, module in EXPECTED_ISOLATED_ROWS.items():
        if declarations.get(name) != (module, "definition", "private"):
            raise ValueError(f"four-root extraction lacks exact isolated private row {name}")
        if name in incident:
            raise ValueError(f"isolated private row unexpectedly has a project edge: {name}")


def closed_extractor_bytes(extractor: Path) -> bytes:
    if digest(extractor) != EXTRACTOR_SHA:
        raise ValueError(f"official declaration extractor hash mismatch: {extractor}")
    text = extractor.read_text(encoding="utf-8")
    if text.count(EXTRACTOR_LOAD_LINE) != 1:
        raise ValueError("official declaration extractor load site is not unique")
    entries = ",\n".join(f"    {{ module := `{module} }}" for module in EXTRACTION_MODULES)
    replacement = f"  withImportModules #[\n{entries}\n  ] {{}} fun env => do"
    return text.replace(EXTRACTOR_LOAD_LINE, replacement).encode("utf-8")


def run_checked(command: list[str], cwd: Path, label: str) -> bytes:
    result = subprocess.run(
        command, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    if result.returncode:
        if result.stdout:
            sys.stdout.buffer.write(result.stdout)
        raise ValueError(f"{label} failed with exit code {result.returncode}")
    return result.stdout


def regenerate_closed_candidate(worker: Path) -> tuple[dict[str, bytes], str]:
    generator = worker / "tools/architecture/generate_baseline.py"
    extractor = worker / "tools/architecture/declaration_dependencies.lean"
    if digest(generator) != GENERATOR_SHA:
        raise ValueError(f"official baseline generator hash mismatch: {generator}")
    extractor_bytes = closed_extractor_bytes(extractor)
    extractor_digest = hashlib.sha256(extractor_bytes).hexdigest().upper()
    if extractor_digest != CLOSED_EXTRACTOR_SHA:
        raise ValueError("derived four-root declaration extractor hash mismatch")
    with tempfile.TemporaryDirectory(prefix="r07-closed-projection-") as temporary:
        temporary_root = Path(temporary).resolve()
        try:
            temporary_root.relative_to(worker)
        except ValueError:
            pass
        else:
            raise ValueError("temporary extraction directory must be outside the worker checkout")
        temporary_extractor = temporary_root / "declaration_dependencies_r07.lean"
        temporary_tsv = temporary_root / f"{CANDIDATE_STEM}.tsv"
        temporary_extractor.write_bytes(extractor_bytes)
        run_checked(
            [
                "lake", "env", "lean", "--run", str(temporary_extractor),
                str(temporary_tsv),
            ],
            worker,
            "hash-pinned four-root Lean extraction",
        )
        run_checked(
            [
                sys.executable, "-B", str(generator), "--no-build",
                "--dependency-tsv", str(temporary_tsv),
                "--output-dir", str(temporary_root), "--name", CANDIDATE_STEM,
            ],
            worker,
            "official candidate companion generation",
        )
        validate_closed_tsv(temporary_tsv)
        temporary_bytes = temporary_tsv.read_bytes()
        temporary_json = temporary_root / f"{CANDIDATE_STEM}.json"
        temporary_markdown = temporary_root / f"{CANDIDATE_STEM}.md"
        data = load_json_object(temporary_json)
        exact_declaration_summary(data, "regenerated candidate")
        artifacts = {
            "tsv": temporary_bytes,
            "json": temporary_json.read_bytes(),
            "md": temporary_markdown.read_bytes(),
        }
    return artifacts, extractor_digest


def atomic_write(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary_name, path)
    except BaseException:
        try:
            os.unlink(temporary_name)
        except FileNotFoundError:
            pass
        raise


def file_matches_bytes(path: Path, data: bytes) -> bool:
    if not path.is_file() or path.stat().st_size != len(data):
        return False
    view = memoryview(data)
    offset = 0
    with path.open("rb") as stream:
        while offset < len(view):
            block = stream.read(min(1024 * 1024, len(view) - offset))
            if not block or block != view[offset:offset + len(block)]:
                return False
            offset += len(block)
        return stream.read(1) == b""


def candidate_policy_problems(
    worker: Path, artifacts: tuple[Path, ...], *, require_files: bool
) -> list[str]:
    problems: list[str] = []
    for artifact in artifacts:
        try:
            relative = artifact.relative_to(worker)
        except ValueError:
            problems.append(f"candidate artifact escapes worker checkout: {artifact}")
            continue
        if artifact.is_symlink():
            problems.append(f"candidate artifact must not be a symlink: {artifact}")
        if not artifact.is_file():
            if require_files:
                problems.append(f"candidate artifact missing: {artifact}")
        else:
            try:
                artifact.resolve(strict=True).relative_to(worker)
            except (OSError, ValueError):
                problems.append(f"candidate artifact resolves outside worker checkout: {artifact}")
            if artifact.stat().st_size == 0:
                problems.append(f"candidate artifact is empty: {artifact}")
        try:
            tracked, staged = tracked_or_staged(worker, relative)
        except (OSError, subprocess.CalledProcessError) as error:
            problems.append(f"cannot inspect candidate artifact index state {artifact}: {error}")
            continue
        if tracked:
            problems.append(f"candidate artifact must be untracked: {artifact}")
        if staged:
            problems.append(f"candidate artifact must not be staged: {artifact}")
        if not is_ignored(worker, relative):
            problems.append(f"candidate artifact must be ignored: {artifact}")
    return problems


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "candidate", nargs="?", type=Path, default=WORKER_ROOT / CANDIDATE_RELATIVE,
        help="must be benchmark-results/R07-candidate.tsv in this worker checkout",
    )
    parser.add_argument("--control-root", required=True, type=Path)
    parser.add_argument(
        "--materialize-candidate", action="store_true",
        help="atomically replace the ignored candidate trio from the exact four-root extractor",
    )
    args = parser.parse_args()
    control = args.control_root.resolve()
    worker = WORKER_ROOT
    candidate = absolute_without_resolving(args.candidate)
    expected_candidate = absolute_without_resolving(worker / CANDIDATE_RELATIVE)
    json_path = expected_candidate.with_suffix(".json")
    markdown_path = expected_candidate.with_suffix(".md")
    candidate_artifacts = (expected_candidate, json_path, markdown_path)
    problems: list[str] = []
    worker_head: str | None = None

    try:
        worker_git_root = Path(git(worker, "rev-parse", "--show-toplevel")).resolve()
    except (OSError, subprocess.CalledProcessError) as error:
        problems.append(f"cannot identify worker checkout: {error}")
    else:
        if worker_git_root != worker:
            problems.append(
                f"checker is not running from its worker checkout: {worker_git_root} != {worker}"
            )
        try:
            worker_head = git(worker, "rev-parse", "HEAD")
            if worker_head != WORKER_HEAD:
                parent_line = git(worker, "rev-list", "--parents", "-n", "1", worker_head)
                parents = parent_line.split()
                if len(parents) != 2 or parents[1] != WORKER_HEAD:
                    problems.append(
                        "worker checkout is neither exact C0005 code nor its single delivery child"
                    )
        except (OSError, subprocess.CalledProcessError) as error:
            problems.append(f"cannot inspect worker HEAD: {error}")
    if candidate != expected_candidate:
        problems.append(
            f"candidate must be exactly {expected_candidate}; received {candidate}"
        )
    if args.materialize_candidate and worker_head != WORKER_HEAD:
        problems.append("candidate materialization is permitted only at exact C0005 code")

    try:
        if git(control, "rev-parse", "HEAD") != CONTROL_HEAD:
            problems.append("control checkout is not the activated R07 control commit")
    except (OSError, subprocess.CalledProcessError) as error:
        problems.append(f"cannot inspect control checkout: {error}")
    record_path = control / PHASE / "projections" / "P0010.json"
    graph_path = control / PHASE / "projections" / "P0010.tsv.gz"
    checker_path = control / "tools/architecture/check_completion_phase_projection.py"
    private_path = control / PHASE / "branches" / "B0010-private-normalization.tsv"
    expected_files = [
        (record_path, P_RECORD_SHA, None), (graph_path, P_GZIP_SHA, P_GZIP_SIZE),
        (checker_path, CHECKER_SHA, None), (private_path, PRIVATE_SHA, None),
    ]
    for path, expected_sha, expected_size in expected_files:
        if not path.is_file():
            problems.append(f"missing control artifact: {path}")
            continue
        if digest(path) != expected_sha:
            problems.append(f"control artifact hash mismatch: {path}")
        if expected_size is not None and path.stat().st_size != expected_size:
            problems.append(f"control artifact size mismatch: {path}")
    problems.extend(
        candidate_policy_problems(
            worker, candidate_artifacts, require_files=not args.materialize_candidate
        )
    )
    if problems:
        for problem in problems:
            print(f"error: {problem}", file=sys.stderr)
        return 2

    try:
        regenerated, closed_extractor_sha = regenerate_closed_candidate(worker)
    except (OSError, UnicodeError, subprocess.CalledProcessError, ValueError) as error:
        print(f"error: cannot regenerate exact four-root candidate: {error}", file=sys.stderr)
        return 2
    expected_bytes = {
        expected_candidate: regenerated["tsv"],
        json_path: regenerated["json"],
        markdown_path: regenerated["md"],
    }
    if args.materialize_candidate:
        try:
            for path, data in expected_bytes.items():
                atomic_write(path, data)
        except OSError as error:
            print(f"error: cannot materialize candidate evidence: {error}", file=sys.stderr)
            return 2
        print("candidate_materialization: replaced exact ignored TSV/JSON/Markdown trio")
    else:
        if not file_matches_bytes(expected_candidate, regenerated["tsv"]):
            print(
                "error: candidate TSV is not the byte-exact four-root Lean extraction",
                file=sys.stderr,
            )
            return 2
    final_policy = candidate_policy_problems(worker, candidate_artifacts, require_files=True)
    if final_policy:
        for problem in final_policy:
            print(f"error: {problem}", file=sys.stderr)
        return 2

    try:
        record = load_json_object(record_path)
        candidate_json = load_json_object(json_path)
    except ValueError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    if record.get("status") != "active" or record.get("projection_id") != "P0010":
        print("error: P0010 record is not active", file=sys.stderr)
        return 2
    if record.get("expected_counts") != {
        "body_edges": 752, "declarations": 194,
        "signature_edges": 243, "union_edges": 775,
    }:
        print("error: P0010 expected counts drifted", file=sys.stderr)
        return 2
    contract = record.get("checker")
    if not isinstance(contract, dict):
        print("error: P0010 checker contract is missing or malformed", file=sys.stderr)
        return 2
    if contract.get("artifact") != {
        "path": "tools/architecture/check_completion_phase_projection.py",
        "sha256": CHECKER_SHA,
    }:
        print("error: P0010 checker artifact contract drifted", file=sys.stderr)
        return 2
    recorded = contract.get("arguments")
    if not isinstance(recorded, list) or not all(
        isinstance(item, str) for item in recorded
    ):
        print("error: P0010 checker arguments are missing or malformed", file=sys.stderr)
        return 2
    if len(recorded) != 80:
        print(f"error: P0010 argument count {len(recorded)}, expected 80", file=sys.stderr)
        return 2
    allow_modules = [item for item in recorded if item.startswith("--allow-module=")]
    allow_prefixes = [item for item in recorded if item.startswith("--allow-prefix=")]
    placeholders = [item for item in recorded if item == "--candidate=<candidate-format2.tsv>"]
    if len(allow_modules) != 75 or allow_prefixes or len(placeholders) != 1:
        print("error: P0010 allow-list/placeholder contract drifted", file=sys.stderr)
        return 2

    source = candidate_json.get("source")
    if not isinstance(source, dict):
        print("error: candidate JSON lacks a source object", file=sys.stderr)
        return 2
    try:
        declarations = exact_declaration_summary(candidate_json, "candidate JSON")
    except ValueError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    edge_counts = declarations["edge_counts"]
    declaration_count = declarations["declaration_count"]
    signature_edges = edge_counts["signature"]
    body_edges = edge_counts["body_or_proof"]
    source_tree_sha = source.get("source_tree_sha256")
    if not isinstance(source_tree_sha, str) or not SHA256_RE.fullmatch(source_tree_sha):
        print("error: candidate JSON has no valid source.source_tree_sha256", file=sys.stderr)
        return 2
    if source_tree_sha.upper() != EXPECTED_SOURCE_TREE_SHA:
        print(
            "error: candidate source tree does not match the final reviewed R07 worker sources",
            file=sys.stderr,
        )
        return 2

    provenance_command = [
        sys.executable,
        "-B",
        str(worker / "tools/architecture/generate_baseline.py"),
        "--no-build",
        "--dependency-tsv",
        str(expected_candidate),
        "--output-dir",
        str(expected_candidate.parent),
        "--name",
        CANDIDATE_STEM,
        "--check",
    ]
    provenance = subprocess.run(
        provenance_command,
        cwd=worker,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    if provenance.stdout:
        print(provenance.stdout, end="")
    if provenance.returncode:
        print(
            "error: generate_baseline.py replay rejected the candidate pair or "
            "its source-tree provenance",
            file=sys.stderr,
        )
        return provenance.returncode

    command = [sys.executable, "-B", str(checker_path)]
    for item in recorded:
        if item == "--candidate=<candidate-format2.tsv>":
            command.append(f"--candidate={candidate}")
        else:
            command.append(item)
    candidate_sha = digest(candidate)
    command.append(f"--candidate-sha256={candidate_sha}")
    result = subprocess.run(
        command, cwd=control, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    print(result.stdout, end="")
    if result.returncode:
        return result.returncode
    expected_lines = {
        "phase projection contract passed",
        "selected_declarations: 194", "relocated_declarations: 194",
        "signature_edges: 243", "body_edges: 752",
        "candidate_declarations_scanned: 56903",
        "candidate_edges_scanned: 649259",
        "allowed_exact_modules: 75", "allowed_prefixes: 0",
        f"private_map_sha256: {PRIVATE_SHA}", "private_normalizations: 44",
    }
    actual_lines = set(result.stdout.splitlines())
    missing = sorted(expected_lines - actual_lines)
    if missing:
        for line in missing:
            print(f"error: checker output missing exact result {line!r}", file=sys.stderr)
        return 1
    print("candidate_baseline_check: passed")
    print("candidate_extraction_roots: " + ",".join(EXTRACTION_MODULES))
    print(f"candidate_official_extractor_sha256: {EXTRACTOR_SHA}")
    print(f"candidate_closed_extractor_sha256: {closed_extractor_sha}")
    print(f"candidate_generator_sha256: {GENERATOR_SHA}")
    print(f"candidate_declarations: {declaration_count}")
    print(f"candidate_modules_with_declarations: {declarations['module_count']}")
    print(f"candidate_signature_edges: {signature_edges}")
    print(f"candidate_body_edges: {body_edges}")
    print(f"candidate_union_edges: {edge_counts['union']}")
    print(f"candidate_typed_edges: {signature_edges + body_edges}")
    print(f"candidate_source_tree_sha256: {source_tree_sha.upper()}")
    for label, artifact in (
        ("tsv", expected_candidate), ("json", json_path), ("md", markdown_path)
    ):
        print(f"candidate_{label}_path: {artifact}")
        print(f"candidate_{label}_sha256: {digest(artifact)}")
        print(f"candidate_{label}_size: {artifact.stat().st_size}")
    # Preserve the original TSV evidence labels for existing delivery consumers.
    print(f"candidate_path: {expected_candidate}")
    print(f"candidate_sha256: {candidate_sha}")
    print(f"candidate_size: {expected_candidate.stat().st_size}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
