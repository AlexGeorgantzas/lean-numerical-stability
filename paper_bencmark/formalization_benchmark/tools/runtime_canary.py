from __future__ import annotations

import json
import tempfile
from pathlib import Path
from typing import Any

from common import BenchmarkError, sha256_bytes, utc_now
from deployment import Deployment
from formalization_validator import validate_candidate
from lean_sandbox import compiler_command


def _candidate(import_name: str) -> str:
    return f"""import {import_name}

namespace HighamBenchCandidate

theorem target : True := by sorry

end HighamBenchCandidate
"""


def _compile_probe(
    deployment: Deployment,
    *,
    condition: str,
    import_name: str,
    root: Path,
) -> dict[str, Any]:
    probe_root = root / f"{condition}-{import_name}"
    probe_root.mkdir()
    candidate = probe_root / "Candidate.lean"
    source = _candidate(import_name)
    candidate.write_text(source, encoding="utf-8")
    result = validate_candidate(
        candidate,
        compiler_command=compiler_command(deployment, condition),
        compiler_environment={},
        scratch_root=probe_root,
        timeout_seconds=300,
    )
    return {
        "condition": condition,
        "import": import_name,
        "candidate_sha256": sha256_bytes(source.encode("utf-8")),
        "pass": result["pass"],
        "failure_code": result["failure_code"],
        "compile_returncode": (
            result["compile"].get("returncode")
            if isinstance(result.get("compile"), dict)
            else None
        ),
    }


def run_runtime_canaries(deployment: Deployment) -> dict[str, Any]:
    """Exercise the real no-network compiler boundary without provider calls."""

    deployment.run_root.mkdir(parents=True, exist_ok=True, mode=0o700)
    with tempfile.TemporaryDirectory(
        prefix="formalization-runtime-canary-", dir=deployment.run_root
    ) as temporary:
        root = Path(temporary)
        mathlib_n = _compile_probe(
            deployment, condition="N", import_name="Mathlib", root=root
        )
        library_n = _compile_probe(
            deployment, condition="N", import_name="NumStability", root=root
        )
        library_l = _compile_probe(
            deployment, condition="L", import_name="NumStability", root=root
        )
    if not mathlib_n["pass"]:
        raise BenchmarkError("runtime canary: condition N cannot compile Mathlib")
    if library_n["pass"] or library_n["failure_code"] != "COMPILATION_FAILURE":
        raise BenchmarkError("runtime canary: condition N can import NumStability")
    if not library_l["pass"]:
        raise BenchmarkError("runtime canary: condition L cannot import NumStability")
    return {
        "schema_version": "formalization-runtime-canary-1",
        "completed_at_utc": utc_now(),
        "provider_calls": 0,
        "checks": [mathlib_n, library_n, library_l],
        "admitted": True,
    }
