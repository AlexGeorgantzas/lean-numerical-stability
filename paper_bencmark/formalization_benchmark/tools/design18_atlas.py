"""Bind Pilot-18's corrected task-neutral catalogs to the frozen runtime."""

from __future__ import annotations

from dataclasses import replace
from pathlib import Path

from common import BenchmarkError, load_json, sha256_file
from deployment import Deployment
from design18_preflight import DESIGN_ROOT


def verify_release_atlas(kind: str, path: Path) -> Path:
    if kind not in {"mathlib", "numstability"}:
        raise BenchmarkError("unknown Pilot 18 atlas kind")
    if path.is_symlink() or not path.is_dir():
        raise BenchmarkError(f"Pilot 18 {kind} atlas directory is missing or unsafe")
    release = load_json(DESIGN_ROOT / "ATLAS_RELEASE.json")
    if release.get("schema_version") != "pilot-18-atlas-release-1":
        raise BenchmarkError("Pilot 18 atlas release schema changed")
    expected = release.get(kind)
    if not isinstance(expected, dict):
        raise BenchmarkError(f"Pilot 18 {kind} release record is missing")
    files = expected.get("files")
    if not isinstance(files, dict) or set(files) != {
        "GUIDE.md", "atlas.json", "declarations.jsonl", "modules.tsv",
        "query.py", "show.py",
    }:
        raise BenchmarkError(f"Pilot 18 {kind} release files are malformed")
    actual_files = {item.name for item in path.iterdir()}
    if actual_files != set(files):
        raise BenchmarkError(f"Pilot 18 {kind} atlas has missing or extra files")
    for name, digest in files.items():
        entry = path / name
        if entry.is_symlink() or not entry.is_file() or sha256_file(entry) != digest:
            raise BenchmarkError(f"Pilot 18 {kind} atlas file changed: {name}")
    metadata = load_json(path / "atlas.json")
    for key in ("library_commit", "source_closure_sha256", "declaration_count"):
        if metadata.get(key) != expected.get(key):
            raise BenchmarkError(f"Pilot 18 {kind} atlas identity changed: {key}")
    if (metadata.get("declarations_sha256") != expected.get("declarations_sha256")
            or expected.get("atlas_json_sha256") != files["atlas.json"]
            or expected.get("declarations_sha256") != files["declarations.jsonl"]):
        raise BenchmarkError(f"Pilot 18 {kind} catalog hash changed")
    return path.resolve()


def bind_release_atlases(deployment: Deployment, *, mathlib: Path,
                         numstability: Path) -> tuple[Deployment, Path]:
    """Keep the old deployment immutable; replace only its discovery catalog."""
    mathlib_path = verify_release_atlas("mathlib", mathlib)
    numstability_path = verify_release_atlas("numstability", numstability)
    old_metadata = load_json(deployment.library_atlas / "atlas.json")
    new_metadata = load_json(numstability_path / "atlas.json")
    for key in ("library_commit", "source_closure_sha256", "declaration_count"):
        if old_metadata.get(key) != new_metadata.get(key):
            raise BenchmarkError("Pilot 18 atlas does not index the deployed library snapshot")
    return replace(deployment, library_atlas=numstability_path), mathlib_path
