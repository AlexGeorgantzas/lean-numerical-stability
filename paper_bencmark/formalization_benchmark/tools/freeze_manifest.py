#!/usr/bin/env python3
"""Regenerate the source-first pilot's self-hashed release manifest.

This is a release-authoring command, never an admission command. Measurement
code only verifies the resulting bytes and must not invoke this script.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

from common import load_json, sha256_file, write_json_atomic
from manifest_control import (
    EXPECTED_BASE_COMMIT,
    MANIFEST_PATH,
    REPOSITORY_ROOT,
    ROOT,
    manifest_payload_sha256,
)


TASK_IDS = ["P01-T2", "P02-T2", "P03-T2", "P13-T2", "P14-T2"]
REPOSITORY_DEPENDENCIES = [
    ".codex/skills/run-highambench-experiments/SKILL.md",
    ".codex/skills/run-highambench-experiments/agents/openai.yaml",
    ".codex/skills/run-highambench-experiments/references/operations.md",
    "lakefile.toml",
    "lake-manifest.json",
    "lean-toolchain",
    "paper_bencmark/highambench/tools/offline_shell.c",
]


def file_ref(path: Path) -> dict[str, str]:
    return {"relative_path": path.relative_to(ROOT).as_posix(), "sha256": sha256_file(path)}


def build() -> dict:
    config_path = ROOT / "config.json"
    config = load_json(config_path)
    if config.get("task_ids") != TASK_IDS:
        raise RuntimeError("config task order is not the frozen pilot order")
    tasks = []
    for task_id in TASK_IDS:
        packet_path = ROOT / "packets" / f"{task_id}.json"
        packet = load_json(packet_path)
        if packet.get("task_id") != task_id:
            raise RuntimeError(f"packet ID mismatch: {packet_path}")
        tasks.append(
            {
                "task_id": task_id,
                "source_packet": file_ref(packet_path),
                "source_pdf": packet["paper_pdf"],
            }
        )
    schemas = sorted(
        [*(ROOT / "schemas").glob("*.json"), *(ROOT / "audit" / "schemas").glob("*.json")],
        key=lambda path: path.relative_to(ROOT).as_posix(),
    )
    release_paths = sorted(
        [
            path
            for path in ROOT.rglob("*")
            if path.is_file()
            and path != MANIFEST_PATH
            and "__pycache__" not in path.parts
            and path.suffix != ".pyc"
        ],
        key=lambda path: path.relative_to(ROOT).as_posix(),
    )
    repository_files = []
    for relative in REPOSITORY_DEPENDENCIES:
        path = REPOSITORY_ROOT / relative
        if not path.is_file():
            raise RuntimeError(f"missing repository dependency: {relative}")
        repository_files.append(
            {"repository_relative_path": relative, "sha256": sha256_file(path)}
        )
    value = {
        "schema_version": "formalization-benchmark-manifest-1",
        "pilot_id": config["pilot_id"],
        "base_commit": EXPECTED_BASE_COMMIT,
        "freeze_algorithm": (
            "Every referenced file digest is SHA-256 over raw bytes. The manifest "
            "payload digest is SHA-256 over canonical UTF-8 JSON after removing its "
            "own digest field."
        ),
        "config": file_ref(config_path),
        "schemas": [file_ref(path) for path in schemas],
        "task_count": len(TASK_IDS),
        "task_ids": TASK_IDS,
        "tasks": tasks,
        "release_files": [file_ref(path) for path in release_paths],
        "repository_files": repository_files,
    }
    value["manifest_payload_sha256"] = manifest_payload_sha256(value)
    return value


def make_parser() -> argparse.ArgumentParser:
    return argparse.ArgumentParser(description=__doc__)


def main(argv: list[str] | None = None) -> int:
    raw_arguments = list(sys.argv[1:] if argv is None else argv)
    parser = make_parser()
    if len(raw_arguments) > 1 and any(
        argument in {"-h", "--help"} for argument in raw_arguments
    ):
        parser.error("--help must be used by itself")
    parser.parse_args(raw_arguments)
    # argparse consumes a bare `--`, so retain an explicit raw-argument check:
    # this release-authoring command intentionally has no operational options.
    if raw_arguments:
        parser.error("this command accepts no arguments")
    manifest = build()
    write_json_atomic(MANIFEST_PATH, manifest, mode=0o644)
    print(manifest["manifest_payload_sha256"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
