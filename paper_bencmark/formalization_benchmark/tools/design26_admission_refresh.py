#!/usr/bin/env python3
"""Bind unchanged source admissions to a new hash-verified corpus preflight."""

from __future__ import annotations

import argparse
from pathlib import Path

from common import (BenchmarkError, load_json, sha256_file, write_json_atomic)
from deployment import load_deployment
from design20_admission import verify_admission
from design20_matched import ROOT


def refresh(*, previous: Path, preflight: Path, corpus: Path,
            deployment_path: Path, output: Path) -> dict:
    if not output.is_absolute() or output.exists() or output.is_symlink():
        raise BenchmarkError("new admission must have a fresh absolute path")
    old = load_json(previous)
    check = load_json(preflight)
    schedule = load_json(corpus)["scheduled_order"]
    if (old.get("schema_version") != "pilot-20-development-admission-1"
            or set(old.get("tasks", {})) != set(schedule)
            or check.get("status") != "PASS"
            or check.get("corpus_sha256") != sha256_file(corpus)
            or set(check.get("tasks", {})) != set(schedule)):
        raise BenchmarkError("previous admission or new preflight does not match corpus")
    record = dict(old)
    record.update({
        "scope": "Pilot 26 twelve-task adaptive exploratory development corpus; Pilot 25 preserved separately; not confirmatory",
        "previous_admission_sha256": sha256_file(previous),
        "static_preflight_path": str(preflight.resolve()),
        "static_preflight_sha256": sha256_file(preflight),
    })
    output.parent.mkdir(parents=True, exist_ok=True)
    write_json_atomic(output, record, mode=0o400)
    deployment = load_deployment(deployment_path)
    for task in schedule:
        packet_path = ROOT / "packets" / f"{task}.json"
        packet = load_json(packet_path)
        paper = ROOT / "sources" / packet["paper_pdf"]["path_basename"]
        if not paper.is_file():
            paper = deployment.pdf_root / packet["paper_pdf"]["path_basename"]
        verify_admission(task, packet_path=packet_path, paper=paper,
                         admission_path=output, corpus_path=corpus)
    return record


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("previous", "preflight", "corpus", "deployment", "output"):
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    refresh(previous=args.previous, preflight=args.preflight,
            corpus=args.corpus, deployment_path=args.deployment,
            output=args.output)
    print(f"PASS {args.output}")


if __name__ == "__main__":
    try:
        main()
    except (BenchmarkError, OSError, ValueError, KeyError, TypeError) as error:
        raise SystemExit(f"Pilot 26 admission refresh failed: {error}")
