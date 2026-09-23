#!/usr/bin/env python3
"""Prepare one verified task-neutral warm conversation for Pilot 27."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

from common import BenchmarkError
from design18_envelope import launch_or_activate
from design18_prepare_warm_root import prepare


PROMPT = Path(__file__).resolve().parents[1] / "design27" / "prompts" / "scout.md"
SCHEMA = "pilot-27-warm-root-1"


def main() -> int:
    launched = launch_or_activate(Path(__file__))
    if launched is not None:
        return launched
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("deployment", "mathlib-atlas", "numstability-atlas",
                 "model-qualification", "output-root"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    record = prepare(
        deployment_path=args.deployment,
        mathlib_atlas=args.mathlib_atlas,
        numstability_atlas=args.numstability_atlas,
        model_qualification=args.model_qualification,
        output_root=args.output_root,
        scout_prompt=PROMPT,
        schema_version=SCHEMA,
        require_pilot18_corpus=False,
        required_final_terms=("FPModel", "BasicOp", "gamma", "gammaValid"),
        model="gpt-6-sol",
        effort="high",
        qualification_schema="pilot-20-model-qualification-1",
    )
    print(json.dumps({
        key: record[key]
        for key in ("status", "model", "scout_usage", "scout_wall_seconds")
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError) as error:
        print(f"Pilot 27 warm-root error: {error}", file=sys.stderr)
        raise SystemExit(2)
