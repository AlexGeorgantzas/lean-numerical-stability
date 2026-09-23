#!/usr/bin/env python3
"""One-shot GPT-6 Sol/high qualification for prospective Pilot 20."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

from common import BenchmarkError
from design18_envelope import launch_or_activate
from design18_model_qualify import qualify


def main() -> int:
    launched = launch_or_activate(Path(__file__))
    if launched is not None:
        return launched
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--deployment", required=True, type=Path)
    parser.add_argument("--output-root", required=True, type=Path)
    args = parser.parse_args()
    result = qualify(
        deployment_path=args.deployment,
        output_root=args.output_root,
        model="gpt-6-sol",
        effort="high",
        schema_version="pilot-20-model-qualification-1",
    )
    print(json.dumps({key: result[key] for key in
                      ("status", "model", "reasoning_effort", "usage", "wall_seconds")},
                     sort_keys=True))
    return 0 if result["status"] == "PASS" else 2


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError) as error:
        print(f"Pilot 20 qualification error: {error}", file=sys.stderr)
        raise SystemExit(2)
