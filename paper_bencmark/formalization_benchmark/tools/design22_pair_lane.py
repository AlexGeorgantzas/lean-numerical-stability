#!/usr/bin/env python3
"""Run one frozen development pair inside its own Titan lane."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

from common import BenchmarkError
from design20_envelope import launch_or_activate
from design20_matched import run


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("deployment", "mathlib-atlas", "numstability-atlas",
                 "model-qualification", "warm-root", "output-root"):
        parser.add_argument("--" + name, required=True, type=Path)
    parser.add_argument("--task-id", required=True)
    parser.add_argument("--condition-order", required=True)
    parser.add_argument("--lane", required=True, choices=("A", "B", "C"))
    args = parser.parse_args()
    launched = launch_or_activate(Path(__file__), lane=args.lane)
    if launched is not None:
        return launched
    pair = run(args)
    print(json.dumps({"task_id": pair["task_id"], "status": pair["status"],
                      "lane": args.lane, "faithfulness_status": pair.get("faithfulness_status")},
                     sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError) as error:
        print(f"Development lane pair error: {error}", file=sys.stderr)
        raise SystemExit(2)
