#!/usr/bin/env python3
"""Chapter 9 fixed-scope interface to the shared semantic-contract checker."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from check_chapter_contract import post_check, pre_check, self_test
from lane_common import PROPOSAL_ROOT


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--contract-root", type=Path, default=PROPOSAL_ROOT / "ch09")
    parser.add_argument("--baseline-zip", type=Path)
    parser.add_argument("--candidate-format2", type=Path)
    parser.add_argument("--mode", choices=["pre", "post", "stage"], default="pre")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return
    if not args.baseline_zip:
        parser.error("--baseline-zip is required")
    if args.mode == "pre":
        result = pre_check(args.contract_root.resolve(), args.baseline_zip.resolve())
    else:
        if not args.candidate_format2:
            parser.error("--candidate-format2 is required for post/stage mode")
        result = post_check(
            args.contract_root.resolve(),
            args.baseline_zip.resolve(),
            args.candidate_format2.resolve(),
            args.mode,
        )
    if result["chapter"] != "09":
        raise ValueError("not a Chapter 9 contract")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
