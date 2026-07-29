#!/usr/bin/env python3
"""Review-safe application helper for an approved classification TSV."""

from __future__ import annotations

import argparse
import json
import tempfile
from pathlib import Path

from lane_common import CLASSIFICATION_ROOT, ROOT, read_tsv


SHARED_MANIFEST = (ROOT / "docs/architecture/tiers.json").resolve()
TIER_MAP = {"mixed_pending_split": "mixed"}


def proposed_manifest(input_path: Path, proposal_path: Path) -> dict[str, object]:
    manifest = json.loads(input_path.read_text(encoding="utf-8"))
    rows = read_tsv(proposal_path)
    exact = dict(manifest.get("exact", {}))
    allowed = set(manifest.get("tiers", []))
    for row in rows:
        tier = TIER_MAP.get(row["proposed_tier"], row["proposed_tier"])
        if tier not in allowed:
            raise ValueError(f"unsupported target tier {tier!r}")
        exact[row["module"]] = tier
    manifest["exact"] = dict(sorted(exact.items()))
    return manifest


def apply(input_path: Path, proposal_path: Path, output_path: Path) -> None:
    paths = [input_path.resolve(), proposal_path.resolve(), output_path.resolve()]
    if output_path.resolve() in paths[:2]:
        raise ValueError("output must differ from both input files")
    if output_path.resolve() == SHARED_MANIFEST:
        raise ValueError("refusing to overwrite the shared tiers manifest")
    manifest = proposed_manifest(input_path, proposal_path)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )


def self_test() -> None:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        manifest = root / "tiers.json"
        proposal = root / "proposal.tsv"
        output = root / "out.json"
        manifest.write_text(
            json.dumps({"tiers": ["reusable", "mixed"], "exact": {}}), encoding="utf-8"
        )
        proposal.write_text(
            "module\tproposed_tier\nA\treusable\nB\tmixed_pending_split\n", encoding="utf-8"
        )
        apply(manifest, proposal, output)
        result = json.loads(output.read_text(encoding="utf-8"))
        assert result["exact"] == {"A": "reusable", "B": "mixed"}
        for forbidden in (manifest, proposal, SHARED_MANIFEST):
            try:
                apply(manifest, proposal, forbidden)
            except ValueError:
                pass
            else:
                raise AssertionError(f"unsafe output accepted: {forbidden}")
    print("apply_tier_proposal self-test: PASS")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=SHARED_MANIFEST)
    parser.add_argument(
        "--proposal", type=Path, default=CLASSIFICATION_ROOT / "modules.tsv"
    )
    parser.add_argument("--output", type=Path)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return
    if args.check:
        result = proposed_manifest(args.input, args.proposal)
        print(
            f"apply_tier_proposal check: PASS "
            f"({len(read_tsv(args.proposal))} proposal rows, {len(result['exact'])} exact entries)"
        )
        return
    if not args.output:
        parser.error("--output is required unless --self-test or --check is used")
    apply(args.input, args.proposal, args.output)


if __name__ == "__main__":
    main()
