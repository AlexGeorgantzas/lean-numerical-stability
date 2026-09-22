#!/usr/bin/env python3
"""Provider-free corpus and symmetric retrieval preflight for Pilot 18.

This command never starts a contestant, judge, or timer. Its output is evidence
for admission review, not an audit verdict or a measured benchmark result.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from common import BenchmarkError, load_json, sha256_file
from composition_packets import load_records, rank_records
from component_router import BRIDGES, CORE, FAMILIES, routing_anchor_text, select_component_roots


DESIGN_ROOT = Path(__file__).resolve().parents[1] / "design18"
SOURCE_SCHEMA = "formalization-source-packet-2-draft"


def check_corpus(
    *, design_root: Path = DESIGN_ROOT,
) -> tuple[dict, list[dict], list[str]]:
    corpus = load_json(design_root / "CORPUS_12.json")
    task_ids = corpus.get("task_ids")
    if not isinstance(task_ids, list) or len(task_ids) != 12 or len(set(task_ids)) != 12:
        raise BenchmarkError("Pilot 18 requires twelve distinct task IDs")
    if set(corpus.get("early_review_order", [])) - set(task_ids):
        raise BenchmarkError("early-review order contains an unknown task")
    scheduled = corpus.get("scheduled_order")
    if (not isinstance(scheduled, list) or len(scheduled) != 12
            or set(scheduled) != set(task_ids)
            or scheduled[:3] != corpus["early_review_order"]):
        raise BenchmarkError("frozen task schedule is not a permutation with early canaries first")
    source_pdfs = corpus.get("source_pdfs")
    if not isinstance(source_pdfs, dict):
        raise BenchmarkError("source PDF manifest is malformed")
    for key, item in source_pdfs.items():
        path = design_root / item["file"]
        if path.is_symlink() or not path.is_file() or sha256_file(path) != item["sha256"]:
            raise BenchmarkError(f"frozen PDF hash mismatch: {key}")
    packets: list[dict] = []
    for task_id in task_ids:
        path = design_root / "packets" / f"{task_id}.json"
        if path.is_symlink() or not path.is_file():
            raise BenchmarkError(f"source packet missing or unsafe: {task_id}")
        packet = load_json(path)
        if packet.get("task_id") != task_id or packet.get("schema_version") != SOURCE_SCHEMA:
            raise BenchmarkError(f"draft source packet identity mismatch: {task_id}")
        if not all(isinstance(packet.get(key), list) and packet[key] for key in
                   ("task_clarification", "scope_constraints", "paper_locations")):
            raise BenchmarkError(f"source packet lacks a full contract: {task_id}")
        pdf = packet.get("paper_pdf", {})
        if not any(pdf.get("sha256") == item["sha256"] and
                   pdf.get("path_basename") == Path(item["file"]).name
                   for item in source_pdfs.values()):
            raise BenchmarkError(f"source packet references a non-manifest PDF: {task_id}")
        packets.append(packet)
    extra = {path.stem for path in (design_root / "packets").glob("*.json")} - set(task_ids)
    if extra:
        raise BenchmarkError(f"unexpected Pilot 18 packets: {sorted(extra)}")
    flags = sorted(corpus.get("known_source_review_flags", {}))
    return corpus, packets, flags


def check_retrieval(
    packets: list[dict], *, mathlib_atlas: Path, numstability_atlas: Path,
    root_limit: int = 10,
) -> dict[str, dict[str, list[dict]]]:
    mathlib = load_records([mathlib_atlas])
    numstability = load_records([numstability_atlas])
    if any(str(record.get("module", "")).startswith("NumStability") for record in mathlib):
        raise BenchmarkError("Mathlib-only atlas contains treatment declarations")
    if not any(str(record.get("module", "")).startswith("NumStability")
               for record in numstability):
        raise BenchmarkError("treatment atlas contains no NumStability declarations")
    atlas_names = {record["name"] for record in [*mathlib, *numstability]}
    anchors = {name for _, algorithms, support in FAMILIES.values()
               for name in [*algorithms, *support]}
    anchors.update(name for names in BRIDGES.values() for name in names)
    anchors.update(name for names in CORE.values() for name in names)
    if missing := sorted(anchors - atlas_names):
        raise BenchmarkError(f"API catalog anchors absent from frozen atlases: {missing}")
    conditions = {"R0": mathlib, "R1": sorted(
        [*mathlib, *numstability], key=lambda record: (record.get("module", ""), record["name"])
    )}
    result: dict[str, dict[str, list[dict]]] = {}
    for packet in packets:
        task_id = packet["task_id"]
        result[task_id] = {}
        for condition, records in conditions.items():
            ranked = rank_records(packet, records)
            cards = select_component_roots(
                ranked, records=records,
                source_text=routing_anchor_text(packet), limit=root_limit
            )
            result[task_id][condition] = [
                {"role": card["component_role"], "name": card["record"]["name"],
                 "module": card["record"].get("module"), "api_anchor": card["api_anchor"]}
                for card in cards
            ]
        if any(str(card["module"]).startswith("NumStability")
               for card in result[task_id]["R0"]):
            raise BenchmarkError(f"R0 treatment leakage: {task_id}")
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib-atlas", type=Path, required=True)
    parser.add_argument("--numstability-atlas", type=Path, required=True)
    args = parser.parse_args()
    from design18_atlas import verify_release_atlas
    for kind, declarations in (("mathlib", args.mathlib_atlas),
                               ("numstability", args.numstability_atlas)):
        root = verify_release_atlas(kind, declarations.parent)
        if declarations.resolve() != root / "declarations.jsonl":
            raise BenchmarkError(f"Pilot 18 {kind} declarations path is not the release file")
    corpus, packets, flags = check_corpus()
    common_prompt = (DESIGN_ROOT / "prompts" / "common.md").read_bytes()
    library_appendix = (DESIGN_ROOT / "prompts" / "library_appendix.md").read_bytes()
    if not common_prompt or not library_appendix or not library_appendix.startswith(b"\n"):
        raise BenchmarkError("Pilot 18 condition prompts are malformed")
    prompts = {"R0": common_prompt, "R1": common_prompt + library_appendix}
    retrieval = check_retrieval(
        packets, mathlib_atlas=args.mathlib_atlas,
        numstability_atlas=args.numstability_atlas,
    )
    print(json.dumps({
        "schema_version": "pilot-18-provider-free-preflight-1",
        "admission_status": "NOT_ADMITTED_SOURCE_FLAGS" if flags else "SOURCE_REVIEW_PENDING",
        "task_ids": corpus["task_ids"],
        "known_source_review_flags": flags,
        "model_gate": "not_checked_by_provider_free_preflight",
        "atlas_sha256": {"mathlib": sha256_file(args.mathlib_atlas),
                         "numstability": sha256_file(args.numstability_atlas)},
        "prompt_sha256": {key: hashlib.sha256(value).hexdigest()
                          for key, value in prompts.items()},
        "r1_prompt_has_exact_r0_prefix": prompts["R1"].startswith(prompts["R0"]),
        "retrieval": retrieval,
    }, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError, KeyError) as error:
        raise SystemExit(f"Pilot 18 preflight error: {error}") from error
