#!/usr/bin/env python3
"""Deterministically apply the classification proposal to a *copy* of a tier manifest.

This tool is review-safe by construction:

* it reads an explicit ``--input-tiers`` manifest and an explicit ``--proposal``;
* it writes only to an explicit ``--output`` path;
* it refuses to write to its input, to ``docs/architecture/tiers.json``, or to
  any path under ``docs/architecture/`` that is not clearly a review copy;
* it never edits Lean sources, aggregates, or layout exceptions;
* it preserves every unrelated manifest entry and the manifest's formatting
  (two-space indentation, sorted keys, trailing newline);
* rows whose ``required_action`` is ``defer_pending_upstream_split`` are skipped
  unless ``--include-deferred`` is passed, so the applied manifest can never
  introduce a forbidden reusable-to-source edge;
* ``mixed_pending_split`` rows are registered as the manifest's ``mixed`` tier,
  which is the repository's explicit split queue.

``--check`` compares an existing output against what would be written and fails
on any difference.  ``--self-test`` exercises the merge, the refusals, and the
deferral policy on in-memory fixtures.
"""

from __future__ import annotations

import argparse
import json
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import lane_policy
import module_evidence as me


ROOT = Path(__file__).resolve().parents[3]
SHARED_MANIFEST = ROOT / "docs/architecture/tiers.json"
DEFAULT_PROPOSAL = (
    ROOT / "docs/architecture/lane-proposals/claude-classification/classification/modules.tsv"
)
MANIFEST_TIER = {"mixed_pending_split": "mixed"}
DEFERRED_ACTION = "defer_pending_upstream_split"


class ApplyError(RuntimeError):
    pass


def render_manifest(manifest: dict) -> str:
    return json.dumps(manifest, indent=2, sort_keys=False) + "\n"


def merge(manifest: dict, rows: list[dict[str, str]], include_deferred: bool) -> tuple[dict, dict]:
    """Return ``(new_manifest, report)`` without mutating ``manifest``."""

    if manifest.get("schema_version") != 1:
        raise ApplyError("unsupported tier manifest schema")
    allowed = set(manifest.get("tiers", ()))
    if not allowed:
        raise ApplyError("tier manifest declares no tiers")

    updated = json.loads(json.dumps(manifest))
    exact = updated.get("exact")
    if not isinstance(exact, dict):
        raise ApplyError("tier manifest has no 'exact' object")

    added: dict[str, str] = {}
    skipped_deferred: list[str] = []
    conflicts: list[str] = []
    for row in rows:
        module = row["module"]
        tier = MANIFEST_TIER.get(row["proposed_tier"], row["proposed_tier"])
        if tier not in allowed:
            raise ApplyError(f"{module}: tier {tier!r} is not declared by the manifest")
        if row["required_action"] == DEFERRED_ACTION and not include_deferred:
            skipped_deferred.append(module)
            continue
        if module in exact:
            if exact[module] != tier:
                conflicts.append(f"{module}: manifest has {exact[module]!r}, proposal has {tier!r}")
            continue
        added[module] = tier
    if conflicts:
        raise ApplyError("proposal conflicts with the input manifest: " + "; ".join(conflicts))

    exact.update(added)
    updated["exact"] = dict(sorted(exact.items()))
    report = {
        "added": dict(sorted(added.items())),
        "added_count": len(added),
        "skipped_deferred": sorted(skipped_deferred),
        "skipped_deferred_count": len(skipped_deferred),
        "preserved_entries": len(manifest["exact"]),
        "total_entries": len(updated["exact"]),
    }
    return updated, report


def guard_output(output: Path, input_tiers: Path) -> None:
    if output.resolve() == input_tiers.resolve():
        raise ApplyError("refusing to overwrite the input manifest")
    if output.resolve() == SHARED_MANIFEST.resolve():
        raise ApplyError("refusing to write the shared docs/architecture/tiers.json")
    try:
        relative = output.resolve().relative_to(ROOT.resolve())
    except ValueError:
        return
    posix = relative.as_posix()
    if posix.startswith("docs/architecture/") and not posix.startswith(
        "docs/architecture/lane-proposals/claude-classification/"
    ):
        raise ApplyError(
            "refusing to write a shared docs/architecture path; use a lane-owned review copy"
        )


def self_test() -> list[str]:
    problems: list[str] = []
    manifest = {
        "schema_version": 1,
        "tiers": ["reusable", "source", "internal", "upstream", "mixed", "compatibility",
                  "aggregate"],
        "exact": {"NumStability.Kept": "aggregate"},
        "prefixes": [{"prefix": "NumStability.Source", "tier": "source"}],
    }
    rows = [
        {"module": "NumStability.A", "proposed_tier": "source",
         "required_action": "plan_source_extraction"},
        {"module": "NumStability.B", "proposed_tier": "mixed_pending_split",
         "required_action": lane_policy.SPLIT_ACTION_PREFIX + "x -> y; z -> w"},
        {"module": "NumStability.C", "proposed_tier": "reusable",
         "required_action": DEFERRED_ACTION},
    ]
    updated, report = merge(manifest, rows, include_deferred=False)
    if manifest["exact"] != {"NumStability.Kept": "aggregate"}:
        problems.append("merge must not mutate its input manifest")
    if updated["exact"].get("NumStability.Kept") != "aggregate":
        problems.append("unrelated manifest entries must be preserved")
    if updated["exact"].get("NumStability.A") != "source":
        problems.append("a source row must be registered")
    if updated["exact"].get("NumStability.B") != "mixed":
        problems.append("a mixed_pending_split row must register as 'mixed'")
    if "NumStability.C" in updated["exact"]:
        problems.append("a deferred row must be skipped by default")
    if report["skipped_deferred"] != ["NumStability.C"]:
        problems.append("the report must list skipped deferred rows")
    if list(updated["exact"]) != sorted(updated["exact"]):
        problems.append("the merged 'exact' map must be sorted")
    if updated["prefixes"] != manifest["prefixes"]:
        problems.append("prefix rules must be preserved verbatim")
    included, _ = merge(manifest, rows, include_deferred=True)
    if included["exact"].get("NumStability.C") != "reusable":
        problems.append("--include-deferred must register deferred rows")

    try:
        merge({"schema_version": 2}, [], False)
    except ApplyError:
        pass
    else:
        problems.append("an unsupported schema must be rejected")
    try:
        merge(manifest, [{"module": "NumStability.Kept", "proposed_tier": "source",
                          "required_action": "plan_source_extraction"}], False)
    except ApplyError:
        pass
    else:
        problems.append("a conflicting existing entry must be rejected")
    try:
        merge(manifest, [{"module": "NumStability.D", "proposed_tier": "invented",
                          "required_action": "register_tier_only"}], False)
    except ApplyError:
        pass
    else:
        problems.append("an undeclared tier must be rejected")

    with tempfile.TemporaryDirectory() as raw:
        temp = Path(raw)
        source = temp / "tiers-input.json"
        source.write_text(render_manifest(manifest), encoding="utf-8")
        for bad, label in (
            (source, "its own input"),
            (SHARED_MANIFEST, "the shared manifest"),
            (ROOT / "docs/architecture/layout-exceptions.json", "a shared architecture path"),
        ):
            try:
                guard_output(bad, source)
            except ApplyError:
                continue
            problems.append(f"writing {label} must be refused")
        allowed = (
            ROOT
            / "docs/architecture/lane-proposals/claude-classification/classification"
            / "tiers-with-proposal.json"
        )
        try:
            guard_output(allowed, source)
        except ApplyError:
            problems.append("a lane-owned review copy must be allowed")
    return problems


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-tiers", type=Path, default=SHARED_MANIFEST,
                        help="tier manifest to read (never written)")
    parser.add_argument("--proposal", type=Path, default=DEFAULT_PROPOSAL)
    parser.add_argument("--output", type=Path,
                        help="review copy to write; must differ from --input-tiers")
    parser.add_argument("--report", type=Path, help="optional JSON merge report path")
    parser.add_argument("--include-deferred", action="store_true",
                        help="also register rows marked defer_pending_upstream_split")
    parser.add_argument("--check", action="store_true",
                        help="compare an existing --output against the deterministic result")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()

    if args.self_test:
        problems = self_test()
        if problems:
            for problem in problems:
                print(f"ERROR: self-test: {problem}", file=sys.stderr)
            return 1
        print("Apply-tool self-test passed: merge, refusals, and deferral policy verified.")
        return 0

    if args.output is None:
        print("ERROR: --output is required", file=sys.stderr)
        return 2
    try:
        guard_output(args.output, args.input_tiers)
        manifest = json.loads(args.input_tiers.read_text(encoding="utf-8"))
        _, rows = me.read_tsv(args.proposal)
        updated, report = merge(manifest, rows, args.include_deferred)
    except (ApplyError, OSError, ValueError, json.JSONDecodeError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1

    rendered = render_manifest(updated)
    if args.check:
        if not args.output.is_file():
            print(f"ERROR: missing {args.output}", file=sys.stderr)
            return 1
        if args.output.read_text(encoding="utf-8") != rendered:
            print(f"ERROR: {args.output} is not the deterministic merge result", file=sys.stderr)
            return 1
        print(f"Merge result verified: {args.output}")
        return 0

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(rendered, encoding="utf-8")
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n",
                               encoding="utf-8")
    print(
        f"Wrote {args.output}: {report['added_count']} tier rule(s) added, "
        f"{report['skipped_deferred_count']} deferred row(s) skipped, "
        f"{report['total_entries']} exact entries total."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
