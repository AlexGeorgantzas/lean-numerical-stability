#!/usr/bin/env python3
"""Generate the reviewed 386-module classification proposal and evidence."""

from __future__ import annotations

import argparse
import collections
import json
import re
from pathlib import Path

from lane_common import (
    BASE_SHA,
    CLASSIFICATION_ROOT,
    EVIDENCE_HEAD,
    SOURCE_NAME_RE,
    git,
    git_show_bytes,
    module_from_path,
    read_format2_zip,
    read_tsv,
    safe_cell,
    sha256_bytes,
    sha256_file,
    source_analysis_from_bytes,
    source_declarations,
    stable_json,
    write_tsv,
)


FIELDS = [
    "module",
    "path",
    "proposed_tier",
    "confidence",
    "source_markers",
    "reusable_markers",
    "public_declaration_count",
    "direct_project_imports",
    "required_action",
    "proposed_canonical_family",
    "cross_lane_dependency",
    "rationale",
]


# These are the deliberately reviewed mixed files. Each combines a substantial
# source-neutral API/proof family with numbered, printed, or source-correction
# declarations in the same physical owner. The set is intentionally explicit:
# mixedness is never inferred from a filename alone.
MIXED = {
    "NumStability.Algorithms.Ch14AsymptoticFamilies",
    "NumStability.Algorithms.Ch14ProductErrorNotation",
    "NumStability.Algorithms.HighamChapter10",
    "NumStability.Algorithms.HighamChapter15BoydBridges",
    "NumStability.Algorithms.HighamChapter15BoydConcreteLemma3",
    "NumStability.Algorithms.HighamChapter15BoydLocalStability",
    "NumStability.Algorithms.HighamChapter15BoydRowwiseDomain",
    "NumStability.Algorithms.HighamChapter15BoydScalar",
    "NumStability.Algorithms.HighamChapter15BoydSourceDomain",
    "NumStability.Algorithms.HighamChapter15BoydSourceLocal",
    "NumStability.Algorithms.HighamChapter15BoydSourceSecondDerivative",
    "NumStability.Algorithms.HighamChapter15BoydUniqueness",
    "NumStability.Algorithms.HighamChapter15ConvergenceProse",
    "NumStability.Algorithms.HighamChapter15RectTermination",
    "NumStability.Algorithms.HighamChapter5ComplexAlgorithm51",
    "NumStability.Algorithms.HighamChapter9Theorem99Closure",
    "NumStability.Algorithms.HighamChapter9Theorem99ComplexClosure",
    "NumStability.Algorithms.Horner",
    "NumStability.Algorithms.MatrixInversion",
    "NumStability.Algorithms.PNormPowerMethod",
    "NumStability.Algorithms.PNormPowerMethodGeneralP",
    "NumStability.Algorithms.PNormPowerMethodRect",
    "NumStability.Algorithms.StationaryIteration",
    "NumStability.Algorithms.TriangularArbitraryOrder",
    "NumStability.Algorithms.TriangularNoGuard",
    "NumStability.Analysis.CancellationOfRoundingErrors",
    "NumStability.Analysis.FloatingPointArithmetic",
    "NumStability.Analysis.HighamChapter7",
    "NumStability.Analysis.IncreasingPrecision",
    "NumStability.Analysis.InstabilityWithoutCancellation",
    "NumStability.Algorithms.TestMatrices.Higham28",
    "NumStability.Algorithms.TestMatrices.Higham28Contracts",
    "NumStability.Algorithms.TestMatrices.Higham28GinibreProjectiveIntegral",
    "NumStability.Algorithms.Cholesky.AasenAdjacentPivotOperationalMiddleCh11",
    "NumStability.Algorithms.Cholesky.AasenAdjacentPivotTridiagExecutorCh11Closure",
    "NumStability.Algorithms.Cholesky.AasenDirect118Ch11Closure",
    "NumStability.Algorithms.Cholesky.AasenOriginalCoordinateCorrectionCh11",
    "NumStability.Algorithms.Cholesky.AasenUnitOuterSolveCh11Closure",
    "NumStability.Algorithms.Cholesky.BlockLDLTBunchTridiagonalCh11Closure",
    "NumStability.Algorithms.Cholesky.BlockLDLTMixedPivotCh11Closure",
    "NumStability.Algorithms.Cholesky.BlockLDLTSolveBackwardCh11Closure",
    "NumStability.Algorithms.Cholesky.BunchTridiagonalActualSolveCh11Closure",
    "NumStability.Algorithms.Cholesky.BunchTridiagonalHFactorCh11Closure",
    "NumStability.Algorithms.Cholesky.TwoByTwoSchurStepCh11Closure",
}


CH11_REUSABLE = {
    "AasenCoupledFpCh11Closure",
    "AasenFactorResidualCh11Closure",
    "BunchTridiagonalFactorBoundCh11Closure",
    "BunchTridiagonalGrowthCh11Closure",
    "BunchTridiagonalGrowthInvariantCh11Closure",
    "BunchTridiagonalSparseFactorCh11Closure",
    "BunchTridiagonalSparseSolveCh11Closure",
}


HIGHAM28_REUSABLE = {
    "Higham28Cauchy",
    "Higham28Companion",
    "Higham28CompanionSpectral",
    "Higham28Exact",
    "Higham28GaussianDirection",
    "Higham28GaussianOrthogonal",
    "Higham28GinibreDimensionTwo",
    "Higham28HilbertAsymptotic",
    "Higham28OrthogonalCoordinates",
    "Higham28OrthogonalFibers",
    "Higham28OrthogonalHaar",
    "Higham28OrthogonalSphere",
    "Higham28PascalDualFlag",
    "Higham28PascalOscillationCore",
    "Higham28PascalOscillationExact",
    "Higham28PascalTotalPositivity",
    "Higham28ShiftedHilbert",
    "Higham28StewartHaar",
    "Higham28StewartRawFiber",
    "Higham28StewartRecursion",
    "Higham28ToeplitzSpectrum",
}


ANALYSIS_SOURCE = {
    "Accumulation",
    "AccuracyTests",
    "CalculatorWords",
    "Counting",
    "MullerRecurrence",
    "NearInteger",
}


TOP_SOURCE_EXACT = {
    "KahanAbsolute",
    "OrderingExamples",
    "WilkinsonAttainability",
    "HighamChapters1To9SourceClosure",
    "HighamLemma88Entrywise",
    "Chapter15CondEst",
}


def reviewed_tier(module: str, analysis: dict[str, object]) -> str:
    if module == "NumStability.Algorithms.RandNLA":
        return "aggregate"
    if module in MIXED:
        return "mixed_pending_split"

    leaf = module.rsplit(".", 1)[-1]
    if module.startswith("NumStability.Analysis.Problem2_"):
        return "source"
    if module.startswith("NumStability.Analysis.Higham"):
        return "source"
    if module.startswith("NumStability.Analysis.") and leaf in ANALYSIS_SOURCE:
        return "source"

    if module.startswith("NumStability.Algorithms.TestMatrices."):
        if leaf in HIGHAM28_REUSABLE:
            return "reusable"
        return "source"

    if module.startswith("NumStability.Algorithms.Cholesky."):
        if leaf.startswith("Cholesky"):
            return "reusable"
        if leaf in CH11_REUSABLE:
            return "reusable"
        if "Higham10" in leaf or "Higham11" in leaf or "HighamMathias" in leaf:
            return "source"
        if "Ch11" in leaf:
            return "source"
        return "reusable"

    if module.startswith("NumStability.Algorithms.RandNLA."):
        return "reusable"
    if module.startswith("NumStability.Algorithms.LU.Higham15"):
        return "source"
    if module.startswith("NumStability.Algorithms.LU.TridiagonalCondCh15"):
        return "source"
    if module.startswith("NumStability.Algorithms.Ch10"):
        return "source"
    if module.startswith("NumStability.Algorithms.Ch14"):
        return "source"
    if module.startswith("NumStability.Algorithms.Ch5"):
        return "source"
    if module.startswith("NumStability.Algorithms.Higham"):
        return "source"
    if module.startswith("NumStability.Algorithms.Ch15Dixon"):
        return "source"
    if leaf in TOP_SOURCE_EXACT:
        return "source"
    return "reusable"


def canonical_family(module: str, tier: str) -> str:
    leaf = module.rsplit(".", 1)[-1]
    if tier == "aggregate":
        return module
    if tier == "mixed_pending_split":
        if "Cholesky" in module or "Ch11" in module or "HighamChapter11" in module:
            return "NumStability.Algorithms.LinearSystems.SymmetricIndefinite + NumStability.Source.Higham.Chapter11"
        if "Chapter15" in module or "PNormPower" in module:
            return "NumStability.Algorithms.NormEstimation + NumStability.Source.Higham.Chapter15"
        if "Higham28" in module:
            return "NumStability.Analysis.TestMatrices + NumStability.Source.Higham.Chapter28"
        if "HighamChapter7" in module:
            return "NumStability.Analysis.Conditioning + NumStability.Source.Higham.Chapter07"
        if "HighamChapter10" in module:
            return "NumStability.Algorithms.LinearSystems.Cholesky + NumStability.Source.Higham.Chapter10"
        if "HighamChapter5" in module or leaf == "Horner":
            return "NumStability.Algorithms.PolynomialEvaluation + NumStability.Source.Higham.Chapter05"
        if "StationaryIteration" in module:
            return "NumStability.Algorithms.LinearSystems.Iterative + NumStability.Source.Higham.Chapter17"
        if "Triangular" in module:
            return "NumStability.Algorithms.LinearSystems.Triangular + NumStability.Source.Higham.Chapter08"
        if "Ch14" in module or leaf == "MatrixInversion":
            return "NumStability.Algorithms.MatrixInversion + NumStability.Source.Higham.Chapter14"
        if module.startswith("NumStability.Analysis."):
            return "NumStability.Analysis + NumStability.Source.Higham"
        return "NumStability.Algorithms + NumStability.Source.Higham"
    if tier == "source":
        patterns = [
            (r"(?:Ch|Chapter|HighamChapter|Higham)(\d{1,2})", leaf),
            (r"Problem(\d+)_", leaf),
            (r"Higham(\d{2})", leaf),
        ]
        chapter = None
        for pattern, value in patterns:
            match = re.search(pattern, value)
            if match:
                digits = match.group(1)
                chapter = digits[:2] if len(digits) > 2 else digits
                break
        if leaf in ANALYSIS_SOURCE and chapter is None:
            chapter = "01"
        if chapter is None and "Cholesky" in module:
            chapter = "11"
        if chapter is None:
            chapter = "Review"
        return f"NumStability.Source.Higham.Chapter{int(chapter):02d}" if chapter.isdigit() else "NumStability.Source.Higham.Review"
    if module.startswith("NumStability.Analysis."):
        return ".".join(module.split(".")[:3]) + "." + leaf
    if ".Cholesky." in module:
        return "NumStability.Algorithms.LinearSystems.Cholesky"
    if ".LU." in module:
        return "NumStability.Algorithms.LinearSystems.LU"
    if ".RandNLA." in module:
        return "NumStability.Algorithms.RandomizedLinearAlgebra"
    if ".TestMatrices." in module:
        return "NumStability.Analysis.TestMatrices"
    if leaf.startswith("PNormPower") or "CondEst" in leaf:
        return "NumStability.Algorithms.NormEstimation"
    return f"NumStability.Algorithms.{leaf}"


def cross_lane(module: str) -> str:
    if module in {
        "NumStability.Algorithms.Ch14Problem142",
        "NumStability.Algorithms.HighamChapter9",
        "NumStability.Algorithms.MatrixInversionMethod2BInstance",
    }:
        return f"BLOCKLU_REFRESH_REQUIRED;REFRESHED_AT_{EVIDENCE_HEAD}"
    if module in {
        "NumStability.Algorithms.MatrixInversion",
        "NumStability.Algorithms.RandNLA.LeastSquaresSketch",
    }:
        return f"LSQ_REFRESHED_AT_{EVIDENCE_HEAD}"
    if module == "NumStability.Algorithms.StationaryIteration":
        return f"POST_PACKET_DECLARATIONS_REFRESHED_AT_{EVIDENCE_HEAD}"
    return "NONE"


def current_public_count(module: str, path: str, frozen_public: int) -> tuple[int, list[str], list[str]]:
    base_text = git_show_bytes(BASE_SHA, path).decode("utf-8-sig")
    current_text = git_show_bytes(EVIDENCE_HEAD, path).decode("utf-8-sig")
    base = {name: visibility for name, _, visibility in source_declarations(base_text)}
    current = {name: visibility for name, _, visibility in source_declarations(current_text)}
    added = sorted(name for name in current.keys() - base.keys() if current[name] == "public")
    removed = sorted(name for name in base.keys() - current.keys() if base[name] == "public")
    return frozen_public + len(added) - len(removed), added, removed


def generate(packet_root: Path) -> None:
    if git("rev-parse", "HEAD").strip() != EVIDENCE_HEAD:
        raise SystemExit(f"classification generator requires evidence HEAD {EVIDENCE_HEAD}")
    if git("branch", "--show-current").strip() != "codex/org-classification-prep":
        raise SystemExit("classification generator requires codex/org-classification-prep")

    CLASSIFICATION_ROOT.mkdir(parents=True, exist_ok=True)
    packet_input = packet_root / "READ_ONLY_MODULES.tsv"
    packet_exclusions = packet_root / "CLASSIFICATION_EXCLUSIONS.tsv"
    input_path = CLASSIFICATION_ROOT / "input-modules.tsv"
    exclusions_path = CLASSIFICATION_ROOT / "exclusions.tsv"
    input_path.write_bytes(packet_input.read_bytes())
    exclusions_path.write_bytes(packet_exclusions.read_bytes())

    inventory = read_tsv(input_path)
    if len(inventory) != 386:
        raise ValueError("expected the frozen 386-module queue")
    declarations, _, baseline_hash, baseline_bytes = read_format2_zip(
        packet_root / "baseline/parallel-base-declarations-v2.zip"
    )
    frozen_public = collections.Counter(
        declaration.module
        for declaration in declarations.values()
        if declaration.visibility == "public"
    )

    rows: list[dict[str, object]] = []
    drift: list[dict[str, object]] = []
    for item in inventory:
        module, path = item["module"], item["path"]
        if module_from_path(path) != module:
            raise ValueError(f"module/path mismatch: {module} / {path}")
        analysis = source_analysis_from_bytes(git_show_bytes(EVIDENCE_HEAD, path))
        tier = reviewed_tier(module, analysis)
        family = canonical_family(module, tier)
        public_count, added, removed = current_public_count(
            module, path, frozen_public[module]
        )
        if added or removed:
            drift.append({"module": module, "added_public": added, "removed_public": removed})

        source_names = list(analysis["source_names"])
        generic_names = list(analysis["generic_names"])
        imports = list(analysis["imports"])
        source_markers = safe_cell(
            f"title={analysis['title']} | higham_tokens={analysis['higham_tokens']} | "
            f"numbered_tokens={analysis['numbered_tokens']} | "
            f"source_named_declarations={len(source_names)} | "
            f"examples={','.join(source_names[:3]) or 'none'}"
        )
        reusable_markers = safe_cell(
            f"generic_named_declarations={len(generic_names)} | "
            f"examples={','.join(generic_names[:3]) or 'none'} | "
            f"direct_project_imports={len(imports)} | lines={analysis['line_count']}"
        )
        if tier == "mixed_pending_split":
            action = (
                f"Split source-neutral declarations into {family.split(' + ')[0]} and "
                f"numbered/printed/source declarations into {family.split(' + ')[-1]}; "
                "preserve this historical path as an import-only compatibility wrapper."
            )
            rationale = (
                f"Reviewed body mixes {len(generic_names)} generic-named commands with "
                f"{len(source_names)} source-marked commands; the module title is "
                f"'{analysis['title']}'. A semantic split is required before tier application."
            )
            confidence = "high" if generic_names and source_names else "medium"
        elif tier == "source":
            action = (
                f"Classify as source correspondence and migrate in dependency order below {family}; "
                "retain the historical import as a compatibility wrapper."
            )
            rationale = (
                f"Source review found numbered/book-specific ownership (title '{analysis['title']}', "
                f"{len(source_names)} source-marked declarations); generic helpers are scoped to "
                "the same source result rather than a supported reusable surface."
            )
            confidence = "high" if source_names or analysis["numbered_tokens"] else "medium"
        elif tier == "aggregate":
            action = "Classify as aggregate; keep declaration-free and curate the exact family imports."
            rationale = (
                f"The body is declaration-free and contains {len(imports)} direct project imports; "
                "it is a discovery umbrella, not a declaration owner."
            )
            confidence = "high"
        else:
            action = (
                f"Classify as reusable API under {family}; any later physical move must preserve "
                "this historical import through a compatibility wrapper."
            )
            rationale = (
                f"Source review found a source-neutral mathematical/algorithmic surface (title "
                f"'{analysis['title']}', {len(generic_names)} generic-named declarations); citations "
                "or historical filenames do not make the declarations source correspondence."
            )
            confidence = "high" if generic_names else "medium"

        rows.append(
            {
                "module": module,
                "path": path,
                "proposed_tier": tier,
                "confidence": confidence,
                "source_markers": source_markers,
                "reusable_markers": reusable_markers,
                "public_declaration_count": public_count,
                "direct_project_imports": ";".join(imports) or "NONE",
                "required_action": safe_cell(action),
                "proposed_canonical_family": family,
                "cross_lane_dependency": cross_lane(module),
                "rationale": safe_cell(rationale),
            }
        )

    rows.sort(key=lambda row: str(row["module"]))
    modules_path = CLASSIFICATION_ROOT / "modules.tsv"
    write_tsv(modules_path, FIELDS, rows)

    changed_paths = set(
        git("diff", "--name-only", f"{BASE_SHA}..{EVIDENCE_HEAD}").splitlines()
    )
    changed_inventory = []
    for item in inventory:
        if item["path"] not in changed_paths:
            continue
        base_blob = git("rev-parse", f"{BASE_SHA}:{item['path']}").strip()
        head_blob = git("rev-parse", f"{EVIDENCE_HEAD}:{item['path']}").strip()
        base_imports = list(source_analysis_from_bytes(git_show_bytes(BASE_SHA, item["path"]))["imports"])
        head_imports = list(
            source_analysis_from_bytes(git_show_bytes(EVIDENCE_HEAD, item["path"]))["imports"]
        )
        changed_inventory.append(
            {
                "module": item["module"],
                "path": item["path"],
                "base_blob": base_blob,
                "head_blob": head_blob,
                "base_project_imports": base_imports,
                "head_project_imports": head_imports,
            }
        )

    counts = collections.Counter(str(row["proposed_tier"]) for row in rows)
    categories = [
        "reusable",
        "source",
        "compatibility",
        "aggregate",
        "mixed_pending_split",
        "internal",
    ]
    confidence = collections.Counter(str(row["confidence"]) for row in rows)
    summary = {
        "schema_version": 1,
        "frozen_inventory_base": BASE_SHA,
        "review_evidence_head": EVIDENCE_HEAD,
        "input_modules": len(inventory),
        "proposal_rows": len(rows),
        "missing_modules": [],
        "extra_modules": [],
        "tier_counts": {category: counts[category] for category in categories},
        "confidence_counts": dict(sorted(confidence.items())),
        "split_queue": [row["module"] for row in rows if row["proposed_tier"] == "mixed_pending_split"],
        "cross_lane_refresh_rows": [row["module"] for row in rows if row["cross_lane_dependency"] != "NONE"],
        "current_declaration_drift": drift,
        "changed_inventory_blobs_since_packet_base": changed_inventory,
        "hashes": {
            "input_modules_sha256": sha256_file(input_path),
            "packet_input_modules_sha256": sha256_file(packet_input),
            "exclusions_sha256": sha256_file(exclusions_path),
            "packet_exclusions_sha256": sha256_file(packet_exclusions),
            "modules_sha256": sha256_file(modules_path),
            "format2_uncompressed_sha256": baseline_hash,
        },
        "format2_uncompressed_bytes": baseline_bytes,
        "public_declaration_count_basis": (
            "packet format-2 baseline adjusted by source-level public declaration additions/removals "
            f"through {EVIDENCE_HEAD}"
        ),
    }
    (CLASSIFICATION_ROOT / "summary.json").write_text(
        stable_json(summary), encoding="utf-8", newline="\n"
    )
    (CLASSIFICATION_ROOT / "README.md").write_text(
        render_readme(summary), encoding="utf-8", newline="\n"
    )


def render_readme(summary: dict[str, object]) -> str:
    counts = summary["tier_counts"]
    rows = "\n".join(f"| {key} | {value} |" for key, value in counts.items())
    changed = summary["changed_inventory_blobs_since_packet_base"]
    changed_lines = "\n".join(
        f"- `{item['module']}`: `{item['base_blob']}` -> `{item['head_blob']}`"
        for item in changed
    )
    return f"""# Frozen classification proposal

This proposal reviews every row of the packet's immutable 386-module queue. It
does not modify production Lean sources or the shared tier manifest. Decisions
use module documentation, declaration roles, direct imports, and source/body
markers; filenames are evidence only when confirmed by the source body.

The queue and the 217-row exclusion inventory are tracked byte-for-byte so the
original 603-module partition remains reproducible after the external packet is
removed. The frozen partition is at `{BASE_SHA}`; source/import refresh evidence
is taken from published main `{EVIDENCE_HEAD}`.

| Proposed category | Modules |
| --- | ---: |
{rows}

`mixed_pending_split` is an implementation queue, not an exception. Every row
contains a concrete reusable/source split action. `modules.tsv` is sorted and
has exactly one row per tracked input module.

## Post-packet refresh

Six inventory blobs changed between the packet base and the reviewed main:

{changed_lines}

The three BlockLU consumers were re-read after the Phase 12 integration. The
least-squares consumers were re-read after their canonical import cutover.
`StationaryIteration` gained two public Chapter 17 declarations, which are
included in its current declaration count and mixed-file action.

## Applying the proposal

`apply_tier_proposal.py` writes only to an explicit output distinct from its
input and refuses the shared `docs/architecture/tiers.json` path. The proposal
must be reviewed and all mixed rows split before an integrator applies it.
"""


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--packet-root", type=Path, required=True)
    return parser.parse_args()


if __name__ == "__main__":
    args = parse_args()
    generate(args.packet_root.resolve())
