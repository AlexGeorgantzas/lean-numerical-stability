#!/usr/bin/env python3
"""Generate the exact-C0004 planned controls for the R04/R08 successor pair.

This is a deterministic control-plane generator.  It never creates Git refs,
worktrees, or worker implementation files.  Every baseline-dependent artifact
is derived from accepted C0004 code and its pinned format-2 graph.  The R08 raw
freeze bundle is hash-verified before it is normalized into branch evidence.
"""

from __future__ import annotations

import csv
import difflib
import gzip
import hashlib
import io
import itertools
import json
import os
import re
import subprocess
import tempfile
from collections import Counter, defaultdict, deque
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Iterator, Sequence


ROOT = Path(__file__).resolve().parents[2]
PHASE = ROOT / "docs/architecture/phases/2026-08-repository-reorganization-completion"
BRANCHES = PHASE / "branches"
PROJECTIONS = PHASE / "projections"
REQUESTS = PHASE / "requests"
REVIEWS = PHASE / "reviews"
SELECTORS = PHASE / "selectors"
BASE_SHA = "783ae9a4951407ece046adb8631d5a8ff1795a18"
BASE_TREE = "122bf65c2e13840ca8251ec0eb7ed7e9cf3e653d"
CONTROL_HEAD = "59115771c816e0f41967c854beb9e86532317e82"
PHASE_ID = "repository-reorganization-completion-2026-08"
BASE_CHECKPOINT = "C0004"
GRAPH = ROOT / "benchmark-results/C0004-combined.tsv"
GRAPH_SHA256 = "98C9C0CA7266A7CF295A27D5D119903F0EF239349F3FBC6C57F29BE9FBF602AB"
INVENTORY = PHASE / "checkpoints/C0004-inventory.tsv"
INVENTORY_SHA256 = "08FA3E41DA0C72E7F5D4ECFD315F0CC6C73EB0F45089CF1DAC6AB04A81A1E326"
BASELINE = PHASE / "baselines/C0004-combined.json"
BASELINE_SHA256 = "D3F30A410903B1CA2858951CB26107B94B62630BC424723A0EC9EDF484AEDDDF"
BASELINE_SUMMARY = PHASE / "baselines/C0004-combined.md"
BASELINE_SUMMARY_SHA256 = "E6D14B92A4D310BB64EF4DBE9F378BB8E0EA5A58B5BBC058AAA43181300F3BB1"
PROJECTION_CHECKER = ROOT / "tools/architecture/check_completion_phase_projection.py"
PROJECTION_CHECKER_SHA256 = "0F32935ED1EFDD2BD4D6A4C346F3E8300C86DB1D4A3551A17165479226109220"
R08_FREEZE = Path(os.environ.get("NUMSTABILITY_R08_FREEZE", r"C:\Users\qed_s\r08-freeze"))
R04_FREEZE = Path(os.environ.get("NUMSTABILITY_R04_FREEZE", r"C:\Users\qed_s\r04-freeze"))

PROTECTED_PREFIXES = (
    "NumStabilityTest/Import/",
    "NumStabilityTest/Worker/",
    "benchmark-results/",
    "docs/architecture/phases/",
    "tools/architecture/",
)

R08_RAW_HASHES = {
    "R08-declaration-routes.tsv": "A00C5BBF97383BA45F752BB4085CB8A8F780B4C211DF95F5CDEA55A77957AD68",
    "R08-destination-modules.txt": "58F71B0EEE5D7766652263CE98AEF0CADF6C2473652A7A498D844AF44466C267",
    "R08-destination-prefixes.txt": "26B02C9B970CD353A33FA9A1DF0268C796E6CF83B36B9C7A62CA7BB871F2C1FE",
    "R08-branch-prefixes.txt": "DA4A204D65FDD85479357E23844D076DF8AC635C192D719BC80921EA70B1D2D5",
    "R08-private-normalization.tsv": "335C3FE17716B3391962CC68EFAD81673E1BAE0E4B4C2F0720C0906703786FC0",
    "R08-destination-dag.tsv": "F0CF51AE800681524F7093ADE99350CB906386376FB8A295A92D0CFE0606F837",
    "R08-post-move-import-manifest.tsv": "86CD1D9603A46D8789C164C99C5D032011C43919D899ECFC80B4E04E13F8D9AE",
    "R08-Algorithms-deletions.txt": "86AF2852FF40BE503B9A98B4B3D09C18ED37F5CDF46F1AE90DDE42A81FB82FA0",
    "Algorithms.postimage.lean": "0DEF3FD36DD507444AC0A317170966B62724BD3155B5DDBC652D33132B58CC3A",
    "R08-Algorithms.patch": "0FCB50855CDCB35F5C769914C50F4862590FCA79D5D9AB48A17986E5D5FC2117",
    "R08-R0010-shared-paths.txt": "27909095ED5B03AF1CDA0AB9CD7757A3D53A772F553B4C115611FA8ADD650384",
    "R08-outside-consumers.txt": "D92A107A41D86E50350E70E9E5746C4B046353F8C3B4A276934E5096CB627F7A",
    "R08-test-modules.txt": "915E0B206130085D69EC82605775383E1041342EC6E306893090235D598A5316",
}

R04_WHOLE_DESTINATIONS = {
    "NumStability.Algorithms.Ch10ActualSourceClosure": "NumStability.Source.Higham.Chapter10.Theorem06.RoundedCholesky.ForwardError.ActualAlgorithm",
    "NumStability.Algorithms.Ch10ComplexPositiveDefiniteSourceClosure": "NumStability.Source.Higham.Chapter10.Equation30.ComplexPositiveDefinite.NoPivotLU.SourceBounds",
    "NumStability.Algorithms.Ch10KahanSharpnessSource": "NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.OperatorNorm.SourceBound",
    "NumStability.Algorithms.Ch10PivotedPSDSourceClosure": "NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.ActualComputation.ErrorBounds",
    "NumStability.Algorithms.Ch10Theorem108Componentwise": "NumStability.Source.Higham.Chapter10.Theorem08.ComponentwisePerturbation.NormalizedResolvent.SourceBound",
    "NumStability.Algorithms.Ch10Theorem108Source": "NumStability.Source.Higham.Chapter10.Theorem08.NormwiseDiscrepancy.Counterexample.Uniqueness",
    "NumStability.Algorithms.Cholesky.Higham1014Equation1022": "NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.SchurPerturbation.Family",
    "NumStability.Algorithms.Cholesky.Higham1014SourceError": "NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.RankSensitiveError.Bounds",
    "NumStability.Algorithms.Cholesky.Higham1029Source": "NumStability.Source.Higham.Chapter10.Section04.PositiveDefiniteSymmetricPart.LUGrowth.Equation29",
    "NumStability.Algorithms.Cholesky.HighamMathiasSource": "NumStability.Source.Higham.Chapter10.Equation29.Mathias.RoundedSchur.Bounds",
}

R04_AGGREGATE_DESTINATIONS = {
    "NumStability.Source.Higham.Chapter06.Lemma06": "NumStability.Source.Higham.Chapter06.Lemma06.Core.Results",
    "NumStability.Source.Higham.Chapter10.Theorem07": "NumStability.Source.Higham.Chapter10.Theorem07.Core.Results",
    "NumStability.Source.Higham.Chapter11.Theorem07": "NumStability.Source.Higham.Chapter11.Theorem07.Core.Results",
}

R04_RETAINED = {
    "NumStability.Algorithms.Cholesky.CholeskyDemmel",
    "NumStability.Algorithms.Cholesky.CholeskyFl",
    "NumStability.Algorithms.Cholesky.CholeskyNonsym",
    "NumStability.Algorithms.Cholesky.CholeskySpec",
}

R04_SPLIT_DESTINATIONS: dict[str, dict[str, str]] = {
    "NumStability.Algorithms.Cholesky.CholeskyPSD": {
        "spd_pivoted_cholesky": "NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.PivotedFactorization.Existence",
        "quadForm_two_point": "NumStability.Source.Higham.Chapter10.Problem01.PositiveSemidefiniteEntries.EntryBounds.Results",
        "psd_all_diag_zero": "NumStability.Source.Higham.Chapter10.Problem01.PositiveSemidefiniteEntries.EntryBounds.Results",
        "psd_abs_entry_le_sqrt_diag": "NumStability.Source.Higham.Chapter10.Problem01.PositiveSemidefiniteEntries.EntryBounds.Results",
        "psd_abs_entry_le_maxdiag": "NumStability.Source.Higham.Chapter10.Problem01.PositiveSemidefiniteEntries.EntryBounds.Results",
        "psd_diag_nonneg": "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.ConstructiveFactorization.Existence",
        "psd_zero_diag_row_zero": "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.ConstructiveFactorization.Existence",
        "sum_filter_succ_tail": "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.ConstructiveFactorization.Existence",
        "psd_cholesky_existence": "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.ConstructiveFactorization.Existence",
        "psd_pivoted_cholesky_exists": "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.ConstructiveFactorization.Existence",
        "psd_pivoted_cholesky_exists_cp": "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.ConstructiveFactorization.Existence",
        "psd_pivoted_cholesky_exists_tail": "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.ConstructiveFactorization.Existence",
        "psd_quadForm_le_trace": "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.QuadraticFormBounds.WeightedNorm",
        "psd_quadForm_le_card_maxdiag": "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.QuadraticFormBounds.WeightedNorm",
        "fl_cp_termination_trailing_bound": "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.TrailingTermination.Bound",
        "fl_factor_row_dominated": "NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.RoundedErrorAnalysis.Bounds",
        "fl_cpFactor_rows_dominated": "NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.RoundedErrorAnalysis.Bounds",
        "higham10_14_as_run_backward_error": "NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.RoundedErrorAnalysis.Bounds",
    },
    "NumStability.Algorithms.HighamChapter10": {
        "finiteMaxEigenvalue_leading_principal_le": "NumStability.Analysis.MatrixNorms.SpectralExtrema.PrincipalSubmatrices.Bounds",
        "finiteMinEigenvalue_leading_principal_ge": "NumStability.Analysis.MatrixNorms.SpectralExtrema.PrincipalSubmatrices.Bounds",
        "min_eig_scaled_bordered_floor": "NumStability.Analysis.MatrixNorms.SpectralExtrema.PrincipalSubmatrices.Bounds",
        "stage_interior_mass_from_full": "NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.StageEmbedding.InteriorMass",
        "fl_cholesky_pivots_pos_sharp_certified": "NumStability.Algorithms.LinearSystems.Cholesky.ErrorAnalysis.PositivePivots.Certificate",
        "kahan_telescope": "NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.KahanTelescope.Identity",
        "kahanR_tail_eq": "NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.KahanTelescope.Identity",
        "higham10_1_cholesky_existence": "NumStability.Source.Higham.Chapter10.Section01.Factorization.ExistenceUniqueness.Results",
        "higham10_1_cholesky_uniqueness": "NumStability.Source.Higham.Chapter10.Section01.Factorization.ExistenceUniqueness.Results",
        "higham10_problem_10_4_first_ge_entry_abs_le_initial_max": "NumStability.Source.Higham.Chapter10.Problem04.UnpivotedGrowth.PositivePivots.Bounds",
        "higham10_problem_10_4_first_ge_maxEntryNorm_le": "NumStability.Source.Higham.Chapter10.Problem04.UnpivotedGrowth.PositivePivots.Bounds",
        "higham10_problem_10_4_first_ge_reduced_submatrix_spd": "NumStability.Source.Higham.Chapter10.Problem04.UnpivotedGrowth.PositivePivots.Bounds",
        "higham10_problem_10_4_unpivoted_ge_positive_pivots_and_growth": "NumStability.Source.Higham.Chapter10.Problem04.UnpivotedGrowth.PositivePivots.Bounds",
        "higham10_3_fl_cholesky_certificate": "NumStability.Source.Higham.Chapter10.Section02.ErrorAnalysis.FactorizationAndSolve.Bounds",
        "higham10_3_fl_cholesky_backward_error": "NumStability.Source.Higham.Chapter10.Section02.ErrorAnalysis.FactorizationAndSolve.Bounds",
        "higham10_4_fl_cholesky_solve_backward_error": "NumStability.Source.Higham.Chapter10.Section02.ErrorAnalysis.FactorizationAndSolve.Bounds",
        "higham10_5_fl_cholesky_demmel_bound": "NumStability.Source.Higham.Chapter10.Section02.ErrorAnalysis.FactorizationAndSolve.Bounds",
        "higham10_7_fl_cholesky_success": "NumStability.Source.Higham.Chapter10.Theorem07.SuccessThreshold.Factorization",
        "higham10_7_fl_cholesky_success_sharp": "NumStability.Source.Higham.Chapter10.Theorem07.SuccessThreshold.Factorization",
        "higham10_7_success_factorization": "NumStability.Source.Higham.Chapter10.Theorem07.SuccessThreshold.Factorization",
        "higham10_7_success_factorization_spectral": "NumStability.Source.Higham.Chapter10.Theorem07.SuccessThreshold.Factorization",
        "higham10_7_success_factorization_min_eig": "NumStability.Source.Higham.Chapter10.Theorem07.SuccessThreshold.Factorization",
        "higham10_9_upper_product_sum_split": "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.PivotingAndScaling.Results",
        "higham10_9_psd_cholesky_existence": "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.PivotingAndScaling.Results",
        "higham10_9_spd_pivoted_cholesky_full_rank": "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.PivotingAndScaling.Results",
        "higham10_9_psd_pivoted_cholesky_rank": "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.PivotingAndScaling.Results",
        "higham10_9_pivoted_cholesky_unique": "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.PivotingAndScaling.Results",
        "higham10_9_psd_pivoted_cholesky_rank_unique": "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.PivotingAndScaling.Results",
        "higham10_12_w_action_trace_bound": "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.PivotingAndScaling.Results",
        "unit_diag_psd_maxEigenvalue_bounds": "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.PivotingAndScaling.Results",
        "higham10_9_unit_diag_cond_bound": "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.PivotingAndScaling.Results",
        "higham10_9_scaled_cond_bound": "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.PivotingAndScaling.Results",
        "higham10_9_van_der_sluis": "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.PivotingAndScaling.Results",
        "higham10_18_row_cast": "NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.UnboundedGrowth.Construction",
        "higham10_18_row_nat": "NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.UnboundedGrowth.Construction",
        "higham10_18_isPosSemiDef": "NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.UnboundedGrowth.Construction",
        "higham10_18_w_arbitrarily_large": "NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.UnboundedGrowth.Construction",
        "higham10_21_stage_interior_mass": "NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.SuccessfulRun.StageBounds",
        "higham10_21_stage_border_mass": "NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.SuccessfulRun.StageBounds",
        "higham10_21_fl_cholesky_leading_pivots_pos": "NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.SuccessfulRun.StageBounds",
        "higham10_21_fl_cholesky_success": "NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.SuccessfulRun.StageBounds",
        "higham10_14_fl_psd_cholesky_backward_error": "NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.RoundedErrorAnalysis.Bounds",
        "higham10_4_nonsym_pd_leading_principal": "NumStability.Source.Higham.Chapter10.Section04.PositiveDefiniteSymmetricPart.SchurStages.Bounds",
        "higham10_29_stage_quadForm_le": "NumStability.Source.Higham.Chapter10.Section04.PositiveDefiniteSymmetricPart.SchurStages.Bounds",
        "higham10_29_stage_operator_le": "NumStability.Source.Higham.Chapter10.Section04.PositiveDefiniteSymmetricPart.SchurStages.Bounds",
        "higham10_29_stage_operator_le_exists": "NumStability.Source.Higham.Chapter10.Section04.PositiveDefiniteSymmetricPart.SchurStages.Bounds",
    },
}

R04_DESTINATION_TIERS = {
    "NumStability.Algorithms.LinearSystems.Cholesky.ErrorAnalysis.PositivePivots.Certificate": "reusable",
    "NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.KahanTelescope.Identity": "reusable",
    "NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.PivotedFactorization.Existence": "reusable",
    "NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.StageEmbedding.InteriorMass": "reusable",
    "NumStability.Analysis.MatrixNorms.SpectralExtrema.PrincipalSubmatrices.Bounds": "reusable",
    "NumStability.Source.Higham.Chapter06.Lemma06.Core.Results": "source",
    "NumStability.Source.Higham.Chapter10.Equation29.Mathias.RoundedSchur.Bounds": "source",
    "NumStability.Source.Higham.Chapter10.Equation30.ComplexPositiveDefinite.NoPivotLU.SourceBounds": "source",
    "NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.OperatorNorm.SourceBound": "source",
    "NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.UnboundedGrowth.Construction": "source",
    "NumStability.Source.Higham.Chapter10.Problem01.PositiveSemidefiniteEntries.EntryBounds.Results": "source",
    "NumStability.Source.Higham.Chapter10.Problem04.UnpivotedGrowth.PositivePivots.Bounds": "source",
    "NumStability.Source.Higham.Chapter10.Section01.Factorization.ExistenceUniqueness.Results": "source",
    "NumStability.Source.Higham.Chapter10.Section02.ErrorAnalysis.FactorizationAndSolve.Bounds": "source",
    "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.ConstructiveFactorization.Existence": "source",
    "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.PivotingAndScaling.Results": "source",
    "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.QuadraticFormBounds.WeightedNorm": "source",
    "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.TrailingTermination.Bound": "source",
    "NumStability.Source.Higham.Chapter10.Section04.PositiveDefiniteSymmetricPart.LUGrowth.Equation29": "source",
    "NumStability.Source.Higham.Chapter10.Section04.PositiveDefiniteSymmetricPart.SchurStages.Bounds": "source",
    "NumStability.Source.Higham.Chapter10.Theorem06.RoundedCholesky.ForwardError.ActualAlgorithm": "source",
    "NumStability.Source.Higham.Chapter10.Theorem07.Core.Results": "source",
    "NumStability.Source.Higham.Chapter10.Theorem07.SuccessThreshold.Factorization": "source",
    "NumStability.Source.Higham.Chapter10.Theorem08.ComponentwisePerturbation.NormalizedResolvent.SourceBound": "source",
    "NumStability.Source.Higham.Chapter10.Theorem08.NormwiseDiscrepancy.Counterexample.Uniqueness": "source",
    "NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.ActualComputation.ErrorBounds": "source",
    "NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.RankSensitiveError.Bounds": "source",
    "NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.RoundedErrorAnalysis.Bounds": "source",
    "NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.SchurPerturbation.Family": "source",
    "NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.SuccessfulRun.StageBounds": "source",
    "NumStability.Source.Higham.Chapter11.Theorem07.Core.Results": "source",
}

R04_BRANCH_PREFIXES = (
    "NumStability/Algorithms/LinearSystems/Cholesky/ErrorAnalysis/PositivePivots/",
    "NumStability/Algorithms/LinearSystems/Cholesky/PositiveSemidefinite/KahanTelescope/",
    "NumStability/Algorithms/LinearSystems/Cholesky/PositiveSemidefinite/PivotedFactorization/",
    "NumStability/Algorithms/LinearSystems/Cholesky/PositiveSemidefinite/StageEmbedding/",
    "NumStability/Analysis/MatrixNorms/SpectralExtrema/PrincipalSubmatrices/",
    "NumStability/Source/Higham/Chapter06/Lemma06/Core/",
    "NumStability/Source/Higham/Chapter10/Equation29/Mathias/RoundedSchur/",
    "NumStability/Source/Higham/Chapter10/Equation30/ComplexPositiveDefinite/NoPivotLU/",
    "NumStability/Source/Higham/Chapter10/Lemma13/KahanSharpness/OperatorNorm/",
    "NumStability/Source/Higham/Chapter10/Lemma13/KahanSharpness/UnboundedGrowth/",
    "NumStability/Source/Higham/Chapter10/Problem01/PositiveSemidefiniteEntries/EntryBounds/",
    "NumStability/Source/Higham/Chapter10/Problem04/UnpivotedGrowth/PositivePivots/",
    "NumStability/Source/Higham/Chapter10/Section01/Factorization/ExistenceUniqueness/",
    "NumStability/Source/Higham/Chapter10/Section02/ErrorAnalysis/FactorizationAndSolve/",
    "NumStability/Source/Higham/Chapter10/Section03/PositiveSemidefinite/ConstructiveFactorization/",
    "NumStability/Source/Higham/Chapter10/Section03/PositiveSemidefinite/PivotingAndScaling/",
    "NumStability/Source/Higham/Chapter10/Section03/PositiveSemidefinite/QuadraticFormBounds/",
    "NumStability/Source/Higham/Chapter10/Section03/PositiveSemidefinite/TrailingTermination/",
    "NumStability/Source/Higham/Chapter10/Section04/PositiveDefiniteSymmetricPart/LUGrowth/",
    "NumStability/Source/Higham/Chapter10/Section04/PositiveDefiniteSymmetricPart/SchurStages/",
    "NumStability/Source/Higham/Chapter10/Theorem06/RoundedCholesky/ForwardError/",
    "NumStability/Source/Higham/Chapter10/Theorem07/Core/",
    "NumStability/Source/Higham/Chapter10/Theorem07/SuccessThreshold/",
    "NumStability/Source/Higham/Chapter10/Theorem08/ComponentwisePerturbation/NormalizedResolvent/",
    "NumStability/Source/Higham/Chapter10/Theorem08/NormwiseDiscrepancy/Counterexample/",
    "NumStability/Source/Higham/Chapter10/Theorem14/CompletePivotedPSD/ActualComputation/",
    "NumStability/Source/Higham/Chapter10/Theorem14/CompletePivotedPSD/RankSensitiveError/",
    "NumStability/Source/Higham/Chapter10/Theorem14/CompletePivotedPSD/RoundedErrorAnalysis/",
    "NumStability/Source/Higham/Chapter10/Theorem14/CompletePivotedPSD/SchurPerturbation/",
    "NumStability/Source/Higham/Chapter10/Theorem14/CompletePivotedPSD/SuccessfulRun/",
    "NumStability/Source/Higham/Chapter11/Theorem07/Core/",
    "NumStabilityTest/Reorganization/R04/",
    "docs/architecture/deliveries/R04/",
)

R04_OUTSIDE_CONSUMERS = (
    "NumStability.Algorithms",
    "NumStability.Algorithms.Ch10Ch14Lemma66Op2Bridge",
    "NumStability.Algorithms.Ch10KahanSharpness",
    "NumStability.Algorithms.Ch10Lemma1011Source",
    "NumStability.Algorithms.Chapter06Lemma66",
    "NumStability.Algorithms.Cholesky.BunchTridiagonalCapstoneCh11Closure",
    "NumStability.Algorithms.Cholesky.CholeskyPerturbation",
    "NumStability.Algorithms.Cholesky.CholeskySolve",
    "NumStability.Algorithms.Cholesky.Higham1014SourceSuccess",
    "NumStability.Algorithms.Cholesky.Higham10Theorem10_7Source",
    "NumStability.Algorithms.Cholesky.HighamMathiasFirstBreakdown",
    "NumStability.Algorithms.LeastSquares.Higham20Remaining",
    "NumStability.Algorithms.LeastSquares.LSNormalEquations",
    "NumStability.Higham.Chapter10.Theorem10_7",
    "NumStability.Higham.Chapter11.Theorem11_7Capstone",
    "NumStability.Source.Higham.Chapter06",
    "NumStability.Source.Higham.Chapter06.Lemma06.OperatorTwoNormBound.Bridge",
    "NumStability.Source.Higham.Chapter10",
    "NumStability.Source.Higham.Chapter10.Equation07.AbsoluteFactorNorm.Bridge",
    "NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.Equation22",
    "NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.SourceError",
    "NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.SourceSuccess",
    "NumStability.Source.Higham.Chapter11",
    "NumStability.Source.Higham.Chapter13.Lemma09",
    "NumStability.Source.Higham.Chapter14.Section03.ResidualOperatorTwoNorm.Bridge",
    "NumStability.Source.Higham.Chapter19.Theorem05.SourceClosure",
    "NumStability.Source.Higham.Chapter20.NormalEquations",
    "NumStability.Source.Higham.Chapter20.Remaining",
)

R0009_PATHS = (
    "NumStability/Algorithms.lean",
    "NumStability/Algorithms/LinearSystems/Cholesky/ErrorAnalysis.lean",
    "NumStability/Algorithms/LinearSystems/Cholesky/PositiveSemidefinite.lean",
    "NumStability/Analysis/MatrixNorms/SpectralExtrema.lean",
    "NumStability/Source/Higham/Chapter06/Lemma06/OperatorTwoNormBound/Bridge.lean",
    "NumStability/Source/Higham/Chapter10/Equation07/AbsoluteFactorNorm/Bridge.lean",
    "NumStability/Source/Higham/Chapter10/Equation29/Mathias.lean",
    "NumStability/Source/Higham/Chapter10/Equation30/ComplexPositiveDefinite.lean",
    "NumStability/Source/Higham/Chapter10/Lemma13/KahanSharpness.lean",
    "NumStability/Source/Higham/Chapter10/Problem01/PositiveSemidefiniteEntries.lean",
    "NumStability/Source/Higham/Chapter10/Problem04/UnpivotedGrowth.lean",
    "NumStability/Source/Higham/Chapter10/Section01/Factorization.lean",
    "NumStability/Source/Higham/Chapter10/Section02/ErrorAnalysis.lean",
    "NumStability/Source/Higham/Chapter10/Section03/PositiveSemidefinite.lean",
    "NumStability/Source/Higham/Chapter10/Section04/PositiveDefiniteSymmetricPart.lean",
    "NumStability/Source/Higham/Chapter10/Theorem06/RoundedCholesky.lean",
    "NumStability/Source/Higham/Chapter10/Theorem08/ComponentwisePerturbation.lean",
    "NumStability/Source/Higham/Chapter10/Theorem08/NormwiseDiscrepancy.lean",
    "NumStability/Source/Higham/Chapter10/Theorem14/CompletePivotedPSD.lean",
    "NumStability/Source/Higham/Chapter10/Theorem14/CompletePivotedPSD/Equation22.lean",
    "NumStability/Source/Higham/Chapter10/Theorem14/CompletePivotedPSD/SourceError.lean",
    "NumStability/Source/Higham/Chapter10/Theorem14/CompletePivotedPSD/SourceSuccess.lean",
    "NumStability/Source/Higham/Chapter14/Section03/ResidualOperatorTwoNorm/Bridge.lean",
    "NumStability/Source/Higham/Chapter19/Theorem05/SourceClosure.lean",
    "NumStabilityTest.lean",
    "docs/architecture/COMPATIBILITY.md",
    "docs/architecture/layout-exceptions.json",
    "docs/architecture/tiers.json",
)

R0010_PATHS = (
    "NumStability/Algorithms.lean",
    "NumStability/Source/Higham/Chapter14/Algorithm04.lean",
    "NumStability/Source/Higham/Chapter14/Corollary06.lean",
    "NumStability/Source/Higham/Chapter14/Corollary07.lean",
    "NumStability/Source/Higham/Chapter14/Problem02.lean",
    "NumStability/Source/Higham/Chapter14/Problem12.lean",
    "NumStability/Source/Higham/Chapter14/Section01.lean",
    "NumStability/Source/Higham/Chapter14/Section02.lean",
    "NumStability/Source/Higham/Chapter14/Theorem05.lean",
    "NumStabilityTest.lean",
    "docs/architecture/COMPATIBILITY.md",
    "docs/architecture/MIGRATION.md",
    "docs/architecture/layout-exceptions.json",
    "docs/architecture/tiers.json",
)

REQUEST_INTERSECTION = (
    "NumStability/Algorithms.lean",
    "NumStabilityTest.lean",
    "docs/architecture/COMPATIBILITY.md",
    "docs/architecture/layout-exceptions.json",
    "docs/architecture/tiers.json",
)

R04_AGGREGATE_IMPORTS = {
    "NumStability/Algorithms/LinearSystems/Cholesky/ErrorAnalysis.lean": (
        "NumStability.Algorithms.LinearSystems.Cholesky.ErrorAnalysis.PositivePivots.Certificate",
    ),
    "NumStability/Algorithms/LinearSystems/Cholesky/PositiveSemidefinite.lean": (
        "NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.KahanTelescope.Identity",
        "NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.PivotedFactorization.Existence",
        "NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.StageEmbedding.InteriorMass",
    ),
    "NumStability/Analysis/MatrixNorms/SpectralExtrema.lean": (
        "NumStability.Analysis.MatrixNorms.SpectralExtrema.PrincipalSubmatrices.Bounds",
    ),
    "NumStability/Source/Higham/Chapter10/Equation29/Mathias.lean": (
        "NumStability.Source.Higham.Chapter10.Equation29.Mathias.RoundedSchur.Bounds",
    ),
    "NumStability/Source/Higham/Chapter10/Equation30/ComplexPositiveDefinite.lean": (
        "NumStability.Source.Higham.Chapter10.Equation30.ComplexPositiveDefinite.NoPivotLU.SourceBounds",
    ),
    "NumStability/Source/Higham/Chapter10/Lemma13/KahanSharpness.lean": (
        "NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.OperatorNorm.SourceBound",
        "NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.UnboundedGrowth.Construction",
    ),
    "NumStability/Source/Higham/Chapter10/Problem01/PositiveSemidefiniteEntries.lean": (
        "NumStability.Source.Higham.Chapter10.Problem01.PositiveSemidefiniteEntries.EntryBounds.Results",
    ),
    "NumStability/Source/Higham/Chapter10/Problem04/UnpivotedGrowth.lean": (
        "NumStability.Source.Higham.Chapter10.Problem04.UnpivotedGrowth.PositivePivots.Bounds",
    ),
    "NumStability/Source/Higham/Chapter10/Section01/Factorization.lean": (
        "NumStability.Source.Higham.Chapter10.Section01.Factorization.ExistenceUniqueness.Results",
    ),
    "NumStability/Source/Higham/Chapter10/Section02/ErrorAnalysis.lean": (
        "NumStability.Source.Higham.Chapter10.Section02.ErrorAnalysis.FactorizationAndSolve.Bounds",
    ),
    "NumStability/Source/Higham/Chapter10/Section03/PositiveSemidefinite.lean": (
        "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.ConstructiveFactorization.Existence",
        "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.PivotingAndScaling.Results",
        "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.QuadraticFormBounds.WeightedNorm",
        "NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.TrailingTermination.Bound",
    ),
    "NumStability/Source/Higham/Chapter10/Section04/PositiveDefiniteSymmetricPart.lean": (
        "NumStability.Source.Higham.Chapter10.Section04.PositiveDefiniteSymmetricPart.LUGrowth.Equation29",
        "NumStability.Source.Higham.Chapter10.Section04.PositiveDefiniteSymmetricPart.SchurStages.Bounds",
    ),
    "NumStability/Source/Higham/Chapter10/Theorem06/RoundedCholesky.lean": (
        "NumStability.Source.Higham.Chapter10.Theorem06.RoundedCholesky.ForwardError.ActualAlgorithm",
    ),
    "NumStability/Source/Higham/Chapter10/Theorem08/ComponentwisePerturbation.lean": (
        "NumStability.Source.Higham.Chapter10.Theorem08.ComponentwisePerturbation.NormalizedResolvent.SourceBound",
    ),
    "NumStability/Source/Higham/Chapter10/Theorem08/NormwiseDiscrepancy.lean": (
        "NumStability.Source.Higham.Chapter10.Theorem08.NormwiseDiscrepancy.Counterexample.Uniqueness",
    ),
    "NumStability/Source/Higham/Chapter10/Theorem14/CompletePivotedPSD.lean": (
        "NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.ActualComputation.ErrorBounds",
        "NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.RankSensitiveError.Bounds",
        "NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.RoundedErrorAnalysis.Bounds",
        "NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.SchurPerturbation.Family",
        "NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.SuccessfulRun.StageBounds",
    ),
}

R04_RETARGETS = {
    "NumStability/Source/Higham/Chapter06/Lemma06/OperatorTwoNormBound/Bridge.lean": (
        "NumStability.Source.Higham.Chapter06.Lemma06",
        "NumStability.Source.Higham.Chapter06.Lemma06.Core.Results",
    ),
    "NumStability/Source/Higham/Chapter10/Equation07/AbsoluteFactorNorm/Bridge.lean": (
        "NumStability.Source.Higham.Chapter06.Lemma06",
        "NumStability.Source.Higham.Chapter06.Lemma06.Core.Results",
    ),
    "NumStability/Source/Higham/Chapter14/Section03/ResidualOperatorTwoNorm/Bridge.lean": (
        "NumStability.Source.Higham.Chapter06.Lemma06",
        "NumStability.Source.Higham.Chapter06.Lemma06.Core.Results",
    ),
    "NumStability/Source/Higham/Chapter19/Theorem05/SourceClosure.lean": (
        "NumStability.Source.Higham.Chapter06.Lemma06",
        "NumStability.Source.Higham.Chapter06.Lemma06.Core.Results",
    ),
    "NumStability/Source/Higham/Chapter10/Theorem14/CompletePivotedPSD/Equation22.lean": (
        "NumStability.Source.Higham.Chapter10.Theorem07",
        "NumStability.Source.Higham.Chapter10.Theorem07.Core.Results",
    ),
    "NumStability/Source/Higham/Chapter10/Theorem14/CompletePivotedPSD/SourceError.lean": (
        "NumStability.Source.Higham.Chapter10.Theorem07",
        "NumStability.Source.Higham.Chapter10.Theorem07.Core.Results",
    ),
    "NumStability/Source/Higham/Chapter10/Theorem14/CompletePivotedPSD/SourceSuccess.lean": (
        "NumStability.Source.Higham.Chapter10.Theorem07",
        "NumStability.Source.Higham.Chapter10.Theorem07.Core.Results",
    ),
}

R08_AGGREGATE_IMPORTS = {
    "NumStability/Source/Higham/Chapter14/Algorithm04.lean": (
        "NumStability.Source.Higham.Chapter14.Algorithm04.FinalDivisionStage.FinalizedErrorFamilies",
    ),
    "NumStability/Source/Higham/Chapter14/Corollary06.lean": (
        "NumStability.Source.Higham.Chapter14.Corollary06.FinalizedRunRegularity.UniformInverseRegularity",
    ),
    "NumStability/Source/Higham/Chapter14/Corollary07.lean": (
        "NumStability.Source.Higham.Chapter14.Corollary07.FinalizedRunFamilies.ResidualAndForwardEnvelopes",
        "NumStability.Source.Higham.Chapter14.Corollary07.PrintedTraceFamilies.ResidualAndForwardEndpoints",
        "NumStability.Source.Higham.Chapter14.Corollary07.RowDominantCertificates.CumulativeProductBounds",
        "NumStability.Source.Higham.Chapter14.Corollary07.WeakDominanceFamilies.ResidualAndForwardBounds",
    ),
    "NumStability/Source/Higham/Chapter14/Problem02.lean": (
        "NumStability.Source.Higham.Chapter14.Problem02.TriangularInversion.TwoBlockFamilies.Derivations",
        "NumStability.Source.Higham.Chapter14.Problem02.TriangularInversion.TwoBlockFirstOrder.Derivations",
        "NumStability.Source.Higham.Chapter14.Problem02.TriangularInversion.TwoBlockMethod2B.FirstOrderBound",
    ),
    "NumStability/Source/Higham/Chapter14/Problem12.lean": (
        "NumStability.Source.Higham.Chapter14.Problem12.ConditionNumberExamples.StressAndPeiMatrices",
    ),
    "NumStability/Source/Higham/Chapter14/Section01.lean": (
        "NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ComposedCoefficientFamilies.RemainderAsymptotics",
        "NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ScaledPerturbationEndpoints.ForwardError",
    ),
    "NumStability/Source/Higham/Chapter14/Section02.lean": (
        "NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method1B.BlockResidual.WholeMatrixBounds",
        "NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2C.BlockResidual.LeftResidualBounds",
        "NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2C.WholeMatrixResidual.LeftResidualBounds",
    ),
    "NumStability/Source/Higham/Chapter14/Theorem05.lean": (
        "NumStability.Source.Higham.Chapter14.Theorem05.EliminationFamilies.CoefficientAsymptotics",
        "NumStability.Source.Higham.Chapter14.Theorem05.PrintedEnvelopes.CorrectionBounds",
        "NumStability.Source.Higham.Chapter14.Theorem05.PrintedTrace.VanishingEndpoints",
    ),
}


class GenerationError(RuntimeError):
    pass


@dataclass(frozen=True)
class Declaration:
    name: str
    owner: str
    kind: str
    visibility: str
    line: str


@dataclass(frozen=True)
class Edge:
    kind: str
    source: str
    target: str
    line: str


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def module_path(module: str) -> str:
    return module.replace(".", "/") + ".lean"


def module_from_path(path: str) -> str:
    if not path.endswith(".lean"):
        raise GenerationError(f"not a Lean module path: {path}")
    return path[:-5].replace("/", ".")


def canonical_json(value: Any) -> bytes:
    return (json.dumps(value, indent=1, sort_keys=True, ensure_ascii=False) + "\n").encode()


def pretty_json(value: Any) -> bytes:
    return (json.dumps(value, indent=2, ensure_ascii=False) + "\n").encode()


def tsv_bytes(header: Sequence[str], rows: Iterable[Sequence[Any]]) -> bytes:
    stream = io.StringIO(newline="")
    writer = csv.writer(stream, delimiter="\t", lineterminator="\n")
    writer.writerow(header)
    writer.writerows(rows)
    return stream.getvalue().encode("utf-8")


def list_bytes(rows: Iterable[str]) -> bytes:
    values = list(rows)
    return ("\n".join(values) + "\n").encode("utf-8")


def write_bytes(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists() and path.read_bytes() == payload:
        return
    path.write_bytes(payload)


def artifact(path: Path) -> dict[str, str]:
    return {"path": rel(path), "sha256": sha256_path(path)}


def git(*args: str, input_bytes: bytes | None = None) -> bytes:
    result = subprocess.run(
        ["git", *args],
        cwd=ROOT,
        input=input_bytes,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if result.returncode:
        raise GenerationError(
            f"git {' '.join(args)} failed: {result.stderr.decode(errors='replace').strip()}"
        )
    return result.stdout


def git_file(path: str) -> bytes:
    return git("show", f"{BASE_SHA}:{path}")


def git_file_at(revision: str, path: str) -> bytes:
    return git("show", f"{revision}:{path}")


def git_blob_oid(path: str) -> str:
    raw = git("ls-tree", BASE_SHA, "--", path).decode("utf-8").strip()
    if not raw:
        raise GenerationError(f"missing C0004 path {path}")
    metadata, returned = raw.split("\t", 1)
    _mode, kind, oid = metadata.split()
    if kind != "blob" or returned != path:
        raise GenerationError(f"unexpected tree entry for {path}: {raw}")
    return oid


def blob_oid(payload: bytes) -> str:
    header = f"blob {len(payload)}\0".encode("ascii")
    return hashlib.sha1(header + payload).hexdigest()


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open("r", encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def read_lines(path: Path) -> list[str]:
    return path.read_text(encoding="utf-8").splitlines()


def verify_inputs() -> None:
    expected = {
        GRAPH: GRAPH_SHA256,
        INVENTORY: INVENTORY_SHA256,
        BASELINE: BASELINE_SHA256,
        BASELINE_SUMMARY: BASELINE_SUMMARY_SHA256,
        PROJECTION_CHECKER: PROJECTION_CHECKER_SHA256,
    }
    for path, digest in expected.items():
        actual = sha256_path(path)
        if actual != digest:
            raise GenerationError(f"{path}: expected {digest}, found {actual}")
    ancestor = subprocess.run(
        ["git", "merge-base", "--is-ancestor", CONTROL_HEAD, "HEAD"],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if ancestor.returncode != 0:
        raise GenerationError(f"pinned control HEAD {CONTROL_HEAD} is not an ancestor of HEAD")
    production_diff = git(
        "diff",
        "--name-only",
        CONTROL_HEAD,
        "--",
        "NumStability",
        "NumStabilityTest",
        "benchmark-results",
    ).decode().strip()
    if production_diff:
        raise GenerationError(
            "production/test/benchmark drift from pinned control HEAD:\n"
            + production_diff
        )
    tree = git("rev-parse", f"{BASE_SHA}^{{tree}}").decode().strip()
    if tree != BASE_TREE:
        raise GenerationError(f"C0004 tree drifted: expected {BASE_TREE}, found {tree}")
    for name, digest in R08_RAW_HASHES.items():
        path = R08_FREEZE / name
        if path.is_file():
            actual = sha256_path(path)
            if actual != digest:
                raise GenerationError(f"{path}: expected {digest}, found {actual}")


def parse_graph() -> tuple[list[Declaration], list[Edge]]:
    declarations: list[Declaration] = []
    edges: list[Edge] = []
    with GRAPH.open("r", encoding="utf-8", newline="") as handle:
        first = handle.readline()
        if first != "format\t2\n":
            raise GenerationError("C0004 graph is not exact LF format 2")
        for number, line in enumerate(handle, 2):
            if not line.endswith("\n"):
                raise GenerationError(f"graph line {number} lacks LF")
            fields = line[:-1].split("\t")
            if fields[0] == "declaration" and len(fields) == 5:
                declarations.append(
                    Declaration(fields[1], fields[2], fields[3], fields[4], line)
                )
            elif (
                fields[0] == "edge"
                and len(fields) == 4
                and fields[1] in {"signature", "body"}
            ):
                edges.append(Edge(fields[1], fields[2], fields[3], line))
            else:
                raise GenerationError(f"unrecognized graph row {number}: {fields[:2]}")
    return declarations, edges


def inventory_rows() -> list[dict[str, str]]:
    rows = read_tsv(INVENTORY)
    if len(rows) != 2766:
        raise GenerationError(f"expected 2766 inventory rows, found {len(rows)}")
    return rows


def wave_selector(rows: list[dict[str, str]], wave: str) -> list[dict[str, str]]:
    selected = sorted(
        (row for row in rows if row["wave_id"] == wave), key=lambda row: row["module"]
    )
    expected = 19 if wave == "R04" else 45
    if len(selected) != expected:
        raise GenerationError(f"{wave}: expected {expected} owners, found {len(selected)}")
    if any(row["phase_scope"] != "in_scope" or row["lane_id"] != "claude-lane" for row in selected):
        raise GenerationError(f"{wave}: selector lane/scope drift")
    return selected


def private_tail(name: str) -> str:
    return name.rsplit(".", 1)[-1]


def r04_route(owner: str, declaration: str) -> tuple[str, str]:
    if owner in R04_WHOLE_DESTINATIONS:
        return R04_WHOLE_DESTINATIONS[owner], "relocate_whole"
    if owner in R04_AGGREGATE_DESTINATIONS:
        return R04_AGGREGATE_DESTINATIONS[owner], "umbrella_extract"
    if owner in R04_RETAINED:
        return "-", "retain_document"
    mapping = R04_SPLIT_DESTINATIONS.get(owner)
    if mapping is None:
        raise GenerationError(f"R04 owner has no route: {owner}")
    tail = private_tail(declaration)
    if tail not in mapping:
        raise GenerationError(f"R04 split route unresolved: {owner}::{declaration}")
    return mapping[tail], "relocate_split"


def build_routes(
    wave: str,
    selector: list[dict[str, str]],
    declarations: list[Declaration],
) -> tuple[list[tuple[str, ...]], dict[tuple[str, str], str]]:
    owners = {row["module"] for row in selector}
    r08_rows = (
        read_tsv(BRANCHES / "B0009-freeze-declaration-routes.tsv")
        if wave == "R08"
        else []
    )
    r08_routes = {
        (row["owner_module"], row["declaration"]): row["destination_module"]
        for row in r08_rows
    }
    expected_r08 = 211 if wave == "R08" else 0
    if len(r08_routes) != expected_r08:
        raise GenerationError(f"R08 raw routes expected 211 identities, found {len(r08_routes)}")
    rows: list[tuple[str, ...]] = []
    routed: dict[tuple[str, str], str] = {}
    declarations_by_owner: dict[str, list[Declaration]] = defaultdict(list)
    for declaration in declarations:
        if declaration.owner in owners:
            declarations_by_owner[declaration.owner].append(declaration)
    for selected in selector:
      for order, declaration in enumerate(declarations_by_owner[selected["module"]]):
          if wave == "R04":
              destination, route_class = r04_route(declaration.owner, declaration.name)
          else:
              destination = r08_routes.get((declaration.owner, declaration.name), "")
              if not destination:
                  raise GenerationError(
                      f"R08 route unresolved: {declaration.owner}::{declaration.name}"
                  )
              route_class = (
                  "umbrella_extract"
                  if declaration.owner.startswith("NumStability.Source.")
                  else "relocate_whole"
              )
          decision = (
              "module-scoped mangle rename"
              if declaration.visibility == "private" and destination != "-"
              else "-"
          )
          rows.append(
              (
                  declaration.owner,
                  declaration.name,
                  declaration.visibility,
                  declaration.kind,
                  str(order),
                  destination,
                  route_class,
                  decision,
              )
          )
          routed[(declaration.owner, declaration.name)] = (
              declaration.owner if destination == "-" else destination
          )
    expected = 289 if wave == "R04" else 211
    if len(rows) != expected:
        raise GenerationError(f"{wave}: expected {expected} routes, found {len(rows)}")
    return rows, routed


def deterministic_gzip(payload: bytes) -> bytes:
    stream = io.BytesIO()
    with gzip.GzipFile(filename="", mode="wb", fileobj=stream, compresslevel=9, mtime=0) as handle:
        handle.write(payload)
    return stream.getvalue()


def build_projection(
    projection_id: str,
    selector: list[dict[str, str]],
    declarations: list[Declaration],
    edges: list[Edge],
) -> tuple[Path, dict[str, int], str]:
    owners = {row["module"] for row in selector}
    selected = [declaration for declaration in declarations if declaration.owner in owners]
    names = {declaration.name for declaration in selected}
    incident = [edge for edge in edges if edge.source in names or edge.target in names]
    selected.sort(key=lambda declaration: declaration.name)
    incident.sort(key=lambda edge: (edge.source, 0 if edge.kind == "signature" else 1, edge.target))
    payload = (
        "format\t2\n"
        + "".join(declaration.line for declaration in selected)
        + "".join(edge.line for edge in incident)
    ).encode("utf-8")
    path = PROJECTIONS / f"{projection_id}.tsv.gz"
    write_bytes(path, deterministic_gzip(payload))
    pairs = {(edge.source, edge.target) for edge in incident}
    counts = {
        "body_edges": sum(edge.kind == "body" for edge in incident),
        "declarations": len(selected),
        "signature_edges": sum(edge.kind == "signature" for edge in incident),
        "union_edges": len(pairs),
    }
    return path, counts, sha256_bytes(payload)


def build_private_map(
    route_rows: list[tuple[str, ...]],
) -> list[tuple[str, str, str]]:
    rows: list[tuple[str, str, str]] = []
    for owner, declaration, visibility, _kind, _order, destination, _route_class, _decision in route_rows:
        if visibility != "private":
            continue
        actual_destination = owner if destination == "-" else destination
        new = declaration if destination == "-" else declaration.replace(
            f"_private.{owner}.0.", f"_private.{actual_destination}.0.", 1
        )
        if destination != "-" and new == declaration:
            raise GenerationError(f"cannot normalize private {declaration}")
        rows.append((declaration, new, actual_destination))
    moving = sorted((row for row in rows if row[0] != row[1]), key=lambda row: row[0])
    identities = sorted((row for row in rows if row[0] == row[1]), key=lambda row: row[0])
    return moving + identities


def build_private_closure(
    route_rows: list[tuple[str, ...]],
    declarations: list[Declaration],
    edges: list[Edge],
    selected_owners: set[str],
) -> list[tuple[str, str, str, str, str]]:
    metadata = {declaration.name: declaration for declaration in declarations}
    seeds = {
        row[1]
        for row in route_rows
        if row[2] == "private"
    }
    reverse: dict[str, set[str]] = defaultdict(set)
    for edge in edges:
        reverse[edge.target].add(edge.source)
    reached = set(seeds)
    queue = deque(sorted(seeds))
    while queue:
        target = queue.popleft()
        for source in sorted(reverse.get(target, ())):
            if source not in reached:
                reached.add(source)
                queue.append(source)
    rows: list[tuple[str, str, str, str, str]] = []
    for name in sorted(reached):
        declaration = metadata.get(name)
        if declaration is None:
            raise GenerationError(f"closure declaration missing metadata: {name}")
        rows.append(
            (
                name,
                declaration.owner,
                declaration.visibility,
                "yes" if declaration.owner in selected_owners else "no",
                "private_seed" if name in seeds else "reverse_dependent",
            )
        )
    return rows


def route_dag(
    routed: dict[tuple[str, str], str], edges: list[Edge]
) -> list[tuple[str, str, int, int]]:
    destination_by_name = {name: destination for (_owner, name), destination in routed.items()}
    counts: dict[tuple[str, str], Counter[str]] = defaultdict(Counter)
    for edge in edges:
        source_destination = destination_by_name.get(edge.source)
        target_destination = destination_by_name.get(edge.target)
        if (
            source_destination is not None
            and target_destination is not None
            and source_destination != target_destination
        ):
            counts[(source_destination, target_destination)][edge.kind] += 1
    return [
        (source, target, kinds["signature"], kinds["body"])
        for (source, target), kinds in sorted(counts.items())
    ]


def copy_freeze_evidence() -> None:
    r04_files = {
        "R04-post-move-import-manifest.tsv": "B0008-post-move-import-manifest.tsv",
        "R04-recursive-frontier.tsv": "B0008-recursive-frontier.tsv",
        "R04-external-owner-supply.tsv": "B0008-external-owner-supply.tsv",
        "R04-split-wrapper-transitive.tsv": "B0008-split-wrapper-transitive.tsv",
        "R04-aggregate-reachability.tsv": "B0008-aggregate-reachability.tsv",
        "R04-aggregate-build-targets.txt": "B0008-aggregate-build-targets.txt",
    }
    r04_hashes = {
        "R04-post-move-import-manifest.tsv": "8BF709213AD10F47011BF4A2084A6E6B0D3E551C84FD8E7EFA8F43296EC50A86",
        "R04-recursive-frontier.tsv": "995F92EC325FF1B50E8E8EA755964E2258EBAD3BABCCB4912DB27351B41E88D2",
        "R04-external-owner-supply.tsv": "829E4F61AEB5EA75018CAE6CFAB36AB6F8AACD88DEB8C921D1C406A1A1E26D10",
        "R04-split-wrapper-transitive.tsv": "CC8E1D4F967D2B4626FE4485C91FBBA7AD3E24E38705C31081373D85365A1F8C",
        "R04-aggregate-reachability.tsv": "5766429BA5F6F7C2795B012148BFB6AEB91CF3574D2E244F44D9F135DBBE3AB9",
        "R04-aggregate-build-targets.txt": "F0E961902044166799F65F90ED6BFD8FB31F74196CE460FEFE77178ABF2877AA",
    }
    for source_name, destination_name in r04_files.items():
        source = R04_FREEZE / source_name
        target = BRANCHES / destination_name
        expected = r04_hashes[source_name]
        if source.is_file() and sha256_path(source) == expected:
            write_bytes(target, source.read_bytes())
        elif not target.is_file() or sha256_path(target) != expected:
            raise GenerationError(
                f"missing or changed R04 freeze artifact: external={source}, branch={target}"
            )

    r08_files = {
        "R08-declaration-routes.tsv": "B0009-freeze-declaration-routes.tsv",
        "R08-destination-modules.txt": "B0009-destination-modules.txt",
        "R08-destination-prefixes.txt": "B0009-destination-prefixes.txt",
        "R08-branch-prefixes.txt": "B0009-branch-prefixes.txt",
        "R08-private-normalization.tsv": "B0009-freeze-private-normalization.tsv",
        "R08-destination-dag.tsv": "B0009-freeze-destination-dag.tsv",
        "R08-post-move-import-manifest.tsv": "B0009-post-move-import-manifest.tsv",
        "R08-Algorithms-deletions.txt": "B0009-algorithms-deletions.txt",
        "R08-R0010-shared-paths.txt": "B0009-shared-request-paths.txt",
        "R08-outside-consumers.txt": "B0009-outside-consumers.txt",
        "R08-test-modules.txt": "B0009-freeze-test-modules.txt",
    }
    for source_name, destination_name in r08_files.items():
        source = R08_FREEZE / source_name
        target = BRANCHES / destination_name
        expected = R08_RAW_HASHES[source_name]
        if source.is_file() and sha256_path(source) == expected:
            write_bytes(target, source.read_bytes())
        elif not target.is_file() or sha256_path(target) != expected:
            raise GenerationError(
                f"missing or changed R08 freeze artifact: external={source}, branch={target}"
            )


def destinations_by_owner(route_rows: list[tuple[str, ...]]) -> dict[str, list[str]]:
    values: dict[str, set[str]] = defaultdict(set)
    for owner, _declaration, _visibility, _kind, _order, destination, _route_class, _decision in route_rows:
        values[owner].add(destination)
    return {owner: sorted(destinations) for owner, destinations in values.items()}


def build_module_routes(
    wave: str,
    selector: list[dict[str, str]],
    route_rows: list[tuple[str, ...]],
) -> bytes:
    counts = Counter(row[0] for row in route_rows)
    route_classes: dict[str, str] = {}
    for row in route_rows:
        route_classes.setdefault(row[0], row[6])
        if route_classes[row[0]] != row[6]:
            raise GenerationError(f"owner has mixed route classes: {row[0]}")
    per_owner = destinations_by_owner(route_rows)
    output: list[tuple[str, ...]] = []
    for inventory in selector:
        owner = inventory["module"]
        count = counts[owner]
        route_class = route_classes.get(owner, "classify_compatibility")
        destinations = per_owner.get(owner, ["-"])
        if route_class == "retain_document":
            action = "retained reusable owner; classify and document only"
            split = "retained owner; no declaration relocation"
        elif route_class == "classify_compatibility":
            action = "remove inert open declarations only; preserve all imports byte-for-byte"
            split = "declaration-free compatibility registration; no declaration route"
        elif route_class == "umbrella_extract":
            action = "owner becomes declaration-free source aggregate importing its new child"
            split = "whole aggregate extraction; no declaration split"
        elif route_class == "relocate_split":
            action = "owner becomes declaration-free compatibility wrapper importing every routed destination"
            split = "reviewed semantic split; every private-sharing component remains indivisible"
        else:
            action = "owner becomes declaration-free compatibility wrapper importing its routed destination"
            split = "whole-owner relocation; no declaration split"
        dependency = (
            "exact post-move import manifest and recursive supply proofs freeze the historical surface"
            if wave == "R04"
            else "existing shim imports are frozen; destination import floor and DAG are hash-pinned"
        )
        output.append(
            (
                owner,
                inventory["path"],
                inventory["base_blob_oid"],
                inventory["current_tier"],
                inventory["debt_flags"],
                str(count),
                route_class,
                ";".join(destinations),
                action,
                split,
                dependency,
                "frozen_before_activation",
            )
        )
    return tsv_bytes(
        (
            "owner_module",
            "path",
            "base_blob_oid",
            "current_tier",
            "debt_flags",
            "declaration_count",
            "semantic_classification",
            "destination_modules",
            "compatibility_action",
            "split_rationale",
            "dependency_rationale",
            "review_status",
        ),
        output,
    )


def build_tier_assignments(
    wave: str,
    selector: list[dict[str, str]],
    route_rows: list[tuple[str, ...]],
) -> bytes:
    route_classes = {row[0]: row[6] for row in route_rows}
    rows: dict[str, tuple[str, str]] = {}
    for selected in selector:
        module = selected["module"]
        route_class = route_classes.get(module, "classify_compatibility")
        if module.startswith("NumStability.Source.") and route_class == "umbrella_extract":
            rows[module] = ("aggregate", "declarations evacuate to a new child; historical source path becomes aggregate")
        elif route_class == "retain_document":
            rows[module] = ("reusable", "reviewed reusable owner retained in place")
        else:
            rows[module] = ("compatibility", "historical Algorithm path is import-only after the wave")
    destinations = (
        R04_DESTINATION_TIERS
        if wave == "R04"
        else {
            module: "source"
            for module in read_lines(BRANCHES / "B0009-destination-modules.txt")
        }
    )
    for module, tier in destinations.items():
        rows[module] = (tier, "new casefold-vacant semantic declaration destination")
    return tsv_bytes(
        ("module", "tier", "reason"),
        ((module, tier, reason) for module, (tier, reason) in sorted(rows.items())),
    )


def test_path(category: str, module: str) -> str:
    filename = module.replace(".", "_") + ".lean"
    return f"NumStabilityTest/Reorganization/R04/{category}/{filename}"


def build_r04_tests(
    route_rows: list[tuple[str, ...]], selector: list[dict[str, str]]
) -> tuple[bytes, list[str]]:
    classes = {row[0]: row[6] for row in route_rows}
    historical = [
        row["module"]
        for row in selector
        if classes.get(row["module"]) in {"relocate_whole", "relocate_split", "umbrella_extract"}
    ]
    destinations = sorted(R04_DESTINATION_TIERS)
    modules = [test_path("OldOnly", module) for module in historical]
    modules += [test_path("Canonical", module) for module in destinations]
    modules += [test_path("Consumer", module) for module in R04_OUTSIDE_CONSUMERS]
    modules += ["NumStabilityTest/Reorganization/R04/PrivateNormalization.lean"]
    modules = sorted(modules)
    if len(modules) != 75:
        raise GenerationError(f"R04 expected 75 leaf tests, found {len(modules)}")
    all_module = "NumStabilityTest/Reorganization/R04/All.lean"
    full = sorted(modules + [all_module])
    rows: list[tuple[str, str, str]] = []
    for path in full:
        if path.endswith("/All.lean"):
            kind = "all"
            purpose = "branch-owned aggregate imports every R04 leaf test"
        elif "/OldOnly/" in path:
            kind = "old_only"
            purpose = "historical module alone checks its complete C0004 public surface"
        elif "/Canonical/" in path:
            kind = "canonical_only"
            purpose = "canonical destination alone checks every routed public declaration"
        elif "/Consumer/" in path:
            kind = "consumer"
            purpose = "outside direct consumer continues to elaborate"
        else:
            kind = "private_normalization"
            purpose = "all 115 private mappings are total; only 101 old names retire"
        rows.append((kind, path, purpose))
    return tsv_bytes(("test_class", "target", "purpose"), rows), full


def build_r08_tests() -> tuple[bytes, list[str]]:
    leaves = read_lines(BRANCHES / "B0009-freeze-test-modules.txt")
    if len(leaves) != 78:
        raise GenerationError(f"R08 expected 78 raw test leaves, found {len(leaves)}")
    all_module = "NumStabilityTest/Reorganization/R08/All.lean"
    modules = sorted(leaves + [all_module])
    expected_hash = "CF2D7A28A8447BBFDC2A23EF2DE08CDE1E4AEB27E11FC5621874882DCAE5A254"
    if sha256_bytes(list_bytes(modules)) != expected_hash:
        raise GenerationError("corrected 79-module R08 test list hash drift")
    rows: list[tuple[str, str, str]] = []
    for path in modules:
        if path.endswith("/All.lean"):
            kind, purpose = "all", "branch-owned aggregate imports every R08 leaf test"
        else:
            category = path.split("/R08/", 1)[1].split("/", 1)[0]
            mapping = {
                "OldPath": ("old_only", "newly evacuated historical Algorithm path checks its residual C0004 surface"),
                "Canonical": ("canonical_only", "new destination alone checks its routed declaration surface"),
                "Consumer": ("consumer", "outside direct import consumer continues to elaborate"),
                "Focused": ("focused", "semantic Chapter 14 cluster build"),
                "PrivateNormalization": ("private_normalization", "private owner rewrite is total and exact"),
                "AggregateCompleteness": ("aggregate_completeness", "new declaration-free aggregate reaches its child"),
            }
            kind, purpose = mapping[category]
        rows.append((kind, path, purpose))
    return tsv_bytes(("test_class", "target", "purpose"), rows), modules


IMPORT_RE = re.compile(r"^import\s+([^\s]+)\s*$", re.MULTILINE)


def imports_at_base(module: str) -> list[str]:
    payload = git_file(module_path(module)).decode("utf-8")
    return IMPORT_RE.findall(payload)


def build_consumers(
    wave: str,
    selector: list[dict[str, str]],
    route_rows: list[tuple[str, ...]],
) -> bytes:
    selected = {row["module"] for row in selector}
    per_owner = destinations_by_owner(route_rows)
    consumers = (
        list(R04_OUTSIDE_CONSUMERS)
        if wave == "R04"
        else read_lines(BRANCHES / "B0009-outside-consumers.txt")
    )
    rows: list[tuple[str, str, str, str, str]] = []
    for consumer in consumers:
        path = module_path(consumer)
        old_imports = sorted(set(imports_at_base(consumer)) & selected)
        if not old_imports:
            raise GenerationError(f"{wave} outside consumer has no direct selected import: {consumer}")
        for old in old_imports:
            if wave == "R08" and consumer == "NumStability.Algorithms":
                new = "-"
            elif wave == "R04" and path == "NumStability/Algorithms.lean" and old in per_owner:
                route_classes = {row[6] for row in route_rows if row[0] == old}
                if route_classes <= {"relocate_whole", "relocate_split"}:
                    new = ";".join(
                        destination
                        for destination in per_owner[old]
                        if destination != "-"
                    )
                else:
                    new = old
            elif wave == "R04" and path in R04_RETARGETS and old == R04_RETARGETS[path][0]:
                new = R04_RETARGETS[path][1]
            else:
                new = old
            rows.append((consumer, path, "outside", old, new))
    rows.sort()
    return tsv_bytes(
        ("consumer_module", "consumer_path", "consumer_scope", "old_import", "new_import"),
        rows,
    )


def build_field_scan(wave: str) -> bytes:
    if wave == "R04":
        rows = (
            (
                "NumStability/Source/Higham/Chapter06/Lemma06/OperatorTwoNormBound/Bridge.lean",
                "Lemma66.* namespace qualification; no receiver-style field notation",
                "retarget to Lemma06.Core.Results preserves qualified namespace supply",
            ),
            (
                "NumStability/Source/Higham/Chapter14/Section03/ResidualOperatorTwoNorm/Bridge.lean",
                "Lemma66.* namespace qualification; no receiver-style field notation",
                "retarget to Lemma06.Core.Results preserves qualified namespace supply",
            ),
            (
                "NumStability/Source/Higham/Chapter19/Theorem05/SourceClosure.lean",
                "Lemma66.* namespace qualification; no receiver-style field notation",
                "retarget to Lemma06.Core.Results preserves one signature and five body edges",
            ),
            (
                "-",
                "structure projections product_eq;R_upper;R_diag_pos;R_rank_zero;perm",
                "canonical destinations import the exact defining specification modules",
            ),
        )
    else:
        rows = (
            (
                "-",
                "zero owner-defined structures/classes; 858 qualified dot tokens are not receiver moves",
                "no R08 field/projection surface moves; anonymous constructors retain external defining imports",
            ),
        )
    return tsv_bytes(
        (
            "consumer_path",
            "dot_notation_token_matching_relocated_declaration",
            "supply_after_retarget",
        ),
        rows,
    )


def write_branch_sidecars(
    wave: str,
    branch_id: str,
    selector: list[dict[str, str]],
    route_rows: list[tuple[str, ...]],
) -> list[str]:
    outputs: list[Path] = []
    module_path_out = BRANCHES / f"{branch_id}-module-routes.tsv"
    write_bytes(module_path_out, build_module_routes(wave, selector, route_rows))
    outputs.append(module_path_out)
    tier_path = BRANCHES / f"{branch_id}-tier-assignments.tsv"
    write_bytes(tier_path, build_tier_assignments(wave, selector, route_rows))
    outputs.append(tier_path)
    consumer_path = BRANCHES / f"{branch_id}-consumers.tsv"
    write_bytes(consumer_path, build_consumers(wave, selector, route_rows))
    outputs.append(consumer_path)
    field_path = BRANCHES / f"{branch_id}-field-projection-scan.tsv"
    write_bytes(field_path, build_field_scan(wave))
    outputs.append(field_path)
    tests, modules = (
        build_r04_tests(route_rows, selector) if wave == "R04" else build_r08_tests()
    )
    test_path_out = BRANCHES / f"{branch_id}-test-plan.tsv"
    write_bytes(test_path_out, tests)
    outputs.append(test_path_out)
    test_modules_path = BRANCHES / f"{branch_id}-test-modules.txt"
    write_bytes(test_modules_path, list_bytes(modules))
    outputs.append(test_modules_path)
    return [rel(path) for path in outputs]


def edit_imports(
    payload: bytes,
    *,
    add: Iterable[str] = (),
    remove: Iterable[str] = (),
) -> bytes:
    """Edit one contiguous Lean import block and preserve its newline style."""

    text = payload.decode("utf-8")
    newline = "\r\n" if "\r\n" in text else "\n"
    final_newline = text.endswith(("\n", "\r"))
    lines = text.splitlines()
    import_rows: list[tuple[int, str]] = []
    for index, line in enumerate(lines):
        match = re.fullmatch(r"import\s+([^\s]+)", line)
        if match:
            import_rows.append((index, match.group(1)))
    if not import_rows:
        raise GenerationError("expected a Lean import block")
    first = import_rows[0][0]
    last = import_rows[-1][0]
    if [index for index, _ in import_rows] != list(range(first, last + 1)):
        raise GenerationError("Lean import block is not contiguous")
    imports = {module for _, module in import_rows}
    missing = set(remove) - imports
    if missing:
        raise GenerationError(f"cannot remove absent imports: {sorted(missing)}")
    imports.difference_update(remove)
    imports.update(add)
    rewritten = (
        lines[:first]
        + [f"import {module}" for module in sorted(imports, key=str.casefold)]
        + lines[last + 1 :]
    )
    result = newline.join(rewritten)
    if final_newline:
        result += newline
    return result.encode("utf-8")


def compatibility_rows_from_manifest(wave: str) -> dict[str, tuple[str, ...]]:
    mappings: dict[str, list[str]] = defaultdict(list)
    if wave == "R04":
        rows = read_tsv(BRANCHES / "B0008-post-move-import-manifest.tsv")
        selected_rows = [row for row in rows if row["role"] == "compatibility"]
        if len(selected_rows) != 134:
            raise GenerationError(
                f"R04: expected 134 compatibility import rows, found {len(selected_rows)}"
            )
        for row in rows:
            if row["role"] != "compatibility":
                continue
            line = row["lean_import_line"]
            if not line.startswith("import "):
                raise GenerationError(f"malformed R04 import manifest row: {line}")
            mappings[row["module"]].append(line.removeprefix("import "))
        if sum(
            target.startswith("NumStability.")
            for targets in mappings.values()
            for target in targets
        ) != 121:
            raise GenerationError("R04: compatibility NumStability import count is not 121")
        for module, module_rows in itertools.groupby(
            selected_rows, key=lambda row: row["module"]
        ):
            orders = [int(row["import_order"]) for row in module_rows]
            if orders != list(range(1, len(orders) + 1)):
                raise GenerationError(
                    f"R04: noncontiguous compatibility import_order for {module}: {orders}"
                )
        expected = 12
    else:
        rows = read_tsv(BRANCHES / "B0009-post-move-import-manifest.tsv")
        selected_rows = [
            row for row in rows if row["role"].startswith("compatibility-shim")
        ]
        if len(selected_rows) != 278:
            raise GenerationError(
                f"R08: expected 278 compatibility import rows, found {len(selected_rows)}"
            )
        for row in rows:
            if not row["role"].startswith("compatibility-shim"):
                continue
            module = row["import"]
            mappings[row["module"]].append(module)
        if sum(
            target.startswith("NumStability.")
            for targets in mappings.values()
            for target in targets
        ) != 241:
            raise GenerationError("R08: compatibility NumStability import count is not 241")
        expected = 42
    if len(mappings) != expected:
        raise GenerationError(
            f"{wave}: expected {expected} compatibility mappings, found {len(mappings)}"
        )
    return {module: tuple(imports) for module, imports in sorted(mappings.items())}


def format_compatibility_targets(targets: Sequence[str]) -> str:
    quoted = [f"`{target}`" for target in targets]
    if len(quoted) == 1:
        return quoted[0]
    if len(quoted) == 2:
        return f"{quoted[0]} and {quoted[1]}"
    return ", ".join(quoted[:-1]) + f", and {quoted[-1]}"


def render_compatibility(waves: frozenset[str]) -> bytes:
    source = git_file("docs/architecture/COMPATIBILITY.md").decode("utf-8")
    lines = source.splitlines()
    try:
        header = lines.index("| Historical path | Canonical path |")
    except ValueError as error:
        raise GenerationError("compatibility table header missing") from error
    end = header + 2
    table_rows: dict[str, str] = {}
    while end < len(lines) and lines[end].startswith("|"):
        names = re.findall(r"`(NumStability(?:\.[A-Za-z0-9_']+)+)`", lines[end])
        if len(names) < 2:
            raise GenerationError(f"malformed compatibility row: {lines[end]}")
        if names[0] in table_rows:
            raise GenerationError(f"duplicate compatibility row: {names[0]}")
        table_rows[names[0]] = lines[end]
        end += 1
    for wave in sorted(waves):
        for historical, targets in compatibility_rows_from_manifest(wave).items():
            if historical in table_rows:
                raise GenerationError(f"new compatibility path already tabled: {historical}")
            table_rows[historical] = (
                f"| `{historical}` | {format_compatibility_targets(targets)} |"
            )
    table = [table_rows[historical] for historical in sorted(table_rows)]
    rewritten = lines[: header + 2] + table + lines[end:]
    return ("\n".join(rewritten) + "\n").encode("utf-8")


def render_tiers(
    waves: frozenset[str], selectors: dict[str, list[dict[str, str]]]
) -> bytes:
    document = json.loads(git_file("docs/architecture/tiers.json"))
    exact = dict(document["exact"])
    if "R04" in waves:
        for owner in R04_WHOLE_DESTINATIONS:
            exact[owner] = "compatibility"
        for owner in R04_SPLIT_DESTINATIONS:
            exact[owner] = "compatibility"
        for owner in R04_AGGREGATE_DESTINATIONS:
            exact[owner] = "aggregate"
        for owner in R04_RETAINED:
            exact[owner] = "reusable"
        exact.update(R04_DESTINATION_TIERS)
    if "R08" in waves:
        for row in selectors["R08"]:
            module = row["module"]
            exact[module] = (
                "compatibility"
                if module.startswith("NumStability.Algorithms.")
                else "aggregate"
            )
        for module in read_lines(BRANCHES / "B0009-destination-modules.txt"):
            exact[module] = "source"
    document["exact"] = {module: exact[module] for module in sorted(exact)}
    return (json.dumps(document, indent=2) + "\n").encode("utf-8")


def render_layout_exceptions(
    waves: frozenset[str], selectors: dict[str, list[dict[str, str]]]
) -> bytes:
    document = json.loads(git_file("docs/architecture/layout-exceptions.json"))
    selected = {
        row["module"]
        for wave in waves
        for row in selectors[wave]
    }
    for key in (
        "declaration_bearing_umbrellas",
        "noncanonical_modules",
        "unclassified_modules",
    ):
        document["legacy"][key] = [
            module for module in document["legacy"][key] if module not in selected
        ]
    if "R04" in waves:
        document["direct_import_ceilings"]["NumStability.Algorithms"][
            "NumStability.Source."
        ] = 72
    expected = {
        frozenset({"R04"}): (5, 114, 175),
        frozenset({"R08"}): (4, 87, 149),
        frozenset({"R04", "R08"}): (1, 76, 133),
    }[waves]
    actual = tuple(
        len(document["legacy"][key])
        for key in (
            "declaration_bearing_umbrellas",
            "noncanonical_modules",
            "unclassified_modules",
        )
    )
    if actual != expected:
        raise GenerationError(f"layout debt count drift for {sorted(waves)}: {actual} != {expected}")
    return (json.dumps(document, indent=2) + "\n").encode("utf-8")


def render_migration() -> bytes:
    payload = git_file("docs/architecture/MIGRATION.md")
    text = payload.decode("utf-8").rstrip("\r\n")
    newline = "\r\n" if "\r\n" in text else "\n"
    addition = newline.join(
        (
            "",
            "",
            "## Planned Chapter 14 matrix-inversion compatibility completion",
            "",
            "R08 preserves 42 historical Algorithm import paths as declaration-free compatibility",
            "modules, relocates their remaining C0004 declarations whole-owner into 21 new Source",
            "leaves, and converts the Chapter 14 Problem13, Problem14, and Problem15 entry points",
            "into declaration-free aggregates. The accepted W08 regression suite remains unchanged;",
            "the R08 delivery adds isolated old-path, canonical, consumer, focused, private-name, and",
            "aggregate-completeness tests under `NumStabilityTest.Reorganization.R08`.",
        )
    )
    return (text + addition + newline).encode("utf-8")


def request_postimages(
    waves: frozenset[str], selectors: dict[str, list[dict[str, str]]]
) -> dict[str, bytes]:
    paths = sorted(
        set(R0009_PATHS if "R04" in waves else ())
        | set(R0010_PATHS if "R08" in waves else ())
    )
    postimages: dict[str, bytes] = {}
    for path in paths:
        base = git_file(path)
        add: set[str] = set()
        remove: set[str] = set()
        if path == "NumStability/Algorithms.lean":
            if "R04" in waves:
                remove.update(R04_WHOLE_DESTINATIONS)
                remove.update(R04_SPLIT_DESTINATIONS)
                add.update(
                    set(R04_DESTINATION_TIERS)
                    - set(R04_AGGREGATE_DESTINATIONS.values())
                )
            if "R08" in waves:
                remove.update(read_lines(BRANCHES / "B0009-algorithms-deletions.txt"))
            post = edit_imports(base, add=add, remove=remove)
        elif path == "NumStabilityTest.lean":
            if "R04" in waves:
                add.add("NumStabilityTest.Reorganization.R04.All")
            if "R08" in waves:
                add.add("NumStabilityTest.Reorganization.R08.All")
            post = edit_imports(base, add=add)
        elif path == "docs/architecture/COMPATIBILITY.md":
            post = render_compatibility(waves)
        elif path == "docs/architecture/tiers.json":
            post = render_tiers(waves, selectors)
        elif path == "docs/architecture/layout-exceptions.json":
            post = render_layout_exceptions(waves, selectors)
        elif path == "docs/architecture/MIGRATION.md":
            post = render_migration()
        elif "R04" in waves and path in R04_AGGREGATE_IMPORTS:
            post = edit_imports(base, add=R04_AGGREGATE_IMPORTS[path])
        elif "R08" in waves and path in R08_AGGREGATE_IMPORTS:
            post = edit_imports(base, add=R08_AGGREGATE_IMPORTS[path])
        elif "R04" in waves and path in R04_RETARGETS:
            old, new = R04_RETARGETS[path]
            post = edit_imports(base, add=(new,), remove=(old,))
        else:
            raise GenerationError(f"no shared-file transform for {path} in {sorted(waves)}")
        if post == base:
            raise GenerationError(f"shared-file transform is a no-op: {path}")
        if path == "NumStability/Algorithms.lean":
            imports = IMPORT_RE.findall(post.decode("utf-8"))
            expected_counts = {
                frozenset({"R04"}): (296, 36, 72),
                frozenset({"R08"}): (238, 35, 49),
                frozenset({"R04", "R08"}): (254, 36, 72),
            }[waves]
            actual_counts = (
                len(imports),
                sum(module.startswith("NumStability.Analysis.") for module in imports),
                sum(module.startswith("NumStability.Source.") for module in imports),
            )
            if actual_counts != expected_counts:
                raise GenerationError(
                    f"Algorithms import-count drift for {sorted(waves)}: "
                    f"{actual_counts} != {expected_counts}"
                )
            if waves == frozenset({"R08"}) and sha256_bytes(post) != (
                "0DEF3FD36DD507444AC0A317170966B62724BD3155B5DDBC652D33132B58CC3A"
            ):
                raise GenerationError("R0010 Algorithms postimage drift from frozen evidence")
        postimages[path] = post
    return postimages


def zero_context_patch(postimages: dict[str, bytes]) -> bytes:
    chunks: list[bytes] = []
    for path in sorted(postimages):
        before = git_file(path)
        after = postimages[path]
        old_oid = git_blob_oid(path)
        new_oid = blob_oid(after)
        chunks.append(f"diff --git a/{path} b/{path}\n".encode("utf-8"))
        chunks.append(f"index {old_oid}..{new_oid} 100644\n".encode("ascii"))
        diff = difflib.unified_diff(
            before.decode("utf-8").splitlines(keepends=True),
            after.decode("utf-8").splitlines(keepends=True),
            fromfile=f"a/{path}",
            tofile=f"b/{path}",
            n=0,
            lineterm="\n",
        )
        chunks.append("".join(diff).encode("utf-8"))
    return b"".join(chunks)


def postimage_ledger(postimages: dict[str, bytes]) -> bytes:
    rows = []
    for path, after in sorted(postimages.items()):
        before = git_file(path)
        rows.append(
            (
                path,
                git_blob_oid(path),
                sha256_bytes(before),
                sha256_bytes(after),
            )
        )
    return tsv_bytes(
        ("path", "preimage_blob_oid", "preimage_sha256", "postimage_sha256"),
        rows,
    )


def run_git_with_index(index: Path, *args: str) -> subprocess.CompletedProcess[bytes]:
    environment = os.environ.copy()
    environment["GIT_INDEX_FILE"] = str(index)
    object_directory = index.parent / "objects"
    object_directory.mkdir(exist_ok=True)
    main_objects = git("rev-parse", "--git-path", "objects").decode().strip()
    main_objects_path = (ROOT / main_objects).resolve()
    environment["GIT_OBJECT_DIRECTORY"] = str(object_directory)
    environment["GIT_ALTERNATE_OBJECT_DIRECTORIES"] = str(main_objects_path)
    return subprocess.run(
        ["git", *args],
        cwd=ROOT,
        env=environment,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )


def verify_patch_replay(
    patch_path: Path,
    postimages: dict[str, bytes],
) -> None:
    with tempfile.TemporaryDirectory(prefix="c0005-request-replay-") as directory:
        index = Path(directory) / "index"
        read_tree = run_git_with_index(index, "read-tree", BASE_SHA)
        if read_tree.returncode != 0:
            raise GenerationError(read_tree.stderr.decode("utf-8", errors="replace"))
        checked = run_git_with_index(
            index,
            "apply",
            "--cached",
            "--check",
            "--unidiff-zero",
            "--whitespace=error-all",
            str(patch_path),
        )
        if checked.returncode != 0:
            raise GenerationError(
                f"patch check failed for {patch_path}: "
                + checked.stderr.decode("utf-8", errors="replace")
            )
        applied = run_git_with_index(
            index,
            "apply",
            "--cached",
            "--unidiff-zero",
            "--whitespace=error-all",
            str(patch_path),
        )
        if applied.returncode != 0:
            raise GenerationError(
                f"patch replay failed for {patch_path}: "
                + applied.stderr.decode("utf-8", errors="replace")
            )
        names = run_git_with_index(index, "diff", "--cached", "--name-only", BASE_SHA)
        changed = names.stdout.decode("utf-8").splitlines()
        if changed != sorted(postimages):
            raise GenerationError(
                f"patch changed-path drift for {patch_path}: {changed} != {sorted(postimages)}"
            )
        for path, expected in sorted(postimages.items()):
            actual = run_git_with_index(index, "show", f":{path}")
            if actual.returncode != 0 or actual.stdout != expected:
                raise GenerationError(f"postimage replay mismatch for {patch_path}: {path}")
        reverse_checked = run_git_with_index(
            index,
            "apply",
            "--cached",
            "--check",
            "--reverse",
            "--unidiff-zero",
            "--whitespace=error-all",
            str(patch_path),
        )
        if reverse_checked.returncode != 0:
            raise GenerationError(
                f"reverse patch check failed for {patch_path}: "
                + reverse_checked.stderr.decode("utf-8", errors="replace")
            )
        reversed_patch = run_git_with_index(
            index,
            "apply",
            "--cached",
            "--reverse",
            "--unidiff-zero",
            "--whitespace=error-all",
            str(patch_path),
        )
        if reversed_patch.returncode != 0:
            raise GenerationError(
                f"reverse replay failed for {patch_path}: "
                + reversed_patch.stderr.decode("utf-8", errors="replace")
            )
        tree = run_git_with_index(index, "write-tree")
        if tree.returncode != 0 or tree.stdout.decode().strip() != BASE_TREE:
            raise GenerationError(f"reverse replay did not reconstruct C0004 for {patch_path}")


def shared_request_record(
    request_id: str,
    wave: str,
    paths: Sequence[str],
    patch_path: Path,
) -> dict[str, Any]:
    path_hash = sha256_bytes(list_bytes(paths))
    return {
        "blocks": [wave],
        "created_at": "2026-08-17T00:00:00Z",
        "depends_on": [],
        "lane_id": "claude-lane",
        "patch": artifact(patch_path),
        "paths": list(paths),
        "phase_id": PHASE_ID,
        "preimage_blobs": [
            {"blob_oid": git_blob_oid(path), "path": path} for path in paths
        ],
        "rationale": (
            f"Primary-human {wave} shared-file postimages independently defined against "
            f"accepted C0004 code {BASE_SHA}. Sorted LF path-list SHA-256 {path_hash}. "
            "The request changes only reviewed consumers, declaration-free aggregates, "
            "test roots, and architecture manifests; relocated declarations remain worker-owned."
        ),
        "record_kind": "shared_file_request",
        "request_id": request_id,
        "requester_id": "primary-human",
        "resolution": {
            "checkpoint_id": None,
            "commit_sha": None,
            "reason": None,
            "resolved_at": None,
            "resolved_by": None,
            "validation_evidence": [],
        },
        "schema_version": 1,
        "status": "active",
        "superseded_by": None,
        "supersedes": None,
        "target_base_sha": BASE_SHA,
        "target_checkpoint_id": BASE_CHECKPOINT,
        "valid_through_checkpoint_id": BASE_CHECKPOINT,
        "wave_id": wave,
    }


def write_requests(
    selectors: dict[str, list[dict[str, str]]]
) -> dict[str, dict[str, bytes]]:
    expected_path_hashes = {
        "R0009": "8EF9434F099EBEC21EBF68BC7F90B70D8A089C6751760FAC15BEF0FB4EBB031C",
        "R0010": "27909095ED5B03AF1CDA0AB9CD7757A3D53A772F553B4C115611FA8ADD650384",
    }
    plans = {
        "R0009": ("R04", tuple(sorted(R0009_PATHS)), frozenset({"R04"})),
        "R0010": ("R08", tuple(sorted(R0010_PATHS)), frozenset({"R08"})),
    }
    if tuple(read_lines(BRANCHES / "B0009-shared-request-paths.txt")) != plans["R0010"][1]:
        raise GenerationError("R0010 path list drift from frozen R08 evidence")
    outputs: dict[str, dict[str, bytes]] = {}
    for request_id, (wave, paths, waves) in plans.items():
        if sha256_bytes(list_bytes(paths)) != expected_path_hashes[request_id]:
            raise GenerationError(f"{request_id}: path-list hash drift")
        postimages = request_postimages(waves, selectors)
        if tuple(sorted(postimages)) != paths:
            raise GenerationError(f"{request_id}: postimage path set drift")
        patch_path = REQUESTS / f"{request_id}.patch"
        write_bytes(patch_path, zero_context_patch(postimages))
        write_bytes(
            REQUESTS / f"{request_id}-postimages.tsv",
            postimage_ledger(postimages),
        )
        verify_patch_replay(patch_path, postimages)
        write_bytes(
            REQUESTS / f"{request_id}.json",
            canonical_json(shared_request_record(request_id, wave, paths, patch_path)),
        )
        outputs[request_id] = postimages

    overlap = tuple(sorted(set(R0009_PATHS) & set(R0010_PATHS)))
    union_paths = tuple(sorted(set(R0009_PATHS) | set(R0010_PATHS)))
    if overlap != REQUEST_INTERSECTION:
        raise GenerationError(f"request overlap drift: {overlap}")
    if sha256_bytes(list_bytes(overlap)) != (
        "D251C487ABEE9E25B128B92F63DC8A81B993C011FDDE6F1A57DCB66B09966BFC"
    ):
        raise GenerationError("request intersection path-list hash drift")
    casefold_overlap = {
        left.casefold()
        for left in R0009_PATHS
        for right in R0010_PATHS
        if left.casefold() == right.casefold()
    }
    if casefold_overlap != {path.casefold() for path in overlap}:
        raise GenerationError("request casefold overlap exceeds exact overlap")
    strict_ancestors = [
        (left, right)
        for left in R0009_PATHS
        for right in R0010_PATHS
        if left.casefold() != right.casefold()
        and (
            right.casefold().startswith(left.casefold().rstrip("/") + "/")
            or left.casefold().startswith(right.casefold().rstrip("/") + "/")
        )
    ]
    if strict_ancestors:
        raise GenerationError(f"request ancestor overlap: {strict_ancestors}")
    if len(union_paths) != 37:
        raise GenerationError(f"request union expected 37 paths, found {len(union_paths)}")
    if sha256_bytes(list_bytes(union_paths)) != (
        "6DB1CD2A1AAB1DAD67924B2FA0ECD5F3FA2B315AB18BED68F7A3559C2DF63B81"
    ):
        raise GenerationError("request union path-list hash drift")
    union_postimages = request_postimages(frozenset({"R04", "R08"}), selectors)
    if tuple(sorted(union_postimages)) != union_paths:
        raise GenerationError("union postimage path set drift")
    for path in set(R0009_PATHS) - set(R0010_PATHS):
        if union_postimages[path] != outputs["R0009"][path]:
            raise GenerationError(f"R0009-only union postimage drift: {path}")
    for path in set(R0010_PATHS) - set(R0009_PATHS):
        if union_postimages[path] != outputs["R0010"][path]:
            raise GenerationError(f"R0010-only union postimage drift: {path}")
    union_patch = REQUESTS / "R0009-R0010-union.patch"
    write_bytes(union_patch, zero_context_patch(union_postimages))
    union_ledger = REQUESTS / "R0009-R0010-union-postimages.tsv"
    write_bytes(union_ledger, postimage_ledger(union_postimages))
    verify_patch_replay(union_patch, union_postimages)
    review = f"""# R0009/R0010 shared-file union review

The primary-human reviewed both active shared-file requests independently against exact
C0004 code `{BASE_SHA}`. The integration postimage is a separate common-base union; it
is not the result of applying either whole-file request after the other.

- R0009 paths: 28; patch SHA-256 `{sha256_path(REQUESTS / 'R0009.patch')}`.
- R0010 paths: 14; patch SHA-256 `{sha256_path(REQUESTS / 'R0010.patch')}`.
- Exact/casefold intersection: 5; no non-equal ancestor relations.
- Sorted intersection SHA-256: `{sha256_bytes(list_bytes(overlap))}`.
- Sorted union: 37 paths; path-list SHA-256 `6DB1CD2A1AAB1DAD67924B2FA0ECD5F3FA2B315AB18BED68F7A3559C2DF63B81`.
- Union patch SHA-256: `{sha256_path(union_patch)}`.
- Union postimage ledger SHA-256: `{sha256_path(union_ledger)}`.
- Replay: `git apply --cached --check --unidiff-zero` and exact postimage verification pass
  from C0004; reverse replay reconstructs tree `{BASE_TREE}`.

The five shared postimages are `NumStability/Algorithms.lean`, `NumStabilityTest.lean`,
`docs/architecture/COMPATIBILITY.md`, `docs/architecture/layout-exceptions.json`, and
`docs/architecture/tiers.json`. No request writes a worker-owned selector path.
"""
    write_bytes(
        REQUESTS / "R0009-R0010-union-review.md",
        review.replace("\r\n", "\n").encode("utf-8"),
    )
    outputs["union"] = union_postimages
    return outputs


def write_destination_evidence() -> dict[str, tuple[str, ...]]:
    r04_modules = tuple(sorted(R04_DESTINATION_TIERS))
    r04_production_prefixes = tuple(R04_BRANCH_PREFIXES[:-2])
    r04_branch_prefixes = tuple(R04_BRANCH_PREFIXES)
    write_bytes(BRANCHES / "B0008-destination-modules.txt", list_bytes(r04_modules))
    write_bytes(
        BRANCHES / "B0008-destination-prefixes.txt",
        list_bytes(r04_production_prefixes),
    )
    write_bytes(
        BRANCHES / "B0008-branch-prefixes.txt", list_bytes(r04_branch_prefixes)
    )
    expected = {
        "B0008-destination-modules.txt": "E5BF22318D3CBFA2ECEC2A4FCA6EC56D26408DFBD25413D502A2EC2C9EDAEE38",
        "B0008-destination-prefixes.txt": "D8DE7708C1B1DC74F0E2CAC4478CDF81971371A23444EC4042473162B3628DD5",
        "B0008-branch-prefixes.txt": "0930457000DBEE61C629AFC0A6FBD8D31695FA6D2D4CEA83B9E1896EA4EC6B0A",
    }
    for name, digest in expected.items():
        if sha256_path(BRANCHES / name) != digest:
            raise GenerationError(f"{name} hash drift")

    r08_modules = tuple(read_lines(BRANCHES / "B0009-destination-modules.txt"))
    r08_production_prefixes = tuple(
        read_lines(BRANCHES / "B0009-destination-prefixes.txt")
    )
    r08_branch_prefixes = tuple(read_lines(BRANCHES / "B0009-branch-prefixes.txt"))
    if (len(r04_modules), len(r08_modules)) != (31, 21):
        raise GenerationError("destination-module count drift")
    if (len(r04_branch_prefixes), len(r08_branch_prefixes)) != (33, 23):
        raise GenerationError("branch-prefix count drift")

    tree_paths = git("ls-tree", "-r", "--name-only", BASE_SHA).decode().splitlines()
    for wave, prefixes in (
        ("R04", r04_branch_prefixes),
        ("R08", r08_branch_prefixes),
    ):
        folded = [prefix.casefold() for prefix in prefixes]
        if len(folded) != len(set(folded)):
            raise GenerationError(f"{wave}: duplicate casefold branch prefix")
        for index, left in enumerate(folded):
            for right in folded[index + 1 :]:
                if left.startswith(right) or right.startswith(left):
                    raise GenerationError(f"{wave}: ancestor branch-prefix collision")
        for prefix in folded:
            module_file = prefix.rstrip("/") + ".lean"
            occupants = [
                path
                for path in tree_paths
                if path.casefold() == module_file
                or path.casefold().startswith(prefix)
            ]
            if occupants:
                raise GenerationError(
                    f"{wave}: destination prefix occupied at C0004: {prefix}: {occupants[:3]}"
                )

    for left in r04_branch_prefixes:
        for right in r08_branch_prefixes:
            a, b = left.casefold(), right.casefold()
            if a == b or a.startswith(b) or b.startswith(a):
                raise GenerationError(f"R04/R08 branch-prefix overlap: {left} / {right}")
    for left in r04_modules:
        for right in r08_modules:
            a, b = left.casefold(), right.casefold()
            if a == b or a.startswith(b + ".") or b.startswith(a + "."):
                raise GenerationError(f"R04/R08 destination overlap: {left} / {right}")
    return {
        "R04_modules": r04_modules,
        "R08_modules": r08_modules,
        "R04_prefixes": r04_branch_prefixes,
        "R08_prefixes": r08_branch_prefixes,
    }


def write_projection_records(
    selectors: dict[str, list[dict[str, str]]],
    destinations: dict[str, tuple[str, ...]],
) -> None:
    facts = {
        "R04": (
            "P0008",
            "B0008",
            {"declarations": 289, "signature_edges": 990, "body_edges": 2239, "union_edges": 2293},
        ),
        "R08": (
            "P0009",
            "B0009",
            {"declarations": 211, "signature_edges": 1229, "body_edges": 2886, "union_edges": 2912},
        ),
    }
    for wave, (projection_id, _branch_id, counts) in facts.items():
        allowed = sorted(
            {row["module"] for row in selectors[wave]}
            | set(destinations[f"{wave}_modules"])
        )
        expected_allowed = 50 if wave == "R04" else 66
        if len(allowed) != expected_allowed:
            raise GenerationError(f"{projection_id}: allowed-module count drift")
        graph_path = PROJECTIONS / f"{projection_id}.tsv.gz"
        record = {
            "base_checkpoint_id": BASE_CHECKPOINT,
            "checker": {
                "arguments": [f"--allow-module={module}" for module in allowed],
                "artifact": artifact(PROJECTION_CHECKER),
            },
            "combined_baseline": artifact(BASELINE),
            "expected_counts": counts,
            "phase_id": PHASE_ID,
            "projection_graph": artifact(graph_path),
            "projection_id": projection_id,
            "record_kind": "baseline_projection",
            "schema_version": 1,
            "selector": {
                "artifact": artifact(SELECTORS / f"{wave}.tsv"),
                "kind": "module_path_tsv",
            },
            "status": "active",
            "superseded_by": None,
            "wave_id": wave,
        }
        write_bytes(PROJECTIONS / f"{projection_id}.json", canonical_json(record))


def write_pair_reviews(
    selectors: dict[str, list[dict[str, str]]],
    destinations: dict[str, tuple[str, ...]],
) -> dict[str, Path]:
    selection = REVIEWS / "C0004-R04-R08-selection.md"
    selection_text = f"""# C0004 R04/R08 successor-pair selection review

Primary-human review freezes R04 and R08 for planned-control construction against accepted
C0004 code `{BASE_SHA}` and graph `{GRAPH_SHA256}`. It does not activate either branch.

| Dimension | Result |
| --- | --- |
| exact owner overlap | 0 |
| strict owner ancestor overlap | 0 |
| direct selected-owner imports in either direction | 0 |
| transitive selected-owner reachability in either direction | 0 |
| typed-signature edges in either direction | 0 |
| proof/body edges in either direction | 0 |
| shared direct production consumers after excluding integrator-owned `NumStability.Algorithms` | 0 |
| casefold exact or ancestor overlap across all 56 branch prefixes | 0 |

R04 selects 19 owners and 289 declarations; R08 selects 45 owners and 211 declarations.
R04 has 31 production destinations and R08 has 21. Every destination prefix is casefold-vacant
in tree `{BASE_TREE}`, internally disjoint, and peer-disjoint. R0009 and R0010 contain 28 and
14 common-base shared paths, intersect on exactly five integrator-owned files, and form the
reviewed 37-path union with path-list SHA-256
`6DB1CD2A1AAB1DAD67924B2FA0ECD5F3FA2B315AB18BED68F7A3559C2DF63B81`.

R08's 222 frozen destination import rows are an implementation lower bound. Delivery may add
an import only to a frozen C0004 dependency or another B0009 destination, with updated DAG
evidence and proofs of no historical-wrapper edge, R04-destination edge, new SCC, or
reusable-to-source violation. Any semantic route or co-location change requires a reviewed
amendment. No Lean build runs during planned-control construction because the 21 destinations
do not yet exist; canonical, focused, consumer, old-path, and full builds are delivery gates.
"""
    write_bytes(selection, selection_text.encode("utf-8"))

    operator = REVIEWS / "R04-R08-operator-authorization.md"
    operator_text = """# R04/R08 temporary operator authorization

The primary-human retains ownership of the immutable `claude-lane` and temporarily adds
`codex-local` as a second lane operator solely for B0008/R04 planning stewardship, activated
worker execution, delivery reporting, and the immutable delivery ref. B0008 records both
`claude-local` and `codex-local`; B0009/R08 remains exclusively `claude-local`.

This authorization expires at C0005 acceptance or when B0008 becomes terminal, whichever
comes first. It grants no B0009, integration, shared-path, main-push, checkpoint acceptance,
or retirement authority. Those authorities remain with `primary-human`. No worker ref or
worktree may be created before the exact planned-control Lean CI is green, and no implementation
may begin before a later activation-control commit is green.
"""
    write_bytes(operator, operator_text.encode("utf-8"))

    replay = REVIEWS / "R04-R08-projection-replay.md"
    replay_text = f"""# R04/R08 C0004 projection replay

Both baseline projections are deterministic format-2 subsets of exact C0004. Freeze replay
uses the accepted graph as candidate and deliberately omits private normalization because the
baseline still contains the historical private names.

| Projection | declarations | signature edges | body edges | union pairs | gzip SHA-256 |
| --- | ---: | ---: | ---: | ---: | --- |
| P0008/R04 | 289 | 990 | 2,239 | 2,293 | `{sha256_path(PROJECTIONS / 'P0008.tsv.gz')}` |
| P0009/R08 | 211 | 1,229 | 2,886 | 2,912 | `{sha256_path(PROJECTIONS / 'P0009.tsv.gz')}` |

Delivery replay must add the total private map: B0008 has 115 rows (101 nonidentity and 14
identity), while B0009 has 48 nonidentity rows. The accepted projection checker is pinned at
`{PROJECTION_CHECKER_SHA256}`. No delivery candidate exists during planning.
"""
    write_bytes(replay, replay_text.encode("utf-8"))

    branch_reviews: dict[str, Path] = {}
    for wave, branch_id, peer in (("R04", "B0008", "R08"), ("R08", "B0009", "R04")):
        path = BRANCHES / f"{branch_id}-overlap-review.md"
        forbidden_count = 2747 if wave == "R04" else 2721
        text = f"""# {branch_id}/{wave} overlap review

Exact-C0004 selector membership is total: {len(selectors[wave])} owned paths, all and only the
inventory rows labeled `{wave}`. The forbidden exact set is the {forbidden_count}-path selector
complement of the 2,766-row C0004 inventory.
All {len(destinations[f'{wave}_prefixes'])} destination prefixes are C0004-vacant and mutually
non-ancestor. Against {peer}, owner overlap, import reachability, signature/body coupling,
convention-filtered shared consumers, and destination exact/ancestor overlap are all zero.

Shared files are excluded from worker ownership and reserved through the reviewed
R0009/R0010 common-base union. Status remains planned; no ref, worktree, or activation exists.
"""
        write_bytes(path, text.encode("utf-8"))
        branch_reviews[branch_id] = path
    return {
        "selection": selection,
        "operator": operator,
        "replay": replay,
        **branch_reviews,
    }


def write_branch_records(
    inventory: list[dict[str, str]],
    selectors: dict[str, list[dict[str, str]]],
    destinations: dict[str, tuple[str, ...]],
    reviews: dict[str, Path],
) -> None:
    facts = {
        "R04": {
            "branch_id": "B0008",
            "projection_id": "P0008",
            "request_id": "R0009",
            "branch_name": "codex/reorg-completion-2026-08-r04-cholesky-higham-ch10",
            "operators": ["claude-local", "codex-local"],
        },
        "R08": {
            "branch_id": "B0009",
            "projection_id": "P0009",
            "request_id": "R0010",
            "branch_name": "codex/reorg-completion-2026-08-r08-matrix-inversion-ch14",
            "operators": ["claude-local"],
        },
    }
    base_evidence = [
        BASELINE,
        BASELINE_SUMMARY,
        PHASE / "checkpoints/C0004-gates.md",
        INVENTORY,
        REQUESTS / "R0009-R0010-union.patch",
        REQUESTS / "R0009-R0010-union-postimages.tsv",
        REQUESTS / "R0009-R0010-union-review.md",
        reviews["selection"],
        reviews["operator"],
        reviews["replay"],
    ]
    for wave, fact in facts.items():
        branch_id = fact["branch_id"]
        projection_id = fact["projection_id"]
        request_id = fact["request_id"]
        selected_paths = {row["path"] for row in selectors[wave]}
        forbidden_exact = sorted(
            row["path"] for row in inventory if row["path"] not in selected_paths
        )
        expected_forbidden = 2747 if wave == "R04" else 2721
        if len(forbidden_exact) != expected_forbidden:
            raise GenerationError(f"{branch_id}: forbidden complement drift")
        owned = [
            {"match": "exact", "path": row["path"]} for row in selectors[wave]
        ]
        forbidden = [
            {"match": "exact", "path": path} for path in forbidden_exact
        ] + [
            {"match": "prefix", "path": path} for path in PROTECTED_PREFIXES
        ]
        branch_evidence = sorted(BRANCHES.glob(f"{branch_id}-*"), key=rel)
        evidence_paths = base_evidence + branch_evidence + [
            PROJECTIONS / f"{projection_id}.json",
            PROJECTIONS / f"{projection_id}.tsv.gz",
            REQUESTS / f"{request_id}.json",
            REQUESTS / f"{request_id}.patch",
            REQUESTS / f"{request_id}-postimages.tsv",
            SELECTORS / f"{wave}.tsv",
        ]
        unique_evidence: dict[str, Path] = {rel(path): path for path in evidence_paths}
        record = {
            "base_checkpoint_id": BASE_CHECKPOINT,
            "base_sha": BASE_SHA,
            "baseline_projection_id": projection_id,
            "branch_id": branch_id,
            "branch_name": fact["branch_name"],
            "delivery": {
                "commit_sha": None,
                "report": None,
                "scope_evidence": None,
            },
            "destination_prefixes": [
                {"match": "prefix", "path": path}
                for path in destinations[f"{wave}_prefixes"]
            ],
            "forbidden_paths": forbidden,
            "integration": {
                "accepted_checkpoint_id": None,
                "accepted_sha": None,
                "method": None,
            },
            "lane_id": "claude-lane",
            "operator_ids": fact["operators"],
            "owned_paths": owned,
            "owner_id": "primary-human",
            "phase_id": PHASE_ID,
            "record_kind": "phase_branch",
            "refresh": {
                "decision": "current",
                "evidence": [
                    artifact(path) for _, path in sorted(unique_evidence.items())
                ],
                "reviewed_checkpoint_id": BASE_CHECKPOINT,
            },
            "retirement": {
                "ancestry_checkpoint_id": None,
                "remote_ref": f"refs/heads/{fact['branch_name']}",
                "retired_at": None,
                "retired_by": None,
                "rule": "delivery_ancestor_of_green_checkpoint",
                "status": "not_due",
            },
            "schema_version": 1,
            "shared_request_ids": [request_id],
            "status": "planned",
            "wave_id": wave,
        }
        write_bytes(BRANCHES / f"{branch_id}.json", canonical_json(record))


def write_planned_phase() -> None:
    phase_path = PHASE / "phase.json"
    phase_relative = rel(phase_path)
    document = json.loads(git_file_at(CONTROL_HEAD, phase_relative))
    if document["current_checkpoint_id"] != BASE_CHECKPOINT:
        raise GenerationError("planned phase must remain at C0004")
    claude_lanes = [
        lane for lane in document["authority"]["lanes"] if lane["lane_id"] == "claude-lane"
    ]
    if len(claude_lanes) != 1 or claude_lanes[0]["operator_ids"] != ["claude-local"]:
        raise GenerationError("accepted C0004 claude-lane authority drift")
    claude_lanes[0]["operator_ids"] = ["claude-local", "codex-local"]

    existing_exact = {
        row["path"] for row in document["shared_paths"] if row["match"] == "exact"
    }
    existing_prefix = [
        row["path"] for row in document["shared_paths"] if row["match"] == "prefix"
    ]
    union_paths = set(R0009_PATHS) | set(R0010_PATHS)
    additions = union_paths - existing_exact
    if len(additions) != 32:
        raise GenerationError(f"expected 32 new shared exact reservations, found {len(additions)}")
    exact = sorted(existing_exact | union_paths)
    if len(exact) != 187 or len(existing_prefix) != 5:
        raise GenerationError("planned shared-path cardinality drift")
    document["shared_paths"] = [
        {"match": "exact", "path": path} for path in exact
    ] + [
        {"match": "prefix", "path": path} for path in existing_prefix
    ]
    if len(document["shared_paths"]) != 192:
        raise GenerationError("planned phase expected 192 shared path rules")
    for milestone in document["milestones"]:
        if milestone["milestone_id"] in {"M04", "M08"} and milestone["status"] != "ready":
            raise GenerationError("M04/M08 must remain ready during planning")
    write_bytes(phase_path, pretty_json(document))


def main() -> int:
    verify_inputs()
    copy_freeze_evidence()
    inventory = inventory_rows()
    declarations, edges = parse_graph()
    selectors: dict[str, list[dict[str, str]]] = {}
    for wave, projection_id in (("R04", "P0008"), ("R08", "P0009")):
        selector = wave_selector(inventory, wave)
        selectors[wave] = selector
        selector_path = SELECTORS / f"{wave}.tsv"
        write_bytes(
            selector_path,
            tsv_bytes(("module", "path"), ((row["module"], row["path"]) for row in selector)),
        )
        route_rows, routed = build_routes(wave, selector, declarations)
        branch_id = "B0008" if wave == "R04" else "B0009"
        write_branch_sidecars(wave, branch_id, selector, route_rows)
        write_bytes(
            BRANCHES / f"{branch_id}-declaration-routes.tsv",
            tsv_bytes(
                (
                    "baseline_owner_module",
                    "baseline_declaration_name",
                    "visibility",
                    "kind",
                    "baseline_order",
                    "destination_module",
                    "route_class",
                    "normalization_decision",
                ),
                route_rows,
            ),
        )
        private_rows = build_private_map(route_rows)
        write_bytes(
            BRANCHES / f"{branch_id}-private-normalization.tsv",
            tsv_bytes(("old_private", "new_private", "destination_module"), private_rows),
        )
        closure_rows = build_private_closure(
            route_rows, declarations, edges, {row["module"] for row in selector}
        )
        write_bytes(
            BRANCHES / f"{branch_id}-private-closure.tsv",
            tsv_bytes(
                ("declaration", "owner_module", "visibility", "selected_owner", "closure_role"),
                closure_rows,
            ),
        )
        dag_rows = route_dag(routed, edges)
        write_bytes(
            BRANCHES / f"{branch_id}-destination-dag.tsv",
            tsv_bytes(
                ("from_destination", "to_destination", "signature_edges", "body_edges"),
                dag_rows,
            ),
        )
        projection_path, counts, payload_sha = build_projection(
            projection_id, selector, declarations, edges
        )
        print(
            f"{wave}: selector={sha256_path(selector_path)} routes={sha256_path(BRANCHES / f'{branch_id}-declaration-routes.tsv')} "
            f"private={sha256_path(BRANCHES / f'{branch_id}-private-normalization.tsv')} "
            f"closure_rows={len(closure_rows)} dag_rows={len(dag_rows)} "
            f"projection={sha256_path(projection_path)} payload={payload_sha} counts={counts}"
        )
    destinations = write_destination_evidence()
    write_projection_records(selectors, destinations)
    requests = write_requests(selectors)
    reviews = write_pair_reviews(selectors, destinations)
    write_branch_records(inventory, selectors, destinations, reviews)
    write_planned_phase()
    print(
        "requests: "
        f"R0009={sha256_path(REQUESTS / 'R0009.patch')} "
        f"R0010={sha256_path(REQUESTS / 'R0010.patch')} "
        f"union={sha256_path(REQUESTS / 'R0009-R0010-union.patch')} "
        f"union_paths={len(requests['union'])}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
