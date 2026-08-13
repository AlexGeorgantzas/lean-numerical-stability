#!/usr/bin/env python3
"""Validate the C0008-rooted repository-reorganization completion phase.

This checker is deliberately independent of ``check_phase.py``.  The generic
phase checker validates the reusable phase schema; this file enforces the
one-off, exact activation-to-C0001 contract, its C0001-rooted successor
controls, and C0002 acceptance/retirement.  It uses only the Python standard
library and disposable Git indexes rooted at the applicable checkpoint to
materialize and hash-check independent requests and their reviewed-union
postimages.
"""

from __future__ import annotations

import argparse
import csv
import gzip
import hashlib
import io
import json
import os
import re
import subprocess
import sys
import tempfile
from collections import Counter, defaultdict
from dataclasses import dataclass, replace
from pathlib import Path, PurePosixPath
from typing import Any, Iterable, Iterator, Sequence


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_PHASE_DIR = Path(
    "docs/architecture/phases/2026-08-repository-reorganization-completion"
)
PREDECESSOR_DIR = Path(
    "docs/architecture/phases/2026-08-repository-reorganization"
)
ACTIVE_POINTER = Path("docs/architecture/phases/active-phase.json")

PHASE_ID = "repository-reorganization-completion-2026-08"
PREDECESSOR_PHASE_ID = "repository-reorganization-2026-08"
CODE_SHA = "b1b18772d80185ec08f49c818919558645c330a1"
INTEGRATED_CODE_SHA = "117aa2bb7e61f41e1531a78452f9f7f6cd5b0771"
R01_MERGE_SHA = "b5966cdc88d136936e6566010cd4113b81f20711"
R02_MERGE_SHA = "52632d28f0c78438d883bde337700f330895159a"
R01_MERGE_PARENTS = (
    "f98f0c8598b7834cb9a80567bc57053e9befa66a",
    "0bdf03a383377c8c6da89d85393e56fca8c00ccd",
)
R02_MERGE_PARENTS = (
    R01_MERGE_SHA,
    "f790c8413412177bb74f47fee74bb12c48c11155",
)
BUILD_LOCK = "lean-reorganization-2026-08"
CHECKPOINT_ID = "C0000"
SUCCESSOR_CHECKPOINT_ID = "C0001"
C0002_CHECKPOINT_ID = "C0002"
C0002_CODE_SHA = "9d2334d77f1a38f8a4caa81fe53eeb11a8e3e7cd"
R11_MERGE_SHA = "10169717ce4966e9963885b04e7b7733a3bc7730"
R12_MERGE_SHA = "1495047a1befb1431f0501cf7a423c8e77f8661a"
R11_MERGE_PARENTS = (
    "de0ea2a54ea53d0e3724a72135d6da7d22739226",
    "444a03259af510bdfe0921d1847b6add1b26ed73",
)
R12_MERGE_PARENTS = (
    R11_MERGE_SHA,
    "0726678a0f2db56e533f3b956a2f7f1531059d7d",
)
MATRIX_ALGEBRA = "NumStability/Analysis/MatrixAlgebra.lean"

SUCCESSOR_METRICS = {
    "production_modules": 2631,
    "unclassified_modules": 277,
    "mixed_modules": 9,
    "missing_module_docstrings": 72,
    "noncanonical_modules": 244,
    "declaration_bearing_umbrellas": 21,
    "unsorted_aggregate_imports": 0,
}
SUCCESSOR_MILESTONES = ["M01", "M02"]
SUCCESSOR_GATE_IDS = {
    "architecture",
    "canonical_import",
    "combined_baseline",
    "compatibility",
    "focused_build",
    "full_build",
    "full_tests",
    "layout",
    "old_import",
    "provenance",
    "scope",
    "strict_source",
}
C0002_METRICS = {
    "production_modules": 2642,
    "unclassified_modules": 277,
    "mixed_modules": 9,
    "missing_module_docstrings": 13,
    "noncanonical_modules": 241,
    "declaration_bearing_umbrellas": 16,
    "unsorted_aggregate_imports": 0,
}
C0002_MILESTONES = ["M01", "M02", "M11", "M12"]
C0002_COMBINED_BASELINE_SHA256 = (
    "0A062C8EB887E34907BF15F9423EDA6E7FB3DD032495B6DE98A7ED8538A32485"
)
C0002_COMBINED_SUMMARY_SHA256 = (
    "0866C152BD9162719EBC3343A7B1B76BB8B6FBB647DCF5B3389BD7E18F6EC705"
)
C0002_INVENTORY_SHA256 = (
    "BB5AE8029CC3DC547BA1E4C8B581BA11948E527810AC29F0EBE8E1CC5D81BF02"
)
C0002_INTEGRATOR_LEDGER_SHA256 = (
    "004B3B305708CB4C9098C931938F9C0385181B81FD22387632E347D667896A3A"
)
C0002_GATES_SHA256 = (
    "4C5368D6CA295DD885B77CD6CC79A2519FFEE6926A5A0D21F968DA8F41C07361"
)
C0002_RELEASED_SHARED_PATHS = frozenset(
    {
        "NumStability/Algorithms/LinearSystems/LeastSquares/Equality/Basic.lean",
        "NumStability/Algorithms/LinearSystems/Underdetermined/QR/Givens/StoredReplay/Closure.lean",
        "NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/ForwardError/ActualOutput.lean",
        "NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/HouseholderClosure/Closure.lean",
        "NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/HouseholderClosure/Uniform.lean",
        "NumStability/Analysis/Perturbation/LeastSquares/BackwardError.lean",
        "NumStability/Analysis/Perturbation/LeastSquares/Basic.lean",
        "NumStability/Analysis/Perturbation/LeastSquares/Equality/RowwiseBackwardError.lean",
        "NumStability/Source/Higham/Chapter20/Theorem03/QRSolve.lean",
        "NumStability/Source/Higham/Chapter20/Theorem07.lean",
        "NumStability/Algorithms/TestMatrices/Higham28Stewart.lean",
    }
)
R03_RERESERVED_C0002_PATHS = frozenset(
    {
        "NumStability/Algorithms/LinearSystems/Underdetermined/QR/Givens/StoredReplay/Closure.lean",
        "NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/ForwardError/ActualOutput.lean",
        "NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/HouseholderClosure/Closure.lean",
        "NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/HouseholderClosure/Uniform.lean",
    }
)
REQUEST_RESOLUTION_EVIDENCE = {
    "R0001": (
        "docs/architecture/phases/2026-08-repository-reorganization-completion/"
        "requests/R0001-R0002-union-review.md",
        "620CFDEFA27F49655D0F399A56461DD60B7D8BCB2169BF1E2C84B515A46F7DF5",
    ),
    "R0002": (
        "docs/architecture/phases/2026-08-repository-reorganization-completion/"
        "requests/R0001-R0002-union-review.md",
        "620CFDEFA27F49655D0F399A56461DD60B7D8BCB2169BF1E2C84B515A46F7DF5",
    ),
    "R0002T": (
        "docs/architecture/phases/2026-08-repository-reorganization-completion/"
        "reviews/R01-R0002T-test-root-union.md",
        "B223E12C8B9571A41488F6ED0A3A180B2AA91C3870774081CE66073B7EBEB487",
    ),
}

SCOPE_HEADER = (
    "module",
    "path",
    "base_blob_oid",
    "current_tier",
    "debt_flags",
    "phase_scope",
    "lane_id",
    "wave_id",
    "planned_actions",
    "rationale",
)
SELECTOR_HEADER = ("module", "path")
DELIVERY_SCOPE_HEADER = ("status", "path")
SHA1_RE = re.compile(r"^[0-9a-f]{40}$")
SHA256_RE = re.compile(r"^[0-9A-Fa-f]{64}$")
RFC3339_RE = re.compile(
    r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?(?:Z|[+-]\d{2}:\d{2})$"
)
IMPORT_RE = re.compile(
    r"(?m)^[ \t]*(?:(?:public|private|meta)\s+)*import[ \t]+([A-Za-z0-9_'.]+)"
)
DEFERRED_RE = re.compile(
    r"\b(?:tbd|todo|pending|unreviewed|undecided|worker decides|decide later|later)\b",
    re.IGNORECASE,
)
GENERATED_PARTS = frozenset({".lake", "__pycache__", ".DS_Store"})
GENERATED_SUFFIXES = frozenset(
    {".olean", ".ilean", ".pyc", ".pyo", ".aux", ".log", ".out"}
)
GENERATED_PREFIXES = ("benchmark-results/",)


R01_PATHS = frozenset(
    """NumStability/Algorithms/StationaryIteration.lean
NumStability/Algorithms/StationaryIterationDrazin.lean
NumStability/Algorithms/StationaryIterationRounded.lean
NumStability/Algorithms/StationaryIterationSemiconvergent.lean
NumStability/Algorithms/StationaryIterationSemiconvergentExistence.lean
NumStability/Analysis/SemiconvergentBlockFormExists.lean
NumStability/Analysis/SemiconvergentExistenceComplete.lean
NumStability/Analysis/SemiconvergentExistenceFull.lean
NumStability/Analysis/SemiconvergentLimitGeneral.lean
NumStability/Analysis/SemiconvergentRealSpectrumComplete.lean
NumStability/Source/Higham/Chapter17/Equation08.lean
NumStability/Source/Higham/Chapter17/Equation12.lean
NumStability/Source/Higham/Chapter17/Equation15.lean
NumStability/Source/Higham/Chapter17/Equation16.lean
NumStability/Source/Higham/Chapter17/Equation17.lean
NumStability/Source/Higham/Chapter17/Equation20.lean""".splitlines()
)

R02_PATHS = frozenset(
    """NumStability/Algorithms/Ch15CondEstimators.lean
NumStability/Algorithms/Ch15DixonClosure.lean
NumStability/Algorithms/Ch15DixonProbability.lean
NumStability/Algorithms/Chapter15CondEst.lean
NumStability/Algorithms/HighamChapter15BoydBridges.lean
NumStability/Algorithms/HighamChapter15BoydConcreteLemma3.lean
NumStability/Algorithms/HighamChapter15BoydLocalStability.lean
NumStability/Algorithms/HighamChapter15BoydRowwiseDomain.lean
NumStability/Algorithms/HighamChapter15BoydScalar.lean
NumStability/Algorithms/HighamChapter15BoydSourceClosure.lean
NumStability/Algorithms/HighamChapter15BoydSourceDomain.lean
NumStability/Algorithms/HighamChapter15BoydSourceLocal.lean
NumStability/Algorithms/HighamChapter15BoydSourceSecondDerivative.lean
NumStability/Algorithms/HighamChapter15BoydUniqueness.lean
NumStability/Algorithms/HighamChapter15ConvergenceProse.lean
NumStability/Algorithms/HighamChapter15RectTermination.lean
NumStability/Algorithms/LU/Higham15Problem15_4.lean
NumStability/Algorithms/LU/Higham15Problem15_6.lean
NumStability/Algorithms/LU/Higham15Problem15_6Closure.lean
NumStability/Algorithms/LU/Higham15Problem15_6Operational.lean
NumStability/Algorithms/LU/TridiagonalCondCh15.lean
NumStability/Algorithms/LU/TridiagonalCondCh15Closure.lean
NumStability/Algorithms/LU/TridiagonalCondCh15IkebeClosure.lean
NumStability/Algorithms/NormEstimation/PNorm/Endpoints/ConvergenceStatements.lean
NumStability/Algorithms/NormEstimation/PNorm/Endpoints/PNormRectangular.lean
NumStability/Algorithms/PNormPowerMethod.lean
NumStability/Algorithms/PNormPowerMethodGeneralP.lean
NumStability/Algorithms/PNormPowerMethodRect.lean""".splitlines()
)

R01_DESTINATIONS = frozenset(
    {
        "NumStability/Algorithms/LinearSystems/Iterative/Stationary/Semiconvergence",
        "NumStability/Analysis/LinearOperators/MatrixPowers/Semiconvergence",
        "NumStability/Source/Higham/Chapter17/Results",
        "NumStabilityTest/Reorganization/R01",
        "docs/architecture/deliveries/R01",
    }
)

R01_CONSUMERS = frozenset(
    {
        "NumStability/Algorithms.lean",
        "NumStability/Analysis.lean",
        "NumStability/Algorithms/StationaryIterationSeries.lean",
        "NumStability/Source/Higham/Chapter17.lean",
        "NumStability/Source/Higham/Chapter17/Equation22.lean",
    }
)
R02_CONSUMERS = frozenset(
    {
        "NumStability/Algorithms.lean",
        "NumStability/Algorithms/NormEstimation/PNorm/All.lean",
        "NumStability/Algorithms/NormEstimation/PNorm/Rectangular/RectangularTermination.lean",
        "NumStability/Source/Higham/Chapter15/Lemma02/PNormPowerMethod/PNormRectangular.lean",
        "NumStability/Source/Higham/Chapter15/Section02/Boyd/EndpointTermination/ConvergenceStatements.lean",
        "NumStability/Source/Higham/Chapter15/Section02/Boyd/EndpointTermination/RectangularTermination.lean",
    }
)
SHARED_CONSUMERS = frozenset(
    R01_CONSUMERS
    | R02_CONSUMERS
    | {"NumStability/Source/Higham/Chapter15.lean"}
)
R0002T_PATHS = frozenset(
    {"NumStabilityTest.lean", "NumStabilityTest/Reorganization/R02.lean"}
)

NEXT_COMBINED_BASELINE_SHA256 = (
    "F6AD7BC1267CB73968D8933D1126DCE30AD2748E1B2EFD611C3D6509872243F2"
)
NEXT_INVENTORY_SHA256 = (
    "E07B4BA74EE62737B8B2AB8DDF8FA9E43C8614DFFDC26C5E69535A4E38F1F57F"
)
NEXT_PROJECTION_CHECKER_SHA256 = (
    "0F32935ED1EFDD2BD4D6A4C346F3E8300C86DB1D4A3551A17165479226109220"
)
NEXT_CANDIDATE_SHA256 = (
    "55E0D29D626D746CB165DD7C874DA11A96B72602A66C1A6D8173F986178536C4"
)
NEXT_PROJECTION_REPLAY_SHA256 = (
    "F2EC6803CB0CD81953B15E05574122E7276737F0651C347041E6687F33212A60"
)
NEXT_OPERATOR_AUTHORIZATION_SHA256 = (
    "E6CBEFC8E640603A8FB176268301A34727D777120B3ED3386517403A4A8DCB5D"
)
NEXT_OVERLAP_FACTS_SHA256 = (
    "3BC917D2E25E2CB795C4C4094F06DD2A72F2DA0030F5DFCECA4BB8BA31A0E412"
)
NEXT_IMPORT_REVIEW_SHA256 = (
    "7EE5623EB236248C96A8C65A3A4601A6819495A40B3F067BC9A6639836D38611"
)
NEXT_UNION_PATCH_SHA256 = (
    "A6AB1307D19CBF2BEDDA37EAC8C68FFB405292B405E068908E6E4F15406A3E3B"
)
NEXT_UNION_POSTIMAGES_SHA256 = (
    "7279EDF6AF7277C2A4DD45286AEE97878EBFD025A89B240A6A644EE6FB665701"
)
NEXT_UNION_REVIEW_SHA256 = (
    "5B43D44B16496CAEACB14DE98FB4472B1698E18C3708B3BCD058C64C119F59DB"
)
NEXT_PROTECTED_PREFIXES = frozenset(
    {
        ".github",
        "NumStabilityTest/Import",
        "NumStabilityTest/Worker",
        "benchmark-results",
        "docs/architecture/phases",
        "tools/architecture",
    }
)
NEXT_REQUEST_OVERLAP = frozenset(
    {
        "NumStabilityTest.lean",
        "docs/architecture/layout-exceptions.json",
        "docs/architecture/tiers.json",
    }
)

# The successor to the completed C0001-rooted R11/R12 pair is deliberately a
# separate, singleton epoch.  Do not fold these facts into NEXT_BRANCH_FACTS:
# those constants are immutable evidence for the already accepted C0002
# checkpoint, while this packet is the independent planned/active R03 state.
R03_BRANCH_ID = "B0005"
R03_PROJECTION_ID = "P0005"
R03_REQUEST_ID = "R0005"
R03_WAVE_ID = "R03"
R03_LANE_ID = "codex-lane"
R03_OPERATOR_ID = "codex-local"
R03_BRANCH_NAME = (
    "codex/reorg-completion-2026-08-r03-floating-point-foundations-ch01-ch12"
)
R03_REMOTE_REF = f"refs/heads/{R03_BRANCH_NAME}"
R03_PLANNED_WORKTREE = (
    r"C:\Users\qed_s\higham-worktrees\completion-r03-codex"
)
R03_PLANNED_CONTROL_SHA = "fb5a021b4640dd595a99f7560ce252ad9836a5b6"
R03_PLANNED_CONTROL_CI_RUN = "31691727184"
R03_PLANNED_CONTROL_CI_JOB = "94420320315"
R03_SELECTOR_SHA256 = (
    "176BC214ABAE4B9CC2E9822E3177033213C4BD730D0057FBE8BAB524412C6B3A"
)
R03_PROJECTION_SHA256 = (
    "9D221D2DF34D79D67799F2F4F3ED16D74365A7EEBBDB372700EF574242F16D53"
)
R03_PROJECTION_PAYLOAD_SHA256 = (
    "7AAB876C821A25ABAD19346BCE35188CF28D1A31C20AF0C931CA1B3AC9892733"
)
R03_CANDIDATE_SHA256 = (
    "E03DB7A24886AD0B45C7371FE30ACE3AD135B3C4CC9866D65186753CD14FAD4C"
)
R03_PRIVATE_CLOSURE_SHA256 = (
    "59B218703D4EEAAC056773C3C91F0506089962ADB7BEB09E0B55D847E65647A3"
)
R03_COUNTS = {
    "declarations": 2389,
    "signature_edges": 28180,
    "body_edges": 42404,
    "union_edges": 43943,
}
R03_OWNER_COUNT = 47
R03_FORBIDDEN_EXACT_COUNT = C0002_METRICS["production_modules"] - R03_OWNER_COUNT
R03_PRIVATE_COUNT = 398
R03_PRIVATE_CLOSURE_ROWS = 2502
R03_PRIVATE_REVERSE_DEPENDENTS = 2104
R03_PRIVATE_SELECTED_OWNER_ROWS = 2063
R03_DEBT_COUNTS = {
    "unclassified_modules": 23,
    "mixed_modules": 9,
    "missing_module_docstrings": 13,
    "noncanonical_modules": 24,
    "declaration_bearing_umbrellas": 2,
}
R03_R07_OVERLAP_COUNTS = {
    "r03_to_r07_transitive_owner_pairs": 24,
    "r07_to_r03_transitive_owner_pairs": 23,
    "common_direct_project_dependencies": 7,
    "shared_outside_consumers": 5,
}
R03_PROTECTED_PREFIXES = NEXT_PROTECTED_PREFIXES
R03_TEST_CLASSES = frozenset(
    {
        "aggregate_entrypoint",
        "canonical_only",
        "focused",
        "old_only",
        "protected_consumer",
    }
)
R03_DECLARATION_ROUTE_HEADER = (
    "baseline_owner_module",
    "baseline_declaration_name",
    "visibility",
    "kind",
    "baseline_order",
    "destination_module",
    "route_class",
    "normalization_decision",
)
R03_MODULE_ROUTE_HEADER = (
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
)
R03_PRIVATE_HEADER = ("old_private", "new_private", "destination_module")
R03_PRIVATE_CLOSURE_HEADER = (
    "declaration",
    "owner_module",
    "visibility",
    "selected_owner",
    "closure_role",
)
R03_TEST_HEADER = ("test_class", "target", "purpose")

R03_PHASE_PREFIX = (
    "docs/architecture/phases/2026-08-repository-reorganization-completion"
)
R03_ACTIVATION_REVIEW_PATH = f"{R03_PHASE_PREFIX}/reviews/R03-activation.md"
R03_ACTIVATION_REVIEW_SHA256 = (
    "752B79BC9BBB2B492FA50DD43EC7E108DEF60D24D72B4F602CF2055B29189DB2"
)
R03_EVIDENCE_PATHS = {
    "baseline": f"{R03_PHASE_PREFIX}/baselines/C0002-combined.json",
    "baseline_summary": f"{R03_PHASE_PREFIX}/baselines/C0002-combined.md",
    "inventory": f"{R03_PHASE_PREFIX}/checkpoints/C0002-inventory.tsv",
    "gates": f"{R03_PHASE_PREFIX}/checkpoints/C0002-gates.md",
    "declaration_routes": f"{R03_PHASE_PREFIX}/branches/B0005-declaration-routes.tsv",
    "module_routes": f"{R03_PHASE_PREFIX}/branches/B0005-module-routes.tsv",
    "private_map": f"{R03_PHASE_PREFIX}/branches/B0005-private-normalization.tsv",
    "private_closure": f"{R03_PHASE_PREFIX}/branches/B0005-private-closure.tsv",
    "test_plan": f"{R03_PHASE_PREFIX}/branches/B0005-test-plan.tsv",
    "consumers": f"{R03_PHASE_PREFIX}/branches/B0005-consumers.tsv",
    "overlap_review": f"{R03_PHASE_PREFIX}/branches/B0005-overlap-review.md",
    "projection_record": f"{R03_PHASE_PREFIX}/projections/P0005.json",
    "projection_graph": f"{R03_PHASE_PREFIX}/projections/P0005.tsv.gz",
    "request_record": f"{R03_PHASE_PREFIX}/requests/R0005.json",
    "request_patch": f"{R03_PHASE_PREFIX}/requests/R0005.patch",
    "request_postimages": f"{R03_PHASE_PREFIX}/requests/R0005-postimages.tsv",
    "request_replacements": f"{R03_PHASE_PREFIX}/requests/R0005-replacements.tsv",
    "selection_review": f"{R03_PHASE_PREFIX}/reviews/C0002-R03-selection.md",
    "route_review": f"{R03_PHASE_PREFIX}/reviews/R03-route-review.md",
    "projection_replay": f"{R03_PHASE_PREFIX}/reviews/R03-projection-replay.md",
    "selector": f"{R03_PHASE_PREFIX}/selectors/R03.tsv",
}

# PENDING_R03_SHA256: replace every None with the reviewed artifact digest in
# the planning commit.  The runtime validator treats a None as a hard failure;
# placeholders can never silently weaken the ratchet.
R03_ARTIFACT_SHA256: dict[str, str | None] = {
    "baseline": C0002_COMBINED_BASELINE_SHA256,
    "baseline_summary": C0002_COMBINED_SUMMARY_SHA256,
    "inventory": C0002_INVENTORY_SHA256,
    "gates": C0002_GATES_SHA256,
    "declaration_routes": "85B286E4D78B19814A68EDABA70A648EA3E2C394577E0CCBF4670FD0DD93C5D9",
    "module_routes": "D430CD1D62D599F0DEF9F2E260D9B389048B5A7289189DACC7834DDD0B233972",
    "private_map": "EB2729C65CCAFF1ED4FE6712C3373A78570088D2BCC07FB18DE72B7033721146",
    "private_closure": R03_PRIVATE_CLOSURE_SHA256,
    "test_plan": "C319C48A3643BA0476A1F842A8B21C3C6C4D71CA9E3778CC12503DAE4AE3D4AB",
    "consumers": "3AFD072408026219BDB07D1004E3768B27576AEB88AFBC8312FA9D9467155400",
    "overlap_review": "EC3ADA8E009CCD9E0C8849F73FB8F248EED9FEB1C31A4B33D2C41A74A047CA67",
    "projection_record": "43F3343E1D8BDEFF81682FBFD068958D952D334EE3204E65A6923BAACE1617DB",
    "projection_graph": R03_PROJECTION_SHA256,
    "request_record": "166864879AE95E091E8B945585BED92571CDAFD257E882E0A51D7F13DFB68567",
    "request_patch": "7B560710C0D8206B18EC18CA92E94A949639CDE60E7351B8E8198077389A7C7F",
    "request_postimages": "01AED0CF9F56EDC490E2FB35ADFDCAF5B55AD23AE2FA04D507FBE82973CF0BA3",
    "request_replacements": "94F809C455D30DE3A757739AC4258DC3C21A9B7AB41732724B64F2FDB11EFFC8",
    "selection_review": "C78A5AB0BB71B6FE97B41D363DDE44F74253F3EE6DE8C8782C309D47BD17A167",
    "route_review": "A90899E79B900B5C4047D2489A9F4BE5327BECA6E943141A72B4AF58C6CBACF9",
    "projection_replay": "D2399C417DE20AB7187F948DE394CFCD3EE7F74ADEE80AFE6F1D05C19EA7BEF8",
    "selector": R03_SELECTOR_SHA256,
}

# PENDING_R03_DESTINATIONS/PENDING_R03_REQUEST: filled from the reviewed route
# and shared-request packets.  As above, None is rejected at runtime.
R03_DESTINATIONS: frozenset[str] | None = frozenset(
    {
        "NumStability/Algorithms/LinearSystems/LU/Doolittle/Assembly",
        "NumStability/Algorithms/PolynomialEvaluation/DerivativeEvaluation",
        "NumStability/Analysis/Approximation/SineTaylor/OddDegreeFiveError",
        "NumStability/Analysis/FloatingPointArithmetic/IeeeSpecialValueOperations",
        "NumStability/Analysis/Statistics/SampleVariance/RoundingErrorBounds",
        "NumStability/Source/Higham/Chapter01/Problem10/TwoPassSampleVariance/RemainderBound",
        "NumStability/Source/Higham/Chapter01/Section09/SampleVariance/IeeeSingleOnePassCounterexample",
        "NumStability/Source/Higham/Chapter01/Section12/InstabilityWithoutCancellation",
        "NumStability/Source/Higham/Chapter01/Section13/IncreasingPrecision",
        "NumStability/Source/Higham/Chapter01/Section14/CancellationOfRoundingErrors",
        "NumStability/Source/Higham/Chapter02/Problem03/AdjacentPrecisionValues/Results",
        "NumStability/Source/Higham/Chapter02/Problem09/DoubleRounding/Counterexample",
        "NumStability/Source/Higham/Chapter02/Problem10/DivisionRoundTrip/ExhaustiveBinary64",
        "NumStability/Source/Higham/Chapter02/Problem12/ReciprocalProduct/Results",
        "NumStability/Source/Higham/Chapter02/Problem13/ReciprocalProductThreshold/Results",
        "NumStability/Source/Higham/Chapter02/Problem14/UnitRoundoffProbe/IeeeExamples",
        "NumStability/Source/Higham/Chapter02/Problem21/HypotenuseNormalization/StandardModelCounterexample",
        "NumStability/Source/Higham/Chapter02/Problem25/NonzeroEvaluation/IeeeFiniteSystems",
        "NumStability/Source/Higham/Chapter02/Problem28/IterativeDivisionTermination/UnderflowAwareConvergence",
        "NumStability/Source/Higham/Chapter02/Section06/Discriminant/FusedMultiplyAdd/Counterexample",
        "NumStability/Source/Higham/Chapter02/Section06/Discriminant/StandardModel/Counterexample",
        "NumStability/Source/Higham/Chapter02/Section10/ArctangentRange/Counterexample",
        "NumStability/Source/Higham/Chapter02/Section10/Tablemaker/FiniteSeparation/Results",
        "NumStability/Source/Higham/Chapter02/Section11/AccuracyTests/CodySineResults",
        "NumStability/Source/Higham/Chapter03/Problem11/KahanAbsoluteValue/IeeeDoubleTrace",
        "NumStability/Source/Higham/Chapter04/Problem02/WilkinsonAttainability/IeeeDoubleTrace",
        "NumStability/Source/Higham/Chapter05/Algorithm01/ComplexHorner/ErrorBounds",
        "NumStability/Source/Higham/Chapter05/Section02/BidiagonalDerivativeAnalysis/Results",
        "NumStability/Source/Higham/Chapter05/Section02/DerivativeError/Results",
        "NumStability/Source/Higham/Chapter05/Section04/PatersonStockmeyer/Results",
        "NumStability/Source/Higham/Chapter05/Section05/FastPolynomialEvaluation/Results",
        "NumStability/Source/Higham/Chapter07/Equation17",
        "NumStability/Source/Higham/Chapter07/Equation26/DistanceToSingularity",
        "NumStability/Source/Higham/Chapter07/Equation26/RumpCycle/Results",
        "NumStability/Source/Higham/Chapter07/LinearSystemsConditioning/Theorem03",
        "NumStability/Source/Higham/Chapter07/LinearSystemsConditioning/Theorem05/RowInfinityScaleCounterexample",
        "NumStability/Source/Higham/Chapter08/Equation02/TriangularSubstitution/RelativeInfinityNormBounds",
        "NumStability/Source/Higham/Chapter08/Equation15/FanInExecutor",
        "NumStability/Source/Higham/Chapter08/Equation15/GlobalEnvelopeCounterexample/LocalCancellationResults",
        "NumStability/Source/Higham/Chapter08/Equation18/FanInExecutor",
        "NumStability/Source/Higham/Chapter08/Problem02/ComparisonMatrixWitness/ArbitraryRatios",
        "NumStability/Source/Higham/Chapter08/Problem07/DiagonalScaling/Results",
        "NumStability/Source/Higham/Chapter08/Problem08/SingleEntrySingularity/Results",
        "NumStability/Source/Higham/Chapter08/Problem09/KahanSingularValues/Results",
        "NumStability/Source/Higham/Chapter08/Section03/TriangularSystems/ComparisonConditioningResults",
        "NumStability/Source/Higham/Chapter08/Section03/TriangularSystems/InverseNormResults",
        "NumStability/Source/Higham/Chapter12/IterativeRefinement/ForwardErrorBounds",
        "NumStability/Source/Higham/Chapter12/IterativeRefinement/Results",
        "NumStabilityTest/Reorganization/R03",
        "docs/architecture/deliveries/R03",
    }
)
R03_REQUEST_PATH_COUNT: int | None = 121
R03_REQUEST_PATH_SHA256: str | None = (
    "22D7FB62215BA50D4C9E5E83254B3196C2920CC7B8BF2A835201D7730694E3FB"
)
NEXT_BRANCH_FACTS = {
    "B0003": {
        "wave": "R11",
        "projection": "P0003",
        "request": "R0003",
        "operator": "claude-local",
        "lane": "claude-lane",
        "branch": "codex/reorg-completion-2026-08-r11-qr-ch19",
        "delivery_sha": "444a03259af510bdfe0921d1847b6add1b26ed73",
        "delivery_report": (
            "docs/architecture/deliveries/R11/DELIVERY.md",
            "35C9AE0319D4248F450E3B83252C0802483E6433EE7F6E6B1A22AF33497722EC",
        ),
        "delivery_scope": (
            "docs/architecture/deliveries/R11/CHANGED_PATHS.md",
            "1B6A0356843A96C21D4ADE283DC920E4408204925B8FD35F78EB8A122A82AB3F",
        ),
        "owned_count": 65,
        "selector_sha256": "461D1A0E09A0EADD02B57F3FEB6E097508D02F769A13A11E1CF6896B289A3F23",
        "projection_sha256": "31EC591D949DB6041078C036F0CFF74A0A3EE229B35E351DDF999D15F494D60E",
        "projection_payload_sha256": "26469E530A4BC43B96D88665E4EAAB0D89AB2F3B624CA592CE4ACCC9FD1F04E3",
        "counts": {
            "declarations": 1477,
            "signature_edges": 15172,
            "body_edges": 18056,
            "union_edges": 19873,
        },
        "private": 17,
        "private_map_sha256": "12E4D4F517D3678DABA4A11F57D36E22EE4428BC3598D3CA0FC7E41A9323E70E",
        "private_closure_sha256": "74FA741BC9C9CCF802ED9999D64DB81E40F4D027A25351CAFF78F67196822145",
        "private_closure_rows": 954,
        "declaration_free": 59,
        "relocated": 412,
        "retained": 1065,
        "test_rows": 204,
        "test_targets": 199,
        "test_classes": {
            "canonical_only": 5,
            "focused": 5,
            "old_only": 65,
            "protected_consumer": 129,
        },
        "forbidden_exact": 2566,
        "forbidden_prefix": 14,
        "request_paths": 133,
        "request_path_sha256": "B98B986ED724D1B90DB2C368E4ADAE6046002DD05820883D0A8B1EBD445714FD",
        "request_patch_sha256": "E1BFBF147D61FFE2CA08090B91DE362A2C089709221624AB2F9B36F9F4E2F4D3",
        "request_postimages_sha256": "6799789E9E739095C49E409799F17D723C4EE038E2E341105BD38595F26CC5D2",
        "destinations": frozenset(
            {
                "NumStability/Algorithms/LinearSystems/QR/Householder",
                "NumStability/Source/Higham/Chapter19/Sensitivity/Bounds",
                "NumStability/Source/Higham/Chapter19/StoredLoop/Perturbation",
                "NumStabilityTest/Reorganization/R11",
                "docs/architecture/deliveries/R11",
            }
        ),
        "destination_counts": {
            "NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication": 101,
            "NumStability.Algorithms.LinearSystems.QR.Householder.StoredQR": 132,
            "NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels": 112,
            "NumStability.Source.Higham.Chapter19.Core": 1065,
            "NumStability.Source.Higham.Chapter19.Sensitivity.Bounds.Results": 59,
            "NumStability.Source.Higham.Chapter19.StoredLoop.Perturbation.Bridge": 8,
        },
    },
    "B0004": {
        "wave": "R12",
        "projection": "P0004",
        "request": "R0004",
        "operator": "codex-local",
        "lane": "claude-lane",
        "branch": "codex/reorg-completion-2026-08-r12-ch13-equations-table",
        "delivery_sha": "0726678a0f2db56e533f3b956a2f7f1531059d7d",
        "delivery_report": (
            "docs/architecture/deliveries/R12/DELIVERY.md",
            "266B867F4B57B62B6CFB72B186A75CE5084CCA76973CF89B634F61815D06B105",
        ),
        "delivery_scope": (
            "docs/architecture/deliveries/R12/CHANGED_PATHS.md",
            "4B40844FCA0FAE502A644DDBB108E34738D3C2516D0809FAEDD38FFE9C3450A2",
        ),
        "owned_count": 3,
        "selector_sha256": "2A45891E56E976DEAC01B791293D4DF05A4C1A045498D98B7D087B940582AD0F",
        "projection_sha256": "E84302EC06E0215758B91F9B179D89E0A5E17931CF42734828F1253BB4C129D2",
        "projection_payload_sha256": "6665F3F34F2F5DF062D6EC2438F6CBD3D599CBE756FC5591DCC9D3E96AD7F3C2",
        "counts": {
            "declarations": 34,
            "signature_edges": 80,
            "body_edges": 133,
            "union_edges": 139,
        },
        "private": 0,
        "private_map_sha256": "3266EAFAE1CD51DCBF459760E1D24DC5F88E2E29AA3E633D3B313DCF96CA368C",
        "private_closure_sha256": "E013C92B4965455EF8C0B9D82007458E2E9C3496769FB3879091AF4CCDDB04AD",
        "private_closure_rows": 0,
        "declaration_free": 0,
        "relocated": 34,
        "retained": 0,
        "test_rows": 26,
        "test_targets": 20,
        "test_classes": {
            "canonical_only": 6,
            "focused": 6,
            "old_only": 3,
            "protected_consumer": 11,
        },
        "forbidden_exact": 2628,
        "forbidden_prefix": 11,
        "request_paths": 3,
        "request_path_sha256": "D9BB4F3E7F383A45EB84DF97977D766925CCFD2FF85508077CEFE6F8F952049A",
        "request_patch_sha256": "449E350993D72F8A38A894CAF8DA245E06ED66D48A176EAE66EC65364F8D7BEB",
        "request_postimages_sha256": "6CC237E4F8F99328DAA098591F3551A8FF6A452AFF908E81B37C4AFABCF8900E",
        "destinations": frozenset(
            {
                "NumStability/Source/Higham/Chapter13/Equation23/ProductBounds",
                "NumStability/Source/Higham/Chapter13/Equation25/BackwardError",
                "NumStability/Source/Higham/Chapter13/Equation25/PartitionedComputation",
                "NumStability/Source/Higham/Chapter13/Table01/BackwardErrorBounds",
                "NumStability/Source/Higham/Chapter13/Table01/DiagonalDominance",
                "NumStability/Source/Higham/Chapter13/Table01/ProductTransfers",
                "NumStabilityTest/Reorganization/R12",
                "docs/architecture/deliveries/R12",
            }
        ),
        "destination_counts": {
            "NumStability.Source.Higham.Chapter13.Equation23.ProductBounds.PointRow": 3,
            "NumStability.Source.Higham.Chapter13.Equation25.BackwardError.Bounds": 2,
            "NumStability.Source.Higham.Chapter13.Equation25.PartitionedComputation.Implementation1": 1,
            "NumStability.Source.Higham.Chapter13.Table01.BackwardErrorBounds.Endpoints": 8,
            "NumStability.Source.Higham.Chapter13.Table01.DiagonalDominance.Bounds": 15,
            "NumStability.Source.Higham.Chapter13.Table01.ProductTransfers.Families": 5,
        },
    },
}

BRANCH_FACTS = {
    "B0001": {
        "wave": "R01",
        "projection": "P0001",
        "operator": "codex-local",
        "lane": "codex-lane",
        "branch": "codex/reorg-completion-2026-08-r01-stationary-semiconvergence",
        "paths": R01_PATHS,
        "declarations": 243,
        "private": 10,
        "declaration_free": 0,
        "consumers": R01_CONSUMERS,
        "delivery_sha": "0bdf03a383377c8c6da89d85393e56fca8c00ccd",
        "changed_paths": 98,
        "delivery_report": "docs/architecture/deliveries/R01/DELIVERY.md",
        "delivery_report_sha256": "BD5CB4ED6A2C8CEDFAD35DEE491E65EA41A0DCD70181B533B0AD3534F91815B2",
        "scope_evidence": "docs/architecture/deliveries/R01/CHANGED_PATHS.md",
        "scope_evidence_sha256": "84AF04D86C4924295BA7E984F9DB69CD83E095FDE9E45713272F1CAA574D1E27",
    },
    "B0002": {
        "wave": "R02",
        "projection": "P0002",
        "operator": "claude-local",
        "lane": "claude-lane",
        "branch": "codex/reorg-completion-2026-08-r02-norm-estimation-ch15",
        "paths": R02_PATHS,
        "declarations": 142,
        "private": 76,
        "declaration_free": 14,
        "consumers": R02_CONSUMERS,
        "delivery_sha": "f790c8413412177bb74f47fee74bb12c48c11155",
        "changed_paths": 145,
        "delivery_report": "docs/architecture/deliveries/R02/DELIVERY.md",
        "delivery_report_sha256": "C8889350AE3E11CA4A951037D46BC1C9D3FD9F30A777C433EEADB8930E66A6AE",
        "scope_evidence": (
            "docs/architecture/phases/2026-08-repository-reorganization-completion/"
            "reviews/R02-intake-scope.tsv"
        ),
        "scope_evidence_sha256": "801759184E6F986D009F84E84164FD1DA06FA2B3BFC1BDD30A2982FD509132E0",
    },
}

TEST_CLASSES = frozenset(
    {"canonical-only", "old-only", "focused", "protected-consumer"}
)
OVERLAP_CATEGORIES = {
    "owner": ("owner", "overlap"),
    "destination": ("destination", "ancestor"),
    "direct_import": ("direct", "import"),
    "transitive": ("transitive", "reach"),
    "signature": ("signature", "edge"),
    "body": ("body", "edge"),
}


class ValidationFailure(RuntimeError):
    """Raised only by the isolated self-test."""


@dataclass(frozen=True)
class Artifact:
    path: str
    sha256: str


@dataclass(frozen=True)
class PathRule:
    path: str
    match: str

    @property
    def folded(self) -> str:
        return normalize_path(self.path).casefold()

    def intersects(self, other: "PathRule") -> bool:
        left, right = self.folded, other.folded
        if self.match == "exact" and other.match == "exact":
            return left == right
        if self.match == "prefix" and other.match == "prefix":
            return is_equal_or_child(left, right) or is_equal_or_child(right, left)
        prefix, exact = (self, other) if self.match == "prefix" else (other, self)
        return is_equal_or_child(exact.folded, prefix.folded)

    def matches(self, path: str) -> bool:
        folded = normalize_path(path).casefold()
        return folded == self.folded if self.match == "exact" else is_equal_or_child(
            folded, self.folded
        )


class Problems:
    def __init__(self) -> None:
        self.messages: list[str] = []

    def add(self, context: str, message: str) -> None:
        self.messages.append(f"{context}: {message}")

    def require(self, condition: bool, context: str, message: str) -> None:
        if not condition:
            self.add(context, message)


@dataclass(frozen=True)
class R03EpochSnapshot:
    """Small policy surface shared by the runtime ratchet and adversarial tests."""

    branch_base_checkpoint_id: str
    branch_base_sha: str
    branch_status: str
    operator_ids: tuple[str, ...]
    lane_operator_ids: tuple[str, ...]
    selector_sha256: str
    selector_rows: int
    selector_matches_inventory: bool
    route_sha256: str
    activation_evidence: tuple[Artifact, ...]
    delivery: dict[str, Any]
    integration: dict[str, Any]
    retirement: dict[str, Any]
    projection_base_checkpoint_id: str
    projection_status: str
    projection_selector_sha256: str
    request_target_checkpoint_id: str
    request_target_base_sha: str
    request_status: str
    request_resolution: dict[str, Any]
    r07_milestone_status: str
    worker_shared_leaks: tuple[str, ...]
    request_unreserved_paths: tuple[str, ...]


def r03_activation_fact(text: str, label: str) -> str | None:
    """Read one exact-value row from the activation review's fact table."""

    match = re.search(
        rf"^\|\s*{re.escape(label)}\s*\|\s*`([^`\r\n]+)`\s*\|\s*$",
        text,
        re.MULTILINE,
    )
    return match.group(1) if match is not None else None


def validate_r03_activation_review_text(
    text: str, problems: Problems, *, context: str = R03_ACTIVATION_REVIEW_PATH
) -> None:
    """Validate the human-reviewed external activation facts without Git/network I/O."""

    activated = re.search(r"^- Activated at: `([^`\r\n]+)`\s*$", text, re.MULTILINE)
    problems.require(
        activated is not None
        and RFC3339_RE.fullmatch(activated.group(1)) is not None,
        f"{context}.activated_at",
        "activation time must be an exact RFC3339 timestamp",
    )
    exact_lines = (
        (
            "- Authority: `primary-human`, exercising the explicitly granted "
            "branch-registry, activation-control, main-push, and worktree-creation authority",
            "primary-human activation authority",
        ),
        (f"- Branch / wave: `{R03_BRANCH_ID}` / `{R03_WAVE_ID}`", "branch/wave"),
        (f"- Lane / operator: `{R03_LANE_ID}` / `{R03_OPERATOR_ID}`", "lane/operator"),
        (f"- Current checkpoint: `{C0002_CHECKPOINT_ID}`", "current checkpoint"),
        (
            "- Accepted C0002 checkpoint and immutable worker base: "
            f"`{C0002_CODE_SHA}`",
            "accepted checkpoint/base",
        ),
        (f"- Planned-control commit: `{R03_PLANNED_CONTROL_SHA}`", "planned-control commit"),
        (
            "- Planned-control CI: Lean CI push run "
            f"`{R03_PLANNED_CONTROL_CI_RUN}`, job `{R03_PLANNED_CONTROL_CI_JOB}`, "
            "completed `success`",
            "planned-control CI",
        ),
    )
    text_lines = set(text.splitlines())
    for exact, label in exact_lines:
        problems.require(
            exact in text_lines,
            f"{context}.identity",
            f"activation review must record exact {label}",
        )

    expected_facts = {
        "Local branch": R03_BRANCH_NAME,
        "Local branch tip": C0002_CODE_SHA,
        "Remote ref": R03_REMOTE_REF,
        "Remote ref tip": C0002_CODE_SHA,
        "Named worktree": R03_PLANNED_WORKTREE,
        "Worktree HEAD": C0002_CODE_SHA,
    }
    actual_facts = {
        label: r03_activation_fact(text, label) for label in expected_facts
    }
    for label, expected in expected_facts.items():
        problems.require(
            actual_facts[label] == expected,
            f"{context}.tips",
            f"{label} must equal exact activation fact {expected!r}",
        )

    required_statements = (
        (
            "The planned-control gate was green for the exact planned-control commit "
            "before any B0005 ref or worktree was created.",
            "green planned-control ordering",
        ),
        ("explicit nonexistent-tip lease", "nonexistent-tip lease"),
        ("empty tracked and untracked status", "clean tracked/untracked worktree"),
        ("No worker commit, production edit, or R0005 application exists.", "no worker edit"),
        ("R07 remains unactivated and M07 remains `planned`.", "R07/M07 deferral"),
        (
            "Workers may edit only B0005-owned paths, B0005 destination prefixes, "
            "`NumStabilityTest/Reorganization/R03/`, and "
            "`docs/architecture/deliveries/R03/`.",
            "worker scope",
        ),
        ("All 121 R0005 paths remain integrator-only.", "R0005 integrator ownership"),
        (
            "R0005 is context-free; any disposable replay must use "
            "`git apply --unidiff-zero`.",
            "context-free replay command",
        ),
        ("No implementation began before activation-control CI.", "implementation ordering"),
        ("full `NumStability` and `NumStabilityTest` build", "full activation build"),
        ("`core.autocrlf=false`", "LF autocrlf setting"),
        ("`core.eol=lf`", "LF eol setting"),
        ("`core.safecrlf=false`", "LF safecrlf setting"),
    )
    for statement, label in required_statements:
        problems.require(
            statement in text,
            f"{context}.claims",
            f"activation review must record exact {label}",
        )


def validate_r03_epoch_snapshot(
    snapshot: R03EpochSnapshot,
    problems: Problems,
    *,
    expected_route_sha256: str,
) -> None:
    """Enforce the exact planned/active lifecycle independently of file I/O."""

    context = "C0002-rooted R03 planned/active epoch"
    problems.require(
        snapshot.branch_base_checkpoint_id == C0002_CHECKPOINT_ID
        and snapshot.branch_base_sha == C0002_CODE_SHA,
        f"{context}.base",
        f"branch must use exact {C0002_CHECKPOINT_ID} code {C0002_CODE_SHA}",
    )
    problems.require(
        snapshot.selector_sha256 == R03_SELECTOR_SHA256
        and snapshot.projection_selector_sha256 == R03_SELECTOR_SHA256
        and snapshot.selector_rows == R03_OWNER_COUNT
        and snapshot.selector_matches_inventory,
        f"{context}.selector",
        "selector drift: branch/projection selector must be the exact sorted 47-owner C0002 R03 wave",
    )
    problems.require(
        snapshot.route_sha256 == expected_route_sha256,
        f"{context}.routes",
        f"route/hash drift: expected declaration-route SHA-256 {expected_route_sha256}",
    )
    problems.require(
        snapshot.operator_ids == (R03_OPERATOR_ID,)
        and snapshot.lane_operator_ids == (R03_OPERATOR_ID,),
        f"{context}.authority",
        "unauthorized operator: branch and codex-lane must authorize only codex-local",
    )
    expected_activation = Artifact(
        R03_ACTIVATION_REVIEW_PATH, R03_ACTIVATION_REVIEW_SHA256
    )
    problems.require(
        snapshot.branch_status in {"planned", "active"},
        f"{context}.activation",
        "branch status must be exactly planned or active",
    )
    if snapshot.branch_status == "planned":
        problems.require(
            not snapshot.activation_evidence,
            f"{context}.activation",
            "planned epoch may not carry activation/base-tip/ref-tip/worktree evidence",
        )
    elif snapshot.branch_status == "active":
        problems.require(
            snapshot.activation_evidence == (expected_activation,),
            f"{context}.activation",
            "active epoch must hash-pin exactly the reviewed R03 activation evidence",
        )
    expected_delivery = {
        "commit_sha": None,
        "report": None,
        "scope_evidence": None,
    }
    expected_integration = {
        "method": None,
        "accepted_checkpoint_id": None,
        "accepted_sha": None,
    }
    expected_retirement = {
        "remote_ref": R03_REMOTE_REF,
        "rule": "delivery_ancestor_of_green_checkpoint",
        "status": "not_due",
        "retired_at": None,
        "retired_by": None,
        "ancestry_checkpoint_id": None,
    }
    expected_resolution = {
        "checkpoint_id": None,
        "commit_sha": None,
        "reason": None,
        "resolved_at": None,
        "resolved_by": None,
        "validation_evidence": [],
    }
    problems.require(
        snapshot.delivery == expected_delivery
        and snapshot.integration == expected_integration
        and snapshot.retirement == expected_retirement
        and snapshot.projection_base_checkpoint_id == C0002_CHECKPOINT_ID
        and snapshot.projection_status == "active"
        and snapshot.request_target_checkpoint_id == C0002_CHECKPOINT_ID
        and snapshot.request_target_base_sha == C0002_CODE_SHA
        and snapshot.request_status == "active"
        and snapshot.request_resolution == expected_resolution,
        f"{context}.lifecycle",
        "invalid lifecycle transition: planned/active branch with null delivery+integration, not_due retirement, active projection, and unresolved active request required",
    )
    problems.require(
        snapshot.r07_milestone_status == "planned",
        f"{context}.r07",
        "R07/M07 must remain unactivated and planned",
    )
    problems.require(
        not snapshot.worker_shared_leaks and not snapshot.request_unreserved_paths,
        f"{context}.shared_paths",
        "shared-path leakage: worker paths must avoid shared controls and every request path must be reserved",
    )


def normalize_path(value: str) -> str:
    return value.replace("\\", "/").rstrip("/")


def is_equal_or_child(path: str, parent: str) -> bool:
    return path == parent or path.startswith(parent + "/")


def module_from_path(path: str) -> str:
    path = normalize_path(path)
    return path[:-5].replace("/", ".") if path.endswith(".lean") else path.replace("/", ".")


def sha256_path(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def path_list_sha256(paths: Iterable[str]) -> str:
    payload = ("\n".join(sorted(paths)) + "\n").encode("utf-8")
    return hashlib.sha256(payload).hexdigest().upper()


def path_from_module(module: str) -> str:
    return module.replace(".", "/") + ".lean"


def split_values(value: str) -> list[str]:
    return [part.strip() for part in re.split(r"[;,]", value) if part.strip() and part.strip() != "-"]


def next_branch_statuses(checkpoint_id: str) -> set[str]:
    if checkpoint_id == SUCCESSOR_CHECKPOINT_ID:
        return {"planned", "active", "delivered"}
    if checkpoint_id == C0002_CHECKPOINT_ID:
        return {"accepted", "retired"}
    return set()


def next_projection_status(checkpoint_id: str) -> str | None:
    if checkpoint_id == SUCCESSOR_CHECKPOINT_ID:
        return "active"
    if checkpoint_id == C0002_CHECKPOINT_ID:
        return "retired"
    return None


def next_request_status(checkpoint_id: str) -> str | None:
    if checkpoint_id == SUCCESSOR_CHECKPOINT_ID:
        return "active"
    if checkpoint_id == C0002_CHECKPOINT_ID:
        return "applied"
    return None


def next_lane_operators(checkpoint_id: str) -> list[str]:
    if checkpoint_id == SUCCESSOR_CHECKPOINT_ID:
        return ["claude-local", "codex-local"]
    if checkpoint_id == C0002_CHECKPOINT_ID:
        return ["claude-local"]
    return []


def next_retirement_status(branch_status: str) -> str | None:
    if branch_status in {"planned", "active", "delivered"}:
        return "not_due"
    if branch_status == "accepted":
        return "due"
    if branch_status == "retired":
        return "retired"
    return None


def flatten_strings(value: Any) -> Iterator[str]:
    if isinstance(value, str):
        yield value
    elif isinstance(value, dict):
        for key, item in value.items():
            yield str(key)
            yield from flatten_strings(item)
    elif isinstance(value, list):
        for item in value:
            yield from flatten_strings(item)


def remove_lean_comments(text: str) -> str:
    """Replace nested comments while preserving enough layout for import scans."""

    result: list[str] = []
    index = 0
    depth = 0
    in_string = False
    escaped = False
    while index < len(text):
        pair = text[index : index + 2]
        char = text[index]
        if depth:
            if pair == "/-":
                depth += 1
                result.extend("  ")
                index += 2
            elif pair == "-/":
                depth -= 1
                result.extend("  ")
                index += 2
            else:
                result.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if in_string:
            result.append(char)
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if pair == "/-":
            depth = 1
            result.extend("  ")
            index += 2
        elif pair == "--":
            newline = text.find("\n", index + 2)
            if newline < 0:
                result.extend(" " * (len(text) - index))
                break
            result.extend(" " * (newline - index))
            result.append("\n")
            index = newline + 1
        else:
            result.append(char)
            if char == '"':
                in_string = True
            index += 1
    return "".join(result)


class CompletionValidator:
    def __init__(self, root: Path, phase_dir: Path) -> None:
        self.root = root.resolve()
        self.phase_dir = (
            phase_dir.resolve()
            if phase_dir.is_absolute()
            else (self.root / phase_dir).resolve()
        )
        self.problems = Problems()
        self.phase: dict[str, Any] = {}
        self.scope: list[dict[str, str]] = []
        self.scope_by_path: dict[str, dict[str, str]] = {}
        self.shared_rules: list[PathRule] = []
        self.branch_records: dict[str, dict[str, Any]] = {}
        self.branch_evidence: dict[str, list[Artifact]] = defaultdict(list)
        self.requests: dict[str, dict[str, Any]] = {}
        self.current_checkpoint_id = CHECKPOINT_ID
        self._git_tree_blobs: dict[str, dict[str, str]] = {}

    def relative(self, path: Path) -> str:
        try:
            return path.resolve().relative_to(self.root).as_posix()
        except ValueError:
            return str(path)

    def resolve_repo_path(self, value: str, context: str) -> Path | None:
        value = normalize_path(value)
        pure = PurePosixPath(value)
        if pure.is_absolute() or ".." in pure.parts or value in {"", "."}:
            self.problems.add(context, f"invalid repository-relative path {value!r}")
            return None
        path = (self.root / Path(*pure.parts)).resolve()
        try:
            path.relative_to(self.root)
        except ValueError:
            self.problems.add(context, f"path escapes repository: {value!r}")
            return None
        return path

    def read_json(self, path: Path, context: str) -> dict[str, Any] | None:
        try:
            value = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, UnicodeError, json.JSONDecodeError) as error:
            self.problems.add(context, f"cannot read JSON: {error}")
            return None
        if not isinstance(value, dict):
            self.problems.add(context, "expected a JSON object")
            return None
        return value

    def read_tsv(
        self,
        path: Path,
        context: str,
        expected_header: Sequence[str] | None = None,
    ) -> tuple[tuple[str, ...], list[dict[str, str]]]:
        try:
            raw = path.read_bytes()
        except OSError as error:
            self.problems.add(context, f"cannot read TSV: {error}")
            return (), []
        if b"\r" in raw:
            self.problems.add(context, "TSV must use LF line endings")
        if raw and not raw.endswith(b"\n"):
            self.problems.add(context, "TSV must end with a newline")
        try:
            text = raw.decode("utf-8-sig")
            reader = csv.DictReader(text.splitlines(), delimiter="\t")
            header = tuple(reader.fieldnames or ())
            rows = [dict(row) for row in reader]
        except (UnicodeError, csv.Error) as error:
            self.problems.add(context, f"cannot parse TSV: {error}")
            return (), []
        if expected_header is not None and header != tuple(expected_header):
            self.problems.add(
                context,
                "header must be exactly: " + "\t".join(expected_header),
            )
        if any(None in row or any(value is None for value in row.values()) for row in rows):
            self.problems.add(context, "malformed row or wrong column count")
        return header, rows

    def artifact(self, value: Any, context: str) -> Artifact | None:
        if not isinstance(value, dict) or set(value) != {"path", "sha256"}:
            self.problems.add(context, "expected exactly {path, sha256}")
            return None
        path_value, digest = value.get("path"), value.get("sha256")
        if not isinstance(path_value, str) or not isinstance(digest, str):
            self.problems.add(context, "path and sha256 must be strings")
            return None
        if not SHA256_RE.fullmatch(digest):
            self.problems.add(context, "sha256 must be 64 hexadecimal characters")
            return None
        path = self.resolve_repo_path(path_value, context)
        if path is None:
            return None
        if not path.is_file():
            self.problems.add(context, f"missing artifact {path_value}")
            return None
        actual = sha256_path(path)
        if actual != digest.upper():
            self.problems.add(
                context,
                f"SHA-256 mismatch for {path_value}: expected {digest.upper()}, found {actual}",
            )
        return Artifact(normalize_path(path_value), digest.upper())

    def git(self, *args: str, check: bool = True, env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
        process = subprocess.run(
            ["git", *args],
            cwd=self.root,
            env=env,
            text=True,
            encoding="utf-8",
            errors="replace",
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        if check and process.returncode:
            raise RuntimeError(
                f"git {' '.join(args)} failed ({process.returncode}): "
                f"{process.stderr.strip() or process.stdout.strip()}"
            )
        return process

    def git_bytes(
        self,
        *args: str,
        check: bool = True,
        env: dict[str, str] | None = None,
    ) -> subprocess.CompletedProcess[bytes]:
        process = subprocess.run(
            ["git", *args],
            cwd=self.root,
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        if check and process.returncode:
            detail = (process.stderr or process.stdout).decode(
                "utf-8", errors="replace"
            ).strip()
            raise RuntimeError(
                f"git {' '.join(args)} failed ({process.returncode}): {detail}"
            )
        return process

    def git_blob_payloads(
        self,
        oids: Iterable[str],
        context: str,
        *,
        env: dict[str, str] | None = None,
    ) -> dict[str, bytes]:
        """Read many Git blobs with one ``cat-file --batch`` process."""

        requested = sorted(set(oids))
        if not requested:
            return {}
        process = subprocess.run(
            ["git", "cat-file", "--batch"],
            cwd=self.root,
            env=env,
            input=("\n".join(requested) + "\n").encode("ascii"),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        if process.returncode:
            self.problems.add(
                context,
                "cannot batch-read Git blobs: "
                + (process.stderr or process.stdout).decode(
                    "utf-8", errors="replace"
                ).strip(),
            )
            return {}
        stream = io.BytesIO(process.stdout)
        payloads: dict[str, bytes] = {}
        for requested_oid in requested:
            header = stream.readline().rstrip(b"\n")
            try:
                returned_oid, kind, raw_size = header.decode("ascii").split()
                size = int(raw_size)
            except (UnicodeError, ValueError):
                self.problems.add(
                    context,
                    f"malformed cat-file batch header for {requested_oid}: {header!r}",
                )
                break
            payload = stream.read(size)
            terminator = stream.read(1)
            if (
                returned_oid != requested_oid
                or kind != "blob"
                or len(payload) != size
                or terminator != b"\n"
            ):
                self.problems.add(
                    context,
                    f"malformed cat-file batch payload for {requested_oid}",
                )
                break
            payloads[requested_oid] = payload
        return payloads

    def run(self) -> Problems:
        self.validate_pointer()
        self.load_phase()
        self.validate_checkpoint_and_scope()
        self.validate_branches()
        self.validate_routes_and_tests()
        self.validate_projections()
        self.validate_overlap_reviews()
        self.validate_requests_and_postimages()
        self.validate_next_wave_controls()
        self.validate_r03_epoch()
        self.validate_milestone_dag()
        return self.problems

    def validate_pointer(self) -> None:
        path = self.root / ACTIVE_POINTER
        pointer = self.read_json(path, ACTIVE_POINTER.as_posix())
        if pointer is None:
            return
        expected = {
            "schema_version": 1,
            "record_kind": "active_reorganization_phase",
            "phase_id": PHASE_ID,
            "path": DEFAULT_PHASE_DIR.as_posix(),
        }
        self.problems.require(
            pointer == expected,
            ACTIVE_POINTER.as_posix(),
            f"must exactly equal {canonical_json(expected)}",
        )

    def load_phase(self) -> None:
        context = self.relative(self.phase_dir / "phase.json")
        phase = self.read_json(self.phase_dir / "phase.json", context)
        if phase is None:
            return
        self.phase = phase
        exact = {
            "schema_version": 1,
            "record_kind": "reorganization_phase",
            "phase_id": PHASE_ID,
            "origin_checkpoint_id": CHECKPOINT_ID,
            "status": "active",
        }
        for key, expected in exact.items():
            self.problems.require(
                phase.get(key) == expected,
                f"phase.json.{key}",
                f"expected {expected!r}, found {phase.get(key)!r}",
            )
        current = phase.get("current_checkpoint_id")
        allowed_checkpoints = {
            CHECKPOINT_ID,
            SUCCESSOR_CHECKPOINT_ID,
            C0002_CHECKPOINT_ID,
        }
        self.problems.require(
            current in allowed_checkpoints,
            "phase.json.current_checkpoint_id",
            f"expected one of {sorted(allowed_checkpoints)}, found {current!r}",
        )
        if current in allowed_checkpoints:
            self.current_checkpoint_id = current
        base = phase.get("base_policy")
        if not isinstance(base, dict):
            self.problems.add("phase.json.base_policy", "expected an object")
        else:
            self.problems.require(
                base.get("immutable_origin_sha") == CODE_SHA,
                "phase.json.base_policy.immutable_origin_sha",
                f"expected {CODE_SHA}",
            )
        authority = phase.get("authority")
        if not isinstance(authority, dict):
            self.problems.add("phase.json.authority", "expected an object")
        else:
            for key in ("integration_authority_id", "release_manager_id"):
                self.problems.require(
                    authority.get(key) == "primary-human",
                    f"phase.json.authority.{key}",
                    "expected primary-human",
                )
            self.problems.require(
                authority.get("build_lock_name") == BUILD_LOCK,
                "phase.json.authority.build_lock_name",
                f"expected {BUILD_LOCK}",
            )
            shared_auth = authority.get("shared_path_authority_ids")
            self.problems.require(
                isinstance(shared_auth, list) and set(shared_auth) == {"primary-human"},
                "phase.json.authority.shared_path_authority_ids",
                "expected exactly primary-human",
            )
            lanes = authority.get("lanes") if isinstance(authority.get("lanes"), list) else []
            operators = {
                operator
                for lane in lanes
                if isinstance(lane, dict)
                for operator in lane.get("operator_ids", [])
                if isinstance(operator, str)
            }
            self.problems.require(
                {"codex-local", "claude-local"} <= operators,
                "phase.json.authority.lanes",
                "local lanes must include codex-local and claude-local",
            )
        scope_ref = self.artifact(phase.get("scope"), "phase.json.scope")
        if scope_ref is not None:
            self.problems.require(
                scope_ref.path == self.relative(self.phase_dir / "scope.tsv"),
                "phase.json.scope.path",
                "must point to successor scope.tsv",
            )
        self.shared_rules = self.parse_rules(phase.get("shared_paths"), "phase.json.shared_paths")
        shared_exact = {rule.path for rule in self.shared_rules if rule.match == "exact"}
        missing = sorted(SHARED_CONSUMERS - shared_exact)
        if missing:
            self.problems.add(
                "phase.json.shared_paths",
                "missing exact integrator-shared consumer(s): " + ", ".join(missing),
            )
        if self.current_checkpoint_id == C0002_CHECKPOINT_ID:
            # C0002 released eleven future-owner reservations after R11/R12.
            # R0005 independently needs four of those same files as exact R03
            # consumer postimages, so a new active request may re-reserve only
            # this reviewed subset; the other seven must remain released.
            stale = sorted(
                (C0002_RELEASED_SHARED_PATHS - R03_RERESERVED_C0002_PATHS)
                & shared_exact
            )
            self.problems.require(
                not stale,
                "phase.json.shared_paths",
                "C0002 must keep the seven non-R03 future R05/R09 owner reservations released; "
                f"still present: {stale}",
            )
            self.problems.require(
                R03_RERESERVED_C0002_PATHS <= shared_exact,
                "phase.json.shared_paths",
                "active R0005 must exactly re-reserve its four reviewed C0002 consumer paths",
            )
        readme = self.phase_dir / "README.md"
        try:
            text = readme.read_text(encoding="utf-8")
        except OSError as error:
            self.problems.add(self.relative(readme), f"cannot read phase README: {error}")
        else:
            for token in ("predecessor", "C0008", CODE_SHA):
                if token not in text:
                    self.problems.add(self.relative(readme), f"missing predecessor root token {token!r}")

    def parse_rules(self, value: Any, context: str) -> list[PathRule]:
        if not isinstance(value, list):
            self.problems.add(context, "expected a list")
            return []
        result: list[PathRule] = []
        for index, item in enumerate(value):
            item_context = f"{context}[{index}]"
            if not isinstance(item, dict) or set(item) != {"path", "match"}:
                self.problems.add(item_context, "expected exactly {path, match}")
                continue
            path, match = item.get("path"), item.get("match")
            if not isinstance(path, str) or match not in {"exact", "prefix"}:
                self.problems.add(item_context, "invalid path rule")
                continue
            normalized = normalize_path(path)
            if normalized != path.rstrip("/").replace("\\", "/"):
                self.problems.add(item_context, "path rule must use normalized repository separators")
            result.append(PathRule(normalized, match))
        keys = [(rule.path.casefold(), rule.match) for rule in result]
        if len(keys) != len(set(keys)):
            self.problems.add(context, "duplicate case-insensitive path rule")
        return result

    def validate_checkpoint_and_scope(self) -> None:
        checkpoint_path = self.phase_dir / "checkpoints/C0000.json"
        checkpoint = self.read_json(checkpoint_path, self.relative(checkpoint_path))
        if checkpoint is None:
            return
        for key, expected in {
            "schema_version": 1,
            "record_kind": "phase_checkpoint",
            "phase_id": PHASE_ID,
            "checkpoint_id": CHECKPOINT_ID,
            "commit_sha": CODE_SHA,
        }.items():
            self.problems.require(
                checkpoint.get(key) == expected,
                f"checkpoints/C0000.json.{key}",
                f"expected {expected!r}",
            )
        if self.current_checkpoint_id in {
            SUCCESSOR_CHECKPOINT_ID,
            C0002_CHECKPOINT_ID,
        }:
            self.validate_successor_checkpoint()
        if self.current_checkpoint_id == C0002_CHECKPOINT_ID:
            self.validate_c0002_checkpoint()
        inventory_ref = self.artifact(
            checkpoint.get("inventory"), "checkpoints/C0000.json.inventory"
        )
        scope_path = self.phase_dir / "scope.tsv"
        _, scope = self.read_tsv(scope_path, self.relative(scope_path), SCOPE_HEADER)
        self.scope = scope
        self.scope_by_path = {row.get("path", ""): row for row in scope}
        self.problems.require(
            len(scope) == 2593,
            self.relative(scope_path),
            f"expected 2,593 production rows, found {len(scope)}",
        )
        if len(self.scope_by_path) != len(scope):
            self.problems.add(self.relative(scope_path), "duplicate scope path")
        if inventory_ref is not None:
            inventory_path = self.root / inventory_ref.path
            _, inventory = self.read_tsv(
                inventory_path, inventory_ref.path, SCOPE_HEADER
            )
            if inventory != scope:
                self.problems.add(
                    inventory_ref.path,
                    "C0000 inventory must byte-semantically equal successor scope.tsv",
                )
        predecessor_path = self.root / PREDECESSOR_DIR / "checkpoints/C0008-inventory.tsv"
        _, predecessor = self.read_tsv(
            predecessor_path,
            (PREDECESSOR_DIR / "checkpoints/C0008-inventory.tsv").as_posix(),
            SCOPE_HEADER,
        )
        predecessor_by_path = {row.get("path", ""): row for row in predecessor}
        self.problems.require(
            len(predecessor) == 2593,
            "predecessor C0008 inventory",
            f"expected 2,593 rows, found {len(predecessor)}",
        )
        debt = {row["path"] for row in predecessor if row.get("debt_flags") != "-"}
        clean_w90 = {
            row["path"]
            for row in predecessor
            if row.get("debt_flags") == "-" and row.get("wave_id") == "W90"
        }
        self.problems.require(len(debt) == 467, "residual accounting", f"expected 467 debt rows, found {len(debt)}")
        self.problems.require(len(clean_w90) == 15, "residual accounting", f"expected 15 debt-free W90 outliers, found {len(clean_w90)}")
        for path, old in predecessor_by_path.items():
            new = self.scope_by_path.get(path)
            if new is None:
                self.problems.add("scope.tsv", f"missing immutable C0008 path {path}")
                continue
            for key in ("module", "path", "base_blob_oid", "current_tier", "debt_flags"):
                if new.get(key) != old.get(key):
                    self.problems.add(
                        f"scope.tsv[{path}]",
                        f"immutable {key} drift: {old.get(key)!r} -> {new.get(key)!r}",
                    )
        in_scope = {row["path"] for row in scope if row.get("phase_scope") == "in_scope"}
        complete = {row["path"] for row in scope if row.get("phase_scope") == "already_complete"}
        self.problems.require(len(in_scope) == 492, "scope.tsv", f"expected 492 in_scope rows, found {len(in_scope)}")
        self.problems.require(len(complete) == 2101, "scope.tsv", f"expected 2,101 already_complete rows, found {len(complete)}")
        expected_editable = (debt | clean_w90) - {MATRIX_ALGEBRA}
        expected_in_scope = expected_editable | SHARED_CONSUMERS
        missing = sorted(expected_in_scope - in_scope)
        extra = sorted(in_scope - expected_in_scope)
        if missing or extra:
            self.problems.add(
                "scope.tsv residual assignment",
                f"expected exact 492-row set; missing={missing}, extra={extra}",
            )
        matrix = self.scope_by_path.get(MATRIX_ALGEBRA)
        if matrix is None:
            self.problems.add("scope.tsv", f"missing protected {MATRIX_ALGEBRA}")
        else:
            self.problems.require(
                matrix.get("phase_scope") == "already_complete"
                and matrix.get("lane_id") == "-"
                and matrix.get("wave_id") == "-",
                f"scope.tsv[{MATRIX_ALGEBRA}]",
                "must be protected already_complete with lane_id/wave_id '-'",
            )
        for path in SHARED_CONSUMERS:
            row = self.scope_by_path.get(path)
            if row is None:
                self.problems.add("scope.tsv", f"missing shared consumer {path}")
                continue
            self.problems.require(
                row.get("phase_scope") == "in_scope" and row.get("wave_id") == "I01",
                f"scope.tsv[{path}]",
                "integrator-shared consumer must be in_scope in I01",
            )
        for row in scope:
            disposition = row.get("phase_scope")
            if disposition == "in_scope":
                if row.get("lane_id") in {"", "-"} or row.get("wave_id") in {"", "-"}:
                    self.problems.add(
                        f"scope.tsv[{row.get('path')}]",
                        "in_scope row requires a lane and wave",
                    )
            elif disposition == "already_complete":
                if row.get("lane_id") != "-" or row.get("wave_id") != "-":
                    self.problems.add(
                        f"scope.tsv[{row.get('path')}]",
                        "already_complete row must use '-' lane and wave",
                    )
            else:
                self.problems.add(
                    f"scope.tsv[{row.get('path')}]",
                    f"completion scope permits only in_scope/already_complete, found {disposition!r}",
                )
        for wave, paths in (("R01", R01_PATHS), ("R02", R02_PATHS)):
            actual = {
                row["path"]
                for row in scope
                if row.get("phase_scope") == "in_scope" and row.get("wave_id") == wave
            }
            if actual != paths:
                self.problems.add(
                    f"scope.tsv wave {wave}",
                    f"must equal exact selector paths; missing={sorted(paths-actual)}, extra={sorted(actual-paths)}",
                )
        accounting = self.phase_dir / "reviews/residual-accounting.md"
        try:
            text = accounting.read_text(encoding="utf-8")
        except OSError as error:
            self.problems.add(self.relative(accounting), f"cannot read residual review: {error}")
        else:
            compact = text.replace(",", "")
            for token in ("467", "15", "481", "492", "2101", MATRIX_ALGEBRA):
                if token not in compact:
                    self.problems.add(self.relative(accounting), f"missing accounting token {token!r}")

    def validate_successor_checkpoint(self) -> None:
        context = "checkpoints/C0001.json"
        path = self.phase_dir / "checkpoints/C0001.json"
        checkpoint = self.read_json(path, self.relative(path))
        if checkpoint is None:
            return
        for key, expected in {
            "schema_version": 1,
            "record_kind": "phase_checkpoint",
            "phase_id": PHASE_ID,
            "checkpoint_id": SUCCESSOR_CHECKPOINT_ID,
            "parent_checkpoint_id": CHECKPOINT_ID,
            "commit_sha": INTEGRATED_CODE_SHA,
            "accepted_by": "primary-human",
            "milestones_satisfied": SUCCESSOR_MILESTONES,
            "unblocks": [],
            "metrics": SUCCESSOR_METRICS,
        }.items():
            self.problems.require(
                checkpoint.get(key) == expected,
                f"{context}.{key}",
                f"expected {expected!r}, found {checkpoint.get(key)!r}",
            )
        accepted_at = checkpoint.get("accepted_at")
        self.problems.require(
            isinstance(accepted_at, str)
            and RFC3339_RE.fullmatch(accepted_at) is not None,
            f"{context}.accepted_at",
            "expected an RFC3339 timestamp with timezone",
        )

        inventory = self.artifact(checkpoint.get("inventory"), f"{context}.inventory")
        expected_inventory = self.relative(
            self.phase_dir / "checkpoints/C0001-inventory.tsv"
        )
        if inventory is not None:
            self.problems.require(
                inventory.path == expected_inventory,
                f"{context}.inventory.path",
                f"expected {expected_inventory}",
            )
            _, rows = self.read_tsv(
                self.root / inventory.path,
                inventory.path,
                SCOPE_HEADER,
            )
            self.problems.require(
                len(rows) == SUCCESSOR_METRICS["production_modules"],
                inventory.path,
                "row count must equal the exact C0001 production-module metric",
            )
            paths = [row.get("path", "") for row in rows]
            self.problems.require(
                len(paths) == len(set(paths)),
                inventory.path,
                "C0001 inventory paths must be unique",
            )

        baseline = checkpoint.get("combined_baseline")
        if not isinstance(baseline, dict):
            self.problems.add(f"{context}.combined_baseline", "expected an object")
        else:
            self.problems.require(
                baseline.get("format_version") == 2,
                f"{context}.combined_baseline.format_version",
                "expected exact format version 2",
            )
            artifact = self.artifact(
                baseline.get("artifact"),
                f"{context}.combined_baseline.artifact",
            )
            summary = self.artifact(
                baseline.get("summary_artifact"),
                f"{context}.combined_baseline.summary_artifact",
            )
            expected_artifact = self.relative(
                self.phase_dir / "baselines/C0001-combined.json"
            )
            expected_summary = self.relative(
                self.phase_dir / "baselines/C0001-combined.md"
            )
            if artifact is not None:
                self.problems.require(
                    artifact.path == expected_artifact,
                    f"{context}.combined_baseline.artifact.path",
                    f"expected {expected_artifact}",
                )
                document = self.read_json(
                    self.root / artifact.path,
                    f"{context}.combined_baseline.artifact",
                )
                metadata = document.get("metadata") if document is not None else None
                self.problems.require(
                    isinstance(metadata, dict)
                    and metadata.get("commit") == INTEGRATED_CODE_SHA
                    and metadata.get("library_source_clean") is True
                    and metadata.get("library_source_dirty_paths") == [],
                    f"{context}.combined_baseline.artifact.metadata",
                    "must record the exact clean integrated code commit",
                )
            if summary is not None:
                self.problems.require(
                    summary.path == expected_summary,
                    f"{context}.combined_baseline.summary_artifact.path",
                    f"expected {expected_summary}",
                )
            self.problems.require(
                isinstance(baseline.get("generation_command"), str)
                and bool(baseline.get("generation_command", "").strip()),
                f"{context}.combined_baseline.generation_command",
                "must record a nonempty generation command",
            )

        gates = checkpoint.get("gates")
        if not isinstance(gates, list):
            self.problems.add(f"{context}.gates", "expected a list")
        else:
            gate_ids = [
                gate.get("gate_id")
                for gate in gates
                if isinstance(gate, dict)
            ]
            self.problems.require(
                len(gate_ids) == len(gates)
                and len(gate_ids) == len(set(gate_ids))
                and set(gate_ids) == SUCCESSOR_GATE_IDS,
                f"{context}.gates",
                "must contain every and only the 12 exact C0001 acceptance gates",
            )
            expected_evidence = self.relative(
                self.phase_dir / "checkpoints/C0001-gates.md"
            )
            for index, gate in enumerate(gates):
                if not isinstance(gate, dict):
                    self.problems.add(f"{context}.gates[{index}]", "expected an object")
                    continue
                gate_id = gate.get("gate_id")
                gate_context = f"{context}.gates[{gate_id or index}]"
                self.problems.require(
                    gate.get("status") == "PASS"
                    and gate.get("commit_sha") == INTEGRATED_CODE_SHA,
                    gate_context,
                    "must record PASS at the exact integrated code commit",
                )
                evidence = self.artifact(
                    gate.get("evidence"), f"{gate_context}.evidence"
                )
                if evidence is not None:
                    self.problems.require(
                        evidence.path == expected_evidence,
                        f"{gate_context}.evidence.path",
                        f"expected {expected_evidence}",
                    )

        milestones = self.phase.get("milestones")
        milestone_map = {
            item.get("milestone_id"): item
            for item in milestones
            if isinstance(item, dict) and isinstance(item.get("milestone_id"), str)
        } if isinstance(milestones, list) else {}
        for milestone_id in SUCCESSOR_MILESTONES:
            milestone = milestone_map.get(milestone_id)
            self.problems.require(
                isinstance(milestone, dict)
                and milestone.get("status") == "accepted"
                and milestone.get("accepted_checkpoint_id")
                == SUCCESSOR_CHECKPOINT_ID,
                f"phase.json.milestones[{milestone_id}]",
                "must be accepted at exact checkpoint C0001",
            )
        self.validate_successor_history()

    def validate_successor_history(self) -> None:
        for commit, parents, label in (
            (R01_MERGE_SHA, R01_MERGE_PARENTS, "R01 merge"),
            (R02_MERGE_SHA, R02_MERGE_PARENTS, "R02 merge"),
        ):
            process = self.git(
                "rev-list", "--parents", "-n", "1", commit, check=False
            )
            actual = process.stdout.strip().split()
            expected = [commit, *parents]
            self.problems.require(
                process.returncode == 0 and actual == expected,
                f"C0001 {label} ancestry",
                f"expected exact commit/parent vector {expected}, found {actual}",
            )
        for ancestor, label in (
            (R01_MERGE_SHA, "R01 merge"),
            (R02_MERGE_SHA, "R02 merge"),
            (BRANCH_FACTS["B0001"]["delivery_sha"], "R01 delivery"),
            (BRANCH_FACTS["B0002"]["delivery_sha"], "R02 delivery"),
        ):
            ancestry = self.git(
                "merge-base",
                "--is-ancestor",
                ancestor,
                INTEGRATED_CODE_SHA,
                check=False,
            )
            self.problems.require(
                ancestry.returncode == 0,
                f"C0001 {label} ancestry",
                f"{ancestor} must be an ancestor of exact integrated code {INTEGRATED_CODE_SHA}",
            )

    def validate_c0002_checkpoint(self) -> None:
        context = "checkpoints/C0002.json"
        path = self.phase_dir / "checkpoints/C0002.json"
        checkpoint = self.read_json(path, self.relative(path))
        if checkpoint is None:
            return
        for key, expected in {
            "schema_version": 1,
            "record_kind": "phase_checkpoint",
            "phase_id": PHASE_ID,
            "checkpoint_id": C0002_CHECKPOINT_ID,
            "parent_checkpoint_id": SUCCESSOR_CHECKPOINT_ID,
            "commit_sha": C0002_CODE_SHA,
            "accepted_by": "primary-human",
            "milestones_satisfied": C0002_MILESTONES,
            "unblocks": [],
            "metrics": C0002_METRICS,
        }.items():
            self.problems.require(
                checkpoint.get(key) == expected,
                f"{context}.{key}",
                f"expected {expected!r}, found {checkpoint.get(key)!r}",
            )
        accepted_at = checkpoint.get("accepted_at")
        self.problems.require(
            isinstance(accepted_at, str)
            and RFC3339_RE.fullmatch(accepted_at) is not None,
            f"{context}.accepted_at",
            "expected an RFC3339 timestamp with timezone",
        )

        inventory = self.artifact(checkpoint.get("inventory"), f"{context}.inventory")
        expected_inventory = self.relative(
            self.phase_dir / "checkpoints/C0002-inventory.tsv"
        )
        if inventory is not None:
            self.problems.require(
                inventory.path == expected_inventory
                and inventory.sha256 == C0002_INVENTORY_SHA256,
                f"{context}.inventory",
                f"must pin {expected_inventory} at {C0002_INVENTORY_SHA256}",
            )
            _, rows = self.read_tsv(
                self.root / inventory.path, inventory.path, SCOPE_HEADER
            )
            paths = [row.get("path", "") for row in rows]
            self.problems.require(
                len(rows) == C0002_METRICS["production_modules"]
                and len(paths) == len(set(paths)),
                inventory.path,
                "must contain 2,642 unique production-module rows",
            )
            dispositions = Counter(row.get("phase_scope", "") for row in rows)
            debt_rows = sum(row.get("debt_flags", "") != "-" for row in rows)
            self.problems.require(
                dispositions == Counter({"already_complete": 2262, "in_scope": 380})
                and debt_rows == 356,
                inventory.path,
                "must record exact C0002 2,262/380 disposition and 356-row debt accounting",
            )
            if (self.root / inventory.path).is_file():
                self.problems.require(
                    sha256_path(self.root / inventory.path) == C0002_INVENTORY_SHA256,
                    inventory.path,
                    "C0002 inventory content drifted",
                )

        baseline = checkpoint.get("combined_baseline")
        if not isinstance(baseline, dict):
            self.problems.add(f"{context}.combined_baseline", "expected an object")
        else:
            self.problems.require(
                baseline.get("format_version") == 2
                and isinstance(baseline.get("generation_command"), str)
                and bool(baseline.get("generation_command", "").strip()),
                f"{context}.combined_baseline",
                "requires format 2 and a nonempty generation command",
            )
            artifact = self.artifact(
                baseline.get("artifact"), f"{context}.combined_baseline.artifact"
            )
            summary = self.artifact(
                baseline.get("summary_artifact"),
                f"{context}.combined_baseline.summary_artifact",
            )
            expected_artifact = self.relative(
                self.phase_dir / "baselines/C0002-combined.json"
            )
            expected_summary = self.relative(
                self.phase_dir / "baselines/C0002-combined.md"
            )
            if artifact is not None:
                self.problems.require(
                    artifact.path == expected_artifact
                    and artifact.sha256 == C0002_COMBINED_BASELINE_SHA256,
                    f"{context}.combined_baseline.artifact",
                    "must pin the exact C0002 format-2 JSON baseline",
                )
                document = self.read_json(
                    self.root / artifact.path,
                    f"{context}.combined_baseline.artifact",
                )
                metadata = document.get("metadata") if document is not None else None
                source = document.get("source") if document is not None else None
                self.problems.require(
                    isinstance(metadata, dict)
                    and metadata.get("commit") == C0002_CODE_SHA
                    and metadata.get("library_source_clean") is True
                    and metadata.get("library_source_dirty_paths") == [],
                    f"{context}.combined_baseline.artifact.metadata",
                    "must record the exact clean C0002 code commit",
                )
                self.problems.require(
                    isinstance(source, dict)
                    and source.get("module_count") == 2642
                    and source.get("line_count") == 4001883
                    and source.get("nonblank_line_count") == 1452020
                    and source.get("byte_count") == 74555226
                    and source.get("direct_import_count") == 27407
                    and source.get("internal_direct_import_count") == 16479
                    and source.get("external_direct_import_count") == 10928,
                    f"{context}.combined_baseline.artifact.source",
                    "source totals must equal the exact C0002 measurements",
                )
                if (self.root / artifact.path).is_file():
                    self.problems.require(
                        sha256_path(self.root / artifact.path)
                        == C0002_COMBINED_BASELINE_SHA256,
                        artifact.path,
                        "C0002 baseline content drifted",
                    )
            if summary is not None:
                self.problems.require(
                    summary.path == expected_summary
                    and summary.sha256 == C0002_COMBINED_SUMMARY_SHA256,
                    f"{context}.combined_baseline.summary_artifact",
                    "must pin the exact C0002 Markdown summary",
                )
                if (self.root / summary.path).is_file():
                    self.problems.require(
                        sha256_path(self.root / summary.path)
                        == C0002_COMBINED_SUMMARY_SHA256,
                        summary.path,
                        "C0002 baseline summary content drifted",
                    )

        gates = checkpoint.get("gates")
        expected_evidence = self.relative(
            self.phase_dir / "checkpoints/C0002-gates.md"
        )
        if not isinstance(gates, list):
            self.problems.add(f"{context}.gates", "expected a list")
        else:
            gate_ids = [
                gate.get("gate_id") for gate in gates if isinstance(gate, dict)
            ]
            self.problems.require(
                len(gate_ids) == len(gates)
                and len(gate_ids) == len(set(gate_ids))
                and set(gate_ids) == SUCCESSOR_GATE_IDS,
                f"{context}.gates",
                "must contain every and only the 12 exact C0002 acceptance gates",
            )
            for index, gate in enumerate(gates):
                if not isinstance(gate, dict):
                    self.problems.add(f"{context}.gates[{index}]", "expected an object")
                    continue
                gate_id = gate.get("gate_id")
                gate_context = f"{context}.gates[{gate_id or index}]"
                self.problems.require(
                    gate.get("status") == "PASS"
                    and gate.get("commit_sha") == C0002_CODE_SHA,
                    gate_context,
                    "must record PASS at the exact C0002 code commit",
                )
                evidence = self.artifact(
                    gate.get("evidence"), f"{gate_context}.evidence"
                )
                if evidence is not None:
                    self.problems.require(
                        evidence.path == expected_evidence
                        and evidence.sha256 == C0002_GATES_SHA256,
                        f"{gate_context}.evidence",
                        "must pin the exact C0002 gate report",
                    )
        gate_path = self.root / expected_evidence
        if gate_path.is_file():
            self.problems.require(
                sha256_path(gate_path) == C0002_GATES_SHA256,
                expected_evidence,
                "C0002 gate report content drifted",
            )

        ledger_path = self.phase_dir / "checkpoints/C0002-integrator-paths.tsv"
        if ledger_path.is_file():
            _, ledger = self.read_tsv(
                ledger_path,
                self.relative(ledger_path),
                ("status", "category", "path"),
            )
            actual_paths = {row.get("path", "") for row in ledger}
            changed = self.git(
                "diff",
                "--name-only",
                f"{R12_MERGE_SHA}..{C0002_CODE_SHA}",
            ).stdout.splitlines()
            self.problems.require(
                len(ledger) == 146
                and len(actual_paths) == 146
                and actual_paths == set(changed)
                and sha256_path(ledger_path) == C0002_INTEGRATOR_LEDGER_SHA256,
                self.relative(ledger_path),
                "must exactly ledger the 146-path post-R12 integration range",
            )
        else:
            self.problems.add(self.relative(ledger_path), "missing C0002 integrator ledger")

        milestones = self.phase.get("milestones")
        milestone_map = {
            item.get("milestone_id"): item
            for item in milestones
            if isinstance(item, dict) and isinstance(item.get("milestone_id"), str)
        } if isinstance(milestones, list) else {}
        for milestone_id in C0002_MILESTONES:
            milestone = milestone_map.get(milestone_id)
            expected_checkpoint = (
                SUCCESSOR_CHECKPOINT_ID
                if milestone_id in SUCCESSOR_MILESTONES
                else C0002_CHECKPOINT_ID
            )
            self.problems.require(
                isinstance(milestone, dict)
                and milestone.get("status") == "accepted"
                and milestone.get("accepted_checkpoint_id") == expected_checkpoint,
                f"phase.json.milestones[{milestone_id}]",
                f"must be accepted at exact checkpoint {expected_checkpoint}",
            )
        self.validate_c0002_history()

    def validate_c0002_history(self) -> None:
        for commit, parents, label in (
            (R11_MERGE_SHA, R11_MERGE_PARENTS, "R11 merge"),
            (R12_MERGE_SHA, R12_MERGE_PARENTS, "R12 merge"),
        ):
            process = self.git(
                "rev-list", "--parents", "-n", "1", commit, check=False
            )
            actual = process.stdout.strip().split()
            expected = [commit, *parents]
            self.problems.require(
                process.returncode == 0 and actual == expected,
                f"C0002 {label} ancestry",
                f"expected exact commit/parent vector {expected}, found {actual}",
            )
        for ancestor, label in (
            (R11_MERGE_SHA, "R11 merge"),
            (R12_MERGE_SHA, "R12 merge"),
            (NEXT_BRANCH_FACTS["B0003"]["delivery_sha"], "R11 delivery"),
            (NEXT_BRANCH_FACTS["B0004"]["delivery_sha"], "R12 delivery"),
        ):
            ancestry = self.git(
                "merge-base", "--is-ancestor", ancestor, C0002_CODE_SHA, check=False
            )
            self.problems.require(
                ancestry.returncode == 0,
                f"C0002 {label} ancestry",
                f"{ancestor} must be an ancestor of exact C0002 code {C0002_CODE_SHA}",
            )

    def validate_branches(self) -> None:
        base_paths = self.git_tree_paths(CODE_SHA)
        scope_rules = [PathRule(path, "exact") for path in self.scope_by_path]
        live_rules: dict[str, list[PathRule]] = {}
        statuses: set[str] = set()
        for branch_id, facts in BRANCH_FACTS.items():
            path = self.phase_dir / f"branches/{branch_id}.json"
            branch = self.read_json(path, self.relative(path))
            if branch is None:
                continue
            self.branch_records[branch_id] = branch
            for key, expected in {
                "schema_version": 1,
                "record_kind": "phase_branch",
                "phase_id": PHASE_ID,
                "branch_id": branch_id,
                "lane_id": facts["lane"],
                "wave_id": facts["wave"],
                "branch_name": facts["branch"],
                "owner_id": "primary-human",
                "base_checkpoint_id": CHECKPOINT_ID,
                "base_sha": CODE_SHA,
                "baseline_projection_id": facts["projection"],
            }.items():
                self.problems.require(
                    branch.get(key) == expected,
                    f"{branch_id}.{key}",
                    f"expected {expected!r}, found {branch.get(key)!r}",
                )
            operators = branch.get("operator_ids")
            self.problems.require(
                isinstance(operators, list) and operators == [facts["operator"]],
                f"{branch_id}.operator_ids",
                f"expected exactly [{facts['operator']!r}]",
            )
            status = branch.get("status")
            allowed_statuses = (
                {"delivered"}
                if self.current_checkpoint_id == CHECKPOINT_ID
                else {"accepted", "retired"}
            )
            self.problems.require(
                status in allowed_statuses,
                f"{branch_id}.status",
                f"must be one of {sorted(allowed_statuses)} while current checkpoint is "
                f"{self.current_checkpoint_id}",
            )
            if isinstance(status, str):
                statuses.add(status)
            owned = self.parse_rules(branch.get("owned_paths"), f"{branch_id}.owned_paths")
            actual_owned = {rule.path for rule in owned if rule.match == "exact"}
            self.problems.require(
                len(owned) == len(actual_owned) and actual_owned == facts["paths"],
                f"{branch_id}.owned_paths",
                "must be exact rules for every and only selector path",
            )
            destinations = self.parse_rules(
                branch.get("destination_prefixes"), f"{branch_id}.destination_prefixes"
            )
            if not destinations:
                self.problems.add(f"{branch_id}.destination_prefixes", "must not be empty")
            if any(rule.match != "prefix" for rule in destinations):
                self.problems.add(f"{branch_id}.destination_prefixes", "all destination rules must be prefixes")
            if branch_id == "B0001":
                actual_dest = {rule.path for rule in destinations}
                self.problems.require(
                    actual_dest == R01_DESTINATIONS,
                    f"{branch_id}.destination_prefixes",
                    f"must equal exact reviewed five-prefix set; found {sorted(actual_dest)}",
                )
            forbidden = self.parse_rules(
                branch.get("forbidden_paths"), f"{branch_id}.forbidden_paths"
            )
            self.problems.require(
                PathRule(MATRIX_ALGEBRA, "exact") in forbidden,
                f"{branch_id}.forbidden_paths",
                f"must protect exact {MATRIX_ALGEBRA}",
            )
            delivery = branch.get("delivery")
            delivery_required = status in {"delivered", "accepted", "retired"}
            if not isinstance(delivery, dict):
                self.problems.add(f"{branch_id}.delivery", "expected an object")
            elif delivery_required:
                self.problems.require(
                    delivery.get("commit_sha") == facts["delivery_sha"],
                    f"{branch_id}.delivery.commit_sha",
                    f"expected immutable delivery {facts['delivery_sha']}",
                )
                report = self.artifact(delivery.get("report"), f"{branch_id}.delivery.report")
                scope_evidence = self.artifact(
                    delivery.get("scope_evidence"), f"{branch_id}.delivery.scope_evidence"
                )
                for artifact, key in (
                    (report, "delivery_report"),
                    (scope_evidence, "scope_evidence"),
                ):
                    if artifact is not None:
                        self.problems.require(
                            artifact.path == facts[key]
                            and artifact.sha256 == facts[f"{key}_sha256"],
                            f"{branch_id}.delivery.{key}",
                            f"must exactly hash-pin {facts[key]} at "
                            f"{facts[f'{key}_sha256']}",
                        )
                self.validate_delivery_scope(
                    branch_id, facts, owned, destinations, forbidden
                )
            else:
                self.problems.require(
                    delivery
                    == {"commit_sha": None, "report": None, "scope_evidence": None},
                    f"{branch_id}.delivery",
                    "planned/active state requires an empty delivery record",
                )
            self.validate_branch_lifecycle(branch_id, branch, facts, status)
            evidence = branch.get("refresh", {}).get("evidence") if isinstance(branch.get("refresh"), dict) else None
            if not isinstance(evidence, list):
                self.problems.add(f"{branch_id}.refresh.evidence", "expected hash-pinned evidence list")
            else:
                for index, item in enumerate(evidence):
                    artifact = self.artifact(item, f"{branch_id}.refresh.evidence[{index}]")
                    if artifact is not None:
                        self.branch_evidence[branch_id].append(artifact)
            selector_path = self.phase_dir / f"selectors/{facts['wave']}.tsv"
            _, selector = self.read_tsv(
                selector_path, self.relative(selector_path), SELECTOR_HEADER
            )
            expected_rows = sorted(
                ((module_from_path(item), item) for item in facts["paths"]),
                key=lambda pair: pair[0],
            )
            actual_rows = [(row.get("module", ""), row.get("path", "")) for row in selector]
            self.problems.require(
                actual_rows == expected_rows,
                self.relative(selector_path),
                "selector must contain exact sorted module/path rows",
            )
            for own in owned:
                for shared in self.shared_rules:
                    if own.intersects(shared):
                        self.problems.add(
                            f"{branch_id} owner/shared collision",
                            f"{own.path} intersects {shared.path}",
                        )
            for dest in destinations:
                folded = dest.folded
                occupied = [
                    item for item in base_paths if is_equal_or_child(item.casefold(), folded)
                ]
                if occupied:
                    self.problems.add(
                        f"{branch_id}.destination_prefixes",
                        f"destination {dest.path} is not casefold-vacant at C0000: {occupied[:5]}",
                    )
                for rule in scope_rules + self.shared_rules + forbidden:
                    if dest.intersects(rule):
                        self.problems.add(
                            f"{branch_id}.destination_prefixes",
                            f"destination {dest.path} intersects protected/scope path {rule.path}",
                        )
            live_rules[branch_id] = owned + destinations
        self.problems.require(
            len(statuses) <= 1,
            "branch pair state",
            f"B0001/B0002 must transition together, found statuses {sorted(statuses)}",
        )
        if set(live_rules) == set(BRANCH_FACTS):
            left, right = live_rules["B0001"], live_rules["B0002"]
            for one in left:
                for two in right:
                    if one.intersects(two):
                        self.problems.add(
                            "B0001/B0002 ownership",
                            f"equal-or-ancestor collision {one.path} / {two.path}",
                        )

    def validate_branch_lifecycle(
        self,
        branch_id: str,
        branch: dict[str, Any],
        facts: dict[str, Any],
        status: Any,
    ) -> None:
        integration = branch.get("integration")
        remote_ref = f"refs/heads/{facts['branch']}"
        if self.current_checkpoint_id == CHECKPOINT_ID:
            self.problems.require(
                integration
                == {
                    "method": None,
                    "accepted_checkpoint_id": None,
                    "accepted_sha": None,
                },
                f"{branch_id}.integration",
                "C0000 delivery state requires an exact empty integration record",
            )
            expected_retirement = {
                "remote_ref": remote_ref,
                "rule": "delivery_ancestor_of_green_checkpoint",
                "status": "not_due",
                "retired_at": None,
                "retired_by": None,
                "ancestry_checkpoint_id": None,
            }
            self.problems.require(
                branch.get("retirement") == expected_retirement,
                f"{branch_id}.retirement",
                f"expected exact C0000 retirement state {expected_retirement!r}",
            )
            return

        expected_integration = {
            "method": "merge",
            "accepted_checkpoint_id": SUCCESSOR_CHECKPOINT_ID,
            "accepted_sha": INTEGRATED_CODE_SHA,
        }
        self.problems.require(
            integration == expected_integration,
            f"{branch_id}.integration",
            f"expected exact true-merge integration record {expected_integration!r}",
        )
        retirement = branch.get("retirement")
        if not isinstance(retirement, dict):
            self.problems.add(f"{branch_id}.retirement", "expected an object")
            return
        exact_common = {
            "remote_ref": remote_ref,
            "rule": "delivery_ancestor_of_green_checkpoint",
        }
        for key, expected in exact_common.items():
            self.problems.require(
                retirement.get(key) == expected,
                f"{branch_id}.retirement.{key}",
                f"expected {expected!r}",
            )
        if status == "accepted":
            expected = {
                **exact_common,
                "status": "due",
                "retired_at": None,
                "retired_by": None,
                "ancestry_checkpoint_id": None,
            }
            self.problems.require(
                retirement == expected,
                f"{branch_id}.retirement",
                f"accepted branch must have exact due retirement state {expected!r}",
            )
        elif status == "retired":
            self.problems.require(
                retirement.get("status") == "retired"
                and retirement.get("retired_by") == "primary-human"
                and retirement.get("ancestry_checkpoint_id")
                == SUCCESSOR_CHECKPOINT_ID,
                f"{branch_id}.retirement",
                "retired branch must be retired by primary-human against exact C0001 ancestry",
            )
            retired_at = retirement.get("retired_at")
            self.problems.require(
                isinstance(retired_at, str)
                and RFC3339_RE.fullmatch(retired_at) is not None,
                f"{branch_id}.retirement.retired_at",
                "expected an RFC3339 retirement timestamp with timezone",
            )

    def git_tree_paths(self, revision: str) -> list[str]:
        return sorted(self.git_tree_blobs(revision))

    def git_tree_blobs(self, revision: str) -> dict[str, str]:
        if revision in self._git_tree_blobs:
            return self._git_tree_blobs[revision]
        try:
            output = self.git("ls-tree", "-r", "-z", revision).stdout
        except RuntimeError as error:
            self.problems.add("git tree", str(error))
            self._git_tree_blobs[revision] = {}
            return {}
        blobs: dict[str, str] = {}
        for record in output.split("\0"):
            if not record:
                continue
            try:
                metadata, path = record.split("\t", 1)
                _mode, kind, oid = metadata.split()
            except ValueError:
                self.problems.add("git tree", f"cannot parse ls-tree row {record!r}")
                continue
            if kind == "blob" and SHA1_RE.fullmatch(oid):
                blobs[normalize_path(path)] = oid
        self._git_tree_blobs[revision] = blobs
        return blobs

    def validate_delivery_scope(
        self,
        branch_id: str,
        facts: dict[str, Any],
        owned: list[PathRule],
        destinations: list[PathRule],
        forbidden: list[PathRule],
    ) -> None:
        delivery_sha = facts["delivery_sha"]
        ancestry = self.git(
            "merge-base", "--is-ancestor", CODE_SHA, delivery_sha, check=False
        )
        self.problems.require(
            ancestry.returncode == 0,
            f"{branch_id}.delivery",
            f"immutable delivery {delivery_sha} must descend from {CODE_SHA}",
        )
        try:
            output = self.git(
                "diff",
                "--name-status",
                "--no-renames",
                f"{CODE_SHA}..{delivery_sha}",
            ).stdout
        except RuntimeError as error:
            self.problems.add(f"{branch_id}.delivery scope", str(error))
            return
        rows: list[tuple[str, str]] = []
        for index, line in enumerate(output.splitlines(), 1):
            fields = line.split("\t")
            if len(fields) != 2 or fields[0] not in {"A", "M", "D"}:
                self.problems.add(
                    f"{branch_id}.delivery scope[{index}]",
                    f"malformed no-renames name-status row {line!r}",
                )
                continue
            rows.append((fields[0], normalize_path(fields[1])))
        self.problems.require(
            len(rows) == facts["changed_paths"],
            f"{branch_id}.delivery scope",
            f"expected {facts['changed_paths']} actual paths, found {len(rows)}",
        )
        self.problems.require(
            len({path for _, path in rows}) == len(rows),
            f"{branch_id}.delivery scope",
            "actual diff contains duplicate paths",
        )
        authorized = owned + destinations
        for status, path in rows:
            context = f"{branch_id}.delivery scope[{path}]"
            if not any(rule.matches(path) for rule in authorized):
                self.problems.add(context, "path is outside owner/destination authority")
            if any(rule.matches(path) for rule in forbidden):
                self.problems.add(context, "path is forbidden")
            if any(rule.matches(path) for rule in self.shared_rules):
                self.problems.add(context, "path is integrator-shared")
            parts = set(PurePosixPath(path).parts)
            if (
                parts & GENERATED_PARTS
                or PurePosixPath(path).suffix in GENERATED_SUFFIXES
                or path.startswith(GENERATED_PREFIXES)
            ):
                self.problems.add(context, "path is prohibited generated output")
            if status == "D":
                self.problems.add(context, "delivery may not delete a scoped path")

        evidence_path = self.root / facts["scope_evidence"]
        if branch_id == "B0001":
            try:
                evidence_text = evidence_path.read_text(encoding="utf-8")
            except OSError as error:
                self.problems.add(f"{branch_id}.delivery.scope_evidence", str(error))
            else:
                evidence_rows = re.findall(
                    r"(?m)^- `([AMD])` `([^`]+)`$", evidence_text
                )
                self.problems.require(
                    Counter(evidence_rows) == Counter(rows),
                    f"{branch_id}.delivery.scope_evidence",
                    "worker CHANGED_PATHS ledger must exactly equal the 98-row diff",
                )
        else:
            _, evidence_rows = self.read_tsv(
                evidence_path,
                self.relative(evidence_path),
                DELIVERY_SCOPE_HEADER,
            )
            parsed = [(row.get("status", ""), row.get("path", "")) for row in evidence_rows]
            self.problems.require(
                parsed == rows,
                f"{branch_id}.delivery.scope_evidence",
                "primary-human intake ledger must exactly equal the ordered 145-row diff",
            )
            categories = Counter()
            for status, path in rows:
                if path in R02_PATHS:
                    categories["owners"] += 1
                    if status != "M":
                        self.problems.add(path, "R02 owner must be modified")
                elif path.startswith("NumStabilityTest/Reorganization/R02/"):
                    categories["tests"] += 1
                elif path.startswith("docs/architecture/deliveries/R02/"):
                    categories["evidence"] += 1
                else:
                    categories["destinations"] += 1
                if path not in R02_PATHS and status != "A":
                    self.problems.add(path, "R02 non-owner delivery path must be added")
            expected = Counter(
                {"owners": 28, "destinations": 14, "tests": 63, "evidence": 40}
            )
            self.problems.require(
                categories == expected,
                f"{branch_id}.delivery scope classes",
                f"expected {dict(expected)}, found {dict(categories)}",
            )
            audit_path = self.phase_dir / "reviews/R02-intake-audit.md"
            try:
                audit = audit_path.read_text(encoding="utf-8")
            except OSError as error:
                self.problems.add(self.relative(audit_path), str(error))
            else:
                ledger_digest = sha256_path(evidence_path)
                for token in (
                    delivery_sha,
                    ledger_digest,
                    "113",
                    "145",
                    "28 owners",
                    "14 destinations",
                    "63",
                    "40",
                    "zero paths outside",
                    "142 relocated",
                    "123-row",
                    "P0002 replay records PASS",
                ):
                    if token.casefold() not in audit.casefold():
                        self.problems.add(
                            self.relative(audit_path), f"missing intake token {token!r}"
                        )

    def evidence_for(self, branch_id: str, filename: str) -> Artifact | None:
        expected = self.relative(self.phase_dir / "branches" / filename)
        matches = [item for item in self.branch_evidence.get(branch_id, []) if item.path == expected]
        if len(matches) != 1:
            self.problems.add(
                f"{branch_id}.refresh.evidence",
                f"must hash-pin exactly one {expected}",
            )
            return None
        return matches[0]

    def validate_routes_and_tests(self) -> None:
        route_header = (
            "baseline_owner_module",
            "baseline_declaration_name",
            "visibility",
            "kind",
            "baseline_order",
            "destination_module",
            "route_class",
            "normalization_decision",
        )
        private_header = ("old_private", "new_private", "destination_module")
        for branch_id, facts in BRANCH_FACTS.items():
            filenames = {
                "routes": f"{branch_id}-declaration-routes.tsv",
                "private": f"{branch_id}-private-normalization.tsv",
                "modules": f"{branch_id}-module-routes.tsv",
                "tests": f"{branch_id}-test-plan.tsv",
                "closure": f"{branch_id}-private-closure.tsv",
            }
            artifacts = {
                key: self.evidence_for(branch_id, filename)
                for key, filename in filenames.items()
            }
            route_path = self.phase_dir / "branches" / filenames["routes"]
            _, routes = self.read_tsv(
                route_path, self.relative(route_path), route_header
            )
            self.problems.require(
                len(routes) == facts["declarations"],
                self.relative(route_path),
                f"expected {facts['declarations']} exact declaration routes, found {len(routes)}",
            )
            identities = [
                (row.get("baseline_owner_module", ""), row.get("baseline_declaration_name", ""))
                for row in routes
            ]
            if len(identities) != len(set(identities)):
                self.problems.add(self.relative(route_path), "duplicate baseline declaration route")
            if identities != sorted(identities, key=lambda item: (item[0], self.numeric_order(routes, item))):
                # The exact order is independently frozen by baseline_order; only enforce
                # that baseline_order is a positive, unique integer per owner below.
                pass
            by_owner_orders: dict[str, list[int]] = defaultdict(list)
            private_names: set[str] = set()
            selector_modules = {module_from_path(path) for path in facts["paths"]}
            for index, row in enumerate(routes):
                owner = row.get("baseline_owner_module", "")
                declaration = row.get("baseline_declaration_name", "")
                destination = row.get("destination_module", "")
                decision = row.get("normalization_decision", "")
                if owner not in selector_modules:
                    self.problems.add(
                        f"{self.relative(route_path)}[{index}]",
                        f"owner {owner!r} is absent from the selector",
                    )
                if not declaration or not destination:
                    self.problems.add(
                        f"{self.relative(route_path)}[{index}]",
                        "declaration and destination_module must be nonempty",
                    )
                if not decision or DEFERRED_RE.search(decision):
                    self.problems.add(
                        f"{self.relative(route_path)}[{index}]",
                        "normalization decision must be explicit and reviewed before activation",
                    )
                try:
                    order = int(row.get("baseline_order", ""))
                    if order < 1:
                        raise ValueError
                except ValueError:
                    self.problems.add(
                        f"{self.relative(route_path)}[{index}].baseline_order",
                        "expected a positive integer",
                    )
                else:
                    by_owner_orders[owner].append(order)
                visibility = row.get("visibility", "").casefold()
                if visibility == "private":
                    private_names.add(declaration)
                elif visibility != "public":
                    self.problems.add(
                        f"{self.relative(route_path)}[{index}].visibility",
                        "expected public or private",
                    )
            self.problems.require(
                len(private_names) == facts["private"],
                self.relative(route_path),
                f"expected {facts['private']} private declaration routes, found {len(private_names)}",
            )
            for owner, orders in by_owner_orders.items():
                if len(orders) != len(set(orders)):
                    self.problems.add(self.relative(route_path), f"duplicate baseline_order in {owner}")
            private_path = self.phase_dir / "branches" / filenames["private"]
            _, private_rows = self.read_tsv(
                private_path, self.relative(private_path), private_header
            )
            self.problems.require(
                len(private_rows) == facts["private"],
                self.relative(private_path),
                f"expected {facts['private']} private normalizations, found {len(private_rows)}",
            )
            old_private = {row.get("old_private", "") for row in private_rows}
            self.problems.require(
                len(old_private) == len(private_rows) and "" not in old_private,
                self.relative(private_path),
                "old_private values must be nonempty and unique",
            )
            if old_private != private_names:
                self.problems.add(
                    self.relative(private_path),
                    f"private map must exactly cover route privates; missing={sorted(private_names-old_private)}, extra={sorted(old_private-private_names)}",
                )
            for index, row in enumerate(private_rows):
                for key in private_header:
                    value = row.get(key, "")
                    if not value or DEFERRED_RE.search(value):
                        self.problems.add(
                            f"{self.relative(private_path)}[{index}].{key}",
                            "private normalization must be explicit; no deferred worker decision",
                        )
            module_path = self.phase_dir / "branches" / filenames["modules"]
            module_header, module_rows = self.read_tsv(module_path, self.relative(module_path))
            module_column = self.choose_column(
                module_header, "module", "owner_module", "baseline_owner_module"
            )
            count_column = self.choose_column(module_header, "declaration_count", "baseline_declaration_count")
            if module_column is None or count_column is None:
                self.problems.add(
                    self.relative(module_path),
                    "module routes require module and declaration_count columns",
                )
            else:
                module_names = [row.get(module_column, "") for row in module_rows]
                self.problems.require(
                    set(module_names) == selector_modules and len(module_names) == len(selector_modules),
                    self.relative(module_path),
                    "module routes must cover every and only selector owner once",
                )
                counts: list[int] = []
                for index, row in enumerate(module_rows):
                    try:
                        value = int(row.get(count_column, ""))
                        if value < 0:
                            raise ValueError
                    except ValueError:
                        self.problems.add(
                            f"{self.relative(module_path)}[{index}].{count_column}",
                            "expected a nonnegative integer",
                        )
                    else:
                        counts.append(value)
                self.problems.require(
                    sum(counts) == facts["declarations"],
                    self.relative(module_path),
                    f"module declaration counts must sum to {facts['declarations']}",
                )
                self.problems.require(
                    sum(value == 0 for value in counts) == facts["declaration_free"],
                    self.relative(module_path),
                    f"expected {facts['declaration_free']} declaration-free modules",
                )
            closure_path = self.phase_dir / "branches" / filenames["closure"]
            closure_header, closure_rows = self.read_tsv(closure_path, self.relative(closure_path))
            closure_text = "\n".join("\t".join(row.values()) for row in closure_rows)
            self.problems.require(
                len(closure_rows) >= facts["private"],
                self.relative(closure_path),
                "full-graph private closure cannot be smaller than the selected private set",
            )
            for name in private_names:
                if name not in closure_text:
                    self.problems.add(self.relative(closure_path), f"private closure omits {name}")
            if not any("closure" in column.casefold() for column in closure_header):
                self.problems.add(self.relative(closure_path), "private closure TSV needs an explicit closure column")
            test_path = self.phase_dir / "branches" / filenames["tests"]
            test_header, test_rows = self.read_tsv(test_path, self.relative(test_path))
            class_column = self.choose_column(test_header, "test_class", "class", "plan_class")
            if class_column is None:
                self.problems.add(self.relative(test_path), "test plan requires a test_class column")
            else:
                found = {
                    row.get(class_column, "").casefold().replace("_", "-")
                    for row in test_rows
                }
                missing_classes = sorted(TEST_CLASSES - found)
                if missing_classes:
                    self.problems.add(
                        self.relative(test_path),
                        "missing test-plan class(es): " + ", ".join(missing_classes),
                    )
                for index, row in enumerate(test_rows):
                    joined = " ".join(row.values())
                    if DEFERRED_RE.search(joined):
                        self.problems.add(
                            f"{self.relative(test_path)}[{index}]",
                            "test plan may not defer design to the worker",
                        )

    @staticmethod
    def numeric_order(rows: list[dict[str, str]], identity: tuple[str, str]) -> int:
        for row in rows:
            if (
                row.get("baseline_owner_module", ""),
                row.get("baseline_declaration_name", ""),
            ) == identity:
                try:
                    return int(row.get("baseline_order", "0"))
                except ValueError:
                    return 0
        return 0

    @staticmethod
    def choose_column(header: Sequence[str], *names: str) -> str | None:
        for name in names:
            if name in header:
                return name
        return None

    def validate_projections(self) -> None:
        expected_status = (
            "active"
            if self.current_checkpoint_id == CHECKPOINT_ID
            else "retired"
        )
        for branch_id, facts in BRANCH_FACTS.items():
            projection_id = facts["projection"]
            path = self.phase_dir / f"projections/{projection_id}.json"
            projection = self.read_json(path, self.relative(path))
            if projection is None:
                continue
            for key, expected in {
                "schema_version": 1,
                "record_kind": "baseline_projection",
                "phase_id": PHASE_ID,
                "projection_id": projection_id,
                "wave_id": facts["wave"],
                "base_checkpoint_id": CHECKPOINT_ID,
                "status": expected_status,
            }.items():
                self.problems.require(
                    projection.get(key) == expected,
                    f"{projection_id}.{key}",
                    f"expected {expected!r}",
                )
            selector = projection.get("selector")
            selector_artifact = None
            if not isinstance(selector, dict) or selector.get("kind") != "module_path_tsv":
                self.problems.add(f"{projection_id}.selector", "expected module_path_tsv selector")
            else:
                selector_artifact = self.artifact(
                    selector.get("artifact"), f"{projection_id}.selector.artifact"
                )
            expected_selector = self.relative(
                self.phase_dir / f"selectors/{facts['wave']}.tsv"
            )
            if selector_artifact is not None:
                self.problems.require(
                    selector_artifact.path == expected_selector,
                    f"{projection_id}.selector.artifact.path",
                    f"expected {expected_selector}",
                )
            graph = self.artifact(
                projection.get("projection_graph"), f"{projection_id}.projection_graph"
            )
            if graph is not None:
                counts = self.parse_projection_graph(self.root / graph.path, projection_id)
                declared = projection.get("expected_counts")
                if not isinstance(declared, dict):
                    self.problems.add(f"{projection_id}.expected_counts", "expected an object")
                else:
                    for key, actual in counts.items():
                        self.problems.require(
                            declared.get(key) == actual,
                            f"{projection_id}.expected_counts.{key}",
                            f"expected actual graph count {actual}, found {declared.get(key)!r}",
                        )
                    self.problems.require(
                        counts.get("signature_edges", 0) > 0 and counts.get("body_edges", 0) > 0,
                        f"{projection_id}.projection_graph",
                        "format-2 graph must contain signature and body/proof edges",
                    )
            combined = self.artifact(
                projection.get("combined_baseline"), f"{projection_id}.combined_baseline"
            )
            if combined is not None and "C0000-combined" not in combined.path:
                self.problems.add(
                    f"{projection_id}.combined_baseline.path",
                    "projection must be rooted in C0000 combined baseline",
                )

    def parse_projection_graph(self, path: Path, context: str) -> dict[str, int]:
        declarations = 0
        signature = 0
        body = 0
        union: set[tuple[str, str]] = set()
        try:
            with gzip.open(path, "rt", encoding="utf-8", newline="") as handle:
                first = handle.readline().rstrip("\n")
                if first != "format\t2":
                    self.problems.add(context, "projection graph must start with format<TAB>2")
                for number, line in enumerate(handle, 2):
                    fields = line.rstrip("\n").split("\t")
                    if not fields or fields == [""]:
                        continue
                    if fields[0] == "declaration" and len(fields) == 5:
                        declarations += 1
                    elif fields[0] == "edge" and len(fields) == 4:
                        kind, source, target = fields[1:]
                        if kind == "signature":
                            signature += 1
                        elif kind == "body":
                            body += 1
                        else:
                            self.problems.add(context, f"unknown edge kind {kind!r} at line {number}")
                        union.add((source, target))
                    else:
                        self.problems.add(context, f"malformed format-2 row at line {number}")
        except (OSError, UnicodeError, gzip.BadGzipFile) as error:
            self.problems.add(context, f"cannot parse projection graph: {error}")
        return {
            "declarations": declarations,
            "signature_edges": signature,
            "body_edges": body,
            "union_edges": len(union),
        }

    def validate_overlap_reviews(self) -> None:
        for branch_id in BRANCH_FACTS:
            filename = f"{branch_id}-overlap-review.md"
            artifact = self.evidence_for(branch_id, filename)
            path = self.phase_dir / "branches" / filename
            try:
                text = path.read_text(encoding="utf-8")
            except OSError as error:
                self.problems.add(self.relative(path), f"cannot read overlap review: {error}")
                continue
            folded = " ".join(text.casefold().replace("_", "-").split())
            has_directions = (
                ("r01" in folded and "r02" in folded)
                and (
                    "either direction" in folded
                    or "both directions" in folded
                    or (
                        "ordered comparison" in folded
                        and folded.count("r01") >= 2
                        and folded.count("r02") >= 2
                    )
                    or ("r01 -> r02" in folded and "r02 -> r01" in folded)
                    or ("r01 → r02" in folded and "r02 → r01" in folded)
                    or ("r01-to-r02" in folded and "r02-to-r01" in folded)
                )
            )
            self.problems.require(
                has_directions,
                self.relative(path),
                "must prove R01/R02 results in both directions",
            )
            for name, tokens in OVERLAP_CATEGORIES.items():
                token_positions = [folded.find(token) for token in tokens]
                present = all(position >= 0 for position in token_positions)
                zero_near = False
                if present:
                    start = max(0, min(token_positions) - 80)
                    end = min(len(folded), max(token_positions) + 180)
                    window = folded[start:end]
                    zero_near = bool(re.search(r"\bzero\b|(?:^|\D)0(?:\D|$)", window))
                self.problems.require(
                    present and zero_near,
                    self.relative(path),
                    f"must explicitly declare zero {name} result",
                )
            for token in ("matrixalgebra", "c0000", "reviewed union"):
                if token not in folded.replace("/", "").replace(" ", "") and token not in folded:
                    self.problems.add(self.relative(path), f"missing joint-review token {token!r}")

    def validate_requests_and_postimages(self) -> None:
        request_dir = self.phase_dir / "requests"
        expected_status = (
            "active"
            if self.current_checkpoint_id == CHECKPOINT_ID
            else "applied"
        )
        request_specs = [
            ("R0001", "B0001"),
            ("R0002", "B0002"),
            ("R0002T", "B0002"),
        ]
        for request_id, branch_id in request_specs:
            path = request_dir / f"{request_id}.json"
            request = self.read_json(path, self.relative(path))
            if request is None:
                continue
            self.requests[request_id] = request
            facts = BRANCH_FACTS[branch_id]
            for key, expected in {
                "schema_version": 1,
                "record_kind": "shared_file_request",
                "phase_id": PHASE_ID,
                "request_id": request_id,
                "lane_id": facts["lane"],
                "wave_id": facts["wave"],
                "requester_id": (
                    "primary-human" if request_id == "R0002T" else facts["operator"]
                ),
                "target_checkpoint_id": CHECKPOINT_ID,
                "target_base_sha": CODE_SHA,
                "valid_through_checkpoint_id": CHECKPOINT_ID,
                "status": expected_status,
            }.items():
                self.problems.require(
                    request.get(key) == expected,
                    f"{request_id}.{key}",
                    f"expected {expected!r}, found {request.get(key)!r}",
                )
            paths = request.get("paths") if isinstance(request.get("paths"), list) else []
            if paths != sorted(set(paths)):
                self.problems.add(f"{request_id}.paths", "paths must be sorted and unique")
            self.problems.require(
                (
                    set(paths) == R0002T_PATHS
                    if request_id == "R0002T"
                    else facts["consumers"] <= set(paths)
                ),
                f"{request_id}.paths",
                (
                    f"must equal exact supplemental paths {sorted(R0002T_PATHS)}"
                    if request_id == "R0002T"
                    else "must include every required clean consumer postimage"
                ),
            )
            preimages = request.get("preimage_blobs") if isinstance(request.get("preimage_blobs"), list) else []
            parsed_preimages: dict[str, str | None] = {}
            for index, item in enumerate(preimages):
                if not isinstance(item, dict) or set(item) != {"path", "blob_oid"}:
                    self.problems.add(f"{request_id}.preimage_blobs[{index}]", "expected exactly path/blob_oid")
                    continue
                item_path, blob = item.get("path"), item.get("blob_oid")
                if isinstance(item_path, str) and (blob is None or isinstance(blob, str)):
                    parsed_preimages[item_path] = blob
                else:
                    self.problems.add(f"{request_id}.preimage_blobs[{index}]", "invalid preimage")
            self.problems.require(
                set(parsed_preimages) == set(paths),
                f"{request_id}.preimage_blobs",
                "preimage paths must exactly equal request paths",
            )
            for item_path, expected_blob in parsed_preimages.items():
                actual_blob = self.git_blob(CODE_SHA, item_path)
                self.problems.require(
                    actual_blob == expected_blob,
                    f"{request_id}.preimage_blobs[{item_path}]",
                    f"expected C0000 blob {actual_blob!r}, found {expected_blob!r}",
                )
            patch = self.artifact(request.get("patch"), f"{request_id}.patch")
            patch_path: Path | None = None
            if patch is not None:
                expected_patch = self.relative(request_dir / f"{request_id}.patch")
                self.problems.require(
                    patch.path == expected_patch,
                    f"{request_id}.patch.path",
                    f"expected {expected_patch}",
                )
                patch_path = self.root / patch.path
            post_name = f"{request_id}-postimages.tsv"
            post_path = request_dir / post_name
            post_digest = sha256_path(post_path) if post_path.is_file() else None
            post_header, post_rows = self.read_tsv(post_path, self.relative(post_path))
            postimages = self.validate_postimage_rows(
                post_header,
                post_rows,
                self.relative(post_path),
                set(paths),
                "postimage_sha256",
            )
            if patch_path is not None:
                self.materialize_patch_postimages(
                    request_id,
                    patch_path,
                    set(paths),
                    postimages,
                )
            rationale = request.get("rationale") if isinstance(request.get("rationale"), str) else ""
            if post_digest is not None:
                self.problems.require(
                    post_digest in rationale.upper(),
                    f"{request_id}.rationale",
                    f"must hash-pin {post_name} at SHA-256 {post_digest}",
                )
            self.validate_request_lifecycle(request_id, request)
        expected_links = {
            "B0001": ["R0001"],
            "B0002": ["R0002", "R0002T"],
        }
        for branch_id, expected in expected_links.items():
            branch = self.branch_records.get(branch_id, {})
            linked = (
                branch.get("shared_request_ids")
                if isinstance(branch.get("shared_request_ids"), list)
                else []
            )
            self.problems.require(
                linked == expected,
                f"{branch_id}.shared_request_ids",
                f"expected exactly {expected}",
            )
        if {"R0001", "R0002"} <= set(self.requests):
            first, second = self.requests["R0001"], self.requests["R0002"]
            first_pre = {item["path"]: item["blob_oid"] for item in first.get("preimage_blobs", []) if isinstance(item, dict) and "path" in item and "blob_oid" in item}
            second_pre = {item["path"]: item["blob_oid"] for item in second.get("preimage_blobs", []) if isinstance(item, dict) and "path" in item and "blob_oid" in item}
            overlap = set(first_pre) & set(second_pre)
            expected_overlap = {"NumStability/Algorithms.lean"}
            self.problems.require(
                overlap == expected_overlap,
                "request overlap",
                "independent request overlap must be exactly "
                f"{sorted(expected_overlap)}, found {sorted(overlap)}",
            )
            for path in overlap:
                if first_pre[path] != second_pre[path]:
                    self.problems.add(
                        "request overlap",
                        f"{path} is not independently based on the same C0000 blob",
                    )
            union_path = request_dir / "R0001-R0002-union-postimages.tsv"
            header, rows = self.read_tsv(union_path, self.relative(union_path))
            union_expected = set(first.get("paths", [])) | set(second.get("paths", []))
            union_postimages = self.validate_postimage_rows(
                header,
                rows,
                self.relative(union_path),
                union_expected,
                "union_postimage_sha256",
            )
            union_patch_path = request_dir / "R0001-R0002-union.patch"
            union_patch_context = self.relative(union_patch_path)
            union_patch_digest = (
                sha256_path(union_patch_path) if union_patch_path.is_file() else ""
            )
            if not union_patch_digest:
                self.problems.add(
                    union_patch_context,
                    "missing reviewed-union patch rooted at exact C0000",
                )
            else:
                self.materialize_patch_postimages(
                    "R0001-R0002 reviewed union",
                    union_patch_path,
                    union_expected,
                    union_postimages,
                )
                for branch_id in ("B0001", "B0002"):
                    matches = [
                        item
                        for item in self.branch_evidence.get(branch_id, [])
                        if item.path == union_patch_context
                    ]
                    self.problems.require(
                        len(matches) == 1
                        and matches[0].sha256 == union_patch_digest,
                        f"{branch_id}.refresh.evidence",
                        "must hash-pin exactly one reviewed-union patch at SHA-256 "
                        f"{union_patch_digest}",
                    )
            review_path = request_dir / "R0001-R0002-union-review.md"
            review = ""
            try:
                review = review_path.read_text(encoding="utf-8")
            except OSError as error:
                self.problems.add(self.relative(review_path), f"cannot read union review: {error}")
            else:
                folded = " ".join(review.casefold().split())
                for token in ("r0001", "r0002", "c0000", CODE_SHA):
                    if token.casefold() not in folded:
                        self.problems.add(self.relative(review_path), f"missing union evidence token {token!r}")
                self.problems.require(
                    ("reviewed union" in folded)
                    or ("union postimage" in folded and "reconcil" in folded),
                    self.relative(review_path),
                    "must explicitly record the reviewed/reconciled union postimage",
                )
                for path in sorted(overlap):
                    if path.casefold() not in folded:
                        self.problems.add(self.relative(review_path), f"union review omits overlap path {path}")
                if union_patch_digest and union_patch_digest.casefold() not in folded:
                    self.problems.add(
                        self.relative(review_path),
                        "union review must hash-pin reviewed-union patch SHA-256 "
                        f"{union_patch_digest}",
                    )
            union_manifest_digest = sha256_path(union_path) if union_path.is_file() else ""
            review_digest = sha256_path(review_path) if review_path.is_file() else ""
            for request_id in ("R0001", "R0002"):
                request = self.requests[request_id]
                rationale = str(request.get("rationale", "")).upper()
                for digest, label in (
                    (union_manifest_digest, "union postimages"),
                    (review_digest, "union review"),
                    (union_patch_digest, "reviewed-union patch"),
                ):
                    if digest and digest not in rationale:
                        self.problems.add(
                            f"{request_id}.rationale",
                            f"must hash-pin {label} SHA-256 {digest}",
                        )

    def validate_request_lifecycle(
        self, request_id: str, request: dict[str, Any]
    ) -> None:
        context = f"{request_id}.resolution"
        resolution = request.get("resolution")
        empty = {
            "checkpoint_id": None,
            "commit_sha": None,
            "reason": None,
            "resolved_at": None,
            "resolved_by": None,
            "validation_evidence": [],
        }
        if self.current_checkpoint_id == CHECKPOINT_ID:
            self.problems.require(
                resolution == empty,
                context,
                f"active C0000 request requires exact empty resolution {empty!r}",
            )
            return
        if not isinstance(resolution, dict):
            self.problems.add(context, "expected an object")
            return
        self.problems.require(
            set(resolution) == set(empty),
            context,
            f"expected exactly the resolution keys {sorted(empty)}",
        )
        for key, expected in {
            "checkpoint_id": SUCCESSOR_CHECKPOINT_ID,
            "commit_sha": INTEGRATED_CODE_SHA,
            "resolved_by": "primary-human",
        }.items():
            self.problems.require(
                resolution.get(key) == expected,
                f"{context}.{key}",
                f"expected {expected!r}, found {resolution.get(key)!r}",
            )
        reason = resolution.get("reason")
        self.problems.require(
            isinstance(reason, str) and bool(reason.strip()),
            f"{context}.reason",
            "applied request requires a nonempty reason",
        )
        resolved_at = resolution.get("resolved_at")
        self.problems.require(
            isinstance(resolved_at, str)
            and RFC3339_RE.fullmatch(resolved_at) is not None,
            f"{context}.resolved_at",
            "expected an RFC3339 resolution timestamp with timezone",
        )
        evidence = resolution.get("validation_evidence")
        artifacts: list[Artifact] = []
        if not isinstance(evidence, list) or not evidence:
            self.problems.add(
                f"{context}.validation_evidence",
                "applied request requires nonempty hash-pinned validation evidence",
            )
        else:
            for index, item in enumerate(evidence):
                artifact = self.artifact(
                    item, f"{context}.validation_evidence[{index}]"
                )
                if artifact is not None:
                    artifacts.append(artifact)
        expected_path, expected_digest = REQUEST_RESOLUTION_EVIDENCE[request_id]
        matches = [
            artifact
            for artifact in artifacts
            if artifact.path == expected_path
            and artifact.sha256 == expected_digest
        ]
        self.problems.require(
            len(matches) == 1,
            f"{context}.validation_evidence",
            "must contain exactly one immutable acceptance pin "
            f"{expected_path} at SHA-256 {expected_digest}",
        )

    def validate_postimage_rows(
        self,
        header: Sequence[str],
        rows: list[dict[str, str]],
        context: str,
        expected_paths: set[str],
        post_column: str,
        *,
        base_sha: str = CODE_SHA,
        base_label: str = "C0000",
    ) -> dict[str, str]:
        path_column = self.choose_column(header, "path", "shared_path")
        pre_column = self.choose_column(header, "preimage_blob_oid", "c0000_blob_oid", "base_blob_oid")
        pre_sha_column = self.choose_column(header, "preimage_sha256")
        if (
            path_column is None
            or pre_column is None
            or pre_sha_column is None
            or post_column not in header
        ):
            self.problems.add(
                context,
                "postimage TSV requires path, base preimage blob/SHA-256, and exact "
                f"{post_column} column",
            )
            return {}
        paths = [row.get(path_column, "") for row in rows]
        self.problems.require(
            paths == sorted(set(paths)),
            context,
            "postimage rows must be sorted and unique by path",
        )
        self.problems.require(
            set(paths) == expected_paths,
            context,
            f"postimage paths must equal request union; missing={sorted(expected_paths-set(paths))}, extra={sorted(set(paths)-expected_paths)}",
        )
        postimages: dict[str, str] = {}
        actual_preimages = {
            path: self.git_blob(base_sha, path) for path in paths if path
        }
        preimage_payloads = self.git_blob_payloads(
            (
                oid
                for oid in actual_preimages.values()
                if isinstance(oid, str)
            ),
            f"{context} {base_label} preimages",
        )
        for index, row in enumerate(rows):
            path = row.get(path_column, "")
            actual_pre = actual_preimages.get(path)
            self.problems.require(
                row.get(pre_column) == (actual_pre or "-"),
                f"{context}[{index}].{pre_column}",
                f"expected {base_label} blob {(actual_pre or '-')!r}",
            )
            if actual_pre is not None:
                preimage = preimage_payloads.get(actual_pre)
                if preimage is None:
                    self.problems.add(
                        f"{context}[{index}].{pre_sha_column}",
                        f"cannot read {base_label} preimage blob {actual_pre}",
                    )
                else:
                    actual_pre_sha = hashlib.sha256(preimage).hexdigest().upper()
                    self.problems.require(
                        row.get(pre_sha_column, "").upper() == actual_pre_sha,
                        f"{context}[{index}].{pre_sha_column}",
                        f"expected {base_label} content SHA-256 {actual_pre_sha}",
                    )
            post_digest = row.get(post_column, "")
            if not SHA256_RE.fullmatch(post_digest):
                self.problems.add(
                    f"{context}[{index}].{post_column}",
                    "postimage SHA-256 must be exactly 64 hexadecimal characters",
                )
            elif path:
                postimages[path] = post_digest.upper()
        return postimages

    def git_blob(self, revision: str, path: str) -> str | None:
        return self.git_tree_blobs(revision).get(normalize_path(path))

    def materialize_patch_postimages(
        self,
        context: str,
        patch: Path,
        expected_paths: set[str],
        expected_sha256: dict[str, str],
        *,
        base_sha: str = CODE_SHA,
        base_label: str = "C0000",
        unidiff_zero: bool = False,
    ) -> None:
        """Apply *patch* to a disposable base index, hash results, then reverse."""

        with tempfile.TemporaryDirectory(prefix="completion-phase-index-") as directory:
            index = Path(directory) / "index"
            env = os.environ.copy()
            env["GIT_INDEX_FILE"] = str(index)
            read = self.git("read-tree", base_sha, check=False, env=env)
            if read.returncode:
                self.problems.add(
                    f"{context}.patch",
                    f"cannot initialize exact {base_label} index: {read.stderr.strip()}",
                )
                return
            apply_mode = ["--unidiff-zero"] if unidiff_zero else []
            applied = self.git(
                "apply",
                "--cached",
                *apply_mode,
                "--whitespace=nowarn",
                str(patch),
                check=False,
                env=env,
            )
            if applied.returncode:
                self.problems.add(
                    f"{context}.patch",
                    f"does not materialize independently from exact {base_label}: "
                    f"{applied.stderr.strip() or applied.stdout.strip()}",
                )
                return
            changed_process = self.git(
                "diff",
                "--cached",
                "--name-only",
                "-z",
                base_sha,
                "--",
                check=False,
                env=env,
            )
            if changed_process.returncode:
                self.problems.add(
                    f"{context}.patch",
                    "cannot enumerate materialized postimages: "
                    f"{changed_process.stderr.strip() or changed_process.stdout.strip()}",
                )
                return
            changed_paths = {
                normalize_path(path)
                for path in changed_process.stdout.split("\0")
                if path
            }
            self.problems.require(
                changed_paths == expected_paths,
                f"{context}.patch",
                "materialized changed paths must exactly equal manifest paths; "
                f"missing={sorted(expected_paths-changed_paths)}, "
                f"extra={sorted(changed_paths-expected_paths)}",
            )
            self.problems.require(
                set(expected_sha256) == expected_paths,
                f"{context}.postimages",
                "must provide exactly one valid SHA-256 for every manifest path; "
                f"missing={sorted(expected_paths-set(expected_sha256))}, "
                f"extra={sorted(set(expected_sha256)-expected_paths)}",
            )
            staged_process = self.git(
                "ls-files", "--stage", "-z", check=False, env=env
            )
            staged: dict[str, str] = {}
            if staged_process.returncode:
                self.problems.add(
                    f"{context}.postimages",
                    "cannot enumerate materialized stage-0 blobs: "
                    f"{staged_process.stderr.strip() or staged_process.stdout.strip()}",
                )
            else:
                for record in staged_process.stdout.split("\0"):
                    if not record:
                        continue
                    try:
                        metadata, staged_path = record.split("\t", 1)
                        _mode, oid, stage = metadata.split()
                    except ValueError:
                        self.problems.add(
                            f"{context}.postimages",
                            f"cannot parse staged index row {record!r}",
                        )
                        continue
                    if stage == "0" and SHA1_RE.fullmatch(oid):
                        staged[normalize_path(staged_path)] = oid
            materialized_payloads = self.git_blob_payloads(
                (
                    staged[path]
                    for path in expected_paths
                    if path in staged
                ),
                f"{context} materialized postimages",
                env=env,
            )
            for path in sorted(expected_paths):
                expected = expected_sha256.get(path)
                if expected is None:
                    continue
                oid = staged.get(path)
                if oid is None:
                    self.problems.add(
                        f"{context}.postimages[{path}]",
                        "cannot resolve materialized stage-0 blob",
                    )
                    continue
                content = materialized_payloads.get(oid)
                if content is None:
                    self.problems.add(
                        f"{context}.postimages[{path}]",
                        f"cannot read materialized blob {oid}",
                    )
                    continue
                actual = hashlib.sha256(content).hexdigest().upper()
                self.problems.require(
                    actual == expected,
                    f"{context}.postimages[{path}]",
                    f"materialized SHA-256 mismatch: manifest {expected}, actual {actual}",
                )
            reversed_patch = self.git(
                "apply",
                "--cached",
                "--reverse",
                *apply_mode,
                "--whitespace=nowarn",
                str(patch),
                check=False,
                env=env,
            )
            if reversed_patch.returncode:
                self.problems.add(
                    f"{context}.patch",
                    f"cannot reverse replay to exact {base_label}: "
                    f"{reversed_patch.stderr.strip() or reversed_patch.stdout.strip()}",
                )
                return
            remaining = self.git(
                "diff",
                "--cached",
                "--name-only",
                "-z",
                base_sha,
                "--",
                check=False,
                env=env,
            )
            if remaining.returncode:
                self.problems.add(
                    f"{context}.patch",
                    f"cannot verify reverse replay against exact {base_label}: "
                    f"{remaining.stderr.strip() or remaining.stdout.strip()}",
                )
            else:
                remaining_paths = {
                    normalize_path(path)
                    for path in remaining.stdout.split("\0")
                    if path
                }
                self.problems.require(
                    not remaining_paths,
                    f"{context}.patch",
                    f"reverse replay must restore exact {base_label}; "
                    f"remaining={sorted(remaining_paths)}",
                )

    def validate_next_wave_controls(self) -> None:
        """Validate the distinct C0001-rooted R11/R12 control epoch.

        The generic phase checker owns the reusable B/P/R schemas.  This
        method supplies the completion-phase ratchets: the exact graph-derived
        pair, its same-base evidence, and its independently replayable shared
        postimages.  It intentionally does not alter the historical B0001 /
        B0002 validation above.
        """

        context = "C0001-rooted R11/R12 controls"
        self.problems.require(
            self.current_checkpoint_id
            in {SUCCESSOR_CHECKPOINT_ID, C0002_CHECKPOINT_ID},
            context,
            "next-wave controls require current checkpoint C0001 or C0002",
        )

        inventory_path = self.phase_dir / "checkpoints/C0001-inventory.tsv"
        if inventory_path.is_file():
            self.problems.require(
                sha256_path(inventory_path) == NEXT_INVENTORY_SHA256,
                self.relative(inventory_path),
                f"expected exact C0001 inventory SHA-256 {NEXT_INVENTORY_SHA256}",
            )
        _, inventory = self.read_tsv(
            inventory_path, self.relative(inventory_path), SCOPE_HEADER
        )
        self.problems.require(
            len(inventory) == SUCCESSOR_METRICS["production_modules"],
            self.relative(inventory_path),
            f"expected {SUCCESSOR_METRICS['production_modules']} C0001 rows",
        )
        inventory_by_path = {row.get("path", ""): row for row in inventory}
        self.problems.require(
            len(inventory_by_path) == len(inventory),
            self.relative(inventory_path),
            "C0001 inventory paths must be unique",
        )

        baseline_path = self.phase_dir / "baselines/C0001-combined.json"
        if baseline_path.is_file():
            self.problems.require(
                sha256_path(baseline_path) == NEXT_COMBINED_BASELINE_SHA256,
                self.relative(baseline_path),
                "C0001 combined baseline SHA-256 drifted from the activated epoch",
            )
        else:
            self.problems.add(self.relative(baseline_path), "missing C0001 combined baseline")

        self.validate_next_wave_authority()
        base_tree_paths = self.git_tree_paths(INTEGRATED_CODE_SHA)
        branch_rules: dict[str, list[PathRule]] = {}
        protected_consumers: dict[str, set[str]] = {}
        statuses: set[str] = set()

        for branch_id, facts in NEXT_BRANCH_FACTS.items():
            branch_path = self.phase_dir / f"branches/{branch_id}.json"
            branch = self.read_json(branch_path, self.relative(branch_path))
            if branch is None:
                continue
            self.branch_records[branch_id] = branch
            for key, expected in {
                "schema_version": 1,
                "record_kind": "phase_branch",
                "phase_id": PHASE_ID,
                "branch_id": branch_id,
                "lane_id": facts["lane"],
                "wave_id": facts["wave"],
                "branch_name": facts["branch"],
                "owner_id": "primary-human",
                "base_checkpoint_id": SUCCESSOR_CHECKPOINT_ID,
                "base_sha": INTEGRATED_CODE_SHA,
                "baseline_projection_id": facts["projection"],
            }.items():
                self.problems.require(
                    branch.get(key) == expected,
                    f"{branch_id}.{key}",
                    f"expected {expected!r}, found {branch.get(key)!r}",
                )
            self.problems.require(
                branch.get("operator_ids") == [facts["operator"]],
                f"{branch_id}.operator_ids",
                f"expected exactly [{facts['operator']!r}]",
            )
            status = branch.get("status")
            allowed_statuses = next_branch_statuses(self.current_checkpoint_id)
            self.problems.require(
                status in allowed_statuses,
                f"{branch_id}.status",
                f"expected one of {sorted(allowed_statuses)} at "
                f"{self.current_checkpoint_id}",
            )
            if isinstance(status, str):
                statuses.add(status)

            refresh = branch.get("refresh")
            if not isinstance(refresh, dict):
                self.problems.add(f"{branch_id}.refresh", "expected an object")
                evidence: Any = []
            else:
                self.problems.require(
                    refresh.get("reviewed_checkpoint_id") == SUCCESSOR_CHECKPOINT_ID
                    and refresh.get("decision") == "current",
                    f"{branch_id}.refresh",
                    "must record a current review against exact C0001",
                )
                evidence = refresh.get("evidence")
            self.branch_evidence[branch_id] = []
            if not isinstance(evidence, list):
                self.problems.add(
                    f"{branch_id}.refresh.evidence", "expected a hash-pinned list"
                )
            else:
                evidence_paths: list[str] = []
                for index, item in enumerate(evidence):
                    artifact = self.artifact(
                        item, f"{branch_id}.refresh.evidence[{index}]"
                    )
                    if artifact is not None:
                        self.branch_evidence[branch_id].append(artifact)
                        evidence_paths.append(artifact.path)
                self.problems.require(
                    len(evidence_paths) == len(set(evidence_paths)),
                    f"{branch_id}.refresh.evidence",
                    "refresh evidence paths must be unique",
                )

            self.require_next_evidence(
                branch_id,
                self.relative(baseline_path),
                NEXT_COMBINED_BASELINE_SHA256,
            )
            self.require_next_evidence(
                branch_id,
                self.relative(inventory_path),
                NEXT_INVENTORY_SHA256,
            )

            selector_path = self.phase_dir / f"selectors/{facts['wave']}.tsv"
            _, selector_rows = self.read_tsv(
                selector_path, self.relative(selector_path), SELECTOR_HEADER
            )
            expected_selector = sorted(
                (
                    (row.get("module", ""), row.get("path", ""))
                    for row in inventory
                    if row.get("wave_id") == facts["wave"]
                ),
                key=lambda item: (item[0], item[1]),
            )
            actual_selector = [
                (row.get("module", ""), row.get("path", ""))
                for row in selector_rows
            ]
            self.problems.require(
                actual_selector == expected_selector
                and len(actual_selector) == facts["owned_count"],
                self.relative(selector_path),
                "selector must equal the exact sorted C0001 inventory wave",
            )
            for module, selected_path in expected_selector:
                row = inventory_by_path.get(selected_path, {})
                self.problems.require(
                    module_from_path(selected_path) == module,
                    f"{facts['wave']} selector[{selected_path}]",
                    "module/path identity mismatch",
                )
                self.problems.require(
                    row.get("phase_scope") == "in_scope"
                    and row.get("lane_id") == facts["lane"]
                    and row.get("wave_id") == facts["wave"],
                    f"{facts['wave']} selector[{selected_path}]",
                    "C0001 scope row must be in-scope on the exact immutable lane/wave",
                )
                actual_blob = self.git_blob(INTEGRATED_CODE_SHA, selected_path)
                self.problems.require(
                    actual_blob == row.get("base_blob_oid"),
                    f"{facts['wave']} selector[{selected_path}]",
                    f"C0001 blob mismatch: inventory {row.get('base_blob_oid')!r}, Git {actual_blob!r}",
                )

            owned = self.parse_rules(branch.get("owned_paths"), f"{branch_id}.owned_paths")
            expected_owned = {path for _, path in expected_selector}
            self.problems.require(
                len(owned) == len(expected_owned)
                and all(rule.match == "exact" for rule in owned)
                and {rule.path for rule in owned} == expected_owned,
                f"{branch_id}.owned_paths",
                "must contain exact rules for every and only selector path",
            )

            destinations = self.parse_rules(
                branch.get("destination_prefixes"),
                f"{branch_id}.destination_prefixes",
            )
            self.problems.require(
                all(rule.match == "prefix" for rule in destinations)
                and {rule.path for rule in destinations} == facts["destinations"],
                f"{branch_id}.destination_prefixes",
                f"must equal exact reviewed set {sorted(facts['destinations'])}",
            )
            for index, destination in enumerate(destinations):
                occupied = [
                    path
                    for path in base_tree_paths
                    if is_equal_or_child(path.casefold(), destination.folded)
                ]
                self.problems.require(
                    not occupied,
                    f"{branch_id}.destination_prefixes[{destination.path}]",
                    f"must be casefold-vacant at C0001; found {occupied[:5]}",
                )
                for other in destinations[index + 1 :]:
                    if destination.intersects(other):
                        self.problems.add(
                            f"{branch_id}.destination_prefixes",
                            f"internal equal/ancestor collision {destination.path} / {other.path}",
                        )

            forbidden = self.parse_rules(
                branch.get("forbidden_paths"), f"{branch_id}.forbidden_paths"
            )
            actual_forbidden_exact = {
                rule.path for rule in forbidden if rule.match == "exact"
            }
            actual_forbidden_prefix = {
                rule.path for rule in forbidden if rule.match == "prefix"
            }
            expected_forbidden_exact = set(inventory_by_path) - expected_owned
            peer_id = "B0004" if branch_id == "B0003" else "B0003"
            expected_forbidden_prefix = (
                set(NEXT_PROTECTED_PREFIXES)
                | set(NEXT_BRANCH_FACTS[peer_id]["destinations"])
            )
            self.problems.require(
                actual_forbidden_exact == expected_forbidden_exact
                and len(actual_forbidden_exact) == facts["forbidden_exact"],
                f"{branch_id}.forbidden_paths",
                "exact forbidden rules must be the exhaustive C0001 inventory complement",
            )
            self.problems.require(
                actual_forbidden_prefix == expected_forbidden_prefix
                and len(actual_forbidden_prefix) == facts["forbidden_prefix"],
                f"{branch_id}.forbidden_paths",
                "prefix forbidden rules must be guarded infrastructure plus every peer destination",
            )
            self.problems.require(
                len(forbidden)
                == facts["forbidden_exact"] + facts["forbidden_prefix"],
                f"{branch_id}.forbidden_paths",
                "forbidden rule count drifted",
            )
            for rule in owned + destinations:
                for shared in self.shared_rules:
                    if rule.intersects(shared):
                        self.problems.add(
                            f"{branch_id} authority",
                            f"worker rule {rule.path} intersects integrator-shared {shared.path}",
                        )

            self.validate_next_branch_lifecycle(branch_id, branch, facts)
            declarations = self.validate_next_projection(
                branch_id,
                facts,
                {module for module, _ in expected_selector},
            )
            protected_consumers[branch_id] = self.validate_next_routes_and_tests(
                branch_id,
                facts,
                expected_selector,
                declarations,
            )
            self.validate_next_overlap_review(branch_id, facts)
            branch_rules[branch_id] = owned + destinations

        self.problems.require(
            len(statuses) == 1,
            "B0003/B0004 state",
            "branches must transition synchronously through "
            "planned/active/delivered/accepted/retired; "
            f"found {sorted(statuses)}",
        )
        if set(branch_rules) == set(NEXT_BRANCH_FACTS):
            for left in branch_rules["B0003"]:
                for right in branch_rules["B0004"]:
                    if left.intersects(right):
                        self.problems.add(
                            "B0003/B0004 authority",
                            f"equal-or-ancestor collision {left.path} / {right.path}",
                        )
        state = next(iter(statuses)) if len(statuses) == 1 else None
        self.validate_next_joint_evidence(state)
        self.validate_next_requests(protected_consumers)

    def validate_next_wave_authority(self) -> None:
        authority = self.phase.get("authority")
        lanes = authority.get("lanes") if isinstance(authority, dict) else None
        lane = None
        if isinstance(lanes, list):
            matches = [
                item
                for item in lanes
                if isinstance(item, dict) and item.get("lane_id") == "claude-lane"
            ]
            if len(matches) == 1:
                lane = matches[0]
        expected_operators = next_lane_operators(self.current_checkpoint_id)
        self.problems.require(
            isinstance(lane, dict)
            and lane.get("owner_id") == "primary-human"
            and lane.get("operator_ids") == expected_operators,
            "phase.json.authority.lanes[claude-lane]",
            "R11/R12 authority must use the reviewed C0001 expansion and "
            "restore the single Claude operator at C0002",
        )

    def require_next_evidence(
        self, branch_id: str, path: str, expected_sha256: str | None = None
    ) -> Artifact | None:
        normalized = normalize_path(path)
        matches = [
            artifact
            for artifact in self.branch_evidence.get(branch_id, [])
            if artifact.path == normalized
        ]
        self.problems.require(
            len(matches) == 1,
            f"{branch_id}.refresh.evidence",
            f"must hash-pin exactly one {normalized}",
        )
        if len(matches) != 1:
            return None
        artifact = matches[0]
        if expected_sha256 is not None:
            self.problems.require(
                artifact.sha256 == expected_sha256,
                f"{branch_id}.refresh.evidence[{normalized}]",
                f"expected exact SHA-256 {expected_sha256}",
            )
        return artifact

    def validate_next_branch_lifecycle(
        self, branch_id: str, branch: dict[str, Any], facts: dict[str, Any]
    ) -> None:
        status = branch.get("status")
        report_path, report_sha256 = facts["delivery_report"]
        scope_path, scope_sha256 = facts["delivery_scope"]
        delivery_required = status in {"delivered", "accepted", "retired"}
        expected_delivery = (
            {
                "commit_sha": facts["delivery_sha"],
                "report": {"path": report_path, "sha256": report_sha256},
                "scope_evidence": {"path": scope_path, "sha256": scope_sha256},
            }
            if delivery_required
            else {"commit_sha": None, "report": None, "scope_evidence": None}
        )
        self.problems.require(
            branch.get("delivery") == expected_delivery,
            f"{branch_id}.delivery",
            f"expected exact {status} delivery record {expected_delivery!r}",
        )
        if delivery_required:
            ancestry = self.git(
                "merge-base",
                "--is-ancestor",
                facts["delivery_sha"],
                "HEAD",
                check=False,
            )
            self.problems.require(
                ancestry.returncode == 0,
                f"{branch_id}.delivery.commit_sha",
                "delivered tip must be an ancestor of the integrated tree",
            )
            parent_vector = self.git(
                "rev-list",
                "--parents",
                "-n",
                "1",
                facts["delivery_sha"],
                check=False,
            ).stdout.strip().split()
            self.problems.require(
                parent_vector == [facts["delivery_sha"], INTEGRATED_CODE_SHA],
                f"{branch_id}.delivery.commit_sha",
                "delivery must be a direct child of exact C0001",
            )
            for label, path, expected_sha256 in (
                ("report", report_path, report_sha256),
                ("scope_evidence", scope_path, scope_sha256),
            ):
                artifact_path = self.root / path
                self.problems.require(
                    artifact_path.is_file()
                    and sha256_path(artifact_path) == expected_sha256,
                    f"{branch_id}.delivery.{label}",
                    f"expected exact delivery artifact {path} at {expected_sha256}",
                )
        expected_integration = (
            {
                "method": "merge",
                "accepted_checkpoint_id": C0002_CHECKPOINT_ID,
                "accepted_sha": C0002_CODE_SHA,
            }
            if status in {"accepted", "retired"}
            else {
                "method": None,
                "accepted_checkpoint_id": None,
                "accepted_sha": None,
            }
        )
        self.problems.require(
            branch.get("integration") == expected_integration,
            f"{branch_id}.integration",
            f"expected exact {status} integration record {expected_integration!r}",
        )
        retirement_status = next_retirement_status(str(status))
        expected_retirement = {
            "remote_ref": f"refs/heads/{facts['branch']}",
            "rule": "delivery_ancestor_of_green_checkpoint",
            "status": retirement_status,
            "retired_at": None if status != "retired" else branch.get("retirement", {}).get("retired_at"),
            "retired_by": None if status != "retired" else "primary-human",
            "ancestry_checkpoint_id": None if status != "retired" else C0002_CHECKPOINT_ID,
        }
        self.problems.require(
            branch.get("retirement") == expected_retirement,
            f"{branch_id}.retirement",
            f"expected exact {status} retirement state {expected_retirement!r}",
        )
        if status == "retired":
            retired_at = branch.get("retirement", {}).get("retired_at")
            self.problems.require(
                isinstance(retired_at, str)
                and RFC3339_RE.fullmatch(retired_at) is not None,
                f"{branch_id}.retirement.retired_at",
                "retired branch requires an RFC3339 retirement timestamp",
            )

    def validate_next_projection(
        self,
        branch_id: str,
        facts: dict[str, Any],
        selector_modules: set[str],
    ) -> dict[tuple[str, str], tuple[str, str]]:
        projection_id = facts["projection"]
        path = self.phase_dir / f"projections/{projection_id}.json"
        projection = self.read_json(path, self.relative(path))
        if projection is None:
            return {}
        for key, expected in {
            "schema_version": 1,
            "record_kind": "baseline_projection",
            "phase_id": PHASE_ID,
            "projection_id": projection_id,
            "wave_id": facts["wave"],
            "base_checkpoint_id": SUCCESSOR_CHECKPOINT_ID,
            "status": next_projection_status(self.current_checkpoint_id),
            "superseded_by": None,
        }.items():
            self.problems.require(
                projection.get(key) == expected,
                f"{projection_id}.{key}",
                f"expected {expected!r}, found {projection.get(key)!r}",
            )

        selector = projection.get("selector")
        selector_artifact = None
        if not isinstance(selector, dict) or selector.get("kind") != "module_path_tsv":
            self.problems.add(f"{projection_id}.selector", "expected module_path_tsv")
        else:
            selector_artifact = self.artifact(
                selector.get("artifact"), f"{projection_id}.selector.artifact"
            )
        expected_selector_path = self.relative(
            self.phase_dir / f"selectors/{facts['wave']}.tsv"
        )
        if selector_artifact is not None:
            self.problems.require(
                selector_artifact.path == expected_selector_path
                and selector_artifact.sha256 == facts["selector_sha256"],
                f"{projection_id}.selector.artifact",
                f"must pin {expected_selector_path} at {facts['selector_sha256']}",
            )

        graph = self.artifact(
            projection.get("projection_graph"), f"{projection_id}.projection_graph"
        )
        expected_graph_path = self.relative(
            self.phase_dir / f"projections/{projection_id}.tsv.gz"
        )
        declarations: dict[tuple[str, str], tuple[str, str]] = {}
        if graph is not None:
            self.problems.require(
                graph.path == expected_graph_path
                and graph.sha256 == facts["projection_sha256"],
                f"{projection_id}.projection_graph",
                f"must pin exact deterministic projection {facts['projection_sha256']}",
            )
            counts = self.parse_projection_graph(self.root / graph.path, projection_id)
            self.problems.require(
                counts == facts["counts"]
                and projection.get("expected_counts") == facts["counts"],
                f"{projection_id}.expected_counts",
                f"expected exact graph counts {facts['counts']}, found {counts}",
            )
            try:
                with gzip.open(self.root / graph.path, "rb") as handle:
                    payload_digest = hashlib.sha256(handle.read()).hexdigest().upper()
            except (OSError, gzip.BadGzipFile) as error:
                self.problems.add(projection_id, f"cannot hash projection payload: {error}")
            else:
                self.problems.require(
                    payload_digest == facts["projection_payload_sha256"],
                    f"{projection_id}.projection_graph",
                    "decompressed format-2 payload SHA-256 drifted",
                )
            declarations = self.parse_projection_declarations(
                self.root / graph.path, projection_id
            )
            declaration_owners = {owner for owner, _ in declarations}
            self.problems.require(
                declaration_owners <= selector_modules,
                f"{projection_id}.projection_graph",
                f"declaration owner outside selector: {sorted(declaration_owners-selector_modules)}",
            )

        combined = self.artifact(
            projection.get("combined_baseline"), f"{projection_id}.combined_baseline"
        )
        expected_combined = self.relative(
            self.phase_dir / "baselines/C0001-combined.json"
        )
        if combined is not None:
            self.problems.require(
                combined.path == expected_combined
                and combined.sha256 == NEXT_COMBINED_BASELINE_SHA256,
                f"{projection_id}.combined_baseline",
                "projection must use the exact official C0001 combined baseline",
            )

        checker = projection.get("checker")
        if not isinstance(checker, dict):
            self.problems.add(f"{projection_id}.checker", "expected an object")
        else:
            checker_artifact = self.artifact(
                checker.get("artifact"), f"{projection_id}.checker.artifact"
            )
            expected_checker_path = "tools/architecture/check_completion_phase_projection.py"
            if checker_artifact is not None:
                self.problems.require(
                    checker_artifact.path == expected_checker_path
                    and checker_artifact.sha256 == NEXT_PROJECTION_CHECKER_SHA256,
                    f"{projection_id}.checker.artifact",
                    "must pin the immutable private-aware projection checker",
                )
            production_prefixes = {
                destination
                for destination in facts["destinations"]
                if destination.startswith("NumStability/")
            }
            expected_arguments = sorted(
                [f"--allow-module={module}" for module in selector_modules]
                + [
                    f"--allow-prefix={module_from_path(prefix)}."
                    for prefix in production_prefixes
                ]
                + [
                    "--candidate=<candidate-format2.tsv>",
                    f"--private-map-sha256={facts['private_map_sha256']}",
                    "--private-map="
                    + self.relative(
                        self.phase_dir
                        / f"branches/{branch_id}-private-normalization.tsv"
                    ),
                    f"--projection-sha256={facts['projection_sha256']}",
                    f"--projection={expected_graph_path}",
                ]
            )
            self.problems.require(
                checker.get("arguments") == expected_arguments,
                f"{projection_id}.checker.arguments",
                "checker arguments must exactly bind owners, destinations, private map, and projection",
            )
        return declarations

    def parse_projection_declarations(
        self, path: Path, context: str
    ) -> dict[tuple[str, str], tuple[str, str]]:
        declarations: dict[tuple[str, str], tuple[str, str]] = {}
        try:
            with gzip.open(path, "rt", encoding="utf-8", newline="") as handle:
                if handle.readline().rstrip("\n") != "format\t2":
                    return declarations
                for number, line in enumerate(handle, 2):
                    fields = line.rstrip("\n").split("\t")
                    if not fields or fields[0] != "declaration" or len(fields) != 5:
                        continue
                    _, name, owner, kind, visibility = fields
                    identity = (owner, name)
                    if identity in declarations:
                        self.problems.add(
                            context,
                            f"duplicate declaration identity {identity!r} at line {number}",
                        )
                    declarations[identity] = (kind, visibility)
        except (OSError, UnicodeError, gzip.BadGzipFile) as error:
            self.problems.add(context, f"cannot parse projection declarations: {error}")
        return declarations

    def validate_next_routes_and_tests(
        self,
        branch_id: str,
        facts: dict[str, Any],
        selector: list[tuple[str, str]],
        declarations: dict[tuple[str, str], tuple[str, str]],
    ) -> set[str]:
        route_header = (
            "baseline_owner_module",
            "baseline_declaration_name",
            "visibility",
            "kind",
            "baseline_order",
            "destination_module",
            "route_class",
            "normalization_decision",
        )
        module_header = (
            "owner_module",
            "path",
            "declaration_count",
            "destination_modules",
            "compatibility_action",
            "review_status",
        )
        private_header = ("old_private", "new_private", "destination_module")
        closure_header = (
            "declaration",
            "owner_module",
            "visibility",
            "selected_owner",
            "closure_role",
        )
        test_header = ("test_class", "target", "purpose")
        filenames = {
            "routes": f"{branch_id}-declaration-routes.tsv",
            "modules": f"{branch_id}-module-routes.tsv",
            "private": f"{branch_id}-private-normalization.tsv",
            "closure": f"{branch_id}-private-closure.tsv",
            "tests": f"{branch_id}-test-plan.tsv",
        }
        evidence: dict[str, Artifact | None] = {}
        for key, filename in filenames.items():
            expected_digest = None
            if key == "private":
                expected_digest = facts["private_map_sha256"]
            elif key == "closure":
                expected_digest = facts["private_closure_sha256"]
            evidence[key] = self.require_next_evidence(
                branch_id,
                self.relative(self.phase_dir / "branches" / filename),
                expected_digest,
            )

        route_path = self.phase_dir / "branches" / filenames["routes"]
        _, routes = self.read_tsv(
            route_path, self.relative(route_path), route_header
        )
        self.problems.require(
            len(routes) == facts["counts"]["declarations"],
            self.relative(route_path),
            f"expected {facts['counts']['declarations']} declaration routes",
        )
        route_identities = [
            (
                row.get("baseline_owner_module", ""),
                row.get("baseline_declaration_name", ""),
            )
            for row in routes
        ]
        self.problems.require(
            len(route_identities) == len(set(route_identities)),
            self.relative(route_path),
            "declaration route identities must be unique",
        )
        self.problems.require(
            set(route_identities) == set(declarations),
            self.relative(route_path),
            "routes must cover every and only projected declaration identity",
        )

        orders: dict[str, list[int]] = defaultdict(list)
        per_owner_destinations: dict[str, set[str]] = defaultdict(set)
        destination_counts: Counter[str] = Counter()
        private_routes: dict[str, tuple[str, str]] = {}
        retained = 0
        relocated = 0
        ordered_keys: list[tuple[str, int]] = []
        for index, row in enumerate(routes):
            row_context = f"{self.relative(route_path)}[{index}]"
            owner = row.get("baseline_owner_module", "")
            name = row.get("baseline_declaration_name", "")
            destination = row.get("destination_module", "")
            expected_declaration = declarations.get((owner, name))
            if expected_declaration is not None:
                expected_kind, expected_visibility = expected_declaration
                self.problems.require(
                    row.get("kind") == expected_kind
                    and row.get("visibility") == expected_visibility,
                    row_context,
                    "kind/visibility must equal the frozen format-2 declaration",
                )
            try:
                order = int(row.get("baseline_order", ""))
                if order < 1:
                    raise ValueError
            except ValueError:
                self.problems.add(
                    f"{row_context}.baseline_order", "expected a positive integer"
                )
                order = 0
            orders[owner].append(order)
            ordered_keys.append((owner, order))
            per_owner_destinations[owner].add(destination)
            destination_counts[destination] += 1

            if destination == owner:
                retained += 1
                expected_class = "source_retained_outlier"
                expected_decision = "approved_retained_outlier"
            else:
                relocated += 1
                expected_class = (
                    "reusable"
                    if destination.startswith("NumStability.Algorithms.")
                    else "source"
                )
                expected_decision = (
                    "preserve_public_name"
                    if branch_id == "B0004"
                    else "approved_owner_block_route"
                )
            self.problems.require(
                row.get("route_class") == expected_class,
                f"{row_context}.route_class",
                f"expected {expected_class!r}",
            )
            decision = row.get("normalization_decision", "")
            self.problems.require(
                decision == expected_decision and DEFERRED_RE.search(decision) is None,
                f"{row_context}.normalization_decision",
                f"expected exact reviewed decision {expected_decision!r}",
            )
            if row.get("visibility") == "private":
                if name in private_routes:
                    self.problems.add(row_context, f"duplicate private name {name}")
                private_routes[name] = (owner, destination)

        self.problems.require(
            ordered_keys == sorted(ordered_keys),
            self.relative(route_path),
            "routes must be sorted by owner and frozen baseline order",
        )
        for owner, owner_orders in orders.items():
            self.problems.require(
                owner_orders == list(range(1, len(owner_orders) + 1)),
                self.relative(route_path),
                f"{owner} baseline_order must be the exact contiguous 1-based sequence",
            )
        self.problems.require(
            dict(destination_counts) == facts["destination_counts"],
            self.relative(route_path),
            f"destination declaration counts must equal {facts['destination_counts']}",
        )
        self.problems.require(
            relocated == facts["relocated"] and retained == facts["retained"],
            self.relative(route_path),
            f"expected relocated/retained {facts['relocated']}/{facts['retained']}, found {relocated}/{retained}",
        )
        self.problems.require(
            len(private_routes) == facts["private"],
            self.relative(route_path),
            f"expected {facts['private']} projected private declarations",
        )

        selector_by_module = {module: selected_path for module, selected_path in selector}
        projected_counts = Counter(owner for owner, _ in declarations)
        module_path = self.phase_dir / "branches" / filenames["modules"]
        _, module_rows = self.read_tsv(
            module_path, self.relative(module_path), module_header
        )
        module_names = [row.get("owner_module", "") for row in module_rows]
        self.problems.require(
            module_names == sorted(selector_by_module)
            and set(module_names) == set(selector_by_module),
            self.relative(module_path),
            "module routes must cover every selector owner once in sorted order",
        )
        declaration_free = 0
        for index, row in enumerate(module_rows):
            row_context = f"{self.relative(module_path)}[{index}]"
            owner = row.get("owner_module", "")
            self.problems.require(
                row.get("path") == selector_by_module.get(owner),
                f"{row_context}.path",
                "module route path must equal the selector path",
            )
            try:
                count = int(row.get("declaration_count", ""))
            except ValueError:
                self.problems.add(
                    f"{row_context}.declaration_count", "expected an integer"
                )
                count = -1
            expected_count = projected_counts.get(owner, 0)
            self.problems.require(
                count == expected_count,
                f"{row_context}.declaration_count",
                f"expected exact projected count {expected_count}",
            )
            if count == 0:
                declaration_free += 1
            listed_destinations = split_values(row.get("destination_modules", ""))
            self.problems.require(
                listed_destinations == sorted(set(listed_destinations)),
                f"{row_context}.destination_modules",
                "destination modules must be sorted and unique",
            )
            routed_destinations = per_owner_destinations.get(owner, set())
            if routed_destinations:
                self.problems.require(
                    set(listed_destinations) == routed_destinations,
                    f"{row_context}.destination_modules",
                    f"must equal routed destinations {sorted(routed_destinations)}",
                )
            else:
                self.problems.require(
                    set(listed_destinations) <= set(facts["destination_counts"]),
                    f"{row_context}.destination_modules",
                    "declaration-free wrapper may name only a reviewed declaration destination",
                )
            action = row.get("compatibility_action", "")
            self.problems.require(
                bool(action.strip()) and DEFERRED_RE.search(action) is None,
                f"{row_context}.compatibility_action",
                "compatibility action must be explicit before activation",
            )
            self.problems.require(
                row.get("review_status") == "approved_before_activation",
                f"{row_context}.review_status",
                "expected approved_before_activation",
            )
        self.problems.require(
            declaration_free == facts["declaration_free"],
            self.relative(module_path),
            f"expected {facts['declaration_free']} declaration-free owners",
        )

        private_path = self.phase_dir / "branches" / filenames["private"]
        _, private_rows = self.read_tsv(
            private_path, self.relative(private_path), private_header
        )
        self.problems.require(
            len(private_rows) == facts["private"],
            self.relative(private_path),
            f"expected exact {facts['private']}-row private map",
        )
        old_names = [row.get("old_private", "") for row in private_rows]
        new_names = [row.get("new_private", "") for row in private_rows]
        self.problems.require(
            old_names == sorted(private_routes)
            and set(old_names) == set(private_routes),
            self.relative(private_path),
            "private map must exactly cover projected private names in sorted order",
        )
        self.problems.require(
            len(new_names) == len(set(new_names)),
            self.relative(private_path),
            "normalized private names must be unique",
        )
        for index, row in enumerate(private_rows):
            row_context = f"{self.relative(private_path)}[{index}]"
            old = row.get("old_private", "")
            new = row.get("new_private", "")
            owner, destination = private_routes.get(old, ("", ""))
            self.problems.require(
                row.get("destination_module") == destination,
                f"{row_context}.destination_module",
                f"expected routed destination {destination!r}",
            )
            self.problems.require(
                bool(old) and bool(new) and DEFERRED_RE.search(" ".join(row.values())) is None,
                row_context,
                "private normalization must be complete and non-deferred",
            )
            if destination == owner:
                self.problems.require(
                    new == old,
                    f"{row_context}.new_private",
                    "retained-owner private identity must remain exact",
                )
            elif destination:
                self.problems.require(
                    new != old and f".{destination}." in new,
                    f"{row_context}.new_private",
                    "relocated private must receive only the reviewed owner-prefix rewrite",
                )

        closure_path = self.phase_dir / "branches" / filenames["closure"]
        _, closure_rows = self.read_tsv(
            closure_path, self.relative(closure_path), closure_header
        )
        self.problems.require(
            len(closure_rows) == facts["private_closure_rows"],
            self.relative(closure_path),
            f"expected exact {facts['private_closure_rows']}-row private closure",
        )
        closure_names = [row.get("declaration", "") for row in closure_rows]
        self.problems.require(
            len(closure_names) == len(set(closure_names)),
            self.relative(closure_path),
            "private closure declarations must be unique",
        )
        seeds = {
            row.get("declaration", "")
            for row in closure_rows
            if row.get("closure_role") == "private_seed"
        }
        self.problems.require(
            seeds == set(private_routes),
            self.relative(closure_path),
            "private closure seeds must exactly equal the private-normalization domain",
        )
        for index, row in enumerate(closure_rows):
            row_context = f"{self.relative(closure_path)}[{index}]"
            role = row.get("closure_role")
            expected_visibility = "private" if role == "private_seed" else "public"
            self.problems.require(
                role in {"private_seed", "reverse_dependent"}
                and row.get("visibility") == expected_visibility
                and row.get("selected_owner") in {"yes", "no"},
                row_context,
                "closure rows require typed seed/dependent role, visibility, and owner flag",
            )
            if role == "private_seed":
                expected_owner = private_routes.get(row.get("declaration", ""), ("", ""))[0]
                self.problems.require(
                    row.get("owner_module") == expected_owner,
                    f"{row_context}.owner_module",
                    f"private seed owner must be {expected_owner!r}",
                )

        test_path = self.phase_dir / "branches" / filenames["tests"]
        _, test_rows = self.read_tsv(
            test_path, self.relative(test_path), test_header
        )
        self.problems.require(
            len(test_rows) == facts["test_rows"],
            self.relative(test_path),
            f"expected exact {facts['test_rows']}-row test plan",
        )
        test_pairs = [
            (row.get("test_class", ""), row.get("target", ""))
            for row in test_rows
        ]
        self.problems.require(
            test_pairs == sorted(test_pairs) and len(test_pairs) == len(set(test_pairs)),
            self.relative(test_path),
            "test class/target pairs must be sorted and unique",
        )
        class_counts = Counter(row.get("test_class", "") for row in test_rows)
        self.problems.require(
            dict(class_counts) == facts["test_classes"],
            self.relative(test_path),
            f"expected exact test-class counts {facts['test_classes']}",
        )
        unique_targets = {row.get("target", "") for row in test_rows}
        self.problems.require(
            len(unique_targets) == facts["test_targets"],
            self.relative(test_path),
            f"expected {facts['test_targets']} distinct test targets",
        )
        by_class = {
            name: {
                row.get("target", "")
                for row in test_rows
                if row.get("test_class") == name
            }
            for name in facts["test_classes"]
        }
        relocated_destinations = {
            destination
            for (owner, _), _metadata in declarations.items()
            for destination in per_owner_destinations.get(owner, set())
            if destination != owner
        }
        self.problems.require(
            by_class.get("old_only", set()) == set(selector_by_module),
            self.relative(test_path),
            "old-only tests must cover every and only historical selector owner",
        )
        for test_class in ("canonical_only", "focused"):
            self.problems.require(
                by_class.get(test_class, set()) == relocated_destinations,
                self.relative(test_path),
                f"{test_class} tests must cover every and only relocated destination",
            )
        for index, row in enumerate(test_rows):
            purpose = row.get("purpose", "")
            self.problems.require(
                bool(purpose.strip()) and DEFERRED_RE.search(purpose) is None,
                f"{self.relative(test_path)}[{index}].purpose",
                "test purpose must be explicit and non-deferred",
            )
        return by_class.get("protected_consumer", set())

    def validate_next_overlap_review(
        self, branch_id: str, facts: dict[str, Any]
    ) -> None:
        path = self.phase_dir / f"branches/{branch_id}-overlap-review.md"
        self.require_next_evidence(branch_id, self.relative(path))
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as error:
            self.problems.add(self.relative(path), f"cannot read overlap review: {error}")
            return
        folded = " ".join(text.casefold().replace("_", "-").split())
        required = (
            "r11",
            "r12",
            "both directions",
            "owner",
            "destination",
            "direct",
            "transitive",
            "signature",
            "body",
            INTEGRATED_CODE_SHA,
            facts["selector_sha256"].casefold(),
            facts["projection_sha256"].casefold(),
        )
        for token in required:
            if token not in folded:
                self.problems.add(self.relative(path), f"missing overlap token {token!r}")
        self.problems.require(
            "zero" in folded or re.search(r"(?:^|\D)0(?:\D|$)", folded) is not None,
            self.relative(path),
            "must state the zero cross-wave results explicitly",
        )
        self.problems.require(
            DEFERRED_RE.search(text) is None,
            self.relative(path),
            "overlap review may not defer an activation decision",
        )

    def validate_next_joint_evidence(self, state: str | None) -> None:
        authorization_path = self.phase_dir / "reviews/R11-R12-operator-authorization.md"
        overlap_path = self.phase_dir / "reviews/R11-R12-overlap-facts.md"
        projection_replay_path = (
            self.phase_dir / "reviews/R11-R12-projection-replay.md"
        )
        import_path = self.phase_dir / "reviews/R11-shared-import-replacements.tsv"
        union_patch_path = self.phase_dir / "requests/R0003-R0004-union.patch"
        for branch_id in NEXT_BRANCH_FACTS:
            self.require_next_evidence(
                branch_id,
                self.relative(authorization_path),
                NEXT_OPERATOR_AUTHORIZATION_SHA256,
            )
            self.require_next_evidence(
                branch_id,
                self.relative(overlap_path),
                NEXT_OVERLAP_FACTS_SHA256,
            )
            self.require_next_evidence(
                branch_id,
                self.relative(projection_replay_path),
                NEXT_PROJECTION_REPLAY_SHA256,
            )
            self.require_next_evidence(
                branch_id,
                self.relative(union_patch_path),
                NEXT_UNION_PATCH_SHA256,
            )
        self.require_next_evidence(
            "B0003", self.relative(import_path), NEXT_IMPORT_REVIEW_SHA256
        )

        try:
            authorization = authorization_path.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as error:
            self.problems.add(
                self.relative(authorization_path),
                f"cannot read operator authorization: {error}",
            )
        else:
            folded = " ".join(authorization.casefold().split())
            for token in (
                "primary-human",
                "claude-lane",
                "claude-local",
                "codex-local",
                "b0004",
                "r12",
                "temporary",
                INTEGRATED_CODE_SHA,
            ):
                if token not in folded:
                    self.problems.add(
                        self.relative(authorization_path),
                        f"missing authority-expansion token {token!r}",
                    )
            self.problems.require(
                "expire" in folded,
                self.relative(authorization_path),
                "temporary operator expansion must state its expiry",
            )

        try:
            overlap = overlap_path.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as error:
            self.problems.add(
                self.relative(overlap_path), f"cannot read joint overlap facts: {error}"
            )
        else:
            folded = " ".join(overlap.casefold().split())
            for token in (
                "r11",
                "r12",
                "c0001",
                INTEGRATED_CODE_SHA,
                NEXT_BRANCH_FACTS["B0003"]["selector_sha256"].casefold(),
                NEXT_BRANCH_FACTS["B0004"]["selector_sha256"].casefold(),
                NEXT_BRANCH_FACTS["B0003"]["projection_sha256"].casefold(),
                NEXT_BRANCH_FACTS["B0004"]["projection_sha256"].casefold(),
                NEXT_BRANCH_FACTS["B0003"]["request_path_sha256"].casefold(),
                NEXT_BRANCH_FACTS["B0004"]["request_path_sha256"].casefold(),
            ):
                if token not in folded:
                    self.problems.add(
                        self.relative(overlap_path),
                        f"missing exact joint-overlap token {token!r}",
                    )
            for category in (
                "owner",
                "destination",
                "direct",
                "transitive",
                "signature",
                "body",
            ):
                self.problems.require(
                    category in folded,
                    self.relative(overlap_path),
                    f"joint overlap evidence omits {category}",
                )
            self.problems.require(
                "both ways" in folded or "both directions" in folded,
                self.relative(overlap_path),
                "joint overlap evidence must cover both directed comparisons",
            )

        try:
            projection_replay = projection_replay_path.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as error:
            self.problems.add(
                self.relative(projection_replay_path),
                f"cannot read same-candidate projection replay: {error}",
            )
        else:
            folded = " ".join(projection_replay.casefold().split())
            compact = folded.replace(",", "")
            for token in (
                "primary-human",
                "c0001",
                INTEGRATED_CODE_SHA,
                NEXT_CANDIDATE_SHA256.casefold(),
                NEXT_PROJECTION_CHECKER_SHA256.casefold(),
                NEXT_BRANCH_FACTS["B0003"]["projection_sha256"].casefold(),
                NEXT_BRANCH_FACTS["B0004"]["projection_sha256"].casefold(),
                NEXT_BRANCH_FACTS["B0003"]["private_map_sha256"].casefold(),
                "same exact",
                "passed",
            ):
                if token not in folded:
                    self.problems.add(
                        self.relative(projection_replay_path),
                        f"missing projection-replay token {token!r}",
                    )
            for token in ("56903", "649259", "1477", "34", "15172", "18056", "80", "133"):
                if token not in compact:
                    self.problems.add(
                        self.relative(projection_replay_path),
                        f"missing exact projection-replay count {token}",
                    )

        if state in {"active", "delivered", "accepted", "retired"}:
            activation_path = self.phase_dir / "reviews/R11-R12-activation.md"
            pins = [
                self.require_next_evidence(branch_id, self.relative(activation_path))
                for branch_id in NEXT_BRANCH_FACTS
            ]
            self.problems.require(
                all(pin is not None for pin in pins)
                and len({pin.sha256 for pin in pins if pin is not None}) == 1,
                "B0003/B0004 activation evidence",
                "activated branches must pin the same activation review SHA-256",
            )
            try:
                activation = activation_path.read_text(encoding="utf-8")
            except (OSError, UnicodeError) as error:
                self.problems.add(
                    self.relative(activation_path), f"cannot read activation review: {error}"
                )
            else:
                folded = " ".join(activation.casefold().split())
                for token in (
                    "primary-human",
                    "c0001",
                    INTEGRATED_CODE_SHA,
                    "b0003",
                    "b0004",
                    "r11",
                    "r12",
                    "active",
                ):
                    if token not in folded:
                        self.problems.add(
                            self.relative(activation_path),
                            f"missing activation token {token!r}",
                        )

    def validate_next_requests(
        self, protected_consumers: dict[str, set[str]]
    ) -> None:
        request_dir = self.phase_dir / "requests"
        controls = {
            "NumStabilityTest.lean",
            "docs/architecture/COMPATIBILITY.md",
            "docs/architecture/layout-exceptions.json",
            "docs/architecture/tiers.json",
        }
        expected_paths = {
            "R0003": {
                path_from_module(module)
                for module in protected_consumers.get("B0003", set())
            }
            | controls,
            "R0004": set(NEXT_REQUEST_OVERLAP),
        }
        request_to_branch = {"R0003": "B0003", "R0004": "B0004"}
        parsed_preimages: dict[str, dict[str, str | None]] = {}
        created_at: set[str] = set()

        for request_id, branch_id in request_to_branch.items():
            facts = NEXT_BRANCH_FACTS[branch_id]
            path = request_dir / f"{request_id}.json"
            request = self.read_json(path, self.relative(path))
            if request is None:
                continue
            self.requests[request_id] = request
            expected_request_status = next_request_status(self.current_checkpoint_id)
            for key, expected in {
                "schema_version": 1,
                "record_kind": "shared_file_request",
                "phase_id": PHASE_ID,
                "request_id": request_id,
                "lane_id": facts["lane"],
                "wave_id": facts["wave"],
                "requester_id": "primary-human",
                "target_checkpoint_id": SUCCESSOR_CHECKPOINT_ID,
                "target_base_sha": INTEGRATED_CODE_SHA,
                "valid_through_checkpoint_id": SUCCESSOR_CHECKPOINT_ID,
                "status": expected_request_status,
                "depends_on": [],
                "blocks": [facts["wave"]],
                "supersedes": None,
                "superseded_by": None,
            }.items():
                self.problems.require(
                    request.get(key) == expected,
                    f"{request_id}.{key}",
                    f"expected {expected!r}, found {request.get(key)!r}",
                )
            timestamp = request.get("created_at")
            self.problems.require(
                isinstance(timestamp, str)
                and RFC3339_RE.fullmatch(timestamp) is not None,
                f"{request_id}.created_at",
                "expected an RFC3339 authority timestamp",
            )
            if isinstance(timestamp, str):
                created_at.add(timestamp)

            paths = request.get("paths")
            if not isinstance(paths, list) or not all(
                isinstance(item, str) for item in paths
            ):
                self.problems.add(f"{request_id}.paths", "expected a string list")
                paths = []
            wanted = expected_paths[request_id]
            self.problems.require(
                paths == sorted(wanted)
                and len(paths) == facts["request_paths"],
                f"{request_id}.paths",
                f"must equal exact reviewed {facts['request_paths']}-path set",
            )
            self.problems.require(
                path_list_sha256(paths) == facts["request_path_sha256"],
                f"{request_id}.paths",
                f"newline path-list SHA-256 must be {facts['request_path_sha256']}",
            )
            if expected_request_status == "active":
                shared_exact = {
                    rule.path for rule in self.shared_rules if rule.match == "exact"
                }
                self.problems.require(
                    set(paths) <= shared_exact,
                    f"{request_id}.paths",
                    "active request paths missing exact shared reservations: "
                    f"{sorted(set(paths)-shared_exact)}",
                )

            expected_preimages = []
            preimage_map: dict[str, str | None] = {}
            for affected in sorted(paths):
                oid = self.git_blob(INTEGRATED_CODE_SHA, affected)
                expected_preimages.append({"blob_oid": oid, "path": affected})
                preimage_map[affected] = oid
            self.problems.require(
                request.get("preimage_blobs") == expected_preimages,
                f"{request_id}.preimage_blobs",
                "must exactly record sorted C0001 blob OIDs for every requested path",
            )
            parsed_preimages[request_id] = preimage_map

            patch = self.artifact(request.get("patch"), f"{request_id}.patch")
            expected_patch_path = self.relative(request_dir / f"{request_id}.patch")
            patch_path: Path | None = None
            if patch is not None:
                self.problems.require(
                    patch.path == expected_patch_path
                    and patch.sha256 == facts["request_patch_sha256"],
                    f"{request_id}.patch",
                    f"must pin {expected_patch_path} at {facts['request_patch_sha256']}",
                )
                patch_path = self.root / patch.path

            post_path = request_dir / f"{request_id}-postimages.tsv"
            post_header, post_rows = self.read_tsv(
                post_path,
                self.relative(post_path),
                (
                    "path",
                    "preimage_blob_oid",
                    "preimage_sha256",
                    "postimage_sha256",
                ),
            )
            postimages = self.validate_postimage_rows(
                post_header,
                post_rows,
                self.relative(post_path),
                set(paths),
                "postimage_sha256",
                base_sha=INTEGRATED_CODE_SHA,
                base_label=SUCCESSOR_CHECKPOINT_ID,
            )
            if post_path.is_file():
                self.problems.require(
                    sha256_path(post_path) == facts["request_postimages_sha256"],
                    self.relative(post_path),
                    f"expected exact postimage SHA-256 {facts['request_postimages_sha256']}",
                )
            if patch_path is not None:
                self.materialize_patch_postimages(
                    request_id,
                    patch_path,
                    set(paths),
                    postimages,
                    base_sha=INTEGRATED_CODE_SHA,
                    base_label=SUCCESSOR_CHECKPOINT_ID,
                )

            if expected_request_status == "active":
                expected_resolution = {
                    "checkpoint_id": None,
                    "commit_sha": None,
                    "reason": None,
                    "resolved_at": None,
                    "resolved_by": None,
                    "validation_evidence": [],
                }
            else:
                resolution = request.get("resolution")
                resolved_at = (
                    resolution.get("resolved_at")
                    if isinstance(resolution, dict)
                    else None
                )
                reason = (
                    resolution.get("reason")
                    if isinstance(resolution, dict)
                    else None
                )
                expected_resolution = {
                    "checkpoint_id": C0002_CHECKPOINT_ID,
                    "commit_sha": C0002_CODE_SHA,
                    "reason": reason,
                    "resolved_at": resolved_at,
                    "resolved_by": "primary-human",
                    "validation_evidence": [
                        {
                            "path": self.relative(
                                request_dir / "R0003-R0004-union-review.md"
                            ),
                            "sha256": NEXT_UNION_REVIEW_SHA256,
                        }
                    ],
                }
                self.problems.require(
                    isinstance(reason, str) and bool(reason.strip()),
                    f"{request_id}.resolution.reason",
                    "applied request requires a nonempty reviewed-union reason",
                )
                self.problems.require(
                    isinstance(resolved_at, str)
                    and RFC3339_RE.fullmatch(resolved_at) is not None,
                    f"{request_id}.resolution.resolved_at",
                    "applied request requires an RFC3339 resolution timestamp",
                )
            self.problems.require(
                request.get("resolution") == expected_resolution,
                f"{request_id}.resolution",
                f"expected exact {expected_request_status} resolution",
            )
            rationale = str(request.get("rationale", "")).upper()
            for digest, label in (
                (facts["request_path_sha256"], "path list"),
                (facts["request_patch_sha256"], "request patch"),
                (facts["request_postimages_sha256"], "request postimages"),
                (NEXT_UNION_PATCH_SHA256, "reviewed union patch"),
                (NEXT_UNION_POSTIMAGES_SHA256, "reviewed union postimages"),
                (NEXT_UNION_REVIEW_SHA256, "reviewed union review"),
            ):
                if digest not in rationale:
                    self.problems.add(
                        f"{request_id}.rationale",
                        f"must hash-pin {label} SHA-256 {digest}",
                    )
            self.problems.require(
                INTEGRATED_CODE_SHA.upper() in rationale,
                f"{request_id}.rationale",
                "must name the exact C0001 code preimage",
            )

            branch = self.branch_records.get(branch_id, {})
            self.problems.require(
                branch.get("shared_request_ids") == [request_id],
                f"{branch_id}.shared_request_ids",
                f"expected exactly [{request_id!r}]",
            )

        self.problems.require(
            len(created_at) == 1,
            "R0003/R0004 created_at",
            "the independently generated request pair must share one authority timestamp",
        )
        if set(parsed_preimages) == {"R0003", "R0004"}:
            first, second = parsed_preimages["R0003"], parsed_preimages["R0004"]
            overlap = set(first) & set(second)
            self.problems.require(
                overlap == NEXT_REQUEST_OVERLAP,
                "R0003/R0004 request overlap",
                f"expected exact three-path intersection {sorted(NEXT_REQUEST_OVERLAP)}, found {sorted(overlap)}",
            )
            for affected in overlap:
                self.problems.require(
                    first[affected] == second[affected],
                    "R0003/R0004 request overlap",
                    f"{affected} is not rooted in the same C0001 preimage blob",
                )

        union_paths = expected_paths["R0003"] | expected_paths["R0004"]
        union_patch_path = request_dir / "R0003-R0004-union.patch"
        union_manifest_path = request_dir / "R0003-R0004-union-postimages.tsv"
        union_review_path = request_dir / "R0003-R0004-union-review.md"
        for artifact_path, expected_digest, label in (
            (union_patch_path, NEXT_UNION_PATCH_SHA256, "union patch"),
            (
                union_manifest_path,
                NEXT_UNION_POSTIMAGES_SHA256,
                "union postimages",
            ),
            (union_review_path, NEXT_UNION_REVIEW_SHA256, "union review"),
        ):
            if not artifact_path.is_file():
                self.problems.add(self.relative(artifact_path), f"missing {label}")
            else:
                self.problems.require(
                    sha256_path(artifact_path) == expected_digest,
                    self.relative(artifact_path),
                    f"expected exact SHA-256 {expected_digest}",
                )

        union_header, union_rows = self.read_tsv(
            union_manifest_path,
            self.relative(union_manifest_path),
            (
                "path",
                "preimage_blob_oid",
                "preimage_sha256",
                "union_postimage_sha256",
                "source_requests",
            ),
        )
        union_postimages = self.validate_postimage_rows(
            union_header,
            union_rows,
            self.relative(union_manifest_path),
            union_paths,
            "union_postimage_sha256",
            base_sha=INTEGRATED_CODE_SHA,
            base_label=SUCCESSOR_CHECKPOINT_ID,
        )
        for index, row in enumerate(union_rows):
            affected = row.get("path", "")
            expected_sources = (
                "R0003+R0004" if affected in NEXT_REQUEST_OVERLAP else "R0003"
            )
            self.problems.require(
                row.get("source_requests") == expected_sources,
                f"{self.relative(union_manifest_path)}[{index}].source_requests",
                f"expected exact provenance {expected_sources!r}",
            )
        if union_patch_path.is_file():
            self.materialize_patch_postimages(
                "R0003/R0004 reviewed union",
                union_patch_path,
                union_paths,
                union_postimages,
                base_sha=INTEGRATED_CODE_SHA,
                base_label=SUCCESSOR_CHECKPOINT_ID,
            )

        try:
            union_review = union_review_path.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as error:
            self.problems.add(
                self.relative(union_review_path), f"cannot read union review: {error}"
            )
            union_review = ""
        folded_review = " ".join(union_review.casefold().split())
        for token in (
            "r0003",
            "r0004",
            "c0001",
            INTEGRATED_CODE_SHA,
            NEXT_BRANCH_FACTS["B0003"]["request_path_sha256"].casefold(),
            NEXT_BRANCH_FACTS["B0004"]["request_path_sha256"].casefold(),
            NEXT_BRANCH_FACTS["B0003"]["request_patch_sha256"].casefold(),
            NEXT_BRANCH_FACTS["B0004"]["request_patch_sha256"].casefold(),
            NEXT_UNION_PATCH_SHA256.casefold(),
            NEXT_UNION_POSTIMAGES_SHA256.casefold(),
            NEXT_IMPORT_REVIEW_SHA256.casefold(),
            "reverse",
        ):
            if token not in folded_review:
                self.problems.add(
                    self.relative(union_review_path),
                    f"missing reviewed-union token {token!r}",
                )
        for affected in sorted(NEXT_REQUEST_OVERLAP):
            if affected.casefold() not in folded_review:
                self.problems.add(
                    self.relative(union_review_path),
                    f"review omits exact intersection path {affected}",
                )
        self.problems.require(
            ("commute" in folded_review or "identical" in folded_review)
            and "sequential whole-file replacement" in folded_review,
            self.relative(union_review_path),
            "must record commutative same-preimage reconciliation without sequential replacement",
        )

        import_review_path = self.phase_dir / "reviews/R11-shared-import-replacements.tsv"
        _, import_rows = self.read_tsv(
            import_review_path,
            self.relative(import_review_path),
            ("consumer_path", "preimage_blob_oid", "old_import", "new_import"),
        )
        self.problems.require(
            len(import_rows) == 209,
            self.relative(import_review_path),
            "expected exact 209 reviewed import occurrences",
        )
        expected_consumers = {
            path_from_module(module)
            for module in protected_consumers.get("B0003", set())
        }
        actual_consumers = {row.get("consumer_path", "") for row in import_rows}
        self.problems.require(
            actual_consumers == expected_consumers,
            self.relative(import_review_path),
            "import-occurrence review must cover every and only R11 protected consumers",
        )
        for index, row in enumerate(import_rows):
            consumer = row.get("consumer_path", "")
            self.problems.require(
                row.get("preimage_blob_oid")
                == self.git_blob(INTEGRATED_CODE_SHA, consumer),
                f"{self.relative(import_review_path)}[{index}].preimage_blob_oid",
                "must equal the exact C0001 consumer blob",
            )
            self.problems.require(
                bool(row.get("old_import", ""))
                and bool(row.get("new_import", ""))
                and row.get("old_import") != row.get("new_import"),
                f"{self.relative(import_review_path)}[{index}]",
                "import replacement must name distinct nonempty old/new modules",
            )

    def r03_expected_digest(self, key: str, context: str) -> str | None:
        expected = R03_ARTIFACT_SHA256.get(key)
        if expected is None:
            self.problems.add(
                context,
                f"PENDING_R03_SHA256: validator constant for {key!r} has not been ratcheted",
            )
            return None
        self.problems.require(
            SHA256_RE.fullmatch(expected) is not None,
            context,
            f"malformed R03 SHA-256 constant for {key!r}",
        )
        return expected

    def require_r03_evidence(self, key: str) -> Artifact | None:
        path = R03_EVIDENCE_PATHS[key]
        matches = [
            artifact
            for artifact in self.branch_evidence.get(R03_BRANCH_ID, [])
            if artifact.path == path
        ]
        self.problems.require(
            len(matches) == 1,
            f"{R03_BRANCH_ID}.refresh.evidence",
            f"must hash-pin exactly one {path}",
        )
        if len(matches) != 1:
            return None
        expected = self.r03_expected_digest(key, f"R03 artifact {key}")
        if expected is not None:
            self.problems.require(
                matches[0].sha256 == expected,
                f"{R03_BRANCH_ID}.refresh.evidence[{path}]",
                f"expected exact SHA-256 {expected}",
            )
        return matches[0]

    def validate_r03_epoch(self) -> None:
        """Ratchet the singleton exact-C0002 R03 packet through activation."""

        context = "C0002-rooted R03 planned/active epoch"
        self.problems.require(
            self.current_checkpoint_id == C0002_CHECKPOINT_ID,
            context,
            "R03 planned/active controls require current checkpoint C0002",
        )
        r07_milestone_status = self.validate_r03_milestones()
        lane_operators = self.validate_r03_authority()
        inventory, inventory_by_path, selector = self.validate_r03_selector()
        branch, worker_rules, activation_evidence = self.validate_r03_branch(
            inventory_by_path, selector
        )
        projection, declarations = self.validate_r03_projection(
            {module for module, _path in selector}
        )
        consumer_sets = self.validate_r03_consumers()
        self.validate_r03_routes_and_tests(
            selector, inventory_by_path, declarations, worker_rules, consumer_sets
        )
        self.validate_r03_reviews()
        request, request_paths, unreserved = self.validate_r03_request(
            worker_rules, consumer_sets
        )
        if branch is not None and branch.get("status") == "planned":
            self.validate_r03_ref_and_worktree_absence()
        elif branch is not None and branch.get("status") == "active":
            self.validate_r03_activation_review()

        if branch is not None and projection is not None and request is not None:
            shared_leaks = tuple(
                sorted(
                    {
                        f"{rule.path} -> {shared.path}"
                        for rule in worker_rules
                        for shared in self.shared_rules
                        if rule.intersects(shared)
                    }
                )
            )
            selector_path = self.phase_dir / "selectors/R03.tsv"
            route_path = self.phase_dir / "branches/B0005-declaration-routes.tsv"
            selector_sha = sha256_path(selector_path) if selector_path.is_file() else ""
            route_sha = sha256_path(route_path) if route_path.is_file() else ""
            selector_expected = sorted(
                (row.get("module", ""), row.get("path", ""))
                for row in inventory
                if row.get("wave_id") == R03_WAVE_ID
            )
            snapshot = R03EpochSnapshot(
                branch_base_checkpoint_id=str(branch.get("base_checkpoint_id", "")),
                branch_base_sha=str(branch.get("base_sha", "")),
                branch_status=str(branch.get("status", "")),
                operator_ids=tuple(branch.get("operator_ids", ()))
                if isinstance(branch.get("operator_ids"), list)
                else (),
                lane_operator_ids=lane_operators,
                selector_sha256=selector_sha,
                selector_rows=len(selector),
                selector_matches_inventory=selector == selector_expected,
                route_sha256=route_sha,
                activation_evidence=activation_evidence,
                delivery=branch.get("delivery", {})
                if isinstance(branch.get("delivery"), dict)
                else {},
                integration=branch.get("integration", {})
                if isinstance(branch.get("integration"), dict)
                else {},
                retirement=branch.get("retirement", {})
                if isinstance(branch.get("retirement"), dict)
                else {},
                projection_base_checkpoint_id=str(
                    projection.get("base_checkpoint_id", "")
                ),
                projection_status=str(projection.get("status", "")),
                projection_selector_sha256=str(
                    projection.get("selector", {})
                    .get("artifact", {})
                    .get("sha256", "")
                )
                if isinstance(projection.get("selector"), dict)
                else "",
                request_target_checkpoint_id=str(
                    request.get("target_checkpoint_id", "")
                ),
                request_target_base_sha=str(request.get("target_base_sha", "")),
                request_status=str(request.get("status", "")),
                request_resolution=request.get("resolution", {})
                if isinstance(request.get("resolution"), dict)
                else {},
                r07_milestone_status=r07_milestone_status,
                worker_shared_leaks=shared_leaks,
                request_unreserved_paths=tuple(sorted(unreserved)),
            )
            expected_route = self.r03_expected_digest(
                "declaration_routes", "R03 declaration-route snapshot"
            )
            validate_r03_epoch_snapshot(
                snapshot,
                self.problems,
                expected_route_sha256=expected_route or "<pending>",
            )

    def validate_r03_milestones(self) -> str:
        milestones = self.phase.get("milestones")
        if not isinstance(milestones, list):
            self.problems.add("phase.json.milestones", "expected a list")
            return ""
        by_id = {
            item.get("milestone_id"): item
            for item in milestones
            if isinstance(item, dict) and isinstance(item.get("milestone_id"), str)
        }
        m03 = by_id.get("M03", {})
        self.problems.require(
            m03.get("wave_ids") == [R03_WAVE_ID]
            and m03.get("status") == "ready"
            and m03.get("accepted_checkpoint_id") is None,
            "phase.json.milestones[M03]",
            "M03 alone must be ready for R03 with accepted_checkpoint_id null",
        )
        for milestone_id, milestone in sorted(by_id.items()):
            if milestone.get("accepted_checkpoint_id") is not None:
                continue
            expected = "ready" if milestone_id == "M03" else "planned"
            self.problems.require(
                milestone.get("status") == expected,
                f"phase.json.milestones[{milestone_id}]",
                f"unaccepted milestone must remain {expected!r}",
            )
        self.problems.require(
            by_id.get("M07", {}).get("status") == "planned",
            "phase.json.milestones[M07]",
            "R07 must remain explicitly deferred/planned",
        )
        return str(by_id.get("M07", {}).get("status", ""))

    def validate_r03_authority(self) -> tuple[str, ...]:
        authority = self.phase.get("authority")
        lanes = authority.get("lanes") if isinstance(authority, dict) else None
        matches = [
            lane
            for lane in lanes or []
            if isinstance(lane, dict) and lane.get("lane_id") == R03_LANE_ID
        ]
        lane = matches[0] if len(matches) == 1 else {}
        operators = (
            tuple(lane.get("operator_ids", ()))
            if isinstance(lane.get("operator_ids"), list)
            else ()
        )
        self.problems.require(
            len(matches) == 1
            and lane.get("owner_id") == "primary-human"
            and operators == (R03_OPERATOR_ID,),
            f"phase.json.authority.lanes[{R03_LANE_ID}]",
            "R03 requires one primary-human-owned codex-lane authorizing only codex-local",
        )
        return operators

    def validate_r03_selector(
        self,
    ) -> tuple[
        list[dict[str, str]],
        dict[str, dict[str, str]],
        list[tuple[str, str]],
    ]:
        inventory_path = self.phase_dir / "checkpoints/C0002-inventory.tsv"
        if inventory_path.is_file():
            self.problems.require(
                sha256_path(inventory_path) == C0002_INVENTORY_SHA256,
                self.relative(inventory_path),
                f"expected exact C0002 inventory SHA-256 {C0002_INVENTORY_SHA256}",
            )
        _, inventory = self.read_tsv(
            inventory_path, self.relative(inventory_path), SCOPE_HEADER
        )
        self.problems.require(
            len(inventory) == C0002_METRICS["production_modules"],
            self.relative(inventory_path),
            f"expected {C0002_METRICS['production_modules']} exact C0002 inventory rows",
        )
        inventory_by_path = {row.get("path", ""): row for row in inventory}
        self.problems.require(
            len(inventory_by_path) == len(inventory),
            self.relative(inventory_path),
            "C0002 inventory paths must be unique",
        )
        expected = sorted(
            (row.get("module", ""), row.get("path", ""))
            for row in inventory
            if row.get("wave_id") == R03_WAVE_ID
        )
        selector_path = self.phase_dir / "selectors/R03.tsv"
        if selector_path.is_file():
            self.problems.require(
                sha256_path(selector_path) == R03_SELECTOR_SHA256,
                self.relative(selector_path),
                f"expected exact R03 selector SHA-256 {R03_SELECTOR_SHA256}",
            )
        _, selector_rows = self.read_tsv(
            selector_path, self.relative(selector_path), SELECTOR_HEADER
        )
        actual = [
            (row.get("module", ""), row.get("path", "")) for row in selector_rows
        ]
        self.problems.require(
            actual == expected and len(actual) == R03_OWNER_COUNT,
            self.relative(selector_path),
            "selector must equal the exact sorted 47-owner C0002 R03 inventory wave",
        )
        selected_rows = [inventory_by_path.get(path, {}) for _module, path in expected]
        debt_counts = Counter(
            flag
            for row in selected_rows
            for flag in split_values(row.get("debt_flags", ""))
        )
        self.problems.require(
            {key: debt_counts.get(key, 0) for key in R03_DEBT_COUNTS}
            == R03_DEBT_COUNTS,
            "R03 C0002 debt facts",
            f"expected exact debt counts {R03_DEBT_COUNTS}",
        )
        for module, path in expected:
            row = inventory_by_path.get(path, {})
            self.problems.require(
                module_from_path(path) == module
                and row.get("phase_scope") == "in_scope"
                and row.get("lane_id") == R03_LANE_ID,
                f"R03 selector[{path}]",
                "module/path and immutable in-scope lane assignment must match C0002",
            )
            actual_blob = self.git_blob(C0002_CODE_SHA, path)
            self.problems.require(
                actual_blob == row.get("base_blob_oid"),
                f"R03 selector[{path}]",
                f"C0002 blob mismatch: inventory {row.get('base_blob_oid')!r}, Git {actual_blob!r}",
            )
        baseline_path = self.phase_dir / "baselines/C0002-combined.json"
        if baseline_path.is_file():
            self.problems.require(
                sha256_path(baseline_path) == C0002_COMBINED_BASELINE_SHA256,
                self.relative(baseline_path),
                "C0002 combined baseline drifted",
            )
        else:
            self.problems.add(self.relative(baseline_path), "missing C0002 combined baseline")
        return inventory, inventory_by_path, actual

    def validate_r03_branch(
        self,
        inventory_by_path: dict[str, dict[str, str]],
        selector: list[tuple[str, str]],
    ) -> tuple[dict[str, Any] | None, list[PathRule], tuple[Artifact, ...]]:
        path = self.phase_dir / "branches/B0005.json"
        branch = self.read_json(path, self.relative(path))
        if branch is None:
            return None, [], ()
        self.branch_records[R03_BRANCH_ID] = branch
        exact_keys = {
            "schema_version",
            "record_kind",
            "phase_id",
            "branch_id",
            "lane_id",
            "wave_id",
            "branch_name",
            "owner_id",
            "operator_ids",
            "base_checkpoint_id",
            "base_sha",
            "owned_paths",
            "destination_prefixes",
            "forbidden_paths",
            "baseline_projection_id",
            "shared_request_ids",
            "status",
            "refresh",
            "delivery",
            "integration",
            "retirement",
        }
        self.problems.require(
            set(branch) == exact_keys,
            self.relative(path),
            "must retain the strict generic phase_branch schema (no ad-hoc activation/worktree fields)",
        )
        for key, expected in {
            "schema_version": 1,
            "record_kind": "phase_branch",
            "phase_id": PHASE_ID,
            "branch_id": R03_BRANCH_ID,
            "lane_id": R03_LANE_ID,
            "wave_id": R03_WAVE_ID,
            "branch_name": R03_BRANCH_NAME,
            "owner_id": "primary-human",
            "operator_ids": [R03_OPERATOR_ID],
            "base_checkpoint_id": C0002_CHECKPOINT_ID,
            "base_sha": C0002_CODE_SHA,
            "baseline_projection_id": R03_PROJECTION_ID,
            "shared_request_ids": [R03_REQUEST_ID],
        }.items():
            self.problems.require(
                branch.get(key) == expected,
                f"{R03_BRANCH_ID}.{key}",
                f"expected {expected!r}, found {branch.get(key)!r}",
            )
        status = branch.get("status")
        self.problems.require(
            status in {"planned", "active"},
            f"{R03_BRANCH_ID}.status",
            "expected exact planned or active R03 lifecycle state",
        )

        refresh = branch.get("refresh")
        evidence: Any = []
        if not isinstance(refresh, dict) or set(refresh) != {
            "reviewed_checkpoint_id",
            "decision",
            "evidence",
        }:
            self.problems.add(
                f"{R03_BRANCH_ID}.refresh",
                "expected exactly reviewed_checkpoint_id/decision/evidence",
            )
        else:
            self.problems.require(
                refresh.get("reviewed_checkpoint_id") == C0002_CHECKPOINT_ID
                and refresh.get("decision") == "current",
                f"{R03_BRANCH_ID}.refresh",
                "must record a current review against exact C0002",
            )
            evidence = refresh.get("evidence")
        artifacts: list[Artifact] = []
        if not isinstance(evidence, list):
            self.problems.add(
                f"{R03_BRANCH_ID}.refresh.evidence", "expected a hash-pinned list"
            )
        else:
            for index, item in enumerate(evidence):
                artifact = self.artifact(
                    item, f"{R03_BRANCH_ID}.refresh.evidence[{index}]"
                )
                if artifact is not None:
                    artifacts.append(artifact)
        self.branch_evidence[R03_BRANCH_ID] = artifacts
        evidence_paths = [artifact.path for artifact in artifacts]
        expected_evidence_paths = set(R03_EVIDENCE_PATHS.values())
        if status == "active":
            expected_evidence_paths.add(R03_ACTIVATION_REVIEW_PATH)
        self.problems.require(
            evidence_paths == sorted(evidence_paths)
            and len(evidence_paths) == len(set(evidence_paths))
            and set(evidence_paths) == expected_evidence_paths,
            f"{R03_BRANCH_ID}.refresh.evidence",
            "must be the exact sorted R03 evidence manifest for the branch lifecycle state",
        )
        for key in R03_EVIDENCE_PATHS:
            self.require_r03_evidence(key)
        activation_evidence = tuple(
            sorted(
                (
                    artifact
                    for artifact in artifacts
                    if artifact.path == R03_ACTIVATION_REVIEW_PATH
                ),
                key=lambda artifact: (artifact.path, artifact.sha256),
            )
        )
        if status == "planned":
            self.problems.require(
                not activation_evidence
                and not any(
                    any(
                        token in evidence_path.casefold()
                        for token in ("activation", "base-tip", "ref-tip", "worktree")
                    )
                    for evidence_path in evidence_paths
                ),
                f"{R03_BRANCH_ID}.refresh.evidence",
                "planned packet may not contain activation, base-tip, ref-tip, or worktree evidence",
            )
        elif status == "active":
            self.problems.require(
                activation_evidence
                == (
                    Artifact(
                        R03_ACTIVATION_REVIEW_PATH,
                        R03_ACTIVATION_REVIEW_SHA256,
                    ),
                ),
                f"{R03_BRANCH_ID}.refresh.evidence",
                "active packet must hash-pin the exact R03 activation review",
            )

        expected_owned = {selected_path for _module, selected_path in selector}
        owned = self.parse_rules(branch.get("owned_paths"), f"{R03_BRANCH_ID}.owned_paths")
        self.problems.require(
            len(owned) == R03_OWNER_COUNT
            and all(rule.match == "exact" for rule in owned)
            and {rule.path for rule in owned} == expected_owned,
            f"{R03_BRANCH_ID}.owned_paths",
            "must own every and only exact R03 selector path",
        )
        destinations = self.parse_rules(
            branch.get("destination_prefixes"),
            f"{R03_BRANCH_ID}.destination_prefixes",
        )
        expected_destinations = R03_DESTINATIONS
        if expected_destinations is None:
            self.problems.add(
                f"{R03_BRANCH_ID}.destination_prefixes",
                "PENDING_R03_DESTINATIONS: exact reviewed destination set is not ratcheted",
            )
        else:
            self.problems.require(
                all(rule.match == "prefix" for rule in destinations)
                and {rule.path for rule in destinations} == expected_destinations,
                f"{R03_BRANCH_ID}.destination_prefixes",
                f"must equal exact reviewed set {sorted(expected_destinations)}",
            )
        base_paths = self.git_tree_paths(C0002_CODE_SHA)
        for index, destination in enumerate(destinations):
            occupied = [
                tree_path
                for tree_path in base_paths
                if is_equal_or_child(tree_path.casefold(), destination.folded)
            ]
            self.problems.require(
                not occupied,
                f"{R03_BRANCH_ID}.destination_prefixes[{destination.path}]",
                f"must be casefold-vacant at C0002; found {occupied[:5]}",
            )
            for other in destinations[index + 1 :]:
                self.problems.require(
                    not destination.intersects(other),
                    f"{R03_BRANCH_ID}.destination_prefixes",
                    f"equal-or-ancestor collision {destination.path} / {other.path}",
                )

        forbidden = self.parse_rules(
            branch.get("forbidden_paths"), f"{R03_BRANCH_ID}.forbidden_paths"
        )
        forbidden_exact = {rule.path for rule in forbidden if rule.match == "exact"}
        forbidden_prefix = {rule.path for rule in forbidden if rule.match == "prefix"}
        self.problems.require(
            forbidden_exact == set(inventory_by_path) - expected_owned
            and len(forbidden_exact) == R03_FORBIDDEN_EXACT_COUNT,
            f"{R03_BRANCH_ID}.forbidden_paths",
            "exact forbidden rules must be the exhaustive 2,595-path C0002 complement",
        )
        self.problems.require(
            forbidden_prefix == set(R03_PROTECTED_PREFIXES),
            f"{R03_BRANCH_ID}.forbidden_paths",
            "prefix forbidden rules must be the exact guarded infrastructure set",
        )
        worker_rules = owned + destinations
        for rule in worker_rules:
            for shared in self.shared_rules:
                if rule.intersects(shared):
                    self.problems.add(
                        f"{R03_BRANCH_ID} authority",
                        f"worker rule {rule.path} intersects integrator-shared {shared.path}",
                    )
        return branch, worker_rules, activation_evidence

    def validate_r03_projection(
        self, selector_modules: set[str]
    ) -> tuple[
        dict[str, Any] | None,
        dict[tuple[str, str], tuple[str, str]],
    ]:
        path = self.phase_dir / "projections/P0005.json"
        projection = self.read_json(path, self.relative(path))
        if projection is None:
            return None, {}
        exact_keys = {
            "schema_version",
            "record_kind",
            "phase_id",
            "projection_id",
            "wave_id",
            "base_checkpoint_id",
            "selector",
            "projection_graph",
            "combined_baseline",
            "expected_counts",
            "checker",
            "status",
            "superseded_by",
        }
        self.problems.require(
            set(projection) == exact_keys,
            self.relative(path),
            "must retain the strict generic baseline_projection schema",
        )
        for key, expected in {
            "schema_version": 1,
            "record_kind": "baseline_projection",
            "phase_id": PHASE_ID,
            "projection_id": R03_PROJECTION_ID,
            "wave_id": R03_WAVE_ID,
            "base_checkpoint_id": C0002_CHECKPOINT_ID,
            "status": "active",
            "superseded_by": None,
            "expected_counts": R03_COUNTS,
        }.items():
            self.problems.require(
                projection.get(key) == expected,
                f"{R03_PROJECTION_ID}.{key}",
                f"expected {expected!r}, found {projection.get(key)!r}",
            )

        selector = projection.get("selector")
        selector_artifact = None
        if not isinstance(selector, dict) or set(selector) != {"kind", "artifact"}:
            self.problems.add(
                f"{R03_PROJECTION_ID}.selector", "expected exactly kind/artifact"
            )
        else:
            self.problems.require(
                selector.get("kind") == "module_path_tsv",
                f"{R03_PROJECTION_ID}.selector.kind",
                "expected module_path_tsv",
            )
            selector_artifact = self.artifact(
                selector.get("artifact"), f"{R03_PROJECTION_ID}.selector.artifact"
            )
        if selector_artifact is not None:
            self.problems.require(
                selector_artifact.path == R03_EVIDENCE_PATHS["selector"]
                and selector_artifact.sha256 == R03_SELECTOR_SHA256,
                f"{R03_PROJECTION_ID}.selector.artifact",
                "must pin exact C0002 R03 selector",
            )

        graph = self.artifact(
            projection.get("projection_graph"),
            f"{R03_PROJECTION_ID}.projection_graph",
        )
        declarations: dict[tuple[str, str], tuple[str, str]] = {}
        if graph is not None:
            self.problems.require(
                graph.path == R03_EVIDENCE_PATHS["projection_graph"]
                and graph.sha256 == R03_PROJECTION_SHA256,
                f"{R03_PROJECTION_ID}.projection_graph",
                f"must pin deterministic graph {R03_PROJECTION_SHA256}",
            )
            graph_path = self.root / graph.path
            counts = self.parse_projection_graph(graph_path, R03_PROJECTION_ID)
            self.problems.require(
                counts == R03_COUNTS,
                f"{R03_PROJECTION_ID}.expected_counts",
                f"expected exact format-2 counts {R03_COUNTS}, found {counts}",
            )
            try:
                with gzip.open(graph_path, "rb") as handle:
                    payload_sha = hashlib.sha256(handle.read()).hexdigest().upper()
            except (OSError, gzip.BadGzipFile) as error:
                self.problems.add(
                    f"{R03_PROJECTION_ID}.projection_graph",
                    f"cannot hash decompressed payload: {error}",
                )
            else:
                self.problems.require(
                    payload_sha == R03_PROJECTION_PAYLOAD_SHA256,
                    f"{R03_PROJECTION_ID}.projection_graph",
                    f"expected payload SHA-256 {R03_PROJECTION_PAYLOAD_SHA256}",
                )
            declarations = self.parse_projection_declarations(
                graph_path, R03_PROJECTION_ID
            )
            owners = {owner for owner, _name in declarations}
            self.problems.require(
                owners == selector_modules,
                f"{R03_PROJECTION_ID}.projection_graph",
                "every and only R03 selector owner must contribute declarations",
            )
            self.problems.require(
                Counter(visibility for _kind, visibility in declarations.values()).get(
                    "private", 0
                )
                == R03_PRIVATE_COUNT,
                f"{R03_PROJECTION_ID}.projection_graph",
                f"expected exact {R03_PRIVATE_COUNT} private declarations",
            )

        combined = self.artifact(
            projection.get("combined_baseline"),
            f"{R03_PROJECTION_ID}.combined_baseline",
        )
        if combined is not None:
            self.problems.require(
                combined.path == R03_EVIDENCE_PATHS["baseline"]
                and combined.sha256 == C0002_COMBINED_BASELINE_SHA256,
                f"{R03_PROJECTION_ID}.combined_baseline",
                "must use the exact official C0002 combined baseline",
            )

        checker = projection.get("checker")
        if not isinstance(checker, dict) or set(checker) != {"artifact", "arguments"}:
            self.problems.add(
                f"{R03_PROJECTION_ID}.checker",
                "expected exactly artifact/arguments",
            )
        else:
            checker_artifact = self.artifact(
                checker.get("artifact"), f"{R03_PROJECTION_ID}.checker.artifact"
            )
            if checker_artifact is not None:
                self.problems.require(
                    checker_artifact.path
                    == "tools/architecture/check_completion_phase_projection.py"
                    and checker_artifact.sha256 == NEXT_PROJECTION_CHECKER_SHA256,
                    f"{R03_PROJECTION_ID}.checker.artifact",
                    "must pin the exact private-aware projection checker",
                )
            destinations = R03_DESTINATIONS or frozenset()
            if R03_DESTINATIONS is None:
                self.problems.add(
                    f"{R03_PROJECTION_ID}.checker.arguments",
                    "PENDING_R03_DESTINATIONS: cannot ratchet allow-prefix vector",
                )
            private_map_sha = self.r03_expected_digest(
                "private_map", f"{R03_PROJECTION_ID}.checker.arguments"
            )
            expected_arguments = sorted(
                [f"--allow-module={module}" for module in selector_modules]
                + [
                    f"--allow-prefix={module_from_path(prefix)}."
                    for prefix in destinations
                    if prefix.startswith("NumStability/")
                ]
                + [
                    "--candidate=<candidate-format2.tsv>",
                    f"--candidate-sha256={R03_CANDIDATE_SHA256}",
                    f"--private-map-sha256={private_map_sha or '<pending>'}",
                    f"--private-map={R03_EVIDENCE_PATHS['private_map']}",
                    f"--projection-sha256={R03_PROJECTION_SHA256}",
                    f"--projection={R03_EVIDENCE_PATHS['projection_graph']}",
                ]
            )
            arguments = checker.get("arguments")
            self.problems.require(
                isinstance(arguments, list)
                and len(arguments) == len(set(arguments))
                and set(arguments) == set(expected_arguments),
                f"{R03_PROJECTION_ID}.checker.arguments",
                "checker vector must exactly and uniquely bind all owners, destinations, private map, and graph",
            )
        return projection, declarations

    def validate_r03_consumers(self) -> dict[str, set[str]]:
        path = self.phase_dir / "branches/B0005-consumers.tsv"
        header = (
            "record_kind",
            "direction",
            "consumer_module",
            "consumer_path",
            "consumer_scope",
            "consumer_wave",
            "target_wave",
            "target_owner",
            "relation",
            "edge_kind",
            "source_declaration",
            "targets",
            "witness",
            "details",
        )
        _, rows = self.read_tsv(path, self.relative(path), header)
        expected_counts = {
            "common_direct_project_dependency": 7,
            "owner_reachability": 47,
            "r03_external_declaration_consumer": 14287,
            "r03_module_consumer": 2058,
            "shared_direct_outside_consumer": 5,
        }
        counts = Counter(row.get("record_kind", "") for row in rows)
        self.problems.require(
            dict(counts) == expected_counts,
            self.relative(path),
            f"expected exact consumer/reachability row counts {expected_counts}",
        )
        identities = [tuple(row.get(column, "") for column in header) for row in rows]
        self.problems.require(
            len(identities) == len(set(identities)),
            self.relative(path),
            "consumer evidence rows must be unique",
        )
        reach = Counter(
            row.get("direction", "")
            for row in rows
            if row.get("record_kind") == "owner_reachability"
        )
        self.problems.require(
            reach
            == Counter(
                {
                    "R03->R07": R03_R07_OVERLAP_COUNTS[
                        "r03_to_r07_transitive_owner_pairs"
                    ],
                    "R07->R03": R03_R07_OVERLAP_COUNTS[
                        "r07_to_r03_transitive_owner_pairs"
                    ],
                }
            ),
            self.relative(path),
            "must contain exact 24/23 directed transitive owner-reachability rows",
        )
        self.problems.require(
            counts.get("common_direct_project_dependency", 0)
            == R03_R07_OVERLAP_COUNTS["common_direct_project_dependencies"]
            and counts.get("shared_direct_outside_consumer", 0)
            == R03_R07_OVERLAP_COUNTS["shared_outside_consumers"],
            self.relative(path),
            "must contain exact seven common dependencies and five shared outside consumers",
        )
        allowed_kinds = set(expected_counts)
        for index, row in enumerate(rows):
            row_context = f"{self.relative(path)}[{index}]"
            kind = row.get("record_kind", "")
            module = row.get("consumer_module", "")
            consumer_path = row.get("consumer_path", "")
            self.problems.require(
                kind in allowed_kinds
                and bool(module)
                and consumer_path == path_from_module(module),
                row_context,
                "consumer kind/module/path must be complete and canonical",
            )
            self.problems.require(
                DEFERRED_RE.search(" ".join(row.values())) is None,
                row_context,
                "consumer evidence may not contain deferred review text",
            )
            if kind == "owner_reachability":
                self.problems.require(
                    row.get("relation") == "transitive"
                    and bool(row.get("target_owner"))
                    and " -> " in row.get("witness", ""),
                    row_context,
                    "owner reachability requires a transitive target and concrete witness",
                )
            elif kind == "common_direct_project_dependency":
                self.problems.require(
                    row.get("target_wave") == "R03+R07"
                    and row.get("relation") == "direct_dependency",
                    row_context,
                    "common dependency must be a direct R03+R07 project dependency",
                )
            elif kind == "shared_direct_outside_consumer":
                self.problems.require(
                    row.get("target_wave") == "R03+R07"
                    and row.get("relation") == "direct_both",
                    row_context,
                    "shared outside consumer must directly consume both waves",
                )
            elif kind == "r03_module_consumer":
                self.problems.require(
                    row.get("target_wave") == R03_WAVE_ID
                    and row.get("relation") in {"direct", "transitive_only"},
                    row_context,
                    "R03 module consumer requires direct or transitive-only relation",
                )
            elif kind == "r03_external_declaration_consumer":
                self.problems.require(
                    row.get("target_wave") == R03_WAVE_ID
                    and row.get("relation") == "declaration_edge"
                    and row.get("edge_kind")
                    in {"signature", "body", "signature+body"}
                    and bool(row.get("source_declaration")),
                    row_context,
                    "external declaration consumer requires typed format-2 edge evidence",
                )
        return {
            "module_consumers": {
                row.get("consumer_module", "")
                for row in rows
                if row.get("record_kind") == "r03_module_consumer"
            },
            "external_consumer_modules": {
                row.get("consumer_module", "")
                for row in rows
                if row.get("record_kind") == "r03_external_declaration_consumer"
            },
            "shared_outside_consumers": {
                row.get("consumer_module", "")
                for row in rows
                if row.get("record_kind") == "shared_direct_outside_consumer"
            },
            "common_dependencies": {
                row.get("consumer_module", "")
                for row in rows
                if row.get("record_kind") == "common_direct_project_dependency"
            },
        }

    def validate_r03_routes_and_tests(
        self,
        selector: list[tuple[str, str]],
        inventory_by_path: dict[str, dict[str, str]],
        declarations: dict[tuple[str, str], tuple[str, str]],
        worker_rules: list[PathRule],
        consumer_sets: dict[str, set[str]],
    ) -> None:
        branch_dir = self.phase_dir / "branches"
        route_path = branch_dir / "B0005-declaration-routes.tsv"
        _, routes = self.read_tsv(
            route_path,
            self.relative(route_path),
            R03_DECLARATION_ROUTE_HEADER,
        )
        self.problems.require(
            len(routes) == R03_COUNTS["declarations"],
            self.relative(route_path),
            f"expected exact {R03_COUNTS['declarations']} declaration routes",
        )
        route_identities = [
            (
                row.get("baseline_owner_module", ""),
                row.get("baseline_declaration_name", ""),
            )
            for row in routes
        ]
        self.problems.require(
            len(route_identities) == len(set(route_identities))
            and set(route_identities) == set(declarations),
            self.relative(route_path),
            "routes must uniquely cover every and only projected declaration",
        )
        orders: dict[str, list[int]] = defaultdict(list)
        owner_destinations: dict[str, set[str]] = defaultdict(set)
        private_routes: dict[str, tuple[str, str]] = {}
        route_keys: list[tuple[str, int]] = []
        public_names: set[str] = set()
        for index, row in enumerate(routes):
            row_context = f"{self.relative(route_path)}[{index}]"
            owner = row.get("baseline_owner_module", "")
            name = row.get("baseline_declaration_name", "")
            destination = row.get("destination_module", "")
            expected = declarations.get((owner, name))
            if expected is not None:
                self.problems.require(
                    (row.get("kind", ""), row.get("visibility", "")) == expected,
                    row_context,
                    "kind/visibility must equal the frozen format-2 declaration",
                )
            try:
                order = int(row.get("baseline_order", ""))
                if order < 1:
                    raise ValueError
            except ValueError:
                self.problems.add(
                    f"{row_context}.baseline_order", "expected a positive integer"
                )
                order = 0
            orders[owner].append(order)
            route_keys.append((owner, order))
            owner_destinations[owner].add(destination)
            self.problems.require(
                row.get("route_class") in {"reusable", "source", "internal"},
                f"{row_context}.route_class",
                "R03 route class must be exactly reusable, source, or internal",
            )
            expected_decision = (
                "private_name_hash_pinned"
                if row.get("visibility") == "private"
                else "preserve_name_and_signature"
            )
            self.problems.require(
                row.get("normalization_decision") == expected_decision,
                f"{row_context}.normalization_decision",
                f"expected exact decision {expected_decision!r}",
            )
            self.problems.require(
                destination.startswith("NumStability.")
                and "Chapter72" not in destination,
                f"{row_context}.destination_module",
                "destination must be a reviewed NumStability module and may not use invalid Chapter72",
            )
            if row.get("visibility") == "private":
                self.problems.require(
                    name not in private_routes,
                    row_context,
                    f"duplicate private declaration {name}",
                )
                private_routes[name] = (owner, destination)
            else:
                public_names.add(name)
        self.problems.require(
            route_keys == sorted(route_keys),
            self.relative(route_path),
            "routes must be sorted by owner and frozen baseline order",
        )
        for owner, owner_orders in orders.items():
            self.problems.require(
                owner_orders == list(range(1, len(owner_orders) + 1)),
                self.relative(route_path),
                f"{owner} baseline_order must be a contiguous 1-based sequence",
            )
        self.problems.require(
            len(private_routes) == R03_PRIVATE_COUNT,
            self.relative(route_path),
            f"expected exact {R03_PRIVATE_COUNT} private declaration routes",
        )
        rump_destinations = owner_destinations.get(
            "NumStability.Algorithms.Higham726Rump", set()
        )
        self.problems.require(
            bool(rump_destinations)
            and all(
                destination.startswith(
                    "NumStability.Source.Higham.Chapter07.Equation26."
                )
                for destination in rump_destinations
            ),
            self.relative(route_path),
            "Higham726Rump must route only through Higham Chapter 7 Equation 26",
        )

        selector_by_module = {module: path for module, path in selector}
        projected_counts = Counter(owner for owner, _name in declarations)
        module_path = branch_dir / "B0005-module-routes.tsv"
        _, module_rows = self.read_tsv(
            module_path,
            self.relative(module_path),
            R03_MODULE_ROUTE_HEADER,
        )
        module_names = [row.get("owner_module", "") for row in module_rows]
        self.problems.require(
            module_names == sorted(selector_by_module)
            and set(module_names) == set(selector_by_module)
            and len(module_names) == R03_OWNER_COUNT,
            self.relative(module_path),
            "module routes must cover every selector owner once in sorted order",
        )
        mixed_count = 0
        missing_doc_count = 0
        noncanonical_count = 0
        umbrella_count = 0
        unclassified_count = 0
        semantic_classes: Counter[str] = Counter()
        for index, row in enumerate(module_rows):
            row_context = f"{self.relative(module_path)}[{index}]"
            owner = row.get("owner_module", "")
            selected_path = selector_by_module.get(owner, "")
            inventory_row = inventory_by_path.get(selected_path, {})
            self.problems.require(
                row.get("path") == selected_path
                and row.get("base_blob_oid") == inventory_row.get("base_blob_oid")
                and row.get("current_tier") == inventory_row.get("current_tier")
                and row.get("debt_flags") == inventory_row.get("debt_flags"),
                row_context,
                "path/blob/tier/debt flags must exactly mirror C0002 inventory",
            )
            flags = set(split_values(row.get("debt_flags", "")))
            unclassified_count += "unclassified_modules" in flags
            mixed_count += "mixed_modules" in flags
            missing_doc_count += "missing_module_docstrings" in flags
            noncanonical_count += "noncanonical_modules" in flags
            umbrella_count += "declaration_bearing_umbrellas" in flags
            try:
                declaration_count = int(row.get("declaration_count", ""))
            except ValueError:
                self.problems.add(
                    f"{row_context}.declaration_count", "expected an integer"
                )
                declaration_count = -1
            self.problems.require(
                declaration_count == projected_counts.get(owner, 0),
                f"{row_context}.declaration_count",
                f"expected exact projected count {projected_counts.get(owner, 0)}",
            )
            listed = split_values(row.get("destination_modules", ""))
            self.problems.require(
                listed == sorted(set(listed))
                and set(listed) == owner_destinations.get(owner, set()),
                f"{row_context}.destination_modules",
                f"must equal exact declaration destinations {sorted(owner_destinations.get(owner, set()))}",
            )
            semantic = row.get("semantic_classification", "")
            semantic_parts = (
                semantic.removeprefix("mixed_split_").split("_")
                if semantic.startswith("mixed_split_")
                else split_values(semantic)
            )
            semantic_classes.update(semantic_parts)
            self.problems.require(
                bool(semantic_parts)
                and set(semantic_parts) <= {"reusable", "source", "internal"},
                f"{row_context}.semantic_classification",
                "must explicitly classify declarations as reusable/source/internal",
            )
            if inventory_row.get("current_tier") == "mixed":
                routed_classes = {
                    route.get("route_class", "")
                    for route in routes
                    if route.get("baseline_owner_module") == owner
                }
                self.problems.require(
                    all(
                        bool(row.get(key, "").strip())
                        and DEFERRED_RE.search(row.get(key, "")) is None
                        for key in ("split_rationale", "dependency_rationale")
                    ),
                    row_context,
                    "each mixed owner requires an explicit declaration classification/split and dependency rationale",
                )
                self.problems.require(
                    set(semantic_parts) == (routed_classes - {"internal"})
                    and routed_classes <= {"reusable", "source", "internal"},
                    f"{row_context}.semantic_classification",
                    "mixed-owner module classification must equal its declaration-level reusable/source roles (internal support may be additional)",
                )
            self.problems.require(
                bool(row.get("compatibility_action", "").strip())
                and DEFERRED_RE.search(row.get("compatibility_action", "")) is None
                and row.get("review_status") == "approved_before_activation",
                row_context,
                "compatibility action must be explicit and primary-human reviewed before activation",
            )
        self.problems.require(
            {
                "unclassified_modules": unclassified_count,
                "mixed_modules": mixed_count,
                "missing_module_docstrings": missing_doc_count,
                "noncanonical_modules": noncanonical_count,
                "declaration_bearing_umbrellas": umbrella_count,
            }
            == R03_DEBT_COUNTS,
            self.relative(module_path),
            f"module route debt facts must equal {R03_DEBT_COUNTS}",
        )

        private_path = branch_dir / "B0005-private-normalization.tsv"
        _, private_rows = self.read_tsv(
            private_path, self.relative(private_path), R03_PRIVATE_HEADER
        )
        self.problems.require(
            len(private_rows) == R03_PRIVATE_COUNT,
            self.relative(private_path),
            f"expected exact {R03_PRIVATE_COUNT}-row private map",
        )
        old_names = [row.get("old_private", "") for row in private_rows]
        new_names = [row.get("new_private", "") for row in private_rows]
        self.problems.require(
            old_names == sorted(private_routes)
            and set(old_names) == set(private_routes)
            and len(new_names) == len(set(new_names)),
            self.relative(private_path),
            "private map must exactly cover projected private names with unique postimages",
        )
        for index, row in enumerate(private_rows):
            row_context = f"{self.relative(private_path)}[{index}]"
            old = row.get("old_private", "")
            new = row.get("new_private", "")
            owner, destination = private_routes.get(old, ("", ""))
            self.problems.require(
                row.get("destination_module") == destination,
                f"{row_context}.destination_module",
                f"expected routed destination {destination!r}",
            )
            expected_prefix = f"_private.{destination}."
            self.problems.require(
                bool(old)
                and bool(new)
                and (new == old if destination == owner else new.startswith(expected_prefix))
                and DEFERRED_RE.search(" ".join(row.values())) is None,
                row_context,
                "private normalization must be complete and use only the reviewed destination prefix",
            )

        closure_path = branch_dir / "B0005-private-closure.tsv"
        _, closure_rows = self.read_tsv(
            closure_path,
            self.relative(closure_path),
            R03_PRIVATE_CLOSURE_HEADER,
        )
        roles = Counter(row.get("closure_role", "") for row in closure_rows)
        selected_owner_rows = sum(
            row.get("selected_owner") == "yes" for row in closure_rows
        )
        self.problems.require(
            len(closure_rows) == R03_PRIVATE_CLOSURE_ROWS
            and roles
            == Counter(
                {
                    "private_seed": R03_PRIVATE_COUNT,
                    "reverse_dependent": R03_PRIVATE_REVERSE_DEPENDENTS,
                }
            )
            and selected_owner_rows == R03_PRIVATE_SELECTED_OWNER_ROWS,
            self.relative(closure_path),
            "private reverse closure must be exact 2,502 = 398 seeds + 2,104 dependents with 2,063 selected-owner rows",
        )
        closure_names = [row.get("declaration", "") for row in closure_rows]
        seeds = {
            row.get("declaration", "")
            for row in closure_rows
            if row.get("closure_role") == "private_seed"
        }
        self.problems.require(
            len(closure_names) == len(set(closure_names))
            and seeds == set(private_routes),
            self.relative(closure_path),
            "closure declarations must be unique and seeds must equal private-map domain",
        )
        for index, row in enumerate(closure_rows):
            role = row.get("closure_role", "")
            self.problems.require(
                row.get("visibility")
                == ("private" if role == "private_seed" else "public")
                and row.get("selected_owner") in {"yes", "no"},
                f"{self.relative(closure_path)}[{index}]",
                "closure role/visibility/selected-owner typing drifted",
            )

        test_path = branch_dir / "B0005-test-plan.tsv"
        _, test_rows = self.read_tsv(
            test_path, self.relative(test_path), R03_TEST_HEADER
        )
        pairs = [
            (row.get("test_class", ""), row.get("target", ""))
            for row in test_rows
        ]
        classes = {row.get("test_class", "") for row in test_rows}
        self.problems.require(
            pairs == sorted(pairs)
            and len(pairs) == len(set(pairs))
            and classes == R03_TEST_CLASSES,
            self.relative(test_path),
            f"test plan must be sorted/unique and cover exactly {sorted(R03_TEST_CLASSES)}",
        )
        by_class = {
            test_class: {
                row.get("target", "")
                for row in test_rows
                if row.get("test_class") == test_class
            }
            for test_class in R03_TEST_CLASSES
        }
        relocated_destinations = {
            destination
            for owner, destinations in owner_destinations.items()
            for destination in destinations
            if destination != owner
        }
        relocated_owners = {
            owner
            for owner, destinations in owner_destinations.items()
            if any(destination != owner for destination in destinations)
        }
        self.problems.require(
            by_class["old_only"] == relocated_owners,
            self.relative(test_path),
            "old-only tests must cover every and only relocated historical owners",
        )
        self.problems.require(
            by_class["canonical_only"] == relocated_destinations,
            self.relative(test_path),
            "canonical-only tests must cover every and only relocated destinations",
        )
        self.problems.require(
            by_class["focused"] == {"NumStabilityTest.Reorganization.R03.All"},
            self.relative(test_path),
            "focused plan must compile the exact R03 test umbrella",
        )
        protected_expected = (
            consumer_sets.get("module_consumers", set())
            | consumer_sets.get("external_consumer_modules", set())
        )
        self.problems.require(
            by_class["protected_consumer"] == protected_expected,
            self.relative(test_path),
            "protected-consumer tests must cover every exact module/declaration consumer",
        )
        self.problems.require(
            by_class["aggregate_entrypoint"]
            == {
                "NumStability",
                "NumStability.Algorithms",
                "NumStability.Analysis",
                "NumStability.Analysis.FloatingPointArithmetic",
                "NumStability.Source",
                "NumStability.Source.Higham",
                "NumStability.Source.Higham.Chapter12.IterativeRefinement",
            },
            self.relative(test_path),
            "aggregate/entry-point tests must equal the seven reviewed public entry points",
        )
        for index, row in enumerate(test_rows):
            purpose = row.get("purpose", "")
            self.problems.require(
                bool(purpose.strip()) and DEFERRED_RE.search(purpose) is None,
                f"{self.relative(test_path)}[{index}].purpose",
                "test purpose must be explicit and non-deferred",
            )

    def validate_r03_request(
        self,
        worker_rules: list[PathRule],
        consumer_sets: dict[str, set[str]],
    ) -> tuple[dict[str, Any] | None, set[str], set[str]]:
        request_dir = self.phase_dir / "requests"
        path = request_dir / "R0005.json"
        request = self.read_json(path, self.relative(path))
        if request is None:
            return None, set(), set()
        self.requests[R03_REQUEST_ID] = request
        exact_keys = {
            "schema_version",
            "record_kind",
            "phase_id",
            "request_id",
            "lane_id",
            "wave_id",
            "requester_id",
            "created_at",
            "target_checkpoint_id",
            "target_base_sha",
            "paths",
            "preimage_blobs",
            "rationale",
            "patch",
            "depends_on",
            "blocks",
            "valid_through_checkpoint_id",
            "status",
            "supersedes",
            "superseded_by",
            "resolution",
        }
        self.problems.require(
            set(request) == exact_keys,
            self.relative(path),
            "must retain the strict generic shared_file_request schema",
        )
        for key, expected in {
            "schema_version": 1,
            "record_kind": "shared_file_request",
            "phase_id": PHASE_ID,
            "request_id": R03_REQUEST_ID,
            "lane_id": R03_LANE_ID,
            "wave_id": R03_WAVE_ID,
            "requester_id": "primary-human",
            "target_checkpoint_id": C0002_CHECKPOINT_ID,
            "target_base_sha": C0002_CODE_SHA,
            "depends_on": [],
            "blocks": [R03_WAVE_ID],
            "valid_through_checkpoint_id": C0002_CHECKPOINT_ID,
            "status": "active",
            "supersedes": None,
            "superseded_by": None,
        }.items():
            self.problems.require(
                request.get(key) == expected,
                f"{R03_REQUEST_ID}.{key}",
                f"expected {expected!r}, found {request.get(key)!r}",
            )
        created_at = request.get("created_at")
        self.problems.require(
            isinstance(created_at, str)
            and RFC3339_RE.fullmatch(created_at) is not None,
            f"{R03_REQUEST_ID}.created_at",
            "expected an RFC3339 primary-human authority timestamp",
        )
        raw_paths = request.get("paths")
        paths = (
            raw_paths
            if isinstance(raw_paths, list)
            and all(isinstance(item, str) for item in raw_paths)
            else []
        )
        self.problems.require(
            paths == sorted(set(paths)) and bool(paths),
            f"{R03_REQUEST_ID}.paths",
            "request paths must be a nonempty sorted unique string list",
        )
        if R03_REQUEST_PATH_COUNT is None or R03_REQUEST_PATH_SHA256 is None:
            self.problems.add(
                f"{R03_REQUEST_ID}.paths",
                "PENDING_R03_REQUEST: exact path count/digest is not ratcheted",
            )
        else:
            self.problems.require(
                len(paths) == R03_REQUEST_PATH_COUNT
                and path_list_sha256(paths) == R03_REQUEST_PATH_SHA256,
                f"{R03_REQUEST_ID}.paths",
                f"expected exact {R03_REQUEST_PATH_COUNT}-path set at {R03_REQUEST_PATH_SHA256}",
            )
        shared_exact = {
            rule.path for rule in self.shared_rules if rule.match == "exact"
        }
        unreserved = set(paths) - shared_exact
        self.problems.require(
            not unreserved,
            f"{R03_REQUEST_ID}.paths",
            f"active request paths lack exact shared reservations: {sorted(unreserved)}",
        )
        for requested in paths:
            requested_rule = PathRule(requested, "exact")
            for worker in worker_rules:
                self.problems.require(
                    not requested_rule.intersects(worker),
                    f"{R03_REQUEST_ID}.paths[{requested}]",
                    f"integrator request leaks into worker rule {worker.path}",
                )

        expected_preimages = [
            {"blob_oid": self.git_blob(C0002_CODE_SHA, requested), "path": requested}
            for requested in paths
        ]
        self.problems.require(
            request.get("preimage_blobs") == expected_preimages,
            f"{R03_REQUEST_ID}.preimage_blobs",
            "must exactly record sorted C0002 blob OIDs for every request path",
        )
        patch = self.artifact(request.get("patch"), f"{R03_REQUEST_ID}.patch")
        patch_expected = self.r03_expected_digest(
            "request_patch", f"{R03_REQUEST_ID}.patch"
        )
        patch_path: Path | None = None
        if patch is not None:
            self.problems.require(
                patch.path == R03_EVIDENCE_PATHS["request_patch"]
                and patch.sha256 == (patch_expected or "<pending>"),
                f"{R03_REQUEST_ID}.patch",
                "must pin the exact independently replayable R0005 patch",
            )
            patch_path = self.root / patch.path

        post_path = request_dir / "R0005-postimages.tsv"
        post_header, post_rows = self.read_tsv(
            post_path,
            self.relative(post_path),
            (
                "path",
                "preimage_blob_oid",
                "preimage_sha256",
                "postimage_sha256",
            ),
        )
        postimages = self.validate_postimage_rows(
            post_header,
            post_rows,
            self.relative(post_path),
            set(paths),
            "postimage_sha256",
            base_sha=C0002_CODE_SHA,
            base_label=C0002_CHECKPOINT_ID,
        )
        post_expected = self.r03_expected_digest(
            "request_postimages", self.relative(post_path)
        )
        if post_path.is_file() and post_expected is not None:
            self.problems.require(
                sha256_path(post_path) == post_expected,
                self.relative(post_path),
                f"expected exact postimage SHA-256 {post_expected}",
            )
        if patch_path is not None:
            self.materialize_patch_postimages(
                R03_REQUEST_ID,
                patch_path,
                set(paths),
                postimages,
                base_sha=C0002_CODE_SHA,
                base_label=C0002_CHECKPOINT_ID,
                unidiff_zero=True,
            )

        replacement_path = request_dir / "R0005-replacements.tsv"
        replacement_header, replacement_rows = self.read_tsv(
            replacement_path, self.relative(replacement_path)
        )
        allowed_headers = {
            ("old_import", "new_import", "path", "occurrences"),
            ("path", "old_import", "new_import", "occurrences"),
            ("path", "old_import", "old_occurrences", "new_imports"),
            (
                "consumer_path",
                "preimage_blob_oid",
                "old_import",
                "new_import",
            ),
        }
        self.problems.require(
            tuple(replacement_header) in allowed_headers,
            self.relative(replacement_path),
            "replacement TSV must use an approved exact import-replacement schema",
        )
        replacement_paths: list[str] = []
        replacement_keys: list[tuple[str, str, str]] = []
        for index, row in enumerate(replacement_rows):
            row_context = f"{self.relative(replacement_path)}[{index}]"
            replacement_path_value = row.get("path") or row.get("consumer_path", "")
            old_import = row.get("old_import", "")
            new_import = row.get("new_import") or row.get("new_imports", "")
            new_import_values = split_values(new_import)
            replacement_paths.append(replacement_path_value)
            replacement_keys.append(
                (replacement_path_value, old_import, new_import)
            )
            self.problems.require(
                replacement_path_value in set(paths)
                and bool(old_import)
                and bool(new_import_values)
                and old_import not in new_import_values
                and new_import_values == sorted(set(new_import_values)),
                row_context,
                "replacement must name a requested path and sorted distinct old/new imports",
            )
            occurrence_field = (
                "occurrences" if "occurrences" in row else "old_occurrences"
            )
            if occurrence_field in row:
                try:
                    occurrence_count = int(row.get(occurrence_field, ""))
                except ValueError:
                    occurrence_count = 0
                self.problems.require(
                    occurrence_count > 0,
                    f"{row_context}.{occurrence_field}",
                    "occurrence count must be a positive integer",
                )
            if "preimage_blob_oid" in row:
                self.problems.require(
                    row.get("preimage_blob_oid")
                    == self.git_blob(C0002_CODE_SHA, replacement_path_value),
                    f"{row_context}.preimage_blob_oid",
                    "replacement must pin exact C0002 consumer blob",
                )
        self.problems.require(
            replacement_keys == sorted(set(replacement_keys))
            and bool(replacement_rows),
            self.relative(replacement_path),
            "replacement rows must be nonempty, sorted, and unique",
        )
        expected_consumer_paths = {
            path_from_module(module)
            for module in consumer_sets.get("module_consumers", set())
        }
        self.problems.require(
            set(replacement_paths) <= expected_consumer_paths,
            self.relative(replacement_path),
            "every replacement path must be an exact graph-derived R03 consumer",
        )

        expected_resolution = {
            "checkpoint_id": None,
            "commit_sha": None,
            "reason": None,
            "resolved_at": None,
            "resolved_by": None,
            "validation_evidence": [],
        }
        self.problems.require(
            request.get("resolution") == expected_resolution,
            f"{R03_REQUEST_ID}.resolution",
            "planned request must remain active and completely unresolved",
        )
        rationale = str(request.get("rationale", "")).upper()
        rationale_digests = [
            R03_REQUEST_PATH_SHA256,
            patch_expected,
            post_expected,
            self.r03_expected_digest(
                "request_replacements", f"{R03_REQUEST_ID}.rationale"
            ),
        ]
        for digest in rationale_digests:
            if digest is not None and digest not in rationale:
                self.problems.add(
                    f"{R03_REQUEST_ID}.rationale",
                    f"must hash-pin exact SHA-256 {digest}",
                )
        self.problems.require(
            C0002_CODE_SHA.upper() in rationale,
            f"{R03_REQUEST_ID}.rationale",
            "must name the exact C0002 preimage",
        )
        branch = self.branch_records.get(R03_BRANCH_ID, {})
        self.problems.require(
            branch.get("shared_request_ids") == [R03_REQUEST_ID],
            f"{R03_BRANCH_ID}.shared_request_ids",
            f"expected exactly [{R03_REQUEST_ID!r}]",
        )
        return request, set(paths), unreserved

    def validate_r03_reviews(self) -> None:
        required_artifacts = {
            "selection_review": (
                "c0002",
                C0002_CODE_SHA,
                "r03",
                "r07",
                "singleton",
                "defer",
                "m03",
                "m05",
                "m06",
                "24",
                "23",
                "7",
                "5",
                R03_SELECTOR_SHA256.casefold(),
            ),
            "route_review": (
                "primary-human",
                "r03",
                "c0002",
                C0002_CODE_SHA,
                "higham726rump",
                "chapter72",
                "chapter07",
                "equation26",
                "public",
                "signature",
                "private",
                "mixed",
            ),
            "projection_replay": (
                "c0002",
                C0002_CODE_SHA,
                "r03",
                R03_SELECTOR_SHA256.casefold(),
                R03_PROJECTION_SHA256.casefold(),
                R03_PROJECTION_PAYLOAD_SHA256.casefold(),
                str(R03_COUNTS["declarations"]),
                str(R03_COUNTS["signature_edges"]),
                str(R03_COUNTS["body_edges"]),
                str(R03_COUNTS["union_edges"]),
                "reverse",
            ),
            "overlap_review": (
                "c0002",
                C0002_CODE_SHA,
                "r03",
                "r07",
                "singleton",
                "24",
                "23",
                "7",
                "5",
                R03_SELECTOR_SHA256.casefold(),
                R03_PROJECTION_SHA256.casefold(),
            ),
        }
        for key, tokens in required_artifacts.items():
            path = self.root / R03_EVIDENCE_PATHS[key]
            try:
                text = path.read_text(encoding="utf-8")
            except (OSError, UnicodeError) as error:
                self.problems.add(
                    R03_EVIDENCE_PATHS[key], f"cannot read reviewed evidence: {error}"
                )
                continue
            folded = " ".join(text.casefold().replace("_", "-").split())
            for token in tokens:
                if token.casefold() not in folded:
                    self.problems.add(
                        R03_EVIDENCE_PATHS[key],
                        f"missing exact reviewed token {token!r}",
                    )
            if key in {"route_review", "projection_replay"}:
                self.problems.require(
                    re.search(
                        r"\b(?:tbd|todo|pending|unreviewed|undecided|worker decides|decide later)\b",
                        text,
                        re.IGNORECASE,
                    )
                    is None,
                    R03_EVIDENCE_PATHS[key],
                    "R03 route/projection decisions may not remain deferred",
                )
        route_text_path = self.root / R03_EVIDENCE_PATHS["route_review"]
        try:
            route_text = route_text_path.read_text(encoding="utf-8").casefold()
        except (OSError, UnicodeError):
            route_text = ""
        self.problems.require(
            "chapter72" in route_text
            and any(
                token in route_text
                for token in ("invalid", "reject", "forbidden", "not a valid")
            )
            and "chapter07" in route_text
            and "equation26" in route_text,
            R03_EVIDENCE_PATHS["route_review"],
            "must explicitly reject Chapter72 and freeze Chapter07 Equation26",
        )

    def validate_r03_ref_and_worktree_absence(self) -> None:
        """Check only local state; remote absence remains hash-pinned review evidence."""

        ref = self.git("show-ref", "--verify", "--quiet", R03_REMOTE_REF, check=False)
        self.problems.require(
            ref.returncode == 1,
            "R03 pre-activation ref",
            f"planned epoch must not create local {R03_REMOTE_REF}",
        )
        if os.name == "nt":
            worktree = Path(R03_PLANNED_WORKTREE)
            self.problems.require(
                not worktree.exists(),
                "R03 pre-activation worktree",
                f"planned epoch must not create {R03_PLANNED_WORKTREE}",
            )

    def validate_r03_activation_review(self) -> None:
        """Validate hash-pinned external ref/worktree facts without requiring local state."""

        path = self.root / R03_ACTIVATION_REVIEW_PATH
        if not path.is_file():
            self.problems.add(
                R03_ACTIVATION_REVIEW_PATH,
                "active R03 epoch requires the activation review",
            )
            return
        self.problems.require(
            sha256_path(path) == R03_ACTIVATION_REVIEW_SHA256,
            R03_ACTIVATION_REVIEW_PATH,
            f"expected exact activation review SHA-256 {R03_ACTIVATION_REVIEW_SHA256}",
        )
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as error:
            self.problems.add(
                R03_ACTIVATION_REVIEW_PATH,
                f"cannot read activation review: {error}",
            )
            return
        validate_r03_activation_review_text(text, self.problems)

    def validate_milestone_dag(self) -> None:
        path = self.phase_dir / "reviews/milestone-dag.tsv"
        header, rows = self.read_tsv(path, self.relative(path))
        edge_columns = {
            "importer_wave",
            "imported_wave",
            "direct_module_edges",
            "milestone_dependency",
            "reviewed_ordering_decision",
        }
        summary_columns = {
            "milestone_id",
            "wave_id",
            "depends_on",
            "direct_import_quotient_edges",
            "reviewed_ordering_decision",
        }
        edge_mode = edge_columns <= set(header)
        summary_mode = summary_columns <= set(header)
        if not edge_mode and not summary_mode:
            self.problems.add(
                self.relative(path),
                "milestone DAG requires either the edge-level or milestone-summary schema",
            )
            return
        scope_waves = {
            row.get("wave_id", "")
            for row in self.scope
            if row.get("phase_scope") == "in_scope"
        }
        worker_waves = scope_waves - {"I01"}
        phase_milestones = self.phase.get("milestones")
        if not isinstance(phase_milestones, list):
            self.problems.add("phase.json.milestones", "expected a list")
            return
        wave_to_milestone: dict[str, str] = {}
        dependencies: dict[str, set[str]] = {}
        for index, item in enumerate(phase_milestones):
            if not isinstance(item, dict):
                self.problems.add(f"phase.json.milestones[{index}]", "expected an object")
                continue
            milestone = item.get("milestone_id")
            waves = item.get("wave_ids")
            deps = item.get("depends_on")
            if not isinstance(milestone, str) or not isinstance(waves, list) or not isinstance(deps, list):
                self.problems.add(
                    f"phase.json.milestones[{index}]",
                    "requires milestone_id, wave_ids, and depends_on",
                )
                continue
            dependencies[milestone] = {value for value in deps if isinstance(value, str)}
            for wave in waves:
                if not isinstance(wave, str) or wave in wave_to_milestone:
                    self.problems.add(
                        f"phase.json.milestones[{index}]",
                        f"invalid or duplicate wave {wave!r}",
                    )
                else:
                    wave_to_milestone[wave] = milestone
        self.problems.require(
            set(wave_to_milestone) == scope_waves,
            "phase.json.milestones",
            f"milestones must cover every in-scope wave; missing={sorted(scope_waves-set(wave_to_milestone))}, extra={sorted(set(wave_to_milestone)-scope_waves)}",
        )
        known_milestones = set(dependencies)
        for milestone, deps in dependencies.items():
            unknown = deps - known_milestones
            if unknown:
                self.problems.add(self.relative(path), f"{milestone} has unknown dependencies {sorted(unknown)}")
        self.check_acyclic(dependencies, self.relative(path))
        live_edges = self.live_wave_import_edges(worker_waves)
        declared_edges: Counter[tuple[str, str]] = Counter()
        if edge_mode:
            edge_rows = [
                (index, row)
                for index, row in enumerate(rows)
                if row.get("importer_wave", "") not in {"", "-"}
            ]
            for index, row in edge_rows:
                importer = row.get("importer_wave", "")
                imported = row.get("imported_wave", "")
                context = f"{self.relative(path)}[{index}]"
                try:
                    count = int(row.get("direct_module_edges", ""))
                except ValueError:
                    count = 0
                self.record_dag_edge(
                    declared_edges,
                    importer,
                    imported,
                    count,
                    row.get("reviewed_ordering_decision", ""),
                    context,
                    worker_waves,
                    wave_to_milestone,
                    dependencies,
                    row.get("milestone_dependency", ""),
                )
        else:
            for index, row in enumerate(rows):
                context = f"{self.relative(path)}[{index}]"
                decision = row.get("reviewed_ordering_decision", "")
                if not decision or DEFERRED_RE.search(decision):
                    self.problems.add(context, "ordering decision must be explicit before activation")
                value = row.get("direct_import_quotient_edges", "")
                if value in {"", "-"}:
                    continue
                for encoded in split_values(value):
                    match = re.fullmatch(r"(R\d{2})->(R\d{2}):(\d+)", encoded)
                    if match is None:
                        self.problems.add(
                            context,
                            f"invalid direct-import quotient edge {encoded!r}",
                        )
                        continue
                    importer, imported, count_text = match.groups()
                    importer_milestone = wave_to_milestone.get(importer)
                    imported_milestone = wave_to_milestone.get(imported)
                    dependency_text = ""
                    if (
                        imported_milestone
                        and importer_milestone in dependencies.get(imported_milestone, set())
                    ):
                        dependency_text = f"{imported_milestone} depends on {importer_milestone}"
                    elif (
                        importer_milestone
                        and imported_milestone in dependencies.get(importer_milestone, set())
                    ):
                        dependency_text = f"{importer_milestone} depends on {imported_milestone}"
                    self.record_dag_edge(
                        declared_edges,
                        importer,
                        imported,
                        int(count_text),
                        decision,
                        context,
                        worker_waves,
                        wave_to_milestone,
                        dependencies,
                        dependency_text,
                    )
        if declared_edges != live_edges:
            self.problems.add(
                self.relative(path),
                "edge ledger must exactly equal live direct-import quotient; "
                f"missing={sorted((live_edges-declared_edges).items())}, "
                f"extra={sorted((declared_edges-live_edges).items())}",
            )
        milestone_columns = {"milestone_id", "wave_id", "depends_on"}
        if milestone_columns <= set(header):
            declared_milestones: dict[str, tuple[str, set[str]]] = {}
            for index, row in enumerate(rows):
                milestone = row.get("milestone_id", "")
                if milestone in {"", "-"}:
                    continue
                wave = row.get("wave_id", "")
                if milestone in declared_milestones or wave in {"", "-"}:
                    self.problems.add(
                        f"{self.relative(path)}[{index}]",
                        "milestone summary rows require unique milestone_id and wave_id",
                    )
                    continue
                declared_milestones[milestone] = (
                    wave,
                    set(split_values(row.get("depends_on", ""))),
                )
            expected_milestones = {
                milestone: (
                    next(wave for wave, owner in wave_to_milestone.items() if owner == milestone),
                    deps,
                )
                for milestone, deps in dependencies.items()
            }
            self.problems.require(
                declared_milestones == expected_milestones,
                self.relative(path),
                "milestone summary rows must exactly reproduce phase.json",
            )
        for wave in ("R01", "R02"):
            milestone = wave_to_milestone.get(wave)
            if milestone is not None and dependencies.get(milestone):
                self.problems.add(
                    self.relative(path),
                    f"activation wave {wave} must have no unaccepted successor dependencies",
                )

    def record_dag_edge(
        self,
        declared_edges: Counter[tuple[str, str]],
        importer: str,
        imported: str,
        count: int,
        decision: str,
        context: str,
        worker_waves: set[str],
        wave_to_milestone: dict[str, str],
        dependencies: dict[str, set[str]],
        dependency_text: str,
    ) -> None:
        if importer not in worker_waves or imported not in worker_waves or importer == imported:
            self.problems.add(context, "edge waves must be distinct known worker waves")
            return
        if count < 1:
            self.problems.add(context, "direct module-edge count must be positive")
            return
        declared_edges[importer, imported] += count
        if not decision or DEFERRED_RE.search(decision):
            self.problems.add(context, "ordering decision must be explicit before activation")
        match = re.fullmatch(r"(M\d{2}) depends on (M\d{2})", dependency_text)
        if match is None:
            self.problems.add(
                context,
                "direct-import endpoints must have a reviewed milestone dependency in one direction",
            )
            return
        milestone, dependency = match.groups()
        if dependency not in dependencies.get(milestone, set()):
            self.problems.add(
                context,
                f"{dependency_text} is absent from phase.json milestone dependencies",
            )
        endpoint_milestones = {
            wave_to_milestone.get(importer),
            wave_to_milestone.get(imported),
        }
        if {milestone, dependency} != endpoint_milestones:
            self.problems.add(
                context,
                "milestone dependency must order the two direct-import endpoint waves",
            )

    def check_acyclic(self, graph: dict[str, set[str]], context: str) -> None:
        visiting: set[str] = set()
        visited: set[str] = set()

        def visit(node: str) -> None:
            if node in visiting:
                self.problems.add(context, f"milestone dependency cycle includes {node}")
                return
            if node in visited:
                return
            visiting.add(node)
            for dependency in graph.get(node, set()):
                if dependency in graph:
                    visit(dependency)
            visiting.remove(node)
            visited.add(node)

        for node in graph:
            visit(node)

    def live_wave_import_edges(
        self, worker_waves: set[str]
    ) -> Counter[tuple[str, str]]:
        path_to_wave = {
            row["path"]: row["wave_id"]
            for row in self.scope
            if row.get("phase_scope") == "in_scope" and row.get("wave_id") in worker_waves
        }
        module_to_path = {module_from_path(path): path for path in path_to_wave}
        quotient: Counter[tuple[str, str]] = Counter()
        for path, wave in path_to_wave.items():
            source = self.root / path
            try:
                text = source.read_text(encoding="utf-8-sig", errors="replace")
            except OSError as error:
                self.problems.add("milestone import graph", f"cannot read {path}: {error}")
                continue
            for imported in IMPORT_RE.findall(remove_lean_comments(text)):
                target = module_to_path.get(imported)
                if target is None:
                    continue
                target_wave = path_to_wave[target]
                if target_wave != wave:
                    quotient[wave, target_wave] += 1
        return quotient


def run_self_test() -> int:
    problems = Problems()
    exact = PathRule("NumStability/A.lean", "exact")
    same = PathRule("numstability/a.lean", "exact")
    prefix = PathRule("NumStability", "prefix")
    distant = PathRule("NumStability/B", "prefix")
    problems.require(exact.intersects(same), "self-test", "casefold exact collision missed")
    problems.require(exact.intersects(prefix), "self-test", "exact/prefix collision missed")
    problems.require(exact.matches("NumStability/A.lean"), "self-test", "exact path match missed")
    problems.require(prefix.matches("NumStability/A.lean"), "self-test", "prefix path match missed")
    problems.require(not exact.intersects(distant), "self-test", "false path collision")
    problems.require(len(R01_PATHS) == 16, "self-test", "R01 constant drift")
    problems.require(len(R02_PATHS) == 28, "self-test", "R02 constant drift")
    problems.require(len(SHARED_CONSUMERS) == 11, "self-test", "shared consumer constant drift")
    problems.require(R01_PATHS.isdisjoint(R02_PATHS), "self-test", "selector constants overlap")
    problems.require(
        BRANCH_FACTS["B0001"]["changed_paths"] == 98
        and BRANCH_FACTS["B0002"]["changed_paths"] == 145,
        "self-test",
        "immutable delivery-scope counts drifted",
    )
    problems.require(
        R01_MERGE_PARENTS[1] == BRANCH_FACTS["B0001"]["delivery_sha"]
        and R02_MERGE_PARENTS
        == (R01_MERGE_SHA, BRANCH_FACTS["B0002"]["delivery_sha"]),
        "self-test",
        "exact merge-parent pins drifted from immutable deliveries",
    )
    problems.require(
        len(SUCCESSOR_GATE_IDS) == 12
        and SUCCESSOR_METRICS["production_modules"] == 2631
        and SUCCESSOR_MILESTONES == ["M01", "M02"],
        "self-test",
        "exact C0001 checkpoint contract drifted",
    )
    problems.require(
        len(SUCCESSOR_GATE_IDS) == 12
        and C0002_METRICS
        == {
            "production_modules": 2642,
            "unclassified_modules": 277,
            "mixed_modules": 9,
            "missing_module_docstrings": 13,
            "noncanonical_modules": 241,
            "declaration_bearing_umbrellas": 16,
            "unsorted_aggregate_imports": 0,
        }
        and C0002_MILESTONES == ["M01", "M02", "M11", "M12"],
        "self-test",
        "exact C0002 checkpoint contract drifted",
    )
    problems.require(
        R11_MERGE_PARENTS
        == (
            "de0ea2a54ea53d0e3724a72135d6da7d22739226",
            NEXT_BRANCH_FACTS["B0003"]["delivery_sha"],
        )
        and R12_MERGE_PARENTS
        == (R11_MERGE_SHA, NEXT_BRANCH_FACTS["B0004"]["delivery_sha"]),
        "self-test",
        "exact C0002 merge-parent pins drifted",
    )
    problems.require(
        next_branch_statuses(SUCCESSOR_CHECKPOINT_ID)
        == {"planned", "active", "delivered"}
        and next_branch_statuses(C0002_CHECKPOINT_ID) == {"accepted", "retired"}
        and "active" not in next_branch_statuses(C0002_CHECKPOINT_ID)
        and "delivered" not in next_branch_statuses(C0002_CHECKPOINT_ID)
        and next_projection_status(C0002_CHECKPOINT_ID) == "retired"
        and next_request_status(C0002_CHECKPOINT_ID) == "applied"
        and next_lane_operators(C0002_CHECKPOINT_ID) == ["claude-local"]
        and next_lane_operators(C0002_CHECKPOINT_ID)
        != ["claude-local", "codex-local"]
        and next_retirement_status("accepted") == "due"
        and next_retirement_status("retired") == "retired",
        "self-test",
        "C0002 lifecycle/authority negative-state ratchets drifted",
    )
    problems.require(
        len(C0002_RELEASED_SHARED_PATHS) == 11
        and all(path.startswith("NumStability/") for path in C0002_RELEASED_SHARED_PATHS),
        "self-test",
        "C0002 released shared-path set drifted",
    )
    problems.require(
        RFC3339_RE.fullmatch("2026-08-11T22:00:00Z") is not None
        and RFC3339_RE.fullmatch("2026-08-11") is None,
        "self-test",
        "RFC3339 lifecycle timestamp matcher drifted",
    )
    problems.require(
        set(NEXT_BRANCH_FACTS) == {"B0003", "B0004"}
        and {facts["wave"] for facts in NEXT_BRANCH_FACTS.values()}
        == {"R11", "R12"}
        and {facts["request"] for facts in NEXT_BRANCH_FACTS.values()}
        == {"R0003", "R0004"},
        "self-test",
        "next-wave B/P/R identity constants drifted",
    )
    problems.require(
        NEXT_BRANCH_FACTS["B0003"]["owned_count"] == 65
        and NEXT_BRANCH_FACTS["B0004"]["owned_count"] == 3
        and NEXT_BRANCH_FACTS["B0003"]["forbidden_exact"] == 2631 - 65
        and NEXT_BRANCH_FACTS["B0004"]["forbidden_exact"] == 2631 - 3,
        "self-test",
        "C0001 selector/complement counts drifted",
    )
    problems.require(
        NEXT_BRANCH_FACTS["B0003"]["lane"]
        == NEXT_BRANCH_FACTS["B0004"]["lane"]
        == "claude-lane"
        and {
            NEXT_BRANCH_FACTS["B0003"]["operator"],
            NEXT_BRANCH_FACTS["B0004"]["operator"],
        }
        == {"claude-local", "codex-local"},
        "self-test",
        "reviewed next-wave lane/operator constants drifted",
    )
    problems.require(
        NEXT_BRANCH_FACTS["B0003"]["destinations"].isdisjoint(
            NEXT_BRANCH_FACTS["B0004"]["destinations"]
        )
        and len(NEXT_REQUEST_OVERLAP) == 3,
        "self-test",
        "next-wave destination/request-overlap constants drifted",
    )
    problems.require(
        path_list_sha256(NEXT_REQUEST_OVERLAP)
        == NEXT_BRANCH_FACTS["B0004"]["request_path_sha256"]
        and NEXT_BRANCH_FACTS["B0004"]["request_paths"] == 3,
        "self-test",
        "R0004 exact path-list digest drifted",
    )
    next_digests = [
        C0002_COMBINED_BASELINE_SHA256,
        C0002_COMBINED_SUMMARY_SHA256,
        C0002_INVENTORY_SHA256,
        C0002_INTEGRATOR_LEDGER_SHA256,
        C0002_GATES_SHA256,
        NEXT_COMBINED_BASELINE_SHA256,
        NEXT_INVENTORY_SHA256,
        NEXT_PROJECTION_CHECKER_SHA256,
        NEXT_CANDIDATE_SHA256,
        NEXT_PROJECTION_REPLAY_SHA256,
        NEXT_OPERATOR_AUTHORIZATION_SHA256,
        NEXT_OVERLAP_FACTS_SHA256,
        NEXT_IMPORT_REVIEW_SHA256,
        NEXT_UNION_PATCH_SHA256,
        NEXT_UNION_POSTIMAGES_SHA256,
        NEXT_UNION_REVIEW_SHA256,
        *[
            str(facts[key])
            for facts in NEXT_BRANCH_FACTS.values()
            for key in (
                "selector_sha256",
                "projection_sha256",
                "projection_payload_sha256",
                "private_map_sha256",
                "private_closure_sha256",
                "request_path_sha256",
                "request_patch_sha256",
                "request_postimages_sha256",
            )
        ],
        *[
            str(facts[key][1])
            for facts in NEXT_BRANCH_FACTS.values()
            for key in ("delivery_report", "delivery_scope")
        ],
    ]
    problems.require(
        all(SHA256_RE.fullmatch(digest) is not None for digest in next_digests),
        "self-test",
        "next-wave SHA-256 constants are malformed",
    )
    problems.require(
        all(
            SHA1_RE.fullmatch(str(facts["delivery_sha"])) is not None
            for facts in NEXT_BRANCH_FACTS.values()
        )
        and all(
            SHA1_RE.fullmatch(value) is not None
            for value in (C0002_CODE_SHA, R11_MERGE_SHA, R12_MERGE_SHA)
        ),
        "self-test",
        "C0002 code/merge/delivery SHA-1 constants are malformed",
    )
    problems.require(
        (R03_BRANCH_ID, R03_PROJECTION_ID, R03_REQUEST_ID, R03_WAVE_ID)
        == ("B0005", "P0005", "R0005", "R03")
        and R03_OWNER_COUNT == 47
        and R03_FORBIDDEN_EXACT_COUNT == 2642 - 47
        and R03_COUNTS
        == {
            "declarations": 2389,
            "signature_edges": 28180,
            "body_edges": 42404,
            "union_edges": 43943,
        }
        and R03_PRIVATE_CLOSURE_ROWS
        == R03_PRIVATE_COUNT + R03_PRIVATE_REVERSE_DEPENDENTS
        and R03_PRIVATE_SELECTED_OWNER_ROWS == 2063,
        "self-test R03 constants",
        "exact C0002/R03 identities, graph counts, or closure arithmetic drifted",
    )
    problems.require(
        all(
            isinstance(digest, str) and SHA256_RE.fullmatch(digest) is not None
            for digest in R03_ARTIFACT_SHA256.values()
        )
        and SHA256_RE.fullmatch(R03_ACTIVATION_REVIEW_SHA256) is not None
        and SHA1_RE.fullmatch(R03_PLANNED_CONTROL_SHA) is not None
        and R03_PLANNED_CONTROL_CI_RUN.isdecimal()
        and R03_PLANNED_CONTROL_CI_JOB.isdecimal()
        and R03_REQUEST_PATH_COUNT == 121
        and isinstance(R03_REQUEST_PATH_SHA256, str)
        and SHA256_RE.fullmatch(R03_REQUEST_PATH_SHA256) is not None
        and R03_DESTINATIONS is not None
        and len(R03_DESTINATIONS) == 50
        and not any("Chapter72" in path for path in R03_DESTINATIONS)
        and len(R03_RERESERVED_C0002_PATHS) == 4
        and R03_RERESERVED_C0002_PATHS <= C0002_RELEASED_SHARED_PATHS,
        "self-test R03 artifact ratchets",
        "R03 hashes, request/destination facts, or reviewed re-reservations drifted",
    )
    r03_test_route_sha = "A" * 64
    r03_planned = R03EpochSnapshot(
        branch_base_checkpoint_id=C0002_CHECKPOINT_ID,
        branch_base_sha=C0002_CODE_SHA,
        branch_status="planned",
        operator_ids=(R03_OPERATOR_ID,),
        lane_operator_ids=(R03_OPERATOR_ID,),
        selector_sha256=R03_SELECTOR_SHA256,
        selector_rows=R03_OWNER_COUNT,
        selector_matches_inventory=True,
        route_sha256=r03_test_route_sha,
        activation_evidence=(),
        delivery={"commit_sha": None, "report": None, "scope_evidence": None},
        integration={
            "method": None,
            "accepted_checkpoint_id": None,
            "accepted_sha": None,
        },
        retirement={
            "remote_ref": R03_REMOTE_REF,
            "rule": "delivery_ancestor_of_green_checkpoint",
            "status": "not_due",
            "retired_at": None,
            "retired_by": None,
            "ancestry_checkpoint_id": None,
        },
        projection_base_checkpoint_id=C0002_CHECKPOINT_ID,
        projection_status="active",
        projection_selector_sha256=R03_SELECTOR_SHA256,
        request_target_checkpoint_id=C0002_CHECKPOINT_ID,
        request_target_base_sha=C0002_CODE_SHA,
        request_status="active",
        request_resolution={
            "checkpoint_id": None,
            "commit_sha": None,
            "reason": None,
            "resolved_at": None,
            "resolved_by": None,
            "validation_evidence": [],
        },
        r07_milestone_status="planned",
        worker_shared_leaks=(),
        request_unreserved_paths=(),
    )
    r03_active = replace(
        r03_planned,
        branch_status="active",
        activation_evidence=(
            Artifact(R03_ACTIVATION_REVIEW_PATH, R03_ACTIVATION_REVIEW_SHA256),
        ),
    )
    for label, snapshot in (("planned", r03_planned), ("active", r03_active)):
        positive_r03_problems = Problems()
        validate_r03_epoch_snapshot(
            snapshot,
            positive_r03_problems,
            expected_route_sha256=r03_test_route_sha,
        )
        problems.require(
            not positive_r03_problems.messages,
            f"self-test R03 {label} positive",
            f"valid {label} epoch rejected: {positive_r03_problems.messages}",
        )

    r03_review_text = f"""# R03 activation review

- Activated at: `2026-08-13T11:30:58Z`
- Authority: `primary-human`, exercising the explicitly granted branch-registry, activation-control, main-push, and worktree-creation authority
- Branch / wave: `{R03_BRANCH_ID}` / `{R03_WAVE_ID}`
- Lane / operator: `{R03_LANE_ID}` / `{R03_OPERATOR_ID}`
- Current checkpoint: `{C0002_CHECKPOINT_ID}`
- Accepted C0002 checkpoint and immutable worker base: `{C0002_CODE_SHA}`
- Planned-control commit: `{R03_PLANNED_CONTROL_SHA}`
- Planned-control CI: Lean CI push run `{R03_PLANNED_CONTROL_CI_RUN}`, job `{R03_PLANNED_CONTROL_CI_JOB}`, completed `success`

The planned-control gate was green for the exact planned-control commit before any B0005 ref or worktree was created. The checkout used `core.autocrlf=false`, `core.eol=lf`, and `core.safecrlf=false`, then an explicit nonexistent-tip lease.

| Fact | Exact value |
| --- | --- |
| Local branch | `{R03_BRANCH_NAME}` |
| Local branch tip | `{C0002_CODE_SHA}` |
| Remote ref | `{R03_REMOTE_REF}` |
| Remote ref tip | `{C0002_CODE_SHA}` |
| Named worktree | `{R03_PLANNED_WORKTREE}` |
| Worktree HEAD | `{C0002_CODE_SHA}` |

At activation, the named worktree had empty tracked and untracked status. No worker commit, production edit, or R0005 application exists. R07 remains unactivated and M07 remains `planned`.

Workers may edit only B0005-owned paths, B0005 destination prefixes, `NumStabilityTest/Reorganization/R03/`, and `docs/architecture/deliveries/R03/`. All 121 R0005 paths remain integrator-only. R0005 is context-free; any disposable replay must use `git apply --unidiff-zero`.

No implementation began before activation-control CI. The worker remains frozen through the full `NumStability` and `NumStabilityTest` build.
"""
    positive_review_problems = Problems()
    validate_r03_activation_review_text(
        r03_review_text,
        positive_review_problems,
        context="self-test R03 activation review",
    )
    problems.require(
        not positive_review_problems.messages,
        "self-test R03 activation review positive",
        f"valid activation review rejected: {positive_review_problems.messages}",
    )

    r03_negative_cases: list[tuple[str, R03EpochSnapshot, str]] = [
        (
            "wrong base",
            replace(r03_active, branch_base_sha=INTEGRATED_CODE_SHA),
            ".base:",
        ),
        (
            "wrong projection/request base",
            replace(
                r03_active,
                projection_base_checkpoint_id=SUCCESSOR_CHECKPOINT_ID,
                request_target_base_sha=INTEGRATED_CODE_SHA,
            ),
            ".lifecycle:",
        ),
        (
            "selector drift",
            replace(r03_active, selector_rows=R03_OWNER_COUNT - 1),
            ".selector:",
        ),
        (
            "route/hash drift",
            replace(r03_active, route_sha256="B" * 64),
            ".routes:",
        ),
        (
            "unauthorized operator",
            replace(r03_active, operator_ids=("claude-local",)),
            ".authority:",
        ),
        (
            "planned activation evidence",
            replace(
                r03_planned,
                activation_evidence=(
                    Artifact(
                        R03_ACTIVATION_REVIEW_PATH,
                        R03_ACTIVATION_REVIEW_SHA256,
                    ),
                ),
            ),
            ".activation:",
        ),
        (
            "active missing activation review",
            replace(r03_active, activation_evidence=()),
            ".activation:",
        ),
        (
            "active stale activation review",
            replace(
                r03_active,
                activation_evidence=(
                    Artifact(R03_ACTIVATION_REVIEW_PATH, "B" * 64),
                ),
            ),
            ".activation:",
        ),
        (
            "shared-path leakage",
            replace(
                r03_active,
                worker_shared_leaks=("docs/architecture/tiers.json",),
            ),
            ".shared_paths:",
        ),
        (
            "unreserved request leakage",
            replace(
                r03_active,
                request_unreserved_paths=("NumStabilityTest.lean",),
            ),
            ".shared_paths:",
        ),
        (
            "premature delivery",
            replace(
                r03_active,
                delivery={
                    "commit_sha": "1" * 40,
                    "report": None,
                    "scope_evidence": None,
                },
            ),
            ".lifecycle:",
        ),
        (
            "premature integration",
            replace(
                r03_active,
                integration={
                    "method": "merge",
                    "accepted_checkpoint_id": C0002_CHECKPOINT_ID,
                    "accepted_sha": C0002_CODE_SHA,
                },
            ),
            ".lifecycle:",
        ),
        (
            "premature projection retirement",
            replace(r03_active, projection_status="retired"),
            ".lifecycle:",
        ),
        (
            "premature request resolution",
            replace(
                r03_active,
                request_status="applied",
                request_resolution={
                    "checkpoint_id": C0002_CHECKPOINT_ID,
                    "commit_sha": C0002_CODE_SHA,
                    "reason": "premature",
                    "resolved_at": "2026-08-13T00:00:00Z",
                    "resolved_by": "primary-human",
                    "validation_evidence": [],
                },
            ),
            ".lifecycle:",
        ),
        (
            "premature retirement due",
            replace(
                r03_active,
                retirement={
                    **r03_active.retirement,
                    "status": "due",
                },
            ),
            ".lifecycle:",
        ),
        (
            "R07 activation",
            replace(r03_active, r07_milestone_status="ready"),
            ".r07:",
        ),
    ]
    for label, mutated, diagnostic in r03_negative_cases:
        mutation_problems = Problems()
        validate_r03_epoch_snapshot(
            mutated,
            mutation_problems,
            expected_route_sha256=r03_test_route_sha,
        )
        problems.require(
            any(diagnostic in message for message in mutation_problems.messages),
            f"self-test R03 {label}",
            f"adversarial mutation was not rejected with {diagnostic}: {mutation_problems.messages}",
        )

    r03_review_negative_cases = (
        (
            "wrong activation base",
            r03_review_text.replace(
                "- Accepted C0002 checkpoint and immutable worker base: "
                f"`{C0002_CODE_SHA}`",
                "- Accepted C0002 checkpoint and immutable worker base: "
                f"`{INTEGRATED_CODE_SHA}`",
            ),
            ".identity:",
        ),
        (
            "wrong local branch tip",
            r03_review_text.replace(
                f"| Local branch tip | `{C0002_CODE_SHA}` |",
                f"| Local branch tip | `{INTEGRATED_CODE_SHA}` |",
            ),
            ".tips:",
        ),
        (
            "wrong remote ref tip",
            r03_review_text.replace(
                f"| Remote ref tip | `{C0002_CODE_SHA}` |",
                f"| Remote ref tip | `{INTEGRATED_CODE_SHA}` |",
            ),
            ".tips:",
        ),
        (
            "wrong worktree tip",
            r03_review_text.replace(
                f"| Worktree HEAD | `{C0002_CODE_SHA}` |",
                f"| Worktree HEAD | `{INTEGRATED_CODE_SHA}` |",
            ),
            ".tips:",
        ),
    )
    for label, mutated_text, diagnostic in r03_review_negative_cases:
        mutation_problems = Problems()
        validate_r03_activation_review_text(
            mutated_text,
            mutation_problems,
            context="self-test R03 activation review",
        )
        problems.require(
            any(diagnostic in message for message in mutation_problems.messages),
            f"self-test R03 review {label}",
            f"adversarial review mutation was not rejected with {diagnostic}: "
            f"{mutation_problems.messages}",
        )
    with tempfile.TemporaryDirectory(prefix="completion-validator-self-test-") as directory:
        tsv = Path(directory) / "sample.tsv"
        tsv.write_text("module\tpath\nA\tA.lean\n", encoding="utf-8", newline="\n")
        digest = sha256_path(tsv)
        problems.require(SHA256_RE.fullmatch(digest) is not None, "self-test", "SHA-256 helper failed")
        raw = gzip.compress(
            b"format\t2\ndeclaration\tA.x\tA\ttheorem\tprivate\n"
            b"declaration\tB.y\tB\ttheorem\tpublic\n"
            b"edge\tsignature\tA.x\tB.y\nedge\tbody\tA.x\tB.y\n",
            mtime=0,
        )
        graph = Path(directory) / "graph.tsv.gz"
        graph.write_bytes(raw)
        validator = CompletionValidator(ROOT, DEFAULT_PHASE_DIR)
        counts = validator.parse_projection_graph(graph, "self-test graph")
        problems.require(
            counts
            == {
                "declarations": 2,
                "signature_edges": 1,
                "body_edges": 1,
                "union_edges": 1,
            },
            "self-test",
            f"projection counts drifted: {counts}",
        )
        declarations = validator.parse_projection_declarations(
            graph, "self-test graph"
        )
        problems.require(
            declarations
            == {
                ("A", "A.x"): ("theorem", "private"),
                ("B", "B.y"): ("theorem", "public"),
            },
            "self-test",
            f"projection declaration parser drifted: {declarations}",
        )
        cyclic_problems = Problems()
        validator.problems = cyclic_problems
        validator.check_acyclic({"M1": {"M2"}, "M2": {"M1"}}, "self-test cycle")
        problems.require(
            any("cycle" in message for message in cyclic_problems.messages),
            "self-test",
            "cycle was not rejected",
        )
    if problems.messages:
        for message in problems.messages:
            print(f"completion phase self-test failure: {message}", file=sys.stderr)
        return 1
    print(
        "completion phase self-test passed: exact C0000/C0001/C0002 constants, shared "
        "consumers and releases, next-wave B/P/R lifecycle/authority ratchets, merge/SHA "
        "pins, path collisions, format-2 declaration/signature/body parsing, and DAG "
        "cycle rejection; exact C0002-rooted R03 planned/active states and activation "
        "review plus missing/stale evidence, wrong-base/tip, selector, route/hash, "
        "authority, R07, shared-path, and lifecycle mutations"
    )
    return 0


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--phase-dir",
        type=Path,
        default=DEFAULT_PHASE_DIR,
        help=f"successor phase directory (default: {DEFAULT_PHASE_DIR.as_posix()})",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="run isolated positive/negative helper tests without phase artifacts",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    if args.self_test:
        return run_self_test()
    validator = CompletionValidator(ROOT, args.phase_dir)
    problems = validator.run()
    if problems.messages:
        for message in problems.messages:
            print(f"completion phase violation: {message}", file=sys.stderr)
        print(
            f"completion phase failed with {len(problems.messages)} violation(s)",
            file=sys.stderr,
        )
        return 1
    print(
        f"completion phase passed: {validator.current_checkpoint_id} control state, "
        "C0000-pinned 2,593-row freeze, 492-row scope, exact R01/R02 98/145-path "
        "delivery evidence, projections, routes, private closure, tests, "
        "overlap proofs, postimages, reviewed union, milestone DAG, and exact "
        "C0001-pinned synchronous R11/R12 planned/active/delivered or C0002 "
        "accepted/retired controls with exact checkpoint evidence; plus the singleton "
        "exact-C0002 B0005/P0005/R0005 planned/active R03 epoch"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
