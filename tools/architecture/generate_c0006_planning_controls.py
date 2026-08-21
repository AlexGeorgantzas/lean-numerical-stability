#!/usr/bin/env python3
"""Audit and deterministically stage the exact-C0005 R07 planning inputs.

This planning framework derives the R07 selector,
format-2 declaration projection, direct consumers, and overlap facts from the
accepted C0005 inventory/code/graph.  It also defines and validates the fresh
semantic-review schemas needed before B0010/P0010/R0011 may be emitted.

Historical W06 artifacts are not inputs.  ``--emit-review-drafts`` writes only
the fixed non-authority review candidates.  After those exact bytes receive a
hash-pinned primary-human review, ``--materialize-reviewed-controls`` may write
the planned B0010/P0010/R0011 control files for local checker completion.  This
tool never creates Git refs, worktrees, commits, or pushes.
"""

from __future__ import annotations

import argparse
import csv
import difflib
import gzip
import hashlib
import io
import json
import os
import re
import subprocess
import sys
from collections import Counter, defaultdict, deque
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Sequence


ROOT = Path(__file__).resolve().parents[2]
PHASE = ROOT / "docs/architecture/phases/2026-08-repository-reorganization-completion"
BRANCHES = PHASE / "branches"
PROJECTIONS = PHASE / "projections"
REQUESTS = PHASE / "requests"
SELECTORS = PHASE / "selectors"
REVIEWS = PHASE / "reviews"

PHASE_ID = "repository-reorganization-completion-2026-08"
BASE_CHECKPOINT_ID = "C0005"
BASE_CODE_SHA = "ad92bbfae62d538f3e52829a269a846688a8e213"
BASE_CODE_TREE = "21efef4bb0a2b7ce0e5e5c16e86f2d35963cfc3c"
ACCEPTED_CONTROL_SHA = "52552c8e3ddd9381f36bec8ccb694cf8c830cd49"
ACCEPTED_CONTROL_TREE = "6240f606b7208cd39bf710f619278fa2c8c64f5f"

WAVE_ID = "R07"
MILESTONE_ID = "M07"
BRANCH_ID = "B0010"
PROJECTION_ID = "P0010"
REQUEST_ID = "R0011"
LANE_ID = "codex-lane"
OPERATOR_ID = "codex-local"
OWNER_ID = "primary-human"
REVIEW_ID = "R07-C0005-semantic-v1"
BRANCH_NAME = "codex/reorg-completion-2026-08-r07-matrix-functions-powers-ch18"

CHECKPOINT = PHASE / "checkpoints/C0005.json"
BASELINE = PHASE / "baselines/C0005-combined.json"
BASELINE_SUMMARY = PHASE / "baselines/C0005-combined.md"
INVENTORY = PHASE / "checkpoints/C0005-inventory.tsv"
PROJECTION_CHECKER = ROOT / "tools/architecture/check_completion_phase_projection.py"
SHARED_POSTIMAGE_RENDERER = ROOT / "tools/architecture/r07_shared_postimages.py"
COMPATIBILITY = ROOT / "docs/architecture/COMPATIBILITY.md"
PLANNED_WORKTREE_BASENAME = "completion-r07-codex"

CHECKPOINT_SHA256 = "CBC895B27F9A81C74EF885D4246776E3F29AB58D4095A45EEECF3D6CFBDFD47F"
BASELINE_SHA256 = "2FC0C95FFECF114A2EDB8C14DB8C2874BDBB85FCEBA722C345AA084B3E97C02A"
BASELINE_SUMMARY_SHA256 = "69FF97AF03CD489AAA9A47240169217628293CD1DB33AAB02D174BF501B0EB49"
INVENTORY_SHA256 = "7C383B1AF57F65F9559C81402013412172CC93B623F7ED2E26968B9C7AFB4172"
GRAPH_SHA256 = "85C7B3D06019C92B7234EF5422681E46A9825F733A1AC4AB58A3F8B9B91C345B"
PROJECTION_CHECKER_SHA256 = "0F32935ED1EFDD2BD4D6A4C346F3E8300C86DB1D4A3551A17165479226109220"
SHARED_POSTIMAGE_RENDERER_SHA256 = "3ECC5D64FF466E2982CAF750B49F183F11907F460C3625744825ACB522FA5C86"

ACCEPTED_CI_EVIDENCE = {
    "workflow": "Lean CI",
    "run_id": "32394769969",
    "job_id": "96508922114",
    "head_sha": ACCEPTED_CONTROL_SHA,
    "conclusion": "success",
}
CI_ATTESTATION = PHASE / "reviews/C0005-acceptance-control-ci.json"
CI_ATTESTATION_SHA256 = "977AD3B2B9BCCF468A78F304A09B5D349413E69D83E970C98C20463313EECB86"
EXPECTED_CI_CARDINALITY = {
    "artifact_count": 0,
    "job_count": 1,
    "job_ids": [96508922114],
    "pull_request_count": 0,
    "referenced_workflow_count": 0,
}
EXPECTED_CI_STEPS = (
    (1, "Set up job"),
    (2, "Run actions/checkout@v5"),
    (3, "Check architecture source graph and Python tooling"),
    (4, "Build library and smoke tests"),
    (8, "Post Run actions/checkout@v5"),
    (9, "Complete job"),
)

PINNED_CONFIG_INPUTS = {
    ROOT / "docs/architecture/phases/active-phase.json": "C99061ACCE56AF121B1ACF0FBE2C757B53602A5A8599DC93193871095D3AB360",
    PHASE / "phase.json": "B7DBE6F65CE9F40C6B26582AA13D09826FA00A4B28F8A2853D764FBA5FE4301D",
    ROOT / "lakefile.toml": "9F2CF5039B95F83CD9969F033A2862378D0B80931FCA277AD9DD227A5408D1A4",
    ROOT / "lean-toolchain": "FDF7CCFE204CAFF50FAB1913B9F13A763BE5384E87D14555C9FDCB2BE2B9F7F8",
    ROOT / "lake-manifest.json": "CCFE8A72D6D227AEBFE4E58575DDF2A2AEF03B795052F97B770C36F684CC5774",
    ROOT / ".github/workflows/lean_action_ci.yml": "0A9E8B535D7A780623557A107E00D02B44513E650A4F6C5A259FC0323A435FD7",
    ROOT / ".gitattributes": "A2CB0FAFF284A6DD64B35BB985E8CCD8C5B9AB31E8EC78A82802F799634DAC1F",
    ROOT / ".gitignore": "7CDB46F486C75F667BFEE8DAAF542D2B8174C344AEFC7D655F1263A9D3FC5F7A",
}

TERMINAL_CONTROL_INPUTS = {
    PHASE / "branches/B0008.json": "7B8159BD17D7303CC68C6D9EE0AFD2520A77A19065F2731E7F5C48B8A95143A3",
    PHASE / "branches/B0009.json": "3698662FC90E4CF49663794D695B6CC73617FAA3C21E0550240334961A21BBA2",
    PHASE / "projections/P0008.json": "4E455E14CA6EFE7A8EEFC6319BF822C6FD08906F102CFB50E156B7017B1CA41F",
    PHASE / "projections/P0009.json": "8A2A9DB162C16F55583CD8B0704615BD000154A3EEB50EF1C7192C66CD36DE6E",
    PHASE / "requests/R0009.json": "FA10EFE39EF3F822187BB529528CB89F8886C2B65C21AE70A389B311023D2DE5",
    PHASE / "requests/R0010.json": "13A7B93CEC6F6A15257FCCC482E38682023350A4BD5CA5267BA909934139F2A3",
}

EXPECTED_PRODUCTION_MODULES = 2818
EXPECTED_OWNER_COUNT = 45
EXPECTED_UNCLASSIFIED_OWNERS = 43
EXPECTED_DECLARATIONS = 194
EXPECTED_PUBLIC_DECLARATIONS = 150
EXPECTED_PRIVATE_DECLARATIONS = 44
EXPECTED_SIGNATURE_EDGES = 243
EXPECTED_BODY_EDGES = 752
EXPECTED_UNION_EDGES = 775
EXPECTED_INTERNAL_IMPORT_EDGES = 48
EXPECTED_EXTERNAL_IMPORT_EDGES = 73
EXPECTED_EXTERNAL_CONSUMERS = 24
EXPECTED_POST_MOVE_IMPORT_ROWS = 760
EXPECTED_POST_MOVE_IMPORT_SHA256 = (
    "788DC7987191EBF9325F8DE253DC793FAF3BF8AB1119F201B5E0918971C194E1"
)
EXPECTED_EXTERNAL_OWNER_SUPPLY_ROWS = 31
EXPECTED_EXTERNAL_OWNER_SUPPLY_SHA256 = (
    "EC3E65376EA724B15A54A268731345A22EFF64AE2545754EC3BF6CFEFABFD9A9"
)
EXPECTED_UNCLASSIFIED_QUEUE = {"R07": 43, "R09": 72, "R10": 18}
EXPECTED_R07_ACTION_COUNTS = {
    "classify;document;migrate;rename;split": 1,
    "classify;document;migrate;split": 19,
    "classify;migrate;rename;split": 1,
    "classify;migrate;split": 22,
    "rename": 2,
}

NAMING_ONLY_OWNERS = frozenset(
    {
        "NumStability.Analysis.CStarMatrices.Basic.RealMatrixBridge",
        "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.KreissBridge",
    }
)

INVENTORY_HEADER = (
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
DECLARATION_ROUTES_HEADER = (
    "baseline_owner_module",
    "baseline_declaration_name",
    "visibility",
    "kind",
    "projection_order",
    "source_ordinal",
    "destination_module",
    "route_class",
    "normalization_decision",
)
SOURCE_COMMANDS_HEADER = (
    "owner_module",
    "path",
    "base_blob_oid",
    "baseline_declaration_name",
    "ilean_path",
    "ilean_sha256",
    "ilean_root",
    "source_ordinal",
    "start_line_0",
    "start_column_0",
    "end_line_0",
    "end_column_0",
    "selection_start_line_0",
    "selection_start_column_0",
    "selection_end_line_0",
    "selection_end_column_0",
    "command_sha256",
)
MODULE_ROUTES_HEADER = (
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
WRAPPER_PLAN_HEADER = (
    "owner_module",
    "path",
    "base_blob_oid",
    "preserved_imports",
    "appended_imports",
    "post_imports",
)
PRIVATE_CLOSURE_HEADER = (
    "declaration",
    "owner_module",
    "visibility",
    "selected_owner",
    "closure_role",
    "seed_memberships",
    "membership_witnesses",
    "co_route_component",
    "minimum_depth",
    "signature_edge_span",
    "body_edge_span",
)
PRIVATE_NORMALIZATION_HEADER = (
    "old_private",
    "new_private",
    "destination_module",
)
DESTINATION_DAG_HEADER = (
    "from_destination",
    "to_destination",
    "signature_edges",
    "body_edges",
)
CONSUMERS_HEADER = (
    "consumer_module",
    "consumer_path",
    "consumer_scope",
    "old_import",
    "new_import",
)
TEST_PLAN_HEADER = (
    "test_class",
    "target",
    "imports",
    "expected_declarations",
    "forbidden_imports",
    "purpose",
)
TIER_ASSIGNMENTS_HEADER = ("module", "tier", "reason")
SCOPE_RULES_HEADER = ("scope", "match", "path", "authority_id", "rationale")
REQUEST_PLAN_HEADER = (
    "path",
    "base_blob_oid",
    "transform",
    "add_imports",
    "remove_imports",
    "declaration_use_witnesses",
    "test_witnesses",
    "rationale",
)
EXTERNAL_OWNER_SUPPLY_HEADER = (
    "destination_module",
    "referenced_owner_module",
    "signature_edge_count",
    "body_edge_count",
    "recursive_frontier_direct",
    "post_r0011_supply",
)
POST_MOVE_IMPORT_MANIFEST_HEADER = (
    "module",
    "role",
    "import_order",
    "lean_import_line",
    "provenance",
)
DESTINATION_PLAN_HEADER = (
    "module",
    "tier",
    "existence",
    "base_blob_oid",
    "rationale",
)
REVIEW_METADATA_KEYS = frozenset(
    {
        "accepted_control_sha",
        "artifacts",
        "base_checkpoint_id",
        "base_code_sha",
        "decision",
        "phase_id",
        "record_kind",
        "review_id",
        "reviewed_at",
        "reviewer_id",
        "schema_version",
    }
)

REVIEW_DRAFT_PATHS = {
    "declaration_plan": PHASE / "reviews/R07-declaration-routes.tsv",
    "destination_plan": PHASE / "reviews/R07-destinations.tsv",
    "module_plan": PHASE / "reviews/R07-module-routes.tsv",
    "source_command_plan": PHASE / "reviews/R07-source-commands.tsv",
    "wrapper_plan": PHASE / "reviews/R07-wrapper-imports.tsv",
}
COMPATIBILITY_DRAFT = PHASE / "reviews/R07-COMPATIBILITY-postimage.md"
PRIMARY_REVIEW = PHASE / "reviews/R07-primary-human-review.json"
PLANNED_CONTROL_CONTRACT = PHASE / "reviews/R07-planned-control-contract.json"
DERIVED_REVIEW_DRAFT_PATHS = {
    "consumer_plan": PHASE / "reviews/R07-consumers.tsv",
    "destination_dag": PHASE / "reviews/R07-destination-dag.tsv",
    "external_owner_supply": PHASE / "reviews/R07-external-owner-supply.tsv",
    "inventory": PHASE / "reviews/R07-inventory.tsv",
    "overlap_review": PHASE / "reviews/R07-overlap-review.json",
    "post_move_import_manifest": PHASE / "reviews/R07-post-move-import-manifest.tsv",
    "private_closure": PHASE / "reviews/R07-private-closure.tsv",
    "private_normalization": PHASE / "reviews/R07-private-normalization.tsv",
    "projection_review": PHASE / "reviews/R07-projection-review.json",
    "r0011_import_manifest": PHASE / "reviews/R07-R0011-import-manifest.tsv",
    "r0011_render_review": PHASE / "reviews/R07-R0011-render-review.json",
    "r0011_request_plan": PHASE / "reviews/R07-R0011-request-plan.tsv",
    "review_packet": PHASE / "reviews/R07-review-packet.json",
    "scope_rules": PHASE / "reviews/R07-scope-rules.tsv",
    "test_plan": PHASE / "reviews/R07-test-plan.tsv",
    "tier_assignments": PHASE / "reviews/R07-tier-assignments.tsv",
}

PROTECTED_PREFIXES = (
    "NumStabilityTest/Import/",
    "NumStabilityTest/Worker/",
    "benchmark-results/",
    "docs/architecture/phases/",
    "tools/architecture/",
)

ROUTE_CLASSES = frozenset(
    {
        "classify_compatibility",
        "relocate_split",
        "relocate_whole",
        "retain_document",
        "umbrella_extract",
    }
)
FINAL_TIERS = frozenset(
    {"aggregate", "compatibility", "internal", "reusable", "source", "upstream"}
)
REUSABLE_BANNED_COMPONENTS = frozenset(
    {
        "Actual",
        "Bridge",
        "Chapter",
        "Closure",
        "Endpoint",
        "Higham",
        "Operational",
        "Remaining",
        "Source",
        "Whole",
    }
)

NEW_DESTINATIONS = frozenset(
    {
        "NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.BlockDiagonal",
        "NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.BlockDiagonalCompression",
        "NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.ColumnPair",
        "NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.ColumnPairPinching",
        "NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.ColumnPairRangeProjection",
        "NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.ColumnPairRangeReflection",
        "NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.FiniteDimensional",
        "NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.FiniteMatrixOrder",
        "NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.FiniteRealEmbedding",
        "NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.FiniteRealOrder",
        "NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.ProjectionReflection",
        "NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.RectangularCompression",
        "NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.RectangularMultiplication",
        "NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.ReflectionAverage",
        "NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.StrictPositivity",
        "NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.NormalMatrices.Powers",
        "NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.NormalCharacterization.Schur",
        "NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.SchurBinomialBounds.Estimates",
        "NumStability.Analysis.LinearOperators.Schur.Complex.NormalTriangular.Diagonal",
        "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.ArcLengthPowerBounds.FiniteDimension",
        "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.FiniteDimensionalPowerBounds.Kreiss",
        "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarArcLength.Variation",
        "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarCrossingBounds.Polynomial",
        "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.ResolventCoefficients.Analytic",
        "NumStability.Analysis.LinearOperators.NumericalRadius.Berger.GeneralPowerInequality.Powers",
        "NumStability.Analysis.LinearOperators.NumericalRadius.Berger.Internal.HermitianEuclideanSpaceNotation",
        "NumStability.Analysis.LinearOperators.NumericalRadius.Berger.GeneralPowerInequality.PowersOfTwo",
        "NumStability.Analysis.LinearOperators.NumericalRadius.Core.Internal.EuclideanSpaceNotation",
        "NumStability.Analysis.LinearOperators.Pseudospectra.Resolvent.Internal.ScalarNotation",
        "NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.SpijkerKreissUnconditional.Bounds",
    }
)
NEW_DECLARATION_DESTINATIONS = NEW_DESTINATIONS
SOURCE_DESTINATIONS = frozenset(
    module
    for module in NEW_DECLARATION_DESTINATIONS
    if module.startswith("NumStability.Source.")
)
INTERNAL_DESTINATIONS = frozenset(
    module
    for module in NEW_DECLARATION_DESTINATIONS
    if ".Internal." in module
    or module.endswith(".Internal")
    or module.endswith(".Pseudospectra.Resolvent.Internal.ScalarNotation")
)
INTERNAL_PRIVATE_ROUTES = {
    "_private.NumStability.Analysis.BergerInequality.0.NumStability.term\U0001D53C": (
        "NumStability.Analysis.LinearOperators.NumericalRadius.Berger.Internal.HermitianEuclideanSpaceNotation"
    ),
    "_private.NumStability.Analysis.NumericalRadius.0.NumStability.term\U0001D53C": (
        "NumStability.Analysis.LinearOperators.NumericalRadius.Core.Internal.EuclideanSpaceNotation"
    ),
    "_private.NumStability.Analysis.PseudospectralResolvent.0.NumStability.\u00abterm\u2191\u2090\u00bb": (
        "NumStability.Analysis.LinearOperators.Pseudospectra.Resolvent.Internal.ScalarNotation"
    ),
}
MACRO_ILEAN_ROOTS = {
    "_private.NumStability.Analysis.BergerGeneral.0.NumStability.term\U0001D53C": (
        "_private.NumStability.Analysis.BergerGeneral.0.NumStability."
        "_aux_NumStability_Analysis_BergerGeneral___macroRules__private_"
        "NumStability_Analysis_BergerGeneral_0_NumStability_term\U0001D53C_1"
    ),
    "_private.NumStability.Analysis.BergerInequality.0.NumStability.term\U0001D53C": (
        "_private.NumStability.Analysis.BergerInequality.0.NumStability."
        "_aux_NumStability_Analysis_BergerInequality___macroRules__private_"
        "NumStability_Analysis_BergerInequality_0_NumStability_term\U0001D53C_1"
    ),
    "_private.NumStability.Analysis.BergerResolvent.0.NumStability.term\U0001D53C": (
        "_private.NumStability.Analysis.BergerResolvent.0.NumStability."
        "_aux_NumStability_Analysis_BergerResolvent___macroRules__private_"
        "NumStability_Analysis_BergerResolvent_0_NumStability_term\U0001D53C_1"
    ),
    "_private.NumStability.Analysis.NumericalRadius.0.NumStability.term\U0001D53C": (
        "_private.NumStability.Analysis.NumericalRadius.0.NumStability."
        "_aux_NumStability_Analysis_NumericalRadius___macroRules__private_"
        "NumStability_Analysis_NumericalRadius_0_NumStability_term\U0001D53C_1"
    ),
    (
        "_private.NumStability.Analysis.PseudospectralResolvent.0.NumStability."
        "\u00abterm\u2191\u2090\u00bb"
    ): (
        "_private.NumStability.Analysis.PseudospectralResolvent.0.NumStability."
        "\u00ab_aux_NumStability_Analysis_PseudospectralResolvent___macroRules__private_"
        "NumStability_Analysis_PseudospectralResolvent_0_NumStability_term\u2191\u2090_1\u00bb"
    ),
}
MACRO_ILEAN_SPANS = {
    "_private.NumStability.Analysis.BergerGeneral.0.NumStability.term\U0001D53C": (
        109, 0, 109, 47, 109, 0, 109, 47
    ),
    "_private.NumStability.Analysis.BergerInequality.0.NumStability.term\U0001D53C": (
        87, 0, 87, 47, 87, 0, 87, 47
    ),
    "_private.NumStability.Analysis.BergerResolvent.0.NumStability.term\U0001D53C": (
        123, 0, 123, 47, 123, 0, 123, 47
    ),
    "_private.NumStability.Analysis.NumericalRadius.0.NumStability.term\U0001D53C": (
        71, 0, 73, 47, 71, 0, 73, 47
    ),
    (
        "_private.NumStability.Analysis.PseudospectralResolvent.0.NumStability."
        "\u00abterm\u2191\u2090\u00bb"
    ): (68, 0, 68, 38, 68, 0, 68, 38),
}
PRIVATE_ONLY_INTERNAL_ROUTES = {
    "NumStability.Analysis.BergerInequality": frozenset(
        {
            "NumStability.Analysis.LinearOperators.NumericalRadius.Berger.Internal."
            "HermitianEuclideanSpaceNotation"
        }
    ),
    "NumStability.Analysis.NumericalRadius": frozenset(
        {
            "NumStability.Analysis.LinearOperators.NumericalRadius.Core.Internal."
            "EuclideanSpaceNotation"
        }
    ),
    "NumStability.Analysis.PseudospectralResolvent": frozenset(
        {
            "NumStability.Analysis.LinearOperators.Pseudospectra.Resolvent.Internal."
            "ScalarNotation"
        }
    ),
}
AUTHORIZED_NONPRODUCTION_PREFIXES = (
    "NumStabilityTest/Reorganization/R07/",
    "docs/architecture/deliveries/R07/",
)

KREISS_ANALYTIC_DESTINATION = (
    "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.ResolventCoefficients.Analytic"
)
KREISS_ARC_DESTINATION = (
    "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.ArcLengthPowerBounds.FiniteDimension"
)
EXACT_NORMAL_DESTINATION = (
    "NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.NormalMatrices.Powers"
)
NORMAL_TRIANGULAR_DESTINATION = (
    "NumStability.Analysis.LinearOperators.Schur.Complex.NormalTriangular.Diagonal"
)
HENRICI_NORMAL_DESTINATION = (
    "NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.NormalCharacterization.Schur"
)
EXACT_DECLARATION_ROUTE_GROUPS = {
    KREISS_ANALYTIC_DESTINATION: frozenset(
        f"NumStability.{name}"
        for name in {
            "cstarMatrixEuclideanCoefficientLinear",
            "cstarMatrixEuclideanCoefficientCLM",
            "cstarMatrixEuclideanCoefficientCLM_apply",
            "spijkerResolventCoefficient",
            "spijkerResolventCoefficientCurve",
            "cstarMatrixEuclideanCoefficientCLM_circleIntegral",
            "spijkerResolventCoefficient_pow_eq_circleIntegral",
            "spijkerResolventCoefficient_pow_eq_intervalIntegral",
            "spijkerResolventCoefficientCurve_differentiableAt",
            "spijkerResolventCoefficientCurve_hasDerivAt",
            "spijkerResolventCoefficientCurve_deriv_continuous",
            "spijkerResolventCoefficientCurve_deriv_intervalIntegrable",
            "hasDerivAt_spijkerPowerAntiderivative",
        }
    ),
    KREISS_ARC_DESTINATION: frozenset(
        f"NumStability.{name}"
        for name in {
            "SpijkerArcLengthBound",
            "norm_spijkerMoment_le_arcLength",
            "norm_spijkerResolventCoefficient_le",
            "norm_cstarMatrixEuclideanCoefficient_pow_le_of_spijker",
            "norm_pow_le_of_spijker_circle",
            "norm_pow_le_exp_mul_dim_of_spijker",
            "powerBound_exp_mul_dim_of_spijker",
        }
    ),
    EXACT_NORMAL_DESTINATION: frozenset(
        {
            "NumStability.norm_pow_normal_eq",
            "_private.NumStability.Analysis.MatrixPowersSchur.0.NumStability.pi_norm_pow",
            "_private.NumStability.Analysis.MatrixPowersSchur.0.NumStability.l2_opNorm_one",
            "_private.NumStability.Analysis.MatrixPowersSchur.0.NumStability.l2_opNorm_of_mem_unitaryGroup",
            "_private.NumStability.Analysis.MatrixPowersSchur.0.NumStability.l2_opNorm_unitary_conj",
        }
    ),
    NORMAL_TRIANGULAR_DESTINATION: frozenset(
        {
            "NumStability.normal_upperTriangular_isDiag",
            "_private.NumStability.Analysis.MatrixPowersSchur.0.NumStability.conjTranspose_mul_diag",
            "_private.NumStability.Analysis.MatrixPowersSchur.0.NumStability.mul_conjTranspose_diag",
        }
    ),
    HENRICI_NORMAL_DESTINATION: frozenset(
        {
            "NumStability.normal_schur_strictUpper_eq_zero",
            "NumStability.normal_iff_strictUpper_eq_zero_unconditional",
            "NumStability.schurNormalImpliesStrictUpperZero_holds",
        }
    ),
}
EXACT_DAG_EDGES = {
    (KREISS_ARC_DESTINATION, KREISS_ANALYTIC_DESTINATION): (3, 12),
    (
        KREISS_ANALYTIC_DESTINATION,
        "NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.FiniteDimensional",
    ): (0, 1),
    (EXACT_NORMAL_DESTINATION, HENRICI_NORMAL_DESTINATION): (0, 1),
    (HENRICI_NORMAL_DESTINATION, NORMAL_TRIANGULAR_DESTINATION): (0, 2),
}
REAL_DESTINATION_PREFIX = "NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra."
REAL_ROUTE_SHORT_NAMES = {
    REAL_DESTINATION_PREFIX + "FiniteRealEmbedding": frozenset(
        {
            "finiteComplexCStarMatrix",
            "finiteComplexCStarMatrix_apply",
            "finiteComplexCStarMatrix_zero",
            "finiteComplexCStarMatrix_add",
            "finiteComplexCStarMatrix_smul",
            "finiteComplexCStarMatrix_mul",
            "finiteComplexCStarMatrix_isSelfAdjoint_of_symmetric",
            "finiteComplexCStarMatrix_sub",
            "finiteComplexCStarMatrix_neg",
            "finiteComplexCStarMatrix_finset_sum",
            "finiteComplexCStarMatrix_finiteIdMatrix",
            "finiteComplexCStarMatrix_smul_finiteIdMatrix",
        }
    ),
    REAL_DESTINATION_PREFIX + "FiniteDimensional": frozenset(
        {"cstarMatrix_complex_finiteDimensional"}
    ),
    REAL_DESTINATION_PREFIX + "FiniteRealOrder": frozenset(
        {
            "finiteComplexCStarMatrix_nonneg_of_finitePSD",
            "finiteComplexCStarMatrix_le_of_finiteLoewnerLe",
            "finiteComplexCStarMatrix_add_smul_one_le_of_finiteLoewnerLe",
        }
    ),
    REAL_DESTINATION_PREFIX + "FiniteMatrixOrder": frozenset(
        {"cstarMatrix_nonneg_of_matrix_posSemidef", "cstarMatrix_le_of_matrix_le"}
    ),
    REAL_DESTINATION_PREFIX + "StrictPositivity": frozenset(
        {
            "cstarMatrix_pos_real_smul_one_isStrictlyPositive",
            "finiteComplexCStarMatrix_add_pos_smul_one_isStrictlyPositive_of_finitePSD",
            "cstarMatrix_unitary_conj_isStrictlyPositive",
        }
    ),
    REAL_DESTINATION_PREFIX + "RectangularMultiplication": frozenset(
        {
            "cstarMatrix_mul_assoc_rect",
            "cstarMatrix_mul_add_rect",
            "cstarMatrix_add_mul_rect",
            "cstarMatrix_mul_smul_rect",
            "cstarMatrix_smul_mul_rect",
            "cstarMatrix_mul_one_rect",
            "cstarMatrix_one_mul_rect",
            "cstarMatrix_units_inv_mul_rect_eq_mul_units_inv_of_mul_eq",
        }
    ),
    REAL_DESTINATION_PREFIX + "RectangularCompression": frozenset(
        {
            "cstarMatrix_compression_add",
            "cstarMatrix_compression_sub",
            "cstarMatrix_compression_smul",
            "cstarMatrix_compression_real_smul",
            "cstarMatrixCompressionCLM",
            "cstarMatrixCompressionCLM_apply",
            "cstarMatrix_compression_one_of_conjTranspose_mul_self_eq_one",
        }
    ),
    REAL_DESTINATION_PREFIX + "BlockDiagonal": frozenset(
        {
            "cstarMatrixBlockDiagonal",
            "cstarMatrixBlockDiagonal_inl_inl",
            "cstarMatrixBlockDiagonal_inl_inr",
            "cstarMatrixBlockDiagonal_inr_inl",
            "cstarMatrixBlockDiagonal_inr_inr",
            "cstarMatrixBlockDiagonal_zero_zero",
            "cstarMatrixBlockDiagonal_one_one",
            "cstarMatrixBlockDiagonal_add",
            "cstarMatrixBlockDiagonal_neg",
            "cstarMatrixBlockDiagonal_sub",
            "cstarMatrixBlockDiagonal_star",
            "cstarMatrixBlockDiagonal_isSelfAdjoint",
            "cstarMatrixBlockDiagonal_mul",
            "cstarMatrixBlockDiagonal_isUnit",
            "cstarMatrixBlockDiagonal_left_nonneg",
            "cstarMatrixBlockDiagonal_right_nonneg",
            "cstarMatrixBlockDiagonal_nonneg",
            "cstarMatrixBlockDiagonal_isStrictlyPositive",
            "cstarMatrixBlockDiagonalStarAlgHom",
            "cstarMatrixBlockDiagonalStarAlgHom_apply",
            "cstarMatrixBlockDiagonalStarAlgHom_continuous",
        }
    ),
    REAL_DESTINATION_PREFIX + "ColumnPair": frozenset(
        {
            "cstarMatrixColumnPair",
            "cstarMatrixColumnPair_inl",
            "cstarMatrixColumnPair_inr",
            "cstarMatrixColumnPair_conjTranspose_mul_columnPair",
            "cstarMatrixColumnPair_conjTranspose_mul_self",
            "cstarMatrixColumnPair_conjTranspose_mul_self_eq_one_of_sum",
        }
    ),
    REAL_DESTINATION_PREFIX + "BlockDiagonalCompression": frozenset(
        {
            "cstarMatrixBlockDiagonal_mul_columnPair",
            "cstarMatrixColumnPair_conjTranspose_mul_blockDiagonal_mul_columnPair",
        }
    ),
    REAL_DESTINATION_PREFIX + "ColumnPairRangeProjection": frozenset(
        {
            "cstarMatrixColumnPairRangeProjection",
            "cstarMatrixColumnPairRangeProjection_isSelfAdjoint",
            "cstarMatrixColumnPairRangeProjection_mul_self_of_sum",
            "cstarMatrixColumnPairRangeProjection_mul_columnPair_of_sum",
            "cstarMatrixColumnPair_conjTranspose_mul_rangeProjection_of_sum",
        }
    ),
    REAL_DESTINATION_PREFIX + "ProjectionReflection": frozenset(
        {
            "cstarMatrixProjectionReflection",
            "cstarMatrixProjectionReflection_isSelfAdjoint_of_isSelfAdjoint",
            "cstarMatrixProjectionReflection_mul_self_of_idempotent",
            "cstarMatrixProjectionReflection_isUnit_of_idempotent",
            "cstarMatrixProjectionReflection_mem_unitary_of_isSelfAdjoint_of_idempotent",
            "cstarMatrixProjectionReflection_mul_of_mul_eq_self",
            "cstarMatrix_mul_projectionReflection_of_mul_eq_self",
        }
    ),
    REAL_DESTINATION_PREFIX + "ReflectionAverage": frozenset(
        {
            "cstarMatrix_reflectionAverage_compression_of_fixed",
            "cstarMatrix_reflectionAverage_conj_of_involutive",
            "cstarMatrix_reflectionAverage_commute_of_involutive",
            "cstarMatrix_commute_projection_of_commute_reflection",
        }
    ),
    REAL_DESTINATION_PREFIX + "ColumnPairRangeReflection": frozenset(
        {
            "cstarMatrixColumnPairRangeReflection",
            "cstarMatrixColumnPairRangeReflection_isSelfAdjoint",
            "cstarMatrixColumnPairRangeReflection_mul_self_of_sum",
            "cstarMatrixColumnPairRangeReflection_isUnit_of_sum",
            "cstarMatrixColumnPairRangeReflection_mem_unitary_of_sum",
            "cstarMatrixColumnPairRangeReflection_mul_columnPair_of_sum",
            "cstarMatrixColumnPair_conjTranspose_mul_rangeReflection_of_sum",
            "cstarMatrixColumnPairRangeReflection_conj_isStrictlyPositive_of_sum",
        }
    ),
    REAL_DESTINATION_PREFIX + "ColumnPairPinching": frozenset(
        {
            "cstarMatrixColumnPair_reflectionAverage_compression_of_sum",
            "cstarMatrixColumnPair_reflectionAverage_conj_rangeReflection_of_sum",
            "cstarMatrixColumnPair_reflectionAverage_commute_rangeReflection_of_sum",
            "cstarMatrixColumnPair_reflectionAverage_commute_rangeProjection_of_sum",
            "cstarMatrixColumnPair_mul_columnPair_eq_columnPair_compression_of_commute",
            "cstarMatrixColumnPair_conjTranspose_mul_eq_compression_mul_conjTranspose_of_commute",
            "cstarMatrixColumnPair_reflectionAverage_mul_columnPair_of_sum",
            "cstarMatrixColumnPair_conjTranspose_mul_reflectionAverage_of_sum",
        }
    ),
}
REAL_ROUTE_GROUPS = {
    destination: frozenset(f"NumStability.{name}" for name in names)
    for destination, names in REAL_ROUTE_SHORT_NAMES.items()
}
if sum(map(len, REAL_ROUTE_GROUPS.values())) != 97:
    raise RuntimeError("R07 RealMatrixBridge route constant must contain exactly 97 declarations")
R = REAL_DESTINATION_PREFIX
REAL_DAG_EDGES = {
    (R + "BlockDiagonalCompression", R + "BlockDiagonal"): (2, 10),
    (R + "BlockDiagonalCompression", R + "ColumnPair"): (2, 6),
    (R + "ColumnPairPinching", R + "ColumnPair"): (5, 5),
    (R + "ColumnPairPinching", R + "ColumnPairRangeProjection"): (3, 5),
    (R + "ColumnPairPinching", R + "ColumnPairRangeReflection"): (6, 10),
    (R + "ColumnPairPinching", R + "RectangularMultiplication"): (0, 2),
    (R + "ColumnPairPinching", R + "ReflectionAverage"): (0, 4),
    (R + "ColumnPairRangeProjection", R + "ColumnPair"): (2, 8),
    (R + "ColumnPairRangeProjection", R + "RectangularMultiplication"): (0, 6),
    (R + "ColumnPairRangeReflection", R + "ColumnPair"): (2, 2),
    (R + "ColumnPairRangeReflection", R + "ColumnPairRangeProjection"): (0, 14),
    (R + "ColumnPairRangeReflection", R + "ProjectionReflection"): (0, 7),
    (R + "ColumnPairRangeReflection", R + "StrictPositivity"): (0, 1),
    (R + "FiniteRealOrder", R + "FiniteRealEmbedding"): (3, 4),
    (R + "RectangularCompression", R + "FiniteDimensional"): (0, 1),
    (R + "RectangularCompression", R + "RectangularMultiplication"): (0, 7),
    (R + "ReflectionAverage", R + "ProjectionReflection"): (1, 1),
    (R + "ReflectionAverage", R + "RectangularMultiplication"): (0, 14),
    (R + "StrictPositivity", R + "FiniteRealEmbedding"): (1, 1),
    (R + "StrictPositivity", R + "FiniteRealOrder"): (0, 1),
}
WHOLE_OWNER_DESTINATIONS = {
    "NumStability.Analysis.BergerGeneral": (
        "NumStability.Analysis.LinearOperators.NumericalRadius.Berger.GeneralPowerInequality.Powers"
    ),
    "NumStability.Analysis.BergerResolvent": (
        "NumStability.Analysis.LinearOperators.NumericalRadius.Berger.GeneralPowerInequality.PowersOfTwo"
    ),
    "NumStability.Analysis.MatrixPowersBinomialBound": (
        "NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.SchurBinomialBounds.Estimates"
    ),
    "NumStability.Analysis.MatrixPowersSpijkerPlanar": (
        "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarCrossingBounds.Polynomial"
    ),
    "NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis": (
        "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarArcLength.Variation"
    ),
}
FINITE_KREISS_DESTINATION = (
    "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.FiniteDimensionalPowerBounds.Kreiss"
)
HIGHAM_KREISS_DESTINATION = (
    "NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds."
    "SpijkerKreissUnconditional.Bounds"
)
MODULE_NAME = re.compile(r"^[A-Z][A-Za-z0-9_']*(?:\.[A-Z][A-Za-z0-9_']*)*$")
RFC3339_UTC = re.compile(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$")


class GenerationError(RuntimeError):
    """The prospective controls cannot be derived honestly from their inputs."""


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


@dataclass(frozen=True)
class Projection:
    payload: bytes
    compressed: bytes
    counts: dict[str, int]


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def git(*args: str, check: bool = True) -> subprocess.CompletedProcess[bytes]:
    result = subprocess.run(
        ["git", *args],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if check and result.returncode:
        raise GenerationError(
            f"git {' '.join(args)} failed: "
            + result.stderr.decode("utf-8", errors="replace").strip()
        )
    return result


def git_text(*args: str) -> str:
    return git(*args).stdout.decode("utf-8")


def git_blob_oid(revision: str, path: str) -> str:
    row = git_text("ls-tree", revision, "--", path).strip()
    if not row:
        raise GenerationError(f"{revision}: missing blob {path}")
    metadata, returned = row.split("\t", 1)
    _mode, kind, oid = metadata.split()
    if kind != "blob" or returned != path:
        raise GenerationError(f"{revision}: unexpected tree row for {path}: {row}")
    return oid


def git_file(revision: str, path: str) -> bytes:
    return git("show", f"{revision}:{path}").stdout


def module_path(module: str) -> str:
    return module.replace(".", "/") + ".lean"


def module_from_path(path: str) -> str:
    if not path.endswith(".lean"):
        raise GenerationError(f"not a Lean module path: {path}")
    return path[:-5].replace("/", ".")


def canonical_json(value: Any) -> bytes:
    return (json.dumps(value, indent=1, sort_keys=True, ensure_ascii=False) + "\n").encode()


def pretty_json(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode()


def tsv_bytes(header: Sequence[str], rows: Iterable[Sequence[Any]]) -> bytes:
    stream = io.StringIO(newline="")
    writer = csv.writer(stream, delimiter="\t", lineterminator="\n")
    writer.writerow(header)
    writer.writerows(rows)
    return stream.getvalue().encode("utf-8")


def line_list_bytes(rows: Iterable[str]) -> bytes:
    values = list(rows)
    return (("\n".join(values) + "\n") if values else "").encode("utf-8")


def artifact_for_payload(path: Path, payload: bytes) -> dict[str, str]:
    return {"path": repo_relative(path), "sha256": sha256_bytes(payload)}


def write_materialized_payloads(payloads: dict[Path, bytes]) -> list[dict[str, Any]]:
    if set(payloads) != planned_materialized_paths():
        raise GenerationError(
            "planned materializer path set differs from the exact fail-closed output contract"
        )
    # Preflight the entire write set before changing a byte.  This makes a
    # divergent late-sorting target a clean failure rather than a partial state.
    for path, payload in sorted(payloads.items(), key=lambda item: repo_relative(item[0])):
        if path == PHASE / "phase.json":
            expected_base = git_file(ACCEPTED_CONTROL_SHA, repo_relative(path))
            if path.read_bytes() not in {expected_base, payload}:
                raise GenerationError("refusing to overwrite divergent phase.json")
        elif path.exists() and path.read_bytes() != payload:
            raise GenerationError(f"refusing to overwrite divergent planned control: {path}")

    reports: list[dict[str, Any]] = []
    for path, payload in sorted(payloads.items(), key=lambda item: repo_relative(item[0])):
        path.parent.mkdir(parents=True, exist_ok=True)
        if not path.exists() or path.read_bytes() != payload:
            path.write_bytes(payload)
        reports.append(
            {
                "bytes": len(payload),
                "path": repo_relative(path),
                "sha256": sha256_bytes(payload),
            }
        )
    return reports


def deterministic_gzip(payload: bytes) -> bytes:
    stream = io.BytesIO()
    with gzip.GzipFile(
        filename="", mode="wb", fileobj=stream, compresslevel=9, mtime=0
    ) as handle:
        handle.write(payload)
    return stream.getvalue()


def read_tsv(path: Path, expected_header: Sequence[str]) -> list[dict[str, str]]:
    with path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        if tuple(reader.fieldnames or ()) != tuple(expected_header):
            raise GenerationError(
                f"{path}: header {reader.fieldnames!r} != {tuple(expected_header)!r}"
            )
        rows = list(reader)
    return rows


def verify_digest(path: Path, expected: str) -> None:
    if not path.is_file():
        raise GenerationError(f"missing input: {path}")
    actual = sha256_path(path)
    if actual != expected:
        raise GenerationError(f"{path}: expected SHA-256 {expected}, found {actual}")


def require_exact_keys(value: dict[str, Any], expected: Iterable[str], label: str) -> None:
    actual = set(value)
    required = set(expected)
    if actual != required:
        raise GenerationError(
            f"{label}: keys differ; missing={sorted(required - actual)}, "
            f"extra={sorted(actual - required)}"
        )


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise GenerationError(f"{path}: expected a JSON object")
    return value


def repo_relative(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT.resolve()).as_posix()
    except ValueError as error:
        raise GenerationError(f"reviewed input must be inside the repository: {path}") from error


def validate_ci_attestation_payload(attestation: dict[str, Any]) -> None:
    accepted = attestation.get("accepted_control", {})
    run = attestation.get("run", {})
    job = attestation.get("job", {})
    workflow = attestation.get("workflow", {})
    suite = attestation.get("check_suite", {})
    check_run = attestation.get("check_run", {})
    scope = attestation.get("evidence_scope", {})
    repository = attestation.get("repository", {})
    cardinality = attestation.get("cardinality")
    source_api = attestation.get("source_api", {})
    steps = job.get("steps")
    step_contract = (
        tuple((step.get("number"), step.get("name")) for step in steps)
        if isinstance(steps, list)
        else ()
    )
    repository_name = "AlexGeorgantzas/lean-numerical-stability"
    api_root = f"https://api.github.com/repos/{repository_name}"
    run_url = f"{api_root}/actions/runs/32394769969"
    job_url = f"{api_root}/actions/jobs/96508922114"
    run_html = (
        "https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/"
        "32394769969"
    )
    job_html = f"{run_html}/job/96508922114"
    if (
        attestation.get("schema_version") != 1
        or attestation.get("record_kind") != "checkpoint_external_ci_attestation"
        or attestation.get("attestation_id") != "C0005-acceptance-control-ci"
        or repository.get("full_name") != repository_name
        or accepted.get("checkpoint_id") != BASE_CHECKPOINT_ID
        or accepted.get("commit_sha") != ACCEPTED_CONTROL_SHA
        or accepted.get("commit_tree_sha") != ACCEPTED_CONTROL_TREE
        or accepted.get("parent_code_sha") != BASE_CODE_SHA
        or cardinality != EXPECTED_CI_CARDINALITY
        or run.get("id") != 32394769969
        or run.get("head_sha") != ACCEPTED_CONTROL_SHA
        or run.get("name") != "Lean CI"
        or run.get("workflow_id") != 240911818
        or run.get("check_suite_id") != 87818531615
        or run.get("run_number") != 8929
        or run.get("run_attempt") != 1
        or run.get("event") != "push"
        or run.get("head_branch") != "main"
        or run.get("status") != "completed"
        or run.get("conclusion") != "success"
        or run.get("url") != run_url
        or run.get("html_url") != run_html
        or run.get("jobs_url") != f"{run_url}/jobs"
        or job.get("id") != 96508922114
        or job.get("run_id") != run.get("id")
        or job.get("head_sha") != run.get("head_sha")
        or job.get("head_branch") != "main"
        or job.get("name") != "build"
        or job.get("workflow_name") != "Lean CI"
        or job.get("run_attempt") != 1
        or job.get("status") != "completed"
        or job.get("conclusion") != "success"
        or job.get("url") != job_url
        or job.get("run_url") != run_url
        or job.get("html_url") != job_html
        or job.get("check_run_url") != f"{api_root}/check-runs/96508922114"
        or not isinstance(steps, list)
        or len(steps) != len(EXPECTED_CI_STEPS)
        or step_contract != EXPECTED_CI_STEPS
        or len({step.get("number") for step in steps}) != len(EXPECTED_CI_STEPS)
        or any(
            step.get("status") != "completed" or step.get("conclusion") != "success"
            for step in steps
        )
        or workflow.get("id") != run.get("workflow_id")
        or workflow.get("name") != run.get("name")
        or workflow.get("path") != ".github/workflows/lean_action_ci.yml"
        or workflow.get("file_sha256") != PINNED_CONFIG_INPUTS[
            ROOT / ".github/workflows/lean_action_ci.yml"
        ]
        or suite.get("id") != run.get("check_suite_id")
        or suite.get("head_sha") != ACCEPTED_CONTROL_SHA
        or suite.get("head_branch") != "main"
        or suite.get("status") != "completed"
        or suite.get("conclusion") != "success"
        or suite.get("latest_check_runs_count") != 1
        or suite.get("before_sha") != BASE_CODE_SHA
        or suite.get("after_sha") != ACCEPTED_CONTROL_SHA
        or check_run.get("id") != job.get("id")
        or check_run.get("check_suite_id") != suite.get("id")
        or check_run.get("head_sha") != ACCEPTED_CONTROL_SHA
        or check_run.get("name") != job.get("name")
        or check_run.get("status") != "completed"
        or check_run.get("conclusion") != "success"
        or check_run.get("details_url") != job_html
        or source_api.get("run_endpoint") != run_url
        or source_api.get("job_endpoint") != job_url
        or source_api.get("jobs_endpoint") != f"{run_url}/jobs?filter=all&per_page=100"
        or source_api.get("check_suite_endpoint")
        != f"{api_root}/check-suites/87818531615"
        or source_api.get("check_run_endpoint") != f"{api_root}/check-runs/96508922114"
        or scope.get("use") != "R07 activation prerequisite only"
        or scope.get("does_not_authorize_or_record")
        != [
            "B0008 branch retirement",
            "B0009 branch retirement",
            "remote ref deletion",
            "worker worktree removal",
            "R07 self-acceptance",
        ]
    ):
        raise GenerationError("C0005 external CI attestation semantic contract drift")


def validate_ci_attestation(*, live: bool) -> dict[str, Any]:
    verify_digest(CI_ATTESTATION, CI_ATTESTATION_SHA256)
    attestation = load_json(CI_ATTESTATION)
    if CI_ATTESTATION.read_bytes() != canonical_json(attestation):
        raise GenerationError("C0005 CI attestation must use canonical sorted indent-1 LF JSON")
    validate_ci_attestation_payload(attestation)
    run = attestation["run"]
    job = attestation["job"]
    compact = {
        "workflow": run["name"],
        "run_id": str(run["id"]),
        "job_id": str(job["id"]),
        "head_sha": run["head_sha"],
        "conclusion": job["conclusion"],
    }
    if compact != ACCEPTED_CI_EVIDENCE or sha256_bytes(canonical_json(compact)) != (
        "1A49AC4697EA9FB2C473F04CB8B59175D5BC0A12540F5877BA7F6EDE868B6DA9"
    ):
        raise GenerationError("C0005 CI compact semantic digest drift")
    if live:
        repository = "AlexGeorgantzas/lean-numerical-stability"
        endpoints = {
            "run": f"repos/{repository}/actions/runs/{run['id']}",
            "job": f"repos/{repository}/actions/jobs/{job['id']}",
            "suite": f"repos/{repository}/check-suites/{attestation['check_suite']['id']}",
            "check_run": f"repos/{repository}/check-runs/{attestation['check_run']['id']}",
            "jobs": f"repos/{repository}/actions/runs/{run['id']}/jobs?filter=all&per_page=100",
            "artifacts": f"repos/{repository}/actions/runs/{run['id']}/artifacts",
        }
        live_payloads: dict[str, dict[str, Any]] = {}
        for label, endpoint in endpoints.items():
            result = subprocess.run(
                ["gh", "api", endpoint],
                cwd=ROOT,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
            )
            if result.returncode:
                raise GenerationError(
                    f"live GitHub {label} verification failed: "
                    + result.stderr.decode("utf-8", errors="replace").strip()
                )
            value = json.loads(result.stdout)
            if not isinstance(value, dict):
                raise GenerationError(f"live GitHub {label} response is not an object")
            live_payloads[label] = value
        for label, frozen, keys in (
            (
                "run",
                run,
                (
                    "id",
                    "workflow_id",
                    "check_suite_id",
                    "head_sha",
                    "head_branch",
                    "event",
                    "run_attempt",
                    "run_number",
                    "status",
                    "conclusion",
                    "name",
                ),
            ),
            (
                "job",
                job,
                (
                    "id",
                    "run_id",
                    "head_sha",
                    "head_branch",
                    "run_attempt",
                    "status",
                    "conclusion",
                    "name",
                    "workflow_name",
                ),
            ),
            (
                "suite",
                attestation["check_suite"],
                (
                    "id",
                    "head_sha",
                    "head_branch",
                    "latest_check_runs_count",
                    "status",
                    "conclusion",
                ),
            ),
            (
                "check_run",
                attestation["check_run"],
                ("id", "head_sha", "status", "conclusion", "name", "details_url"),
            ),
        ):
            current = live_payloads[label]
            for key in keys:
                if current.get(key) != frozen.get(key):
                    raise GenerationError(f"live GitHub {label}.{key} differs from attestation")
        current_job = live_payloads["job"]
        if current_job.get("steps") != job.get("steps"):
            raise GenerationError("live GitHub job steps differ from the hash-pinned attestation")
        current_check_suite = live_payloads["check_run"].get("check_suite", {})
        if current_check_suite.get("id") != attestation["check_suite"]["id"]:
            raise GenerationError("live GitHub check-run/check-suite linkage differs")
        jobs = live_payloads["jobs"]
        artifacts = live_payloads["artifacts"]
        live_cardinality = {
            "artifact_count": artifacts.get("total_count"),
            "job_count": jobs.get("total_count"),
            "job_ids": [entry.get("id") for entry in jobs.get("jobs", [])],
            "pull_request_count": len(live_payloads["run"].get("pull_requests", [])),
            "referenced_workflow_count": len(
                live_payloads["run"].get("referenced_workflows", [])
            ),
        }
        if live_cardinality != EXPECTED_CI_CARDINALITY:
            raise GenerationError(
                f"live GitHub CI cardinality differs from attestation: {live_cardinality}"
            )
    return attestation


def reject_historical_input(path: Path) -> None:
    normalized = path.resolve().as_posix().casefold()
    forbidden = (
        "/2026-08-repository-reorganization/",
        "/reorg-w06-",
        "/w06/",
        "p0007",
    )
    if any(fragment in normalized for fragment in forbidden):
        raise GenerationError(
            f"historical W06/P0007 evidence is review context, not R07 activation input: {path}"
        )


def planned_materialized_paths() -> set[Path]:
    branch_suffixes = {
        "R0011-import-manifest.tsv",
        "branch-prefixes.txt",
        "consumers.tsv",
        "declaration-routes.tsv",
        "destination-dag.tsv",
        "destination-modules.txt",
        "destination-prefixes.txt",
        "destinations.tsv",
        "external-owner-supply.tsv",
        "inventory.tsv",
        "module-routes.tsv",
        "overlap-review.json",
        "post-move-import-manifest.tsv",
        "private-closure.tsv",
        "private-normalization.tsv",
        "scope-rules.tsv",
        "shared-request-paths.txt",
        "source-commands.tsv",
        "test-modules.txt",
        "test-plan.tsv",
        "tier-assignments.tsv",
        "wrapper-imports.tsv",
    }
    return {
        *(BRANCHES / f"{BRANCH_ID}-{suffix}" for suffix in branch_suffixes),
        BRANCHES / f"{BRANCH_ID}.json",
        SELECTORS / f"{WAVE_ID}.tsv",
        PROJECTIONS / f"{PROJECTION_ID}.json",
        PROJECTIONS / f"{PROJECTION_ID}.tsv.gz",
        REQUESTS / f"{REQUEST_ID}.json",
        REQUESTS / f"{REQUEST_ID}.patch",
        REQUESTS / f"{REQUEST_ID}-postimages.tsv",
        REQUESTS / f"{REQUEST_ID}-request-plan.tsv",
        REQUESTS / f"{REQUEST_ID}-import-manifest.tsv",
        PHASE / "phase.json",
        PLANNED_CONTROL_CONTRACT,
    }


def verify_base(
    graph: Path,
    reviewed_inputs: Sequence[Path] = (),
    *,
    allow_materialized: bool = False,
) -> None:
    for path, digest in (
        (CHECKPOINT, CHECKPOINT_SHA256),
        (BASELINE, BASELINE_SHA256),
        (BASELINE_SUMMARY, BASELINE_SUMMARY_SHA256),
        (INVENTORY, INVENTORY_SHA256),
        (PROJECTION_CHECKER, PROJECTION_CHECKER_SHA256),
        (SHARED_POSTIMAGE_RENDERER, SHARED_POSTIMAGE_RENDERER_SHA256),
        (graph, GRAPH_SHA256),
    ):
        verify_digest(path, digest)
    for path, digest in PINNED_CONFIG_INPUTS.items():
        if allow_materialized and path == PHASE / "phase.json":
            import r07_shared_postimages as shared_postimages

            accepted_phase = git_file(ACCEPTED_CONTROL_SHA, repo_relative(path))
            planned_phase = pretty_json(
                planned_phase_postimage(set(shared_postimages.ALL_PATHS))
            )
            if not path.is_file() or path.read_bytes() not in {
                accepted_phase,
                planned_phase,
            }:
                raise GenerationError(
                    "phase.json must equal exact accepted C0005 or the exact R07 "
                    "planned-state postimage"
                )
            continue
        verify_digest(path, digest)
    for path, digest in TERMINAL_CONTROL_INPUTS.items():
        verify_digest(path, digest)
    validate_ci_attestation(live=False)
    reject_historical_input(graph)

    head = git_text("rev-parse", "HEAD").strip()
    origin_main = git_text("rev-parse", "refs/remotes/origin/main").strip()
    if head != ACCEPTED_CONTROL_SHA or origin_main != ACCEPTED_CONTROL_SHA:
        raise GenerationError(
            "planning must run at exact accepted C0005 with HEAD and origin/main both "
            f"{ACCEPTED_CONTROL_SHA}; found HEAD={head}, origin/main={origin_main}"
        )
    generator_relative = Path(__file__).resolve().relative_to(ROOT).as_posix()
    status = git_text("status", "--porcelain=v1", "--untracked-files=all").splitlines()
    allowed_paths = {
        generator_relative,
        repo_relative(CI_ATTESTATION),
        repo_relative(SHARED_POSTIMAGE_RENDERER),
    }
    for reviewed_input in reviewed_inputs:
        allowed_paths.add(repo_relative(reviewed_input))
    if allow_materialized:
        allowed_paths.update(repo_relative(path) for path in planned_materialized_paths())
    unexpected_status: list[str] = []
    for row in status:
        if len(row) < 4:
            unexpected_status.append(row)
            continue
        state, path = row[:2], row[3:]
        if state not in {"??", " M"} or path not in allowed_paths:
            unexpected_status.append(row)
    if unexpected_status:
        raise GenerationError(
            "planning worktree must be clean except for this generator and the exact supplied "
            "untracked, hash-pinned review inputs; "
            f"unexpected={unexpected_status}; found={status}"
        )

    target_ref = f"refs/heads/{BRANCH_NAME}"
    for ref in (target_ref, f"refs/remotes/origin/{BRANCH_NAME}"):
        if git("show-ref", "--verify", "--quiet", ref, check=False).returncode == 0:
            raise GenerationError(f"R07 activation ref already exists: {ref}")
    remote = git(
        "ls-remote", "--heads", "origin", "refs/heads/main", target_ref, check=False
    )
    if remote.returncode:
        raise GenerationError(
            "cannot prove R07 branch vacancy on origin: "
            + remote.stderr.decode("utf-8", errors="replace").strip()
        )
    remote_refs = {
        fields[1]: fields[0]
        for line in remote.stdout.decode("utf-8").splitlines()
        if len(fields := line.split("\t")) == 2
    }
    if remote_refs.get("refs/heads/main") != ACCEPTED_CONTROL_SHA:
        raise GenerationError(
            "live origin refs/heads/main is not exact accepted C0005: "
            f"{remote_refs.get('refs/heads/main')}"
        )
    if target_ref in remote_refs:
        raise GenerationError(f"R07 activation branch already exists on origin: {target_ref}")
    worktrees = git_text("worktree", "list", "--porcelain").casefold()
    if target_ref.casefold() in worktrees:
        raise GenerationError(f"R07 activation branch already has a worktree: {target_ref}")
    worktree_paths = [
        Path(line.removeprefix("worktree ")).name.casefold()
        for line in git_text("worktree", "list", "--porcelain").splitlines()
        if line.startswith("worktree ")
    ]
    if PLANNED_WORKTREE_BASENAME.casefold() in worktree_paths:
        raise GenerationError(
            f"R07 worker worktree already exists: {PLANNED_WORKTREE_BASENAME}"
        )

    forbidden_files = (
        PHASE / f"branches/{BRANCH_ID}.json",
        PHASE / f"projections/{PROJECTION_ID}.json",
        PHASE / f"projections/{PROJECTION_ID}.tsv.gz",
        PHASE / f"requests/{REQUEST_ID}.json",
        PHASE / f"requests/{REQUEST_ID}.patch",
        PHASE / f"selectors/{WAVE_ID}.tsv",
        ROOT / f"docs/architecture/deliveries/{WAVE_ID}",
        ROOT / f"NumStabilityTest/Reorganization/{WAVE_ID}",
    )
    materialized = planned_materialized_paths() if allow_materialized else set()
    existing = [
        str(path) for path in forbidden_files if path.exists() and path not in materialized
    ]
    if existing:
        raise GenerationError("pre-existing R07 activation artifacts: " + ", ".join(existing))

    if git("merge-base", "--is-ancestor", ACCEPTED_CONTROL_SHA, "HEAD", check=False).returncode:
        raise GenerationError(
            f"accepted C0005 control {ACCEPTED_CONTROL_SHA} must be an ancestor of HEAD"
        )
    for revision, expected_tree in (
        (BASE_CODE_SHA, BASE_CODE_TREE),
        (ACCEPTED_CONTROL_SHA, ACCEPTED_CONTROL_TREE),
    ):
        actual = git_text("rev-parse", f"{revision}^{{tree}}").strip()
        if actual != expected_tree:
            raise GenerationError(
                f"{revision}: expected tree {expected_tree}, found {actual}"
            )
    production_scope = (
        "NumStability",
        "NumStability.lean",
        "NumStabilityTest",
        "NumStabilityTest.lean",
        "benchmark-results",
    )
    accepted_drift = git_text(
        "diff", "--name-only", BASE_CODE_SHA, ACCEPTED_CONTROL_SHA, "--", *production_scope
    ).strip()
    if accepted_drift:
        raise GenerationError(
            "C0005 acceptance control changed the exact worker code/test tree:\n"
            + accepted_drift
        )
    head_drift = git_text(
        "diff", "--name-only", ACCEPTED_CONTROL_SHA, "HEAD", "--", *production_scope
    ).strip()
    if head_drift:
        raise GenerationError(
            "planning history changed production/test/benchmark inputs:\n" + head_drift
        )

    checkpoint = load_json(CHECKPOINT)
    if not (
        checkpoint.get("checkpoint_id") == BASE_CHECKPOINT_ID
        and checkpoint.get("commit_sha") == BASE_CODE_SHA
        and checkpoint.get("accepted_by") == OWNER_ID
    ):
        raise GenerationError("C0005 checkpoint identity/authority drift")
    metrics = checkpoint.get("metrics", {})
    if (
        metrics.get("production_modules") != EXPECTED_PRODUCTION_MODULES
        or metrics.get("unclassified_modules") != sum(EXPECTED_UNCLASSIFIED_QUEUE.values())
        or metrics.get("mixed_modules") != 0
    ):
        raise GenerationError("C0005 checkpoint metrics are not 2818/2685/133/0")
    expected_gate_ids = {
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
    gates = checkpoint.get("gates", [])
    if not isinstance(gates, list) or {gate.get("gate_id") for gate in gates} != expected_gate_ids:
        raise GenerationError("C0005 must contain every and only the 12 accepted gate IDs")
    gate_evidence = {
        "path": str((PHASE / "checkpoints/C0005-gates.md").relative_to(ROOT)).replace("\\", "/"),
        "sha256": "EA0192C5965E1D36B59417D35074E70A075619BBF72ADA24E985C2A632B19C47",
    }
    for gate in gates:
        if (
            gate.get("status") != "PASS"
            or gate.get("commit_sha") != BASE_CODE_SHA
            or gate.get("executor_id") not in {OWNER_ID, "github-actions"}
            or gate.get("evidence") != gate_evidence
        ):
            raise GenerationError(f"C0005 gate is not exact accepted evidence: {gate.get('gate_id')}")

    baseline = load_json(BASELINE)
    metadata = baseline.get("metadata", {})
    if metadata.get("commit") != BASE_CODE_SHA or not metadata.get("library_source_clean"):
        raise GenerationError("C0005 baseline is not a clean exact-code snapshot")
    if baseline.get("source", {}).get("module_count") != EXPECTED_PRODUCTION_MODULES:
        raise GenerationError("C0005 production-module count drift")

    phase = load_json(PHASE / "phase.json")
    milestones = {
        row.get("milestone_id"): row for row in phase.get("milestones", [])
    }
    lanes = {row.get("lane_id"): row for row in phase.get("authority", {}).get("lanes", [])}
    if phase.get("current_checkpoint_id") != BASE_CHECKPOINT_ID:
        raise GenerationError("planning requires current checkpoint C0005")
    if milestones.get(MILESTONE_ID, {}).get("status") != "ready":
        raise GenerationError("M07 must be ready, not planned/active/accepted")
    for milestone in ("M04", "M08"):
        row = milestones.get(milestone, {})
        if row.get("status") != "accepted" or row.get("accepted_checkpoint_id") != BASE_CHECKPOINT_ID:
            raise GenerationError(f"{milestone} must be accepted exactly at C0005")
    if lanes.get(LANE_ID, {}).get("operator_ids") != [OPERATOR_ID]:
        raise GenerationError("codex-lane authority must remain codex-local only")
    for branch_id in ("B0008", "B0009"):
        branch = load_json(PHASE / f"branches/{branch_id}.json")
        retirement = branch.get("retirement", {})
        integration = branch.get("integration", {})
        if (
            branch.get("status") != "accepted"
            or integration
            != {
                "accepted_checkpoint_id": BASE_CHECKPOINT_ID,
                "accepted_sha": BASE_CODE_SHA,
                "method": "merge",
            }
            or retirement.get("status") != "due"
            or retirement.get("retired_at") is not None
            or retirement.get("retired_by") is not None
        ):
            raise GenerationError(f"{branch_id}: C0005 acceptance/retirement-separation drift")
    for projection_id in ("P0008", "P0009"):
        projection = load_json(PHASE / f"projections/{projection_id}.json")
        if projection.get("status") != "retired" or projection.get("superseded_by") is not None:
            raise GenerationError(f"{projection_id}: terminal projection lifecycle drift")
    for request_id in ("R0009", "R0010"):
        request = load_json(PHASE / f"requests/{request_id}.json")
        resolution = request.get("resolution", {})
        if (
            request.get("status") != "applied"
            or resolution.get("checkpoint_id") != BASE_CHECKPOINT_ID
            or resolution.get("commit_sha") != BASE_CODE_SHA
            or resolution.get("resolved_by") != OWNER_ID
            or resolution.get("validation_evidence") != [gate_evidence]
        ):
            raise GenerationError(f"{request_id}: terminal applied lifecycle drift")

    ci_digest = sha256_bytes(canonical_json(ACCEPTED_CI_EVIDENCE))
    if ci_digest != "1A49AC4697EA9FB2C473F04CB8B59175D5BC0A12540F5877BA7F6EDE868B6DA9":
        raise GenerationError("accepted C0005 CI attestation hash drift")


def inventory_rows() -> list[dict[str, str]]:
    rows = read_tsv(INVENTORY, INVENTORY_HEADER)
    if len(rows) != EXPECTED_PRODUCTION_MODULES:
        raise GenerationError(
            f"expected {EXPECTED_PRODUCTION_MODULES} inventory rows, found {len(rows)}"
        )
    modules = [row["module"] for row in rows]
    paths = [row["path"] for row in rows]
    if len(set(modules)) != len(modules) or len(set(paths)) != len(paths):
        raise GenerationError("C0005 inventory module/path identities are not unique")
    unclassified = Counter(
        row["wave_id"] for row in rows if row["current_tier"] == "unclassified"
    )
    if dict(unclassified) != EXPECTED_UNCLASSIFIED_QUEUE:
        raise GenerationError(
            f"terminal queue must be exactly R07=43, R09=72, R10=18; found {dict(unclassified)}"
        )
    r07_actions = Counter(row["planned_actions"] for row in rows if row["wave_id"] == WAVE_ID)
    if dict(r07_actions) != EXPECTED_R07_ACTION_COUNTS:
        raise GenerationError(f"R07 frozen action distribution drift: {dict(r07_actions)}")
    if sum(unclassified.values()) != 133 or len(rows) - sum(unclassified.values()) != 2685:
        raise GenerationError("C0005 inventory does not reproduce 2818/2685/133")
    return rows


def build_selector(rows: list[dict[str, str]]) -> list[dict[str, str]]:
    selected = sorted(
        (row for row in rows if row["wave_id"] == WAVE_ID),
        key=lambda row: row["module"],
    )
    if len(selected) != EXPECTED_OWNER_COUNT:
        raise GenerationError(
            f"R07 expected {EXPECTED_OWNER_COUNT} historical owners, found {len(selected)}"
        )
    if any(
        row["phase_scope"] != "in_scope" or row["lane_id"] != LANE_ID
        for row in selected
    ):
        raise GenerationError("R07 selector scope/lane drift")
    unclassified = {row["module"] for row in selected if row["current_tier"] == "unclassified"}
    naming_only = {row["module"] for row in selected if row["current_tier"] != "unclassified"}
    if len(unclassified) != EXPECTED_UNCLASSIFIED_OWNERS or naming_only != NAMING_ONLY_OWNERS:
        raise GenerationError(
            "R07 must contain exactly 43 unclassified plus the two assigned naming-only owners"
        )
    for row in selected:
        actual_oid = git_blob_oid(BASE_CODE_SHA, row["path"])
        if actual_oid != row["base_blob_oid"]:
            raise GenerationError(
                f"{row['module']}: inventory blob {row['base_blob_oid']} != {actual_oid}"
            )
    return selected


def parse_graph(graph: Path) -> tuple[list[Declaration], list[Edge]]:
    declarations: list[Declaration] = []
    edges: list[Edge] = []
    with graph.open("r", encoding="utf-8", newline="") as handle:
        if handle.readline() != "format\t2\n":
            raise GenerationError("C0005 dependency graph is not exact LF format 2")
        for number, line in enumerate(handle, 2):
            if not line.endswith("\n"):
                raise GenerationError(f"graph row {number} lacks LF termination")
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
    if len({declaration.name for declaration in declarations}) != len(declarations):
        raise GenerationError("format-2 declaration identities are not unique")
    return declarations, edges


def build_projection(
    selector: list[dict[str, str]],
    declarations: list[Declaration],
    edges: list[Edge],
) -> Projection:
    owners = {row["module"] for row in selector}
    selected = sorted(
        (declaration for declaration in declarations if declaration.owner in owners),
        key=lambda declaration: declaration.name,
    )
    names = {declaration.name for declaration in selected}
    if not set(INTERNAL_PRIVATE_ROUTES) <= names:
        raise GenerationError(
            "format-2 graph lacks exact UTF-8 internal private seeds: "
            + ", ".join(sorted(set(INTERNAL_PRIVATE_ROUTES) - names))
        )
    if any(name.encode("utf-8").decode("utf-8") != name for name in INTERNAL_PRIVATE_ROUTES):
        raise GenerationError("internal private seed UTF-8 round-trip failed")
    incident = sorted(
        (edge for edge in edges if edge.source in names or edge.target in names),
        key=lambda edge: (edge.source, 0 if edge.kind == "signature" else 1, edge.target),
    )
    counts = {
        "body_edges": sum(edge.kind == "body" for edge in incident),
        "declarations": len(selected),
        "signature_edges": sum(edge.kind == "signature" for edge in incident),
        "union_edges": len({(edge.source, edge.target) for edge in incident}),
    }
    expected = {
        "body_edges": EXPECTED_BODY_EDGES,
        "declarations": EXPECTED_DECLARATIONS,
        "signature_edges": EXPECTED_SIGNATURE_EDGES,
        "union_edges": EXPECTED_UNION_EDGES,
    }
    if counts != expected:
        raise GenerationError(f"fresh R07 projection counts {counts} != {expected}")
    visibility = Counter(declaration.visibility for declaration in selected)
    if visibility != Counter(
        {"public": EXPECTED_PUBLIC_DECLARATIONS, "private": EXPECTED_PRIVATE_DECLARATIONS}
    ):
        raise GenerationError(f"R07 declaration visibility drift: {visibility}")
    payload = (
        "format\t2\n"
        + "".join(declaration.line for declaration in selected)
        + "".join(edge.line for edge in incident)
    ).encode("utf-8")
    return Projection(payload, deterministic_gzip(payload), counts)


def frozen_declaration_destinations(
    selector: list[dict[str, str]], declarations: list[Declaration]
) -> dict[str, str]:
    selected_owners = {row["module"] for row in selector}
    selected = {
        declaration.name: declaration
        for declaration in declarations
        if declaration.owner in selected_owners
    }
    routes: dict[str, str] = {}

    def assign(name: str, destination: str) -> None:
        if name not in selected:
            raise GenerationError(f"frozen route names a declaration absent from C0005: {name}")
        if name in routes:
            raise GenerationError(f"frozen route assigns a declaration twice: {name}")
        routes[name] = destination

    for destination, names in REAL_ROUTE_GROUPS.items():
        for name in names:
            assign(name, destination)
    for destination, names in EXACT_DECLARATION_ROUTE_GROUPS.items():
        for name in names:
            assign(name, destination)
    for owner, destination in WHOLE_OWNER_DESTINATIONS.items():
        for declaration in selected.values():
            if declaration.owner == owner:
                assign(declaration.name, destination)
    for name, destination in INTERNAL_PRIVATE_ROUTES.items():
        assign(name, destination)
    for name in (
        "NumStability.norm_pow_le_exp_mul_dim_proved",
        "NumStability.powerBound_exp_mul_dim_proved",
    ):
        assign(name, FINITE_KREISS_DESTINATION)
    for name in (
        "NumStability.higham18_kreiss_two_sided_proved",
        "NumStability.higham18_kreiss_upper_proved",
    ):
        assign(name, HIGHAM_KREISS_DESTINATION)
    if set(routes) != set(selected) or len(routes) != EXPECTED_DECLARATIONS:
        raise GenerationError(
            "frozen R07 declaration map must cover every and only the 194 declarations; "
            f"missing={sorted(set(selected) - set(routes))}, "
            f"extra={sorted(set(routes) - set(selected))}"
        )
    if set(routes.values()) != NEW_DECLARATION_DESTINATIONS:
        raise GenerationError("frozen R07 declaration map must use every and only 30 destinations")
    return routes


def frozen_route_rows(
    selector: list[dict[str, str]],
    declarations: list[Declaration],
    routes: dict[str, str],
) -> list[dict[str, str]]:
    selected_owners = {row["module"] for row in selector}
    rows = [
        {
            "baseline_declaration_name": declaration.name,
            "baseline_owner_module": declaration.owner,
            "destination_module": routes[declaration.name],
            "kind": declaration.kind,
            "visibility": declaration.visibility,
        }
        for declaration in declarations
        if declaration.owner in selected_owners
    ]
    if len(rows) != EXPECTED_DECLARATIONS:
        raise GenerationError("frozen-route validation fixture must contain exactly 194 rows")
    return rows


def validate_frozen_route_rows(
    route_rows: list[dict[str, str]],
    selector: list[dict[str, str]],
    declarations: list[Declaration],
) -> None:
    actual = {
        row["baseline_declaration_name"]: row["destination_module"]
        for row in route_rows
    }
    expected = frozen_declaration_destinations(selector, declarations)
    if len(actual) != len(route_rows) or actual != expected:
        raise GenerationError(
            "declaration routes must equal the complete exact frozen 194-row name-to-destination map"
        )


IMPORT_LINE = re.compile(r"^(?:public\s+)?import\s+([^\s]+)\s*$")
GREP_IMPORT = re.compile(
    r"^[^:]+:(?P<path>[^:]+):(?P<line>[0-9]+):(?P<text>.*)$"
)


def direct_import_map(inventory: list[dict[str, str]]) -> dict[str, set[str]]:
    module_by_path = {row["path"]: row["module"] for row in inventory}
    production_modules = set(module_by_path.values())
    result: dict[str, set[str]] = defaultdict(set)
    grep = git(
        "grep",
        "-n",
        "-E",
        r"^(public[[:space:]]+)?import[[:space:]]+",
        BASE_CODE_SHA,
        "--",
        "*.lean",
        check=False,
    )
    if grep.returncode not in {0, 1}:
        raise GenerationError(grep.stderr.decode("utf-8", errors="replace"))
    for raw in grep.stdout.decode("utf-8").splitlines():
        match = GREP_IMPORT.fullmatch(raw)
        if match is None:
            raise GenerationError(f"cannot parse git-grep import row: {raw!r}")
        path = match.group("path")
        importer = module_by_path.get(path)
        if importer is None:
            continue
        import_match = IMPORT_LINE.fullmatch(match.group("text"))
        if import_match is None:
            # `git grep` also sees docstring/prose lines beginning with the word
            # "import".  Only exact Lean import commands participate.
            continue
        imported = import_match.group(1)
        if imported in production_modules:
            result[importer].add(imported)
    return result


def build_consumers(
    selector: list[dict[str, str]],
    inventory: list[dict[str, str]],
    imports: dict[str, set[str]],
) -> tuple[list[tuple[str, str, str, str, str]], dict[str, int]]:
    selected = {row["module"] for row in selector}
    path_by_module = {row["module"]: row["path"] for row in inventory}
    rows: list[tuple[str, str, str, str, str]] = []
    internal_edges = 0
    external_modules: set[str] = set()
    for importer, imported_modules in sorted(imports.items()):
        for imported in sorted(imported_modules & selected):
            if importer in selected:
                internal_edges += 1
                scope = "selected_owner"
            else:
                external_modules.add(importer)
                scope = "outside"
            rows.append(
                (
                    importer,
                    path_by_module[importer],
                    scope,
                    imported,
                    "<fresh-route-plan-required>",
                )
            )
    external_edges = sum(row[2] == "outside" for row in rows)
    actual = {
        "external_consumers": len(external_modules),
        "external_import_edges": external_edges,
        "internal_import_edges": internal_edges,
        "total_import_edges": len(rows),
    }
    expected = {
        "external_consumers": EXPECTED_EXTERNAL_CONSUMERS,
        "external_import_edges": EXPECTED_EXTERNAL_IMPORT_EDGES,
        "internal_import_edges": EXPECTED_INTERNAL_IMPORT_EDGES,
        "total_import_edges": EXPECTED_EXTERNAL_IMPORT_EDGES + EXPECTED_INTERNAL_IMPORT_EDGES,
    }
    if actual != expected:
        raise GenerationError(f"fresh R07 direct-consumer counts {actual} != {expected}")
    return rows, actual


def resolve_consumer_routes(
    rows: list[tuple[str, str, str, str, str]],
    declarations: list[Declaration],
    routes: dict[str, str],
) -> list[tuple[str, str, str, str, str]]:
    """Bind every direct consumer edge to the exact R0011 import postimage."""

    import r07_shared_postimages as shared_postimages

    umbrella_by_destination: dict[str, str] = {}
    for umbrella_path, destinations in shared_postimages.PUBLIC_UMBRELLAS.items():
        umbrella = module_from_path(umbrella_path)
        for destination in destinations:
            if destination in umbrella_by_destination:
                raise GenerationError(
                    f"public destination has multiple R0011 umbrellas: {destination}"
                )
            umbrella_by_destination[destination] = umbrella
    if set(umbrella_by_destination) != (
        NEW_DECLARATION_DESTINATIONS - INTERNAL_DESTINATIONS
    ):
        raise GenerationError("R0011 public umbrellas do not cover the exact 27 public leaves")
    public_destinations_by_owner: dict[str, set[str]] = defaultdict(set)
    for declaration in declarations:
        if declaration.visibility == "public" and declaration.name in routes:
            public_destinations_by_owner[declaration.owner].add(routes[declaration.name])

    resolved: list[tuple[str, str, str, str, str]] = []
    outside_paths: set[str] = set()
    for consumer, path, scope, old_import, _placeholder in rows:
        if scope == "selected_owner":
            new_import = old_import
        else:
            outside_paths.add(path)
            transform = shared_postimages.OUTSIDE_CONSUMER_TRANSFORMS.get(path)
            if transform is None or old_import not in transform.remove:
                raise GenerationError(
                    f"R0011 lacks an exact outside-consumer transform for {path}: {old_import}"
                )
            if path in {"NumStability/Algorithms.lean", "NumStability/Analysis.lean"}:
                suppliers = sorted(
                    {
                        umbrella_by_destination[destination]
                        for destination in public_destinations_by_owner[old_import]
                        if destination not in INTERNAL_DESTINATIONS
                    }
                )
                new_import = _semicolon(suppliers)
            else:
                new_import = _semicolon(transform.add)
        resolved.append((consumer, path, scope, old_import, new_import))
    if outside_paths != set(shared_postimages.OUTSIDE_CONSUMER_TRANSFORMS):
        raise GenerationError(
            "R0011 outside-consumer transform paths differ from the fresh 24-consumer map"
        )
    return resolved


def transitive_reachability(
    starts: set[str], targets: set[str], imports: dict[str, set[str]]
) -> int:
    pairs = 0
    for start in sorted(starts):
        reached: set[str] = set()
        queue = deque(sorted(imports.get(start, ())))
        while queue:
            module = queue.popleft()
            if module in reached:
                continue
            reached.add(module)
            queue.extend(sorted(imports.get(module, ())))
        pairs += len(reached & targets)
    return pairs


def overlap_facts(
    selector: list[dict[str, str]],
    inventory: list[dict[str, str]],
    declarations: list[Declaration],
    edges: list[Edge],
    imports: dict[str, set[str]],
) -> dict[str, Any]:
    r07 = {row["module"] for row in selector}
    declaration_owner = {declaration.name: declaration.owner for declaration in declarations}
    facts: dict[str, Any] = {}
    for peer in ("R09", "R10"):
        owners = {row["module"] for row in inventory if row["wave_id"] == peer}
        direct_forward = sum(len(imports.get(owner, set()) & owners) for owner in r07)
        direct_reverse = sum(len(imports.get(owner, set()) & r07) for owner in owners)
        signature_forward = body_forward = signature_reverse = body_reverse = 0
        for edge in edges:
            source_owner = declaration_owner.get(edge.source)
            target_owner = declaration_owner.get(edge.target)
            if source_owner in r07 and target_owner in owners:
                if edge.kind == "signature":
                    signature_forward += 1
                else:
                    body_forward += 1
            elif source_owner in owners and target_owner in r07:
                if edge.kind == "signature":
                    signature_reverse += 1
                else:
                    body_reverse += 1
        outside_r07 = {
            importer for importer, imported in imports.items() if importer not in r07 and imported & r07
        }
        outside_peer = {
            importer
            for importer, imported in imports.items()
            if importer not in owners and imported & owners
        }
        facts[peer] = {
            "direct_owner_import_edges": [direct_forward, direct_reverse],
            "transitive_owner_reachability_pairs": [
                transitive_reachability(r07, owners, imports),
                transitive_reachability(owners, r07, imports),
            ],
            "typed_signature_edges": [signature_forward, signature_reverse],
            "proof_body_edges": [body_forward, body_reverse],
            "shared_direct_outside_consumers": sorted(outside_r07 & outside_peer),
        }
    return facts


def destination_prefix(module: str) -> str:
    return module_path(module).rsplit("/", 1)[0] + "/"


def validate_destination_contract(
    inventory: list[dict[str, str]],
) -> dict[str, Any]:
    if (
        len(NEW_DECLARATION_DESTINATIONS) != 30
        or len(SOURCE_DESTINATIONS) != 1
        or len(INTERNAL_DESTINATIONS) != 3
    ):
        raise GenerationError(
            "reviewed R07 destination contract must be 30 new leaves: 26 reusable, 3 internal, 1 Source"
        )
    if any(MODULE_NAME.fullmatch(module) is None for module in NEW_DECLARATION_DESTINATIONS):
        raise GenerationError("R07 destination set contains invalid Lean module syntax")
    folded = [module.casefold() for module in NEW_DECLARATION_DESTINATIONS]
    if len(set(folded)) != len(folded):
        raise GenerationError("R07 destination modules collide under case folding")

    existing_modules = {row["module"].casefold(): row for row in inventory}
    existing_paths = {row["path"].casefold() for row in inventory}
    for module in sorted(NEW_DECLARATION_DESTINATIONS):
        path = module_path(module)
        if module.casefold() in existing_modules or path.casefold() in existing_paths:
            raise GenerationError(f"destination is not vacant at C0005: {module}")
        if git("cat-file", "-e", f"{BASE_CODE_SHA}:{path}", check=False).returncode == 0:
            raise GenerationError(f"destination blob already exists at C0005: {path}")
        if module in INTERNAL_DESTINATIONS:
            if not module.startswith("NumStability.Analysis."):
                raise GenerationError(f"internal destination is outside Analysis: {module}")
        elif module.startswith("NumStability.Analysis."):
            banned = REUSABLE_BANNED_COMPONENTS & set(module.split("."))
            if banned:
                raise GenerationError(f"reusable destination {module} has banned components {sorted(banned)}")
        elif module not in SOURCE_DESTINATIONS:
            raise GenerationError(f"destination is outside exact reusable/Source tiers: {module}")

    prefixes = sorted({destination_prefix(module) for module in NEW_DECLARATION_DESTINATIONS})
    for prefix in prefixes:
        overlaps = sorted(path for path in existing_paths if path.startswith(prefix.casefold()))
        if overlaps:
            raise GenerationError(
                f"destination prefix is not casefold-vacant at C0005: {prefix}: {overlaps[:3]}"
            )
    branch_prefixes = sorted([*prefixes, *AUTHORIZED_NONPRODUCTION_PREFIXES])
    for prefix in AUTHORIZED_NONPRODUCTION_PREFIXES:
        existing = git_text("ls-tree", "-r", "--name-only", BASE_CODE_SHA, "--", prefix).strip()
        if existing:
            raise GenerationError(f"authorized R07 test/delivery prefix is not vacant: {prefix}")
    return {
        "all_new_casefold_vacant": True,
        "branch_prefix_count": len(branch_prefixes),
        "branch_prefixes": branch_prefixes,
        "count": len(NEW_DECLARATION_DESTINATIONS),
        "internal_count": len(INTERNAL_DESTINATIONS),
        "prefix_count": len(prefixes),
        "prefixes": prefixes,
        "reusable_count": len(
            NEW_DECLARATION_DESTINATIONS - SOURCE_DESTINATIONS - INTERNAL_DESTINATIONS
        ),
        "source_count": len(SOURCE_DESTINATIONS),
    }


def load_destination_plan(path: Path, inventory: list[dict[str, str]]) -> list[dict[str, str]]:
    reject_historical_input(path)
    rows = read_tsv(path, DESTINATION_PLAN_HEADER)
    if len(rows) != len(NEW_DECLARATION_DESTINATIONS):
        raise GenerationError("destination plan must contain every and only the 30 reviewed leaves")
    by_module = {row["module"]: row for row in rows}
    if len(by_module) != len(rows) or set(by_module) != NEW_DECLARATION_DESTINATIONS:
        raise GenerationError("destination plan differs from the exact all-vacant allowlist")
    inventory_modules = {row["module"].casefold() for row in inventory}
    for module, row in by_module.items():
        expected_tier = (
            "source"
            if module in SOURCE_DESTINATIONS
            else "internal"
            if module in INTERNAL_DESTINATIONS
            else "reusable"
        )
        if (
            row["tier"] != expected_tier
            or row["existence"] != "new_casefold_vacant"
            or row["base_blob_oid"] != "-"
            or not row["rationale"].strip()
            or module.casefold() in inventory_modules
        ):
            raise GenerationError(f"{module}: destination plan existence/tier review drift")
    return rows


def load_review_metadata(
    path: Path,
    expected_sha256: str,
    artifacts: dict[str, Path],
) -> dict[str, Any]:
    reject_historical_input(path)
    if not re.fullmatch(r"[0-9A-F]{64}", expected_sha256):
        raise GenerationError("--review-metadata-sha256 must be uppercase 64-hex")
    verify_digest(path, expected_sha256)
    review = load_json(path)
    require_exact_keys(review, REVIEW_METADATA_KEYS, "review metadata")
    if (
        review.get("schema_version") != 1
        or review.get("record_kind") != "primary_human_semantic_review"
        or review.get("phase_id") != PHASE_ID
        or review.get("base_checkpoint_id") != BASE_CHECKPOINT_ID
        or review.get("base_code_sha") != BASE_CODE_SHA
        or review.get("accepted_control_sha") != ACCEPTED_CONTROL_SHA
        or review.get("reviewer_id") != OWNER_ID
        or review.get("decision") != "approved"
        or review.get("review_id") != REVIEW_ID
        or RFC3339_UTC.fullmatch(str(review.get("reviewed_at"))) is None
    ):
        raise GenerationError("review metadata lacks exact external primary-human authority")
    artifact_rows = review.get("artifacts")
    if not isinstance(artifact_rows, list):
        raise GenerationError("review metadata artifacts must be a list")
    expected = {
        role: {
            "path": repo_relative(plan),
            "role": role,
            "sha256": sha256_path(plan.resolve()),
        }
        for role, plan in artifacts.items()
    }
    actual: dict[str, Any] = {}
    for row in artifact_rows:
        if not isinstance(row, dict):
            raise GenerationError("review metadata artifact rows must be objects")
        require_exact_keys(row, {"path", "role", "sha256"}, "review artifact")
        role = row.get("role")
        if not isinstance(role, str) or role in actual:
            raise GenerationError("review metadata artifact roles must be unique strings")
        actual[role] = row
    if actual != expected:
        raise GenerationError("review metadata does not hash-pin every supplied semantic plan")
    review["_path"] = str(path.resolve())
    return review


def validate_module_classification(
    owner: str,
    actual: str,
    declaration_count: int,
    destinations: list[str],
) -> str:
    if declaration_count == 0:
        expected = "classify_compatibility"
    elif len(destinations) == 1:
        expected = "relocate_whole"
    else:
        expected = "relocate_split"
    if actual != expected:
        raise GenerationError(
            f"{owner}: semantic classification must be derived from declaration routing as "
            f"{expected}, found {actual}"
        )
    return expected


def load_module_plan(
    path: Path,
    selector: list[dict[str, str]],
    declarations: list[Declaration],
) -> list[dict[str, str]]:
    reject_historical_input(path)
    rows = read_tsv(path, MODULE_ROUTES_HEADER)
    selected = {row["module"]: row for row in selector}
    counts = Counter(
        declaration.owner for declaration in declarations if declaration.owner in selected
    )
    if {row["owner_module"] for row in rows} != set(selected) or len(rows) != len(selected):
        raise GenerationError("module plan must review every and only the 45 R07 owners once")
    classifications: Counter[str] = Counter()
    for row in rows:
        owner = row["owner_module"]
        inventory = selected[owner]
        if (
            row["path"] != inventory["path"]
            or row["base_blob_oid"] != inventory["base_blob_oid"]
            or row["current_tier"] != inventory["current_tier"]
            or row["debt_flags"] != inventory["debt_flags"]
            or row["declaration_count"] != str(counts[owner])
        ):
            raise GenerationError(f"{owner}: module plan drift from fresh C0005 facts")
        destinations = row["destination_modules"].split(";")
        if destinations != sorted(set(destinations)):
            raise GenerationError(f"{owner}: destinations must be sorted and unique")
        if not counts[owner] and destinations != ["-"]:
            raise GenerationError(
                f"{owner}: declaration-free owner uses '-' because wrapper imports are reviewed separately"
            )
        if counts[owner] and (
            not destinations
            or not set(destinations) <= NEW_DECLARATION_DESTINATIONS
        ):
            raise GenerationError(
                f"{owner}: declaration-bearing owner destination is outside the exact new-leaf allowlist"
            )
        classifications[
            validate_module_classification(
                owner,
                row["semantic_classification"],
                counts[owner],
                destinations,
            )
        ] += 1
        if row["review_status"] != "reviewed":
            raise GenerationError(f"{owner}: incomplete semantic/reviewer classification")
        if row["compatibility_action"] != "import_only_wrapper":
            raise GenerationError(f"{owner}: historical owner must become an import-only wrapper")
        if not row["split_rationale"] or not row["dependency_rationale"]:
            raise GenerationError(f"{owner}: mathematical/dependency rationale is required")
    if classifications != Counter(
        {"classify_compatibility": 32, "relocate_whole": 9, "relocate_split": 4}
    ):
        raise GenerationError(
            f"module classification census must be 32 compatibility / 9 whole / 4 split: "
            f"{classifications}"
        )
    return rows


def base_import_sequence(path: str) -> list[str]:
    text = git_file(BASE_CODE_SHA, path).decode("utf-8")
    imports: list[str] = []
    for line in text.splitlines():
        match = IMPORT_LINE.fullmatch(line)
        if match is not None:
            imports.append(match.group(1))
    return imports


def read_ilean_entries(path: Path, expected_module: str) -> dict[str, tuple[int, ...]]:
    payload = load_json(path)
    if payload.get("module") != expected_module:
        raise GenerationError(f"{path}: expected .ilean owner {expected_module}")
    decls = payload.get("decls")
    if not isinstance(decls, dict):
        raise GenerationError(f"{path}: .ilean lacks a declaration map")
    result: dict[str, tuple[int, ...]] = {}
    for name, coordinates in decls.items():
        if (
            not isinstance(name, str)
            or not isinstance(coordinates, list)
            or len(coordinates) != 8
            or any(not isinstance(value, int) or value < 0 for value in coordinates)
        ):
            raise GenerationError(f"{path}: malformed .ilean declaration span")
        result[name] = tuple(coordinates)
    return result


def authoritative_ilean_root(
    declaration_name: str, entries: dict[str, tuple[int, ...]]
) -> str:
    macro_root = MACRO_ILEAN_ROOTS.get(declaration_name)
    if macro_root is not None:
        owner_prefix, separator, _suffix = declaration_name.partition(".0.")
        macro_candidates = {
            name for name in entries if "___macroRules__" in name
        }
        if (
            not separator
            or not macro_root.startswith(f"{owner_prefix}.0.")
            or macro_root not in entries
            or entries.get(macro_root) != MACRO_ILEAN_SPANS.get(declaration_name)
            or macro_candidates != {macro_root}
        ):
            raise GenerationError(
                f"{declaration_name}: exact unique macro-generated .ilean root drift"
            )
        return macro_root
    candidate = declaration_name
    while True:
        if candidate in entries:
            return candidate
        if "." not in candidate:
            break
        candidate = candidate.rsplit(".", 1)[0]
    raise GenerationError(f"{declaration_name}: no exact longest-prefix .ilean root")


def validate_all_ilean_roots(
    selector: list[dict[str, str]],
    declarations: list[Declaration],
    ilean_root: Path,
) -> dict[str, str]:
    selected_inventory = {row["module"]: row for row in selector}
    selected_owners = set(selected_inventory)
    selected = [
        declaration
        for declaration in declarations
        if declaration.owner in selected_owners
    ]
    by_owner: dict[str, list[Declaration]] = defaultdict(list)
    for declaration in selected:
        by_owner[declaration.owner].append(declaration)
    roots: dict[str, str] = {}
    command_hashes: dict[str, str] = {}
    for owner, owner_declarations in sorted(by_owner.items()):
        logical_ilean = module_path(owner)[:-5] + ".ilean"
        entries = read_ilean_entries(ilean_root / Path(logical_ilean), owner)
        source_payload = git_file(BASE_CODE_SHA, selected_inventory[owner]["path"])
        for declaration in owner_declarations:
            root = authoritative_ilean_root(declaration.name, entries)
            roots[declaration.name] = root
            try:
                command_hashes[declaration.name] = sha256_bytes(
                    source_command_bytes(source_payload, entries[root])
                )
            except GenerationError as error:
                raise GenerationError(
                    f"{owner}/{declaration.name}: invalid .ilean source command: {error}"
                ) from error
    if len(roots) != EXPECTED_DECLARATIONS or set(roots) != {
        declaration.name for declaration in selected
    }:
        raise GenerationError("exact .ilean root audit must resolve all 194 declarations")
    if len(command_hashes) != EXPECTED_DECLARATIONS or set(command_hashes) != set(roots):
        raise GenerationError("exact .ilean command-byte audit must hash all 194 declarations")
    if set(MACRO_ILEAN_ROOTS) != set(MACRO_ILEAN_SPANS) or {
        name for name in roots if name in MACRO_ILEAN_ROOTS
    } != set(MACRO_ILEAN_ROOTS):
        raise GenerationError("exact .ilean root audit must use every and only five macro overrides")
    return roots


def source_command_bytes(payload: bytes, span: tuple[int, ...]) -> bytes:
    lines = payload.splitlines(keepends=True) or [b""]
    offsets = [0]
    for line in lines:
        offsets.append(offsets[-1] + len(line))

    def offset(line_number: int, column: int) -> int:
        if line_number == len(lines) and column == 0:
            return len(payload)
        if line_number >= len(lines):
            raise GenerationError(f"source coordinate line {line_number} exceeds source")
        content = lines[line_number]
        if content.endswith(b"\r\n"):
            content = content[:-2]
        elif content.endswith((b"\r", b"\n")):
            content = content[:-1]
        try:
            decoded = content.decode("utf-8")
        except UnicodeDecodeError as error:
            raise GenerationError(
                f"source line {line_number} is not valid UTF-8"
            ) from error
        utf16_units = 0
        utf8_bytes = 0
        if column == 0:
            return offsets[line_number]
        for character in decoded:
            next_units = utf16_units + (2 if ord(character) > 0xFFFF else 1)
            if next_units > column:
                raise GenerationError(
                    f"source coordinate column {column} splits a UTF-16 surrogate pair "
                    f"on line {line_number}"
                )
            utf16_units = next_units
            utf8_bytes += len(character.encode("utf-8"))
            if utf16_units == column:
                return offsets[line_number] + utf8_bytes
        raise GenerationError(
            f"source coordinate UTF-16 column {column} exceeds line {line_number} "
            f"length {utf16_units}"
        )

    start = offset(span[0], span[1])
    end = offset(span[2], span[3])
    if end <= start:
        raise GenerationError(f"empty or reversed source command span {span}")
    return payload[start:end]


def validate_internal_wrapper_imports(
    appended_by_owner: dict[str, frozenset[str]],
) -> None:
    actual = {
        owner: frozenset(destinations & INTERNAL_DESTINATIONS)
        for owner, destinations in appended_by_owner.items()
        if destinations & INTERNAL_DESTINATIONS
    }
    if actual:
        raise GenerationError(
            "private-only internal leaves are implementation artifacts and must not be "
            f"advertised through historical compatibility wrappers; found {actual}"
        )


def load_wrapper_plan(
    path: Path,
    selector: list[dict[str, str]],
    declarations: list[Declaration],
    module_plan: list[dict[str, str]],
) -> list[dict[str, str]]:
    reject_historical_input(path)
    rows = read_tsv(path, WRAPPER_PLAN_HEADER)
    selected = {row["module"]: row for row in selector}
    counts = Counter(
        declaration.owner for declaration in declarations if declaration.owner in selected
    )
    module_destinations = {
        row["owner_module"]: (
            [] if row["destination_modules"] == "-" else row["destination_modules"].split(";")
        )
        for row in module_plan
    }
    actual_private_only_routes = {
        owner: frozenset(set(destinations) & INTERNAL_DESTINATIONS)
        for owner, destinations in module_destinations.items()
        if set(destinations) & INTERNAL_DESTINATIONS
    }
    if actual_private_only_routes != PRIVATE_ONLY_INTERNAL_ROUTES:
        raise GenerationError(
            "private-only internal route owners differ from the exact reviewed three-owner map"
        )
    if len(rows) != len(selected) or {row["owner_module"] for row in rows} != set(selected):
        raise GenerationError("wrapper plan must cover every and only the 45 historical owners")
    preserved_total = 0
    appended_total = 0
    bearing_rows = 0
    appended_by_owner: dict[str, frozenset[str]] = {}
    for row in rows:
        owner = row["owner_module"]
        inventory = selected[owner]
        preserved = [] if row["preserved_imports"] == "-" else row["preserved_imports"].split(";")
        appended = [] if row["appended_imports"] == "-" else row["appended_imports"].split(";")
        post = [] if row["post_imports"] == "-" else row["post_imports"].split(";")
        expected_preserved = base_import_sequence(inventory["path"])
        expected_appended = (
            sorted(set(module_destinations[owner]) - INTERNAL_DESTINATIONS)
            if counts[owner]
            else []
        )
        if (
            row["path"] != inventory["path"]
            or row["base_blob_oid"] != inventory["base_blob_oid"]
            or preserved != expected_preserved
            or appended != expected_appended
            or post != [*expected_preserved, *expected_appended]
        ):
            raise GenerationError(f"{owner}: wrapper plan does not preserve exact C0005 imports then append routes")
        if len(post) != len(set(post)):
            raise GenerationError(f"{owner}: wrapper post-import list contains a duplicate")
        if appended and not set(appended) <= NEW_DECLARATION_DESTINATIONS:
            raise GenerationError(f"{owner}: wrapper appends a non-destination target")
        if not counts[owner] and post != expected_preserved:
            raise GenerationError(f"{owner}: pure wrapper must remain byte-for-byte import-equivalent")
        preserved_total += sum(target.startswith("NumStability.") for target in preserved)
        appended_total += len(appended)
        bearing_rows += bool(counts[owner])
        appended_by_owner[owner] = frozenset(appended)
    if (preserved_total, appended_total, bearing_rows) != (130, 28, 13):
        raise GenerationError(
            "wrapper frontier must be 130 preserved NumStability imports + 28 public "
            "destination imports across 13 declaration-bearing owners"
        )
    validate_internal_wrapper_imports(appended_by_owner)
    return rows


def load_source_command_plan(
    path: Path,
    selector: list[dict[str, str]],
    declarations: list[Declaration],
    ilean_root: Path,
) -> list[dict[str, str]]:
    reject_historical_input(path)
    rows = read_tsv(path, SOURCE_COMMANDS_HEADER)
    selected = {row["module"]: row for row in selector}
    metadata = {
        (declaration.owner, declaration.name): declaration
        for declaration in declarations
        if declaration.owner in selected
    }
    keys = {(row["owner_module"], row["baseline_declaration_name"]) for row in rows}
    if len(rows) != len(keys) or keys != set(metadata):
        raise GenerationError("source-command plan must span every and only the 194 declarations")
    by_owner: dict[str, list[dict[str, str]]] = defaultdict(list)
    for row in rows:
        by_owner[row["owner_module"]].append(row)
    coordinate_fields = (
        "start_line_0",
        "start_column_0",
        "end_line_0",
        "end_column_0",
        "selection_start_line_0",
        "selection_start_column_0",
        "selection_end_line_0",
        "selection_end_column_0",
    )
    for owner, owner_rows in by_owner.items():
        inventory = selected[owner]
        logical_ilean = module_path(owner)[:-5] + ".ilean"
        ilean_path = ilean_root / Path(logical_ilean)
        if not ilean_path.is_file():
            raise GenerationError(f"missing authoritative exact-code .ilean: {ilean_path}")
        ilean_sha = sha256_path(ilean_path)
        entries = read_ilean_entries(ilean_path, owner)
        source_payload = git_file(BASE_CODE_SHA, inventory["path"])
        roots = {
            declaration.name: authoritative_ilean_root(declaration.name, entries)
            for declaration in declarations
            if declaration.owner == owner
        }
        unique_spans = sorted(
            {entries[root] for root in roots.values()},
            key=lambda span: (span[0], span[1], span[2], span[3], span[4:]),
        )
        ordinal_by_span = {span: index for index, span in enumerate(unique_spans)}
        for row in owner_rows:
            key = (owner, row["baseline_declaration_name"])
            declaration = metadata[key]
            expected_root = roots[declaration.name]
            expected_span = entries[expected_root]
            if (
                row["path"] != inventory["path"]
                or row["base_blob_oid"] != inventory["base_blob_oid"]
                or row["ilean_path"] != logical_ilean
                or row["ilean_sha256"] != ilean_sha
                or row["ilean_root"] != expected_root
                or row["source_ordinal"] != str(ordinal_by_span[expected_span])
            ):
                raise GenerationError(f"{key}: source-command identity/.ilean binding drift")
            if any(not row[field].isdigit() for field in coordinate_fields):
                raise GenerationError(f"{key}: .ilean coordinates must be nonnegative decimals")
            actual_span = tuple(int(row[field]) for field in coordinate_fields)
            if actual_span != expected_span:
                raise GenerationError(f"{key}: compiler coordinates differ from .ilean")
            command = source_command_bytes(source_payload, expected_span)
            if row["command_sha256"] != sha256_bytes(command):
                raise GenerationError(f"{key}: source command bytes differ from pinned hash")
        ordered_unique = sorted(
            {(int(row["source_ordinal"]), row["ilean_root"]) for row in owner_rows}
        )
        if {ordinal for ordinal, _root in ordered_unique} != set(range(len(unique_spans))):
            raise GenerationError(f"{owner}: source ordinals do not cover increasing .ilean commands")
    return rows


def load_declaration_plan(
    path: Path,
    selector: list[dict[str, str]],
    declarations: list[Declaration],
    module_plan: list[dict[str, str]],
    source_commands: list[dict[str, str]],
) -> list[dict[str, str]]:
    reject_historical_input(path)
    rows = read_tsv(path, DECLARATION_ROUTES_HEADER)
    owners = {row["module"] for row in selector}
    selected = [declaration for declaration in declarations if declaration.owner in owners]
    metadata = {(declaration.owner, declaration.name): declaration for declaration in selected}
    order_by_key: dict[tuple[str, str], int] = {}
    owner_counts: Counter[str] = Counter()
    for declaration in selected:
        key = (declaration.owner, declaration.name)
        order_by_key[key] = owner_counts[declaration.owner]
        owner_counts[declaration.owner] += 1
    plan_keys = {(row["baseline_owner_module"], row["baseline_declaration_name"]) for row in rows}
    if len(rows) != len(plan_keys) or plan_keys != set(metadata):
        raise GenerationError("declaration plan must route every and only the 194 R07 declarations")
    destinations_by_owner = {
        row["owner_module"]: set(row["destination_modules"].split(";"))
        for row in module_plan
    }
    source_ordinal = {
        (row["owner_module"], row["baseline_declaration_name"]): row["source_ordinal"]
        for row in source_commands
    }
    for row in rows:
        key = (row["baseline_owner_module"], row["baseline_declaration_name"])
        declaration = metadata[key]
        expected_order = order_by_key[key]
        if (
            row["visibility"] != declaration.visibility
            or row["kind"] != declaration.kind
            or row["projection_order"] != str(expected_order)
            or row["source_ordinal"] != source_ordinal[key]
        ):
            raise GenerationError(f"{key}: declaration metadata/order drift")
        if row["route_class"] not in ROUTE_CLASSES:
            raise GenerationError(f"{key}: unknown route class {row['route_class']}")
        destination = row["destination_module"]
        if destination not in destinations_by_owner[declaration.owner]:
            raise GenerationError(f"{key}: destination absent from owner review")
        if destination == "-" or destination == declaration.owner:
            raise GenerationError(f"{key}: all 194 declarations must move to a new semantic leaf")
        if row["route_class"] not in {"relocate_split", "relocate_whole"}:
            raise GenerationError(f"{key}: all declarations must use a relocation route class")
        if declaration.visibility == "public" and row["normalization_decision"] != "-":
            raise GenerationError(f"{key}: public declaration names must be preserved exactly")
        if declaration.visibility == "private" and not row["normalization_decision"].startswith("rename:"):
            raise GenerationError(f"{key}: private declaration requires its exact mechanical mangle")
        if destination in SOURCE_DESTINATIONS and declaration.name not in {
            "NumStability.higham18_kreiss_two_sided_proved",
            "NumStability.higham18_kreiss_upper_proved",
        }:
            raise GenerationError(f"{key}: reusable mathematics may not route into Source")
        expected_internal = INTERNAL_PRIVATE_ROUTES.get(declaration.name)
        if destination in INTERNAL_DESTINATIONS and destination != expected_internal:
            raise GenerationError(f"{key}: internal support route is not an exact reviewed private seed")
        if expected_internal is not None and destination != expected_internal:
            raise GenerationError(f"{key}: orphan private notation must use its distinct support leaf")
    validate_frozen_route_rows(rows, selector, declarations)
    actual_by_owner: dict[str, set[str]] = defaultdict(set)
    for row in rows:
        actual_by_owner[row["baseline_owner_module"]].add(row["destination_module"])
    for owner, actual_destinations in actual_by_owner.items():
        if actual_destinations != destinations_by_owner[owner]:
            raise GenerationError(
                f"{owner}: module destinations must exactly equal declaration-route image"
            )
        expected_class = "relocate_whole" if len(actual_destinations) == 1 else "relocate_split"
        owner_classes = {
            row["route_class"]
            for row in rows
            if row["baseline_owner_module"] == owner
        }
        if owner_classes != {expected_class}:
            raise GenerationError(
                f"{owner}: route_class must be {expected_class} for its exact destination image"
            )
    source_routes = {
        row["baseline_declaration_name"]
        for row in rows
        if row["destination_module"] in SOURCE_DESTINATIONS
    }
    if source_routes != {
        "NumStability.higham18_kreiss_two_sided_proved",
        "NumStability.higham18_kreiss_upper_proved",
    }:
        raise GenerationError("Source route must contain exactly the two Higham Chapter 18 aliases")
    internal_routes = {
        row["baseline_declaration_name"]: row["destination_module"]
        for row in rows
        if row["baseline_declaration_name"] in INTERNAL_PRIVATE_ROUTES
    }
    if internal_routes != INTERNAL_PRIVATE_ROUTES:
        raise GenerationError("internal tier must contain exactly the three hash-pinned private support routes")
    for destination, expected_names in EXACT_DECLARATION_ROUTE_GROUPS.items():
        actual_names = {
            row["baseline_declaration_name"]
            for row in rows
            if row["destination_module"] == destination
        }
        if actual_names != expected_names:
            raise GenerationError(
                f"{destination}: exact reconciled declaration set drift; "
                f"missing={sorted(expected_names - actual_names)}, "
                f"extra={sorted(actual_names - expected_names)}"
            )
    for destination, expected_names in REAL_ROUTE_GROUPS.items():
        actual_names = {
            row["baseline_declaration_name"]
            for row in rows
            if row["destination_module"] == destination
        }
        if actual_names != expected_names:
            raise GenerationError(
                f"{destination}: exact corrected 97-row RealMatrixBridge route drift; "
                f"missing={sorted(expected_names - actual_names)}, "
                f"extra={sorted(actual_names - expected_names)}"
            )
    used_destinations = {row["destination_module"] for row in rows}
    if used_destinations != NEW_DECLARATION_DESTINATIONS:
        raise GenerationError(
            "declaration routes must use every and only the 30 reviewed new leaves; "
            f"missing={sorted(NEW_DECLARATION_DESTINATIONS - used_destinations)}, "
            f"extra={sorted(used_destinations - NEW_DECLARATION_DESTINATIONS)}"
        )
    return rows


def _semicolon(values: Iterable[str]) -> str:
    items = list(values)
    return ";".join(items) if items else "-"


def _unsemicolon(value: str) -> tuple[str, ...]:
    return () if value == "-" else tuple(value.split(";"))


def draft_destination_rows(
    routes: dict[str, str], declarations: list[Declaration]
) -> list[dict[str, str]]:
    metadata = {declaration.name: declaration for declaration in declarations}
    names_by_destination: dict[str, list[str]] = defaultdict(list)
    for name, destination in routes.items():
        names_by_destination[destination].append(name)
    rows: list[dict[str, str]] = []
    for module in sorted(NEW_DECLARATION_DESTINATIONS):
        names = sorted(
            names_by_destination[module],
            key=lambda name: (metadata[name].visibility != "public", name),
        )
        public_names = [name for name in names if metadata[name].visibility == "public"]
        representatives = public_names[:3] or names[:3]
        witness_text = ", ".join(f"`{name}`" for name in representatives)
        tier = (
            "source"
            if module in SOURCE_DESTINATIONS
            else "internal"
            if module in INTERNAL_DESTINATIONS
            else "reusable"
        )
        if module in SOURCE_DESTINATIONS:
            rationale = (
                "Exact Higham Chapter 18 unconditional Kreiss correspondence aliases "
                f"({witness_text}); the dedicated source-strength family keeps them separate "
                "from the reusable finite-dimensional bounds."
            )
        elif module in INTERNAL_DESTINATIONS:
            rationale = (
                "Unsupported private notation required by the nearest reusable owner "
                f"({witness_text}); the leaf is deliberately internal and is never advertised "
                "by a public aggregate."
            )
        elif module.endswith("GeneralPowerInequality.PowersOfTwo"):
            rationale = (
                "Reusable Berger k=2 and powers-of-two numerical-radius inequalities "
                f"({witness_text}); declaration review found no resolvent statement in this group."
            )
        else:
            rationale = (
                f"Declaration-level review groups {len(names)} source-independent declaration(s) "
                f"under one mathematical dependency boundary; representative witnesses: "
                f"{witness_text}."
            )
        rows.append(
            {
                "module": module,
                "tier": tier,
                "existence": "new_casefold_vacant",
                "base_blob_oid": "-",
                "rationale": rationale,
            }
        )
    return rows


def draft_module_rows(
    selector: list[dict[str, str]],
    declarations: list[Declaration],
    routes: dict[str, str],
) -> list[dict[str, str]]:
    declaration_bearing_rationales = {
        "NumStability.Analysis.BergerGeneral": (
            "The five public statements are the arbitrary-power Berger inequalities "
            "(`norm_pow_le_two_mul_numericalRadius_pow`, the three "
            "`numericalRadiusCLM_pow_*` forms, and `numericalRadius_pow_le`). The five "
            "private commands—the local Euclidean-space notation, root-of-unity, "
            "telescoping, finite-sum, and scalar-power proof support—feed those statements, "
            "so all ten commands form one general-power API.",
            "The source imports numerical-radius basics, the existing power-two Berger "
            "results, and the complex root-of-unity/circle machinery used by the private "
            "proof closure. No declaration has an independent resolvent or source-locator "
            "boundary, and the whole private reverse-dependency component stays co-routed.",
        ),
        "NumStability.Analysis.BergerInequality": (
            "The projection contains only the private Euclidean-space notation command "
            "`termᵓc`; it is not a public Berger inequality and therefore belongs in an "
            "internal support leaf rather than a reusable theorem module.",
            "Its defining context is supplied by the existing Hermitian Berger and "
            "numerical-radius imports. The historical wrapper retains those imports and "
            "does not import the private-only destination; that internal leaf is built by "
            "its isolated canonical test and remains absent from public umbrellas and "
            "compatibility targets.",
        ),
        "NumStability.Analysis.BergerResolvent": (
            "All seven public statements are k=2 or powers-of-two numerical-radius "
            "inequalities (`norm_apply_sq_add_norm_inner_sq_le`, the `*_pow_two_le` forms, "
            "and their iterates); the remaining three commands are the local Euclidean-space "
            "notation and two private algebraic helpers. No projected declaration states a "
            "resolvent identity or bound.",
            "The commands share the existing Berger `PowerTwo` and numerical-radius "
            "dependencies, and the private `exists_unit_sq_mul`/`inner_diag_diff` support "
            "feeds the public power-two chain. Keeping that closure whole avoids a false "
            "resolvent boundary inherited from the historical filename.",
        ),
        "NumStability.Analysis.CStarMatrices.Basic.RealMatrixBridge": (
            "The 97 declarations separate into fifteen finite-matrix concepts: block "
            "diagonals and their compression, column pairs and pinching, range "
            "projections/reflections, finite dimensionality, matrix and real-order "
            "bridges, projection reflections, rectangular multiplication/compression, "
            "reflection averages, and strict positivity. Each route is determined by the "
            "operation or order structure in the declaration statement, not by the legacy "
            "bridge filename.",
            "The base imports provide CStar matrices, continuous-functional-calculus order, "
            "matrix order/block operations, and the project matrix algebra. The routed DAG "
            "preserves the dependencies among those concepts while allowing consumers such "
            "as trace-MGF, Lieb concavity, and operator-log monotonicity to import only the "
            "finite-matrix facilities they actually use.",
        ),
        "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.KreissBridge": (
            "Thirteen declarations define and analyze the resolvent coefficient curve, its "
            "continuous-linear-map form, derivatives, and circle/interval integral "
            "identities. Seven declarations turn those coefficients and arc lengths into "
            "finite-dimensional norm and power bounds. These are distinct analytic-"
            "coefficient and bound interfaces, so the owner is split at that mathematical "
            "use boundary.",
            "Resolvent analyticity supplies the coefficient leaf; the Kreiss resolvent "
            "bound, matrix norms, singular values, and integration-by-parts machinery feed "
            "the downstream arc-length bound leaf. The destination DAG records the latter's "
            "dependence on the former without creating a reverse edge or cycle.",
        ),
        "NumStability.Analysis.MatrixPowersBinomialBound": (
            "The four public Schur/binomial estimates (`norm_pow_eq_norm_schur_pow`, "
            "`norm_pow_nilpotent`, `opNorm_schurpow_le_binomial`, and "
            "`exists_schur_powerBounds`) are proved through thirteen private `Ppiece`, "
            "unitary-norm, and summation commands. That complete reverse-dependency closure "
            "is one Schur-binomial estimate API.",
            "The existing Henrici binomial-bound and Schur imports jointly supply the "
            "statement vocabulary and proof machinery. Splitting the private `Ppiece` "
            "construction from its four consumers would create an artificial internal API, "
            "so every command is co-routed.",
        ),
        "NumStability.Analysis.MatrixPowersHenriciNormal": (
            "Both declarations characterize normality through the vanishing strict-upper "
            "part of a Schur form: one unconditional equivalence and its named "
            "`schurNormalImpliesStrictUpperZero_holds` witness. They form one normal-Schur "
            "characterization leaf.",
            "The statements depend together on the existing Henrici normal-matrix results, "
            "the historical Henrici surface, and the Schur results. There is no private "
            "closure or second mathematical consumer boundary to justify a split.",
        ),
        "NumStability.Analysis.MatrixPowersSchur": (
            "The nine commands divide by statement semantics: normal upper-triangular "
            "matrices being diagonal (with two private diagonal-product helpers), normal "
            "Schur form having zero strict-upper part, and exact norms of powers of normal "
            "matrices (with four private unitary/pi-norm helpers). These are Schur structure, "
            "Henrici characterization, and exact power-norm APIs respectively.",
            "Complex triangulation supports the structural leaf, while the existing exact-"
            "norm Schur module supports the power leaf. Each private helper remains with all "
            "of its reverse dependents, and the routed DAG permits the normal-"
            "characterization statement to depend on the structural theorem without merging "
            "the independently useful APIs.",
        ),
        "NumStability.Analysis.MatrixPowersSpijkerClosure": (
            "`norm_pow_le_exp_mul_dim_proved` and `powerBound_exp_mul_dim_proved` are reusable "
            "finite-dimensional Kreiss bounds. The two `higham18_kreiss_*_proved` declarations "
            "are exact Chapter 18 correspondence aliases, so they move to Source rather than "
            "being presented as additional reusable mathematics.",
            "The exact aliases depend on the reusable bounds and not conversely. Their "
            "`SpijkerKreissUnconditional/Bounds` family also gives the worker a vacant "
            "directory-prefix authority boundary while the integrator-owned one-child "
            "umbrella is the public Source locator; this is the deliberate reason for the "
            "otherwise shallow family.",
        ),
        "NumStability.Analysis.MatrixPowersSpijkerPlanar": (
            "The four public declarations bound polynomial degree and projection-crossing "
            "cardinality and derive the rational-order arc-length consequence; the private "
            "`natDegree_C_mul_mul_le_two_mul` command is their polynomial-degree support. "
            "They form one planar polynomial-crossing interface.",
            "The existing planar algebra and rational Spijker modules supply the polynomial "
            "and certificate vocabulary. The private degree lemma is in the same reverse-"
            "dependency component as the public crossing results, so no smaller honest leaf "
            "exists.",
        ),
        "NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis": (
            "The four public statements connect crossing variation, the planar analytic "
            "bridge, rational-order arc length, and the proved Spijker arc-length bound. The "
            "thirteen private partition, multiplicity, measurability, integral, and "
            "eVariation commands are exactly the proof closure for that variation argument.",
            "Interval-integral derivatives, product integration, planar analysis, the planar "
            "crossing results, and the projection-integral API all participate in the same "
            "proof chain. Co-routing the private closure preserves that dependency boundary "
            "and avoids exposing proof scaffolding as separate reusable modules.",
        ),
        "NumStability.Analysis.NumericalRadius": (
            "The only remaining declaration is the private Euclidean-space notation "
            "`termᵓc`; the public numerical-radius API is already in "
            "`LinearOperators.NumericalRadius.Core.Basic`. The command is therefore internal "
            "support, not another numerical-radius theorem.",
            "The historical imports establish the matrix, inner-product, Rayleigh, and core "
            "numerical-radius context needed by the notation. The old wrapper preserves "
            "those imports but does not advertise the private-only leaf; its isolated "
            "canonical test supplies the build witness.",
        ),
        "NumStability.Analysis.PseudospectralResolvent": (
            "The only projected declaration is the private scalar algebra-map notation "
            "`«term↑ₐ»`; all public pseudospectral resolvent lower-bound mathematics is "
            "already in its semantic module. This command belongs in an internal notation "
            "leaf rather than a public resolvent API.",
            "The existing spectrum, norm-limit, pseudospectral criterion, and resolvent "
            "lower-bound imports supply its elaboration context. The historical wrapper "
            "retains them without importing the private-only leaf; an isolated canonical "
            "test builds that leaf, and no public aggregate or compatibility target "
            "advertises it.",
        ),
    }
    counts = Counter(
        declaration.owner
        for declaration in declarations
        if declaration.owner in {row["module"] for row in selector}
    )
    names_by_owner: dict[str, list[str]] = defaultdict(list)
    destinations_by_owner: dict[str, set[str]] = defaultdict(set)
    for declaration in declarations:
        if declaration.name in routes:
            names_by_owner[declaration.owner].append(declaration.name)
            destinations_by_owner[declaration.owner].add(routes[declaration.name])
    rows: list[dict[str, str]] = []
    for inventory in selector:
        owner = inventory["module"]
        destinations = sorted(destinations_by_owner.get(owner, set()))
        declaration_count = counts[owner]
        if declaration_count == 0:
            semantic_classification = "classify_compatibility"
            split_rationale = (
                "The exact format-2 projection contains no declarations; retain only the "
                "historical import surface as a compatibility wrapper."
            )
            dependency_rationale = (
                f"Preserve the exact C0005 sequence of {len(base_import_sequence(inventory['path']))} "
                "direct import(s); no declaration implementation remains in this owner."
            )
        elif len(destinations) == 1:
            semantic_classification = "relocate_whole"
            if owner not in declaration_bearing_rationales:
                raise GenerationError(f"missing declaration-specific review rationale: {owner}")
            split_rationale, dependency_rationale = declaration_bearing_rationales[owner]
        else:
            semantic_classification = "relocate_split"
            if owner not in declaration_bearing_rationales:
                raise GenerationError(f"missing declaration-specific review rationale: {owner}")
            split_rationale, dependency_rationale = declaration_bearing_rationales[owner]
        rows.append(
            {
                "owner_module": owner,
                "path": inventory["path"],
                "base_blob_oid": inventory["base_blob_oid"],
                "current_tier": inventory["current_tier"],
                "debt_flags": inventory["debt_flags"],
                "declaration_count": str(declaration_count),
                "semantic_classification": semantic_classification,
                "destination_modules": _semicolon(destinations),
                "compatibility_action": "import_only_wrapper",
                "split_rationale": split_rationale,
                "dependency_rationale": dependency_rationale,
                "review_status": "reviewed",
            }
        )
    expected_rationale_owners = {
        row["module"] for row in selector if counts[row["module"]] > 0
    }
    if set(declaration_bearing_rationales) != expected_rationale_owners:
        raise GenerationError(
            "declaration-specific rationale map differs from exact declaration-bearing owners"
        )
    return rows


def draft_wrapper_rows(
    selector: list[dict[str, str]],
    module_rows: list[dict[str, str]],
) -> list[dict[str, str]]:
    module_destinations = {
        row["owner_module"]: (
            [] if row["destination_modules"] == "-" else row["destination_modules"].split(";")
        )
        for row in module_rows
    }
    declaration_counts = {
        row["owner_module"]: int(row["declaration_count"]) for row in module_rows
    }
    rows: list[dict[str, str]] = []
    for inventory in selector:
        owner = inventory["module"]
        preserved = base_import_sequence(inventory["path"])
        appended = (
            sorted(set(module_destinations[owner]) - INTERNAL_DESTINATIONS)
            if declaration_counts[owner]
            else []
        )
        post = [*preserved, *appended]
        rows.append(
            {
                "owner_module": owner,
                "path": inventory["path"],
                "base_blob_oid": inventory["base_blob_oid"],
                "preserved_imports": _semicolon(preserved),
                "appended_imports": _semicolon(appended),
                "post_imports": _semicolon(post),
            }
        )
    return rows


def draft_source_command_rows(
    selector: list[dict[str, str]],
    declarations: list[Declaration],
    ilean_root: Path,
) -> list[dict[str, str]]:
    selected = {row["module"]: row for row in selector}
    by_owner: dict[str, list[Declaration]] = defaultdict(list)
    for declaration in declarations:
        if declaration.owner in selected:
            by_owner[declaration.owner].append(declaration)
    rows: list[dict[str, str]] = []
    for owner, owner_declarations in sorted(by_owner.items()):
        inventory = selected[owner]
        logical_ilean = module_path(owner)[:-5] + ".ilean"
        ilean_path = ilean_root / Path(logical_ilean)
        entries = read_ilean_entries(ilean_path, owner)
        roots = {
            declaration.name: authoritative_ilean_root(declaration.name, entries)
            for declaration in owner_declarations
        }
        unique_spans = sorted(
            {entries[root] for root in roots.values()},
            key=lambda span: (span[0], span[1], span[2], span[3], span[4:]),
        )
        ordinal_by_span = {span: index for index, span in enumerate(unique_spans)}
        source_payload = git_file(BASE_CODE_SHA, inventory["path"])
        ilean_sha256 = sha256_path(ilean_path)
        for declaration in owner_declarations:
            root = roots[declaration.name]
            span = entries[root]
            values: tuple[Any, ...] = (
                owner,
                inventory["path"],
                inventory["base_blob_oid"],
                declaration.name,
                logical_ilean,
                ilean_sha256,
                root,
                str(ordinal_by_span[span]),
                *(str(value) for value in span),
                sha256_bytes(source_command_bytes(source_payload, span)),
            )
            rows.append(dict(zip(SOURCE_COMMANDS_HEADER, values)))
    return sorted(
        rows,
        key=lambda row: (
            row["owner_module"],
            int(row["source_ordinal"]),
            row["baseline_declaration_name"],
        ),
    )


def draft_declaration_rows(
    selector: list[dict[str, str]],
    declarations: list[Declaration],
    routes: dict[str, str],
    source_rows: list[dict[str, str]],
) -> list[dict[str, str]]:
    selected_owners = {row["module"] for row in selector}
    order_by_key: dict[tuple[str, str], int] = {}
    owner_counts: Counter[str] = Counter()
    destinations_by_owner: dict[str, set[str]] = defaultdict(set)
    for declaration in declarations:
        if declaration.owner not in selected_owners:
            continue
        key = (declaration.owner, declaration.name)
        order_by_key[key] = owner_counts[declaration.owner]
        owner_counts[declaration.owner] += 1
        destinations_by_owner[declaration.owner].add(routes[declaration.name])
    source_ordinal = {
        (row["owner_module"], row["baseline_declaration_name"]): row["source_ordinal"]
        for row in source_rows
    }
    rows: list[dict[str, str]] = []
    for declaration in declarations:
        if declaration.owner not in selected_owners:
            continue
        destination = routes[declaration.name]
        key = (declaration.owner, declaration.name)
        route_class = (
            "relocate_whole"
            if len(destinations_by_owner[declaration.owner]) == 1
            else "relocate_split"
        )
        if declaration.visibility == "public":
            normalization = "-"
        else:
            owner_prefix = f"_private.{declaration.owner}.0."
            if not declaration.name.startswith(owner_prefix):
                raise GenerationError(
                    f"{declaration.name}: private declaration lacks exact baseline owner mangle"
                )
            suffix = declaration.name.removeprefix(owner_prefix)
            normalization = f"rename:_private.{destination}.0.{suffix}"
        rows.append(
            {
                "baseline_owner_module": declaration.owner,
                "baseline_declaration_name": declaration.name,
                "visibility": declaration.visibility,
                "kind": declaration.kind,
                "projection_order": str(order_by_key[key]),
                "source_ordinal": source_ordinal[key],
                "destination_module": destination,
                "route_class": route_class,
                "normalization_decision": normalization,
            }
        )
    return sorted(
        rows,
        key=lambda row: (
            row["baseline_owner_module"],
            int(row["projection_order"]),
            row["baseline_declaration_name"],
        ),
    )


def _format_compatibility_targets(targets: Sequence[str]) -> str:
    quoted = [f"`{target}`" for target in targets]
    if len(quoted) == 1:
        return quoted[0]
    if len(quoted) == 2:
        return f"{quoted[0]} and {quoted[1]}"
    return ", ".join(quoted[:-1]) + f", and {quoted[-1]}"


def draft_compatibility_postimage(wrapper_rows: list[dict[str, str]]) -> bytes:
    base = git_file(BASE_CODE_SHA, "docs/architecture/COMPATIBILITY.md")
    lines = base.decode("utf-8").splitlines(keepends=True)
    pattern = re.compile(r"^\| `([^`]+)` \| (.+) \|\n$")
    row_indices = [index for index, line in enumerate(lines) if pattern.fullmatch(line)]
    if not row_indices:
        raise GenerationError("compatibility draft could not locate the forwarding table")
    first, last = row_indices[0], row_indices[-1]
    if row_indices != list(range(first, last + 1)):
        raise GenerationError("compatibility forwarding rows are not contiguous")
    table_rows = {
        pattern.fullmatch(lines[index]).group(1): lines[index]  # type: ignore[union-attr]
        for index in row_indices
    }
    for row in wrapper_rows:
        owner = row["owner_module"]
        if owner in table_rows:
            raise GenerationError(f"compatibility draft would overwrite existing row {owner}")
        post_imports = [] if row["post_imports"] == "-" else row["post_imports"].split(";")
        targets = list(dict.fromkeys(
            target for target in post_imports if target not in INTERNAL_DESTINATIONS
        ))
        if not targets:
            raise GenerationError(f"{owner}: compatibility draft lacks a public import target")
        table_rows[owner] = (
            f"| `{owner}` | {_format_compatibility_targets(targets)} |\n"
        )
    payload = "".join(
        [*lines[:first], *(table_rows[key] for key in sorted(table_rows)), *lines[last + 1 :]]
    ).encode("utf-8")
    if b"\r" in payload or not payload.endswith(b"\n"):
        raise GenerationError("compatibility draft must use canonical LF text")
    return payload


def planned_phase_postimage(request_paths: set[str]) -> dict[str, Any]:
    phase_path = repo_relative(PHASE / "phase.json")
    document = json.loads(git_file(ACCEPTED_CONTROL_SHA, phase_path))
    if document.get("current_checkpoint_id") != BASE_CHECKPOINT_ID:
        raise GenerationError("R07 planning phase must remain at exact C0005")
    milestones = {
        row.get("milestone_id"): row
        for row in document.get("milestones", [])
        if isinstance(row, dict)
    }
    if milestones.get(MILESTONE_ID, {}).get("status") != "ready":
        raise GenerationError("M07 must remain ready during planned-control construction")
    rules = document.get("shared_paths")
    if not isinstance(rules, list):
        raise GenerationError("phase shared_paths must be a list")
    exact = {
        row.get("path")
        for row in rules
        if isinstance(row, dict) and row.get("match") == "exact"
    }
    prefixes = [
        row.get("path")
        for row in rules
        if isinstance(row, dict) and row.get("match") == "prefix"
    ]
    if None in exact or None in prefixes or (len(exact), len(prefixes)) != (155, 5):
        raise GenerationError("accepted C0005 shared-path census must be 155 exact / 5 prefix")
    overlap = exact & request_paths
    additions = request_paths - exact
    if (len(overlap), len(additions)) != (10, 36):
        raise GenerationError(
            f"R0011 shared reservation census must be 10 existing / 36 new, found "
            f"{len(overlap)} / {len(additions)}"
        )
    exact.update(request_paths)
    if (len(exact), len(prefixes)) != (191, 5):
        raise GenerationError("planned R07 phase must contain 191 exact / 5 prefix rules")
    document["shared_paths"] = [
        {"match": "exact", "path": path} for path in sorted(exact)
    ] + [{"match": "prefix", "path": path} for path in prefixes]
    return document


def tier_assignment_rows(
    selector: list[dict[str, str]],
    destination_rows: list[dict[str, str]],
) -> list[tuple[str, str, str]]:
    import r07_shared_postimages as shared_postimages

    rows: list[tuple[str, str, str]] = []
    for owner in sorted(row["module"] for row in selector):
        rows.append(
            (
                owner,
                "compatibility",
                "historical R07 owner becomes an import-only forwarding module",
            )
        )
    for row in sorted(destination_rows, key=lambda item: item["module"]):
        rows.append((row["module"], row["tier"], row["rationale"]))
    for path in sorted(shared_postimages.PUBLIC_UMBRELLAS):
        rows.append(
            (
                module_from_path(path),
                "aggregate",
                "integrator-owned declaration-free umbrella over reviewed public R07 leaves",
            )
        )
    rows.sort()
    if len(rows) != 87 or Counter(row[1] for row in rows) != Counter(
        {"aggregate": 12, "compatibility": 45, "internal": 3, "reusable": 26, "source": 1}
    ):
        raise GenerationError("R07 tier assignment census must be exact 87-row 45/30/12 plan")
    return rows


def scope_rule_rows(
    selector: list[dict[str, str]],
    inventory: list[dict[str, str]],
    destination_facts: dict[str, Any],
    planned_phase: dict[str, Any],
    request_paths: set[str],
) -> list[tuple[str, str, str, str, str]]:
    rows: list[tuple[str, str, str, str, str]] = []
    owned = {row["path"] for row in selector}
    rows.extend(
        (
            "worker_owned",
            "exact",
            path,
            OPERATOR_ID,
            "frozen exact C0005 R07 historical owner",
        )
        for path in sorted(owned)
    )
    rows.extend(
        (
            "worker_destination",
            "prefix",
            path,
            OPERATOR_ID,
            "casefold-vacant production/test/delivery destination authority",
        )
        for path in destination_facts["branch_prefixes"]
    )
    rows.extend(
        (
            "integrator_shared_request",
            "exact",
            path,
            OWNER_ID,
            "exact common-base R0011 postimage",
        )
        for path in sorted(request_paths)
    )
    shared_rules = planned_phase["shared_paths"]
    forbidden = {
        ("exact", row["path"])
        for row in inventory
        if row["path"] not in owned
    }
    forbidden.update((row["match"], row["path"]) for row in shared_rules)
    forbidden.update(("prefix", path) for path in PROTECTED_PREFIXES)
    exact_count = sum(match == "exact" for match, _path in forbidden)
    prefix_count = sum(match == "prefix" for match, _path in forbidden)
    if (exact_count, prefix_count) != (2804, 6):
        raise GenerationError(
            f"B0010 planned forbidden scope must be 2804 exact / 6 prefix, found "
            f"{exact_count} / {prefix_count}"
        )
    for match, path in sorted(forbidden):
        rows.append(
            (
                "worker_forbidden",
                match,
                path,
                OWNER_ID,
                "selector complement, protected infrastructure, or integrator reservation",
            )
        )
    for selected_path in owned:
        for rule in shared_rules:
            shared_path = rule["path"]
            intersects = (
                selected_path == shared_path
                if rule["match"] == "exact"
                else selected_path.startswith(shared_path)
            )
            if intersects:
                raise GenerationError(
                    f"R07 owned path intersects planned shared authority: {selected_path}"
                )
    return rows


def review_json_payloads(
    *,
    selector: list[dict[str, str]],
    inventory: list[dict[str, str]],
    projection: Projection,
    overlaps: dict[str, Any],
    consumer_counts: dict[str, int],
    destination_facts: dict[str, Any],
    scope_rows: list[tuple[str, str, str, str, str]],
    rendered: Any,
) -> tuple[bytes, bytes, bytes]:
    selected_inventory = [
        row for row in inventory if row["module"] in {item["module"] for item in selector}
    ]
    projection_review = canonical_json(
        {
            "base_checkpoint_id": BASE_CHECKPOINT_ID,
            "base_code_sha": BASE_CODE_SHA,
            "counts": projection.counts,
            "graph_sha256": GRAPH_SHA256,
            "gzip_sha256": sha256_bytes(projection.compressed),
            "payload_sha256": sha256_bytes(projection.payload),
            "projection_id": PROJECTION_ID,
            "selector_count": len(selector),
            "selected_inventory_count": len(selected_inventory),
            "status": "review_candidate",
            "wave_id": WAVE_ID,
        }
    )
    overlap_review = canonical_json(
        {
            "base_checkpoint_id": BASE_CHECKPOINT_ID,
            "base_code_sha": BASE_CODE_SHA,
            "consumer_counts": consumer_counts,
            "destination_contract": destination_facts,
            "overlap_facts": overlaps,
            "projected_remaining_queue": {"R09": 72, "R10": 18},
            "scope_rule_count": len(scope_rows),
            "status": "review_candidate",
            "wave_id": WAVE_ID,
        }
    )
    render_review = canonical_json(rendered.hash_report())
    return projection_review, overlap_review, render_review


def build_review_draft_payloads(
    selector: list[dict[str, str]],
    inventory: list[dict[str, str]],
    declarations: list[Declaration],
    edges: list[Edge],
    routes: dict[str, str],
    consumers: list[tuple[str, str, str, str, str]],
    imports: dict[str, set[str]],
    consumer_counts: dict[str, int],
    overlaps: dict[str, Any],
    projection: Projection,
    destination_facts: dict[str, Any],
    ilean_root: Path,
) -> dict[Path, bytes]:
    import r07_shared_postimages as shared_postimages

    destination_rows = draft_destination_rows(routes, declarations)
    module_rows = draft_module_rows(selector, declarations, routes)
    wrapper_rows = draft_wrapper_rows(selector, module_rows)
    source_rows = draft_source_command_rows(selector, declarations, ilean_root)
    declaration_rows = draft_declaration_rows(
        selector, declarations, routes, source_rows
    )
    normalization_rows = private_normalization(declaration_rows, declarations)
    closure_rows = private_closure(
        declaration_rows,
        declarations,
        edges,
        {row["module"] for row in selector},
    )
    dag_rows = destination_dag(declaration_rows, edges)
    test_rows = minimum_test_plan(
        selector, declaration_rows, consumers, imports, declarations, edges
    )
    compatibility = draft_compatibility_postimage(wrapper_rows)
    rendered = shared_postimages.render_artifacts(compatibility, verify_replay=True)
    request_paths = set(rendered.postimages)
    planned_phase = planned_phase_postimage(request_paths)
    scope_rows = scope_rule_rows(
        selector, inventory, destination_facts, planned_phase, request_paths
    )
    tier_rows = tier_assignment_rows(selector, destination_rows)
    post_move_rows = post_move_import_manifest(
        selector=selector,
        inventory=inventory,
        destination_plan=destination_rows,
        wrapper_plan=wrapper_rows,
        declaration_plan=declaration_rows,
        dag_rows=dag_rows,
        tier_rows=tier_rows,
        rendered=rendered,
    )
    external_supply_rows = external_owner_supply(
        selector=selector,
        inventory=inventory,
        declarations=declarations,
        edges=edges,
        declaration_plan=declaration_rows,
        dag_rows=dag_rows,
        manifest_rows=post_move_rows,
        base_imports=imports,
        rendered=rendered,
    )
    projection_review, overlap_review, render_review = review_json_payloads(
        selector=selector,
        inventory=inventory,
        projection=projection,
        overlaps=overlaps,
        consumer_counts=consumer_counts,
        destination_facts=destination_facts,
        scope_rows=scope_rows,
        rendered=rendered,
    )
    selected_modules = {row["module"] for row in selector}
    selected_inventory = [
        row for row in inventory if row["module"] in selected_modules
    ]
    payloads = {
        REVIEW_DRAFT_PATHS["destination_plan"]: tsv_bytes(
            DESTINATION_PLAN_HEADER,
            ([row[column] for column in DESTINATION_PLAN_HEADER] for row in destination_rows),
        ),
        REVIEW_DRAFT_PATHS["module_plan"]: tsv_bytes(
            MODULE_ROUTES_HEADER,
            ([row[column] for column in MODULE_ROUTES_HEADER] for row in module_rows),
        ),
        REVIEW_DRAFT_PATHS["wrapper_plan"]: tsv_bytes(
            WRAPPER_PLAN_HEADER,
            ([row[column] for column in WRAPPER_PLAN_HEADER] for row in wrapper_rows),
        ),
        REVIEW_DRAFT_PATHS["source_command_plan"]: tsv_bytes(
            SOURCE_COMMANDS_HEADER,
            ([row[column] for column in SOURCE_COMMANDS_HEADER] for row in source_rows),
        ),
        REVIEW_DRAFT_PATHS["declaration_plan"]: tsv_bytes(
            DECLARATION_ROUTES_HEADER,
            ([row[column] for column in DECLARATION_ROUTES_HEADER] for row in declaration_rows),
        ),
        COMPATIBILITY_DRAFT: compatibility,
        DERIVED_REVIEW_DRAFT_PATHS["consumer_plan"]: tsv_bytes(
            CONSUMERS_HEADER, consumers
        ),
        DERIVED_REVIEW_DRAFT_PATHS["destination_dag"]: tsv_bytes(
            DESTINATION_DAG_HEADER, dag_rows
        ),
        DERIVED_REVIEW_DRAFT_PATHS["external_owner_supply"]: tsv_bytes(
            EXTERNAL_OWNER_SUPPLY_HEADER, external_supply_rows
        ),
        DERIVED_REVIEW_DRAFT_PATHS["inventory"]: tsv_bytes(
            INVENTORY_HEADER,
            ([row[column] for column in INVENTORY_HEADER] for row in selected_inventory),
        ),
        DERIVED_REVIEW_DRAFT_PATHS["overlap_review"]: overlap_review,
        DERIVED_REVIEW_DRAFT_PATHS["post_move_import_manifest"]: tsv_bytes(
            POST_MOVE_IMPORT_MANIFEST_HEADER, post_move_rows
        ),
        DERIVED_REVIEW_DRAFT_PATHS["private_closure"]: tsv_bytes(
            PRIVATE_CLOSURE_HEADER, closure_rows
        ),
        DERIVED_REVIEW_DRAFT_PATHS["private_normalization"]: tsv_bytes(
            PRIVATE_NORMALIZATION_HEADER, normalization_rows
        ),
        DERIVED_REVIEW_DRAFT_PATHS["projection_review"]: projection_review,
        DERIVED_REVIEW_DRAFT_PATHS["r0011_import_manifest"]: rendered.import_manifest,
        DERIVED_REVIEW_DRAFT_PATHS["r0011_render_review"]: render_review,
        DERIVED_REVIEW_DRAFT_PATHS["r0011_request_plan"]: rendered.request_plan,
        DERIVED_REVIEW_DRAFT_PATHS["scope_rules"]: tsv_bytes(
            SCOPE_RULES_HEADER, scope_rows
        ),
        DERIVED_REVIEW_DRAFT_PATHS["test_plan"]: tsv_bytes(TEST_PLAN_HEADER, test_rows),
        DERIVED_REVIEW_DRAFT_PATHS["tier_assignments"]: tsv_bytes(
            TIER_ASSIGNMENTS_HEADER, tier_rows
        ),
    }
    packet_artifacts = [
        artifact_for_payload(path, payload)
        for path, payload in sorted(payloads.items(), key=lambda item: repo_relative(item[0]))
    ] + [
        {
            "path": repo_relative(CI_ATTESTATION),
            "sha256": CI_ATTESTATION_SHA256,
        },
        {
            "path": repo_relative(Path(__file__).resolve()),
            "sha256": sha256_path(Path(__file__).resolve()),
        },
        {
            "path": repo_relative(SHARED_POSTIMAGE_RENDERER),
            "sha256": sha256_path(SHARED_POSTIMAGE_RENDERER),
        },
    ]
    payloads[DERIVED_REVIEW_DRAFT_PATHS["review_packet"]] = canonical_json(
        {
            "accepted_control_sha": ACCEPTED_CONTROL_SHA,
            "artifacts": sorted(packet_artifacts, key=lambda row: row["path"]),
            "base_checkpoint_id": BASE_CHECKPOINT_ID,
            "base_code_sha": BASE_CODE_SHA,
            "decision_requested": "primary-human exact semantic and planned-control approval",
            "exclusions": [
                "R07 integration",
                "R07 self-acceptance",
                "checkpoint acceptance",
                "branch retirement",
            ],
            "graph_sha256": GRAPH_SHA256,
            "ids": {
                "branch": BRANCH_ID,
                "milestone": MILESTONE_ID,
                "projection": PROJECTION_ID,
                "request": REQUEST_ID,
                "wave": WAVE_ID,
            },
            "record_kind": "r07_review_packet",
            "schema_version": 1,
        }
    )
    return payloads


def write_review_drafts(
    payloads: dict[Path, bytes], *, refresh: bool = False
) -> list[dict[str, Any]]:
    expected_paths = (
        set(REVIEW_DRAFT_PATHS.values())
        | set(DERIVED_REVIEW_DRAFT_PATHS.values())
        | {COMPATIBILITY_DRAFT}
    )
    if set(payloads) != expected_paths:
        raise GenerationError("review draft emitter path set drift")
    reports: list[dict[str, Any]] = []
    for path, payload in sorted(payloads.items(), key=lambda item: str(item[0])):
        if path.parent != PHASE / "reviews":
            raise GenerationError(f"review draft escaped the fixed review directory: {path}")
        if path.exists() and path.read_bytes() != payload and not refresh:
            raise GenerationError(f"refusing to overwrite divergent review draft: {path}")
        if not path.exists() or path.read_bytes() != payload:
            path.write_bytes(payload)
        reports.append(
            {
                "bytes": len(payload),
                "path": repo_relative(path),
                "sha256": sha256_bytes(payload),
            }
        )
    return reports


def private_normalization(
    route_rows: list[dict[str, str]],
    declarations: list[Declaration],
) -> list[tuple[str, str, str]]:
    rows: list[tuple[str, str, str]] = []
    for row in route_rows:
        if row["visibility"] != "private":
            continue
        old = row["baseline_declaration_name"]
        destination = row["destination_module"]
        decision = row["normalization_decision"]
        owner_prefix = f"_private.{row['baseline_owner_module']}.0."
        if not old.startswith(owner_prefix):
            raise GenerationError(f"{old}: private name lacks its exact baseline owner mangle")
        suffix = old.removeprefix(owner_prefix)
        new = f"_private.{destination}.0.{suffix}"
        if decision != f"rename:{new}":
            raise GenerationError(f"{old}: private rename must preserve the exact unchanged suffix")
        rows.append((old, new, destination))
    if len(rows) != EXPECTED_PRIVATE_DECLARATIONS or len({row[1] for row in rows}) != len(rows):
        raise GenerationError("private normalization must be total and collision-free for 44 rows")
    baseline_names = {declaration.name for declaration in declarations}
    collisions = sorted(new for _old, new, _destination in rows if new in baseline_names)
    if collisions:
        raise GenerationError(f"private target collides with baseline namespace: {collisions}")
    return sorted(rows, key=lambda row: row[0])


def private_closure(
    route_rows: list[dict[str, str]],
    declarations: list[Declaration],
    edges: list[Edge],
    selected_owners: set[str],
) -> list[tuple[str, str, str, str, str, str, int, str, str, int, int]]:
    metadata = {declaration.name: declaration for declaration in declarations}
    seeds = {
        row["baseline_declaration_name"]
        for row in route_rows
        if row["visibility"] == "private"
    }
    reverse: dict[str, list[tuple[str, str]]] = defaultdict(list)
    span: dict[str, Counter[str]] = defaultdict(Counter)
    for edge in edges:
        if edge.source in metadata:
            span[edge.source][edge.kind] += 1
        if edge.target in metadata:
            span[edge.target][edge.kind] += 1
        if edge.source in metadata and edge.target in metadata:
            reverse[edge.target].append((edge.source, edge.kind))
        target = metadata.get(edge.target)
        source = metadata.get(edge.source)
        if (
            target is not None
            and target.name in seeds
            and source is not None
            and source.owner not in selected_owners
        ):
            raise GenerationError(
                f"private declaration escapes selected R07 owners: {edge.source} -> {edge.target}"
            )
    memberships: dict[str, dict[str, tuple[int, str, str]]] = defaultdict(dict)
    for seed in sorted(seeds):
        seen: dict[str, tuple[int, str, str]] = {seed: (0, "-", "seed")}
        queue = deque([seed])
        while queue:
            current = queue.popleft()
            current_depth = seen[current][0]
            for dependent, kind in sorted(reverse.get(current, ())):
                declaration = metadata[dependent]
                if declaration.owner not in selected_owners or dependent in seen:
                    continue
                seen[dependent] = (current_depth + 1, current, kind)
                queue.append(dependent)
        for member, witness in seen.items():
            memberships[member][seed] = witness
    reached = set(memberships)
    if len(seeds) != EXPECTED_PRIVATE_DECLARATIONS or len(reached) != 77:
        raise GenerationError(
            f"directed private reverse closure must be 44 seeds / 77 rows, found {len(seeds)} / {len(reached)}"
        )
    multiple_memberships = sum(len(seed_rows) > 1 for seed_rows in memberships.values())
    maximum_memberships = max(map(len, memberships.values()))
    if (multiple_memberships, maximum_memberships) != (52, 13):
        raise GenerationError(
            "private closure overlap census must be 52 multi-seed members with maximum 13"
        )

    direct_edges = [
        edge
        for edge in edges
        if edge.target in seeds
        and edge.source in metadata
        and metadata[edge.source].owner in selected_owners
    ]
    direct_pairs = {(edge.source, edge.target) for edge in direct_edges}
    if len(direct_edges) != 85 or len(direct_pairs) != 67:
        raise GenerationError(
            f"private direct co-route census must be 85 typed / 67 unique pairs, "
            f"found {len(direct_edges)} / {len(direct_pairs)}"
        )
    parent: dict[str, str] = {name: name for name in seeds | {pair[0] for pair in direct_pairs}}

    def find(name: str) -> str:
        while parent[name] != name:
            parent[name] = parent[parent[name]]
            name = parent[name]
        return name

    def union(left: str, right: str) -> None:
        left_root = find(left)
        right_root = find(right)
        if left_root == right_root:
            return
        low, high = sorted((left_root, right_root))
        parent[high] = low

    for source, target in sorted(direct_pairs):
        union(source, target)
    component_members: dict[str, set[str]] = defaultdict(set)
    for name in parent:
        component_members[find(name)].add(name)
    canonical_component: dict[str, str] = {}
    for members in component_members.values():
        component_id = min(members)
        for name in members:
            canonical_component[name] = component_id
    component_census = (
        len(component_members),
        sum(len(members) > 1 for members in component_members.values()),
        sum(len(members & seeds) > 1 for members in component_members.values()),
    )
    if component_census != (14, 9, 7):
        raise GenerationError(
            "private co-route union-find census must be 14 total components, "
            "9 nontrivial direct-edge components, and 7 multi-seed components"
        )
    rows: list[tuple[str, str, str, str, str, str, int, str, str, int, int]] = []
    for name in sorted(reached):
        declaration = metadata.get(name)
        if declaration is None:
            raise GenerationError(f"private closure lacks declaration metadata: {name}")
        rows.append(
            (
                name,
                declaration.owner,
                declaration.visibility,
                "yes" if declaration.owner in selected_owners else "no",
                "private_seed" if name in seeds else "reverse_dependent_boundary",
                ";".join(sorted(memberships[name])),
                json.dumps(
                    [
                        {
                            "depth": depth,
                            "edge_kind": kind,
                            "predecessor": predecessor,
                            "seed": seed,
                        }
                        for seed, (depth, predecessor, kind) in sorted(
                            memberships[name].items()
                        )
                    ],
                    ensure_ascii=False,
                    separators=(",", ":"),
                    sort_keys=True,
                ),
                canonical_component.get(name, "-"),
                min(witness[0] for witness in memberships[name].values()),
                span[name]["signature"],
                span[name]["body"],
            )
        )
    return rows


def validate_private_route_components(
    route_rows: list[dict[str, str]], edges: list[Edge]
) -> None:
    route = {
        row["baseline_declaration_name"]: row["destination_module"] for row in route_rows
    }
    private = {
        row["baseline_declaration_name"]
        for row in route_rows
        if row["visibility"] == "private"
    }
    direct_edges = [
        edge for edge in edges if edge.source in route and edge.target in private
    ]
    if len(direct_edges) != 85 or len({(edge.source, edge.target) for edge in direct_edges}) != 67:
        raise GenerationError("private direct co-route constraint census drift")
    for edge in direct_edges:
        if route[edge.source] != route[edge.target]:
            raise GenerationError(
                "direct reverse dependent must co-route with its private seed: "
                f"{edge.source} -> {edge.target}"
            )


def destination_dag(
    route_rows: list[dict[str, str]], edges: list[Edge]
) -> list[tuple[str, str, int, int]]:
    destination = {
        row["baseline_declaration_name"]: (
            row["baseline_owner_module"]
            if row["destination_module"] == "-"
            else row["destination_module"]
        )
        for row in route_rows
    }
    counts: dict[tuple[str, str], Counter[str]] = defaultdict(Counter)
    for edge in edges:
        source = destination.get(edge.source)
        target = destination.get(edge.target)
        if source is not None and target is not None and source != target:
            counts[(source, target)][edge.kind] += 1
    rows = [
        (source, target, kinds["signature"], kinds["body"])
        for (source, target), kinds in sorted(counts.items())
    ]
    nodes = set(destination.values())
    outgoing: dict[str, set[str]] = defaultdict(set)
    indegree = Counter({node: 0 for node in nodes})
    for source, target, _signature, _body in rows:
        if target not in outgoing[source]:
            outgoing[source].add(target)
            indegree[target] += 1
    queue = deque(sorted(node for node in nodes if indegree[node] == 0))
    visited = 0
    while queue:
        node = queue.popleft()
        visited += 1
        for target in sorted(outgoing.get(node, ())):
            indegree[target] -= 1
            if indegree[target] == 0:
                queue.append(target)
    if visited != len(nodes):
        raise GenerationError("fresh R07 destination graph contains a cycle")
    actual_edges = {
        (source, target): (signature, body)
        for source, target, signature, body in rows
    }
    for edge, expected_counts in EXACT_DAG_EDGES.items():
        if actual_edges.get(edge) != expected_counts:
            raise GenerationError(
                f"reconciled destination DAG edge {edge} must be {expected_counts}, "
                f"found {actual_edges.get(edge)}"
            )
    actual_real = {
        edge: counts
        for edge, counts in actual_edges.items()
        if edge[0].startswith(REAL_DESTINATION_PREFIX)
        and edge[1].startswith(REAL_DESTINATION_PREFIX)
    }
    if actual_real != REAL_DAG_EDGES:
        raise GenerationError(
            "corrected RealMatrixBridge destination DAG must equal the exact 20-row 27/109 review"
        )
    if len(rows) != 30:
        raise GenerationError(f"full selected destination DAG must contain exactly 30 rows, found {len(rows)}")
    if (
        sum(signature for _source, _target, signature, _body in rows),
        sum(body for _source, _target, _signature, body in rows),
    ) != (31, 136):
        raise GenerationError("full selected destination DAG must total exactly 31 signature / 136 body edges")
    for (source, target), counts_by_kind in actual_edges.items():
        if source not in SOURCE_DESTINATIONS and target in SOURCE_DESTINATIONS:
            raise GenerationError(
                f"reusable/internal destination imports Source via typed edge: {source} -> {target}"
            )
    return rows


def minimum_test_plan(
    selector: list[dict[str, str]],
    route_rows: list[dict[str, str]],
    consumers: list[tuple[str, str, str, str, str]],
    imports: dict[str, set[str]],
    declarations: list[Declaration],
    edges: list[Edge],
) -> list[tuple[str, str, str, str, str, str]]:
    destinations = sorted(
        {
            row["destination_module"]
            for row in route_rows
            if row["destination_module"] != "-"
        }
    )
    outside = sorted({row[0] for row in consumers if row[2] == "outside"})
    public_by_owner: dict[str, list[str]] = defaultdict(list)
    public_by_destination: dict[str, list[str]] = defaultdict(list)
    for row in route_rows:
        if row["visibility"] != "public":
            continue
        public_by_owner[row["baseline_owner_module"]].append(
            row["baseline_declaration_name"]
        )
        public_by_destination[row["destination_module"]].append(
            row["baseline_declaration_name"]
        )
    consumer_retargets: dict[str, list[dict[str, str]]] = defaultdict(list)
    for consumer, _path, scope, old_import, new_import in consumers:
        if scope == "outside":
            consumer_retargets[consumer].append(
                {"new_import": new_import, "old_import": old_import}
            )

    selected_modules = {row["module"] for row in selector}
    route_by_name = {
        row["baseline_declaration_name"]: row["destination_module"]
        for row in route_rows
    }
    visibility_by_name = {
        row["baseline_declaration_name"]: row["visibility"] for row in route_rows
    }
    declaration_owner = {declaration.name: declaration.owner for declaration in declarations}
    consumer_path = {
        consumer: path
        for consumer, path, scope, _old_import, _new_import in consumers
        if scope == "outside"
    }
    direct_names: dict[str, set[str]] = defaultdict(set)
    direct_counts: dict[str, dict[str, Counter[str]]] = defaultdict(
        lambda: defaultdict(Counter)
    )
    for edge in edges:
        consumer = declaration_owner.get(edge.source)
        destination = route_by_name.get(edge.target)
        if consumer not in consumer_path or destination is None:
            continue
        if visibility_by_name[edge.target] != "public":
            raise GenerationError(
                f"external consumer {consumer} depends on private selected declaration "
                f"{edge.target}"
            )
        direct_names[consumer].add(edge.target)
        direct_counts[consumer][destination][edge.kind] += 1

    import r07_shared_postimages as shared_postimages

    for consumer, path in sorted(consumer_path.items()):
        transform = shared_postimages.OUTSIDE_CONSUMER_TRANSFORMS[path]
        if transform.witnesses is None:
            continue
        actual = {
            destination: (counts["signature"], counts["body"])
            for destination, counts in direct_counts[consumer].items()
        }
        if actual != dict(transform.witnesses):
            raise GenerationError(
                f"{consumer}: direct declaration-use witnesses {actual} differ from "
                f"R0011 transform review {dict(transform.witnesses)}"
            )

    aggregate_consumers = {
        "NumStability.Algorithms",
        "NumStability.Analysis",
        "NumStability.Analysis.CStarMatrices.Basic.All",
        "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.All",
    }
    witnessed_consumers = {
        consumer
        for consumer, path in consumer_path.items()
        if consumer not in aggregate_consumers
        and shared_postimages.OUTSIDE_CONSUMER_TRANSFORMS[path].witnesses is not None
    }
    compile_only_consumers = set(consumer_path) - aggregate_consumers - witnessed_consumers
    if (
        len(aggregate_consumers),
        len(witnessed_consumers),
        len(compile_only_consumers),
    ) != (4, 12, 8):
        raise GenerationError(
            "external consumer test partition must be exactly 4 aggregate / "
            "12 direct-use / 8 compile-only consumers"
        )
    unexpected_compile_uses = {
        consumer: sorted(direct_names[consumer])
        for consumer in sorted(compile_only_consumers)
        if direct_names[consumer]
    }
    if unexpected_compile_uses:
        raise GenerationError(
            "compile-only consumers unexpectedly use selected public declarations: "
            f"{unexpected_compile_uses}"
        )

    def historical_public_frontier(consumer: str) -> list[str]:
        reached: set[str] = set()
        queue = deque([consumer])
        while queue:
            module = queue.popleft()
            if module in reached:
                continue
            reached.add(module)
            queue.extend(sorted(imports.get(module, ())))
        owners = reached & selected_modules
        return sorted(
            declaration
            for owner in owners
            for declaration in public_by_owner[owner]
        )
    rows: list[tuple[str, str, str, str, str, str]] = []
    for selected in selector:
        leaf = selected["module"].replace(".", "_")
        private_only_owner = selected["module"] in PRIVATE_ONLY_INTERNAL_ROUTES
        rows.append(
            (
                "old_only",
                f"NumStabilityTest/Reorganization/R07/OldOnly/{leaf}.lean",
                selected["module"],
                (
                    "no public declaration; compile/import witness for the unchanged "
                    "historical import surface"
                    if private_only_owner
                    else _semicolon(sorted(public_by_owner[selected["module"]]))
                    if public_by_owner[selected["module"]]
                    else "no owner-defined public declaration; compile/import witness"
                ),
                ";".join(sorted(NEW_DECLARATION_DESTINATIONS)),
                (
                    "isolated historical import remains declaration-free and does not "
                    "re-export the private-only R07 destination"
                    if private_only_owner
                    else "isolated historical import preserves the exact supported declaration surface"
                ),
            )
        )
    for destination in destinations:
        leaf = destination.replace(".", "_")
        internal_destination = destination in INTERNAL_DESTINATIONS
        rows.append(
            (
                "canonical_only",
                f"NumStabilityTest/Reorganization/R07/CanonicalOnly/{leaf}.lean",
                destination,
                (
                    "direct compile/import witness for the private source command; exact "
                    "normalized name is checked by PrivateNormalization"
                    if internal_destination
                    else _semicolon(sorted(public_by_destination[destination]))
                ),
                ";".join(sorted({row["module"] for row in selector})),
                (
                    "isolated canonical import builds the internal leaf without advertising "
                    "it through a public aggregate or compatibility wrapper"
                    if internal_destination
                    else "isolated canonical import checks representative routed declarations"
                ),
            )
        )
    for consumer in outside:
        leaf = consumer.replace(".", "_")
        witnesses = (
            historical_public_frontier(consumer)
            if consumer in aggregate_consumers
            else sorted(direct_names[consumer])
        )
        retargets = sorted(
            (
                f"{row['old_import']}->{row['new_import']}"
                for row in consumer_retargets[consumer]
            )
        )
        rows.append(
            (
                "consumer",
                f"NumStabilityTest/Reorganization/R07/Consumer/{leaf}.lean",
                consumer,
                (
                    _semicolon(witnesses)
                    if witnesses
                    else "no selected-owner public declaration; compile/import witness"
                ),
                "-",
                (
                    f"imports only {consumer} and checks its exact {len(witnesses)}-declaration "
                    f"{'historical R07 aggregate frontier' if consumer in aggregate_consumers else 'direct format-2 use frontier'} "
                    f"after {';'.join(retargets)}"
                ),
            )
        )
    root_witness_counts = {
        consumer: len(historical_public_frontier(consumer))
        for consumer in ("NumStability.Algorithms", "NumStability.Analysis")
    }
    if root_witness_counts != {
        "NumStability.Algorithms": EXPECTED_PUBLIC_DECLARATIONS,
        "NumStability.Analysis": EXPECTED_PUBLIC_DECLARATIONS,
    }:
        raise GenerationError(
            f"root aggregate R07 declaration frontier drift: {root_witness_counts}"
        )
    if not all(historical_public_frontier(consumer) for consumer in aggregate_consumers):
        raise GenerationError("aggregate consumer declaration frontier unexpectedly empty")
    rows.extend(
        (
            (
                "private_normalization",
                "NumStabilityTest/Reorganization/R07/PrivateNormalization.lean",
                ";".join(sorted(NEW_DECLARATION_DESTINATIONS)),
                "all 44 private target names plus 77-row closure boundaries",
                "-",
                "all 44 private declarations replay under the complete normalization map",
            ),
            (
                "dependency_boundary",
                "NumStabilityTest/Reorganization/R07/ReusableSourceBoundary.lean",
                ";".join(sorted(NEW_DECLARATION_DESTINATIONS - SOURCE_DESTINATIONS)),
                "no reusable/internal import reaches Source",
                ";".join(sorted(SOURCE_DESTINATIONS)),
                "no reusable destination directly or transitively imports Source correspondence",
            ),
        )
    )
    isolated_test_modules = sorted(module_from_path(row[1]) for row in rows)
    rows.append(
        (
            "all",
            "NumStabilityTest/Reorganization/R07/All.lean",
            ";".join(isolated_test_modules),
            f"all {len(isolated_test_modules)} isolated test targets",
            ";".join(sorted(INTERNAL_DESTINATIONS)),
            "branch aggregate imports every isolated R07 test leaf",
        )
    )
    counts = Counter(row[0] for row in rows)
    if counts != Counter(
        {
            "all": 1,
            "canonical_only": len(NEW_DECLARATION_DESTINATIONS),
            "consumer": EXPECTED_EXTERNAL_CONSUMERS,
            "dependency_boundary": 1,
            "old_only": EXPECTED_OWNER_COUNT,
            "private_normalization": 1,
        }
    ):
        raise GenerationError(f"isolated test matrix coverage drift: {counts}")
    if len({row[1] for row in rows}) != len(rows):
        raise GenerationError("isolated test target paths collide")
    return sorted(rows)


def post_move_import_manifest(
    *,
    selector: list[dict[str, str]],
    inventory: list[dict[str, str]],
    destination_plan: list[dict[str, str]],
    wrapper_plan: list[dict[str, str]],
    declaration_plan: list[dict[str, str]],
    dag_rows: list[tuple[str, str, int, int]],
    tier_rows: list[tuple[str, str, str]],
    rendered: Any,
) -> list[tuple[str, str, int, str, str]]:
    """Freeze the exact imports for all 87 R07 batch modules.

    This is the B0008-compatible complete manifest: historical wrappers,
    worker-owned declaration leaves, and integrator-owned public umbrellas.
    """

    import r07_shared_postimages as shared_postimages

    selected = {row["module"] for row in selector}
    wrapper_by_owner = {row["owner_module"]: row for row in wrapper_plan}
    if set(wrapper_by_owner) != selected:
        raise GenerationError("post-move manifest wrapper owner set drift")
    preserved_by_owner = {
        owner: _unsemicolon(row["preserved_imports"])
        for owner, row in wrapper_by_owner.items()
    }
    inventory_tier = {row["module"]: row["current_tier"] for row in inventory}
    destination_tier = {row["module"]: row["tier"] for row in destination_plan}
    if set(destination_tier) != NEW_DECLARATION_DESTINATIONS:
        raise GenerationError("post-move manifest destination tier set drift")

    # The selected-owner expansion must be a DAG; otherwise an import frontier
    # could be truncated by traversal order and cease to be a complete proof.
    selected_edges = {
        owner: {module for module in imports if module in selected}
        for owner, imports in preserved_by_owner.items()
    }
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(owner: str) -> None:
        if owner in visiting:
            raise GenerationError(f"selected-owner import expansion contains a cycle at {owner}")
        if owner in visited:
            return
        visiting.add(owner)
        for imported in sorted(selected_edges[owner]):
            visit(imported)
        visiting.remove(owner)
        visited.add(owner)

    for owner in sorted(selected):
        visit(owner)

    contributors: dict[str, set[str]] = defaultdict(set)
    for row in declaration_plan:
        contributors[row["destination_module"]].add(row["baseline_owner_module"])
    dag_targets: dict[str, set[str]] = defaultdict(set)
    for source, target, _signature, _body in dag_rows:
        dag_targets[source].add(target)

    module_imports: dict[str, list[tuple[str, str]]] = {}
    module_roles: dict[str, str] = {}

    for owner in sorted(selected):
        row = wrapper_by_owner[owner]
        preserved = set(_unsemicolon(row["preserved_imports"]))
        appended = set(_unsemicolon(row["appended_imports"]))
        post = _unsemicolon(row["post_imports"])
        if set(post) != preserved | appended or preserved & appended:
            raise GenerationError(f"{owner}: wrapper import partition drift")
        entries: list[tuple[str, str]] = []
        for imported in post:
            provenance = (
                "c0005_direct"
                if imported in preserved
                else "produced_destination"
                if imported in appended
                else None
            )
            if provenance is None:
                raise GenerationError(f"{owner}: wrapper import lacks provenance: {imported}")
            entries.append((imported, provenance))
        module_imports[owner] = entries
        module_roles[owner] = "compatibility"

    for destination in sorted(NEW_DECLARATION_DESTINATIONS):
        provenance_by_import: dict[str, set[str]] = defaultdict(set)

        def expand(imported: str, depth: int, stack: tuple[str, ...]) -> None:
            if imported in selected:
                if imported in stack:
                    raise GenerationError(
                        "selected-owner recursive import expansion cycle: "
                        + " -> ".join((*stack, imported))
                    )
                for nested in preserved_by_owner[imported]:
                    expand(nested, depth + 1, (*stack, imported))
                return
            if imported == destination:
                raise GenerationError(f"{destination}: destination would import itself")
            if imported.startswith("NumStability."):
                tier = inventory_tier.get(imported)
                if tier is None:
                    raise GenerationError(
                        f"{destination}: terminal production import is absent from C0005 inventory: "
                        f"{imported}"
                    )
                if destination_tier[destination] != "source" and tier == "source":
                    return
                allowed_tiers = (
                    {"reusable", "source"}
                    if destination_tier[destination] == "source"
                    else {"reusable"}
                )
                if tier not in allowed_tiers:
                    raise GenerationError(
                        f"{destination}: terminal import {imported} has forbidden tier {tier}"
                    )
            provenance_by_import[imported].add(
                "c0005_direct" if depth == 0 else "c0005_expanded"
            )

        for owner in sorted(contributors[destination]):
            for imported in preserved_by_owner[owner]:
                expand(imported, 0, (owner,))
        for target in sorted(dag_targets[destination]):
            if target == destination:
                raise GenerationError(f"{destination}: destination DAG contains a self-edge")
            provenance_by_import[target].add("route_dag")
        module_imports[destination] = [
            (imported, "+".join(sorted(provenance_by_import[imported])))
            for imported in sorted(provenance_by_import)
        ]
        module_roles[destination] = "produced_destination"

    for path, expected_imports in sorted(shared_postimages.PUBLIC_UMBRELLAS.items()):
        module = module_from_path(path)
        payload = rendered.postimages[path]
        actual_imports = shared_postimages.extract_imports(path, payload)
        if actual_imports != expected_imports:
            raise GenerationError(f"{module}: rendered public umbrella import drift")
        module_imports[module] = [
            (imported, "produced_destination") for imported in actual_imports
        ]
        module_roles[module] = "aggregate"

    expected_modules = {row[0] for row in tier_rows}
    if set(module_imports) != expected_modules or len(expected_modules) != 87:
        raise GenerationError(
            "post-move manifest module set must equal the exact 87-row tier assignment"
        )
    rows: list[tuple[str, str, int, str, str]] = []
    for module in sorted(module_imports):
        seen: set[str] = set()
        for order, (imported, provenance) in enumerate(module_imports[module], 1):
            if imported in seen:
                raise GenerationError(f"{module}: duplicate post-move import {imported}")
            seen.add(imported)
            if imported in selected and module_roles[module] != "compatibility":
                raise GenerationError(
                    f"{module}: non-wrapper post-move import retains historical owner {imported}"
                )
            if (
                module_roles[module] == "aggregate"
                and imported in INTERNAL_DESTINATIONS
            ):
                raise GenerationError(f"{module}: public umbrella imports internal leaf {imported}")
            rows.append(
                (
                    module,
                    module_roles[module],
                    order,
                    f"import {imported}",
                    provenance,
                )
            )

    role_census = Counter(row[1] for row in rows)
    provenance_census = Counter((row[1], row[4]) for row in rows)
    if role_census != Counter(
        {"aggregate": 27, "compatibility": 292, "produced_destination": 441}
    ):
        raise GenerationError(f"post-move import role census drift: {role_census}")
    expected_provenance = Counter(
        {
            ("aggregate", "produced_destination"): 27,
            ("compatibility", "c0005_direct"): 264,
            ("compatibility", "produced_destination"): 28,
            ("produced_destination", "c0005_direct"): 119,
            ("produced_destination", "c0005_expanded"): 279,
            ("produced_destination", "c0005_direct+c0005_expanded"): 13,
            ("produced_destination", "route_dag"): 30,
        }
    )
    if provenance_census != expected_provenance:
        raise GenerationError(
            f"post-move import provenance census drift: {provenance_census}"
        )
    payload = tsv_bytes(POST_MOVE_IMPORT_MANIFEST_HEADER, rows)
    if len(rows) != EXPECTED_POST_MOVE_IMPORT_ROWS or sha256_bytes(payload) != (
        EXPECTED_POST_MOVE_IMPORT_SHA256
    ):
        raise GenerationError(
            "complete R07 post-move import manifest differs from the B0008-replayed "
            "87-module/760-row review"
        )
    return rows


def external_owner_supply(
    *,
    selector: list[dict[str, str]],
    inventory: list[dict[str, str]],
    declarations: list[Declaration],
    edges: list[Edge],
    declaration_plan: list[dict[str, str]],
    dag_rows: list[tuple[str, str, int, int]],
    manifest_rows: list[tuple[str, str, int, str, str]],
    base_imports: dict[str, set[str]],
    rendered: Any,
) -> list[tuple[str, str, int, int, int, str]]:
    """Prove every routed declaration's external production owner is supplied."""

    import r07_shared_postimages as shared_postimages

    selected = {row["module"] for row in selector}
    production = {row["module"] for row in inventory}
    declaration_owner = {declaration.name: declaration.owner for declaration in declarations}
    route = {
        row["baseline_declaration_name"]: row["destination_module"]
        for row in declaration_plan
    }
    if len(route) != EXPECTED_DECLARATIONS:
        raise GenerationError("external-owner supply route map must contain 194 declarations")

    grouped: dict[tuple[str, str], Counter[str]] = defaultdict(Counter)
    partition: Counter[tuple[str, str]] = Counter()
    for edge in edges:
        source_destination = route.get(edge.source)
        if source_destination is None:
            continue
        target_destination = route.get(edge.target)
        if target_destination is not None:
            relation = "same" if target_destination == source_destination else "cross"
            partition[(relation, edge.kind)] += 1
            continue
        target_owner = declaration_owner.get(edge.target)
        if target_owner is None:
            raise GenerationError(
                f"routed graph edge target lacks a declaration owner: {edge.target}"
            )
        if target_owner in selected or target_owner in NEW_DECLARATION_DESTINATIONS:
            raise GenerationError(
                f"unrouted selected/destination dependency in supply graph: {edge.target}"
            )
        if target_owner not in production:
            raise GenerationError(
                f"external dependency owner is absent from C0005 production inventory: "
                f"{target_owner}"
            )
        partition[("external", edge.kind)] += 1
        grouped[(source_destination, target_owner)][edge.kind] += 1

    expected_partition = Counter(
        {
            ("same", "signature"): 87,
            ("same", "body"): 250,
            ("cross", "signature"): 31,
            ("cross", "body"): 136,
            ("external", "signature"): 60,
            ("external", "body"): 125,
        }
    )
    if partition != expected_partition:
        raise GenerationError(f"routed outgoing-edge partition drift: {partition}")
    dag_counts = {
        (source, target): (signature, body)
        for source, target, signature, body in dag_rows
    }
    if (
        sum(value[0] for value in dag_counts.values()),
        sum(value[1] for value in dag_counts.values()),
    ) != (31, 136):
        raise GenerationError("external-owner supply DAG cross-edge reconciliation drift")

    imports_by_module: dict[str, set[str]] = {
        module: set(imported) for module, imported in base_imports.items()
    }
    manifest_imports: dict[str, set[str]] = defaultdict(set)
    for module, _role, _order, import_line, _provenance in manifest_rows:
        match = IMPORT_LINE.fullmatch(import_line)
        if match is None:
            raise GenerationError(f"post-move manifest import line is malformed: {import_line}")
        imported = match.group(1)
        if imported.startswith("NumStability."):
            manifest_imports[module].add(imported)
    imports_by_module.update(manifest_imports)
    for path, payload in rendered.postimages.items():
        if not path.startswith("NumStability/") or not path.endswith(".lean"):
            continue
        module = module_from_path(path)
        imports_by_module[module] = {
            imported
            for imported in shared_postimages.extract_imports(path, payload)
            if imported.startswith("NumStability.")
        }

    def reachable(start: str, target: str) -> bool:
        seen: set[str] = set()
        queue = deque(sorted(imports_by_module.get(start, ())))
        while queue:
            module = queue.popleft()
            if module == target:
                return True
            if module in seen:
                continue
            seen.add(module)
            queue.extend(sorted(imports_by_module.get(module, ())))
        return False

    rows: list[tuple[str, str, int, int, int, str]] = []
    for (destination, owner), counts in sorted(grouped.items()):
        direct = owner in manifest_imports[destination]
        if not direct and not reachable(destination, owner):
            raise GenerationError(
                f"{destination}: external owner is not supplied after R0011: {owner}"
            )
        rows.append(
            (
                destination,
                owner,
                counts["signature"],
                counts["body"],
                1 if direct else 0,
                "direct" if direct else "transitive",
            )
        )
    if (
        len(rows) != EXPECTED_EXTERNAL_OWNER_SUPPLY_ROWS
        or len({row[0] for row in rows}) != 14
        or len({row[1] for row in rows}) != 17
        or sum(row[2] for row in rows) != 60
        or sum(row[3] for row in rows) != 125
        or Counter(row[5] for row in rows) != Counter({"direct": 31})
    ):
        raise GenerationError("external-owner supply census must be exact 31/14/17/60/125")
    payload = tsv_bytes(EXTERNAL_OWNER_SUPPLY_HEADER, rows)
    if sha256_bytes(payload) != EXPECTED_EXTERNAL_OWNER_SUPPLY_SHA256:
        raise GenerationError("external-owner supply differs from exact reviewed 31-row map")
    return rows


def zero_context_patch(preimages: dict[str, bytes], postimages: dict[str, bytes]) -> bytes:
    if set(preimages) != set(postimages):
        raise GenerationError("request preimage/postimage path sets differ")
    chunks: list[bytes] = []
    for path in sorted(postimages):
        before = preimages[path]
        after = postimages[path]
        if before == after:
            raise GenerationError(f"R0011 transform is a no-op: {path}")
        old_oid = hashlib.sha1(f"blob {len(before)}\0".encode() + before).hexdigest()
        new_oid = hashlib.sha1(f"blob {len(after)}\0".encode() + after).hexdigest()
        chunks.append(f"diff --git a/{path} b/{path}\n".encode())
        chunks.append(f"index {old_oid}..{new_oid} 100644\n".encode())
        diff = difflib.unified_diff(
            before.decode("utf-8").splitlines(keepends=True),
            after.decode("utf-8").splitlines(keepends=True),
            fromfile=f"a/{path}",
            tofile=f"b/{path}",
            n=0,
            lineterm="\n",
        )
        chunks.append("".join(diff).encode())
    return b"".join(chunks)


def planned_control_schema(projection: Projection) -> dict[str, Any]:
    """Describe fixed planned-state identities and schemas without authority placeholders."""

    return {
        "authority": {
            "branch_operator_id": OPERATOR_ID,
            "branch_owner_id": OWNER_ID,
            "integration_lane_owner_id": OWNER_ID,
        },
        "base_checkpoint_id": BASE_CHECKPOINT_ID,
        "base_code_sha": BASE_CODE_SHA,
        "headers": {
            "consumers": CONSUMERS_HEADER,
            "declaration_routes": DECLARATION_ROUTES_HEADER,
            "destination_dag": DESTINATION_DAG_HEADER,
            "external_owner_supply": EXTERNAL_OWNER_SUPPLY_HEADER,
            "module_routes": MODULE_ROUTES_HEADER,
            "post_move_import_manifest": POST_MOVE_IMPORT_MANIFEST_HEADER,
            "private_closure": PRIVATE_CLOSURE_HEADER,
            "private_normalization": PRIVATE_NORMALIZATION_HEADER,
            "request_plan": REQUEST_PLAN_HEADER,
            "selector": SELECTOR_HEADER,
            "source_commands": SOURCE_COMMANDS_HEADER,
            "test_plan": TEST_PLAN_HEADER,
            "tier_assignments": TIER_ASSIGNMENTS_HEADER,
            "wrapper_plan": WRAPPER_PLAN_HEADER,
        },
        "ids": {
            "branch": BRANCH_ID,
            "milestone": MILESTONE_ID,
            "projection": PROJECTION_ID,
            "request": REQUEST_ID,
            "wave": WAVE_ID,
        },
        "lifecycle": {
            "branch_status": "planned",
            "milestone_status": "ready",
            "projection_status": "active",
            "request_status": "active",
        },
        "projection_counts": projection.counts,
    }


def materialize_reviewed_controls(
    *,
    selector: list[dict[str, str]],
    inventory: list[dict[str, str]],
    declarations: list[Declaration],
    edges: list[Edge],
    projection: Projection,
    destination_plan: list[dict[str, str]],
    module_plan: list[dict[str, str]],
    wrapper_plan: list[dict[str, str]],
    source_commands: list[dict[str, str]],
    declaration_plan: list[dict[str, str]],
    consumers: list[tuple[str, str, str, str, str]],
    imports: dict[str, set[str]],
    consumer_counts: dict[str, int],
    overlaps: dict[str, Any],
    destination_facts: dict[str, Any],
    compatibility_postimage: Path,
    review: dict[str, Any],
) -> list[dict[str, Any]]:
    """Materialize the reviewed planned state only; activation remains separate."""

    import r07_shared_postimages as shared_postimages

    if review.get("decision") != "approved" or review.get("reviewer_id") != OWNER_ID:
        raise GenerationError("planned controls require exact primary-human review metadata")
    if PRIMARY_REVIEW.resolve() != Path(review["_path"]).resolve():
        raise GenerationError(f"primary review must use fixed path {PRIMARY_REVIEW}")

    rendered = shared_postimages.render_artifacts(
        compatibility_postimage.read_bytes(), verify_replay=True
    )
    request_paths = sorted(rendered.postimages)
    request_path_set = set(request_paths)
    planned_phase = planned_phase_postimage(request_path_set)
    scope_rows = scope_rule_rows(
        selector, inventory, destination_facts, planned_phase, request_path_set
    )
    normalization_rows = private_normalization(declaration_plan, declarations)
    closure_rows = private_closure(
        declaration_plan,
        declarations,
        edges,
        {row["module"] for row in selector},
    )
    dag_rows = destination_dag(declaration_plan, edges)
    test_rows = minimum_test_plan(
        selector, declaration_plan, consumers, imports, declarations, edges
    )
    tier_rows = tier_assignment_rows(selector, destination_plan)
    post_move_rows = post_move_import_manifest(
        selector=selector,
        inventory=inventory,
        destination_plan=destination_plan,
        wrapper_plan=wrapper_plan,
        declaration_plan=declaration_plan,
        dag_rows=dag_rows,
        tier_rows=tier_rows,
        rendered=rendered,
    )
    external_supply_rows = external_owner_supply(
        selector=selector,
        inventory=inventory,
        declarations=declarations,
        edges=edges,
        declaration_plan=declaration_plan,
        dag_rows=dag_rows,
        manifest_rows=post_move_rows,
        base_imports=imports,
        rendered=rendered,
    )

    selected_modules = {row["module"] for row in selector}
    selected_inventory = [
        row for row in inventory if row["module"] in selected_modules
    ]
    selector_payload = tsv_bytes(
        SELECTOR_HEADER, ((row["module"], row["path"]) for row in selector)
    )
    inventory_payload = tsv_bytes(
        INVENTORY_HEADER,
        ([row[column] for column in INVENTORY_HEADER] for row in selected_inventory),
    )

    branch_payloads: dict[Path, bytes] = {
        BRANCHES / f"{BRANCH_ID}-inventory.tsv": inventory_payload,
        BRANCHES / f"{BRANCH_ID}-destinations.tsv": tsv_bytes(
            DESTINATION_PLAN_HEADER,
            ([row[column] for column in DESTINATION_PLAN_HEADER] for row in destination_plan),
        ),
        BRANCHES / f"{BRANCH_ID}-module-routes.tsv": tsv_bytes(
            MODULE_ROUTES_HEADER,
            ([row[column] for column in MODULE_ROUTES_HEADER] for row in module_plan),
        ),
        BRANCHES / f"{BRANCH_ID}-wrapper-imports.tsv": tsv_bytes(
            WRAPPER_PLAN_HEADER,
            ([row[column] for column in WRAPPER_PLAN_HEADER] for row in wrapper_plan),
        ),
        BRANCHES / f"{BRANCH_ID}-source-commands.tsv": tsv_bytes(
            SOURCE_COMMANDS_HEADER,
            ([row[column] for column in SOURCE_COMMANDS_HEADER] for row in source_commands),
        ),
        BRANCHES / f"{BRANCH_ID}-declaration-routes.tsv": tsv_bytes(
            DECLARATION_ROUTES_HEADER,
            ([row[column] for column in DECLARATION_ROUTES_HEADER] for row in declaration_plan),
        ),
        BRANCHES / f"{BRANCH_ID}-private-normalization.tsv": tsv_bytes(
            PRIVATE_NORMALIZATION_HEADER, normalization_rows
        ),
        BRANCHES / f"{BRANCH_ID}-private-closure.tsv": tsv_bytes(
            PRIVATE_CLOSURE_HEADER, closure_rows
        ),
        BRANCHES / f"{BRANCH_ID}-destination-dag.tsv": tsv_bytes(
            DESTINATION_DAG_HEADER, dag_rows
        ),
        BRANCHES / f"{BRANCH_ID}-external-owner-supply.tsv": tsv_bytes(
            EXTERNAL_OWNER_SUPPLY_HEADER, external_supply_rows
        ),
        BRANCHES / f"{BRANCH_ID}-consumers.tsv": tsv_bytes(CONSUMERS_HEADER, consumers),
        BRANCHES / f"{BRANCH_ID}-test-plan.tsv": tsv_bytes(TEST_PLAN_HEADER, test_rows),
        BRANCHES / f"{BRANCH_ID}-tier-assignments.tsv": tsv_bytes(
            TIER_ASSIGNMENTS_HEADER, tier_rows
        ),
        BRANCHES / f"{BRANCH_ID}-scope-rules.tsv": tsv_bytes(
            SCOPE_RULES_HEADER, scope_rows
        ),
        BRANCHES / f"{BRANCH_ID}-overlap-review.json": (
            DERIVED_REVIEW_DRAFT_PATHS["overlap_review"].read_bytes()
        ),
        BRANCHES / f"{BRANCH_ID}-post-move-import-manifest.tsv": tsv_bytes(
            POST_MOVE_IMPORT_MANIFEST_HEADER, post_move_rows
        ),
        BRANCHES / f"{BRANCH_ID}-R0011-import-manifest.tsv": rendered.import_manifest,
        BRANCHES / f"{BRANCH_ID}-destination-modules.txt": line_list_bytes(
            sorted(NEW_DECLARATION_DESTINATIONS)
        ),
        BRANCHES / f"{BRANCH_ID}-destination-prefixes.txt": line_list_bytes(
            destination_facts["prefixes"]
        ),
        BRANCHES / f"{BRANCH_ID}-branch-prefixes.txt": line_list_bytes(
            destination_facts["branch_prefixes"]
        ),
        BRANCHES / f"{BRANCH_ID}-test-modules.txt": line_list_bytes(
            sorted(module_from_path(row[1]) for row in test_rows)
        ),
        BRANCHES / f"{BRANCH_ID}-shared-request-paths.txt": line_list_bytes(request_paths),
    }

    projection_path = PROJECTIONS / f"{PROJECTION_ID}.tsv.gz"
    projection_record_path = PROJECTIONS / f"{PROJECTION_ID}.json"
    private_map_path = BRANCHES / f"{BRANCH_ID}-private-normalization.tsv"
    projection_arguments = sorted(
        [
            "--candidate=<candidate-format2.tsv>",
            f"--private-map={repo_relative(private_map_path)}",
            f"--private-map-sha256={sha256_bytes(branch_payloads[private_map_path])}",
            f"--projection={repo_relative(projection_path)}",
            f"--projection-sha256={sha256_bytes(projection.compressed)}",
        ]
        + [
            f"--allow-module={module}"
            for module in sorted(selected_modules | NEW_DECLARATION_DESTINATIONS)
        ]
    )
    projection_record = {
        "base_checkpoint_id": BASE_CHECKPOINT_ID,
        "checker": {
            "arguments": projection_arguments,
            "artifact": {
                "path": repo_relative(PROJECTION_CHECKER),
                "sha256": PROJECTION_CHECKER_SHA256,
            },
        },
        "combined_baseline": {
            "path": repo_relative(BASELINE),
            "sha256": BASELINE_SHA256,
        },
        "expected_counts": projection.counts,
        "phase_id": PHASE_ID,
        "projection_graph": {
            "path": repo_relative(projection_path),
            "sha256": sha256_bytes(projection.compressed),
        },
        "projection_id": PROJECTION_ID,
        "record_kind": "baseline_projection",
        "schema_version": 1,
        "selector": {
            "artifact": {
                "path": repo_relative(SELECTORS / f"{WAVE_ID}.tsv"),
                "sha256": sha256_bytes(selector_payload),
            },
            "kind": "module_path_tsv",
        },
        "status": "active",
        "superseded_by": None,
        "wave_id": WAVE_ID,
    }
    projection_record_payload = canonical_json(projection_record)

    request_patch_path = REQUESTS / f"{REQUEST_ID}.patch"
    request_ledger_path = REQUESTS / f"{REQUEST_ID}-postimages.tsv"
    request_plan_path = REQUESTS / f"{REQUEST_ID}-request-plan.tsv"
    request_import_path = REQUESTS / f"{REQUEST_ID}-import-manifest.tsv"
    request_record_path = REQUESTS / f"{REQUEST_ID}.json"
    request_record = {
        "blocks": [WAVE_ID],
        "created_at": review["reviewed_at"],
        "depends_on": [],
        "lane_id": LANE_ID,
        "patch": {
            "path": repo_relative(request_patch_path),
            "sha256": sha256_bytes(rendered.patch),
        },
        "paths": request_paths,
        "phase_id": PHASE_ID,
        "preimage_blobs": [
            {
                "blob_oid": shared_postimages.BASE_EXISTING_OIDS.get(path),
                "path": path,
            }
            for path in request_paths
        ],
        "rationale": (
            "Primary-human reviewed exact-C0005 R07 common-base postimages: 34 existing "
            "shared files and 12 new declaration-free public umbrellas. The compatibility "
            "postimage preserves all existing rows byte-for-byte, adds exactly 45 public "
            "historical frontiers, and advertises none of the three internal leaves. "
            f"Sorted path-list SHA-256 {shared_postimages.path_list_sha256(request_paths)}; "
            f"replayed forward tree {rendered.forward_tree}."
        ),
        "record_kind": "shared_file_request",
        "request_id": REQUEST_ID,
        "requester_id": OWNER_ID,
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
        "target_base_sha": BASE_CODE_SHA,
        "target_checkpoint_id": BASE_CHECKPOINT_ID,
        "valid_through_checkpoint_id": BASE_CHECKPOINT_ID,
        "wave_id": WAVE_ID,
    }
    request_record_payload = canonical_json(request_record)

    payloads: dict[Path, bytes] = {
        **branch_payloads,
        SELECTORS / f"{WAVE_ID}.tsv": selector_payload,
        projection_path: projection.compressed,
        projection_record_path: projection_record_payload,
        request_patch_path: rendered.patch,
        request_ledger_path: rendered.postimage_ledger,
        request_plan_path: rendered.request_plan,
        request_import_path: rendered.import_manifest,
        request_record_path: request_record_payload,
        PHASE / "phase.json": pretty_json(planned_phase),
    }

    evidence_paths = [
        CHECKPOINT,
        BASELINE,
        BASELINE_SUMMARY,
        INVENTORY,
        CI_ATTESTATION,
        PRIMARY_REVIEW,
        *REVIEW_DRAFT_PATHS.values(),
        *DERIVED_REVIEW_DRAFT_PATHS.values(),
        COMPATIBILITY_DRAFT,
        Path(__file__).resolve(),
        SHARED_POSTIMAGE_RENDERER,
    ]
    evidence: dict[str, dict[str, str]] = {}
    for path in evidence_paths:
        evidence[repo_relative(path)] = {
            "path": repo_relative(path),
            "sha256": sha256_path(path),
        }
    for path, payload in payloads.items():
        if path == PHASE / "phase.json":
            continue
        evidence[repo_relative(path)] = artifact_for_payload(path, payload)

    forbidden_paths = [
        {"match": match, "path": path}
        for scope, match, path, _authority, _rationale in scope_rows
        if scope == "worker_forbidden"
    ]
    branch_record = {
        "base_checkpoint_id": BASE_CHECKPOINT_ID,
        "base_sha": BASE_CODE_SHA,
        "baseline_projection_id": PROJECTION_ID,
        "branch_id": BRANCH_ID,
        "branch_name": BRANCH_NAME,
        "delivery": {"commit_sha": None, "report": None, "scope_evidence": None},
        "destination_prefixes": [
            {"match": "prefix", "path": path}
            for path in destination_facts["branch_prefixes"]
        ],
        "forbidden_paths": forbidden_paths,
        "integration": {
            "accepted_checkpoint_id": None,
            "accepted_sha": None,
            "method": None,
        },
        "lane_id": LANE_ID,
        "operator_ids": [OPERATOR_ID],
        "owned_paths": [
            {"match": "exact", "path": row["path"]}
            for row in sorted(selector, key=lambda item: item["path"])
        ],
        "owner_id": OWNER_ID,
        "phase_id": PHASE_ID,
        "record_kind": "phase_branch",
        "refresh": {
            "decision": "current",
            "evidence": [evidence[path] for path in sorted(evidence)],
            "reviewed_checkpoint_id": BASE_CHECKPOINT_ID,
        },
        "retirement": {
            "ancestry_checkpoint_id": None,
            "remote_ref": f"refs/heads/{BRANCH_NAME}",
            "retired_at": None,
            "retired_by": None,
            "rule": "delivery_ancestor_of_green_checkpoint",
            "status": "not_due",
        },
        "schema_version": 1,
        "shared_request_ids": [REQUEST_ID],
        "status": "planned",
        "wave_id": WAVE_ID,
    }
    branch_record_path = BRANCHES / f"{BRANCH_ID}.json"
    payloads[branch_record_path] = canonical_json(branch_record)

    contract_artifacts: dict[str, dict[str, str]] = {}
    for path in [*evidence_paths, *payloads]:
        relative = repo_relative(path)
        payload = payloads.get(path)
        contract_artifacts[relative] = (
            artifact_for_payload(path, payload)
            if payload is not None
            else {"path": relative, "sha256": sha256_path(path)}
        )
    forbidden_counts = Counter(row["match"] for row in forbidden_paths)
    visibility_counts = Counter(row["visibility"] for row in declaration_plan)
    contract_counts = {
        "artifact_rows": len(contract_artifacts),
        "branch_prefixes": len(destination_facts["branch_prefixes"]),
        "consumer_edges": consumer_counts["total_import_edges"],
        "declarations": len(declaration_plan),
        "destination_dag_body_edges": sum(row[3] for row in dag_rows),
        "destination_dag_rows": len(dag_rows),
        "destination_dag_signature_edges": sum(row[2] for row in dag_rows),
        "destinations": len(destination_plan),
        "external_consumers": consumer_counts["external_consumers"],
        "external_import_edges": consumer_counts["external_import_edges"],
        "external_owner_supply_rows": len(external_supply_rows),
        "forbidden_exact": forbidden_counts["exact"],
        "forbidden_prefix": forbidden_counts["prefix"],
        "internal_import_edges": consumer_counts["internal_import_edges"],
        "module_routes": len(module_plan),
        "owners": len(selector),
        "post_move_import_rows": len(post_move_rows),
        "private_closure": len(closure_rows),
        "private_declarations": visibility_counts["private"],
        "private_normalization": len(normalization_rows),
        "public_declarations": visibility_counts["public"],
        "request_paths": len(request_paths),
        "scope_rows": len(scope_rows),
        "source_commands": len(source_commands),
        "test_rows": len(test_rows),
        "tier_rows": len(tier_rows),
        "wrapper_rows": len(wrapper_plan),
    }
    expected_contract_counts = {
        "artifact_rows": 62,
        "branch_prefixes": 17,
        "consumer_edges": 121,
        "declarations": 194,
        "destination_dag_body_edges": 136,
        "destination_dag_rows": 30,
        "destination_dag_signature_edges": 31,
        "destinations": 30,
        "external_consumers": 24,
        "external_import_edges": 73,
        "external_owner_supply_rows": 31,
        "forbidden_exact": 2804,
        "forbidden_prefix": 6,
        "internal_import_edges": 48,
        "module_routes": 45,
        "owners": 45,
        "post_move_import_rows": 760,
        "private_closure": 77,
        "private_declarations": 44,
        "private_normalization": 44,
        "public_declarations": 150,
        "request_paths": 46,
        "scope_rows": 2918,
        "source_commands": 194,
        "test_rows": 102,
        "tier_rows": 87,
        "wrapper_rows": 45,
    }
    if contract_counts != expected_contract_counts:
        raise GenerationError(
            f"R07 planned-control count contract drift: {contract_counts} != "
            f"{expected_contract_counts}"
        )
    contract = {
        "accepted_control_sha": ACCEPTED_CONTROL_SHA,
        "artifact_hash_scope": {
            "lifecycle_mutable_paths": sorted(
                [
                    repo_relative(PHASE / "phase.json"),
                    repo_relative(branch_record_path),
                    repo_relative(projection_record_path),
                    repo_relative(request_record_path),
                ]
            ),
            "mode": "planned_state_only",
        },
        "artifacts": [contract_artifacts[path] for path in sorted(contract_artifacts)],
        "base_checkpoint_id": BASE_CHECKPOINT_ID,
        "base_code_sha": BASE_CODE_SHA,
        "branch_id": BRANCH_ID,
        "counts": contract_counts,
        "headers": {
            "consumers": CONSUMERS_HEADER,
            "declaration_routes": DECLARATION_ROUTES_HEADER,
            "destination_dag": DESTINATION_DAG_HEADER,
            "external_owner_supply": EXTERNAL_OWNER_SUPPLY_HEADER,
            "module_routes": MODULE_ROUTES_HEADER,
            "post_move_import_manifest": POST_MOVE_IMPORT_MANIFEST_HEADER,
            "private_closure": PRIVATE_CLOSURE_HEADER,
            "private_normalization": PRIVATE_NORMALIZATION_HEADER,
            "request_plan": REQUEST_PLAN_HEADER,
            "selector": SELECTOR_HEADER,
            "source_commands": SOURCE_COMMANDS_HEADER,
            "test_plan": TEST_PLAN_HEADER,
            "tier_assignments": TIER_ASSIGNMENTS_HEADER,
            "wrapper_plan": WRAPPER_PLAN_HEADER,
        },
        "lifecycle": {
            "branch_status": "planned",
            "milestone_status": "ready",
            "projection_status": "active",
            "request_status": "active",
        },
        "phase_id": PHASE_ID,
        "projection_id": PROJECTION_ID,
        "projected_remaining_queue": {"R09": 72, "R10": 18},
        "record_kind": "r07_planned_control_contract",
        "request_id": REQUEST_ID,
        "review_id": review["review_id"],
        "reviewed_at": review["reviewed_at"],
        "schema_version": 1,
        "wave_id": WAVE_ID,
    }
    payloads[PLANNED_CONTROL_CONTRACT] = canonical_json(contract)
    return write_materialized_payloads(payloads)


def self_test(graph: Path | None = None, ilean_root: Path | None = None) -> None:
    payload = b"format\t2\ndeclaration\tA.a\tA\ttheorem\tprivate\n"
    if deterministic_gzip(payload) != deterministic_gzip(payload):
        raise GenerationError("deterministic gzip self-test failed")
    if gzip.decompress(deterministic_gzip(payload)) != payload:
        raise GenerationError("gzip round-trip self-test failed")
    patch = zero_context_patch({"A": b"x\n"}, {"A": b"y\n"})
    if b"@@ -1 +1 @@" not in patch or b"-x\n+y\n" not in patch:
        raise GenerationError("zero-context patch self-test failed")
    unicode_lines = [
        "private notation \"𝔼\" => EuclideanSpace ℂ (Fin n)".encode("utf-8"),
        "private notation \"↑ₐ\" => algebraMap R A".encode("utf-8"),
        "theorem curve_hasDerivAt (θ : ℝ) : θ ≤ θ := le_rfl".encode("utf-8"),
    ]
    unicode_payload = b"\n".join(unicode_lines) + b"\n"
    for line_number, line in enumerate(unicode_lines):
        decoded_line = line.decode("utf-8")
        utf16_length = len(decoded_line.encode("utf-16-le")) // 2
        span = (
            line_number,
            0,
            line_number,
            utf16_length,
            line_number,
            0,
            line_number,
            utf16_length,
        )
        if source_command_bytes(unicode_payload, span) != line:
            raise GenerationError("UTF-16-column to UTF-8-byte extraction self-test failed")
    non_bmp_line = unicode_lines[0].decode("utf-8")
    non_bmp_index = non_bmp_line.index("𝔼")
    split_column = len(non_bmp_line[:non_bmp_index].encode("utf-16-le")) // 2 + 1
    caught = False
    try:
        source_command_bytes(
            unicode_payload,
            (0, 0, 0, split_column, 0, 0, 0, split_column),
        )
    except GenerationError:
        caught = True
    if not caught:
        raise GenerationError("UTF-16 surrogate split-column mutation self-test failed")
    caught = False
    try:
        reject_historical_input(Path("docs/architecture/phases/2026-08-repository-reorganization/W06/x"))
    except GenerationError:
        caught = True
    if not caught:
        raise GenerationError("historical-input rejection self-test failed")
    blackboard = "term\U0001D53C"
    if ord(blackboard[-1]) != 0x1D53C or any(
        "term\u1d53" in name for name in INTERNAL_PRIVATE_ROUTES
    ):
        raise GenerationError("blackboard-bold E codepoint self-test failed")
    pseudospectral = (
        "_private.NumStability.Analysis.PseudospectralResolvent.0.NumStability."
        "\u00abterm\u2191\u2090\u00bb"
    )
    if INTERNAL_PRIVATE_ROUTES.get(pseudospectral) != (
        "NumStability.Analysis.LinearOperators.Pseudospectra.Resolvent.Internal.ScalarNotation"
    ):
        raise GenerationError("pseudospectral UTF-8 private route self-test failed")
    if len(INTERNAL_PRIVATE_ROUTES) != 3 or len(set(INTERNAL_PRIVATE_ROUTES.values())) != 3:
        raise GenerationError("internal private route uniqueness self-test failed")
    macro_name, macro_root = next(iter(MACRO_ILEAN_ROOTS.items()))
    if authoritative_ilean_root(
        macro_name, {macro_root: MACRO_ILEAN_SPANS[macro_name]}
    ) != macro_root:
        raise GenerationError("macro-generated .ilean root positive self-test failed")
    caught = False
    try:
        authoritative_ilean_root(
            macro_name, {macro_root: (0, 0, 1, 0, 0, 0, 1, 0)}
        )
    except GenerationError:
        caught = True
    if not caught:
        raise GenerationError("macro-generated .ilean span mutation self-test failed")
    validate_ci_attestation_payload(load_json(CI_ATTESTATION))
    mutated_ci = json.loads(json.dumps(load_json(CI_ATTESTATION)))
    mutated_ci["job"]["steps"] = []
    caught = False
    try:
        validate_ci_attestation_payload(mutated_ci)
    except GenerationError:
        caught = True
    if not caught:
        raise GenerationError("empty CI step list adversarial self-test failed")
    validate_internal_wrapper_imports({})
    mutated_internal_imports: dict[str, frozenset[str]] = {}
    mutated_internal_imports["NumStability.Analysis.BergerGeneral"] = frozenset(
        {next(iter(INTERNAL_DESTINATIONS))}
    )
    caught = False
    try:
        validate_internal_wrapper_imports(mutated_internal_imports)
    except GenerationError:
        caught = True
    if not caught:
        raise GenerationError("internal wrapper-boundary adversarial self-test failed")
    caught = False
    try:
        require_exact_keys({"a": 1, "extra": 2}, {"a"}, "adversarial")
    except GenerationError:
        caught = True
    if not caught:
        raise GenerationError("exact-key adversarial self-test failed")
    case_sensitive = {
        "NumStability.SpijkerPlanarAnalyticBridge": "external-structure",
        "NumStability.spijkerPlanarAnalyticBridge": "new-definition",
    }
    if len(case_sensitive) != 2 or len({key.casefold() for key in case_sensitive}) != 1:
        raise GenerationError("case-sensitive declaration-identity self-test failed")
    if (
        validate_module_classification("zero", "classify_compatibility", 0, ["-"])
        != "classify_compatibility"
        or validate_module_classification("one", "relocate_whole", 1, ["A"])
        != "relocate_whole"
        or validate_module_classification("many", "relocate_split", 2, ["A", "B"])
        != "relocate_split"
    ):
        raise GenerationError("derived module-classification positive self-test failed")
    caught = False
    try:
        validate_module_classification("adversarial", "compatibility", 1, ["A"])
    except GenerationError:
        caught = True
    if not caught:
        raise GenerationError("blanket module-classification mutation self-test failed")
    if graph is not None:
        verify_digest(graph, GRAPH_SHA256)
        inventory = inventory_rows()
        selector = build_selector(inventory)
        declarations, edges = parse_graph(graph)
        routes = frozen_declaration_destinations(selector, declarations)
        route_rows = frozen_route_rows(selector, declarations, routes)
        validate_frozen_route_rows(route_rows, selector, declarations)
        mutated_route_rows = [dict(row) for row in route_rows]
        berger_row = next(
            row
            for row in mutated_route_rows
            if row["baseline_owner_module"] == "NumStability.Analysis.BergerGeneral"
        )
        binomial_row = next(
            row
            for row in mutated_route_rows
            if row["baseline_owner_module"]
            == "NumStability.Analysis.MatrixPowersBinomialBound"
        )
        berger_row["destination_module"], binomial_row["destination_module"] = (
            binomial_row["destination_module"],
            berger_row["destination_module"],
        )
        caught = False
        try:
            validate_frozen_route_rows(mutated_route_rows, selector, declarations)
        except GenerationError:
            caught = True
        if not caught:
            raise GenerationError("whole-owner destination-swap mutation self-test failed")
        destinations_by_owner: dict[str, set[str]] = defaultdict(set)
        declaration_counts: Counter[str] = Counter()
        for row in route_rows:
            declaration_counts[row["baseline_owner_module"]] += 1
            destinations_by_owner[row["baseline_owner_module"]].add(
                row["destination_module"]
            )
        classification_census = Counter(
            "classify_compatibility"
            if declaration_counts[owner["module"]] == 0
            else "relocate_whole"
            if len(destinations_by_owner[owner["module"]]) == 1
            else "relocate_split"
            for owner in selector
        )
        if classification_census != Counter(
            {"classify_compatibility": 32, "relocate_whole": 9, "relocate_split": 4}
        ):
            raise GenerationError("exact frozen-route module-classification census drift")
        validate_private_route_components(route_rows, edges)
        closure = private_closure(
            route_rows,
            declarations,
            edges,
            {row["module"] for row in selector},
        )
        if len(closure) != 77 or len({row[7] for row in closure if row[7] != "-"}) != 14:
            raise GenerationError("exact frozen-route private closure positive self-test failed")
        dag = destination_dag(route_rows, edges)
        if (
            len(dag),
            sum(row[2] for row in dag),
            sum(row[3] for row in dag),
        ) != (30, 31, 136):
            raise GenerationError("exact frozen-route full destination DAG self-test failed")
        mutated_edges = [
            *edges,
            Edge(
                "body",
                "NumStability.cstarMatrixEuclideanCoefficientLinear",
                "NumStability.cstarMatrix_complex_finiteDimensional",
                "adversarial duplicate cross-family edge",
            ),
        ]
        caught = False
        try:
            destination_dag(route_rows, mutated_edges)
        except GenerationError:
            caught = True
        if not caught:
            raise GenerationError("destination DAG mutation self-test failed")
        mutated_rows = [dict(row) for row in route_rows]
        next(row for row in mutated_rows if row["visibility"] == "private")[
            "visibility"
        ] = "public"
        caught = False
        try:
            private_closure(
                mutated_rows,
                declarations,
                edges,
                {row["module"] for row in selector},
            )
        except GenerationError:
            caught = True
        if not caught:
            raise GenerationError("private closure mutation self-test failed")
        if ilean_root is not None:
            resolved_roots = validate_all_ilean_roots(
                selector, declarations, ilean_root
            )
            if len(resolved_roots) != EXPECTED_DECLARATIONS:
                raise GenerationError("all-194 .ilean root positive self-test failed")
    elif ilean_root is not None:
        raise GenerationError("--ilean-root self-test requires --graph")


def audit(args: argparse.Namespace) -> dict[str, Any]:
    if args.graph is None:
        raise GenerationError("--graph is required for a fresh exact-C0005 format-2 replay")
    graph = args.graph.resolve()
    reviewed_inputs = [
        value.resolve()
        for value in (
            args.destination_plan,
            args.module_plan,
            args.wrapper_plan,
            args.source_command_plan,
            args.declaration_plan,
            args.compatibility_postimage,
            args.review_metadata,
        )
        if isinstance(value, Path)
    ]
    if args.emit_review_drafts:
        reviewed_inputs.extend(
            [
                *REVIEW_DRAFT_PATHS.values(),
                *DERIVED_REVIEW_DRAFT_PATHS.values(),
                COMPATIBILITY_DRAFT,
            ]
        )
    elif args.review_metadata is not None:
        reviewed_inputs.extend(DERIVED_REVIEW_DRAFT_PATHS.values())
    verify_base(
        graph,
        reviewed_inputs,
        allow_materialized=args.materialize_reviewed_controls,
    )
    inventory = inventory_rows()
    selector = build_selector(inventory)
    declarations, edges = parse_graph(graph)
    projection = build_projection(selector, declarations, edges)
    frozen_routes = frozen_declaration_destinations(selector, declarations)
    frozen_rows = frozen_route_rows(selector, declarations, frozen_routes)
    validate_frozen_route_rows(frozen_rows, selector, declarations)
    validate_private_route_components(frozen_rows, edges)
    frozen_closure = private_closure(
        frozen_rows,
        declarations,
        edges,
        {row["module"] for row in selector},
    )
    frozen_dag = destination_dag(frozen_rows, edges)
    imports = direct_import_map(inventory)
    consumers, consumer_counts = build_consumers(selector, inventory, imports)
    consumers = resolve_consumer_routes(consumers, declarations, frozen_routes)
    overlaps = overlap_facts(selector, inventory, declarations, edges, imports)
    destination_facts = validate_destination_contract(inventory)

    result: dict[str, Any] = {
        "accepted_control_sha": ACCEPTED_CONTROL_SHA,
        "accepted_control_ci": {
            **ACCEPTED_CI_EVIDENCE,
            "attestation_sha256": sha256_bytes(canonical_json(ACCEPTED_CI_EVIDENCE)),
            "artifact": {
                "path": repo_relative(CI_ATTESTATION),
                "sha256": CI_ATTESTATION_SHA256,
            },
        },
        "base_checkpoint_id": BASE_CHECKPOINT_ID,
        "base_code_sha": BASE_CODE_SHA,
        "consumer_counts": consumer_counts,
        "graph_sha256": sha256_path(graph),
        "ids": {
            "branch": BRANCH_ID,
            "milestone": MILESTONE_ID,
            "projection": PROJECTION_ID,
            "request": REQUEST_ID,
            "wave": WAVE_ID,
        },
        "overlap_facts": overlaps,
        "destination_contract": destination_facts,
        "projection": {
            "counts": projection.counts,
            "gzip_sha256": sha256_bytes(projection.compressed),
            "payload_sha256": sha256_bytes(projection.payload),
        },
        "frozen_routes": {
            "count": len(frozen_routes),
            "destination_dag": {
                "body_edges": sum(row[3] for row in frozen_dag),
                "rows": len(frozen_dag),
                "sha256": sha256_bytes(canonical_json(frozen_dag)),
                "signature_edges": sum(row[2] for row in frozen_dag),
            },
            "destination_counts": dict(sorted(Counter(frozen_routes.values()).items())),
            "private_closure": {
                "rows": len(frozen_closure),
                "sha256": sha256_bytes(canonical_json(frozen_closure)),
            },
            "sha256": sha256_bytes(canonical_json(frozen_routes)),
        },
        "selector": {
            "owners": len(selector),
            "sha256": sha256_bytes(
                tsv_bytes(SELECTOR_HEADER, ((row["module"], row["path"]) for row in selector))
            ),
        },
        "planned_control_schema": planned_control_schema(projection),
        "materialization_blockers": [
            "fresh reviewed 30-row all-vacant destination plan is not yet supplied",
            "fresh reviewed 45-row module/wrapper-frontier plan is not yet supplied",
            "fresh reviewed 45-row exact wrapper import plan is not yet supplied",
            "fresh reviewed 194-row source-command span/order plan is not yet supplied",
            "fresh reviewed 194-row declaration route plan is not yet supplied",
            "fresh reviewed external-owner supply, complete post-move import manifest, and focused-test plan are not yet supplied",
            "fresh reviewed R0011 shared-path transform plan is not yet supplied",
            "R0011 path set and phase shared-path reservations are not yet frozen",
            "completion checker has no exact B0010/P0010/R0011 contract yet",
            "primary-human planned-control timestamp/approval is an external authority input",
        ],
    }

    semantic_inputs = (
        args.destination_plan,
        args.module_plan,
        args.wrapper_plan,
        args.source_command_plan,
        args.declaration_plan,
        args.compatibility_postimage,
        args.ilean_root,
        args.review_metadata,
        args.review_metadata_sha256,
    )
    if args.emit_review_drafts:
        if args.ilean_root is None:
            raise GenerationError("--emit-review-drafts requires --ilean-root")
        supplied_review_inputs = (
            args.destination_plan,
            args.module_plan,
            args.wrapper_plan,
            args.source_command_plan,
            args.declaration_plan,
            args.compatibility_postimage,
            args.review_metadata,
            args.review_metadata_sha256,
        )
        if any(supplied_review_inputs):
            raise GenerationError(
                "--emit-review-drafts cannot be combined with already reviewed semantic inputs"
            )
        payloads = build_review_draft_payloads(
            selector,
            inventory,
            declarations,
            edges,
            frozen_routes,
            consumers,
            imports,
            consumer_counts,
            overlaps,
            projection,
            destination_facts,
            args.ilean_root.resolve(),
        )
        result["review_drafts"] = write_review_drafts(
            payloads, refresh=args.refresh_review_drafts
        )
        result["materialization_blockers"] = [
            "the emitted semantic TSVs and complete compatibility postimage are review candidates, not approvals",
            *result["materialization_blockers"],
        ]
        return result
    if any(semantic_inputs) and not all(semantic_inputs):
        raise GenerationError(
            "--destination-plan, --module-plan, --wrapper-plan, --source-command-plan, "
            "--declaration-plan, --compatibility-postimage, --ilean-root, --review-metadata, "
            "and --review-metadata-sha256 must be supplied together"
        )
    if all(semantic_inputs):
        validate_ci_attestation(live=True)
        destination_plan = load_destination_plan(args.destination_plan.resolve(), inventory)
        module_plan = load_module_plan(args.module_plan.resolve(), selector, declarations)
        wrapper_plan = load_wrapper_plan(
            args.wrapper_plan.resolve(), selector, declarations, module_plan
        )
        compatibility_postimage = args.compatibility_postimage.resolve()
        reject_historical_input(compatibility_postimage)
        expected_compatibility = draft_compatibility_postimage(wrapper_plan)
        if compatibility_postimage.read_bytes() != expected_compatibility:
            raise GenerationError(
                "reviewed compatibility postimage differs from the exact public wrapper frontier"
            )
        source_commands = load_source_command_plan(
            args.source_command_plan.resolve(),
            selector,
            declarations,
            args.ilean_root.resolve(),
        )
        declaration_plan = load_declaration_plan(
            args.declaration_plan.resolve(),
            selector,
            declarations,
            module_plan,
            source_commands,
        )
        expected_review_payloads = build_review_draft_payloads(
            selector,
            inventory,
            declarations,
            edges,
            frozen_routes,
            consumers,
            imports,
            consumer_counts,
            overlaps,
            projection,
            destination_facts,
            args.ilean_root.resolve(),
        )
        supplied_fixed = {
            REVIEW_DRAFT_PATHS["declaration_plan"]: args.declaration_plan.resolve(),
            REVIEW_DRAFT_PATHS["destination_plan"]: args.destination_plan.resolve(),
            REVIEW_DRAFT_PATHS["module_plan"]: args.module_plan.resolve(),
            REVIEW_DRAFT_PATHS["source_command_plan"]: args.source_command_plan.resolve(),
            REVIEW_DRAFT_PATHS["wrapper_plan"]: args.wrapper_plan.resolve(),
            COMPATIBILITY_DRAFT: compatibility_postimage,
        }
        for expected_path, supplied_path in supplied_fixed.items():
            if supplied_path != expected_path.resolve():
                raise GenerationError(
                    f"review input must use fixed activation path {expected_path}: {supplied_path}"
                )
        for path, payload in expected_review_payloads.items():
            if not path.is_file() or path.read_bytes() != payload:
                raise GenerationError(
                    f"reviewed artifact does not reproduce from exact C0005 inputs: {path}"
                )
        review = load_review_metadata(
            args.review_metadata.resolve(),
            args.review_metadata_sha256,
            {
                "declaration_plan": args.declaration_plan.resolve(),
                "destination_plan": args.destination_plan.resolve(),
                "module_plan": args.module_plan.resolve(),
                "source_command_plan": args.source_command_plan.resolve(),
                "wrapper_plan": args.wrapper_plan.resolve(),
                "compatibility_postimage": compatibility_postimage,
                **{
                    role: path
                    for role, path in DERIVED_REVIEW_DRAFT_PATHS.items()
                },
                "planning_generator": Path(__file__).resolve(),
                "shared_postimage_renderer": SHARED_POSTIMAGE_RENDERER,
                "ci_attestation": CI_ATTESTATION,
            },
        )
        validate_private_route_components(declaration_plan, edges)
        normalization = private_normalization(declaration_plan, declarations)
        closure = private_closure(
            declaration_plan,
            declarations,
            edges,
            {row["module"] for row in selector},
        )
        dag = destination_dag(declaration_plan, edges)
        tests = minimum_test_plan(
            selector, declaration_plan, consumers, imports, declarations, edges
        )
        result["reviewed_plan"] = {
            "destination_dag_rows": len(dag),
            "destination_rows": len(destination_plan),
            "minimum_test_rows": len(tests),
            "module_rows": len(module_plan),
            "private_closure_rows": len(closure),
            "private_normalization_rows": len(normalization),
            "route_rows": len(declaration_plan),
            "source_command_rows": len(source_commands),
            "wrapper_rows": len(wrapper_plan),
            "review_id": review["review_id"],
            "review_metadata_sha256": args.review_metadata_sha256,
            "compatibility_postimage_sha256": sha256_path(compatibility_postimage),
        }
        checker_blocker = "completion checker has no exact B0010/P0010/R0011 contract yet"
        discharged_blockers = {
            "fresh reviewed 30-row all-vacant destination plan is not yet supplied",
            "fresh reviewed 45-row module/wrapper-frontier plan is not yet supplied",
            "fresh reviewed 45-row exact wrapper import plan is not yet supplied",
            "fresh reviewed 194-row source-command span/order plan is not yet supplied",
            "fresh reviewed 194-row declaration route plan is not yet supplied",
            "fresh reviewed external-owner supply, complete post-move import manifest, and focused-test plan are not yet supplied",
            "fresh reviewed R0011 shared-path transform plan is not yet supplied",
            "R0011 path set and phase shared-path reservations are not yet frozen",
            "primary-human planned-control timestamp/approval is an external authority input",
        }
        present = set(result["materialization_blockers"])
        if not discharged_blockers <= present or present - discharged_blockers != {
            checker_blocker
        }:
            raise GenerationError(
                "reviewed planning inputs did not discharge the exact internal blocker set"
            )
        result["materialization_blockers"] = [checker_blocker]
        if args.materialize_reviewed_controls:
            if result["materialization_blockers"] != [checker_blocker]:
                raise GenerationError("unresolved internal blocker forbids materialization")
            result["emitted_artifacts"] = materialize_reviewed_controls(
                selector=selector,
                inventory=inventory,
                declarations=declarations,
                edges=edges,
                projection=projection,
                destination_plan=destination_plan,
                module_plan=module_plan,
                wrapper_plan=wrapper_plan,
                source_commands=source_commands,
                declaration_plan=declaration_plan,
                consumers=consumers,
                imports=imports,
                consumer_counts=consumer_counts,
                overlaps=overlaps,
                destination_facts=destination_facts,
                compatibility_postimage=compatibility_postimage,
                review=review,
            )
            result["materialization_blockers"] = [
                "completion checker exact B0010/P0010/R0011 contract must be pinned to "
                "the emitted planned-control contract before commit",
                "planned-control main commit/push and exact CI green are external authority gates",
            ]
    elif args.materialize_reviewed_controls:
        raise GenerationError(
            "--materialize-reviewed-controls requires the complete reviewed semantic input set"
        )
    return result


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--graph",
        type=Path,
        help="required fresh exact-C0005 format-2 graph (SHA-256 is pinned)",
    )
    parser.add_argument(
        "--destination-plan",
        type=Path,
        help="fresh reviewed 30-row destination-plan TSV; all leaves must be casefold-vacant",
    )
    parser.add_argument(
        "--module-plan",
        type=Path,
        help="fresh reviewed B0010 module-routes TSV; historical W06 input is rejected",
    )
    parser.add_argument(
        "--wrapper-plan",
        type=Path,
        help="fresh reviewed 45-row exact C0005-import-preserving wrapper plan TSV",
    )
    parser.add_argument(
        "--source-command-plan",
        type=Path,
        help="fresh reviewed 194-row exact source-span and command-order TSV",
    )
    parser.add_argument(
        "--ilean-root",
        type=Path,
        help="exact-code build lib/lean root used to bind all source commands to .ilean spans",
    )
    parser.add_argument(
        "--declaration-plan",
        type=Path,
        help="fresh reviewed B0010 declaration-routes TSV; historical W06 input is rejected",
    )
    parser.add_argument(
        "--compatibility-postimage",
        type=Path,
        help="fresh reviewed complete COMPATIBILITY.md postimage for the 45 public frontiers",
    )
    parser.add_argument(
        "--review-metadata",
        type=Path,
        help="external primary-human JSON review that hash-pins all supplied semantic plans",
    )
    parser.add_argument(
        "--review-metadata-sha256",
        help="independently supplied uppercase SHA-256 of --review-metadata",
    )
    parser.add_argument(
        "--emit-review-drafts",
        action="store_true",
        help="write only the fixed non-authority R07 review candidates",
    )
    parser.add_argument(
        "--refresh-review-drafts",
        action="store_true",
        help="replace divergent fixed review candidates; requires --emit-review-drafts",
    )
    parser.add_argument(
        "--materialize-reviewed-controls",
        action="store_true",
        help="write exact planned controls only after validating the full hash-pinned review",
    )
    parser.add_argument("--self-test", action="store_true")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        if args.refresh_review_drafts and not args.emit_review_drafts:
            raise GenerationError("--refresh-review-drafts requires --emit-review-drafts")
        if args.materialize_reviewed_controls and args.emit_review_drafts:
            raise GenerationError(
                "--materialize-reviewed-controls cannot be combined with --emit-review-drafts"
            )
        if args.self_test:
            self_test(
                args.graph.resolve() if args.graph is not None else None,
                args.ilean_root.resolve() if args.ilean_root is not None else None,
            )
            print("C0006/R07 planning generator self-test passed")
            return 0
        print(canonical_json(audit(args)).decode("utf-8"), end="")
        return 0
    except (GenerationError, OSError, UnicodeError, json.JSONDecodeError) as error:
        print(f"C0006/R07 planning generation blocked: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
