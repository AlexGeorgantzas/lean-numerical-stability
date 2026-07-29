#!/usr/bin/env python3
"""Generate and enforce the BlockLU Phase 12 sibling ownership contract.

This follow-on contract covers the ten declaration-bearing historical BlockLU
siblings that were deliberately excluded from the original 1,990-declaration
Phase 12 partition.  The checker reuses the format-2 graph and structural-file
parsers from ``check_blocklu_phase12_ownership.py`` but freezes a distinct
selection, route map, private-name map, and compatibility-wrapper contract.

The migration permits owner changes and the 27 explicitly listed Lean private
name changes only.  It has no reviewed edge-drop mechanism: stage and post mode
require the complete normalized format-2 declaration/signature/body graph to
match the frozen pre-edit graph exactly.
"""

from __future__ import annotations

import argparse
import tempfile
from collections import Counter, defaultdict
from pathlib import Path
from typing import Callable

import check_blocklu_phase12_ownership as core


BASELINE_TSV_BYTES = 115_774_316
BASELINE_TSV_SHA256 = (
    "AC7DB49BEA92D0FFA4753B43851C02FE0306CF8CC4A5EA8B593DE735CCE6E6F5"
)

# Filled from the canonical LF-normalized tracked artifacts.  Keeping these
# beside the immutable baseline identity makes a route or exception change a
# reviewed contract revision rather than an unnoticed checker input change.
MANIFEST_SHA256 = (
    "72D8658C8FAFF2E99276CF5AB9F0658A7089D9BB35BB1E749A00F30EDB606BA8"
)
ROUTES_SHA256 = (
    "C81E89528999F8A9E4A04B16EA4F1D015BCDEA2B43681F0A9260601BD0627626"
)
PRIVATE_REWRITES_SHA256 = (
    "240C4E2C897CB702F4508ABB7725D3FD661F7916F9DE75BACAD543AA8D4F2921"
)
STRUCTURAL_CONTRACT_SHA256 = (
    "77249431759AE98B8487941C997E5EC5EE6CDA4CEAC9EEE7D929C034B99DD3E8"
)
PHASE12_BASE_STRUCTURAL_CONTRACT_SHA256 = (
    "E259772BA776EC0595600F6F1DD25FACC036ED247995B5AFA1B3C0EFD353769F"
)
EXPANDED_PHASE12_STRUCTURAL_CONTRACT_SHA256 = (
    "06A59060BA12FAC096F4A78F286AA5B205251ACC86A15CDC6A99A91C4E09211B"
)

DEFAULT_MANIFEST = Path(
    "docs/architecture/declaration-ownership/"
    "blocklu-phase12-siblings.tsv"
)
DEFAULT_ROUTES = Path(
    "docs/architecture/declaration-ownership/"
    "blocklu-phase12-siblings-routes.tsv"
)
DEFAULT_PRIVATE_REWRITES = Path(
    "docs/architecture/declaration-ownership/"
    "blocklu-phase12-siblings-private-rewrites.tsv"
)
DEFAULT_STRUCTURAL_CONTRACT = Path(
    "docs/architecture/declaration-ownership/"
    "blocklu-phase12-siblings-structural-contract.tsv"
)
DEFAULT_PHASE12_STRUCTURAL_CONTRACT = Path(
    "docs/architecture/declaration-ownership/"
    "blocklu-phase12-structural-contract.tsv"
)
DEFAULT_PARENT_PHASE12_STRUCTURAL_CONTRACT = Path(
    "docs/architecture/declaration-ownership/"
    "blocklu-phase12-siblings-parent-structural-contract.tsv"
)
DEFAULT_EXPANDED_PHASE12_STRUCTURAL_CONTRACT = Path(
    "docs/architecture/declaration-ownership/"
    "blocklu-phase12-siblings-expanded-structural-contract.tsv"
)

HISTORICAL_COUNTS = {
    "NumStability.Algorithms.LU.BlockLUArbitraryNormSourceClosure": 18,
    "NumStability.Algorithms.LU.BlockLUComputationSourceClosure": 14,
    "NumStability.Algorithms.LU.BlockLUFirstOrderFamilies": 94,
    "NumStability.Algorithms.LU.BlockLUPointRowGrowthSourceClosure": 25,
    "NumStability.Algorithms.LU.BlockLURowSourceClosure": 10,
    "NumStability.Algorithms.LU.BlockLUScalarGrowthBridge": 36,
    "NumStability.Algorithms.LU.BlockLUSPDFamilies": 4,
    "NumStability.Algorithms.LU.BlockLUSPDSourceClosure": 22,
    "NumStability.Algorithms.LU.BlockLUSourceClosure": 9,
    "NumStability.Algorithms.LU.BlockLUVarying": 55,
}
HISTORICAL_MODULES = frozenset(HISTORICAL_COUNTS)
EXPECTED_DECLARATIONS = 287
EXPECTED_PUBLIC = 260
EXPECTED_PRIVATE = 27

DESTINATION_COUNTS = {
    "NumStability.Algorithms.LinearSystems.LU.BlockLU.ArbitraryNorm": 11,
    "NumStability.Algorithms.LinearSystems.LU.BlockLU.FirstOrderFamilies": 60,
    "NumStability.Algorithms.LinearSystems.LU.BlockLU.OperatorTwo": 3,
    "NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefinite": 1,
    "NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefiniteFactorBounds": 16,
    "NumStability.Algorithms.LinearSystems.LU.BlockLU.VaryingBlocks.Algebra": 8,
    "NumStability.Algorithms.LinearSystems.LU.BlockLU.VaryingBlocks.Basic": 28,
    "NumStability.Algorithms.LinearSystems.LU.BlockLU.VaryingBlocks.RecursiveFactorization": 6,
    "NumStability.Algorithms.LinearSystems.LU.BlockLU.VaryingBlocks.SchurComplement": 4,
    "NumStability.Algorithms.LinearSystems.LU.BlockLU.VaryingBlocks.Uniqueness": 9,
    "NumStability.Source.Higham.Chapter13.Equation23.PointRowGrowth": 25,
    "NumStability.Source.Higham.Chapter13.Equation25.Factorization": 2,
    "NumStability.Source.Higham.Chapter13.Equation25.Families": 4,
    "NumStability.Source.Higham.Chapter13.Problem04.ScalarGrowthBridge": 36,
    "NumStability.Source.Higham.Chapter13.Section01.OperationModelFamilies": 3,
    "NumStability.Source.Higham.Chapter13.Section03.ArbitraryNormDominance": 7,
    "NumStability.Source.Higham.Chapter13.Section03.ColumnDominanceClosure": 6,
    "NumStability.Source.Higham.Chapter13.Section03.RowDominanceClosure": 10,
    "NumStability.Source.Higham.Chapter13.Section03.SPDFactorBounds": 3,
    "NumStability.Source.Higham.Chapter13.Table01.Families": 2,
    "NumStability.Source.Higham.Chapter13.Theorem05.FamilyErrorAnalysis": 29,
    "NumStability.Source.Higham.Chapter13.Theorem06.Computation": 14,
}

EXPECTED_REUSABLE_DECLARATIONS = 146
EXPECTED_SOURCE_DECLARATIONS = 141
EXPECTED_DESTINATION_NODES = 22
EXPECTED_DESTINATION_EDGES = 22
EXPECTED_CROSS_DESTINATION_TYPED_EDGES = Counter(
    {"body": 226, "signature": 79}
)
EXPECTED_PRIVATE_TARGET_EDGES = Counter(
    {
        ("body", "private"): 38,
        ("body", "public"): 56,
        ("signature", "private"): 21,
        ("signature", "public"): 11,
    }
)
EXPECTED_PRIVATE_BY_HISTORICAL = Counter(
    {
        "NumStability.Algorithms.LU.BlockLUScalarGrowthBridge": 25,
        "NumStability.Algorithms.LU.BlockLUVarying": 2,
    }
)

VARYING_DESTINATIONS = frozenset(
    {
        "NumStability.Algorithms.LinearSystems.LU.BlockLU.VaryingBlocks.Algebra",
        "NumStability.Algorithms.LinearSystems.LU.BlockLU.VaryingBlocks.Basic",
        "NumStability.Algorithms.LinearSystems.LU.BlockLU.VaryingBlocks.RecursiveFactorization",
        "NumStability.Algorithms.LinearSystems.LU.BlockLU.VaryingBlocks.SchurComplement",
        "NumStability.Algorithms.LinearSystems.LU.BlockLU.VaryingBlocks.Uniqueness",
    }
)
VARYING_UMBRELLA = (
    "NumStability.Algorithms.LinearSystems.LU.BlockLU.VaryingBlocks"
)
VARYING_SOURCE_LOCATOR = (
    "NumStability.Source.Higham.Chapter13.Theorem02.VaryingBlocks"
)

EXPECTED_STRUCTURAL_IMPORTS = {
    "NumStability.Algorithms.LU.BlockLUArbitraryNormSourceClosure": (
        "NumStability.Algorithms.LinearSystems.LU.BlockLU.ArbitraryNorm",
        "NumStability.Source.Higham.Chapter13.Section03.ArbitraryNormDominance",
    ),
    "NumStability.Algorithms.LU.BlockLUComputationSourceClosure": (
        "NumStability.Source.Higham.Chapter13.Theorem06.Computation",
    ),
    "NumStability.Algorithms.LU.BlockLUFirstOrderFamilies": (
        "NumStability.Algorithms.LinearSystems.LU.BlockLU.FirstOrderFamilies",
        "NumStability.Source.Higham.Chapter13.Section01.OperationModelFamilies",
        "NumStability.Source.Higham.Chapter13.Table01.Families",
        "NumStability.Source.Higham.Chapter13.Theorem05.FamilyErrorAnalysis",
    ),
    "NumStability.Algorithms.LU.BlockLUPointRowGrowthSourceClosure": (
        "NumStability.Source.Higham.Chapter13.Equation23.PointRowGrowth",
    ),
    "NumStability.Algorithms.LU.BlockLURowSourceClosure": (
        "NumStability.Source.Higham.Chapter13.Section03.RowDominanceClosure",
    ),
    "NumStability.Algorithms.LU.BlockLUScalarGrowthBridge": (
        "NumStability.Source.Higham.Chapter13.Problem04.ScalarGrowthBridge",
    ),
    "NumStability.Algorithms.LU.BlockLUSPDFamilies": (
        "NumStability.Source.Higham.Chapter13.Equation25.Families",
    ),
    "NumStability.Algorithms.LU.BlockLUSPDSourceClosure": (
        "NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefinite",
        "NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefiniteFactorBounds",
        "NumStability.Source.Higham.Chapter13.Equation25.Factorization",
        "NumStability.Source.Higham.Chapter13.Section03.SPDFactorBounds",
    ),
    "NumStability.Algorithms.LU.BlockLUSourceClosure": (
        "NumStability.Algorithms.LinearSystems.LU.BlockLU.OperatorTwo",
        "NumStability.Source.Higham.Chapter13.Section03.ColumnDominanceClosure",
    ),
    # The five reusable leaves are exposed through one declaration-free family
    # umbrella.  Source.Higham.Chapter13.Theorem02.VaryingBlocks is a separate
    # declaration-free source locator and does not own any of the 55 constants.
    "NumStability.Algorithms.LU.BlockLUVarying": (
        VARYING_UMBRELLA,
    ),
    VARYING_UMBRELLA: (
        "NumStability.Algorithms.LinearSystems.LU.BlockLU.VaryingBlocks.Algebra",
        "NumStability.Algorithms.LinearSystems.LU.BlockLU.VaryingBlocks.Basic",
        "NumStability.Algorithms.LinearSystems.LU.BlockLU.VaryingBlocks.RecursiveFactorization",
        "NumStability.Algorithms.LinearSystems.LU.BlockLU.VaryingBlocks.SchurComplement",
        "NumStability.Algorithms.LinearSystems.LU.BlockLU.VaryingBlocks.Uniqueness",
    ),
    VARYING_SOURCE_LOCATOR: (
        VARYING_UMBRELLA,
    ),
}

# These are additions to existing canonical aggregates owned by the
# integration lane.  They are intentionally kept out of the sibling-local
# wrapper contract and are instead composed with the frozen 143-pair parent
# checkpoint into a separately reviewed 170-pair post artifact.  The sibling
# post gate owns validation of that complete composed structural surface.
POST_INTEGRATION_REQUIRED_IMPORTS = {
    "NumStability.Algorithms.LinearSystems.LU.BlockLU": (
        "NumStability.Algorithms.LinearSystems.LU.BlockLU.ArbitraryNorm",
        "NumStability.Algorithms.LinearSystems.LU.BlockLU.FirstOrderFamilies",
        "NumStability.Algorithms.LinearSystems.LU.BlockLU.OperatorTwo",
        "NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefiniteFactorBounds",
        VARYING_UMBRELLA,
    ),
    "NumStability.Source.Higham.Chapter13.BlockLU": (
        "NumStability.Source.Higham.Chapter13.Equation23.PointRowGrowth",
        "NumStability.Source.Higham.Chapter13.Equation25.Factorization",
        "NumStability.Source.Higham.Chapter13.Equation25.Families",
        "NumStability.Source.Higham.Chapter13.Problem04.ScalarGrowthBridge",
        "NumStability.Source.Higham.Chapter13.Section01.OperationModelFamilies",
        "NumStability.Source.Higham.Chapter13.Section03.ArbitraryNormDominance",
        "NumStability.Source.Higham.Chapter13.Section03.ColumnDominanceClosure",
        "NumStability.Source.Higham.Chapter13.Section03.RowDominanceClosure",
        "NumStability.Source.Higham.Chapter13.Section03.SPDFactorBounds",
        "NumStability.Source.Higham.Chapter13.Table01.Families",
        VARYING_SOURCE_LOCATOR,
        "NumStability.Source.Higham.Chapter13.Theorem05.FamilyErrorAnalysis",
        "NumStability.Source.Higham.Chapter13.Theorem06.Computation",
    ),
    "NumStability.Source.Higham.Chapter13.Problem04": (
        "NumStability.Source.Higham.Chapter13.Problem04.ScalarGrowthBridge",
    ),
    "NumStability.Source.Higham.Chapter13.Section01": (
        "NumStability.Source.Higham.Chapter13.Section01.OperationModelFamilies",
    ),
    "NumStability.Source.Higham.Chapter13.Section03": (
        "NumStability.Source.Higham.Chapter13.Section03.ArbitraryNormDominance",
        "NumStability.Source.Higham.Chapter13.Section03.ColumnDominanceClosure",
        "NumStability.Source.Higham.Chapter13.Section03.RowDominanceClosure",
        "NumStability.Source.Higham.Chapter13.Section03.SPDFactorBounds",
    ),
    "NumStability.Source.Higham.Chapter13.Theorem02": (
        VARYING_SOURCE_LOCATOR,
    ),
    "NumStability.Source.Higham.Chapter13.Theorem05": (
        "NumStability.Source.Higham.Chapter13.Theorem05.FamilyErrorAnalysis",
    ),
    "NumStability.Source.Higham.Chapter13.Theorem06": (
        "NumStability.Source.Higham.Chapter13.Theorem06.Computation",
    ),
}
EXPECTED_POST_INTEGRATION_PAIRS = 27
EXPECTED_PHASE12_BASE_STRUCTURAL_PAIRS = 143
EXPECTED_EXPANDED_PHASE12_STRUCTURAL_PAIRS = 170
EXPECTED_EXPANDED_PHASE12_STRUCTURAL_MODULES = 19

# Current non-wrapper consumers of the historical sibling paths must stop
# relying on compatibility imports.  These are the exact canonical modules
# required by their frozen semantic dependencies (or, for Algorithms.lean,
# the two already-established aggregate surfaces).
POST_CONSUMER_REQUIRED_IMPORTS = {
    "NumStability.Algorithms": (
        "NumStability.Algorithms.LinearSystems.LU.BlockLU",
        "NumStability.Source.Higham.Chapter13.BlockLU",
    ),
    "NumStability.Algorithms.QR.Higham19WYApplicationClosure": (
        "NumStability.Analysis.FirstOrder.AsymptoticFamilies",
    ),
    "NumStability.Source.Higham.Chapter13.DemmelSharpMultiplier": (
        "NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefinite",
        "NumStability.Source.Higham.Chapter13.Lemma10.SchurComplement",
    ),
    "NumStability.Source.Higham.Chapter13.Equation25": (
        "NumStability.Source.Higham.Chapter13.Equation25.Families",
        "NumStability.Source.Higham.Chapter13.Section03.SPDFactorBounds",
        "NumStability.Source.Higham.Chapter13.Theorem05.FamilyErrorAnalysis",
        "NumStability.Source.Higham.Chapter13.Theorem06.Computation",
    ),
    "NumStability.Source.Higham.Chapter13.Table01": (
        "NumStability.Source.Higham.Chapter13.Table01.Families",
        "NumStability.Source.Higham.Chapter13.Theorem05.FamilyErrorAnalysis",
        "NumStability.Source.Higham.Chapter13.Theorem06.Computation",
    ),
}


def configure_shared_checker() -> None:
    """Parameterize the already-reviewed generic Phase 12 machinery."""

    core.HISTORICAL_MODULES = set(HISTORICAL_MODULES)
    core.COMPLETE_HISTORICAL_MODULES = set(HISTORICAL_MODULES)
    core.GROWTH_FACTOR_SELECTION = set()
    core.EXPECTED_HISTORICAL_COUNTS = dict(HISTORICAL_COUNTS)
    core.EXPECTED_MANIFEST_ROWS = EXPECTED_DECLARATIONS
    core.BASELINE_TSV_SHA256 = BASELINE_TSV_SHA256
    core.DEFAULT_STRUCTURAL_MODULES = set(HISTORICAL_MODULES)


configure_shared_checker()


def validate_baseline_identity(path: Path) -> None:
    size = path.stat().st_size
    if size != BASELINE_TSV_BYTES:
        raise ValueError(
            f"baseline TSV size differs: expected {BASELINE_TSV_BYTES}, found {size}"
        )
    digest = core.sha256_file(path)
    if digest != BASELINE_TSV_SHA256:
        raise ValueError(
            "baseline TSV SHA-256 differs: expected "
            f"{BASELINE_TSV_SHA256}, found {digest}"
        )


def selected_baseline(
    declarations: list[core.Declaration],
) -> dict[str, core.Declaration]:
    return core.selected_baseline_declarations(declarations)


def validate_partition_shape(records: dict[str, core.ManifestRow]) -> None:
    core.validate_manifest_shape(records)

    destination_counts = Counter(
        row.destination_module for row in records.values()
    )
    if destination_counts != Counter(DESTINATION_COUNTS):
        raise ValueError(
            "destination declaration counts differ from the reviewed 22-owner "
            f"partition: expected {DESTINATION_COUNTS}, found "
            f"{dict(destination_counts)}"
        )

    visibility_counts = Counter(row.visibility for row in records.values())
    expected_visibility = Counter(
        {"public": EXPECTED_PUBLIC, "private": EXPECTED_PRIVATE}
    )
    if visibility_counts != expected_visibility:
        raise ValueError(
            f"visibility counts differ: expected {dict(expected_visibility)}, "
            f"found {dict(visibility_counts)}"
        )

    private_by_historical = Counter(
        row.historical_module
        for row in records.values()
        if row.visibility == "private"
    )
    if private_by_historical != EXPECTED_PRIVATE_BY_HISTORICAL:
        raise ValueError(
            "private historical-owner counts differ: expected "
            f"{dict(EXPECTED_PRIVATE_BY_HISTORICAL)}, found "
            f"{dict(private_by_historical)}"
        )

    role_counts = Counter()
    for row in records.values():
        role_counts[core.destination_role(row.destination_module)] += 1
    expected_roles = Counter(
        {
            "reusable": EXPECTED_REUSABLE_DECLARATIONS,
            "source": EXPECTED_SOURCE_DECLARATIONS,
        }
    )
    if role_counts != expected_roles:
        raise ValueError(
            f"reusable/source counts differ: expected {dict(expected_roles)}, "
            f"found {dict(role_counts)}"
        )


def validate_structural_contract_design(
    contract: dict[str, tuple[str, ...]],
) -> None:
    if contract != EXPECTED_STRUCTURAL_IMPORTS:
        missing = sorted(set(EXPECTED_STRUCTURAL_IMPORTS) - set(contract))
        extra = sorted(set(contract) - set(EXPECTED_STRUCTURAL_IMPORTS))
        changed = sorted(
            module
            for module in set(contract) & set(EXPECTED_STRUCTURAL_IMPORTS)
            if contract[module] != EXPECTED_STRUCTURAL_IMPORTS[module]
        )
        raise ValueError(
            "compatibility structural contract differs: "
            f"missing={missing}; extra={extra}; changed={changed}"
        )

    integration_pairs = sum(
        len(imports) for imports in POST_INTEGRATION_REQUIRED_IMPORTS.values()
    )
    if integration_pairs != EXPECTED_POST_INTEGRATION_PAIRS:
        raise ValueError(
            "post-integration pair count differs: expected "
            f"{EXPECTED_POST_INTEGRATION_PAIRS}, found {integration_pairs}"
        )
    for module, imports in POST_INTEGRATION_REQUIRED_IMPORTS.items():
        core.check_module_name(module, "post-integration aggregate")
        if imports != tuple(sorted(imports)) or len(imports) != len(set(imports)):
            raise ValueError(
                f"post-integration imports are not unique and sorted for {module}"
            )
        for imported in imports:
            core.check_module_name(imported, f"post-integration import for {module}")
    for module, imports in POST_CONSUMER_REQUIRED_IMPORTS.items():
        core.check_module_name(module, "post-integration consumer")
        if imports != tuple(sorted(imports)) or len(imports) != len(set(imports)):
            raise ValueError(
                f"post-integration consumer imports are not unique and sorted "
                f"for {module}"
            )
        for imported in imports:
            core.check_module_name(imported, f"consumer import for {module}")


def structural_pair_count(contract: dict[str, tuple[str, ...]]) -> int:
    return sum(len(imports) for imports in contract.values())


def validate_expanded_phase12_contract_derivation(
    base: dict[str, tuple[str, ...]],
    expanded: dict[str, tuple[str, ...]],
) -> None:
    """Require the reviewed post contract to be base plus exactly 27 pairs."""

    base_pairs = structural_pair_count(base)
    if base_pairs != EXPECTED_PHASE12_BASE_STRUCTURAL_PAIRS:
        raise ValueError(
            "parent-checkpoint structural pair count differs: expected "
            f"{EXPECTED_PHASE12_BASE_STRUCTURAL_PAIRS}, found {base_pairs}"
        )
    unknown_aggregates = sorted(
        set(POST_INTEGRATION_REQUIRED_IMPORTS) - set(base)
    )
    if unknown_aggregates:
        raise ValueError(
            "sibling integration additions target unknown parent aggregates: "
            + ", ".join(unknown_aggregates)
        )

    expected = dict(base)
    for module, additions in POST_INTEGRATION_REQUIRED_IMPORTS.items():
        overlap = sorted(set(base[module]) & set(additions))
        if overlap:
            raise ValueError(
                f"sibling integration additions already occur in {module}: "
                + ", ".join(overlap)
            )
        expected[module] = tuple(sorted((*base[module], *additions)))

    expanded_pairs = structural_pair_count(expanded)
    if expanded_pairs != EXPECTED_EXPANDED_PHASE12_STRUCTURAL_PAIRS:
        raise ValueError(
            "expanded structural pair count differs: expected "
            f"{EXPECTED_EXPANDED_PHASE12_STRUCTURAL_PAIRS}, "
            f"found {expanded_pairs}"
        )
    if len(expanded) != EXPECTED_EXPANDED_PHASE12_STRUCTURAL_MODULES:
        raise ValueError(
            "expanded structural module count differs: expected "
            f"{EXPECTED_EXPANDED_PHASE12_STRUCTURAL_MODULES}, "
            f"found {len(expanded)}"
        )
    if expanded != expected:
        missing = sorted(set(expected) - set(expanded))
        extra = sorted(set(expanded) - set(expected))
        changed = sorted(
            module
            for module in set(expanded) & set(expected)
            if expanded[module] != expected[module]
        )
        raise ValueError(
            "expanded Phase 12 structural contract is not the exact parent "
            "checkpoint plus 27 sibling pairs: "
            f"missing={missing}; extra={extra}; changed={changed}"
        )


def validate_live_phase12_contract(
    live: dict[str, tuple[str, ...]],
    expanded: dict[str, tuple[str, ...]],
) -> None:
    if live == expanded:
        return
    missing = sorted(set(expanded) - set(live))
    extra = sorted(set(live) - set(expanded))
    changed = sorted(
        module
        for module in set(live) & set(expanded)
        if live[module] != expanded[module]
    )
    raise ValueError(
        "live Phase 12 structural contract differs from the reviewed "
        f"170-pair post artifact: missing={missing}; extra={extra}; "
        f"changed={changed}"
    )


def validate_required_import_map(
    actual: dict[str, tuple[str, ...]],
    required: dict[str, tuple[str, ...]],
    label: str,
) -> None:
    missing = [
        f"{module} -> {imported}"
        for module, imports in required.items()
        for imported in imports
        if imported not in set(actual.get(module, ()))
    ]
    if missing:
        raise ValueError(
            f"{label} omits required sibling integration imports: "
            + "; ".join(missing[:30])
        )


def read_direct_imports(path: Path) -> tuple[str, ...]:
    if not path.is_file():
        raise ValueError(f"missing post-integration consumer: {path}")
    source_lines = path.read_text(encoding="utf-8").splitlines()
    imports: list[str] = []
    for code in core.strip_lean_comments(source_lines):
        fields = code.strip().split()
        if fields[:1] == ["import"]:
            imported_modules = fields[1:]
        elif fields[:2] == ["public", "import"]:
            imported_modules = fields[2:]
        else:
            continue
        for imported in imported_modules:
            core.check_module_name(imported, f"{path}: import")
            imports.append(imported)
    return tuple(imports)


def historical_import_violations(project_root: Path) -> list[str]:
    scan_paths: list[Path] = []
    root_module = project_root / "NumStability.lean"
    if root_module.is_file():
        scan_paths.append(root_module)
    for scan_root in (project_root / "NumStability", project_root / "examples"):
        if scan_root.is_dir():
            scan_paths.extend(sorted(scan_root.rglob("*.lean")))

    violations: list[str] = []
    for path in scan_paths:
        legacy_imports = sorted(set(read_direct_imports(path)) & HISTORICAL_MODULES)
        if legacy_imports:
            violations.append(f"{path}: {', '.join(legacy_imports)}")
    return violations


def validate_post_consumer_retargets(project_root: Path) -> None:
    actual_imports = {
        module: read_direct_imports(core.module_path(project_root, module))
        for module in POST_CONSUMER_REQUIRED_IMPORTS
    }
    validate_required_import_map(
        actual_imports,
        POST_CONSUMER_REQUIRED_IMPORTS,
        "retargeted production consumers",
    )

    historical_importers = historical_import_violations(project_root)
    if historical_importers:
        raise ValueError(
            "root, production, or example modules still import historical "
            "BlockLU sibling paths: "
            + "; ".join(historical_importers[:30])
        )


def validate_post_integration_structures(
    project_root: Path,
    declarations: list[core.Declaration],
    phase12_structural_contract: Path,
    expanded_phase12_structural_contract: Path,
) -> None:
    """Validate the complete composed 170-pair canonical structural surface."""

    expanded_contract = core.read_structural_contract(
        expanded_phase12_structural_contract
    )
    validate_contract_file_digest(
        expanded_phase12_structural_contract,
        EXPANDED_PHASE12_STRUCTURAL_CONTRACT_SHA256,
        "expanded Phase 12 structural contract",
    )
    if (
        structural_pair_count(expanded_contract)
        != EXPECTED_EXPANDED_PHASE12_STRUCTURAL_PAIRS
        or len(expanded_contract) != EXPECTED_EXPANDED_PHASE12_STRUCTURAL_MODULES
    ):
        raise ValueError(
            "expanded Phase 12 structural contract has the wrong complete shape"
        )
    validate_required_import_map(
        expanded_contract,
        POST_INTEGRATION_REQUIRED_IMPORTS,
        "expanded Phase 12 structural contract",
    )

    live_contract = core.read_structural_contract(
        phase12_structural_contract
    )
    validate_live_phase12_contract(live_contract, expanded_contract)
    live_digest = core.sha256_file(phase12_structural_contract)
    if live_digest != EXPANDED_PHASE12_STRUCTURAL_CONTRACT_SHA256:
        raise ValueError(
            "live Phase 12 structural contract bytes differ from the reviewed "
            f"post artifact: found {live_digest}"
        )

    core.validate_structural_modules(
        project_root,
        declarations,
        set(expanded_contract),
        expanded_contract,
    )
    validate_post_consumer_retargets(project_root)


def validate_contract_file_digest(path: Path, expected: str, label: str) -> None:
    if not expected:
        # This branch exists only while initially generating the canonical
        # manifest and filling the checked-in digest constants.
        return
    digest = core.sha256_file(path)
    if digest != expected:
        raise ValueError(
            f"{label} SHA-256 differs: expected {expected}, found {digest}"
        )


def validate_contract_inputs(
    manifest: Path,
    routes: Path | None,
    private_rewrites: Path,
    structural_contract: Path,
    parent_phase12_structural_contract: Path,
    expanded_phase12_structural_contract: Path,
) -> None:
    validate_contract_file_digest(manifest, MANIFEST_SHA256, "manifest")
    # Stage/post may omit route regeneration, but they may not omit validation
    # of the checked-in reviewed route contract.
    route_contract = DEFAULT_ROUTES if routes is None else routes
    validate_contract_file_digest(route_contract, ROUTES_SHA256, "routes")
    validate_contract_file_digest(
        private_rewrites, PRIVATE_REWRITES_SHA256, "private rewrites"
    )
    validate_contract_file_digest(
        structural_contract,
        STRUCTURAL_CONTRACT_SHA256,
        "structural contract",
    )
    validate_contract_file_digest(
        parent_phase12_structural_contract,
        PHASE12_BASE_STRUCTURAL_CONTRACT_SHA256,
        "parent-checkpoint Phase 12 structural snapshot",
    )
    validate_contract_file_digest(
        expanded_phase12_structural_contract,
        EXPANDED_PHASE12_STRUCTURAL_CONTRACT_SHA256,
        "expanded Phase 12 structural contract",
    )


def validate_pre_expanded_structural_contract(
    parent_snapshot_path: Path,
    expanded_path: Path,
) -> None:
    validate_contract_file_digest(
        parent_snapshot_path,
        PHASE12_BASE_STRUCTURAL_CONTRACT_SHA256,
        "parent-checkpoint Phase 12 structural snapshot",
    )
    validate_contract_file_digest(
        expanded_path,
        EXPANDED_PHASE12_STRUCTURAL_CONTRACT_SHA256,
        "expanded Phase 12 structural contract",
    )
    base = core.read_structural_contract(parent_snapshot_path)
    expanded = core.read_structural_contract(expanded_path)
    validate_expanded_phase12_contract_derivation(base, expanded)


def validate_pre_live_parent_contract(
    live_path: Path,
    parent_snapshot_path: Path,
) -> None:
    validate_contract_file_digest(
        live_path,
        PHASE12_BASE_STRUCTURAL_CONTRACT_SHA256,
        "live pre-edit Phase 12 structural contract",
    )
    live = core.read_structural_contract(live_path)
    parent_snapshot = core.read_structural_contract(parent_snapshot_path)
    if live != parent_snapshot:
        raise ValueError(
            "live pre-edit Phase 12 structural contract differs from the "
            "pinned 143-pair parent snapshot"
        )


def validate_selected_edge_contract(
    dependency_tsv: Path,
    declarations: list[core.Declaration],
    actual_to_logical: dict[str, str],
    records: dict[str, core.ManifestRow],
) -> None:
    declaration_by_name = {
        declaration.name: declaration for declaration in declarations
    }
    cross_destination = Counter()
    private_target_edges = Counter()
    private_crossings: list[str] = []

    for edge in core.iter_dependency_edges(dependency_tsv):
        source_logical = actual_to_logical.get(edge.source)
        if source_logical is None:
            continue
        target_logical = actual_to_logical.get(edge.target)
        if target_logical is None:
            continue

        source_row = records[source_logical]
        target_row = records[target_logical]
        if source_row.destination_module != target_row.destination_module:
            cross_destination[edge.kind] += 1

        target_declaration = declaration_by_name[edge.target]
        if target_row.visibility == "private":
            source_visibility = records[source_logical].visibility
            private_target_edges[(edge.kind, source_visibility)] += 1
            if source_row.destination_module != target_row.destination_module:
                private_crossings.append(
                    f"{edge.kind} {edge.source} -> {edge.target}: "
                    f"{source_row.destination_module} -> "
                    f"{target_row.destination_module}"
                )
            if target_declaration.visibility != "private":
                raise ValueError(
                    f"manifest-private target is not private in graph: {edge.target}"
                )

    if cross_destination != EXPECTED_CROSS_DESTINATION_TYPED_EDGES:
        raise ValueError(
            "cross-destination typed edge counts differ: expected "
            f"{dict(EXPECTED_CROSS_DESTINATION_TYPED_EDGES)}, found "
            f"{dict(cross_destination)}"
        )
    if private_target_edges != EXPECTED_PRIVATE_TARGET_EDGES:
        raise ValueError(
            "private-target edge counts differ: expected "
            f"{dict(EXPECTED_PRIVATE_TARGET_EDGES)}, found "
            f"{dict(private_target_edges)}"
        )
    if private_crossings:
        raise ValueError(
            "private declarations cross destination boundaries: "
            + "; ".join(private_crossings[:20])
        )


def read_and_validate_manifest(
    manifest_path: Path,
    baseline: dict[str, core.Declaration],
) -> dict[str, core.ManifestRow]:
    records = core.read_manifest(manifest_path)
    core.validate_manifest_against_baseline(records, baseline)
    validate_partition_shape(records)
    digest = core.validate_expected_manifest_digest(
        records, MANIFEST_SHA256 or None
    )
    if MANIFEST_SHA256 and digest != MANIFEST_SHA256:
        raise AssertionError("manifest digest validation returned inconsistently")
    return records


def read_completed_destinations(args: argparse.Namespace) -> set[str]:
    completed: set[str] = set()
    for destination in args.completed_destination:
        core.check_module_name(destination, "--completed-destination")
        completed.add(destination)
    if args.completed_destinations is not None:
        completed.update(
            core.read_completed_destinations(args.completed_destinations)
        )
    return completed


def completed_historical_wrappers(
    records: dict[str, core.ManifestRow], completed: set[str]
) -> set[str]:
    destinations_by_historical: dict[str, set[str]] = defaultdict(set)
    for row in records.values():
        destinations_by_historical[row.historical_module].add(
            row.destination_module
        )
    return {
        historical
        for historical, destinations in destinations_by_historical.items()
        if destinations <= completed
    }


def completed_structural_modules(
    records: dict[str, core.ManifestRow], completed: set[str]
) -> tuple[set[str], set[str]]:
    """Return ready historical wrappers and all ready import-only modules."""

    wrappers = completed_historical_wrappers(records, completed)
    structural_modules = set(wrappers)
    if VARYING_DESTINATIONS <= completed:
        structural_modules.update((VARYING_UMBRELLA, VARYING_SOURCE_LOCATOR))
    return wrappers, structural_modules


def expect_value_error(action: Callable[[], object], label: str) -> None:
    try:
        action()
    except ValueError:
        return
    raise AssertionError(f"negative self-test accepted {label}")


def run_self_test() -> None:
    # The self-test validates the tracked positive contract before mutating
    # copies for negative count and compatibility cases.
    validate_contract_inputs(
        DEFAULT_MANIFEST,
        None,
        DEFAULT_PRIVATE_REWRITES,
        DEFAULT_STRUCTURAL_CONTRACT,
        DEFAULT_PARENT_PHASE12_STRUCTURAL_CONTRACT,
        DEFAULT_EXPANDED_PHASE12_STRUCTURAL_CONTRACT,
    )
    validate_pre_expanded_structural_contract(
        DEFAULT_PARENT_PHASE12_STRUCTURAL_CONTRACT,
        DEFAULT_EXPANDED_PHASE12_STRUCTURAL_CONTRACT,
    )
    records = core.read_manifest(DEFAULT_MANIFEST)
    validate_partition_shape(records)
    contract = core.read_structural_contract(DEFAULT_STRUCTURAL_CONTRACT)
    validate_structural_contract_design(contract)

    first_logical = sorted(records)[0]
    first = records[first_logical]
    wrong_destination = next(
        destination
        for destination in DESTINATION_COUNTS
        if destination != first.destination_module
    )
    bad_records = dict(records)
    bad_records[first_logical] = core.ManifestRow(
        first.logical_name,
        first.historical_module,
        wrong_destination,
        first.kind,
        first.visibility,
    )
    expect_value_error(
        lambda: validate_partition_shape(bad_records),
        "destination reassignment with wrong counts",
    )

    bad_contract = dict(contract)
    module = sorted(bad_contract)[0]
    bad_contract[module] = bad_contract[module][:-1]
    expect_value_error(
        lambda: validate_structural_contract_design(bad_contract),
        "missing compatibility target",
    )

    one_varying_destination = sorted(VARYING_DESTINATIONS)[0]
    _, incomplete_structural = completed_structural_modules(
        records, set(VARYING_DESTINATIONS) - {one_varying_destination}
    )
    if VARYING_UMBRELLA in incomplete_structural:
        raise AssertionError(
            "incomplete VaryingBlocks wave enabled its structural modules"
        )
    _, complete_structural = completed_structural_modules(
        records, set(VARYING_DESTINATIONS)
    )
    expected_varying_structural = {VARYING_UMBRELLA, VARYING_SOURCE_LOCATOR}
    if not expected_varying_structural <= complete_structural:
        raise AssertionError(
            "complete VaryingBlocks wave omitted its umbrella or source locator"
        )

    complete_integration = dict(POST_INTEGRATION_REQUIRED_IMPORTS)
    validate_required_import_map(
        complete_integration,
        POST_INTEGRATION_REQUIRED_IMPORTS,
        "self-test integration contract",
    )
    first_aggregate = sorted(complete_integration)[0]
    incomplete_integration = dict(complete_integration)
    incomplete_integration[first_aggregate] = complete_integration[
        first_aggregate
    ][1:]
    expect_value_error(
        lambda: validate_required_import_map(
            incomplete_integration,
            POST_INTEGRATION_REQUIRED_IMPORTS,
            "self-test integration contract",
        ),
        "missing canonical aggregate integration import",
    )

    base_phase12_contract = core.read_structural_contract(
        DEFAULT_PARENT_PHASE12_STRUCTURAL_CONTRACT
    )
    expanded_phase12_contract = core.read_structural_contract(
        DEFAULT_EXPANDED_PHASE12_STRUCTURAL_CONTRACT
    )
    validate_expanded_phase12_contract_derivation(
        base_phase12_contract, expanded_phase12_contract
    )
    validate_live_phase12_contract(
        expanded_phase12_contract, expanded_phase12_contract
    )
    expect_value_error(
        lambda: validate_live_phase12_contract(
            base_phase12_contract, expanded_phase12_contract
        ),
        "live 143-pair contract at full sibling completion",
    )
    bad_expanded_contract = dict(expanded_phase12_contract)
    first_parent_module = sorted(bad_expanded_contract)[0]
    bad_expanded_contract[first_parent_module] = bad_expanded_contract[
        first_parent_module
    ][1:]
    expect_value_error(
        lambda: validate_expanded_phase12_contract_derivation(
            base_phase12_contract, bad_expanded_contract
        ),
        "expanded structural contract with one missing pair",
    )

    with tempfile.TemporaryDirectory() as root_scan_directory:
        root_scan = Path(root_scan_directory)
        root_file = root_scan / "NumStability.lean"
        root_file.write_text(
            f"import {sorted(HISTORICAL_MODULES)[0]}\n",
            encoding="utf-8",
            newline="\n",
        )
        root_violations = historical_import_violations(root_scan)
        if len(root_violations) != 1 or "NumStability.lean" not in root_violations[0]:
            raise AssertionError(
                "root NumStability.lean historical import escaped the post scan"
            )

    reusable_a = "NumStability.Algorithms.LinearSystems.Example.A"
    reusable_b = "NumStability.Algorithms.LinearSystems.Example.B"
    source = "NumStability.Source.Higham.Example.Source"
    historical_a = "NumStability.Example.HistoricalA"
    historical_b = "NumStability.Example.HistoricalB"
    declarations = [
        core.Declaration("NumStability.a", historical_a, "theorem", "public"),
        core.Declaration("NumStability.b", historical_b, "theorem", "public"),
    ]
    actual_to_logical = {
        "NumStability.a": "NumStability.a",
        "NumStability.b": "NumStability.b",
    }

    def graph_records(first_destination: str, second_destination: str):
        return {
            "NumStability.a": core.ManifestRow(
                "NumStability.a",
                historical_a,
                first_destination,
                "theorem",
                "public",
            ),
            "NumStability.b": core.ManifestRow(
                "NumStability.b",
                historical_b,
                second_destination,
                "theorem",
                "public",
            ),
        }

    with tempfile.TemporaryDirectory() as temp_directory:
        temp = Path(temp_directory)
        dependency = temp / "dependency.tsv"
        dependency.write_text(
            "format\t2\n"
            "declaration\tNumStability.a\tNumStability.Example.HistoricalA"
            "\ttheorem\tpublic\n"
            "declaration\tNumStability.b\tNumStability.Example.HistoricalB"
            "\ttheorem\tpublic\n"
            "edge\tbody\tNumStability.a\tNumStability.b\n",
            encoding="utf-8",
            newline="\n",
        )
        expect_value_error(
            lambda: core.validate_destination_graph(
                dependency,
                declarations,
                actual_to_logical,
                graph_records(reusable_a, source),
            ),
            "reusable-to-source edge",
        )

        dependency.write_text(
            dependency.read_text(encoding="utf-8")
            + "edge\tbody\tNumStability.b\tNumStability.a\n",
            encoding="utf-8",
            newline="\n",
        )
        expect_value_error(
            lambda: core.validate_destination_graph(
                dependency,
                declarations,
                actual_to_logical,
                graph_records(reusable_a, reusable_b),
            ),
            "destination cycle",
        )

        logical_private = "_private.<module>.NumStability.helper"
        historical_private = (
            "_private.NumStability.Example.HistoricalA.0.NumStability.helper"
        )
        private_baseline = {
            logical_private: core.Declaration(
                historical_private, historical_a, "theorem", "private"
            )
        }
        private_records = {
            logical_private: core.ManifestRow(
                logical_private,
                historical_a,
                reusable_a,
                "theorem",
                "private",
            )
        }
        rewrites = temp / "private.tsv"
        rewrites.write_text("format\t1\n", encoding="utf-8", newline="\n")
        expect_value_error(
            lambda: core.read_private_rewrites(
                rewrites, private_records, private_baseline
            ),
            "missing private rewrite",
        )
        rewrites.write_text(
            "format\t1\n"
            f"{logical_private}\t{historical_private}\t"
            "_private.NumStability.Wrong.Owner.0.NumStability.helper\n",
            encoding="utf-8",
            newline="\n",
        )
        expect_value_error(
            lambda: core.read_private_rewrites(
                rewrites, private_records, private_baseline
            ),
            "private rewrite with wrong destination owner",
        )

        tiny = temp / "tiny.tsv"
        tiny.write_text("format\t2\n", encoding="utf-8", newline="\n")
        expect_value_error(
            lambda: validate_baseline_identity(tiny), "baseline size/hash"
        )

    expect_value_error(
        lambda: core.validate_normalized_graph_delta(
            Counter({"edge\tbody\tNumStability.a\tNumStability.b": 1}),
            Counter(),
        ),
        "unreviewed graph edge drop",
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--mode", choices=("pre", "stage", "post"))
    parser.add_argument("--dependency-tsv", type=Path)
    parser.add_argument("--baseline-tsv", type=Path)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--routes", type=Path)
    parser.add_argument("--write-manifest", action="store_true")
    parser.add_argument(
        "--ilean",
        action="append",
        default=[],
        metavar="HISTORICAL_MODULE=PATH",
    )
    parser.add_argument(
        "--private-rewrites", type=Path, default=DEFAULT_PRIVATE_REWRITES
    )
    parser.add_argument(
        "--structural-contract", type=Path, default=DEFAULT_STRUCTURAL_CONTRACT
    )
    parser.add_argument(
        "--phase12-structural-contract",
        type=Path,
        default=DEFAULT_PHASE12_STRUCTURAL_CONTRACT,
        help=(
            "live Phase 12 aggregate contract; full sibling stage/post "
            "requires it to equal the reviewed expanded contract"
        ),
    )
    parser.add_argument(
        "--parent-phase12-structural-contract",
        type=Path,
        default=DEFAULT_PARENT_PHASE12_STRUCTURAL_CONTRACT,
        help="immutable reviewed 143-pair parent-checkpoint snapshot",
    )
    parser.add_argument(
        "--expanded-phase12-structural-contract",
        type=Path,
        default=DEFAULT_EXPANDED_PHASE12_STRUCTURAL_CONTRACT,
        help="reviewed 170-pair composed structural contract for sibling post",
    )
    parser.add_argument("--expected-manifest-sha256")
    parser.add_argument("--project-root", type=Path, default=Path("."))
    parser.add_argument("--completed-destination", action="append", default=[])
    parser.add_argument("--completed-destinations", type=Path)
    parser.add_argument("--self-test", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.self_test:
        run_self_test()
        print("BlockLU Phase 12 sibling ownership checker self-test passed")
        return 0

    if args.mode is None or args.dependency_tsv is None:
        raise ValueError("--mode and --dependency-tsv are required")
    if args.write_manifest and args.mode != "pre":
        raise ValueError("--write-manifest is valid only in pre mode")
    if args.mode == "pre" and args.routes is None:
        raise ValueError("pre mode requires the reviewed --routes file")
    if args.expected_manifest_sha256 is not None:
        expected = args.expected_manifest_sha256.upper()
        if MANIFEST_SHA256 and expected != MANIFEST_SHA256:
            raise ValueError(
                "--expected-manifest-sha256 differs from the frozen sibling "
                f"manifest digest {MANIFEST_SHA256}"
            )

    structural_contract = core.read_structural_contract(
        args.structural_contract
    )
    validate_structural_contract_design(structural_contract)
    ilean_overrides = core.parse_ilean_overrides(args.ilean)

    if args.mode == "pre":
        validate_baseline_identity(args.dependency_tsv)
        # Reject a mutated auxiliary contract before --write-manifest can
        # touch the tracked manifest.  The generated canonical digest is also
        # checked in memory below before any write.
        validate_contract_file_digest(args.routes, ROUTES_SHA256, "routes")
        validate_contract_file_digest(
            args.private_rewrites, PRIVATE_REWRITES_SHA256, "private rewrites"
        )
        validate_contract_file_digest(
            args.structural_contract,
            STRUCTURAL_CONTRACT_SHA256,
            "structural contract",
        )
        validate_pre_expanded_structural_contract(
            args.parent_phase12_structural_contract,
            args.expanded_phase12_structural_contract,
        )
        validate_pre_live_parent_contract(
            args.phase12_structural_contract,
            args.parent_phase12_structural_contract,
        )
        declarations = core.read_dependency_declarations(args.dependency_tsv)
        baseline = selected_baseline(declarations)
        generated = core.generate_manifest(
            baseline, args.routes, args.project_root, ilean_overrides
        )
        validate_partition_shape(generated)
        core.validate_expected_manifest_digest(generated, MANIFEST_SHA256)
        if args.write_manifest:
            core.write_manifest(args.manifest, generated)

        records = read_and_validate_manifest(args.manifest, baseline)
        if records != generated:
            raise ValueError(
                "tracked sibling ownership manifest differs from reviewed "
                "route generation"
            )
        validate_contract_inputs(
            args.manifest,
            args.routes,
            args.private_rewrites,
            args.structural_contract,
            args.parent_phase12_structural_contract,
            args.expanded_phase12_structural_contract,
        )
        core.read_private_rewrites(
            args.private_rewrites, records, baseline
        )
        actual_to_logical = core.baseline_actual_to_logical(baseline)
        destination_nodes, destination_edges = core.validate_destination_graph(
            args.dependency_tsv,
            declarations,
            actual_to_logical,
            records,
        )
        if (
            destination_nodes != EXPECTED_DESTINATION_NODES
            or destination_edges != EXPECTED_DESTINATION_EDGES
        ):
            raise ValueError(
                "destination DAG size differs: expected "
                f"{EXPECTED_DESTINATION_NODES} nodes/"
                f"{EXPECTED_DESTINATION_EDGES} edges, found "
                f"{destination_nodes}/{destination_edges}"
            )
        validate_selected_edge_contract(
            args.dependency_tsv,
            declarations,
            actual_to_logical,
            records,
        )
        digest = core.sha256_bytes(core.manifest_bytes(records))
        print(
            "BlockLU Phase 12 sibling pre-migration ownership passed: "
            f"{len(records)} declarations ({EXPECTED_PUBLIC} public, "
            f"{EXPECTED_PRIVATE} private), canonical manifest {digest}, "
            f"{EXPECTED_REUSABLE_DECLARATIONS} reusable and "
            f"{EXPECTED_SOURCE_DECLARATIONS} source-owned declarations, "
            f"acyclic {destination_nodes}-destination graph with "
            f"{destination_edges} destination edges and "
            f"{sum(EXPECTED_CROSS_DESTINATION_TYPED_EDGES.values())} typed "
            "cross-destination edges"
        )
        return 0

    if args.baseline_tsv is None:
        raise ValueError("stage/post mode requires --baseline-tsv")
    validate_baseline_identity(args.baseline_tsv)
    baseline_declarations = core.read_dependency_declarations(args.baseline_tsv)
    baseline = selected_baseline(baseline_declarations)
    records = read_and_validate_manifest(args.manifest, baseline)
    if args.routes is not None:
        generated = core.generate_manifest(
            baseline, args.routes, args.project_root, ilean_overrides
        )
        if generated != records:
            raise ValueError(
                "tracked sibling ownership manifest differs from reviewed "
                "route generation"
            )
    validate_contract_inputs(
        args.manifest,
        args.routes,
        args.private_rewrites,
        args.structural_contract,
        args.parent_phase12_structural_contract,
        args.expanded_phase12_structural_contract,
    )
    rewrites = core.read_private_rewrites(
        args.private_rewrites, records, baseline
    )

    all_destinations = set(DESTINATION_COUNTS)
    if args.mode == "stage":
        completed = read_completed_destinations(args)
        if not completed:
            raise ValueError("stage mode requires completed destinations")
        unknown = sorted(completed - all_destinations)
        if unknown:
            raise ValueError(
                "completed destinations are outside the contract: "
                + ", ".join(unknown)
            )
    else:
        if args.completed_destination or args.completed_destinations is not None:
            raise ValueError(
                "completed-destination options are valid only in stage mode"
            )
        completed = all_destinations

    baseline_actual_to_logical = core.baseline_actual_to_logical(baseline)
    core.validate_destination_graph(
        args.baseline_tsv,
        baseline_declarations,
        baseline_actual_to_logical,
        records,
    )
    candidate_declarations = core.read_dependency_declarations(
        args.dependency_tsv
    )
    candidate_actual_to_logical = core.check_candidate_ownership(
        records,
        baseline,
        candidate_declarations,
        rewrites,
        completed,
    )
    destination_nodes, destination_edges = core.validate_destination_graph(
        args.dependency_tsv,
        candidate_declarations,
        candidate_actual_to_logical,
        records,
    )
    if (
        destination_nodes != EXPECTED_DESTINATION_NODES
        or destination_edges != EXPECTED_DESTINATION_EDGES
    ):
        raise ValueError(
            "candidate destination DAG size differs from the frozen contract"
        )
    validate_selected_edge_contract(
        args.dependency_tsv,
        candidate_declarations,
        candidate_actual_to_logical,
        records,
    )

    ready_wrappers, ready_structural_modules = completed_structural_modules(
        records, completed
    )
    ready_contract = {
        module: structural_contract[module]
        for module in ready_structural_modules
    }
    core.validate_structural_modules(
        args.project_root,
        candidate_declarations,
        ready_structural_modules,
        ready_contract,
    )
    if all_destinations <= completed:
        validate_post_integration_structures(
            args.project_root,
            candidate_declarations,
            args.phase12_structural_contract,
            args.expanded_phase12_structural_contract,
        )

    # Empty reviewed-drop set is intentional and non-configurable.
    core.compare_full_graph(
        args.baseline_tsv,
        args.dependency_tsv,
        baseline,
        candidate_actual_to_logical,
        records,
        frozenset(),
    )

    completed_logicals = sum(
        row.destination_module in completed for row in records.values()
    )
    mode_label = "staged" if args.mode == "stage" else "post-migration"
    integration_clause = (
        ", complete 170-pair composed structural surface verified"
        if all_destinations <= completed
        else ""
    )
    print(
        f"BlockLU Phase 12 sibling {mode_label} ownership passed: "
        f"{completed_logicals} of {len(records)} declarations moved across "
        f"{len(completed)} destinations, {len(ready_wrappers)} historical "
        f"wrappers verified{integration_clause}, acyclic "
        f"{destination_nodes}-destination graph, "
        "and exact normalized graph preserved with zero edge drops"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
