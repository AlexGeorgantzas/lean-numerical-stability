#!/usr/bin/env python3
"""Generate and check the least-squares / Chapter 20 semantic ownership partition.

The lane migrates the 42 historical ``NumStability.Algorithms.LeastSquares``
modules into three reviewed roots:

* ``NumStability.Algorithms.LinearSystems.LeastSquares`` — source-neutral
  least-squares specifications and algorithms;
* ``NumStability.Analysis.Perturbation.LeastSquares`` — source-neutral
  perturbation and error analysis;
* ``NumStability.Source.Higham.Chapter20`` — numbered results, named prose,
  printed examples, corrections, execution traces, and capstones.

The ownership manifest has the following tab-separated schema::

    format\t1
    logical_name\thistorical_module\tdestination_module\tkind\tvisibility

Manifest generation is driven by a separately reviewed format-2 route map.
Every selected declaration has one row naming its authoritative compiler
source-command root, all eight coordinates from that root's ``.ilean`` entry,
and the SHA-256 of the exact LF-normalized command text.  Compiler-generated
declarations name the authored root that generated them.  Rows sharing a
compiler span must share one destination.  There is no exact-route escape
hatch that can bypass compiler spans.

Lean private names encode their owning module and therefore necessarily change
when a declaration moves.  Stage and post modes require an explicit companion
map for every private declaration owned by a completed destination::

    format\t1
    logical_name\thistorical_actual_name\tcandidate_actual_name

Only those reviewed private-name rewrites are normalized during the exact
LS-incident graph comparison.  That graph contains every selected LS
declaration and every typed edge with at least one selected LS endpoint;
declaration moves wholly outside the lane are intentionally outside this
worker's contract.

The lane additionally freezes the 19 ``LS_TO_QR`` and four ``QR_TO_LS`` base
edges together with their final canonical normalization.  A deliberately
unresolved QR-owner token is accepted as contract data in pre/stage mode but
cannot be resolved without a separately hash-pinned QR handoff covering all 68
declaration identities and the import-only carrier.  Post requires that
handoff and exact resolution of every placeholder.  This prevents either lane
from guessing the other lane's final owner while also preventing
compatibility-wrapper imports from surviving in production after integration.

Proposed tiers live in a lane-owned manifest because the global
``docs/architecture/tiers.json`` registration is integrator-owned::

    format\t1
    module\ttier

``tier`` is one of ``reusable``, ``source``, or ``compatibility``.  A lane
production module classified ``mixed`` is rejected outright.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import sys
import tempfile
from collections import Counter, defaultdict, deque
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Callable, Iterable

LS_PREFIX = "NumStability.Algorithms.LeastSquares"
REUSABLE_ALGORITHM_ROOT = "NumStability.Algorithms.LinearSystems.LeastSquares"
REUSABLE_ANALYSIS_ROOT = "NumStability.Analysis.Perturbation.LeastSquares"
SOURCE_ROOT = "NumStability.Source.Higham.Chapter20"
HIGHAM_COMPAT_ROOT = "NumStability.Higham.Chapter20"
CHAPTER_SEVEN = "NumStability.Analysis.HighamChapter7"

REUSABLE_DESTINATION_PREFIXES = (
    REUSABLE_ALGORITHM_ROOT + ".",
    REUSABLE_ANALYSIS_ROOT + ".",
)
SOURCE_DESTINATION_PREFIX = SOURCE_ROOT + "."
QR_SOURCE_PREFIX = "NumStability.Source.Higham.Chapter19."
QR_CANONICAL_RETARGETS = {
    "NumStability.Algorithms.QR.HouseholderApply":
        "NumStability.Algorithms.LinearSystems.QR.HouseholderApply",
    "NumStability.Algorithms.QR.HouseholderQRSupport":
        "NumStability.Algorithms.LinearSystems.QR.HouseholderQRSupport",
    "NumStability.Algorithms.QR.GramSchmidtPolar":
        "NumStability.Algorithms.LinearSystems.QR.GramSchmidtPolar",
    "NumStability.Algorithms.QR.QRSolve":
        "NumStability.Algorithms.LinearSystems.QR.QRSolve",
}
# Reviewed pre-reorganization dependencies of the canonical Conditioning
# module.  These roots belong to the preserved Chapter 21 / Chapter 7 work;
# they are deliberately exact rather than a general cross-chapter exemption.
PRESERVED_LSQ_SOURCE_IMPORTS = frozenset(
    {
        (
            "NumStability.Analysis.Perturbation.LeastSquares.Conditioning",
            "NumStability.Analysis.HighamChapter7",
        ),
        (
            "NumStability.Analysis.Perturbation.LeastSquares.Conditioning",
            "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve",
        ),
        (
            "NumStability.Analysis.Perturbation.LeastSquares.Conditioning",
            "NumStability.Source.Higham.Chapter21.RowScalingInvariance",
        ),
    }
)

# Frozen historical declaration counts at base
# 6487fc33088523b8f27ecde9ad613515b78f9977.  Higham20SourceAliases is the
# already-compatibility member of the family and owns no declaration, so it is
# a structural module rather than a historical owner.
EXPECTED_HISTORICAL_COUNTS = {
    f"{LS_PREFIX}.Higham20Algorithms": 86,
    f"{LS_PREFIX}.Higham20AlternativeBound": 14,
    f"{LS_PREFIX}.Higham20CrossProductExample": 12,
    f"{LS_PREFIX}.Higham20EliminationActual": 63,
    f"{LS_PREFIX}.Higham20Equations": 26,
    f"{LS_PREFIX}.Higham20ExampleCondition": 9,
    f"{LS_PREFIX}.Higham20GeneralWedin": 32,
    f"{LS_PREFIX}.Higham20Lemma20_11": 20,
    f"{LS_PREFIX}.Higham20Lemma20_12": 8,
    f"{LS_PREFIX}.Higham20MGSStability": 31,
    f"{LS_PREFIX}.Higham20MPProse": 16,
    f"{LS_PREFIX}.Higham20MinimumNormBackwardError": 22,
    f"{LS_PREFIX}.Higham20NormalEquationsNorms": 15,
    f"{LS_PREFIX}.Higham20Problem20_3": 21,
    f"{LS_PREFIX}.Higham20Prose": 27,
    f"{LS_PREFIX}.Higham20QuantitativeProse": 6,
    f"{LS_PREFIX}.Higham20Refinement": 52,
    f"{LS_PREFIX}.Higham20Remaining": 15,
    f"{LS_PREFIX}.Higham20ResidualQuality": 27,
    f"{LS_PREFIX}.Higham20RowSorting": 78,
    f"{LS_PREFIX}.Higham20Theorem20_10": 23,
    f"{LS_PREFIX}.Higham20Theorem20_3": 8,
    f"{LS_PREFIX}.Higham20Theorem20_4Absorption": 21,
    f"{LS_PREFIX}.Higham20Theorem20_7": 150,
    f"{LS_PREFIX}.Higham20Theorem20_7ActualAssembly": 79,
    f"{LS_PREFIX}.Higham20Theorem20_7ActualBackSub": 34,
    f"{LS_PREFIX}.Higham20Theorem20_7ActualClosure": 30,
    f"{LS_PREFIX}.Higham20Theorem20_7ActualGrowth": 4,
    f"{LS_PREFIX}.Higham20Theorem20_7ActualRhs": 26,
    f"{LS_PREFIX}.Higham20Theorem20_7ActualTrace": 49,
    f"{LS_PREFIX}.Higham20Theorem20_7Contract": 143,
    f"{LS_PREFIX}.Higham20Theorem20_7QdR": 43,
    f"{LS_PREFIX}.Higham20Theorem20_7Runtime": 20,
    f"{LS_PREFIX}.Higham20Theorem20_7SourceTrace": 54,
    f"{LS_PREFIX}.Higham20Theorem20_8": 41,
    f"{LS_PREFIX}.Higham20WeightedLimit": 10,
    f"{LS_PREFIX}.Higham20ZeroDeltaB": 50,
    f"{LS_PREFIX}.LSE": 1982,
    f"{LS_PREFIX}.LSNormalEquations": 38,
    f"{LS_PREFIX}.LSPerturbation": 259,
    f"{LS_PREFIX}.LSQRSolve": 1485,
}
EXPECTED_MANIFEST_ROWS = sum(EXPECTED_HISTORICAL_COUNTS.values())
EXPECTED_PRIVATE_ROWS = 151
EXPECTED_CROSS_LANE_ROWS = 4224
EXPECTED_CROSS_LANE_EDGE_ROWS = 4221
EXPECTED_CROSS_LANE_IMPORT_ROWS = 3
EXPECTED_QR_HANDOFF_ROWS = 69

# The declaration-free members of the historical family and the pre-existing
# canonical Chapter 20 leaves.  These modules are checked as import-only
# wrappers or aggregates once the lane declares them complete.
REUSABLE_ALGORITHM_UMBRELLA = REUSABLE_ALGORITHM_ROOT
REUSABLE_ANALYSIS_UMBRELLA = REUSABLE_ANALYSIS_ROOT

HISTORICAL_DECLARATION_WRAPPERS = frozenset(EXPECTED_HISTORICAL_COUNTS)
BASE_COMPATIBILITY_WRAPPERS = frozenset(
    {
        f"{LS_PREFIX}.Higham20SourceAliases",
        f"{HIGHAM_COMPAT_ROOT}.SourceAliases",
    }
)
ALL_COMPATIBILITY_WRAPPERS = (
    HISTORICAL_DECLARATION_WRAPPERS | BASE_COMPATIBILITY_WRAPPERS
)

DEFAULT_STRUCTURAL_MODULES = set(ALL_COMPATIBILITY_WRAPPERS) | {
    SOURCE_ROOT,
    REUSABLE_ALGORITHM_UMBRELLA,
    REUSABLE_ANALYSIS_UMBRELLA,
}

PRESERVED_SOURCE_LEAVES = {
    f"{SOURCE_ROOT}.Equation32",
    f"{SOURCE_ROOT}.Lemma06",
    f"{SOURCE_ROOT}.Theorem01",
}

# Exactly the 19 LS_TO_QR rows of KNOWN_CROSS_LANE_EDGES.tsv.
FROZEN_LS_TO_QR = frozenset(
    {
        (f"{LS_PREFIX}.Higham20MGSStability", "NumStability.Algorithms.QR.Higham19"),
        (
            f"{LS_PREFIX}.Higham20MGSStability",
            "NumStability.Algorithms.QR.Higham19Alg12MGSRounded",
        ),
        (
            f"{LS_PREFIX}.Higham20MGSStability",
            "NumStability.Algorithms.QR.Higham19Alg12MGSRepair",
        ),
        (f"{LS_PREFIX}.Higham20Theorem20_3", "NumStability.Algorithms.QR.Higham19"),
        (
            f"{LS_PREFIX}.Higham20Theorem20_7",
            "NumStability.Algorithms.QR.Higham19Thm6CoxHigham",
        ),
        (
            f"{LS_PREFIX}.Higham20Theorem20_7",
            "NumStability.Algorithms.QR.Higham19Thm6CoxHighamConcrete",
        ),
        (
            f"{LS_PREFIX}.Higham20Theorem20_7",
            "NumStability.Algorithms.QR.HouseholderApply",
        ),
        (
            f"{LS_PREFIX}.Higham20Theorem20_7",
            "NumStability.Algorithms.QR.HouseholderQRSupport",
        ),
        (
            f"{LS_PREFIX}.Higham20Theorem20_7Contract",
            "NumStability.Algorithms.QR.Higham19Thm6RowSpecific",
        ),
        (
            f"{LS_PREFIX}.Higham20ZeroDeltaB",
            "NumStability.Algorithms.QR.Higham19Labels",
        ),
        (f"{LS_PREFIX}.LSQRSolve", "NumStability.Algorithms.QR.QRSolve"),
        (f"{LS_PREFIX}.LSQRSolve", "NumStability.Algorithms.QR.HouseholderQRSupport"),
        (f"{LS_PREFIX}.LSE", "NumStability.Algorithms.QR.GramSchmidtPolar"),
        (f"{LS_PREFIX}.LSE", "NumStability.Algorithms.QR.Higham19"),
        (
            f"{LS_PREFIX}.LSE",
            "NumStability.Algorithms.QR.Higham19Thm6ElementwisePackaged",
        ),
        (f"{LS_PREFIX}.LSE", "NumStability.Algorithms.QR.Higham19Thm6RowSpecific"),
        (f"{LS_PREFIX}.LSE", "NumStability.Algorithms.QR.Higham19Thm6CoxHigham"),
        (
            f"{LS_PREFIX}.LSE",
            "NumStability.Algorithms.QR.Higham19Thm6CoxHighamConcrete",
        ),
        (f"{LS_PREFIX}.LSE", "NumStability.Algorithms.QR.Higham19Thm6ColPivot"),
    }
)

# Exactly the four QR_TO_LS rows of KNOWN_CROSS_LANE_EDGES.tsv.
FROZEN_QR_TO_LS = frozenset(
    {
        (
            "NumStability.Algorithms.QR.Higham19Alg12MGSSourceRate",
            f"{LS_PREFIX}.Higham20MPProse",
        ),
        (
            "NumStability.Algorithms.QR.Higham19Problem19_10",
            f"{LS_PREFIX}.Higham20CrossProductExample",
        ),
        (
            "NumStability.Algorithms.QR.Higham19Theorem5SourceClosure",
            f"{LS_PREFIX}.Higham20ZeroDeltaB",
        ),
        (
            "NumStability.Algorithms.QR.Higham19Theorem6ActualSource",
            f"{LS_PREFIX}.Higham20Theorem20_7ActualAssembly",
        ),
    }
)

# These three frozen direct imports have no typed declaration edge in the base
# stream.  Their canonical carrier is therefore an explicit reviewed choice,
# not something inferred by the checker.
IMPORT_ONLY_LS_DESTINATIONS = {
    (
        f"{LS_PREFIX}.Higham20Theorem20_7",
        "NumStability.Algorithms.QR.HouseholderQRSupport",
    ): f"{SOURCE_ROOT}.Theorem07",
    # Carrier is Equality.GQR: the generalized-QR material is what uses the QR
    # lane's Gram-Schmidt polar factorization, so the import belongs with it.
    #
    # This was briefly retargeted to Equality.Basic on the theory that Equality.GQR
    # could not exist while private visibility was preserved.  That was wrong: of
    # 708 declarations intended for Basic/GQR/KKT only 2 co-location components
    # straddle the split, and confining those two leaves Basic and GQR both
    # non-empty with zero cross-module private uses.  GQR is restored, so the
    # carrier returns with it.
    (
        f"{LS_PREFIX}.LSE",
        "NumStability.Algorithms.QR.GramSchmidtPolar",
    ): f"{REUSABLE_ALGORITHM_ROOT}.Equality.GQR",
    (
        "NumStability.Algorithms.QR.Higham19Alg12MGSSourceRate",
        f"{LS_PREFIX}.Higham20MPProse",
    ): f"{SOURCE_ROOT}.Prose.MoorePenrose",
}

BASELINE_TSV_SHA256 = (
    "32ADA469E27A971E9B0BB972F29C51E1DCBE99104A1492D4C69549C339825563"
)

OWNERSHIP_DIR = Path("docs/architecture/declaration-ownership")
DEFAULT_MANIFEST = OWNERSHIP_DIR / "lsq-ch20-ownership.tsv"
DEFAULT_ROUTES = OWNERSHIP_DIR / "lsq-ch20-routes.tsv"
DEFAULT_PRIVATE_REWRITES = OWNERSHIP_DIR / "lsq-ch20-private-rewrites.tsv"
DEFAULT_TIERS = OWNERSHIP_DIR / "lsq-ch20-tiers.tsv"
DEFAULT_FROZEN_OWNERS = OWNERSHIP_DIR / "lsq-ch20-frozen-owners.tsv"
DEFAULT_STRUCTURAL_IMPORTS = OWNERSHIP_DIR / "lsq-ch20-structural-imports.tsv"
DEFAULT_DESTINATION_DAG = OWNERSHIP_DIR / "lsq-ch20-destination-dag.tsv"
DEFAULT_CROSS_LANE = OWNERSHIP_DIR / "lsq-ch20-cross-lane-normalization.tsv"
DEFAULT_COORDINATOR_PATCHES = OWNERSHIP_DIR / "lsq-ch20-coordinator-patches.tsv"

COORDINATOR_CONSUMER_FINAL_IMPORTS = {
    "NumStability.Algorithms": {
        REUSABLE_ALGORITHM_UMBRELLA,
        REUSABLE_ANALYSIS_UMBRELLA,
        SOURCE_ROOT,
    },
    "NumStability.Algorithms.MatrixInversion": {
        f"{REUSABLE_ANALYSIS_ROOT}.Wedin",
    },
    "NumStability.Algorithms.RandNLA.LeastSquaresSketch": {
        f"{REUSABLE_ALGORITHM_ROOT}.Basic",
        f"{REUSABLE_ALGORITHM_ROOT}.NormalEquations",
        f"{REUSABLE_ALGORITHM_ROOT}.StoredQR",
        f"{REUSABLE_ANALYSIS_ROOT}.BackwardError",
        f"{REUSABLE_ANALYSIS_ROOT}.Basic",
        f"{REUSABLE_ANALYSIS_ROOT}.NormalEquations",
        f"{SOURCE_ROOT}.Theorem03.QRSolve",
    },
    "NumStability.Algorithms.Underdetermined.UnderdeterminedSolve": {
        f"{REUSABLE_ALGORITHM_ROOT}.Basic",
        f"{REUSABLE_ALGORITHM_ROOT}.RankGeometry",
        f"{REUSABLE_ANALYSIS_ROOT}.Normwise",
        f"{REUSABLE_ANALYSIS_ROOT}.Wedin",
        f"{SOURCE_ROOT}.Theorem03.QRSolve",
    },
    "NumStability.Source.Higham.Chapter14.Section05.SpectralConvergence": {
        f"{SOURCE_ROOT}.Problem03",
    },
}

ROOT_TEST_IMPORTS = {
    "NumStabilityTest.Import.Algorithms.LinearSystems.LeastSquares",
    "NumStabilityTest.Import.Analysis.Perturbation.LeastSquares",
    "NumStabilityTest.Import.Compatibility.Algorithms.LeastSquares",
}

LANE_PRESERVED_FINAL_IMPORTS = {
    f"{SOURCE_ROOT}.Equation32": {
        f"{REUSABLE_ANALYSIS_ROOT}.Wedin",
    },
    f"{SOURCE_ROOT}.Lemma06": {
        f"{REUSABLE_ALGORITHM_ROOT}.AugmentedSystem",
        f"{REUSABLE_ALGORITHM_ROOT}.Basic",
        f"{SOURCE_ROOT}.Theorem03.QRSolve",
    },
    f"{SOURCE_ROOT}.Theorem01": {
        f"{REUSABLE_ANALYSIS_ROOT}.Wedin",
        f"{SOURCE_ROOT}.Lemma11.Support",
    },
}

HEX_SHA256 = re.compile(r"^[0-9A-Fa-f]{64}$")
MODULE_NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$")
EDGE_KINDS = {"body", "signature"}
TIERS = {"reusable", "source", "compatibility"}
IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+([A-Za-z_][A-Za-z0-9_.]*)\s*$")
COMMAND_PROVENANCE = {"authored", "compiler_generated"}
CROSS_LANE_DIRECTIONS = {"LS_TO_QR", "QR_TO_LS"}
CROSS_LANE_STATUS = {"resolved", "qr_owner_required"}
QR_OWNER_PLACEHOLDER = re.compile(r"^@QR_OWNER_REQUIRED:[A-Za-z_][A-Za-z0-9_.]*$")
GIT_COMMIT_SHA = re.compile(r"^[0-9A-Fa-f]{40}$")


@dataclass(frozen=True)
class Declaration:
    name: str
    module: str
    kind: str
    visibility: str


@dataclass(frozen=True)
class ManifestRow:
    logical_name: str
    historical_module: str
    destination_module: str
    kind: str
    visibility: str


@dataclass(frozen=True)
class RangeRoute:
    historical_module: str
    first_line: int
    last_line: int
    destination_module: str


@dataclass(frozen=True)
class CommandRoute:
    historical_module: str
    logical_name: str
    historical_actual_name: str
    command_root_logical: str
    command_root_actual_name: str
    provenance: str
    start_line: int
    start_col: int
    end_line: int
    end_col: int
    selection_start_line: int
    selection_start_col: int
    selection_end_line: int
    selection_end_col: int
    command_sha256: str
    destination_module: str

    @property
    def span(self) -> tuple[int, int, int, int, int, int, int, int]:
        return (
            self.start_line,
            self.start_col,
            self.end_line,
            self.end_col,
            self.selection_start_line,
            self.selection_start_col,
            self.selection_end_line,
            self.selection_end_col,
        )


@dataclass(frozen=True)
class FrozenOwner:
    module: str
    path: str
    git_blob: str
    source_sha256: str
    physical_lines: int
    nonblank_lines: int
    ilean_sha256: str
    ilean_bytes: int


@dataclass(frozen=True)
class CrossLaneNormalization:
    row_type: str
    direction: str
    edge_kind: str
    base_source_module: str
    base_source_name: str
    base_target_module: str
    base_target_name: str
    ls_destination: str
    qr_owner: str
    status: str


@dataclass(frozen=True)
class PrivateRewrite:
    logical_name: str
    historical_actual_name: str
    candidate_actual_name: str


@dataclass(frozen=True)
class DependencyEdge:
    kind: str
    source: str
    target: str


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def check_module_name(module: str, context: str) -> None:
    if not MODULE_NAME.fullmatch(module):
        raise ValueError(f"{context}: invalid Lean module name {module!r}")


def private_suffix(actual_name: str, actual_module: str) -> str:
    """Return the stable part of a Lean private name, dropping the ordinal.

    A Lean private name encodes both its owning module and an unstable
    per-scope ordinal.  Only the ordinal is genuinely volatile, so it is the
    only component removed here.
    """

    prefix = f"_private.{actual_module}."
    if not actual_name.startswith(prefix):
        raise ValueError(
            f"private name {actual_name!r} does not encode owner {actual_module!r}"
        )
    ordinal, separator, suffix = actual_name[len(prefix) :].partition(".")
    if not separator or not ordinal.isdigit() or not suffix:
        raise ValueError(f"unexpected Lean private name: {actual_name}")
    return suffix


def logical_name(actual_name: str, actual_module: str) -> str:
    """Normalize only the scope ordinal in a Lean private name.

    The owning module is retained.  This lane migrates 42 historical owners and
    the same private helper suffix occurs in more than one of them, so dropping
    the module would collapse distinct declarations onto one key.  Keeping the
    historical module makes the logical name both unique and stable, because a
    declaration's historical owner never changes.
    """

    if not actual_name.startswith("_private."):
        return actual_name
    return f"_private.{actual_module}.{private_suffix(actual_name, actual_module)}"


def read_dependency_declarations(path: Path) -> list[Declaration]:
    declarations: list[Declaration] = []
    names: set[str] = set()
    saw_format = False
    with path.open(encoding="utf-8", newline="") as stream:
        for line_number, row in enumerate(csv.reader(stream, delimiter="\t"), 1):
            if not row:
                continue
            if row == ["format", "2"]:
                if saw_format or declarations or line_number != 1:
                    raise ValueError(
                        f"{path}:{line_number}: misplaced or duplicate format row"
                    )
                saw_format = True
            elif row[0] == "declaration" and len(row) == 5:
                if not saw_format:
                    raise ValueError(f"{path}: declaration precedes format row")
                declaration = Declaration(*row[1:])
                if not all(
                    (
                        declaration.name,
                        declaration.module,
                        declaration.kind,
                        declaration.visibility,
                    )
                ):
                    raise ValueError(f"{path}:{line_number}: empty declaration field")
                if declaration.name in names:
                    raise ValueError(
                        f"{path}:{line_number}: duplicate declaration "
                        f"{declaration.name}"
                    )
                names.add(declaration.name)
                declarations.append(declaration)
            elif row[0] == "edge" and len(row) == 4:
                if not saw_format or row[1] not in EDGE_KINDS or not all(row[2:]):
                    raise ValueError(f"{path}:{line_number}: malformed edge row")
            else:
                raise ValueError(
                    f"{path}:{line_number}: malformed dependency row {row!r}"
                )
    if not saw_format:
        raise ValueError(f"{path}: dependency TSV must start with 'format\\t2'")
    return declarations


def iter_dependency_edges(path: Path) -> Iterable[DependencyEdge]:
    """Stream already schema-validated typed edges from a dependency TSV."""

    saw_format = False
    with path.open(encoding="utf-8", newline="") as stream:
        for line_number, row in enumerate(csv.reader(stream, delimiter="\t"), 1):
            if not row:
                continue
            if row == ["format", "2"]:
                if saw_format or line_number != 1:
                    raise ValueError(
                        f"{path}:{line_number}: misplaced or duplicate format row"
                    )
                saw_format = True
            elif row[0] == "declaration" and len(row) == 5:
                if not saw_format or not all(row[1:]):
                    raise ValueError(f"{path}:{line_number}: malformed declaration row")
            elif row[0] == "edge" and len(row) == 4:
                if not saw_format or row[1] not in EDGE_KINDS or not all(row[2:]):
                    raise ValueError(f"{path}:{line_number}: malformed edge row")
                yield DependencyEdge(*row[1:])
            else:
                raise ValueError(
                    f"{path}:{line_number}: malformed dependency row {row!r}"
                )
    if not saw_format:
        raise ValueError(f"{path}: dependency TSV must start with 'format\\t2'")


def selected_baseline_declarations(
    declarations: Iterable[Declaration],
    expected_counts: dict[str, int] | None = None,
) -> dict[str, Declaration]:
    counts = EXPECTED_HISTORICAL_COUNTS if expected_counts is None else expected_counts
    records: dict[str, Declaration] = {}
    raw_counts: Counter[str] = Counter()

    for declaration in declarations:
        if declaration.module not in counts:
            continue
        logical = logical_name(declaration.name, declaration.module)
        if logical in records:
            raise ValueError(f"duplicate selected logical name: {logical}")
        records[logical] = declaration
        raw_counts[declaration.module] += 1

    if raw_counts != Counter(counts):
        missing = {m: c for m, c in counts.items() if raw_counts[m] != c}
        raise ValueError(
            "historical declaration counts differ from the frozen lane selection: "
            f"{ {m: (counts[m], raw_counts[m]) for m in sorted(missing)} }"
        )
    if len(records) != sum(counts.values()):
        raise ValueError(
            f"expected {sum(counts.values())} selected declarations, found {len(records)}"
        )
    return records


def manifest_bytes(records: dict[str, ManifestRow]) -> bytes:
    rows = ["format\t1"]
    rows.extend(
        "\t".join(
            (
                row.logical_name,
                row.historical_module,
                row.destination_module,
                row.kind,
                row.visibility,
            )
        )
        for _, row in sorted(records.items())
    )
    return ("\n".join(rows) + "\n").encode("utf-8")


def destination_role(module: str) -> str:
    if module.startswith(REUSABLE_DESTINATION_PREFIXES):
        return "reusable"
    if module.startswith(SOURCE_DESTINATION_PREFIX):
        return "source"
    raise ValueError(
        "lane destination is outside the reviewed reusable/source roots: " f"{module}"
    )


def validate_manifest_shape(
    records: dict[str, ManifestRow],
    expected_counts: dict[str, int] | None = None,
) -> None:
    counts_contract = (
        EXPECTED_HISTORICAL_COUNTS if expected_counts is None else expected_counts
    )
    expected_rows = sum(counts_contract.values())
    if len(records) != expected_rows:
        raise ValueError(
            f"expected {expected_rows} ownership rows, found {len(records)}"
        )
    counts = Counter(row.historical_module for row in records.values())
    if counts != Counter(counts_contract):
        raise ValueError(
            f"manifest historical-owner counts differ: expected {counts_contract}, "
            f"found {dict(counts)}"
        )

    for logical, row in records.items():
        if logical != row.logical_name or not logical:
            raise ValueError(f"invalid manifest logical name: {logical!r}")
        check_module_name(row.historical_module, logical)
        check_module_name(row.destination_module, logical)
        if row.historical_module not in counts_contract:
            raise ValueError(
                f"{logical}: unexpected historical owner {row.historical_module}"
            )
        if row.destination_module in counts_contract:
            raise ValueError(
                f"{logical}: destination remains a historical owner: "
                f"{row.destination_module}"
            )
        if row.destination_module.startswith(LS_PREFIX + "."):
            raise ValueError(
                f"{logical}: destination stays inside the legacy family: "
                f"{row.destination_module}"
            )
        destination_role(row.destination_module)
        if not row.kind or not row.visibility:
            raise ValueError(f"{logical}: empty kind or visibility")
        if row.visibility == "private" and not logical.startswith(
            f"_private.{row.historical_module}."
        ):
            raise ValueError(
                f"{logical}: private declaration must be keyed by its historical owner "
                f"{row.historical_module}"
            )
        if row.visibility != "private" and logical.startswith("_private."):
            raise ValueError(
                f"{logical}: private-shaped name has visibility {row.visibility}"
            )


def read_manifest(
    path: Path, expected_counts: dict[str, int] | None = None
) -> dict[str, ManifestRow]:
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["format", "1"]:
        raise ValueError(f"{path}: manifest must start with 'format\\t1'")
    if any(not row for row in rows):
        raise ValueError(f"{path}: blank manifest rows are not allowed")

    records: dict[str, ManifestRow] = {}
    order: list[str] = []
    for line_number, row in enumerate(rows[1:], 2):
        if len(row) != 5:
            raise ValueError(
                f"{path}:{line_number}: expected five manifest columns, got {row!r}"
            )
        record = ManifestRow(*row)
        if record.logical_name in records:
            raise ValueError(
                f"{path}:{line_number}: duplicate logical name {record.logical_name}"
            )
        records[record.logical_name] = record
        order.append(record.logical_name)
    if order != sorted(order):
        raise ValueError(f"{path}: ownership rows must be sorted by logical name")
    validate_manifest_shape(records, expected_counts)
    return records


def write_manifest(
    path: Path,
    records: dict[str, ManifestRow],
    expected_counts: dict[str, int] | None = None,
) -> None:
    validate_manifest_shape(records, expected_counts)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(manifest_bytes(records))


def validate_manifest_against_baseline(
    records: dict[str, ManifestRow],
    baseline: dict[str, Declaration],
) -> None:
    if set(records) != set(baseline):
        missing = sorted(set(baseline) - set(records))
        extra = sorted(set(records) - set(baseline))
        raise ValueError(
            "manifest does not exactly cover the frozen selection: "
            f"missing={missing[:20]}; extra={extra[:20]}"
        )
    for logical, expected in records.items():
        actual = baseline[logical]
        expected_metadata = (
            expected.historical_module,
            expected.kind,
            expected.visibility,
        )
        actual_metadata = (actual.module, actual.kind, actual.visibility)
        if actual_metadata != expected_metadata:
            raise ValueError(
                f"{logical}: manifest expects {expected_metadata}, "
                f"baseline has {actual_metadata}"
            )


def default_ilean_path(project_root: Path, module: str) -> Path:
    return project_root / ".lake/build/lib/lean" / (module.replace(".", "/") + ".ilean")


def parse_ilean_overrides(values: list[str]) -> dict[str, Path]:
    result: dict[str, Path] = {}
    for value in values:
        module, separator, raw_path = value.partition("=")
        if not separator or not module or not raw_path:
            raise ValueError(f"invalid --ilean {value!r}; expected HISTORICAL_MODULE=PATH")
        if module in result:
            raise ValueError(f"duplicate --ilean override for {module}")
        check_module_name(module, "--ilean")
        result[module] = Path(raw_path)
    return result


def read_ilean_entries(
    path: Path, expected_module: str
) -> dict[str, tuple[int, int, int, int, int, int, int, int]]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as error:
        raise ValueError(f"invalid .ilean JSON {path}: {error}") from error
    actual_module = payload.get("module")
    if actual_module != expected_module:
        raise ValueError(
            f"{path}: expected .ilean owner {expected_module}, found {actual_module!r}"
        )
    decls = payload.get("decls")
    if not isinstance(decls, dict):
        raise ValueError(f"{path}: .ilean lacks a declaration map")
    roots: dict[str, tuple[int, int, int, int, int, int, int, int]] = {}
    for name, source_range in decls.items():
        if (
            not isinstance(name, str)
            or not isinstance(source_range, list)
            or len(source_range) != 8
            or any(not isinstance(value, int) for value in source_range)
        ):
            raise ValueError(f"{path}: malformed declaration source range")
        span = tuple(source_range)
        if any(value < 0 for value in span):
            raise ValueError(f"{path}: negative declaration source coordinate")
        if (span[2], span[3]) < (span[0], span[1]):
            raise ValueError(f"{path}: reversed declaration source range")
        roots[name] = span
    return roots


def normalized_source_bytes(path: Path) -> bytes:
    return path.read_bytes().replace(b"\r\n", b"\n").replace(b"\r", b"\n")


def source_command_bytes(
    payload: bytes, span: tuple[int, int, int, int, int, int, int, int]
) -> bytes:
    """Slice one compiler command using Lean's zero-based UTF-8 coordinates."""

    start_line, start_col, end_line, end_col = span[:4]
    lines = payload.splitlines(keepends=True)
    if not lines:
        lines = [b""]
    offsets = [0]
    for line in lines:
        offsets.append(offsets[-1] + len(line))

    def offset(line: int, column: int) -> int:
        if line == len(lines) and column == 0:
            return len(payload)
        if line >= len(lines):
            raise ValueError(
                f"compiler source coordinate line {line} exceeds {len(lines)} lines"
            )
        line_payload = lines[line]
        content_length = len(line_payload.rstrip(b"\n"))
        if column > content_length:
            raise ValueError(
                f"compiler source coordinate column {column} exceeds line length "
                f"{content_length} on line {line}"
            )
        return offsets[line] + column

    start = offset(start_line, start_col)
    end = offset(end_line, end_col)
    if end <= start:
        raise ValueError(f"empty or reversed compiler command span {span}")
    return payload[start:end]


def read_frozen_owners(path: Path) -> dict[str, FrozenOwner]:
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["format", "1"]:
        raise ValueError(f"{path}: frozen owners must start with 'format\\t1'")
    owners: dict[str, FrozenOwner] = {}
    order: list[str] = []
    for line_number, row in enumerate(rows[1:], 2):
        if len(row) != 8:
            raise ValueError(f"{path}:{line_number}: expected eight owner columns")
        module, source_path, git_blob, source_hash, physical, nonblank, ilean_hash, ilean_bytes = row
        check_module_name(module, f"{path}:{line_number}")
        if module in owners:
            raise ValueError(f"{path}:{line_number}: duplicate owner {module}")
        if not re.fullmatch(r"[0-9A-Fa-f]{40}", git_blob):
            raise ValueError(f"{path}:{line_number}: invalid Git blob ID")
        if not HEX_SHA256.fullmatch(source_hash):
            raise ValueError(f"{path}:{line_number}: invalid source SHA-256")
        if ilean_hash != "-" and not HEX_SHA256.fullmatch(ilean_hash):
            raise ValueError(f"{path}:{line_number}: invalid .ilean SHA-256")
        try:
            physical_count = int(physical)
            nonblank_count = int(nonblank)
            ilean_size = int(ilean_bytes)
        except ValueError as error:
            raise ValueError(f"{path}:{line_number}: invalid numeric owner field") from error
        if physical_count < 1 or not (0 <= nonblank_count <= physical_count):
            raise ValueError(f"{path}:{line_number}: invalid source line counts")
        if (ilean_hash == "-") != (ilean_size == 0):
            raise ValueError(f"{path}:{line_number}: inconsistent missing .ilean marker")
        owners[module] = FrozenOwner(
            module,
            source_path,
            git_blob.lower(),
            source_hash.upper(),
            physical_count,
            nonblank_count,
            ilean_hash.upper() if ilean_hash != "-" else "-",
            ilean_size,
        )
        order.append(module)
    expected = set(EXPECTED_HISTORICAL_COUNTS) | {f"{LS_PREFIX}.Higham20SourceAliases"}
    if set(owners) != expected:
        raise ValueError(
            f"{path}: frozen owner coverage differs: "
            f"missing={sorted(expected - set(owners))}; "
            f"extra={sorted(set(owners) - expected)}"
        )
    if order != sorted(order):
        raise ValueError(f"{path}: frozen owners must be sorted by module")
    for module in EXPECTED_HISTORICAL_COUNTS:
        if owners[module].ilean_sha256 == "-":
            raise ValueError(f"{path}: declaration owner lacks frozen .ilean: {module}")
    return owners


def frozen_source_path(
    project_root: Path, owner: FrozenOwner, frozen_source_dir: Path | None
) -> Path:
    if frozen_source_dir is None:
        return project_root / owner.path
    return frozen_source_dir / f"{owner.module}.lean"


def frozen_ilean_path(
    project_root: Path, module: str, frozen_ilean_dir: Path | None
) -> Path:
    if frozen_ilean_dir is None:
        return default_ilean_path(project_root, module)
    return frozen_ilean_dir / f"{module}.ilean"


def generate_command_routes(
    baseline: dict[str, Declaration],
    records: dict[str, ManifestRow],
    project_root: Path,
    owners: dict[str, FrozenOwner],
    frozen_source_dir: Path | None,
    frozen_ilean_dir: Path | None,
) -> dict[str, CommandRoute]:
    actual_to_logical = baseline_actual_to_logical(baseline)
    entries_by_module: dict[
        str, dict[str, tuple[int, int, int, int, int, int, int, int]]
    ] = {}
    source_by_module: dict[str, bytes] = {}
    historical_modules = {declaration.module for declaration in baseline.values()}
    for module in sorted(historical_modules):
        entries_by_module[module] = read_ilean_entries(
            frozen_ilean_path(project_root, module, frozen_ilean_dir), module
        )
        source_by_module[module] = normalized_source_bytes(
            frozen_source_path(project_root, owners[module], frozen_source_dir)
        )

    generated: dict[str, CommandRoute] = {}
    for logical, declaration in sorted(baseline.items()):
        entries = entries_by_module[declaration.module]
        candidates = [
            root
            for root in entries
            if declaration.name == root or declaration.name.startswith(root + ".")
        ]
        if not candidates:
            raise ValueError(
                f"{logical}: no authoritative .ilean source-command root"
            )
        longest = max(map(len, candidates))
        roots = [root for root in candidates if len(root) == longest]
        if len(roots) != 1:
            raise ValueError(f"{logical}: ambiguous authoritative roots {roots}")
        root = roots[0]
        root_logical = actual_to_logical.get(root)
        if root_logical is None:
            raise ValueError(
                f"{logical}: .ilean root {root} is absent from the frozen selection"
            )
        span = entries[root]
        command_hash = sha256_bytes(
            source_command_bytes(source_by_module[declaration.module], span)
        )
        generated[logical] = CommandRoute(
            declaration.module,
            logical,
            declaration.name,
            root_logical,
            root,
            "authored" if declaration.name == root else "compiler_generated",
            *span,
            command_hash,
            records[logical].destination_module,
        )
    validate_command_routes(generated, baseline, records)
    return generated


def command_route_bytes(routes: dict[str, CommandRoute]) -> bytes:
    rows = ["format\t2"]
    for logical in sorted(routes):
        route = routes[logical]
        rows.append(
            "\t".join(
                (
                    "route",
                    route.historical_module,
                    route.logical_name,
                    route.historical_actual_name,
                    route.command_root_logical,
                    route.command_root_actual_name,
                    route.provenance,
                    *(str(value) for value in route.span),
                    route.command_sha256,
                    route.destination_module,
                )
            )
        )
    return ("\n".join(rows) + "\n").encode("utf-8")


def write_command_routes(path: Path, routes: dict[str, CommandRoute]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(command_route_bytes(routes))


def read_command_routes(
    path: Path,
    baseline: dict[str, Declaration],
    records: dict[str, ManifestRow],
) -> dict[str, CommandRoute]:
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["format", "2"]:
        raise ValueError(f"{path}: routes must start with 'format\\t2'")
    routes: dict[str, CommandRoute] = {}
    order: list[str] = []
    for line_number, row in enumerate(rows[1:], 2):
        if len(row) != 17 or row[0] != "route":
            raise ValueError(
                f"{path}:{line_number}: expected one 17-column command route"
            )
        try:
            span = tuple(int(value) for value in row[7:15])
        except ValueError as error:
            raise ValueError(
                f"{path}:{line_number}: non-integer compiler coordinate"
            ) from error
        route = CommandRoute(
            row[1], row[2], row[3], row[4], row[5], row[6], *span, row[15], row[16]
        )
        if route.logical_name in routes:
            raise ValueError(
                f"{path}:{line_number}: duplicate route {route.logical_name}"
            )
        routes[route.logical_name] = route
        order.append(route.logical_name)
    if order != sorted(order):
        raise ValueError(f"{path}: command routes must be sorted by logical name")
    validate_command_routes(routes, baseline, records)
    return routes


def validate_command_routes(
    routes: dict[str, CommandRoute],
    baseline: dict[str, Declaration],
    records: dict[str, ManifestRow],
) -> None:
    if set(routes) != set(records) or set(routes) != set(baseline):
        raise ValueError(
            "command routes do not exactly cover the 5,129 frozen declarations: "
            f"missing={sorted(set(records) - set(routes))[:20]}; "
            f"extra={sorted(set(routes) - set(records))[:20]}"
        )
    groups: dict[
        tuple[str, tuple[int, int, int, int, int, int, int, int]],
        list[CommandRoute],
    ] = defaultdict(list)
    for logical, route in routes.items():
        declaration = baseline[logical]
        record = records[logical]
        if route.logical_name != logical:
            raise ValueError(f"{logical}: route key/name mismatch")
        if route.historical_module != declaration.module:
            raise ValueError(f"{logical}: route historical owner drift")
        if route.historical_actual_name != declaration.name:
            raise ValueError(f"{logical}: route historical actual-name drift")
        root = baseline.get(route.command_root_logical)
        if root is None or root.module != declaration.module:
            raise ValueError(f"{logical}: invalid command root logical owner")
        if route.command_root_actual_name != root.name:
            raise ValueError(f"{logical}: command root actual-name drift")
        expected_provenance = (
            "authored"
            if route.historical_actual_name == route.command_root_actual_name
            else "compiler_generated"
        )
        if route.provenance not in COMMAND_PROVENANCE or route.provenance != expected_provenance:
            raise ValueError(f"{logical}: invalid compiler provenance {route.provenance}")
        if any(value < 0 for value in route.span):
            raise ValueError(f"{logical}: negative compiler coordinate")
        if (route.end_line, route.end_col) < (route.start_line, route.start_col):
            raise ValueError(f"{logical}: reversed compiler span")
        if not HEX_SHA256.fullmatch(route.command_sha256):
            raise ValueError(f"{logical}: invalid command SHA-256")
        if route.destination_module != record.destination_module:
            raise ValueError(f"{logical}: route destination differs from ownership")
        groups[(route.historical_module, route.span)].append(route)

    for group, members in groups.items():
        destinations = {member.destination_module for member in members}
        hashes = {member.command_sha256.upper() for member in members}
        roots = {
            (member.command_root_logical, member.command_root_actual_name)
            for member in members
        }
        if len(destinations) != 1:
            raise ValueError(
                f"authoritative compiler span {group} straddles destinations: "
                f"{sorted(destinations)}"
            )
        if len(hashes) != 1:
            raise ValueError(f"authoritative compiler span {group} has hash drift")
        if not any(member.provenance == "authored" for member in members):
            raise ValueError(f"authoritative compiler span {group} lacks an authored root")
        for root_logical, root_actual in roots:
            if not any(
                member.logical_name == root_logical
                and member.historical_actual_name == root_actual
                and member.provenance == "authored"
                for member in members
            ):
                raise ValueError(
                    f"authoritative compiler span {group} references absent root "
                    f"{root_logical}"
                )


def validate_routes_against_frozen_inputs(
    routes: dict[str, CommandRoute],
    owners: dict[str, FrozenOwner],
    project_root: Path,
    frozen_source_dir: Path | None,
    frozen_ilean_dir: Path | None,
) -> tuple[int, int]:
    entries_by_module: dict[
        str, dict[str, tuple[int, int, int, int, int, int, int, int]]
    ] = {}
    source_by_module: dict[str, bytes] = {}
    for module, owner in sorted(owners.items()):
        source_path = frozen_source_path(project_root, owner, frozen_source_dir)
        if sha256_file(source_path) != owner.source_sha256:
            raise ValueError(f"{module}: frozen source SHA-256 differs")
        source_payload = normalized_source_bytes(source_path)
        physical = len(source_payload.splitlines())
        nonblank = sum(bool(line.strip()) for line in source_payload.splitlines())
        if (physical, nonblank) != (owner.physical_lines, owner.nonblank_lines):
            raise ValueError(f"{module}: frozen source line counts differ")
        source_by_module[module] = source_payload
        if owner.ilean_sha256 == "-":
            continue
        ilean_path = frozen_ilean_path(project_root, module, frozen_ilean_dir)
        if sha256_file(ilean_path) != owner.ilean_sha256:
            raise ValueError(f"{module}: frozen .ilean SHA-256 differs")
        if ilean_path.stat().st_size != owner.ilean_bytes:
            raise ValueError(f"{module}: frozen .ilean byte count differs")
        entries_by_module[module] = read_ilean_entries(ilean_path, module)

    groups: set[tuple[str, tuple[int, int, int, int, int, int, int, int]]] = set()
    for logical, route in routes.items():
        actual_span = entries_by_module[route.historical_module].get(
            route.command_root_actual_name
        )
        if actual_span != route.span:
            raise ValueError(
                f"{logical}: committed command span differs from frozen .ilean"
            )
        actual_hash = sha256_bytes(
            source_command_bytes(source_by_module[route.historical_module], route.span)
        )
        if actual_hash != route.command_sha256.upper():
            raise ValueError(
                f"{logical}: committed command fingerprint differs from frozen source"
            )
        groups.add((route.historical_module, route.span))
    return len(routes), len(groups)


def manifest_from_command_routes(
    routes: dict[str, CommandRoute], baseline: dict[str, Declaration]
) -> dict[str, ManifestRow]:
    generated = {
        logical: ManifestRow(
            logical,
            baseline[logical].module,
            route.destination_module,
            baseline[logical].kind,
            baseline[logical].visibility,
        )
        for logical, route in routes.items()
    }
    expected_counts = dict(
        Counter(declaration.module for declaration in baseline.values())
    )
    validate_manifest_shape(generated, expected_counts)
    return generated


def read_tiers(path: Path) -> dict[str, str]:
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["format", "1"]:
        raise ValueError(f"{path}: tier manifest must start with 'format\\t1'")
    tiers: dict[str, str] = {}
    order: list[str] = []
    for line_number, row in enumerate(rows[1:], 2):
        if len(row) != 2:
            raise ValueError(f"{path}:{line_number}: expected module and tier columns")
        module, tier = row
        check_module_name(module, f"{path}:{line_number}")
        if tier not in TIERS:
            raise ValueError(
                f"{path}:{line_number}: tier {tier!r} is not one of {sorted(TIERS)}"
            )
        if module in tiers:
            raise ValueError(f"{path}:{line_number}: duplicate tier row for {module}")
        tiers[module] = tier
        order.append(module)
    if order != sorted(order):
        raise ValueError(f"{path}: tier rows must be sorted by module")
    if not tiers:
        raise ValueError(f"{path}: tier manifest is empty")
    return tiers


def generate_tiers(
    records: dict[str, ManifestRow], structural_modules: set[str]
) -> dict[str, str]:
    tiers = {
        row.destination_module: destination_role(row.destination_module)
        for row in records.values()
    }
    tiers.update({module: "source" for module in PRESERVED_SOURCE_LEAVES})
    for module in structural_modules:
        if module == SOURCE_ROOT:
            tiers[module] = "source"
        elif module in {
            REUSABLE_ALGORITHM_UMBRELLA,
            REUSABLE_ANALYSIS_UMBRELLA,
        }:
            tiers[module] = "reusable"
        else:
            tiers[module] = "compatibility"
    validate_tier_coverage(tiers, records, structural_modules)
    return tiers


def write_tiers(path: Path, tiers: dict[str, str]) -> None:
    rows = ["format\t1"]
    rows.extend(f"{module}\t{tier}" for module, tier in sorted(tiers.items()))
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(("\n".join(rows) + "\n").encode("utf-8"))


def validate_tier_coverage(
    tiers: dict[str, str],
    records: dict[str, ManifestRow],
    structural_modules: set[str],
) -> None:
    """Require one proposed tier for every final lane production module."""

    destinations = {row.destination_module for row in records.values()}
    required = destinations | structural_modules | PRESERVED_SOURCE_LEAVES
    missing = sorted(required - set(tiers))
    extra = sorted(set(tiers) - required)
    if missing or extra:
        raise ValueError(
            f"proposed tier coverage is not exactly the lane surface: "
            f"missing={missing[:20]}; extra={extra[:20]}"
        )
    for module, tier in sorted(tiers.items()):
        if module in destinations:
            role = destination_role(module)
            if tier != role:
                raise ValueError(
                    f"{module}: proposed tier {tier} contradicts destination role {role}"
                )
        elif module in structural_modules:
            if module == SOURCE_ROOT:
                if tier != "source":
                    raise ValueError(
                        f"{module}: canonical source aggregate must propose tier source"
                    )
            elif module in {
                REUSABLE_ALGORITHM_UMBRELLA,
                REUSABLE_ANALYSIS_UMBRELLA,
            }:
                if tier != "reusable":
                    raise ValueError(
                        f"{module}: reusable umbrella must propose tier reusable"
                    )
            elif tier != "compatibility":
                raise ValueError(
                    f"{module}: historical wrapper must propose tier compatibility"
                )
        elif tier != "source":
            raise ValueError(f"{module}: preserved Chapter 20 leaf must propose source")


def baseline_actual_to_logical(baseline: dict[str, Declaration]) -> dict[str, str]:
    result = {declaration.name: logical for logical, declaration in baseline.items()}
    if len(result) != len(baseline):
        raise ValueError("baseline selected-name map is not one-to-one")
    return result


def destination_sccs(graph: dict[str, set[str]]) -> list[list[str]]:
    """Return nontrivial strongly connected components deterministically."""

    next_index = 0
    indices: dict[str, int] = {}
    lowlinks: dict[str, int] = {}
    stack: list[str] = []
    on_stack: set[str] = set()
    components: list[list[str]] = []

    def visit(root: str) -> None:
        nonlocal next_index
        work: list[tuple[str, list[str]]] = [(root, sorted(graph[root]))]
        indices[root] = lowlinks[root] = next_index
        next_index += 1
        stack.append(root)
        on_stack.add(root)
        while work:
            owner, pending = work[-1]
            if pending:
                dependency = pending.pop()
                if dependency not in indices:
                    indices[dependency] = lowlinks[dependency] = next_index
                    next_index += 1
                    stack.append(dependency)
                    on_stack.add(dependency)
                    work.append((dependency, sorted(graph[dependency])))
                elif dependency in on_stack:
                    lowlinks[owner] = min(lowlinks[owner], indices[dependency])
                continue
            work.pop()
            if work:
                parent = work[-1][0]
                lowlinks[parent] = min(lowlinks[parent], lowlinks[owner])
            if lowlinks[owner] == indices[owner]:
                component: list[str] = []
                while True:
                    member = stack.pop()
                    on_stack.remove(member)
                    component.append(member)
                    if member == owner:
                        break
                if len(component) > 1:
                    components.append(sorted(component))

    for owner in sorted(graph):
        if owner not in indices:
            visit(owner)
    return sorted(components)


def validate_destination_graph(
    dependency_tsv: Path,
    declarations: list[Declaration],
    actual_to_logical: dict[str, str],
    records: dict[str, ManifestRow],
    allowed_external_source_imports: set[tuple[str, str]] | None = None,
) -> tuple[int, int]:
    """Enforce the declaration DAG and the reviewed reusable/source boundary."""

    allowed_external_source_imports = allowed_external_source_imports or set()
    module_by_name = {
        declaration.name: declaration.module for declaration in declarations
    }
    owners = {row.destination_module for row in records.values()}
    graph: dict[str, set[str]] = {owner: set() for owner in owners}
    witnesses: dict[tuple[str, str], DependencyEdge] = {}
    forbidden: list[str] = []

    for edge in iter_dependency_edges(dependency_tsv):
        source_logical = actual_to_logical.get(edge.source)
        if source_logical is None:
            continue
        source_owner = records[source_logical].destination_module
        source_role = destination_role(source_owner)

        target_logical = actual_to_logical.get(edge.target)
        if target_logical is not None:
            target_owner = records[target_logical].destination_module
            target_role = destination_role(target_owner)
            if source_owner != target_owner:
                graph[source_owner].add(target_owner)
                witnesses.setdefault((source_owner, target_owner), edge)
            if source_role == "reusable" and target_role == "source":
                forbidden.append(
                    f"{source_owner} -> {target_owner} via {edge.kind} "
                    f"{edge.source} -> {edge.target}"
                )
            continue

        target_module = module_by_name.get(edge.target)
        if source_role != "reusable" or target_module is None:
            continue
        if (
            target_module.startswith(SOURCE_DESTINATION_PREFIX)
            or target_module == SOURCE_ROOT
            or target_module.startswith("NumStability.Source.")
            or target_module.startswith(HIGHAM_COMPAT_ROOT)
            or target_module.startswith("NumStability.Higham.")
            or target_module == CHAPTER_SEVEN
            or target_module.startswith(LS_PREFIX)
        ):
            if (
                (source_owner, target_module) in allowed_external_source_imports
                or target_module.startswith(QR_SOURCE_PREFIX)
            ):
                continue
            forbidden.append(
                f"{source_owner} -> external {target_module} via {edge.kind} "
                f"{edge.source} -> {edge.target}"
            )

    if forbidden:
        raise ValueError(
            "reusable destinations depend on source, compatibility, legacy, or "
            "Chapter 7 declarations: " + "; ".join(sorted(forbidden)[:20])
        )

    components = destination_sccs(graph)
    if components:
        component = components[0]
        members = set(component)
        component_witnesses: list[str] = []
        for source in component:
            for target in sorted(graph[source] & members):
                edge = witnesses[(source, target)]
                component_witnesses.append(
                    f"{source} -> {target} via {edge.kind} {edge.source} -> {edge.target}"
                )
        raise ValueError(
            f"destination ownership graph contains a cycle among {component}: "
            + "; ".join(component_witnesses[:20])
        )

    return len(owners), sum(len(dependencies) for dependencies in graph.values())


def read_private_rewrites(
    path: Path,
    records: dict[str, ManifestRow],
    baseline: dict[str, Declaration],
    required_logicals: set[str] | None = None,
) -> dict[str, PrivateRewrite]:
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["format", "1"]:
        raise ValueError(f"{path}: private rewrites must start with 'format\\t1'")

    rewrites: dict[str, PrivateRewrite] = {}
    candidate_names: set[str] = set()
    order: list[str] = []
    for line_number, row in enumerate(rows[1:], 2):
        if len(row) != 3:
            raise ValueError(
                f"{path}:{line_number}: private rewrites require three columns"
            )
        rewrite = PrivateRewrite(*row)
        logical = rewrite.logical_name
        if logical in rewrites:
            raise ValueError(f"{path}:{line_number}: duplicate rewrite {logical}")
        if rewrite.candidate_actual_name in candidate_names:
            raise ValueError(
                f"{path}:{line_number}: duplicate candidate private name "
                f"{rewrite.candidate_actual_name}"
            )
        rewrites[logical] = rewrite
        candidate_names.add(rewrite.candidate_actual_name)
        order.append(logical)
    if order != sorted(order):
        raise ValueError(f"{path}: rewrite rows must be sorted by logical name")

    all_private_logicals = {
        logical for logical, row in records.items() if row.visibility == "private"
    }
    expected_logicals = (
        all_private_logicals
        if required_logicals is None
        else all_private_logicals & required_logicals
    )
    if set(rewrites) != expected_logicals:
        missing = sorted(expected_logicals - set(rewrites))
        extra = sorted(set(rewrites) - expected_logicals)
        raise ValueError(
            f"private rewrite coverage differs: missing={missing[:20]}; extra={extra[:20]}"
        )
    for logical, rewrite in rewrites.items():
        historical = baseline[logical]
        destination = records[logical].destination_module
        if rewrite.historical_actual_name != historical.name:
            raise ValueError(
                f"{logical}: expected historical private name {historical.name}, "
                f"found {rewrite.historical_actual_name}"
            )
        expected_suffix = private_suffix(historical.name, historical.module)
        try:
            candidate_suffix = private_suffix(
                rewrite.candidate_actual_name, destination
            )
        except ValueError as error:
            raise ValueError(
                f"{logical}: candidate private name does not encode destination "
                f"{destination}: {rewrite.candidate_actual_name}"
            ) from error
        if candidate_suffix != expected_suffix:
            raise ValueError(
                f"{logical}: candidate private name changes the declaration suffix: "
                f"expected {expected_suffix}, found {candidate_suffix}"
            )
    return rewrites


def check_candidate_ownership(
    records: dict[str, ManifestRow],
    baseline: dict[str, Declaration],
    declarations: list[Declaration],
    rewrites: dict[str, PrivateRewrite],
    completed_destinations: set[str] | None = None,
) -> dict[str, str]:
    completed = (
        {row.destination_module for row in records.values()}
        if completed_destinations is None
        else completed_destinations
    )
    declaration_by_name = {
        declaration.name: declaration for declaration in declarations
    }
    candidate_actual_to_logical: dict[str, str] = {}
    expected_actual_by_logical: dict[str, str] = {}

    for logical, expected in records.items():
        is_completed = expected.destination_module in completed
        if expected.visibility == "private" and is_completed:
            candidate_name = rewrites[logical].candidate_actual_name
        else:
            candidate_name = baseline[logical].name
        expected_actual_by_logical[logical] = candidate_name
        actual = declaration_by_name.get(candidate_name)
        if actual is None:
            raise ValueError(
                f"{logical}: candidate declaration is missing ({candidate_name})"
            )
        actual_metadata = (actual.module, actual.kind, actual.visibility)
        expected_metadata = (
            (
                expected.destination_module
                if is_completed
                else expected.historical_module
            ),
            expected.kind,
            expected.visibility,
        )
        if actual_metadata != expected_metadata:
            raise ValueError(
                f"{logical}: expected destination metadata {expected_metadata}, "
                f"found {actual_metadata}"
            )
        candidate_actual_to_logical[candidate_name] = logical

    # Every historical owner and every canonical destination is exclusive to
    # this 5,129-declaration contract.  Reject any extra declaration there,
    # including an edge-free public declaration that the incident graph would
    # otherwise never observe.  Stage-appropriate private rewrites are already
    # represented in ``accepted`` and therefore remain one-to-one as well.
    selected_modules = set(EXPECTED_HISTORICAL_COUNTS) | {
        row.destination_module for row in records.values()
    }
    accepted = set(expected_actual_by_logical.values())
    actual_selected = {
        declaration.name
        for declaration in declarations
        if declaration.module in selected_modules
    }
    extra = sorted(actual_selected - accepted)
    missing = sorted(accepted - actual_selected)
    if extra or missing:
        raise ValueError(
            "candidate declarations in selected historical/canonical owners "
            f"differ from the exact contract: missing={missing[:20]}; "
            f"extra={extra[:20]}"
        )
    if len(candidate_actual_to_logical) != len(records):
        raise ValueError("candidate selected-name map is not one-to-one")
    return candidate_actual_to_logical


def validate_candidate_command_fingerprints(
    project_root: Path,
    routes: dict[str, CommandRoute],
    records: dict[str, ManifestRow],
    candidate_actual_to_logical: dict[str, str],
    completed_destinations: set[str],
    ilean_overrides: dict[str, Path],
) -> int:
    """Reject same-kind/same-edge edits by comparing exact compiler commands.

    All authored roots of one frozen compiler span must still share one
    candidate compiler span, and the LF-normalized UTF-8 command bytes must
    retain the frozen SHA-256.  Compiler-generated declarations are covered by
    the same group even though Lean does not emit separate ``.ilean`` roots for
    them.
    """

    logical_to_candidate = {
        logical: actual for actual, logical in candidate_actual_to_logical.items()
    }
    groups: dict[
        tuple[str, tuple[int, int, int, int, int, int, int, int]],
        list[CommandRoute],
    ] = defaultdict(list)
    for route in routes.values():
        groups[(route.historical_module, route.span)].append(route)

    ilean_cache: dict[
        str, dict[str, tuple[int, int, int, int, int, int, int, int]]
    ] = {}
    source_cache: dict[str, bytes] = {}
    for group, members in sorted(groups.items()):
        destination = members[0].destination_module
        owner = (
            destination
            if destination in completed_destinations
            else members[0].historical_module
        )
        if owner not in ilean_cache:
            ilean_path = ilean_overrides.get(owner, default_ilean_path(project_root, owner))
            ilean_cache[owner] = read_ilean_entries(ilean_path, owner)
            source_cache[owner] = normalized_source_bytes(module_path(project_root, owner))

        candidate_spans: set[
            tuple[int, int, int, int, int, int, int, int]
        ] = set()
        for root_logical in sorted({member.command_root_logical for member in members}):
            candidate_root = logical_to_candidate[root_logical]
            candidate_span = ilean_cache[owner].get(candidate_root)
            if candidate_span is None:
                raise ValueError(
                    f"compiler root {root_logical} is absent from candidate .ilean "
                    f"owner {owner} ({candidate_root})"
                )
            candidate_spans.add(candidate_span)
        if len(candidate_spans) != 1:
            raise ValueError(
                f"frozen source-command group {group} split across candidate spans: "
                f"{sorted(candidate_spans)}"
            )
        candidate_span = next(iter(candidate_spans))
        candidate_hash = sha256_bytes(
            source_command_bytes(source_cache[owner], candidate_span)
        )
        expected_hashes = {member.command_sha256.upper() for member in members}
        if expected_hashes != {candidate_hash}:
            raise ValueError(
                f"source-command semantic fingerprint changed for {group}: "
                f"expected {sorted(expected_hashes)}, found {candidate_hash}"
            )
    return len(groups)


def strip_lean_comments(lines: list[str]) -> list[str]:
    """Blank out block and line comments while preserving line structure."""

    result: list[str] = []
    depth = 0
    for line in lines:
        out: list[str] = []
        index = 0
        while index < len(line):
            if depth:
                if line.startswith("/-", index):
                    depth += 1
                    index += 2
                elif line.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
                continue
            if line.startswith("--", index):
                break
            if line.startswith("/-", index):
                depth += 1
                index += 2
                continue
            out.append(line[index])
            index += 1
        result.append("".join(out))
    if depth:
        raise ValueError("unterminated Lean block comment")
    return result


def module_path(project_root: Path, module: str) -> Path:
    return project_root / (module.replace(".", "/") + ".lean")


def has_top_level_module_docstring(source: str) -> bool:
    """Recognize a real top-level ``/-!`` comment, not text inside a comment."""

    depth = 0
    line_comment = False
    index = 0
    while index < len(source):
        if line_comment:
            if source[index] in "\r\n":
                line_comment = False
            index += 1
        elif depth:
            if source.startswith("/-", index):
                depth += 1
                index += 2
            elif source.startswith("-/", index):
                depth -= 1
                index += 2
            else:
                index += 1
        elif source.startswith("--", index):
            line_comment = True
            index += 2
        elif source.startswith("/-!", index):
            return True
        elif source.startswith("/-", index):
            depth = 1
            index += 2
        else:
            index += 1
    return False


def validate_import_sequence(
    path: Path, imports: list[str], expected: tuple[str, ...] | None
) -> tuple[str, ...]:
    actual = tuple(imports)
    duplicates = sorted(
        imported for imported, count in Counter(imports).items() if count > 1
    )
    if duplicates:
        raise ValueError(
            f"structural module has duplicate imports in {path}: {duplicates}"
        )
    ordered = tuple(sorted(imports))
    if actual != ordered:
        raise ValueError(
            f"structural module imports are not sorted in {path}: "
            f"found {actual}, expected {ordered}"
        )
    if expected is not None and actual != expected:
        raise ValueError(
            f"structural import contract differs for {path}: "
            f"expected {expected}, found {actual}"
        )
    return actual


def validate_import_only_module(
    project_root: Path,
    module: str,
    expected: tuple[str, ...] | None = None,
) -> tuple[str, ...]:
    path = module_path(project_root, module)
    if not path.is_file():
        raise ValueError(f"missing completed structural module: {path}")
    source = path.read_text(encoding="utf-8")
    if not has_top_level_module_docstring(source):
        raise ValueError(f"structural module lacks a module docstring: {path}")
    imports: list[str] = []
    source_lines = source.splitlines()
    for original, code in zip(
        source_lines, strip_lean_comments(source_lines), strict=True
    ):
        stripped = code.strip()
        if not stripped:
            continue
        fields = stripped.split()
        if len(fields) == 2 and fields[0] == "import":
            imported = fields[1]
        elif len(fields) == 3 and fields[:2] == ["public", "import"]:
            imported = fields[2]
        else:
            raise ValueError(
                f"structural module contains non-import code in {path}: {original!r}"
            )
        check_module_name(imported, f"{path}: import")
        imports.append(imported)
    if not imports:
        raise ValueError(f"structural module has no imports: {path}")
    return validate_import_sequence(path, imports, expected)


def read_structural_modules(path: Path) -> set[str]:
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["format", "1"]:
        raise ValueError(f"{path}: structural modules must start with 'format\\t1'")
    modules: set[str] = set()
    order: list[str] = []
    for line_number, row in enumerate(rows[1:], 2):
        if len(row) != 1:
            raise ValueError(
                f"{path}:{line_number}: expected one structural-module column"
            )
        module = row[0]
        check_module_name(module, f"{path}:{line_number}")
        if module in modules:
            raise ValueError(f"{path}:{line_number}: duplicate module {module}")
        modules.add(module)
        order.append(module)
    if order != sorted(order):
        raise ValueError(f"{path}: structural modules must be sorted")
    return modules


def read_structural_import_contract(
    path: Path,
) -> dict[str, tuple[str, ...]]:
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["format", "1"]:
        raise ValueError(f"{path}: structural imports must start with 'format\\t1'")
    allowed_roles = {
        "compatibility_wrapper",
        "reusable_aggregate",
        "source_aggregate",
    }
    imports: dict[str, list[str]] = defaultdict(list)
    roles: dict[str, str] = {}
    order: list[tuple[str, str]] = []
    for line_number, row in enumerate(rows[1:], 2):
        if len(row) != 4 or row[0] != "import":
            raise ValueError(
                f"{path}:{line_number}: expected import, module, role, dependency"
            )
        _, module, role, dependency = row
        check_module_name(module, f"{path}:{line_number}")
        check_module_name(dependency, f"{path}:{line_number}")
        if role not in allowed_roles:
            raise ValueError(f"{path}:{line_number}: unknown structural role {role}")
        if module in roles and roles[module] != role:
            raise ValueError(f"{path}:{line_number}: conflicting role for {module}")
        roles[module] = role
        imports[module].append(dependency)
        order.append((module, dependency))
    if order != sorted(order):
        raise ValueError(f"{path}: structural import rows must be sorted")
    if set(imports) != DEFAULT_STRUCTURAL_MODULES:
        raise ValueError(
            f"{path}: structural surface differs: "
            f"missing={sorted(DEFAULT_STRUCTURAL_MODULES - set(imports))}; "
            f"extra={sorted(set(imports) - DEFAULT_STRUCTURAL_MODULES)}"
        )
    result: dict[str, tuple[str, ...]] = {}
    for module, dependencies in sorted(imports.items()):
        if len(dependencies) != len(set(dependencies)):
            raise ValueError(f"{path}: duplicate structural import for {module}")
        if dependencies != sorted(dependencies):
            raise ValueError(f"{path}: imports for {module} are not sorted")
        expected_role = (
            "compatibility_wrapper"
            if module in ALL_COMPATIBILITY_WRAPPERS
            else "source_aggregate"
            if module == SOURCE_ROOT
            else "reusable_aggregate"
        )
        if roles[module] != expected_role:
            raise ValueError(
                f"{path}: {module} has role {roles[module]}, expected {expected_role}"
            )
        result[module] = tuple(dependencies)
    return result


def frozen_historical_imports(
    project_root: Path,
    frozen_owners: dict[str, FrozenOwner],
    frozen_source_dir: Path | None,
) -> dict[str, tuple[str, ...]]:
    """Historical import list of every declaration owner, from frozen sources.

    Read from the blob-verified pristine copy rather than the worktree: after a
    wave the worktree file is already the wrapper, so reading it back would
    return the wrapper's own imports and preserve nothing.
    """
    imports: dict[str, tuple[str, ...]] = {}
    for module in sorted(HISTORICAL_DECLARATION_WRAPPERS):
        owner = frozen_owners[module]
        path = frozen_source_path(project_root, owner, frozen_source_dir)
        if not path.is_file():
            raise ValueError(f"missing frozen source for {module}: {path}")
        declared: list[str] = []
        for imported in read_import_prefix(path):
            check_module_name(imported, f"{path}: import")
            if imported == module:
                raise ValueError(f"{path}: historical owner imports itself")
            if imported not in declared:
                declared.append(imported)
        if not declared:
            raise ValueError(f"frozen historical owner declares no imports: {module}")
        imports[module] = tuple(sorted(declared))
    return imports


def generate_structural_import_contract(
    records: dict[str, ManifestRow],
    historical_imports: dict[str, tuple[str, ...]],
) -> dict[str, tuple[str, ...]]:
    destinations_by_historical: dict[str, set[str]] = defaultdict(set)
    destinations = {row.destination_module for row in records.values()}
    for record in records.values():
        destinations_by_historical[record.historical_module].add(
            record.destination_module
        )
    missing = set(HISTORICAL_DECLARATION_WRAPPERS) - set(historical_imports)
    if missing:
        raise ValueError(
            "no frozen historical imports for: " + ", ".join(sorted(missing))
        )
    # A wrapper forwards its destinations *and* re-states the historical import
    # list.  Forwarding destinations alone narrows the transitive surface the
    # historical module used to offer, which breaks any consumer that reached an
    # identifier through it; the packet contract preserves historical imports.
    contract: dict[str, tuple[str, ...]] = {
        historical: tuple(
            sorted(
                destinations_by_historical[historical]
                | set(historical_imports[historical])
            )
        )
        for historical in sorted(HISTORICAL_DECLARATION_WRAPPERS)
    }
    preserved = tuple(sorted(PRESERVED_SOURCE_LEAVES))
    contract[f"{LS_PREFIX}.Higham20SourceAliases"] = preserved
    contract[f"{HIGHAM_COMPAT_ROOT}.SourceAliases"] = preserved
    contract[SOURCE_ROOT] = tuple(
        sorted(
            PRESERVED_SOURCE_LEAVES
            | {
                destination
                for destination in destinations
                if destination_role(destination) == "source"
            }
        )
    )
    contract[REUSABLE_ALGORITHM_UMBRELLA] = tuple(
        sorted(
            destination
            for destination in destinations
            if destination.startswith(REUSABLE_ALGORITHM_ROOT + ".")
        )
    )
    contract[REUSABLE_ANALYSIS_UMBRELLA] = tuple(
        sorted(
            destination
            for destination in destinations
            if destination.startswith(REUSABLE_ANALYSIS_ROOT + ".")
        )
    )
    if set(contract) != DEFAULT_STRUCTURAL_MODULES:
        raise ValueError("generated structural module surface is incomplete")
    if any(not dependencies for dependencies in contract.values()):
        raise ValueError("generated structural module has no imports")
    return contract


def structural_import_bytes(
    contract: dict[str, tuple[str, ...]]
) -> bytes:
    rows = ["format\t1"]
    for module, dependencies in sorted(contract.items()):
        role = (
            "compatibility_wrapper"
            if module in ALL_COMPATIBILITY_WRAPPERS
            else "source_aggregate"
            if module == SOURCE_ROOT
            else "reusable_aggregate"
        )
        rows.extend(
            f"import\t{module}\t{role}\t{dependency}"
            for dependency in dependencies
        )
    return ("\n".join(rows) + "\n").encode("utf-8")


def write_structural_import_contract(
    path: Path, contract: dict[str, tuple[str, ...]]
) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(structural_import_bytes(contract))


def generate_coordinator_patches(
    project_root: Path,
    records: dict[str, ManifestRow],
    structural_contract: dict[str, tuple[str, ...]],
) -> set[tuple[str, str, str, str]]:
    """Freeze every shared-file edit the lane is not allowed to make."""

    graph = read_module_imports(project_root)
    qr_consumers = {source for source, _ in FROZEN_QR_TO_LS}
    lane_modules = set(EXPECTED_HISTORICAL_COUNTS) | {
        f"{LS_PREFIX}.Higham20SourceAliases",
        *PRESERVED_SOURCE_LEAVES,
    }
    discovered_consumers = {
        module
        for module, imports in graph.items()
        if module.startswith("NumStability")
        and not module.startswith("NumStabilityTest")
        and module not in lane_modules
        and module not in qr_consumers
        and any(dependency in ALL_COMPATIBILITY_WRAPPERS for dependency in imports)
    }
    if discovered_consumers != set(COORDINATOR_CONSUMER_FINAL_IMPORTS):
        raise ValueError(
            "non-lane least-squares consumers differ from the exact coordinator "
            f"contract: missing={sorted(set(COORDINATOR_CONSUMER_FINAL_IMPORTS) - discovered_consumers)}; "
            f"extra={sorted(discovered_consumers - set(COORDINATOR_CONSUMER_FINAL_IMPORTS))}"
        )

    rows: set[tuple[str, str, str, str]] = set()
    for consumer, final_imports in COORDINATOR_CONSUMER_FINAL_IMPORTS.items():
        historical_imports = {
            dependency
            for dependency in graph[consumer]
            if dependency in ALL_COMPATIBILITY_WRAPPERS
        }
        if not historical_imports:
            raise ValueError(f"coordinator consumer has no historical import: {consumer}")
        rows.update(
            ("remove_import", consumer, dependency, "-")
            for dependency in historical_imports
        )
        rows.update(
            ("add_import", consumer, "-", dependency)
            for dependency in final_imports
        )

    rows.add(
        (
            "add_import",
            "NumStability.Algorithms.LinearSystems",
            "-",
            REUSABLE_ALGORITHM_UMBRELLA,
        )
    )
    rows.add(
        (
            "add_import",
            "NumStability.Analysis",
            "-",
            "NumStability.Analysis.Perturbation",
        )
    )
    rows.add(
        (
            "new_aggregate",
            "NumStability.Analysis.Perturbation",
            "-",
            REUSABLE_ANALYSIS_UMBRELLA,
        )
    )

    for historical in sorted(HISTORICAL_DECLARATION_WRAPPERS):
        rows.update(
            ("compatibility_map", historical, "-", canonical)
            for canonical in structural_contract[historical]
        )

    rows.update(
        (
            "global_tier_exact",
            historical,
            "-",
            "compatibility",
        )
        for historical in HISTORICAL_DECLARATION_WRAPPERS
    )
    rows.update(
        {
            (
                "global_tier_exact",
                REUSABLE_ALGORITHM_UMBRELLA,
                "-",
                "aggregate",
            ),
            (
                "global_tier_exact",
                REUSABLE_ANALYSIS_UMBRELLA,
                "-",
                "aggregate",
            ),
            (
                "global_tier_exact",
                "NumStability.Analysis.Perturbation",
                "-",
                "aggregate",
            ),
            (
                "global_tier_prefix",
                REUSABLE_ALGORITHM_ROOT + ".",
                "-",
                "reusable",
            ),
            (
                "global_tier_prefix",
                REUSABLE_ANALYSIS_ROOT + ".",
                "-",
                "reusable",
            ),
        }
    )
    rows.update(
        ("root_test_import", "NumStabilityTest", "-", module)
        for module in ROOT_TEST_IMPORTS
    )
    return rows


def coordinator_patch_bytes(rows: set[tuple[str, str, str, str]]) -> bytes:
    payload = ["format\t1"]
    payload.extend("\t".join(("patch", *row)) for row in sorted(rows))
    return ("\n".join(payload) + "\n").encode("utf-8")


def write_coordinator_patches(
    path: Path, rows: set[tuple[str, str, str, str]]
) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(coordinator_patch_bytes(rows))


def read_coordinator_patches(
    path: Path,
) -> set[tuple[str, str, str, str]]:
    with path.open(encoding="utf-8", newline="") as stream:
        raw = list(csv.reader(stream, delimiter="\t"))
    if not raw or raw[0] != ["format", "1"]:
        raise ValueError(f"{path}: coordinator patches must start with 'format\\t1'")
    rows: list[tuple[str, str, str, str]] = []
    allowed = {
        "add_import",
        "remove_import",
        "new_aggregate",
        "compatibility_map",
        "global_tier_exact",
        "global_tier_prefix",
        "root_test_import",
    }
    for line_number, row in enumerate(raw[1:], 2):
        if len(row) != 5 or row[0] != "patch":
            raise ValueError(f"{path}:{line_number}: malformed coordinator patch")
        value = tuple(row[1:])
        if value[0] not in allowed or any(not field for field in value):
            raise ValueError(f"{path}:{line_number}: invalid coordinator patch")
        rows.append(value)
    if rows != sorted(rows):
        raise ValueError(f"{path}: coordinator patches must be sorted")
    if len(rows) != len(set(rows)):
        raise ValueError(f"{path}: duplicate coordinator patch")
    return set(rows)


def validate_coordinator_patches_applied(
    project_root: Path,
    rows: set[tuple[str, str, str, str]],
    import_graph: dict[str, list[str]],
    lane_preserved_final_imports: dict[str, set[str]] | None = None,
) -> tuple[int, int, int]:
    failures: list[str] = []
    for action, subject, old, new in sorted(rows):
        if action == "add_import":
            if new not in import_graph.get(subject, []):
                failures.append(f"{subject} lacks coordinator import {new}")
        elif action == "remove_import":
            if old in import_graph.get(subject, []):
                failures.append(f"{subject} still imports compatibility path {old}")
        elif action == "new_aggregate":
            try:
                validate_import_only_module(project_root, subject, (new,))
            except ValueError as error:
                failures.append(str(error))
        elif action == "root_test_import":
            if new not in import_graph.get(subject, []):
                failures.append(f"{subject} lacks root test import {new}")
    if failures:
        raise ValueError(
            "coordinator import/test patches are incomplete: "
            + "; ".join(failures[:20])
        )

    tier_path = project_root / "docs/architecture/tiers.json"
    try:
        tier_payload = json.loads(tier_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ValueError(f"cannot read global tier manifest {tier_path}: {error}") from error
    exact = tier_payload.get("exact")
    prefixes = tier_payload.get("prefixes")
    if not isinstance(exact, dict) or not isinstance(prefixes, list):
        raise ValueError("global tier manifest has unexpected exact/prefix schema")
    prefix_map = {
        row.get("prefix"): row.get("tier")
        for row in prefixes
        if isinstance(row, dict)
    }
    tier_failures: list[str] = []
    for action, subject, _, value in sorted(rows):
        if action == "global_tier_exact" and exact.get(subject) != value:
            tier_failures.append(
                f"tiers.json exact {subject}={exact.get(subject)!r}, expected {value!r}"
            )
        elif action == "global_tier_prefix" and prefix_map.get(subject) != value:
            tier_failures.append(
                f"tiers.json prefix {subject}={prefix_map.get(subject)!r}, expected {value!r}"
            )
    if tier_failures:
        raise ValueError(
            "coordinator global-tier patches are incomplete: "
            + "; ".join(tier_failures[:20])
        )

    compatibility_path = project_root / "docs/architecture/COMPATIBILITY.md"
    compatibility_rows: dict[str, set[str]] = {}
    for line in compatibility_path.read_text(encoding="utf-8").splitlines():
        if not line.startswith("|"):
            continue
        cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
        if len(cells) != 2:
            continue
        historical = re.findall(r"`([^`]+)`", cells[0])
        canonical = re.findall(r"`([^`]+)`", cells[1])
        if len(historical) == 1 and canonical:
            compatibility_rows[historical[0]] = set(canonical)
    expected_compatibility: dict[str, set[str]] = defaultdict(set)
    for action, historical, _, canonical in rows:
        if action == "compatibility_map":
            expected_compatibility[historical].add(canonical)
    compatibility_failures = [
        (
            historical,
            sorted(expected),
            sorted(compatibility_rows.get(historical, set())),
        )
        for historical, expected in sorted(expected_compatibility.items())
        if compatibility_rows.get(historical) != expected
    ]
    if compatibility_failures:
        raise ValueError(
            "COMPATIBILITY.md mappings are incomplete or inexact: "
            f"{compatibility_failures[:10]}"
        )

    preserved_contract = (
        LANE_PRESERVED_FINAL_IMPORTS
        if lane_preserved_final_imports is None
        else lane_preserved_final_imports
    )
    for module, expected_imports in sorted(preserved_contract.items()):
        actual_relevant = {
            dependency
            for dependency in import_graph.get(module, [])
            if dependency.startswith(REUSABLE_ALGORITHM_ROOT + ".")
            or dependency.startswith(REUSABLE_ANALYSIS_ROOT + ".")
            or dependency.startswith(SOURCE_ROOT + ".")
            or dependency in ALL_COMPATIBILITY_WRAPPERS
        }
        if actual_relevant != expected_imports:
            raise ValueError(
                f"lane-owned preserved consumer {module} has imports "
                f"{sorted(actual_relevant)}, expected {sorted(expected_imports)}"
            )
    return (
        sum(action in {"add_import", "remove_import", "new_aggregate"} for action, *_ in rows),
        sum(action.startswith("global_tier") for action, *_ in rows),
        len(expected_compatibility),
    )


def destination_dag_from_stream(
    dependency_tsv: Path,
    actual_to_logical: dict[str, str],
    records: dict[str, ManifestRow],
) -> dict[tuple[str, str], tuple[int, int]]:
    counts: dict[tuple[str, str], Counter[str]] = defaultdict(Counter)
    for edge in iter_dependency_edges(dependency_tsv):
        source_logical = actual_to_logical.get(edge.source)
        target_logical = actual_to_logical.get(edge.target)
        if source_logical is None or target_logical is None:
            continue
        source = records[source_logical].destination_module
        target = records[target_logical].destination_module
        if source != target:
            counts[(source, target)][edge.kind] += 1
    return {
        pair: (typed["signature"], typed["body"])
        for pair, typed in sorted(counts.items())
    }


def destination_dag_bytes(
    dag: dict[tuple[str, str], tuple[int, int]]
) -> bytes:
    rows = ["format\t1"]
    rows.extend(
        f"edge\t{source}\t{target}\t{signature}\t{body}"
        for (source, target), (signature, body) in sorted(dag.items())
    )
    return ("\n".join(rows) + "\n").encode("utf-8")


def write_destination_dag(
    path: Path, dag: dict[tuple[str, str], tuple[int, int]]
) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(destination_dag_bytes(dag))


def read_destination_dag(
    path: Path, records: dict[str, ManifestRow]
) -> dict[tuple[str, str], tuple[int, int]]:
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["format", "1"]:
        raise ValueError(f"{path}: destination DAG must start with 'format\\t1'")
    destinations = {row.destination_module for row in records.values()}
    dag: dict[tuple[str, str], tuple[int, int]] = {}
    order: list[tuple[str, str]] = []
    for line_number, row in enumerate(rows[1:], 2):
        if len(row) != 5 or row[0] != "edge":
            raise ValueError(f"{path}:{line_number}: malformed destination edge")
        _, source, target, signature, body = row
        if source not in destinations or target not in destinations or source == target:
            raise ValueError(f"{path}:{line_number}: invalid destination edge endpoints")
        try:
            typed = (int(signature), int(body))
        except ValueError as error:
            raise ValueError(f"{path}:{line_number}: invalid typed-edge counts") from error
        if typed[0] < 0 or typed[1] < 0 or sum(typed) < 1:
            raise ValueError(f"{path}:{line_number}: empty destination edge")
        pair = (source, target)
        if pair in dag:
            raise ValueError(f"{path}:{line_number}: duplicate destination edge")
        dag[pair] = typed
        order.append(pair)
    if order != sorted(order):
        raise ValueError(f"{path}: destination edges must be sorted")
    graph: dict[str, set[str]] = {destination: set() for destination in destinations}
    for source, target in dag:
        graph[source].add(target)
    components = destination_sccs(graph)
    if components:
        raise ValueError(f"{path}: destination DAG contains cycles: {components[:3]}")
    return dag


def validate_private_colocation(
    dependency_tsv: Path,
    declarations: list[Declaration],
    actual_to_logical: dict[str, str],
    records: dict[str, ManifestRow],
) -> int:
    """Require every private declaration to share its users' destination.

    A Lean private name is scoped to the module that defines it, so a private
    declaration is invisible outside that module.  If the manifest routes a
    private declaration away from a declaration that uses it, the migrated tree
    cannot compile: the user reports an unknown identifier.  Neither escape is
    open to this lane -- duplicating the declaration is forbidden, and widening
    its visibility would break the preserve-visibility contract -- so the
    manifest itself has to co-locate them.

    This is not implied by command-route grouping: a private helper and its user
    are usually separate source commands, so they can be routed apart while every
    other gate still passes.
    """

    visibility = {
        declaration.name: declaration.visibility for declaration in declarations
    }
    offenders: list[str] = []
    for edge in iter_dependency_edges(dependency_tsv):
        if visibility.get(edge.target) != "private":
            continue
        target_logical = actual_to_logical.get(edge.target)
        source_logical = actual_to_logical.get(edge.source)
        if target_logical is None or source_logical is None:
            continue
        target_owner = records[target_logical].destination_module
        source_owner = records[source_logical].destination_module
        if target_owner != source_owner:
            offenders.append(
                f"{edge.target} (private, {target_owner}) used by "
                f"{edge.source} ({source_owner}) via {edge.kind}"
            )
    if offenders:
        raise ValueError(
            f"{len(offenders)} private declaration uses cross a destination "
            "boundary and cannot compile: " + "; ".join(sorted(offenders)[:10])
        )
    return sum(1 for value in visibility.values() if value == "private")


def validate_destination_dag_contract(
    dependency_tsv: Path,
    actual_to_logical: dict[str, str],
    records: dict[str, ManifestRow],
    expected: dict[tuple[str, str], tuple[int, int]],
) -> None:
    actual = destination_dag_from_stream(dependency_tsv, actual_to_logical, records)
    if actual != expected:
        missing = sorted(set(expected) - set(actual))
        extra = sorted(set(actual) - set(expected))
        changed = sorted(
            pair
            for pair in set(actual) & set(expected)
            if actual[pair] != expected[pair]
        )
        raise ValueError(
            "destination typed-edge DAG differs from its frozen contract: "
            f"missing={missing[:20]}; extra={extra[:20]}; "
            f"changed={[(p, expected[p], actual[p]) for p in changed[:20]]}"
        )


def validate_destination_direct_imports(
    import_graph: dict[str, list[str]],
    records: dict[str, ManifestRow],
    dag: dict[tuple[str, str], tuple[int, int]],
    completed: set[str],
) -> None:
    destinations = {row.destination_module for row in records.values()}
    expected_by_source: dict[str, set[str]] = defaultdict(set)
    for source, target in dag:
        expected_by_source[source].add(target)
    failures: list[str] = []
    for source in sorted(completed):
        if source not in destinations:
            continue
        if source not in import_graph:
            failures.append(f"missing destination source {source}")
            continue
        imports = import_graph[source]
        duplicates = sorted(
            dependency
            for dependency, count in Counter(imports).items()
            if count > 1
        )
        if duplicates:
            failures.append(f"{source} has duplicate imports {duplicates}")
        if imports != sorted(imports):
            failures.append(f"{source} imports are not sorted")
        actual_lane = set(imports) & destinations
        expected_lane = expected_by_source[source]
        if actual_lane != expected_lane:
            failures.append(
                f"{source}: expected lane imports {sorted(expected_lane)}, "
                f"found {sorted(actual_lane)}"
            )
    if failures:
        raise ValueError(
            "destination direct-import graph differs: " + "; ".join(failures[:20])
        )


def validate_no_orphaned_destinations(
    project_root: Path, records: dict[str, ManifestRow]
) -> int:
    """Every canonical lane module on disk must own at least one manifest row.

    A retarget can empty a destination an earlier wave already created. The file
    keeps its copy of declarations that now live elsewhere, the family aggregate
    imports both, and Lean reports a duplicate declaration -- but only once the
    build reaches the aggregate, which is far from the change that caused it.
    The manifest already says which modules should exist, so the orphan is
    detectable statically.
    """
    owned = {row.destination_module for row in records.values()}
    roots = (REUSABLE_ALGORITHM_ROOT, REUSABLE_ANALYSIS_ROOT, SOURCE_ROOT)
    orphans: list[str] = []
    for root in roots:
        base = project_root / Path(*root.split("."))
        if not base.is_dir():
            continue
        for path in sorted(base.rglob("*.lean")):
            module = (
                path.relative_to(project_root).with_suffix("").as_posix().replace("/", ".")
            )
            if module in owned or module in PRESERVED_SOURCE_LEAVES:
                continue
            if module in DEFAULT_STRUCTURAL_MODULES:
                continue
            orphans.append(module)
    if orphans:
        raise ValueError(
            "canonical modules own no manifest declaration (retarget left them "
            "behind; their declarations are now declared twice): "
            + ", ".join(orphans[:20])
        )
    return len(owned)


def read_completed_destinations(path: Path) -> set[str]:
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["format", "1"]:
        raise ValueError(f"{path}: completed destinations must start with 'format\\t1'")
    destinations: list[str] = []
    for line_number, row in enumerate(rows[1:], 2):
        if len(row) != 1:
            raise ValueError(f"{path}:{line_number}: expected one completed destination")
        destination = row[0]
        check_module_name(destination, f"{path}:{line_number}")
        destinations.append(destination)
    if not destinations:
        raise ValueError(f"{path}: completed destination set is empty")
    if len(destinations) != len(set(destinations)):
        raise ValueError(f"{path}: duplicate completed destination")
    if destinations != sorted(destinations):
        raise ValueError(f"{path}: completed destinations must be sorted")
    return set(destinations)


def validate_structural_modules(
    project_root: Path,
    declarations: list[Declaration],
    structural_modules: set[str],
    contract: dict[str, tuple[str, ...]] | None,
) -> None:
    offenders = [
        declaration
        for declaration in declarations
        if declaration.module in structural_modules
    ]
    if offenders:
        raise ValueError(
            "completed wrappers or aggregates own compiled declarations: "
            + ", ".join(
                f"{declaration.module}:{declaration.name}"
                for declaration in offenders[:20]
            )
        )
    for module in sorted(structural_modules):
        expected = contract[module] if contract is not None else None
        validate_import_only_module(project_root, module, expected)


def read_import_prefix(path: Path) -> list[str]:
    """Comment-aware direct-import list of one Lean file.

    Shared by the worktree import graph and by the frozen-source reader, so a
    historical import list is parsed exactly the same way whether it comes from
    a tracked module or from a pristine frozen copy.
    """
    imports: list[str] = []
    depth = 0
    with path.open(encoding="utf-8") as stream:
        for original in stream:
            out: list[str] = []
            index = 0
            while index < len(original):
                if depth:
                    if original.startswith("/-", index):
                        depth += 1
                        index += 2
                    elif original.startswith("-/", index):
                        depth -= 1
                        index += 2
                    else:
                        index += 1
                elif original.startswith("--", index):
                    break
                elif original.startswith("/-", index):
                    depth = 1
                    index += 2
                else:
                    out.append(original[index])
                    index += 1
            code = "".join(out)
            if not code.strip():
                continue
            match = IMPORT_RE.match(code)
            if match:
                imports.append(match.group(1))
                continue
            # Lean imports precede declarations/commands.  Stopping here
            # avoids scanning multi-megabyte proof bodies character by
            # character while retaining comment-aware import parsing.
            break
    if depth:
        raise ValueError(f"unterminated Lean block comment in import prefix: {path}")
    return imports


def read_module_imports(project_root: Path) -> dict[str, list[str]]:
    """Read the direct-import graph of every tracked project Lean module."""

    graph: dict[str, list[str]] = {}
    for root in ("NumStability", "NumStabilityTest"):
        base = project_root / root
        if not base.is_dir():
            continue
        for path in sorted(base.rglob("*.lean")):
            module = (
                path.relative_to(project_root)
                .with_suffix("")
                .as_posix()
                .replace("/", ".")
            )
            graph[module] = read_import_prefix(path)
        umbrella = project_root / f"{root}.lean"
        if umbrella.is_file():
            graph[root] = read_import_prefix(umbrella)
    return graph


def forbidden_for_reusable(module: str) -> bool:
    return (
        module == SOURCE_ROOT
        or module.startswith("NumStability.Source.")
        or module.startswith("NumStability.Higham.")
        or module == CHAPTER_SEVEN
        or module == LS_PREFIX
        or module.startswith(LS_PREFIX + ".")
    )


def validate_reusable_isolation(
    project_root: Path,
    records: dict[str, ManifestRow],
    import_graph: dict[str, list[str]] | None = None,
    allowed_direct_imports: set[tuple[str, str]] | None = None,
) -> int:
    """Require isolation except for exact reviewed cross-lane source imports."""

    graph = read_module_imports(project_root) if import_graph is None else import_graph
    allowed_direct_imports = allowed_direct_imports or set()
    reusable = sorted(
        {
            row.destination_module
            for row in records.values()
            if destination_role(row.destination_module) == "reusable"
        }
    )
    violations: list[str] = []
    for start in reusable:
        if start not in graph:
            raise ValueError(f"reusable destination has no source file: {start}")
        seen = {start}
        queue = deque([(start, [start])])
        while queue:
            module, path = queue.popleft()
            for imported in graph.get(module, []):
                if forbidden_for_reusable(imported):
                    qr_carrier_path = any(
                        part.startswith("NumStability.Algorithms.QR.")
                        for part in path[1:]
                    )
                    if (
                        (module, imported) in allowed_direct_imports
                        or any(
                            (part, imported) in allowed_direct_imports
                            for part in path
                        )
                        or (imported.startswith(QR_SOURCE_PREFIX) and qr_carrier_path)
                    ):
                        continue
                    violations.append(" -> ".join(path + [imported]))
                    continue
                if imported in seen or imported not in graph:
                    continue
                seen.add(imported)
                queue.append((imported, path + [imported]))
    if violations:
        raise ValueError(
            "reusable destinations transitively reach source, compatibility, "
            "legacy, or Chapter 7 modules: " + "; ".join(sorted(violations)[:20])
        )
    return len(reusable)


def transitive_imports(graph: dict[str, list[str]], start: str) -> set[str]:
    seen: set[str] = set()
    queue = deque(graph.get(start, []))
    while queue:
        module = queue.popleft()
        if module in seen:
            continue
        seen.add(module)
        queue.extend(graph.get(module, []))
    return seen


def cross_lane_pairs() -> dict[tuple[str, str], str]:
    pairs = {pair: "LS_TO_QR" for pair in FROZEN_LS_TO_QR}
    pairs.update({pair: "QR_TO_LS" for pair in FROZEN_QR_TO_LS})
    return pairs


def read_cross_lane_normalization(
    path: Path, records: dict[str, ManifestRow]
) -> list[CrossLaneNormalization]:
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["format", "1"]:
        raise ValueError(f"{path}: cross-lane contract must start with 'format\\t1'")
    result: list[CrossLaneNormalization] = []
    order: list[tuple[str, ...]] = []
    known_pairs = cross_lane_pairs()
    destinations_by_historical: dict[str, set[str]] = defaultdict(set)
    for record in records.values():
        destinations_by_historical[record.historical_module].add(
            record.destination_module
        )
    for line_number, row in enumerate(rows[1:], 2):
        if len(row) != 11 or row[0] != "normalize":
            raise ValueError(
                f"{path}:{line_number}: expected one 11-column normalization row"
            )
        contract = CrossLaneNormalization(*row[1:])
        if contract.row_type not in {"edge", "import"}:
            raise ValueError(f"{path}:{line_number}: invalid normalization row type")
        if contract.direction not in CROSS_LANE_DIRECTIONS:
            raise ValueError(f"{path}:{line_number}: invalid direction")
        if contract.edge_kind not in EDGE_KINDS | {"import"}:
            raise ValueError(f"{path}:{line_number}: invalid edge kind")
        if (contract.row_type == "import") != (contract.edge_kind == "import"):
            raise ValueError(f"{path}:{line_number}: row type/edge kind mismatch")
        pair = (contract.base_source_module, contract.base_target_module)
        if known_pairs.get(pair) != contract.direction:
            raise ValueError(f"{path}:{line_number}: unknown frozen module edge {pair}")
        check_module_name(contract.base_source_module, f"{path}:{line_number}")
        check_module_name(contract.base_target_module, f"{path}:{line_number}")
        if contract.row_type == "import":
            if contract.base_source_name != "-" or contract.base_target_name != "-":
                raise ValueError(f"{path}:{line_number}: import row must use '-' names")
        elif contract.base_source_name == "-" or contract.base_target_name == "-":
            raise ValueError(f"{path}:{line_number}: edge row lacks declaration names")
        check_module_name(contract.ls_destination, f"{path}:{line_number}")
        historical_ls = (
            contract.base_source_module
            if contract.direction == "LS_TO_QR"
            else contract.base_target_module
        )
        if contract.ls_destination not in destinations_by_historical[historical_ls]:
            raise ValueError(
                f"{path}:{line_number}: {contract.ls_destination} is not an owner of "
                f"{historical_ls}"
            )
        if contract.status not in CROSS_LANE_STATUS:
            raise ValueError(f"{path}:{line_number}: invalid normalization status")
        if contract.status == "resolved":
            check_module_name(contract.qr_owner, f"{path}:{line_number}")
            if contract.qr_owner.startswith("NumStability.Algorithms.QR.Higham19"):
                raise ValueError(
                    f"{path}:{line_number}: final QR owner is still a Higham19 wrapper"
                )
        elif not QR_OWNER_PLACEHOLDER.fullmatch(contract.qr_owner):
            raise ValueError(
                f"{path}:{line_number}: unresolved row lacks QR-owner placeholder"
            )
        result.append(contract)
        order.append(tuple(row[1:]))
    if not result:
        raise ValueError(f"{path}: empty cross-lane normalization contract")
    if order != sorted(order):
        raise ValueError(f"{path}: normalization rows must be sorted")
    if len(order) != len(set(order)):
        raise ValueError(f"{path}: duplicate normalization row")
    return result


def expected_cross_lane_edges(
    dependency_tsv: Path,
    declarations: list[Declaration],
    actual_to_logical: dict[str, str],
    records: dict[str, ManifestRow],
) -> set[tuple[str, str, str, str, str, str, str]]:
    module_by_name = {
        declaration.name: declaration.module for declaration in declarations
    }
    pairs = cross_lane_pairs()
    expected: set[tuple[str, str, str, str, str, str, str]] = set()
    for edge in iter_dependency_edges(dependency_tsv):
        source_module = module_by_name.get(edge.source)
        target_module = module_by_name.get(edge.target)
        direction = pairs.get((source_module, target_module))
        if direction is None:
            continue
        ls_actual = edge.source if direction == "LS_TO_QR" else edge.target
        ls_logical = actual_to_logical.get(ls_actual)
        if ls_logical is None:
            raise ValueError(
                f"frozen cross-lane edge lacks selected LS declaration: {edge}"
            )
        expected.add(
            (
                direction,
                edge.kind,
                source_module,
                edge.source,
                target_module,
                edge.target,
                records[ls_logical].destination_module,
            )
        )
    return expected


def qr_owner_initial_value(module: str) -> tuple[str, str]:
    if module.startswith("NumStability.Algorithms.QR.Higham19"):
        return f"@QR_OWNER_REQUIRED:{module}", "qr_owner_required"
    return module, "resolved"


def generate_cross_lane_normalization(
    dependency_tsv: Path,
    declarations: list[Declaration],
    actual_to_logical: dict[str, str],
    records: dict[str, ManifestRow],
) -> list[CrossLaneNormalization]:
    rows: list[CrossLaneNormalization] = []
    expected_edges = expected_cross_lane_edges(
        dependency_tsv, declarations, actual_to_logical, records
    )
    pairs_with_edges: set[tuple[str, str]] = set()
    for (
        direction,
        edge_kind,
        source_module,
        source_name,
        target_module,
        target_name,
        ls_destination,
    ) in sorted(expected_edges):
        qr_module = target_module if direction == "LS_TO_QR" else source_module
        qr_owner, status = qr_owner_initial_value(qr_module)
        rows.append(
            CrossLaneNormalization(
                "edge",
                direction,
                edge_kind,
                source_module,
                source_name,
                target_module,
                target_name,
                ls_destination,
                qr_owner,
                status,
            )
        )
        pairs_with_edges.add((source_module, target_module))

    for source_module, target_module in sorted(
        set(cross_lane_pairs()) - pairs_with_edges
    ):
        direction = cross_lane_pairs()[(source_module, target_module)]
        ls_destination = IMPORT_ONLY_LS_DESTINATIONS.get(
            (source_module, target_module)
        )
        if ls_destination is None:
            raise ValueError(
                "import-only cross-lane edge lacks a reviewed canonical carrier: "
                f"{source_module} -> {target_module}"
            )
        qr_module = target_module if direction == "LS_TO_QR" else source_module
        qr_owner, status = qr_owner_initial_value(qr_module)
        rows.append(
            CrossLaneNormalization(
                "import",
                direction,
                "import",
                source_module,
                "-",
                target_module,
                "-",
                ls_destination,
                qr_owner,
                status,
            )
        )
    return sorted(rows, key=lambda row: tuple(row.__dict__.values()))


def cross_lane_bytes(contract: list[CrossLaneNormalization]) -> bytes:
    rows = ["format\t1"]
    rows.extend(
        "\t".join(("normalize", *row.__dict__.values())) for row in contract
    )
    return ("\n".join(rows) + "\n").encode("utf-8")


def cross_lane_base_identity(row: CrossLaneNormalization) -> tuple[str, ...]:
    """Return the immutable identity of one frozen typed/import edge."""

    return (
        row.row_type,
        row.direction,
        row.edge_kind,
        row.base_source_module,
        row.base_source_name,
        row.base_target_module,
        row.base_target_name,
    )


def qr_handoff_identity(row: CrossLaneNormalization) -> tuple[str, ...]:
    """Return one exact QR declaration/carrier identity requiring authority."""

    qr_module, qr_name = (
        (row.base_target_module, row.base_target_name)
        if row.direction == "LS_TO_QR"
        else (row.base_source_module, row.base_source_name)
    )
    if row.row_type == "edge":
        return ("edge", qr_module, qr_name, "-", "-")
    return (
        "import",
        qr_module,
        "-",
        row.base_source_module,
        row.base_target_module,
    )


def required_qr_handoff_identities(
    expected: list[CrossLaneNormalization],
) -> set[tuple[str, ...]]:
    return {
        qr_handoff_identity(row)
        for row in expected
        if row.status == "qr_owner_required"
    }


def read_qr_handoff(
    path: Path,
    expected: list[CrossLaneNormalization],
    expected_sha256: str,
    *,
    expected_mappings: int = EXPECTED_QR_HANDOFF_ROWS,
) -> dict[tuple[str, ...], str]:
    """Read a review-pinned QR owner/carrier handoff.

    The file hash is supplied independently by the integrator.  Metadata pins
    the QR delivery commit and its ownership artifact.  Edge mappings name one
    exact historical QR declaration; import mappings name the complete frozen
    module pair because an import-only carrier has no declaration witness.
    """

    if not HEX_SHA256.fullmatch(expected_sha256):
        raise ValueError("--qr-handoff-sha256 must contain 64 hex digits")
    payload = path.read_bytes()
    actual_sha256 = sha256_bytes(payload)
    if actual_sha256 != expected_sha256.upper():
        raise ValueError(
            "QR handoff SHA-256 differs from the separately reviewed digest"
        )

    try:
        text = payload.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ValueError(f"{path}: QR handoff is not UTF-8") from error
    rows = list(csv.reader(text.splitlines(), delimiter="\t"))
    if len(rows) < 3 or rows[0] != ["format", "1"]:
        raise ValueError(f"{path}: QR handoff must start with 'format\\t1'")
    if len(rows[1]) != 2 or rows[1][0] != "qr_commit" or not GIT_COMMIT_SHA.fullmatch(
        rows[1][1]
    ):
        raise ValueError(f"{path}: QR handoff lacks an exact 40-hex qr_commit")
    if (
        len(rows[2]) != 2
        or rows[2][0] != "qr_ownership_sha256"
        or not HEX_SHA256.fullmatch(rows[2][1])
    ):
        raise ValueError(
            f"{path}: QR handoff lacks a 64-hex qr_ownership_sha256"
        )

    required = required_qr_handoff_identities(expected)
    if len(required) != expected_mappings:
        raise ValueError(
            "frozen cross-lane contract has an unexpected number of QR "
            f"handoff identities: {len(required)} != {expected_mappings}"
        )

    owners: dict[tuple[str, ...], str] = {}
    order: list[tuple[str, ...]] = []
    for line_number, row in enumerate(rows[3:], 4):
        if len(row) != 7 or row[0] != "owner":
            raise ValueError(
                f"{path}:{line_number}: expected one seven-column owner row"
            )
        row_type, qr_module, qr_name, base_source, base_target, owner = row[1:]
        if row_type not in {"edge", "import"}:
            raise ValueError(f"{path}:{line_number}: invalid QR handoff row type")
        check_module_name(qr_module, f"{path}:{line_number}")
        check_module_name(owner, f"{path}:{line_number}")
        if not owner.startswith("NumStability."):
            raise ValueError(
                f"{path}:{line_number}: QR owner lies outside NumStability"
            )
        if owner.startswith("NumStability.Algorithms.QR.Higham19"):
            raise ValueError(
                f"{path}:{line_number}: QR owner is still a Higham19 wrapper"
            )
        if row_type == "edge":
            if qr_name == "-" or base_source != "-" or base_target != "-":
                raise ValueError(
                    f"{path}:{line_number}: edge mapping must name one declaration"
                )
            identity = (row_type, qr_module, qr_name, "-", "-")
        else:
            if qr_name != "-":
                raise ValueError(
                    f"{path}:{line_number}: import mapping must use '-' name"
                )
            check_module_name(base_source, f"{path}:{line_number}")
            check_module_name(base_target, f"{path}:{line_number}")
            identity = (
                row_type,
                qr_module,
                "-",
                base_source,
                base_target,
            )
        if identity in owners:
            raise ValueError(f"{path}:{line_number}: duplicate QR handoff identity")
        owners[identity] = owner
        order.append(identity)

    if order != sorted(order):
        raise ValueError(f"{path}: QR handoff owner rows must be sorted")
    actual = set(owners)
    if actual != required:
        raise ValueError(
            "QR handoff identities differ from the frozen placeholder set: "
            f"missing={sorted(required - actual)[:20]}; "
            f"extra={sorted(actual - required)[:20]}"
        )
    return owners


def validate_cross_lane_artifact_contract(
    expected: list[CrossLaneNormalization],
    committed: list[CrossLaneNormalization],
    *,
    qr_handoff: dict[tuple[str, ...], str] | None = None,
    require_qr_resolved: bool = False,
    expected_rows: int = EXPECTED_CROSS_LANE_ROWS,
    expected_edge_rows: int = EXPECTED_CROSS_LANE_EDGE_ROWS,
    expected_import_rows: int = EXPECTED_CROSS_LANE_IMPORT_ROWS,
) -> None:
    """Freeze every base-derived row while allowing reviewed QR resolution.

    The first eight fields (the base edge identity plus ``ls_destination``)
    are regenerated from the hash-pinned baseline and the compiler-span route
    manifest in every mode.  A row whose base QR owner was already canonical
    is wholly immutable.  An explicit ``@QR_OWNER_REQUIRED:*`` owner may only
    change when a separately hash-pinned QR handoff maps its exact declaration
    or import-only carrier identity to that owner.
    """

    expected_types = Counter(row.row_type for row in expected)
    required_types = Counter(
        {"edge": expected_edge_rows, "import": expected_import_rows}
    )
    if len(expected) != expected_rows or expected_types != required_types:
        raise ValueError(
            "authoritative cross-lane regeneration has unexpected cardinality: "
            f"rows={len(expected)}/{expected_rows}, "
            f"types={dict(expected_types)}/{dict(required_types)}"
        )
    if len(committed) != expected_rows:
        raise ValueError(
            "committed cross-lane normalization row count differs from the "
            f"frozen contract: {len(committed)} != {expected_rows}"
        )

    required_handoff = required_qr_handoff_identities(expected)
    if qr_handoff is not None and set(qr_handoff) != required_handoff:
        raise ValueError(
            "authoritative QR handoff coverage differs from the frozen "
            "placeholder identities"
        )
    if require_qr_resolved and qr_handoff is None:
        raise ValueError(
            "post mode requires a hash-pinned authoritative QR handoff"
        )

    expected_by_identity = {
        cross_lane_base_identity(row): row for row in expected
    }
    committed_by_identity = {
        cross_lane_base_identity(row): row for row in committed
    }
    if len(expected_by_identity) != len(expected):
        raise ValueError("authoritative cross-lane rows duplicate a base identity")
    if len(committed_by_identity) != len(committed):
        raise ValueError("committed cross-lane rows duplicate a base identity")

    expected_identities = set(expected_by_identity)
    committed_identities = set(committed_by_identity)
    if committed_identities != expected_identities:
        raise ValueError(
            "committed cross-lane row identities differ from the frozen base: "
            f"missing={sorted(expected_identities - committed_identities)[:20]}; "
            f"extra={sorted(committed_identities - expected_identities)[:20]}"
        )

    for identity in sorted(expected_identities):
        frozen = expected_by_identity[identity]
        actual = committed_by_identity[identity]
        if actual.ls_destination != frozen.ls_destination:
            raise ValueError(
                "committed cross-lane LS owner differs from the base-derived "
                f"route for {identity}: {actual.ls_destination} != "
                f"{frozen.ls_destination}"
            )

        if frozen.status == "resolved":
            expected_owner = QR_CANONICAL_RETARGETS.get(
                frozen.qr_owner, frozen.qr_owner
            )
            if (actual.qr_owner, actual.status) != (
                expected_owner,
                frozen.status,
            ):
                raise ValueError(
                    "an already-canonical QR owner changed in the cross-lane "
                    f"contract for {identity}"
                )
            continue

        if frozen.status != "qr_owner_required" or not QR_OWNER_PLACEHOLDER.fullmatch(
            frozen.qr_owner
        ):
            raise ValueError(
                f"authoritative cross-lane row has invalid QR placeholder: {identity}"
            )
        if actual.status == "qr_owner_required":
            if actual.qr_owner != frozen.qr_owner:
                raise ValueError(
                    "an unresolved QR placeholder changed in the cross-lane "
                    f"contract for {identity}"
                )
            if require_qr_resolved:
                raise ValueError(
                    "post integration is forbidden while a QR placeholder "
                    f"remains for {identity}"
                )
            continue
        if actual.status != "resolved":
            raise ValueError(
                f"cross-lane QR resolution has invalid status for {identity}"
            )
        check_module_name(actual.qr_owner, f"cross-lane QR owner for {identity}")
        if actual.qr_owner.startswith("NumStability.Algorithms.QR.Higham19"):
            raise ValueError(
                "resolved cross-lane QR owner is still a Higham19 compatibility "
                f"wrapper for {identity}"
            )
        handoff_identity = qr_handoff_identity(frozen)
        if qr_handoff is None:
            raise ValueError(
                "QR placeholder resolution lacks a hash-pinned authoritative "
                f"handoff for {handoff_identity}"
            )
        if actual.qr_owner != qr_handoff[handoff_identity]:
            raise ValueError(
                "resolved QR owner differs from the authoritative handoff for "
                f"{handoff_identity}: {actual.qr_owner} != "
                f"{qr_handoff[handoff_identity]}"
            )


def write_cross_lane_normalization(
    path: Path, contract: list[CrossLaneNormalization]
) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(cross_lane_bytes(contract))


def validate_cross_lane_base_contract(
    project_root: Path,
    dependency_tsv: Path,
    declarations: list[Declaration],
    actual_to_logical: dict[str, str],
    records: dict[str, ManifestRow],
    contract: list[CrossLaneNormalization],
    import_graph: dict[str, list[str]] | None = None,
) -> tuple[int, int, int]:
    graph = read_module_imports(project_root) if import_graph is None else import_graph
    pairs = cross_lane_pairs()
    missing_base_imports = [
        (source, target)
        for source, target in sorted(pairs)
        if target not in graph.get(source, [])
    ]
    if missing_base_imports:
        raise ValueError(
            "frozen cross-lane direct imports differ at the base: "
            f"{missing_base_imports[:20]}"
        )

    expected_edges = expected_cross_lane_edges(
        dependency_tsv, declarations, actual_to_logical, records
    )
    actual_edges = {
        (
            row.direction,
            row.edge_kind,
            row.base_source_module,
            row.base_source_name,
            row.base_target_module,
            row.base_target_name,
            row.ls_destination,
        )
        for row in contract
        if row.row_type == "edge"
    }
    if actual_edges != expected_edges:
        raise ValueError(
            "cross-lane declaration-edge freeze differs: "
            f"missing={sorted(expected_edges - actual_edges)[:20]}; "
            f"extra={sorted(actual_edges - expected_edges)[:20]}"
        )

    pairs_with_edges = {
        (source_module, target_module)
        for _, _, source_module, _, target_module, _, _ in expected_edges
    }
    expected_import_only = set(pairs) - pairs_with_edges
    actual_import_only = {
        (row.base_source_module, row.base_target_module)
        for row in contract
        if row.row_type == "import"
    }
    if actual_import_only != expected_import_only:
        raise ValueError(
            "cross-lane import-only freeze differs: "
            f"missing={sorted(expected_import_only - actual_import_only)}; "
            f"extra={sorted(actual_import_only - expected_import_only)}"
        )
    return len(FROZEN_LS_TO_QR), len(FROZEN_QR_TO_LS), len(expected_edges)


def validate_cross_lane_final_contract(
    contract: list[CrossLaneNormalization],
    declarations: list[Declaration],
    import_graph: dict[str, list[str]],
    records: dict[str, ManifestRow],
    qr_handoff: dict[tuple[str, ...], str],
) -> tuple[int, int]:
    if not qr_handoff:
        raise ValueError("final cross-lane validation requires a QR handoff map")
    unresolved = [row for row in contract if row.status != "resolved"]
    if unresolved:
        required = sorted(
            {
                (row.base_source_module, row.base_source_name)
                if row.direction == "QR_TO_LS"
                else (row.base_target_module, row.base_target_name)
                for row in unresolved
            }
        )
        raise ValueError(
            "QR canonical ownership is unresolved; post integration is forbidden "
            f"until the QR lane fills {len(required)} exact owner mappings: "
            f"{required[:20]}"
        )

    module_by_name = {
        declaration.name: declaration.module for declaration in declarations
    }
    required_imports: set[tuple[str, str]] = set()
    compatibility_qr = {
        row.base_target_module
        for row in contract
        if row.direction == "LS_TO_QR"
        and row.base_target_module.startswith("NumStability.Algorithms.QR.Higham19")
    } | {
        row.base_source_module
        for row in contract
        if row.direction == "QR_TO_LS"
        and row.base_source_module.startswith("NumStability.Algorithms.QR.Higham19")
    }
    for row in contract:
        handoff_identity = qr_handoff_identity(row)
        if handoff_identity in qr_handoff and row.qr_owner != qr_handoff[handoff_identity]:
            raise ValueError(
                "final QR owner differs from the authoritative handoff for "
                f"{handoff_identity}: {row.qr_owner} != "
                f"{qr_handoff[handoff_identity]}"
            )
        qr_name = (
            row.base_target_name
            if row.direction == "LS_TO_QR"
            else row.base_source_name
        )
        if row.row_type == "edge" and module_by_name.get(qr_name) != row.qr_owner:
            raise ValueError(
                f"QR declaration {qr_name} is owned by {module_by_name.get(qr_name)}, "
                f"not contracted owner {row.qr_owner}"
            )
        final_source, final_target = (
            (row.ls_destination, row.qr_owner)
            if row.direction == "LS_TO_QR"
            else (row.qr_owner, row.ls_destination)
        )
        required_imports.add((final_source, final_target))

    missing = sorted(
        (source, target)
        for source, target in required_imports
        if target not in import_graph.get(source, [])
    )
    if missing:
        raise ValueError(
            "final canonical cross-lane imports are missing: " f"{missing[:20]}"
        )

    production_modules = {
        row.destination_module for row in records.values()
    } | {row.qr_owner for row in contract}
    forbidden_wrappers = set(ALL_COMPATIBILITY_WRAPPERS) | compatibility_qr
    forbidden = sorted(
        (module, dependency)
        for module in production_modules
        for dependency in import_graph.get(module, [])
        if dependency in forbidden_wrappers
    )
    if forbidden:
        raise ValueError(
            "final production modules import compatibility wrappers: "
            f"{forbidden[:20]}"
        )
    return len(required_imports), len(production_modules)


def normalized_incident_graph_delta(
    baseline_tsv: Path,
    candidate_tsv: Path,
    baseline: dict[str, Declaration],
    candidate_actual_to_logical: dict[str, str],
    records: dict[str, ManifestRow],
) -> Counter[str]:
    """Return the selected LS incident graph delta as a row multiset.

    The contract owns all selected LS declaration rows and every typed edge
    with at least one selected LS endpoint.  Rows wholly outside that incident
    set belong to other integration lanes and are deliberately ignored.  This
    lets a QR or BlockLU declaration move modules without weakening any edge
    entering or leaving an LS declaration.
    """

    candidate_to_baseline_name = {
        candidate: baseline[logical].name
        for candidate, logical in candidate_actual_to_logical.items()
    }
    candidate_to_historical_module = {
        candidate: records[logical].historical_module
        for candidate, logical in candidate_actual_to_logical.items()
    }
    baseline_names = {declaration.name for declaration in baseline.values()}
    candidate_names = set(candidate_actual_to_logical)

    delta: Counter[str] = Counter()
    for declaration in baseline.values():
        delta[
            "\t".join(
                (
                    "declaration",
                    declaration.name,
                    declaration.module,
                    declaration.kind,
                    declaration.visibility,
                )
            )
        ] += 1
    for edge in iter_dependency_edges(baseline_tsv):
        if edge.source in baseline_names or edge.target in baseline_names:
            delta[
                "\t".join(("edge", edge.kind, edge.source, edge.target))
            ] += 1

    candidate_declarations = {
        declaration.name: declaration
        for declaration in read_dependency_declarations(candidate_tsv)
    }
    for candidate_name, logical in candidate_actual_to_logical.items():
        declaration = candidate_declarations.get(candidate_name)
        if declaration is None:
            raise ValueError(
                f"candidate LS declaration is absent from graph: {candidate_name}"
            )
        delta[
            "\t".join(
                (
                    "declaration",
                    candidate_to_baseline_name[candidate_name],
                    candidate_to_historical_module[candidate_name],
                    declaration.kind,
                    declaration.visibility,
                )
            )
        ] -= 1

    # Include historical private names as incident sentinels.  A stale edge
    # that still names a pre-move private declaration is therefore an extra
    # contracted edge rather than disappearing into the unrelated graph.
    candidate_incident_names = candidate_names | baseline_names
    for edge in iter_dependency_edges(candidate_tsv):
        if (
            edge.source not in candidate_incident_names
            and edge.target not in candidate_incident_names
        ):
            continue
        source = candidate_to_baseline_name.get(edge.source, edge.source)
        target = candidate_to_baseline_name.get(edge.target, edge.target)
        delta["\t".join(("edge", edge.kind, source, target))] -= 1

    for row in list(delta):
        if delta[row] == 0:
            del delta[row]

    return delta


def validate_normalized_graph_delta(delta: Counter[str]) -> None:
    if not delta:
        return
    missing = sum(count for count in delta.values() if count > 0)
    extra = -sum(count for count in delta.values() if count < 0)
    details = "; ".join(f"{count:+d} {row}" for row, count in sorted(delta.items())[:20])
    raise ValueError(
        "normalized contracted graph differs from the frozen lane baseline: "
        f"missing={missing}, extra={extra}; {details}"
    )


def compare_lane_incident_graph(
    baseline_tsv: Path,
    candidate_tsv: Path,
    baseline: dict[str, Declaration],
    candidate_actual_to_logical: dict[str, str],
    records: dict[str, ManifestRow],
    expected_baseline_sha256: str | None = BASELINE_TSV_SHA256,
) -> None:
    """Require the exact LS declaration/incident graph after normalization."""

    if expected_baseline_sha256 is not None:
        if sha256_file(baseline_tsv) != expected_baseline_sha256:
            raise ValueError("baseline TSV hash differs from the frozen lane input")
    delta = normalized_incident_graph_delta(
        baseline_tsv, candidate_tsv, baseline, candidate_actual_to_logical, records
    )
    validate_normalized_graph_delta(delta)


def validate_expected_manifest_digest(
    records: dict[str, ManifestRow], expected: str | None
) -> str:
    digest = sha256_bytes(manifest_bytes(records))
    if expected is not None:
        if not HEX_SHA256.fullmatch(expected):
            raise ValueError("--expected-manifest-sha256 must contain 64 hex digits")
        if digest != expected.upper():
            raise ValueError(
                f"canonical manifest hash differs: expected {expected.upper()}, "
                f"found {digest}"
            )
    return digest


# ----------------------------------------------------------------------------
# Self-test
# ----------------------------------------------------------------------------

SELF_HISTORICAL_A = f"{LS_PREFIX}.LSQRSolve"
SELF_HISTORICAL_B = f"{LS_PREFIX}.LSPerturbation"
SELF_REUSABLE = f"{REUSABLE_ALGORITHM_ROOT}.Residual"
SELF_ANALYSIS = f"{REUSABLE_ANALYSIS_ROOT}.Wedin"
SELF_SOURCE = f"{SOURCE_ROOT}.Theorem03"
SELF_OTHER_NAME = "NumStability.otherDeclaration"
SELF_OTHER_TARGET = "NumStability.otherDependency"
SELF_OTHER_OLD = "NumStability.Other.Old"
SELF_OTHER_NEW = "NumStability.Other.New"
SELF_COUNTS = {SELF_HISTORICAL_A: 4, SELF_HISTORICAL_B: 2}
SELF_PRIVATE_LOGICAL = f"_private.{SELF_HISTORICAL_A}.NumStability.lsHelper"


def _self_declarations() -> list[Declaration]:
    return [
        Declaration("NumStability.lsResidual", SELF_HISTORICAL_A, "definition", "public"),
        Declaration(
            "NumStability.lsResidual.eq_1",
            SELF_HISTORICAL_A,
            "theorem",
            "public",
        ),
        Declaration(
            "NumStability.lsResidual_permuteRows", SELF_HISTORICAL_A, "theorem", "public"
        ),
        Declaration(
            f"_private.{SELF_HISTORICAL_A}.0.NumStability.lsHelper",
            SELF_HISTORICAL_A,
            "theorem",
            "private",
        ),
        Declaration(
            "NumStability.wedinLemma20_11_bound", SELF_HISTORICAL_B, "theorem", "public"
        ),
        Declaration(
            "NumStability.theorem20_3_source", SELF_HISTORICAL_B, "theorem", "public"
        ),
        Declaration("NumStability.qrExternal", "NumStability.Algorithms.QR.QRSolve", "theorem", "public"),
        Declaration(SELF_OTHER_NAME, SELF_OTHER_OLD, "theorem", "public"),
        Declaration(
            SELF_OTHER_TARGET,
            "NumStability.Other.Dependency",
            "theorem",
            "public",
        ),
    ]


def _self_stream(declarations: list[Declaration], edges: list[DependencyEdge]) -> str:
    rows = ["format\t2"]
    rows.extend(
        "\t".join(("declaration", d.name, d.module, d.kind, d.visibility))
        for d in declarations
    )
    rows.extend("\t".join(("edge", e.kind, e.source, e.target)) for e in edges)
    return "\n".join(rows) + "\n"


def _self_edges() -> list[DependencyEdge]:
    return [
        DependencyEdge("signature", "NumStability.lsResidual_permuteRows", "NumStability.lsResidual"),
        DependencyEdge(
            "body",
            "NumStability.lsResidual_permuteRows",
            f"_private.{SELF_HISTORICAL_A}.0.NumStability.lsHelper",
        ),
        DependencyEdge("body", "NumStability.theorem20_3_source", "NumStability.lsResidual"),
        DependencyEdge(
            "signature", "NumStability.wedinLemma20_11_bound", "NumStability.wedinLemma20_11_bound"
        ),
        DependencyEdge(
            "body", "NumStability.wedinLemma20_11_bound", "NumStability.lsResidual"
        ),
        DependencyEdge("body", "NumStability.lsResidual", "NumStability.qrExternal"),
        DependencyEdge("body", SELF_OTHER_NAME, SELF_OTHER_TARGET),
    ]


def _self_manifest() -> dict[str, ManifestRow]:
    return {
        "NumStability.lsResidual": ManifestRow(
            "NumStability.lsResidual", SELF_HISTORICAL_A, SELF_REUSABLE, "definition", "public"
        ),
        "NumStability.lsResidual.eq_1": ManifestRow(
            "NumStability.lsResidual.eq_1",
            SELF_HISTORICAL_A,
            SELF_REUSABLE,
            "theorem",
            "public",
        ),
        "NumStability.lsResidual_permuteRows": ManifestRow(
            "NumStability.lsResidual_permuteRows",
            SELF_HISTORICAL_A,
            SELF_REUSABLE,
            "theorem",
            "public",
        ),
        SELF_PRIVATE_LOGICAL: ManifestRow(
            SELF_PRIVATE_LOGICAL,
            SELF_HISTORICAL_A,
            SELF_REUSABLE,
            "theorem",
            "private",
        ),
        "NumStability.wedinLemma20_11_bound": ManifestRow(
            "NumStability.wedinLemma20_11_bound",
            SELF_HISTORICAL_B,
            SELF_ANALYSIS,
            "theorem",
            "public",
        ),
        "NumStability.theorem20_3_source": ManifestRow(
            "NumStability.theorem20_3_source",
            SELF_HISTORICAL_B,
            SELF_SOURCE,
            "theorem",
            "public",
        ),
    }


def run_self_test() -> None:
    def expect_value_error(action: Callable[[], object], label: str) -> None:
        try:
            action()
        except ValueError:
            return
        raise AssertionError(f"self-test did not reject {label}")

    declarations = _self_declarations()
    edges = _self_edges()
    records = _self_manifest()
    baseline = selected_baseline_declarations(declarations, SELF_COUNTS)
    assert len(baseline) == 6, baseline
    validate_manifest_shape(records, SELF_COUNTS)
    validate_manifest_against_baseline(records, baseline)

    assert logical_name("NumStability.x", SELF_HISTORICAL_A) == "NumStability.x"
    assert (
        logical_name(f"_private.{SELF_HISTORICAL_A}.0.NumStability.lsHelper", SELF_HISTORICAL_A)
        == SELF_PRIVATE_LOGICAL
    )
    expect_value_error(
        lambda: logical_name(f"_private.{SELF_HISTORICAL_B}.0.NumStability.x", SELF_HISTORICAL_A),
        "a private name that does not encode its owner",
    )

    # 1. Missing declaration.
    expect_value_error(
        lambda: selected_baseline_declarations(declarations[1:], SELF_COUNTS),
        "a missing historical declaration",
    )
    # 2. Duplicated declaration.
    expect_value_error(
        lambda: selected_baseline_declarations(declarations + [declarations[0]], SELF_COUNTS),
        "a duplicated historical declaration",
    )
    # 3. Public name drift.
    drifted_names = [
        Declaration("NumStability.lsResidualRenamed", d.module, d.kind, d.visibility)
        if d.name == "NumStability.lsResidual"
        else d
        for d in declarations
    ]
    expect_value_error(
        lambda: validate_manifest_against_baseline(
            records, selected_baseline_declarations(drifted_names, SELF_COUNTS)
        ),
        "public declaration name drift",
    )
    # 4. Kind (signature shape) drift.
    drifted_kind = [
        Declaration(d.name, d.module, "theorem" if d.kind == "definition" else d.kind, d.visibility)
        for d in declarations
    ]
    expect_value_error(
        lambda: validate_manifest_against_baseline(
            records, selected_baseline_declarations(drifted_kind, SELF_COUNTS)
        ),
        "declaration kind drift",
    )
    # 5. Visibility drift.
    drifted_visibility = dict(records)
    drifted_visibility["NumStability.lsResidual"] = ManifestRow(
        "NumStability.lsResidual", SELF_HISTORICAL_A, SELF_REUSABLE, "definition", "private"
    )
    expect_value_error(
        lambda: validate_manifest_shape(drifted_visibility, SELF_COUNTS),
        "a private visibility without a normalized private name",
    )
    # 6. Destination that stays in the legacy family.
    legacy_destination = dict(records)
    legacy_destination["NumStability.lsResidual"] = ManifestRow(
        "NumStability.lsResidual",
        SELF_HISTORICAL_A,
        f"{LS_PREFIX}.LSResidual",
        "definition",
        "public",
    )
    expect_value_error(
        lambda: validate_manifest_shape(legacy_destination, SELF_COUNTS),
        "a destination inside the legacy least-squares family",
    )

    with tempfile.TemporaryDirectory() as raw:
        root = Path(raw)
        baseline_tsv = root / "baseline.tsv"
        baseline_tsv.write_text(_self_stream(declarations, edges), encoding="utf-8")

        actual_to_logical = baseline_actual_to_logical(baseline)
        owners, edge_count = validate_destination_graph(
            baseline_tsv, declarations, actual_to_logical, records
        )
        assert owners == 3, owners
        assert edge_count >= 1, edge_count
        self_dag = destination_dag_from_stream(
            baseline_tsv, actual_to_logical, records
        )
        assert len(self_dag) == 2, self_dag
        validate_destination_dag_contract(
            baseline_tsv, actual_to_logical, records, self_dag
        )
        drifted_dag = dict(self_dag)
        first_pair = sorted(drifted_dag)[0]
        signature_count, body_count = drifted_dag[first_pair]
        drifted_dag[first_pair] = (signature_count, body_count + 1)
        expect_value_error(
            lambda: validate_destination_dag_contract(
                baseline_tsv, actual_to_logical, records, drifted_dag
            ),
            "a changed typed destination-DAG count",
        )

        # 6b. A private declaration may not be used across a destination
        # boundary: a Lean private name is scoped to its defining module, so the
        # use would be an unknown identifier.  The fixture co-locates the private
        # helper with its user, and moving only the helper must be rejected.
        private_checked = validate_private_colocation(
            baseline_tsv, declarations, actual_to_logical, records
        )
        assert private_checked == 1, private_checked
        split_private = dict(records)
        split_private[SELF_PRIVATE_LOGICAL] = ManifestRow(
            SELF_PRIVATE_LOGICAL,
            SELF_HISTORICAL_A,
            SELF_ANALYSIS,
            "theorem",
            "private",
        )
        expect_value_error(
            lambda: validate_private_colocation(
                baseline_tsv, declarations, actual_to_logical, split_private
            ),
            "a private declaration used from another destination",
        )

        # 7. Forbidden reusable -> source declaration edge.
        inverted = dict(records)
        inverted["NumStability.theorem20_3_source"] = ManifestRow(
            "NumStability.theorem20_3_source",
            SELF_HISTORICAL_B,
            SELF_SOURCE,
            "theorem",
            "public",
        )
        inverted["NumStability.lsResidual"] = ManifestRow(
            "NumStability.lsResidual", SELF_HISTORICAL_A, SELF_REUSABLE, "definition", "public"
        )
        forbidden_tsv = root / "forbidden.tsv"
        forbidden_tsv.write_text(
            _self_stream(
                declarations,
                edges
                + [
                    DependencyEdge(
                        "body", "NumStability.lsResidual", "NumStability.theorem20_3_source"
                    )
                ],
            ),
            encoding="utf-8",
        )
        expect_value_error(
            lambda: validate_destination_graph(
                forbidden_tsv, declarations, actual_to_logical, inverted
            ),
            "a reusable destination depending on a source declaration",
        )

        # 8. Owner cycle.
        cyclic = dict(records)
        cyclic["NumStability.wedinLemma20_11_bound"] = ManifestRow(
            "NumStability.wedinLemma20_11_bound",
            SELF_HISTORICAL_B,
            SELF_ANALYSIS,
            "theorem",
            "public",
        )
        cycle_tsv = root / "cycle.tsv"
        cycle_tsv.write_text(
            _self_stream(
                declarations,
                edges
                + [
                    DependencyEdge(
                        "body", "NumStability.lsResidual", "NumStability.wedinLemma20_11_bound"
                    ),
                    DependencyEdge(
                        "body", "NumStability.wedinLemma20_11_bound", "NumStability.lsResidual"
                    ),
                ],
            ),
            encoding="utf-8",
        )
        expect_value_error(
            lambda: validate_destination_graph(
                cycle_tsv, declarations, actual_to_logical, cyclic
            ),
            "a destination ownership cycle",
        )

        # Candidate stream after a completed move of both reusable owners.
        moved = [
            Declaration("NumStability.lsResidual", SELF_REUSABLE, "definition", "public"),
            Declaration(
                "NumStability.lsResidual.eq_1",
                SELF_REUSABLE,
                "theorem",
                "public",
            ),
            Declaration("NumStability.lsResidual_permuteRows", SELF_REUSABLE, "theorem", "public"),
            Declaration(
                f"_private.{SELF_REUSABLE}.0.NumStability.lsHelper",
                SELF_REUSABLE,
                "theorem",
                "private",
            ),
            Declaration("NumStability.wedinLemma20_11_bound", SELF_ANALYSIS, "theorem", "public"),
            Declaration("NumStability.theorem20_3_source", SELF_SOURCE, "theorem", "public"),
            Declaration(
                "NumStability.qrExternal", "NumStability.Algorithms.QR.QRSolve", "theorem", "public"
            ),
            # This other-lane declaration moves modules.  The LS incident
            # graph must accept it because neither the declaration nor its
            # edge has an LS endpoint.
            Declaration(SELF_OTHER_NAME, SELF_OTHER_NEW, "theorem", "public"),
            Declaration(
                SELF_OTHER_TARGET,
                "NumStability.Other.Dependency",
                "theorem",
                "public",
            ),
        ]
        moved_edges = [
            DependencyEdge(
                "signature", "NumStability.lsResidual_permuteRows", "NumStability.lsResidual"
            ),
            DependencyEdge(
                "body",
                "NumStability.lsResidual_permuteRows",
                f"_private.{SELF_REUSABLE}.0.NumStability.lsHelper",
            ),
            DependencyEdge("body", "NumStability.theorem20_3_source", "NumStability.lsResidual"),
            DependencyEdge(
                "signature",
                "NumStability.wedinLemma20_11_bound",
                "NumStability.wedinLemma20_11_bound",
            ),
            DependencyEdge(
                "body", "NumStability.wedinLemma20_11_bound", "NumStability.lsResidual"
            ),
            DependencyEdge("body", "NumStability.lsResidual", "NumStability.qrExternal"),
            DependencyEdge("body", SELF_OTHER_NAME, SELF_OTHER_TARGET),
        ]
        rewrites_path = root / "rewrites.tsv"
        rewrites_path.write_text(
            "format\t1\n"
            f"{SELF_PRIVATE_LOGICAL}\t"
            f"_private.{SELF_HISTORICAL_A}.0.NumStability.lsHelper\t"
            f"_private.{SELF_REUSABLE}.0.NumStability.lsHelper\n",
            encoding="utf-8",
        )
        rewrites = read_private_rewrites(rewrites_path, records, baseline)
        assert set(rewrites) == {SELF_PRIVATE_LOGICAL}

        # 9. Unexplained private mapping.
        bad_rewrites = root / "bad-rewrites.tsv"
        bad_rewrites.write_text(
            "format\t1\n"
            f"{SELF_PRIVATE_LOGICAL}\t"
            f"_private.{SELF_HISTORICAL_A}.0.NumStability.lsHelper\t"
            f"_private.{SELF_ANALYSIS}.0.NumStability.lsHelper\n",
            encoding="utf-8",
        )
        expect_value_error(
            lambda: read_private_rewrites(bad_rewrites, records, baseline),
            "a private rewrite that does not normalize from its destination",
        )
        empty_rewrites = root / "empty-rewrites.tsv"
        empty_rewrites.write_text("format\t1\n", encoding="utf-8")
        expect_value_error(
            lambda: read_private_rewrites(empty_rewrites, records, baseline),
            "missing private rewrite coverage",
        )

        candidate_map = check_candidate_ownership(records, baseline, moved, rewrites)
        assert len(candidate_map) == 6, candidate_map
        expect_value_error(
            lambda: check_candidate_ownership(
                records,
                baseline,
                moved
                + [
                    Declaration(
                        "NumStability.edgeFreeUncontractedDeclaration",
                        SELF_REUSABLE,
                        "theorem",
                        "public",
                    )
                ],
                rewrites,
            ),
            "an edge-free public declaration added to a selected owner",
        )

        candidate_tsv = root / "candidate.tsv"
        candidate_tsv.write_text(_self_stream(moved, moved_edges), encoding="utf-8")
        # Positive scope test: candidate.tsv contains an unrelated
        # Other.Old -> Other.New declaration move and an unrelated typed edge.
        # The LS incident contract accepts both while retaining every LS edge.
        compare_lane_incident_graph(
            baseline_tsv, candidate_tsv, baseline, candidate_map, records, None
        )

        # 10. Lost contracted LS-incident typed edge.
        lost_tsv = root / "lost.tsv"
        lost_tsv.write_text(_self_stream(moved, moved_edges[1:]), encoding="utf-8")
        expect_value_error(
            lambda: compare_lane_incident_graph(
                baseline_tsv, lost_tsv, baseline, candidate_map, records, None
            ),
            "a lost typed edge",
        )
        # 11. Extra typed edge.
        extra_tsv = root / "extra.tsv"
        extra_tsv.write_text(
            _self_stream(
                moved,
                moved_edges
                + [
                    DependencyEdge(
                        "body", "NumStability.lsResidual", "NumStability.wedinLemma20_11_bound"
                    )
                ],
            ),
            encoding="utf-8",
        )
        expect_value_error(
            lambda: compare_lane_incident_graph(
                baseline_tsv, extra_tsv, baseline, candidate_map, records, None
            ),
            "an extra typed edge",
        )
        # 12. Lost self-edge.
        without_self = [
            e
            for e in moved_edges
            if not (e.source == e.target == "NumStability.wedinLemma20_11_bound")
        ]
        self_tsv = root / "selfedge.tsv"
        self_tsv.write_text(_self_stream(moved, without_self), encoding="utf-8")
        expect_value_error(
            lambda: compare_lane_incident_graph(
                baseline_tsv, self_tsv, baseline, candidate_map, records, None
            ),
            "a lost declaration self-edge",
        )
        # 13. Baseline digest drift.
        expect_value_error(
            lambda: compare_lane_incident_graph(
                baseline_tsv,
                candidate_tsv,
                baseline,
                candidate_map,
                records,
                "0" * 64,
            ),
            "a baseline stream whose digest changed",
        )

        # Structural wrapper and reusable-isolation checks on a synthetic tree.
        project = root / "project"
        (project / "NumStability/Algorithms/LinearSystems/LeastSquares").mkdir(
            parents=True, exist_ok=True
        )
        (project / "NumStability/Analysis/Perturbation/LeastSquares").mkdir(
            parents=True, exist_ok=True
        )
        (project / "NumStability/Source/Higham/Chapter20").mkdir(parents=True, exist_ok=True)
        (project / "NumStability/Algorithms/LeastSquares").mkdir(parents=True, exist_ok=True)
        (project / "NumStability/Algorithms/QR").mkdir(parents=True, exist_ok=True)

        residual = project / "NumStability/Algorithms/LinearSystems/LeastSquares/Residual.lean"
        residual.write_text(
            "/-! Residual API. -/\nimport NumStability.Algorithms.QR.QRSolve\n",
            encoding="utf-8",
        )
        (project / "NumStability/Analysis/Perturbation/LeastSquares/Wedin.lean").write_text(
            "/-! Wedin analysis. -/\n"
            "import NumStability.Algorithms.LinearSystems.LeastSquares.Residual\n",
            encoding="utf-8",
        )
        (project / "NumStability/Source/Higham/Chapter20/Theorem03.lean").write_text(
            "/-! Theorem 20.3. -/\n"
            "import NumStability.Algorithms.LinearSystems.LeastSquares.Residual\n",
            encoding="utf-8",
        )
        (project / "NumStability/Algorithms/QR/QRSolve.lean").write_text(
            "/-! QR solve. -/\n", encoding="utf-8"
        )
        wrapper = project / "NumStability/Algorithms/LeastSquares/LSQRSolve.lean"
        wrapper.write_text(
            "/-! Historical wrapper. -/\n"
            "import NumStability.Algorithms.LinearSystems.LeastSquares.Residual\n"
            "import NumStability.Algorithms.QR.QRSolve\n",
            encoding="utf-8",
        )
        (project / "NumStability/Algorithms/LeastSquares/LSPerturbation.lean").write_text(
            "/-! Historical wrapper. -/\n"
            "import NumStability.Analysis.Perturbation.LeastSquares.Wedin\n"
            "import NumStability.Source.Higham.Chapter20.Theorem03\n",
            encoding="utf-8",
        )

        graph = read_module_imports(project)
        assert SELF_REUSABLE in graph, sorted(graph)
        assert validate_reusable_isolation(project, records, graph) == 2
        validate_destination_direct_imports(
            graph, records, self_dag, {SELF_REUSABLE, SELF_ANALYSIS, SELF_SOURCE}
        )
        missing_dag_import = dict(graph)
        missing_dag_import[SELF_SOURCE] = []
        expect_value_error(
            lambda: validate_destination_direct_imports(
                missing_dag_import,
                records,
                self_dag,
                {SELF_REUSABLE, SELF_ANALYSIS, SELF_SOURCE},
            ),
            "a missing direct destination-DAG import",
        )
        extra_dag_import = dict(graph)
        extra_dag_import[SELF_REUSABLE] = graph[SELF_REUSABLE] + [SELF_ANALYSIS]
        expect_value_error(
            lambda: validate_destination_direct_imports(
                extra_dag_import,
                records,
                self_dag,
                {SELF_REUSABLE, SELF_ANALYSIS, SELF_SOURCE},
            ),
            "an extra direct destination-DAG import",
        )

        # 14. Forbidden transitive reusable -> source import.
        bad_graph = dict(graph)
        bad_graph[SELF_REUSABLE] = graph[SELF_REUSABLE] + [SELF_SOURCE]
        expect_value_error(
            lambda: validate_reusable_isolation(project, records, bad_graph),
            "a reusable module importing a canonical source leaf",
        )
        assert (
            validate_reusable_isolation(
                project,
                records,
                bad_graph,
                allowed_direct_imports={(SELF_REUSABLE, SELF_SOURCE)},
            )
            == 2
        )
        ch7_graph = dict(graph)
        ch7_graph[SELF_REUSABLE] = graph[SELF_REUSABLE] + [CHAPTER_SEVEN]
        expect_value_error(
            lambda: validate_reusable_isolation(project, records, ch7_graph),
            "a reusable module reaching Analysis.HighamChapter7",
        )

        # 15. Final cross-lane normalization is canonical on both sides.
        qr_source_owner = "NumStability.Source.Higham.Chapter19.Problem10"
        qr_source_path = project / "NumStability/Source/Higham/Chapter19/Problem10.lean"
        qr_source_path.parent.mkdir(parents=True, exist_ok=True)
        qr_source_path.write_text(
            "/-! QR source owner. -/\n"
            "import NumStability.Analysis.Perturbation.LeastSquares.Wedin\n",
            encoding="utf-8",
        )
        graph = read_module_imports(project)
        self_cross = [
            CrossLaneNormalization(
                "edge",
                "LS_TO_QR",
                "body",
                SELF_HISTORICAL_A,
                "NumStability.lsResidual",
                "NumStability.Algorithms.QR.QRSolve",
                "NumStability.qrExternal",
                SELF_REUSABLE,
                "NumStability.Algorithms.QR.QRSolve",
                "resolved",
            ),
            CrossLaneNormalization(
                "import",
                "QR_TO_LS",
                "import",
                "NumStability.Algorithms.QR.Higham19Problem19_10",
                "-",
                f"{LS_PREFIX}.Higham20CrossProductExample",
                "-",
                SELF_ANALYSIS,
                qr_source_owner,
                "resolved",
            ),
        ]
        frozen_self_cross = [
            replace(
                self_cross[0],
                qr_owner=(
                    "@QR_OWNER_REQUIRED:NumStability.Algorithms.QR.QRSolve"
                ),
                status="qr_owner_required",
            ),
            replace(
                self_cross[1],
                qr_owner=(
                    "@QR_OWNER_REQUIRED:"
                    "NumStability.Algorithms.QR.Higham19Problem19_10"
                ),
                status="qr_owner_required",
            ),
        ]
        qr_handoff_path = root / "qr-handoff.tsv"
        qr_handoff_path.write_text(
            "format\t1\n"
            f"qr_commit\t{'A' * 40}\n"
            f"qr_ownership_sha256\t{'B' * 64}\n"
            "owner\tedge\tNumStability.Algorithms.QR.QRSolve\t"
            "NumStability.qrExternal\t-\t-\t"
            "NumStability.Algorithms.QR.QRSolve\n"
            "owner\timport\t"
            "NumStability.Algorithms.QR.Higham19Problem19_10\t-\t"
            "NumStability.Algorithms.QR.Higham19Problem19_10\t"
            f"{LS_PREFIX}.Higham20CrossProductExample\t{qr_source_owner}\n",
            encoding="utf-8",
        )
        self_qr_handoff = read_qr_handoff(
            qr_handoff_path,
            frozen_self_cross,
            sha256_file(qr_handoff_path),
            expected_mappings=2,
        )
        expect_value_error(
            lambda: read_qr_handoff(
                qr_handoff_path,
                frozen_self_cross,
                "0" * 64,
                expected_mappings=2,
            ),
            "a QR handoff whose reviewed hash differs",
        )
        incomplete_qr_handoff_path = root / "qr-handoff-incomplete.tsv"
        incomplete_qr_handoff_path.write_text(
            "format\t1\n"
            f"qr_commit\t{'A' * 40}\n"
            f"qr_ownership_sha256\t{'B' * 64}\n"
            "owner\tedge\tNumStability.Algorithms.QR.QRSolve\t"
            "NumStability.qrExternal\t-\t-\t"
            "NumStability.Algorithms.QR.QRSolve\n",
            encoding="utf-8",
        )
        expect_value_error(
            lambda: read_qr_handoff(
                incomplete_qr_handoff_path,
                frozen_self_cross,
                sha256_file(incomplete_qr_handoff_path),
                expected_mappings=2,
            ),
            "a QR handoff missing the import-only carrier identity",
        )

        # Without a QR handoff, pre/stage accept only unchanged placeholders.
        validate_cross_lane_artifact_contract(
            frozen_self_cross,
            frozen_self_cross,
            expected_rows=2,
            expected_edge_rows=1,
            expected_import_rows=1,
        )
        expect_value_error(
            lambda: validate_cross_lane_artifact_contract(
                frozen_self_cross,
                self_cross,
                expected_rows=2,
                expected_edge_rows=1,
                expected_import_rows=1,
            ),
            "a QR placeholder resolution without an authoritative handoff",
        )
        validate_cross_lane_artifact_contract(
            frozen_self_cross,
            self_cross,
            qr_handoff=self_qr_handoff,
            require_qr_resolved=True,
            expected_rows=2,
            expected_edge_rows=1,
            expected_import_rows=1,
        )
        expect_value_error(
            lambda: validate_cross_lane_artifact_contract(
                frozen_self_cross,
                self_cross[:-1],
                expected_rows=2,
                expected_edge_rows=1,
                expected_import_rows=1,
            ),
            "a truncated cross-lane normalization artifact",
        )

        # Reproduce the subtle old escape: choose a different LS destination
        # that is a valid owner of the same historical module.  The parser can
        # accept that shape, but the regenerated frozen route must reject it.
        multi_owner_records = dict(records)
        multi_owner_records["NumStability.lsResidual.eq_1"] = replace(
            multi_owner_records["NumStability.lsResidual.eq_1"],
            destination_module=SELF_ANALYSIS,
        )
        multi_owner_records["NumStability.syntheticCrossProduct"] = ManifestRow(
            "NumStability.syntheticCrossProduct",
            f"{LS_PREFIX}.Higham20CrossProductExample",
            SELF_ANALYSIS,
            "theorem",
            "public",
        )
        ls_owner_tamper = list(self_cross)
        ls_owner_tamper[0] = replace(
            ls_owner_tamper[0], ls_destination=SELF_ANALYSIS
        )
        ls_owner_tamper_path = root / "cross-lane-ls-owner-tamper.tsv"
        ls_owner_tamper_path.write_bytes(cross_lane_bytes(ls_owner_tamper))
        parsed_ls_owner_tamper = read_cross_lane_normalization(
            ls_owner_tamper_path, multi_owner_records
        )
        expect_value_error(
            lambda: validate_cross_lane_artifact_contract(
                frozen_self_cross,
                parsed_ls_owner_tamper,
                qr_handoff=self_qr_handoff,
                expected_rows=2,
                expected_edge_rows=1,
                expected_import_rows=1,
            ),
            "a false LS-owner substitution in the cross-lane artifact",
        )
        false_qr_owner = list(self_cross)
        false_qr_owner[0] = replace(
            false_qr_owner[0],
            qr_owner="NumStability.Algorithms.QR.FalseOwner",
        )
        expect_value_error(
            lambda: validate_cross_lane_artifact_contract(
                frozen_self_cross,
                false_qr_owner,
                qr_handoff=self_qr_handoff,
                expected_rows=2,
                expected_edge_rows=1,
                expected_import_rows=1,
            ),
            "a false QR declaration owner despite an authoritative handoff",
        )
        false_qr_carrier = list(self_cross)
        false_qr_carrier[1] = replace(
            false_qr_carrier[1],
            qr_owner="NumStability.Source.Higham.Chapter19.FalseCarrier",
        )
        expect_value_error(
            lambda: validate_cross_lane_artifact_contract(
                frozen_self_cross,
                false_qr_carrier,
                qr_handoff=self_qr_handoff,
                expected_rows=2,
                expected_edge_rows=1,
                expected_import_rows=1,
            ),
            "a false import-only QR carrier despite an authoritative handoff",
        )

        # Already-canonical base owners remain immutable independently of the
        # handoff mechanism.
        stable_qr_tamper = [
            replace(
                self_cross[0],
                qr_owner="NumStability.Algorithms.QR.FalseOwner",
            )
        ]
        expect_value_error(
            lambda: validate_cross_lane_artifact_contract(
                [self_cross[0]],
                stable_qr_tamper,
                expected_rows=1,
                expected_edge_rows=1,
                expected_import_rows=0,
            ),
            "a substitution for an already-canonical QR owner",
        )
        assert validate_cross_lane_final_contract(
            self_cross, moved, graph, records, self_qr_handoff
        ) == (2, 5)

        dropped = dict(graph)
        dropped[SELF_REUSABLE] = ["NumStability.Algorithms.QR.HouseholderQRSupport"]
        expect_value_error(
            lambda: validate_cross_lane_final_contract(
                self_cross, moved, dropped, records, self_qr_handoff
            ),
            "a dropped canonical LS-to-QR dependency",
        )
        unresolved = list(self_cross)
        unresolved[1] = replace(
            unresolved[1],
            qr_owner=(
                "@QR_OWNER_REQUIRED:"
                "NumStability.Algorithms.QR.Higham19Problem19_10"
            ),
            status="qr_owner_required",
        )
        expect_value_error(
            lambda: validate_cross_lane_final_contract(
                unresolved, moved, graph, records, self_qr_handoff
            ),
            "an unresolved QR canonical owner in post mode",
        )
        wrapper_import = dict(graph)
        wrapper_import[SELF_REUSABLE] = [SELF_HISTORICAL_A]
        expect_value_error(
            lambda: validate_cross_lane_final_contract(
                self_cross, moved, wrapper_import, records, self_qr_handoff
            ),
            "a final production import of a compatibility wrapper",
        )
        false_carrier_graph = dict(graph)
        false_carrier_graph[
            "NumStability.Source.Higham.Chapter19.FalseCarrier"
        ] = [SELF_ANALYSIS]
        expect_value_error(
            lambda: validate_cross_lane_final_contract(
                false_qr_carrier,
                moved,
                false_carrier_graph,
                records,
                self_qr_handoff,
            ),
            "a fake import-only carrier with a matching import",
        )

        # 16. Structural modules must be import-only and declaration-free.
        self_structural = {
            SELF_HISTORICAL_A: (
                SELF_REUSABLE,
                "NumStability.Algorithms.QR.QRSolve",
            )
        }
        # 15b. A canonical module left behind by a retarget owns nothing and would
        # duplicate declarations that moved elsewhere.
        validate_no_orphaned_destinations(project, records)
        orphan = project / Path(*REUSABLE_ALGORITHM_ROOT.split(".")) / "Orphaned.lean"
        orphan.parent.mkdir(parents=True, exist_ok=True)
        orphan.write_text(
            "/-! Emptied by a retarget. -/\nimport NumStability.Analysis.MatrixAlgebra\n",
            encoding="utf-8",
        )
        expect_value_error(
            lambda: validate_no_orphaned_destinations(project, records),
            "a canonical module a retarget left owning nothing",
        )
        orphan.unlink()
        validate_no_orphaned_destinations(project, records)

        validate_structural_modules(
            project, moved, {SELF_HISTORICAL_A}, self_structural
        )
        expect_value_error(
            lambda: validate_structural_modules(
                project,
                moved,
                {SELF_HISTORICAL_A},
                {SELF_HISTORICAL_A: (SELF_REUSABLE,)},
            ),
            "a structural wrapper whose exact imports drifted",
        )
        expect_value_error(
            lambda: validate_structural_modules(
                project,
                moved + [Declaration("NumStability.leftover", SELF_HISTORICAL_A, "theorem", "public")],
                {SELF_HISTORICAL_A},
                None,
            ),
            "a wrapper that still owns a compiled declaration",
        )
        # 16b. A wrapper's contracted surface is its destinations *plus* its frozen
        # historical imports.  Forwarding destinations alone narrows the transitive
        # surface the historical module offered and breaks consumers that reached an
        # identifier through it, so the generated contract must contain both.
        frozen_dir = root / "frozen-imports"
        frozen_dir.mkdir()
        for owner_module in HISTORICAL_DECLARATION_WRAPPERS:
            (frozen_dir / f"{owner_module}.lean").write_text(
                "import Mathlib.Data.Real.Basic\n"
                "import NumStability.Analysis.MatrixAlgebra\n"
                "/-! Frozen historical owner. -/\n"
                "theorem placeholder : True := trivial\n",
                encoding="utf-8",
            )
        self_frozen_owners = {
            owner_module: FrozenOwner(
                owner_module, f"{owner_module}.lean", "0" * 40, "0" * 64, 4, 4, "-", 0
            )
            for owner_module in HISTORICAL_DECLARATION_WRAPPERS
        }
        historical = frozen_historical_imports(
            project, self_frozen_owners, frozen_dir
        )
        assert historical[SELF_HISTORICAL_A] == (
            "Mathlib.Data.Real.Basic",
            "NumStability.Analysis.MatrixAlgebra",
        ), historical[SELF_HISTORICAL_A]
        widened = generate_structural_import_contract(records, historical)
        assert SELF_REUSABLE in widened[SELF_HISTORICAL_A], widened[SELF_HISTORICAL_A]
        assert (
            "NumStability.Analysis.MatrixAlgebra" in widened[SELF_HISTORICAL_A]
        ), widened[SELF_HISTORICAL_A]
        expect_value_error(
            lambda: generate_structural_import_contract(records, {}),
            "a structural contract generated without frozen historical imports",
        )
        expect_value_error(
            lambda: frozen_historical_imports(
                project, self_frozen_owners, root / "absent-frozen-dir"
            ),
            "a missing frozen historical source",
        )

        unsorted_wrapper = project / "NumStability/Algorithms/LeastSquares/Unsorted.lean"
        unsorted_wrapper.write_text(
            "/-! Unsorted wrapper. -/\n"
            "import NumStability.Algorithms.QR.QRSolve\n"
            "import NumStability.Algorithms.LinearSystems.LeastSquares.Residual\n",
            encoding="utf-8",
        )
        expect_value_error(
            lambda: validate_import_only_module(project, f"{LS_PREFIX}.Unsorted"),
            "an unsorted wrapper import list",
        )
        code_wrapper = project / "NumStability/Algorithms/LeastSquares/WithCode.lean"
        code_wrapper.write_text(
            "/-! Wrapper with code. -/\n"
            "import NumStability.Algorithms.QR.QRSolve\n"
            "theorem leftover : True := trivial\n",
            encoding="utf-8",
        )
        expect_value_error(
            lambda: validate_import_only_module(project, f"{LS_PREFIX}.WithCode"),
            "a wrapper containing non-import code",
        )
        nodoc_wrapper = project / "NumStability/Algorithms/LeastSquares/NoDoc.lean"
        nodoc_wrapper.write_text(
            "import NumStability.Algorithms.QR.QRSolve\n", encoding="utf-8"
        )
        expect_value_error(
            lambda: validate_import_only_module(project, f"{LS_PREFIX}.NoDoc"),
            "a wrapper without a module docstring",
        )

        # 17. Proposed tier coverage.
        tiers_path = root / "tiers.tsv"
        tier_rows = {
            SELF_REUSABLE: "reusable",
            SELF_ANALYSIS: "reusable",
            SELF_SOURCE: "source",
            SELF_HISTORICAL_A: "compatibility",
            SOURCE_ROOT: "source",
            REUSABLE_ALGORITHM_UMBRELLA: "reusable",
            REUSABLE_ANALYSIS_UMBRELLA: "reusable",
            f"{SOURCE_ROOT}.Equation32": "source",
            f"{SOURCE_ROOT}.Lemma06": "source",
            f"{SOURCE_ROOT}.Theorem01": "source",
        }
        tiers_path.write_text(
            "format\t1\n"
            + "".join(f"{m}\t{t}\n" for m, t in sorted(tier_rows.items())),
            encoding="utf-8",
        )
        tiers = read_tiers(tiers_path)
        self_tier_structural = {
            SELF_HISTORICAL_A,
            SOURCE_ROOT,
            REUSABLE_ALGORITHM_UMBRELLA,
            REUSABLE_ANALYSIS_UMBRELLA,
        }
        validate_tier_coverage(tiers, records, self_tier_structural)
        expect_value_error(
            lambda: validate_tier_coverage(tiers, records, {SOURCE_ROOT}),
            "tier rows that omit wrappers or reusable umbrellas",
        )
        mixed_path = root / "mixed.tsv"
        mixed_path.write_text(
            "format\t1\n" + f"{SELF_REUSABLE}\tmixed\n", encoding="utf-8"
        )
        expect_value_error(
            lambda: read_tiers(mixed_path), "a mixed proposed tier"
        )
        contradicting = dict(tier_rows)
        contradicting[SELF_REUSABLE] = "source"
        contra_path = root / "contra.tsv"
        contra_path.write_text(
            "format\t1\n"
            + "".join(f"{m}\t{t}\n" for m, t in sorted(contradicting.items())),
            encoding="utf-8",
        )
        expect_value_error(
            lambda: validate_tier_coverage(
                read_tiers(contra_path), records, self_tier_structural
            ),
            "a proposed tier contradicting its destination role",
        )

        # 18. Coordinator-owned imports, root tests, global tiers and
        # COMPATIBILITY.md rows are executable post gates, not prose requests.
        coordinator_rows = {
            ("add_import", "NumStability.Consumer", "-", SELF_REUSABLE),
            (
                "remove_import",
                "NumStability.Consumer",
                SELF_HISTORICAL_A,
                "-",
            ),
            (
                "new_aggregate",
                "NumStability.Analysis.Perturbation",
                "-",
                SELF_ANALYSIS,
            ),
            (
                "root_test_import",
                "NumStabilityTest",
                "-",
                "NumStabilityTest.Import.Self",
            ),
            (
                "global_tier_exact",
                SELF_HISTORICAL_A,
                "-",
                "compatibility",
            ),
            (
                "global_tier_prefix",
                "NumStability.Self.",
                "-",
                "reusable",
            ),
            (
                "compatibility_map",
                SELF_HISTORICAL_A,
                "-",
                SELF_REUSABLE,
            ),
        }
        coordinator_path = root / "coordinator.tsv"
        write_coordinator_patches(coordinator_path, coordinator_rows)
        assert read_coordinator_patches(coordinator_path) == coordinator_rows
        perturbation_aggregate = module_path(
            project, "NumStability.Analysis.Perturbation"
        )
        perturbation_aggregate.parent.mkdir(parents=True, exist_ok=True)
        perturbation_aggregate.write_text(
            "/-! Perturbation aggregate. -/\n" f"import {SELF_ANALYSIS}\n",
            encoding="utf-8",
        )
        architecture = project / "docs/architecture"
        architecture.mkdir(parents=True, exist_ok=True)
        (architecture / "tiers.json").write_text(
            json.dumps(
                {
                    "exact": {SELF_HISTORICAL_A: "compatibility"},
                    "prefixes": [
                        {"prefix": "NumStability.Self.", "tier": "reusable"}
                    ],
                }
            ),
            encoding="utf-8",
        )
        (architecture / "COMPATIBILITY.md").write_text(
            "| Historical path | Canonical path |\n"
            "| --- | --- |\n"
            f"| `{SELF_HISTORICAL_A}` | `{SELF_REUSABLE}` |\n",
            encoding="utf-8",
        )
        coordinator_graph = {
            "NumStability.Consumer": [SELF_REUSABLE],
            "NumStabilityTest": ["NumStabilityTest.Import.Self"],
        }
        assert validate_coordinator_patches_applied(
            project, coordinator_rows, coordinator_graph, {}
        ) == (3, 2, 1)
        stale_coordinator_graph = dict(coordinator_graph)
        stale_coordinator_graph["NumStability.Consumer"] = [SELF_HISTORICAL_A]
        expect_value_error(
            lambda: validate_coordinator_patches_applied(
                project, coordinator_rows, stale_coordinator_graph, {}
            ),
            "an unapplied coordinator consumer rewrite",
        )

        # 19. Every route is tied to an authoritative .ilean command span and
        # exact source-command fingerprint, including compiler-generated rows.
        frozen_source_dir = root / "frozen-source"
        frozen_ilean_dir = root / "frozen-ilean"
        frozen_source_dir.mkdir()
        frozen_ilean_dir.mkdir()
        source_a_lines = [
            b"def NumStability.lsResidual := 0\n",
            b"theorem NumStability.lsResidual_permuteRows : True := True.intro\n",
            b"private theorem NumStability.lsHelper : True := True.intro\n",
        ]
        source_b_lines = [
            b"theorem NumStability.wedinLemma20_11_bound : True := True.intro\n",
            b"theorem NumStability.theorem20_3_source : True := True.intro\n",
        ]
        source_paths = {
            SELF_HISTORICAL_A: frozen_source_dir / f"{SELF_HISTORICAL_A}.lean",
            SELF_HISTORICAL_B: frozen_source_dir / f"{SELF_HISTORICAL_B}.lean",
        }
        source_paths[SELF_HISTORICAL_A].write_bytes(b"".join(source_a_lines))
        source_paths[SELF_HISTORICAL_B].write_bytes(b"".join(source_b_lines))

        def self_span(line: int, payload: bytes) -> list[int]:
            width = len(payload.rstrip(b"\n"))
            return [line, 0, line, width, line, 0, line, width]

        ilean_payloads = {
            SELF_HISTORICAL_A: {
                "module": SELF_HISTORICAL_A,
                "decls": {
                    "NumStability.lsResidual": self_span(0, source_a_lines[0]),
                    "NumStability.lsResidual_permuteRows": self_span(
                        1, source_a_lines[1]
                    ),
                    f"_private.{SELF_HISTORICAL_A}.0.NumStability.lsHelper": self_span(
                        2, source_a_lines[2]
                    ),
                },
            },
            SELF_HISTORICAL_B: {
                "module": SELF_HISTORICAL_B,
                "decls": {
                    "NumStability.wedinLemma20_11_bound": self_span(
                        0, source_b_lines[0]
                    ),
                    "NumStability.theorem20_3_source": self_span(
                        1, source_b_lines[1]
                    ),
                },
            },
        }
        ilean_paths: dict[str, Path] = {}
        for module, payload in ilean_payloads.items():
            path = frozen_ilean_dir / f"{module}.ilean"
            path.write_text(json.dumps(payload, sort_keys=True), encoding="utf-8")
            ilean_paths[module] = path

        frozen_owners = {
            module: FrozenOwner(
                module,
                f"unused/{module}.lean",
                "0" * 40,
                sha256_file(source_paths[module]),
                len(source_paths[module].read_bytes().splitlines()),
                len(source_paths[module].read_bytes().splitlines()),
                sha256_file(ilean_paths[module]),
                ilean_paths[module].stat().st_size,
            )
            for module in SELF_COUNTS
        }
        generated_routes = generate_command_routes(
            baseline,
            records,
            project,
            frozen_owners,
            frozen_source_dir,
            frozen_ilean_dir,
        )
        assert generated_routes["NumStability.lsResidual.eq_1"].provenance == (
            "compiler_generated"
        )
        routes_path = root / "routes.tsv"
        write_command_routes(routes_path, generated_routes)
        committed_routes = read_command_routes(routes_path, baseline, records)
        assert manifest_from_command_routes(committed_routes, baseline) == records
        assert validate_routes_against_frozen_inputs(
            committed_routes,
            frozen_owners,
            project,
            frozen_source_dir,
            frozen_ilean_dir,
        ) == (6, 5)

        exact_escape = root / "exact-escape.tsv"
        exact_escape.write_text(
            "format\t1\n"
            f"exact\t{SELF_HISTORICAL_A}\tNumStability.lsResidual\t-\t{SELF_REUSABLE}\n",
            encoding="utf-8",
        )
        expect_value_error(
            lambda: read_command_routes(exact_escape, baseline, records),
            "a format-1 exact route that bypasses compiler spans",
        )

        split_group = dict(committed_routes)
        split_group["NumStability.lsResidual.eq_1"] = replace(
            split_group["NumStability.lsResidual.eq_1"],
            destination_module=SELF_SOURCE,
        )
        expect_value_error(
            lambda: validate_command_routes(split_group, baseline, records),
            "co-generated declarations split from their source command",
        )

        span_drift = {
            logical: (
                replace(route, start_col=route.start_col + 1)
                if route.command_root_logical == "NumStability.lsResidual"
                else route
            )
            for logical, route in committed_routes.items()
        }
        expect_value_error(
            lambda: validate_routes_against_frozen_inputs(
                span_drift,
                frozen_owners,
                project,
                frozen_source_dir,
                frozen_ilean_dir,
            ),
            "a route whose compiler coordinates differ from .ilean",
        )

        # The candidate semantic stream is unchanged; only command text moves
        # from ':= 0' to ':= 1'.  Kind and typed-edge checks alone would miss it.
        for module, path in source_paths.items():
            candidate_path = module_path(project, module)
            candidate_path.parent.mkdir(parents=True, exist_ok=True)
            candidate_path.write_bytes(path.read_bytes())
        baseline_map = baseline_actual_to_logical(baseline)
        assert validate_candidate_command_fingerprints(
            project,
            committed_routes,
            records,
            baseline_map,
            set(),
            ilean_paths,
        ) == 5
        candidate_a = module_path(project, SELF_HISTORICAL_A)
        candidate_a.write_bytes(candidate_a.read_bytes().replace(b":= 0", b":= 1"))
        expect_value_error(
            lambda: validate_candidate_command_fingerprints(
                project,
                committed_routes,
                records,
                baseline_map,
                set(),
                ilean_paths,
            ),
            "a same-kind/same-edge semantic command edit",
        )

        digest = validate_expected_manifest_digest(records, None)
        assert HEX_SHA256.fullmatch(digest)
        expect_value_error(
            lambda: validate_expected_manifest_digest(records, "0" * 64),
            "a manifest digest mismatch",
        )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--mode", choices=("pre", "stage", "post"))
    parser.add_argument(
        "--dependency-tsv",
        type=Path,
        help="frozen baseline TSV in pre mode; freshly generated TSV in stage/post mode",
    )
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--routes", type=Path, default=DEFAULT_ROUTES)
    parser.add_argument(
        "--write-manifest",
        action="store_true",
        help="rewrite the manifest from the command routes; valid only in pre mode",
    )
    parser.add_argument(
        "--write-routes",
        action="store_true",
        help="rewrite format-2 command routes from frozen source/.ilean inputs",
    )
    parser.add_argument(
        "--frozen-owners", type=Path, default=DEFAULT_FROZEN_OWNERS
    )
    parser.add_argument(
        "--frozen-source-dir",
        type=Path,
        help="directory containing frozen files named HISTORICAL_MODULE.lean",
    )
    parser.add_argument(
        "--frozen-ilean-dir",
        type=Path,
        help="directory containing frozen files named HISTORICAL_MODULE.ilean",
    )
    parser.add_argument(
        "--ilean",
        action="append",
        default=[],
        metavar="HISTORICAL_MODULE=PATH",
        help="override a historical module's .ilean path (repeatable)",
    )
    parser.add_argument(
        "--baseline-tsv",
        type=Path,
        help="retained frozen lane baseline TSV; required in stage/post mode",
    )
    parser.add_argument(
        "--private-rewrites",
        type=Path,
        default=DEFAULT_PRIVATE_REWRITES,
        help="explicit private-name rewrite map required in stage/post mode",
    )
    parser.add_argument("--tiers", type=Path, default=DEFAULT_TIERS)
    parser.add_argument("--write-tiers", action="store_true")
    parser.add_argument(
        "--structural-imports", type=Path, default=DEFAULT_STRUCTURAL_IMPORTS
    )
    parser.add_argument(
        "--destination-dag", type=Path, default=DEFAULT_DESTINATION_DAG
    )
    parser.add_argument("--cross-lane", type=Path, default=DEFAULT_CROSS_LANE)
    parser.add_argument(
        "--qr-handoff",
        type=Path,
        help=(
            "reviewed QR owner/carrier handoff; required with its SHA-256 "
            "before any placeholder may be resolved"
        ),
    )
    parser.add_argument(
        "--qr-handoff-sha256",
        help="separately reviewed SHA-256 of --qr-handoff",
    )
    parser.add_argument(
        "--coordinator-patches", type=Path, default=DEFAULT_COORDINATOR_PATCHES
    )
    parser.add_argument(
        "--write-structural-imports", action="store_true"
    )
    parser.add_argument("--write-destination-dag", action="store_true")
    parser.add_argument("--write-cross-lane", action="store_true")
    parser.add_argument("--write-coordinator-patches", action="store_true")
    parser.add_argument(
        "--expected-manifest-sha256",
        help="optional canonical LF-normalized manifest digest",
    )
    parser.add_argument(
        "--project-root",
        type=Path,
        default=Path("."),
        help="repository root for .ilean defaults and structural-module checks",
    )
    parser.add_argument(
        "--completed-structural-module",
        action="append",
        default=[],
        help="completed structural module in stage mode (repeatable)",
    )
    parser.add_argument(
        "--completed-structural-modules",
        type=Path,
        help="format-1 one-column completed structural set for stage mode",
    )
    parser.add_argument(
        "--completed-destination",
        action="append",
        default=[],
        help="destination fully moved in stage mode (repeatable)",
    )
    parser.add_argument(
        "--completed-destinations",
        type=Path,
        help="format-1 one-column completed-destination set for stage mode",
    )
    parser.add_argument(
        "--self-test", action="store_true", help="run checker unit smoke tests"
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.self_test:
        run_self_test()
        print("lsq-ch20 ownership checker self-test passed")
        return 0
    if args.mode is None or args.dependency_tsv is None:
        raise ValueError("--mode and --dependency-tsv are required")
    write_flags = (
        args.write_manifest,
        args.write_routes,
        args.write_structural_imports,
        args.write_destination_dag,
        args.write_cross_lane,
        args.write_tiers,
        args.write_coordinator_patches,
    )
    if any(write_flags) and args.mode != "pre":
        raise ValueError("contract write options are valid only in pre mode")
    if (args.qr_handoff is None) != (args.qr_handoff_sha256 is None):
        raise ValueError(
            "--qr-handoff and --qr-handoff-sha256 must be supplied together"
        )

    ilean_overrides = parse_ilean_overrides(args.ilean)
    structural_modules = set(DEFAULT_STRUCTURAL_MODULES)

    if args.mode == "pre":
        if sha256_file(args.dependency_tsv) != BASELINE_TSV_SHA256:
            raise ValueError("pre-migration dependency TSV hash differs from the frozen base")
        declarations = read_dependency_declarations(args.dependency_tsv)
        baseline = selected_baseline_declarations(declarations)
        records = read_manifest(args.manifest)
        validate_manifest_against_baseline(records, baseline)
        frozen_owners = read_frozen_owners(args.frozen_owners)
        if args.write_routes:
            generated_routes = generate_command_routes(
                baseline,
                records,
                args.project_root,
                frozen_owners,
                args.frozen_source_dir,
                args.frozen_ilean_dir,
            )
            write_command_routes(args.routes, generated_routes)
        routes = read_command_routes(args.routes, baseline, records)
        route_rows, command_groups = validate_routes_against_frozen_inputs(
            routes,
            frozen_owners,
            args.project_root,
            args.frozen_source_dir,
            args.frozen_ilean_dir,
        )
        generated_manifest = manifest_from_command_routes(routes, baseline)
        if args.write_manifest:
            write_manifest(args.manifest, generated_manifest)
            records = read_manifest(args.manifest)
        if records != generated_manifest:
            raise ValueError(
                "committed manifest differs from the compiler-span routes"
            )
        digest = validate_expected_manifest_digest(records, args.expected_manifest_sha256)
        actual_to_logical = baseline_actual_to_logical(baseline)
        owners, owner_edges = validate_destination_graph(
            args.dependency_tsv, declarations, actual_to_logical, records
        )

        private_checked = validate_private_colocation(
            args.dependency_tsv, declarations, actual_to_logical, records
        )
        print(
            f"private co-location: {private_checked} private declarations, "
            "0 cross-destination uses"
        )

        generated_dag = destination_dag_from_stream(
            args.dependency_tsv, actual_to_logical, records
        )
        if args.write_destination_dag:
            write_destination_dag(args.destination_dag, generated_dag)
        dag = read_destination_dag(args.destination_dag, records)
        validate_destination_dag_contract(
            args.dependency_tsv, actual_to_logical, records, dag
        )

        historical_imports = frozen_historical_imports(
            args.project_root, frozen_owners, args.frozen_source_dir
        )
        generated_structural = generate_structural_import_contract(
            records, historical_imports
        )
        if args.write_structural_imports:
            write_structural_import_contract(
                args.structural_imports, generated_structural
            )
        structural_contract = read_structural_import_contract(
            args.structural_imports
        )
        if structural_contract != generated_structural:
            raise ValueError(
                "committed wrapper/aggregate imports differ from generated contract"
            )

        generated_coordinator = generate_coordinator_patches(
            args.project_root, records, structural_contract
        )
        if args.write_coordinator_patches:
            write_coordinator_patches(
                args.coordinator_patches, generated_coordinator
            )
        coordinator_patches = read_coordinator_patches(args.coordinator_patches)
        if coordinator_patches != generated_coordinator:
            raise ValueError(
                "committed coordinator patches differ from the exact base-derived set"
            )

        generated_cross = generate_cross_lane_normalization(
            args.dependency_tsv, declarations, actual_to_logical, records
        )
        if args.write_cross_lane:
            write_cross_lane_normalization(args.cross_lane, generated_cross)
        cross_contract = read_cross_lane_normalization(args.cross_lane, records)
        qr_handoff = (
            None
            if args.qr_handoff is None
            else read_qr_handoff(
                args.qr_handoff,
                generated_cross,
                args.qr_handoff_sha256,
            )
        )
        validate_cross_lane_artifact_contract(
            generated_cross, cross_contract, qr_handoff=qr_handoff
        )
        forward, reverse, cross_edges = validate_cross_lane_base_contract(
            args.project_root,
            args.dependency_tsv,
            declarations,
            actual_to_logical,
            records,
            cross_contract,
        )
        if args.write_tiers:
            write_tiers(
                args.tiers, generate_tiers(records, structural_modules)
            )
        tiers = read_tiers(args.tiers)
        validate_tier_coverage(tiers, records, structural_modules)
        print(
            f"pre mode passed: {len(records)} declarations, {command_groups} compiler "
            f"command groups, {owners} destinations, {owner_edges} owner edges, "
            f"{forward} LS-to-QR and {reverse} QR-to-LS base imports "
            f"({cross_edges} typed edges), manifest sha256 {digest}"
        )
        return 0

    if args.baseline_tsv is None:
        raise ValueError(f"--baseline-tsv is required in {args.mode} mode")
    if sha256_file(args.baseline_tsv) != BASELINE_TSV_SHA256:
        raise ValueError("retained baseline TSV hash differs from the frozen base")
    baseline_declarations = read_dependency_declarations(args.baseline_tsv)
    baseline = selected_baseline_declarations(baseline_declarations)
    records = read_manifest(args.manifest)
    validate_manifest_against_baseline(records, baseline)
    routes = read_command_routes(args.routes, baseline, records)
    dag = read_destination_dag(args.destination_dag, records)
    structural_contract = read_structural_import_contract(args.structural_imports)
    cross_contract = read_cross_lane_normalization(args.cross_lane, records)
    reviewed_cross_lane_imports = {
        (row.ls_destination, row.qr_owner)
        for row in cross_contract
        if row.direction == "LS_TO_QR" and row.status == "resolved"
    }
    reviewed_cross_lane_imports.update(PRESERVED_LSQ_SOURCE_IMPORTS)
    generated_cross = generate_cross_lane_normalization(
        args.baseline_tsv,
        baseline_declarations,
        baseline_actual_to_logical(baseline),
        records,
    )
    qr_handoff = (
        None
        if args.qr_handoff is None
        else read_qr_handoff(
            args.qr_handoff,
            generated_cross,
            args.qr_handoff_sha256,
        )
    )
    validate_cross_lane_artifact_contract(
        generated_cross,
        cross_contract,
        qr_handoff=qr_handoff,
        require_qr_resolved=args.mode == "post",
    )
    coordinator_patches = read_coordinator_patches(args.coordinator_patches)
    digest = validate_expected_manifest_digest(records, args.expected_manifest_sha256)

    all_destinations = {row.destination_module for row in records.values()}
    if args.mode == "stage":
        completed: set[str] = set(args.completed_destination)
        if args.completed_destinations is not None:
            completed.update(read_completed_destinations(args.completed_destinations))
        unknown = sorted(completed - all_destinations)
        if unknown:
            raise ValueError(f"completed destinations are not lane owners: {unknown}")
    else:
        completed = all_destinations

    if args.mode == "stage":
        completed_structural = set(args.completed_structural_module)
        if args.completed_structural_modules is not None:
            completed_structural.update(
                read_structural_modules(args.completed_structural_modules)
            )
        unknown_structural = sorted(completed_structural - structural_modules)
        if unknown_structural:
            raise ValueError(
                f"completed structural modules are outside the contract: "
                f"{unknown_structural}"
            )
    else:
        completed_structural = structural_modules

    declarations = read_dependency_declarations(args.dependency_tsv)
    required_private = {
        logical
        for logical, row in records.items()
        if row.visibility == "private" and row.destination_module in completed
    }
    rewrites = read_private_rewrites(
        args.private_rewrites, records, baseline, required_private
    )
    if args.mode == "post" and len(rewrites) != EXPECTED_PRIVATE_ROWS:
        raise ValueError(
            f"post mode requires all {EXPECTED_PRIVATE_ROWS} reviewed private "
            f"rewrites, found {len(rewrites)}"
        )

    candidate_map = check_candidate_ownership(
        records, baseline, declarations, rewrites, completed
    )
    command_groups = validate_candidate_command_fingerprints(
        args.project_root,
        routes,
        records,
        candidate_map,
        completed,
        ilean_overrides,
    )
    if completed_structural:
        validate_structural_modules(
            args.project_root,
            declarations,
            completed_structural,
            {
                module: structural_contract[module]
                for module in completed_structural
            },
        )
    compare_lane_incident_graph(
        args.baseline_tsv, args.dependency_tsv, baseline, candidate_map, records
    )
    actual_to_logical = {
        declaration.name: candidate_map[declaration.name]
        for declaration in declarations
        if declaration.name in candidate_map
    }
    owners, owner_edges = validate_destination_graph(
        args.dependency_tsv,
        declarations,
        actual_to_logical,
        records,
        allowed_external_source_imports=reviewed_cross_lane_imports,
    )
    validate_private_colocation(
        args.dependency_tsv, declarations, actual_to_logical, records
    )
    validate_destination_dag_contract(
        args.dependency_tsv, actual_to_logical, records, dag
    )
    tiers = read_tiers(args.tiers)
    validate_tier_coverage(tiers, records, structural_modules)
    import_graph = read_module_imports(args.project_root)
    validate_destination_direct_imports(import_graph, records, dag, completed)
    owned_destinations = validate_no_orphaned_destinations(args.project_root, records)
    print(f"canonical modules on disk all owned: {owned_destinations} destinations")

    if args.mode == "post":
        if qr_handoff is None:
            raise ValueError("post mode requires an authoritative QR handoff")
        reusable = validate_reusable_isolation(
            args.project_root,
            records,
            import_graph,
            allowed_direct_imports=reviewed_cross_lane_imports,
        )
        normalized_imports, normalized_modules = validate_cross_lane_final_contract(
            cross_contract, declarations, import_graph, records, qr_handoff
        )
        coordinator_imports, coordinator_tiers, compatibility_rows = (
            validate_coordinator_patches_applied(
                args.project_root, coordinator_patches, import_graph
            )
        )
        print(
            f"post mode passed: {len(records)} declarations, {owners} destinations, "
            f"{command_groups} unchanged compiler command groups, "
            f"{owner_edges} owner edges, {reusable} isolated reusable modules, "
            f"{normalized_imports} canonical cross-lane imports across "
            f"{normalized_modules} production modules, {coordinator_imports} shared "
            f"import patches, {coordinator_tiers} tier registrations, and "
            f"{compatibility_rows} compatibility rows, manifest sha256 {digest}"
        )
    else:
        print(
            f"stage mode passed: {len(completed)}/{len(all_destinations)} destinations "
            f"complete, {len(completed_structural)}/{len(structural_modules)} structural "
            f"modules complete, {command_groups} unchanged compiler command groups, "
            f"{owner_edges} owner edges, manifest sha256 {digest}"
        )
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except ValueError as error:
        print(f"error: {error}", file=sys.stderr)
        sys.exit(1)
