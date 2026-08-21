#!/usr/bin/env python3
"""Deterministically render the exact-C0005 R0011 shared postimages.

This module is deliberately separate from ``generate_c0006_planning_controls.py``.
It owns no authority-bearing state: it does not create an R0011 request record,
invent a primary-human timestamp, write repository files, or modify the live Git
index.  Its public API returns bytes in memory.  The command-line interface is a
read-only checker which reports hashes.

The compatibility table is policy prose, not a mechanical consequence of the
import graph.  A complete render therefore requires externally reviewed exact
``COMPATIBILITY.md`` postimage bytes.  Without those bytes the checker reports a
blocker while still hashing every mechanical postimage and both deterministic
TSV plans.
"""

from __future__ import annotations

import argparse
import csv
import difflib
import hashlib
import io
import json
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[2]
BASE_SHA = "ad92bbfae62d538f3e52829a269a846688a8e213"
BASE_TREE = "21efef4bb0a2b7ce0e5e5c16e86f2d35963cfc3c"
BASE_CHECKPOINT = "C0005"
REQUEST_ID = "R0011"
WAVE_ID = "R07"

EXPECTED_PATH_COUNT = 46
EXPECTED_EXISTING_COUNT = 34
EXPECTED_NEW_COUNT = 12
EXPECTED_PATH_LIST_SHA256 = (
    "C05FA858BF0B5CC3A23F06DEC83F0738780566EA89A172DCA446D4F7129CB901"
)

COMPATIBILITY_PATH = "docs/architecture/COMPATIBILITY.md"
LAYOUT_PATH = "docs/architecture/layout-exceptions.json"
TIERS_PATH = "docs/architecture/tiers.json"
TEST_ROOT_PATH = "NumStabilityTest.lean"
TEST_AGGREGATE_MODULE = "NumStabilityTest.Reorganization.R07.All"

POSTIMAGE_LEDGER_HEADER = (
    "path",
    "preimage_blob_oid",
    "preimage_sha256",
    "postimage_sha256",
)
IMPORT_MANIFEST_HEADER = (
    "path",
    "pre_imports",
    "post_imports",
    "added_imports",
    "removed_imports",
)
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

IMPORT_RE = re.compile(r"import ([A-Za-z0-9_'.]+)")
SHA1_RE = re.compile(r"[0-9a-f]{40}")


class RenderError(RuntimeError):
    """The pinned R0011 postimages cannot be rendered honestly."""


class RenderBlocked(RenderError):
    """A non-mechanical reviewed input is absent."""


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


def git_blob_oid(payload: bytes) -> str:
    header = f"blob {len(payload)}\0".encode("ascii")
    return hashlib.sha1(header + payload).hexdigest()


def canonical_compact_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def canonical_report_json(value: Any) -> bytes:
    return (json.dumps(value, indent=1, sort_keys=True, ensure_ascii=False) + "\n").encode(
        "utf-8"
    )


def tsv_bytes(header: Sequence[str], rows: Iterable[Sequence[Any]]) -> bytes:
    stream = io.StringIO(newline="")
    writer = csv.writer(stream, delimiter="\t", lineterminator="\n")
    writer.writerow(header)
    writer.writerows(rows)
    return stream.getvalue().encode("utf-8")


def module_path(module: str) -> str:
    return module.replace(".", "/") + ".lean"


def module_from_path(path: str) -> str:
    if not path.endswith(".lean"):
        raise RenderError(f"not a Lean module path: {path}")
    return path[:-5].replace("/", ".")


def _git(
    *args: str,
    env: Mapping[str, str] | None = None,
    input_bytes: bytes | None = None,
    check: bool = True,
) -> subprocess.CompletedProcess[bytes]:
    process_env = os.environ.copy()
    if env:
        process_env.update(env)
    result = subprocess.run(
        ["git", *args],
        cwd=ROOT,
        env=process_env,
        input=input_bytes,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if check and result.returncode:
        detail = result.stderr.decode("utf-8", errors="replace").strip()
        raise RenderError(f"git {' '.join(args)} failed: {detail}")
    return result


def base_file(path: str) -> bytes:
    return _git("show", f"{BASE_SHA}:{path}").stdout


def _semicolon(values: Iterable[str]) -> str:
    result = tuple(values)
    return ";".join(result) if result else "-"


@dataclass(frozen=True)
class ImportTransform:
    remove: tuple[str, ...] = ()
    add: tuple[str, ...] = ()
    witnesses: Mapping[str, tuple[int, int]] | None = None


@dataclass(frozen=True)
class RenderedArtifacts:
    """Complete deterministic R0011 bytes, held only in memory."""

    postimages: Mapping[str, bytes]
    patch: bytes
    postimage_ledger: bytes
    import_manifest: bytes
    request_plan: bytes
    forward_tree: str

    def hash_report(self) -> dict[str, Any]:
        return {
            "base_checkpoint_id": BASE_CHECKPOINT,
            "base_sha": BASE_SHA,
            "forward_tree": self.forward_tree,
            "import_manifest_sha256": sha256_bytes(self.import_manifest),
            "patch_sha256": sha256_bytes(self.patch),
            "path_count": len(self.postimages),
            "path_list_sha256": path_list_sha256(self.postimages),
            "postimage_ledger_sha256": sha256_bytes(self.postimage_ledger),
            "postimages": {
                path: sha256_bytes(payload)
                for path, payload in sorted(self.postimages.items())
            },
            "request_plan_sha256": sha256_bytes(self.request_plan),
            "status": "ready",
        }


HISTORICAL_OWNERS = frozenset(
    {
        "NumStability.Algorithms.MatrixPowers",
        "NumStability.Algorithms.MatrixPowersComplex",
        "NumStability.Algorithms.MatrixPowersJordan",
        "NumStability.Algorithms.MatrixPowersLp",
        "NumStability.Algorithms.MatrixPowersLpJordan",
        "NumStability.Algorithms.MatrixPowersPseudospectral",
        "NumStability.Algorithms.MatrixPowersPseudospectralCriterion",
        "NumStability.Algorithms.MatrixPowersSpectral",
        "NumStability.Analysis.BergerGeneral",
        "NumStability.Analysis.BergerInequality",
        "NumStability.Analysis.BergerResolvent",
        "NumStability.Analysis.CStarMatrices.Basic.RealMatrixBridge",
        "NumStability.Analysis.CStarMatrixBridge",
        "NumStability.Analysis.CStarMatrixExpectation",
        "NumStability.Analysis.CStarMatrixTrace",
        "NumStability.Analysis.DunfordResidue",
        "NumStability.Analysis.HenriciExtremal",
        "NumStability.Analysis.HenriciSharpConstant",
        "NumStability.Analysis.HenriciSharpConstantExact",
        "NumStability.Analysis.JordanNormalForm",
        "NumStability.Analysis.LiebTrace",
        "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.KreissBridge",
        "NumStability.Analysis.MatrixPowersBaiDemmelGu",
        "NumStability.Analysis.MatrixPowersBaiDemmelGuDistance",
        "NumStability.Analysis.MatrixPowersBinomialBound",
        "NumStability.Analysis.MatrixPowersGautschi",
        "NumStability.Analysis.MatrixPowersHenrici",
        "NumStability.Analysis.MatrixPowersHenriciNormal",
        "NumStability.Analysis.MatrixPowersKreiss",
        "NumStability.Analysis.MatrixPowersKreissSpijker",
        "NumStability.Analysis.MatrixPowersLaszlo",
        "NumStability.Analysis.MatrixPowersLp185Primary",
        "NumStability.Analysis.MatrixPowersSchur",
        "NumStability.Analysis.MatrixPowersSpijkerClosure",
        "NumStability.Analysis.MatrixPowersSpijkerPlanar",
        "NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis",
        "NumStability.Analysis.MatrixPowersSpijkerRational",
        "NumStability.Analysis.NilpotentJordanChain",
        "NumStability.Analysis.NumericalRadius",
        "NumStability.Analysis.OperatorLog",
        "NumStability.Analysis.PseudospectralLowerBound",
        "NumStability.Analysis.PseudospectralPowerBound",
        "NumStability.Analysis.PseudospectralResolvent",
        "NumStability.Analysis.ResolventFunctionalCalculus",
        "NumStability.Analysis.SpijkerProjectionIntegral",
    }
)

F = "NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra."
S = "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker."

DESTINATION_TIERS: dict[str, str] = {
    F + "BlockDiagonal": "reusable",
    F + "BlockDiagonalCompression": "reusable",
    F + "ColumnPair": "reusable",
    F + "ColumnPairPinching": "reusable",
    F + "ColumnPairRangeProjection": "reusable",
    F + "ColumnPairRangeReflection": "reusable",
    F + "FiniteDimensional": "reusable",
    F + "FiniteMatrixOrder": "reusable",
    F + "FiniteRealEmbedding": "reusable",
    F + "FiniteRealOrder": "reusable",
    F + "ProjectionReflection": "reusable",
    F + "RectangularCompression": "reusable",
    F + "RectangularMultiplication": "reusable",
    F + "ReflectionAverage": "reusable",
    F + "StrictPositivity": "reusable",
    "NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.NormalMatrices.Powers": "reusable",
    "NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.NormalCharacterization.Schur": "reusable",
    "NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.SchurBinomialBounds.Estimates": "reusable",
    S + "ArcLengthPowerBounds.FiniteDimension": "reusable",
    S + "FiniteDimensionalPowerBounds.Kreiss": "reusable",
    S + "PlanarArcLength.Variation": "reusable",
    S + "PlanarCrossingBounds.Polynomial": "reusable",
    S + "ResolventCoefficients.Analytic": "reusable",
    "NumStability.Analysis.LinearOperators.NumericalRadius.Berger.GeneralPowerInequality.Powers": "reusable",
    "NumStability.Analysis.LinearOperators.NumericalRadius.Berger.Internal.HermitianEuclideanSpaceNotation": "internal",
    "NumStability.Analysis.LinearOperators.NumericalRadius.Berger.GeneralPowerInequality.PowersOfTwo": "reusable",
    "NumStability.Analysis.LinearOperators.NumericalRadius.Core.Internal.EuclideanSpaceNotation": "internal",
    "NumStability.Analysis.LinearOperators.Pseudospectra.Resolvent.Internal.ScalarNotation": "internal",
    "NumStability.Analysis.LinearOperators.Schur.Complex.NormalTriangular.Diagonal": "reusable",
    "NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.SpijkerKreissUnconditional.Bounds": "source",
}

INTERNAL_DESTINATIONS = frozenset(
    module for module, tier in DESTINATION_TIERS.items() if tier == "internal"
)
PUBLIC_DESTINATIONS = frozenset(DESTINATION_TIERS) - INTERNAL_DESTINATIONS

PUBLIC_UMBRELLAS: dict[str, tuple[str, ...]] = {
    "NumStability/Analysis/CStarMatrices/FiniteMatrixAlgebra.lean": tuple(
        sorted(module for module in PUBLIC_DESTINATIONS if module.startswith(F))
    ),
    "NumStability/Analysis/LinearOperators/MatrixPowers/ExactNormBounds/NormalMatrices.lean": (
        "NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.NormalMatrices.Powers",
    ),
    "NumStability/Analysis/LinearOperators/MatrixPowers/Henrici/NormalCharacterization.lean": (
        "NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.NormalCharacterization.Schur",
    ),
    "NumStability/Analysis/LinearOperators/MatrixPowers/Henrici/SchurBinomialBounds.lean": (
        "NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.SchurBinomialBounds.Estimates",
    ),
    "NumStability/Analysis/LinearOperators/MatrixPowers/Spijker/ArcLengthPowerBounds.lean": (
        S + "ArcLengthPowerBounds.FiniteDimension",
    ),
    "NumStability/Analysis/LinearOperators/MatrixPowers/Spijker/FiniteDimensionalPowerBounds.lean": (
        S + "FiniteDimensionalPowerBounds.Kreiss",
    ),
    "NumStability/Analysis/LinearOperators/MatrixPowers/Spijker/PlanarArcLength.lean": (
        S + "PlanarArcLength.Variation",
    ),
    "NumStability/Analysis/LinearOperators/MatrixPowers/Spijker/PlanarCrossingBounds.lean": (
        S + "PlanarCrossingBounds.Polynomial",
    ),
    "NumStability/Analysis/LinearOperators/MatrixPowers/Spijker/ResolventCoefficients.lean": (
        S + "ResolventCoefficients.Analytic",
    ),
    "NumStability/Analysis/LinearOperators/NumericalRadius/Berger/GeneralPowerInequality.lean": (
        "NumStability.Analysis.LinearOperators.NumericalRadius.Berger.GeneralPowerInequality.Powers",
        "NumStability.Analysis.LinearOperators.NumericalRadius.Berger.GeneralPowerInequality.PowersOfTwo",
    ),
    "NumStability/Analysis/LinearOperators/Schur/Complex/NormalTriangular.lean": (
        "NumStability.Analysis.LinearOperators.Schur.Complex.NormalTriangular.Diagonal",
    ),
    "NumStability/Source/Higham/Chapter18/Section01/MatrixPowerBounds/NamedBounds/SpijkerKreissUnconditional.lean": (
        "NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.SpijkerKreissUnconditional.Bounds",
    ),
}

UMBRELLA_TIERS = {
    module_from_path(path): "aggregate" for path in PUBLIC_UMBRELLAS
}

ALGORITHMS_REMOVALS = tuple(
    sorted(
        {
            "NumStability.Algorithms.MatrixPowers",
            "NumStability.Algorithms.MatrixPowersComplex",
            "NumStability.Algorithms.MatrixPowersJordan",
            "NumStability.Algorithms.MatrixPowersLp",
            "NumStability.Algorithms.MatrixPowersLpJordan",
            "NumStability.Algorithms.MatrixPowersPseudospectral",
            "NumStability.Algorithms.MatrixPowersPseudospectralCriterion",
            "NumStability.Algorithms.MatrixPowersSpectral",
            "NumStability.Analysis.BergerGeneral",
            "NumStability.Analysis.BergerInequality",
            "NumStability.Analysis.BergerResolvent",
            "NumStability.Analysis.DunfordResidue",
            "NumStability.Analysis.HenriciExtremal",
            "NumStability.Analysis.HenriciSharpConstant",
            "NumStability.Analysis.HenriciSharpConstantExact",
            "NumStability.Analysis.JordanNormalForm",
            "NumStability.Analysis.MatrixPowersBaiDemmelGu",
            "NumStability.Analysis.MatrixPowersBaiDemmelGuDistance",
            "NumStability.Analysis.MatrixPowersBinomialBound",
            "NumStability.Analysis.MatrixPowersGautschi",
            "NumStability.Analysis.MatrixPowersHenrici",
            "NumStability.Analysis.MatrixPowersHenriciNormal",
            "NumStability.Analysis.MatrixPowersKreiss",
            "NumStability.Analysis.MatrixPowersKreissSpijker",
            "NumStability.Analysis.MatrixPowersLaszlo",
            "NumStability.Analysis.MatrixPowersLp185Primary",
            "NumStability.Analysis.MatrixPowersSchur",
            "NumStability.Analysis.MatrixPowersSpijkerClosure",
            "NumStability.Analysis.MatrixPowersSpijkerPlanar",
            "NumStability.Analysis.MatrixPowersSpijkerRational",
            "NumStability.Analysis.NilpotentJordanChain",
            "NumStability.Analysis.NumericalRadius",
            "NumStability.Analysis.PseudospectralLowerBound",
            "NumStability.Analysis.PseudospectralPowerBound",
            "NumStability.Analysis.PseudospectralResolvent",
            "NumStability.Analysis.ResolventFunctionalCalculus",
        }
    )
)

SPIJKER_KREISS_UNCONDITIONAL_AGGREGATE = (
    "NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds."
    "SpijkerKreissUnconditional"
)

ALGORITHMS_ADDITIONS = tuple(
    sorted(module_from_path(path) for path in PUBLIC_UMBRELLAS)
)

ANALYSIS_REMOVALS = tuple(
    sorted(
        {
            "NumStability.Analysis.BergerGeneral",
            "NumStability.Analysis.BergerInequality",
            "NumStability.Analysis.CStarMatrixBridge",
            "NumStability.Analysis.CStarMatrixExpectation",
            "NumStability.Analysis.CStarMatrixTrace",
            "NumStability.Analysis.HenriciSharpConstantExact",
            "NumStability.Analysis.LiebTrace",
            "NumStability.Analysis.MatrixPowersBinomialBound",
            "NumStability.Analysis.MatrixPowersGautschi",
            "NumStability.Analysis.MatrixPowersLaszlo",
            "NumStability.Analysis.MatrixPowersLp185Primary",
            "NumStability.Analysis.MatrixPowersSpijkerClosure",
            "NumStability.Analysis.NilpotentJordanChain",
            "NumStability.Analysis.OperatorLog",
            "NumStability.Analysis.PseudospectralLowerBound",
        }
    )
)

ANALYSIS_ADDITIONS = (SPIJKER_KREISS_UNCONDITIONAL_AGGREGATE,)

REAL_BRIDGE = "NumStability.Analysis.CStarMatrices.Basic.RealMatrixBridge"
KREISS_BRIDGE = (
    "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.KreissBridge"
)
JORDAN_OLD = "NumStability.Analysis.JordanNormalForm"
JORDAN_NEW = "NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition"
LIEB_OLD = "NumStability.Analysis.LiebTrace"
LIEB_NEW = "NumStability.Analysis.MatrixInequalities.LiebTrace.Concavity"


def _transform(
    remove: Iterable[str] = (),
    add: Iterable[str] = (),
    witnesses: Mapping[str, tuple[int, int]] | None = None,
) -> ImportTransform:
    removed = tuple(sorted(set(remove)))
    added = tuple(sorted(set(add)))
    if set(removed) & set(added):
        raise RuntimeError("import transform adds and removes the same module")
    return ImportTransform(removed, added, witnesses)


OUTSIDE_CONSUMER_TRANSFORMS: dict[str, ImportTransform] = {
    "NumStability/Algorithms.lean": _transform(
        ALGORITHMS_REMOVALS, ALGORITHMS_ADDITIONS
    ),
    "NumStability/Analysis.lean": _transform(
        ANALYSIS_REMOVALS, ANALYSIS_ADDITIONS
    ),
    "NumStability/Analysis/CStarMatrices/Basic/All.lean": _transform(
        [REAL_BRIDGE], ["NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra"]
    ),
    "NumStability/Analysis/LinearOperators/MatrixPowers/Spijker/All.lean": _transform(
        [KREISS_BRIDGE],
        [
            S + "ArcLengthPowerBounds",
            S + "FiniteDimensionalPowerBounds",
            S + "PlanarArcLength",
            S + "PlanarCrossingBounds",
            S + "ResolventCoefficients",
        ],
    ),
}

for _path in (
    "NumStability/Algorithms/RandNLA/ElementwiseTraceMGF.lean",
    "NumStability/Algorithms/RandNLA/RowSamplingTraceMGF.lean",
    "NumStability/Algorithms/RandNLA/UniformRowSamplingMGF.lean",
):
    OUTSIDE_CONSUMER_TRANSFORMS[_path] = _transform([LIEB_OLD], [LIEB_NEW])

for _path in (
    "NumStability/Algorithms/TestMatrices/Higham28Companion.lean",
    "NumStability/Analysis/TestMatrices/Companion/Companion.lean",
    "NumStability/Analysis/TestMatrices/Companion/CompanionSpectral.lean",
    "NumStability/Source/Higham/Chapter28/Section06/Companion/Companion.lean",
    "NumStability/Source/Higham/Chapter28/Section06/Companion/CompanionSpectral.lean",
):
    OUTSIDE_CONSUMER_TRANSFORMS[_path] = _transform([JORDAN_OLD], [JORDAN_NEW])


def _real_transform(
    path: str, counts: Mapping[str, tuple[int, int]]
) -> None:
    OUTSIDE_CONSUMER_TRANSFORMS[path] = _transform(
        [REAL_BRIDGE], counts, witnesses=counts
    )


_real_transform(
    "NumStability/Algorithms/RandomizedLinearAlgebra/Concentration/TraceMGF/LeverageScore.lean",
    {F + "FiniteRealEmbedding": (3, 5), F + "FiniteRealOrder": (0, 2)},
)
_real_transform(
    "NumStability/Algorithms/RandomizedLinearAlgebra/Concentration/TraceMGF/UniformRows.lean",
    {F + "FiniteRealEmbedding": (12, 28), F + "FiniteRealOrder": (0, 3)},
)
_real_transform(
    "NumStability/Analysis/CStarMatrices/Expectation/Finite.lean",
    {F + "FiniteRealEmbedding": (1, 1), F + "StrictPositivity": (0, 1)},
)
_real_transform(
    "NumStability/Analysis/CStarMatrices/Trace/Basic.lean",
    {F + "FiniteRealEmbedding": (7, 7)},
)
_real_transform(
    "NumStability/Analysis/FunctionalCalculus/OperatorLog/Monotonicity.lean",
    {
        F + "FiniteRealEmbedding": (1, 1),
        F + "FiniteRealOrder": (0, 1),
        F + "StrictPositivity": (0, 1),
    },
)
_real_transform(
    "NumStability/Analysis/MatrixInequalities/LiebTrace/Concavity.lean",
    {
        F + "BlockDiagonal": (2, 13),
        F + "BlockDiagonalCompression": (0, 2),
        F + "ColumnPair": (7, 16),
        F + "ColumnPairPinching": (0, 3),
        F + "ColumnPairRangeReflection": (5, 15),
        F + "FiniteMatrixOrder": (0, 3),
        F + "RectangularCompression": (0, 6),
        F + "RectangularMultiplication": (0, 34),
        F + "StrictPositivity": (0, 3),
    },
)
_real_transform(
    "NumStability/Source/DrineasMahoney/RandNLA2016/Algorithm01/ElementwiseSampling/TraceMGF.lean",
    {F + "FiniteRealEmbedding": (2, 7)},
)
_real_transform(
    "NumStability/Source/DrineasMahoney/RandNLA2016/Equation02/SpectralApproximation/ElementwiseSpectral.lean",
    {F + "FiniteRealEmbedding": (13, 49), F + "FiniteRealOrder": (0, 9)},
)
_real_transform(
    "NumStability/Source/DrineasMahoney/RandNLA2016/Equation07/SubspaceEmbedding/LeverageTraceMGF.lean",
    {F + "FiniteRealEmbedding": (6, 16)},
)
_real_transform(
    "NumStability/Source/DrineasMahoney/RandNLA2016/Equation07/SubspaceEmbedding/RowNormTraceMGF.lean",
    {F + "FiniteRealEmbedding": (2, 7)},
)

OUTSIDE_CONSUMER_TRANSFORMS[
    "NumStability/Analysis/LinearOperators/MatrixPowers/Spijker/Rational.lean"
] = _transform(
    [KREISS_BRIDGE],
    [S + "ResolventCoefficients.Analytic"],
    {S + "ResolventCoefficients.Analytic": (2, 4)},
)
OUTSIDE_CONSUMER_TRANSFORMS[
    "NumStability/Source/Higham/Chapter18/Section01/MatrixPowerBounds/NamedBounds/SpijkerKreiss.lean"
] = _transform(
    [KREISS_BRIDGE],
    [S + "ArcLengthPowerBounds.FiniteDimension"],
    {S + "ArcLengthPowerBounds.FiniteDimension": (2, 4)},
)

ADDITIONAL_AGGREGATE_TRANSFORMS: dict[str, ImportTransform] = {
    "NumStability/Analysis/CStarMatrices.lean": _transform(
        add=["NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra"]
    ),
    "NumStability/Analysis/LinearOperators/MatrixPowers/ExactNormBounds/All.lean": _transform(
        add=[
            "NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.NormalMatrices"
        ]
    ),
    "NumStability/Analysis/LinearOperators/MatrixPowers/Henrici/All.lean": _transform(
        add=[
            "NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.NormalCharacterization",
            "NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.SchurBinomialBounds",
        ]
    ),
    "NumStability/Analysis/LinearOperators/NumericalRadius/Berger/All.lean": _transform(
        add=[
            "NumStability.Analysis.LinearOperators.NumericalRadius.Berger.GeneralPowerInequality",
        ]
    ),
    "NumStability/Analysis/LinearOperators/Schur/All.lean": _transform(
        add=["NumStability.Analysis.LinearOperators.Schur.Complex.NormalTriangular"]
    ),
    "NumStability/Source/Higham/Chapter18/Section01/MatrixPowerBounds/NamedBounds/All.lean": _transform(
        add=[
            "NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.SpijkerKreissUnconditional"
        ]
    ),
}

LEAN_TRANSFORMS: dict[str, ImportTransform] = {
    **OUTSIDE_CONSUMER_TRANSFORMS,
    **ADDITIONAL_AGGREGATE_TRANSFORMS,
    TEST_ROOT_PATH: _transform(add=[TEST_AGGREGATE_MODULE]),
}

UNCLASSIFIED_REMOVALS = frozenset(HISTORICAL_OWNERS - {
    REAL_BRIDGE,
    KREISS_BRIDGE,
})
NONCANONICAL_REMOVALS = frozenset(
    {
        REAL_BRIDGE,
        "NumStability.Analysis.CStarMatrixBridge",
        KREISS_BRIDGE,
        "NumStability.Analysis.MatrixPowersSpijkerClosure",
    }
)


BASE_EXISTING_OIDS: dict[str, str] = {
    "NumStability/Algorithms.lean": "494a0ccc2ff0803c35bd47f0d1bdf96d472a44f6",
    "NumStability/Algorithms/RandNLA/ElementwiseTraceMGF.lean": "519b68aafc5fcdce5bfcce60da4dfea8c0ea8e14",
    "NumStability/Algorithms/RandNLA/RowSamplingTraceMGF.lean": "2707d89e7ef91b8d70a3e0e2e56fbcc6c5268c65",
    "NumStability/Algorithms/RandNLA/UniformRowSamplingMGF.lean": "836181294ef3e4b3a97616ecf8f3ed578827a4f9",
    "NumStability/Algorithms/RandomizedLinearAlgebra/Concentration/TraceMGF/LeverageScore.lean": "0e6ba7bb92437f5c98308c2ef9bc6044a761d465",
    "NumStability/Algorithms/RandomizedLinearAlgebra/Concentration/TraceMGF/UniformRows.lean": "893de46955ad61937e8aaf1cb952becd06cbc05c",
    "NumStability/Algorithms/TestMatrices/Higham28Companion.lean": "8a06e932b87c9492751ee2a8f40adbb4cf3b96de",
    "NumStability/Analysis.lean": "71f1b685eefd8997dca291c0c2fc34c09d2d6f4a",
    "NumStability/Analysis/CStarMatrices.lean": "69d53cd254b6c27db218f2ecca833ae0c1792c89",
    "NumStability/Analysis/CStarMatrices/Basic/All.lean": "8deda002b272537428573a7f60fa757a7edf106c",
    "NumStability/Analysis/CStarMatrices/Expectation/Finite.lean": "eade02deb850b01efbbe3332368b8b8e48dd946b",
    "NumStability/Analysis/CStarMatrices/Trace/Basic.lean": "0e8bcbb610dfb043edf31aca7a3a78026673baa6",
    "NumStability/Analysis/FunctionalCalculus/OperatorLog/Monotonicity.lean": "c055c449b065346e1d68082df63e322d51c26f8f",
    "NumStability/Analysis/LinearOperators/MatrixPowers/ExactNormBounds/All.lean": "f008973c53d51267940791cd57830efe58437ff9",
    "NumStability/Analysis/LinearOperators/MatrixPowers/Henrici/All.lean": "c35c42e7c6d18ce6ec96c150e8d7d3e6d5a291f9",
    "NumStability/Analysis/LinearOperators/MatrixPowers/Spijker/All.lean": "2028d4dd187c3e8404ff0b9f8e301380f70b2214",
    "NumStability/Analysis/LinearOperators/MatrixPowers/Spijker/Rational.lean": "8347dc8317200b2a42915f931c4a35f0f7aa1115",
    "NumStability/Analysis/LinearOperators/NumericalRadius/Berger/All.lean": "422b3aa99eaa187e9d6accbd5b5510da0c8f0260",
    "NumStability/Analysis/LinearOperators/Schur/All.lean": "1bb55795afd7f3bb79e36658186f8cc7d64190e4",
    "NumStability/Analysis/MatrixInequalities/LiebTrace/Concavity.lean": "a78028f30091188511cf16ffce05eed75eaf2530",
    "NumStability/Analysis/TestMatrices/Companion/Companion.lean": "ad09cec79b97318ef08ca057891f4f6e7e588582",
    "NumStability/Analysis/TestMatrices/Companion/CompanionSpectral.lean": "5d688fd7c398f496c793f36a94b773046b163440",
    "NumStability/Source/DrineasMahoney/RandNLA2016/Algorithm01/ElementwiseSampling/TraceMGF.lean": "799f97dc26122775da29c7a3e4d8259dc34c9161",
    "NumStability/Source/DrineasMahoney/RandNLA2016/Equation02/SpectralApproximation/ElementwiseSpectral.lean": "26c46a8acbd771866c81db7b432462b68e7f6581",
    "NumStability/Source/DrineasMahoney/RandNLA2016/Equation07/SubspaceEmbedding/LeverageTraceMGF.lean": "dc45882aee8eaba78b6177e4e34be6f9bf990bbb",
    "NumStability/Source/DrineasMahoney/RandNLA2016/Equation07/SubspaceEmbedding/RowNormTraceMGF.lean": "40b8cc76d011b67238cb8651ea200544dbe581eb",
    "NumStability/Source/Higham/Chapter18/Section01/MatrixPowerBounds/NamedBounds/All.lean": "43ade32ec976f9143dbac9779e49f0dc7a41ff04",
    "NumStability/Source/Higham/Chapter18/Section01/MatrixPowerBounds/NamedBounds/SpijkerKreiss.lean": "4fcf58c8a14503a8d4c8cbba5dfc7e83ed54dd99",
    "NumStability/Source/Higham/Chapter28/Section06/Companion/Companion.lean": "2cf1f01d1c7674b2b7603609680195e789a87392",
    "NumStability/Source/Higham/Chapter28/Section06/Companion/CompanionSpectral.lean": "eb1341c4e731de5b12d6a03fe2f7067d67b7985b",
    TEST_ROOT_PATH: "21ae3b5076f546bf342379a2f6fc0bff1a479e61",
    COMPATIBILITY_PATH: "1038bbc8a34316852fe0796ef0d947f09931e41d",
    LAYOUT_PATH: "d4d919b4256ec8d8ea96a0e1fa55ebf979dbf256",
    TIERS_PATH: "30b89378516465f0ce97df6db31fb0b192976cfa",
}

ALL_PATHS = frozenset(BASE_EXISTING_OIDS) | frozenset(PUBLIC_UMBRELLAS)


def path_list_sha256(paths: Iterable[str]) -> str:
    payload = ("\n".join(sorted(paths)) + "\n").encode("utf-8")
    return sha256_bytes(payload)


def _assert_lf(path: str, payload: bytes) -> None:
    if b"\r" in payload:
        raise RenderError(f"{path}: CR bytes are forbidden")
    if not payload.endswith(b"\n"):
        raise RenderError(f"{path}: payload must end in LF")
    try:
        payload.decode("utf-8")
    except UnicodeDecodeError as error:
        raise RenderError(f"{path}: payload is not UTF-8: {error}") from error


def validate_static_contract() -> None:
    if len(HISTORICAL_OWNERS) != 45:
        raise RenderError("historical owner set must contain exactly 45 modules")
    tier_counts: dict[str, int] = {}
    for tier in DESTINATION_TIERS.values():
        tier_counts[tier] = tier_counts.get(tier, 0) + 1
    if tier_counts != {"internal": 3, "reusable": 26, "source": 1}:
        raise RenderError(f"destination tier counts drifted: {tier_counts}")
    if len(PUBLIC_UMBRELLAS) != EXPECTED_NEW_COUNT:
        raise RenderError("public umbrella set must contain exactly 12 new files")
    imported_public = {
        module for imports in PUBLIC_UMBRELLAS.values() for module in imports
    }
    if imported_public != PUBLIC_DESTINATIONS:
        raise RenderError(
            "new umbrellas must import every and only the 27 public destinations"
        )
    if imported_public & INTERNAL_DESTINATIONS:
        raise RenderError("a public umbrella imports an internal destination")
    if len(OUTSIDE_CONSUMER_TRANSFORMS) != 24:
        raise RenderError("outside consumer transform map must contain exactly 24 paths")
    if len(ADDITIONAL_AGGREGATE_TRANSFORMS) != 6:
        raise RenderError("additional aggregate transform map must contain exactly 6 paths")
    if len(ALGORITHMS_REMOVALS) != 36 or len(ANALYSIS_REMOVALS) != 15:
        raise RenderError("root aggregate removal cardinality drift")
    if ALGORITHMS_ADDITIONS != tuple(sorted(set(ALGORITHMS_ADDITIONS))):
        raise RenderError("Algorithms canonical-supplier additions must be sorted and unique")
    if ANALYSIS_ADDITIONS != tuple(sorted(set(ANALYSIS_ADDITIONS))):
        raise RenderError("Analysis canonical-supplier additions must be sorted and unique")
    exact_r07_umbrellas = tuple(
        sorted(module_from_path(path) for path in PUBLIC_UMBRELLAS)
    )
    if ALGORITHMS_ADDITIONS != exact_r07_umbrellas:
        raise RenderError("Algorithms must add every and only the 12 public R07 umbrellas")
    if ANALYSIS_ADDITIONS != (SPIJKER_KREISS_UNCONDITIONAL_AGGREGATE,):
        raise RenderError("Analysis must add only the missing exact-source R07 umbrella")
    if len(UNCLASSIFIED_REMOVALS) != 43 or len(NONCANONICAL_REMOVALS) != 4:
        raise RenderError("layout debt removal cardinality drift")
    if len(BASE_EXISTING_OIDS) != EXPECTED_EXISTING_COUNT:
        raise RenderError("base preimage map must contain exactly 34 blobs")
    if len(ALL_PATHS) != EXPECTED_PATH_COUNT:
        raise RenderError("R0011 path set must contain exactly 46 paths")
    if path_list_sha256(ALL_PATHS) != EXPECTED_PATH_LIST_SHA256:
        raise RenderError("R0011 exact path-list SHA-256 drift")
    folded = [path.casefold() for path in ALL_PATHS]
    if len(folded) != len(set(folded)):
        raise RenderError("R0011 paths collide under case folding")
    for oid in BASE_EXISTING_OIDS.values():
        if SHA1_RE.fullmatch(oid) is None:
            raise RenderError(f"invalid pinned blob OID: {oid}")


def validate_base_contract() -> dict[str, bytes]:
    validate_static_contract()
    actual_tree = _git("rev-parse", f"{BASE_SHA}^{{tree}}").stdout.decode().strip()
    if actual_tree != BASE_TREE:
        raise RenderError(f"base tree {actual_tree} != pinned {BASE_TREE}")
    tree_paths = _git("ls-tree", "-r", "--name-only", BASE_SHA).stdout.decode(
        "utf-8"
    ).splitlines()
    tree_casefold = {path.casefold(): path for path in tree_paths}
    preimages: dict[str, bytes] = {}
    for path, expected_oid in sorted(BASE_EXISTING_OIDS.items()):
        row = _git("ls-tree", BASE_SHA, "--", path).stdout.decode("utf-8").strip()
        if not row:
            raise RenderError(f"{BASE_SHA}: missing pinned preimage {path}")
        metadata, returned_path = row.split("\t", 1)
        mode, kind, oid = metadata.split()
        if mode != "100644" or kind != "blob" or returned_path != path:
            raise RenderError(f"{path}: unexpected base tree row {row}")
        if oid != expected_oid:
            raise RenderError(f"{path}: base blob {oid} != pinned {expected_oid}")
        payload = _git("cat-file", "blob", oid).stdout
        if git_blob_oid(payload) != oid:
            raise RenderError(f"{path}: Git object payload/OID mismatch")
        _assert_lf(path, payload)
        preimages[path] = payload
    for path in sorted(PUBLIC_UMBRELLAS):
        collision = tree_casefold.get(path.casefold())
        if collision is not None:
            raise RenderError(f"new shared path is not casefold-vacant: {path}: {collision}")
    return preimages


def extract_imports(path: str, payload: bytes) -> tuple[str, ...]:
    _assert_lf(path, payload)
    imports: list[str] = []
    for line in payload.decode("utf-8").splitlines():
        match = IMPORT_RE.fullmatch(line)
        if match is not None:
            imports.append(match.group(1))
    if len(imports) != len(set(imports)):
        raise RenderError(f"{path}: duplicate imports in payload")
    return tuple(imports)


def transform_import_block(
    path: str, payload: bytes, transform: ImportTransform
) -> bytes:
    _assert_lf(path, payload)
    text = payload.decode("utf-8")
    lines = text.splitlines(keepends=True)
    indices = [index for index, line in enumerate(lines) if IMPORT_RE.fullmatch(line.rstrip("\n"))]
    if not indices:
        raise RenderError(f"{path}: expected an import block")
    first, last = indices[0], indices[-1]
    if indices != list(range(first, last + 1)):
        raise RenderError(f"{path}: imports are not one contiguous block")
    original = [IMPORT_RE.fullmatch(lines[index].rstrip("\n")).group(1) for index in indices]  # type: ignore[union-attr]
    if len(original) != len(set(original)):
        raise RenderError(f"{path}: base import block contains duplicates")
    missing = sorted(set(transform.remove) - set(original))
    already = sorted(set(transform.add) & set(original))
    if missing:
        raise RenderError(f"{path}: missing requested removal(s): {missing}")
    if already:
        raise RenderError(f"{path}: requested addition(s) already present: {already}")
    post = sorted((set(original) - set(transform.remove)) | set(transform.add))
    replacement = [f"import {module}\n" for module in post]
    result = "".join([*lines[:first], *replacement, *lines[last + 1 :]]).encode("utf-8")
    if result == payload:
        raise RenderError(f"{path}: import transform is a no-op")
    _assert_lf(path, result)
    if extract_imports(path, result) != tuple(post):
        raise RenderError(f"{path}: rendered imports differ from exact sorted postimage")
    return result


def render_public_umbrella(path: str, imports: Sequence[str]) -> bytes:
    if tuple(imports) != tuple(sorted(set(imports))):
        raise RenderError(f"{path}: umbrella imports must be sorted and unique")
    if set(imports) & INTERNAL_DESTINATIONS:
        raise RenderError(f"{path}: public umbrella imports an internal leaf")
    module = module_from_path(path)
    text = "".join(f"import {target}\n" for target in imports)
    text += (
        "\n/-!\n"
        f"# {module}\n\n"
        "Declaration-free aggregate for the canonical modules in this semantic family.\n"
        "-/\n"
    )
    return text.encode("utf-8")


def render_tiers(base: bytes) -> bytes:
    try:
        document = json.loads(base)
    except json.JSONDecodeError as error:
        raise RenderError(f"{TIERS_PATH}: invalid base JSON: {error}") from error
    exact = document.get("exact")
    if not isinstance(exact, dict):
        raise RenderError(f"{TIERS_PATH}: exact tier map is absent")
    for owner in sorted(HISTORICAL_OWNERS):
        current = exact.get(owner)
        expected = "reusable" if owner in {REAL_BRIDGE, KREISS_BRIDGE} else None
        if current != expected:
            raise RenderError(
                f"{TIERS_PATH}: {owner} base exact tier {current!r} != {expected!r}"
            )
        exact[owner] = "compatibility"
    for module, tier in sorted({**DESTINATION_TIERS, **UMBRELLA_TIERS}.items()):
        if module in exact:
            raise RenderError(f"{TIERS_PATH}: new module is already classified: {module}")
        exact[module] = tier
    document["exact"] = dict(sorted(exact.items()))
    result = (json.dumps(document, indent=2, ensure_ascii=False) + "\n").encode("utf-8")
    _assert_lf(TIERS_PATH, result)
    if result == base:
        raise RenderError(f"{TIERS_PATH}: tier transform is a no-op")
    return result


def render_layout(base: bytes) -> bytes:
    try:
        document = json.loads(base)
    except json.JSONDecodeError as error:
        raise RenderError(f"{LAYOUT_PATH}: invalid base JSON: {error}") from error
    legacy = document.get("legacy")
    if not isinstance(legacy, dict):
        raise RenderError(f"{LAYOUT_PATH}: legacy debt map is absent")
    operations = {
        "unclassified_modules": UNCLASSIFIED_REMOVALS,
        "noncanonical_modules": NONCANONICAL_REMOVALS,
    }
    for key, removals in operations.items():
        values = legacy.get(key)
        if not isinstance(values, list) or not all(isinstance(item, str) for item in values):
            raise RenderError(f"{LAYOUT_PATH}: malformed {key}")
        missing = sorted(removals - set(values))
        if missing:
            raise RenderError(f"{LAYOUT_PATH}: expected {key} entries absent: {missing}")
        legacy[key] = sorted(set(values) - removals)
    result = (json.dumps(document, indent=2, ensure_ascii=False) + "\n").encode("utf-8")
    _assert_lf(LAYOUT_PATH, result)
    if result == base:
        raise RenderError(f"{LAYOUT_PATH}: layout transform is a no-op")
    return result


def _compatibility_rows(payload: bytes) -> tuple[list[str], dict[str, str]]:
    _assert_lf(COMPATIBILITY_PATH, payload)
    order: list[str] = []
    rows: dict[str, str] = {}
    pattern = re.compile(r"^\| `([^`]+)` \| (.+) \|$")
    for line in payload.decode("utf-8").splitlines():
        match = pattern.fullmatch(line)
        if match is None:
            continue
        historical, target = match.groups()
        if historical in rows:
            raise RenderError(f"{COMPATIBILITY_PATH}: duplicate row {historical}")
        order.append(historical)
        rows[historical] = target
    return order, rows


def validate_compatibility_postimage(base: bytes, postimage: bytes) -> None:
    if postimage == base:
        raise RenderError(f"{COMPATIBILITY_PATH}: reviewed postimage is a no-op")
    base_order, base_rows = _compatibility_rows(base)
    post_order, post_rows = _compatibility_rows(postimage)
    if base_order != sorted(base_order):
        raise RenderError(f"{COMPATIBILITY_PATH}: base table is unexpectedly unsorted")
    if post_order != sorted(post_order):
        raise RenderError(f"{COMPATIBILITY_PATH}: reviewed table rows must be sorted")
    changed_existing = sorted(
        historical
        for historical, target in base_rows.items()
        if post_rows.get(historical) != target
    )
    if changed_existing:
        raise RenderError(
            f"{COMPATIBILITY_PATH}: reviewed postimage rewrites existing rows: "
            + ", ".join(changed_existing[:5])
        )
    added = set(post_rows) - set(base_rows)
    if added != HISTORICAL_OWNERS:
        raise RenderError(
            f"{COMPATIBILITY_PATH}: reviewed additions differ from exact 45 owners; "
            f"missing={sorted(HISTORICAL_OWNERS-added)}, extra={sorted(added-HISTORICAL_OWNERS)}"
        )
    for owner in HISTORICAL_OWNERS:
        target = post_rows[owner]
        if not target.strip() or not re.search(r"`[^`]+`", target):
            raise RenderError(f"{COMPATIBILITY_PATH}: {owner} lacks a concrete target")
        advertised_internal = sorted(
            module for module in INTERNAL_DESTINATIONS if f"`{module}`" in target
        )
        if advertised_internal:
            raise RenderError(
                f"{COMPATIBILITY_PATH}: {owner} advertises internal implementation leaves: "
                + ", ".join(advertised_internal)
            )


def render_mechanical_postimages(
    preimages: Mapping[str, bytes] | None = None,
) -> dict[str, bytes]:
    base = dict(preimages) if preimages is not None else validate_base_contract()
    postimages: dict[str, bytes] = {}
    for path, transform in sorted(LEAN_TRANSFORMS.items()):
        postimages[path] = transform_import_block(path, base[path], transform)
    for path, imports in sorted(PUBLIC_UMBRELLAS.items()):
        postimages[path] = render_public_umbrella(path, imports)
    postimages[TIERS_PATH] = render_tiers(base[TIERS_PATH])
    postimages[LAYOUT_PATH] = render_layout(base[LAYOUT_PATH])
    expected = ALL_PATHS - {COMPATIBILITY_PATH}
    if set(postimages) != expected or len(postimages) != 45:
        raise RenderError("mechanical renderer must produce every and only 45 non-prose paths")
    return dict(sorted(postimages.items()))


def _consumer_test_path(path: str) -> str:
    module = module_from_path(path)
    return (
        "NumStabilityTest/Reorganization/R07/Consumer/"
        + module.replace(".", "_")
        + ".lean"
    )


def _witness_json(transform: ImportTransform) -> str:
    if not transform.witnesses:
        return "-"
    value = {
        module: {"body_edges": counts[1], "signature_edges": counts[0]}
        for module, counts in sorted(transform.witnesses.items())
    }
    return canonical_compact_json(value)


def build_request_plan() -> bytes:
    rows: list[tuple[str, ...]] = []
    for path in sorted(ALL_PATHS):
        oid = BASE_EXISTING_OIDS.get(path, "-")
        transform = LEAN_TRANSFORMS.get(path)
        if path in OUTSIDE_CONSUMER_TRANSFORMS:
            kind = "normalize_outside_consumer"
            tests = _consumer_test_path(path)
            rationale = "replace historical direct imports with the exact reviewed canonical supply"
        elif path in ADDITIONAL_AGGREGATE_TRANSFORMS:
            kind = "update_family_aggregate"
            tests = "NumStabilityTest/Reorganization/R07/All.lean"
            rationale = "wire the new public semantic subfamily through its existing family aggregate"
        elif path in PUBLIC_UMBRELLAS:
            kind = "create_public_family_aggregate"
            tests = "NumStabilityTest/Reorganization/R07/All.lean"
            rationale = "create a documented import-only public umbrella over exact reviewed children"
        elif path == TEST_ROOT_PATH:
            kind = "register_r07_test_aggregate"
            tests = "lake test"
            rationale = "register the worker-owned isolated R07 test aggregate in the shared test root"
        elif path == TIERS_PATH:
            kind = "update_tier_manifest"
            tests = "python tools/architecture/check_layout.py"
            rationale = "classify 45 wrappers, 30 leaves, and 12 public umbrellas from reviewed routes"
        elif path == LAYOUT_PATH:
            kind = "remove_resolved_layout_debt"
            tests = "python tools/architecture/check_layout.py"
            rationale = "remove exactly 43 unclassified and four noncanonical resolved entries"
        elif path == COMPATIBILITY_PATH:
            kind = "document_compatibility_frontier"
            tests = "python tools/architecture/check_compatibility.py"
            rationale = "record the externally reviewed 45-path compatibility frontier"
        else:  # pragma: no cover - guarded by the exact path contract
            raise RenderError(f"unclassified R0011 request-plan path: {path}")
        if transform is not None:
            added = transform.add
            removed = transform.remove
            witnesses = _witness_json(transform)
        elif path in PUBLIC_UMBRELLAS:
            added = PUBLIC_UMBRELLAS[path]
            removed = ()
            witnesses = "-"
        else:
            added = ()
            removed = ()
            witnesses = "-"
        rows.append(
            (
                path,
                oid,
                kind,
                _semicolon(added),
                _semicolon(removed),
                witnesses,
                tests,
                rationale,
            )
        )
    return tsv_bytes(REQUEST_PLAN_HEADER, rows)


def build_import_manifest(
    preimages: Mapping[str, bytes], postimages: Mapping[str, bytes]
) -> bytes:
    rows: list[tuple[str, str, str, str, str]] = []
    lean_paths = sorted(set(LEAN_TRANSFORMS) | set(PUBLIC_UMBRELLAS))
    for path in lean_paths:
        pre = extract_imports(path, preimages[path]) if path in preimages else ()
        post = extract_imports(path, postimages[path])
        added = tuple(sorted(set(post) - set(pre)))
        removed = tuple(sorted(set(pre) - set(post)))
        rows.append(
            (
                path,
                _semicolon(pre),
                _semicolon(post),
                _semicolon(added),
                _semicolon(removed),
            )
        )
    if len(rows) != 43:
        raise RenderError("import manifest must contain exactly 43 Lean postimages")
    return tsv_bytes(IMPORT_MANIFEST_HEADER, rows)


def build_postimage_ledger(
    preimages: Mapping[str, bytes], postimages: Mapping[str, bytes]
) -> bytes:
    rows: list[tuple[str, str, str, str]] = []
    for path in sorted(postimages):
        if path in preimages:
            oid = BASE_EXISTING_OIDS[path]
            pre_sha = sha256_bytes(preimages[path])
        else:
            oid = "-"
            pre_sha = "-"
        rows.append((path, oid, pre_sha, sha256_bytes(postimages[path])))
    return tsv_bytes(POSTIMAGE_LEDGER_HEADER, rows)


def zero_context_patch(
    preimages: Mapping[str, bytes], postimages: Mapping[str, bytes]
) -> bytes:
    if set(postimages) != ALL_PATHS:
        raise RenderError("patch postimage set differs from exact 46 paths")
    chunks: list[bytes] = []
    for path in sorted(postimages):
        after = postimages[path]
        before = preimages.get(path)
        if before == after:
            raise RenderError(f"{path}: R0011 patch contains a no-op")
        new_oid = git_blob_oid(after)
        chunks.append(f"diff --git a/{path} b/{path}\n".encode("utf-8"))
        if before is None:
            chunks.append(b"new file mode 100644\n")
            chunks.append(
                f"index {'0' * 40}..{new_oid}\n".encode("ascii")
            )
            fromfile = "/dev/null"
            before_lines: list[str] = []
        else:
            old_oid = git_blob_oid(before)
            chunks.append(f"index {old_oid}..{new_oid} 100644\n".encode("ascii"))
            fromfile = f"a/{path}"
            before_lines = before.decode("utf-8").splitlines(keepends=True)
        diff = difflib.unified_diff(
            before_lines,
            after.decode("utf-8").splitlines(keepends=True),
            fromfile=fromfile,
            tofile=f"b/{path}",
            n=0,
            lineterm="\n",
        )
        chunks.append("".join(diff).encode("utf-8"))
    patch = b"".join(chunks)
    if b"\r" in patch or not patch.endswith(b"\n"):
        raise RenderError("rendered patch is not canonical LF text")
    for path in PUBLIC_UMBRELLAS:
        marker = (
            f"diff --git a/{path} b/{path}\n"
            f"new file mode 100644\n"
            f"index {'0' * 40}.."
        ).encode("utf-8")
        if marker not in patch or f"--- /dev/null\n+++ b/{path}\n".encode() not in patch:
            raise RenderError(f"{path}: new-file patch headers are not exact")
    return patch


def verify_temp_index_replay(
    patch: bytes,
    preimages: Mapping[str, bytes],
    postimages: Mapping[str, bytes],
) -> str:
    with tempfile.TemporaryDirectory(prefix="r0011-index-") as directory:
        index = str(Path(directory) / "index")
        env = {"GIT_INDEX_FILE": index}
        _git("read-tree", BASE_SHA, env=env)
        initial = _git("write-tree", env=env).stdout.decode().strip()
        if initial != BASE_TREE:
            raise RenderError(f"temporary index initial tree {initial} != {BASE_TREE}")
        _git(
            "apply",
            "--cached",
            "--unidiff-zero",
            "--whitespace=nowarn",
            "-",
            env=env,
            input_bytes=patch,
        )
        _git("diff", "--cached", "--check", BASE_SHA, env=env)
        for path, expected in sorted(postimages.items()):
            actual = _git("show", f":{path}", env=env).stdout
            if actual != expected:
                raise RenderError(f"{path}: forward temp-index replay mismatch")
        forward_tree = _git("write-tree", env=env).stdout.decode().strip()
        if forward_tree == BASE_TREE:
            raise RenderError("forward R0011 patch unexpectedly leaves the base tree unchanged")
        _git(
            "apply",
            "--cached",
            "--reverse",
            "--unidiff-zero",
            "--whitespace=nowarn",
            "-",
            env=env,
            input_bytes=patch,
        )
        reversed_tree = _git("write-tree", env=env).stdout.decode().strip()
        if reversed_tree != BASE_TREE:
            raise RenderError(
                f"reverse temp-index replay tree {reversed_tree} != base {BASE_TREE}"
            )
        for path, expected in sorted(preimages.items()):
            actual = _git("show", f":{path}", env=env).stdout
            if actual != expected:
                raise RenderError(f"{path}: reverse temp-index replay mismatch")
        for path in sorted(PUBLIC_UMBRELLAS):
            result = _git("show", f":{path}", env=env, check=False)
            if result.returncode == 0:
                raise RenderError(f"{path}: new path survives reverse replay")
        return forward_tree


def validate_public_boundary(postimages: Mapping[str, bytes]) -> None:
    aggregate_paths = (
        set(PUBLIC_UMBRELLAS)
        | set(ADDITIONAL_AGGREGATE_TRANSFORMS)
        | {
            "NumStability/Algorithms.lean",
            "NumStability/Analysis.lean",
            "NumStability/Analysis/CStarMatrices/Basic/All.lean",
            "NumStability/Analysis/LinearOperators/MatrixPowers/Spijker/All.lean",
        }
    )
    for path in sorted(aggregate_paths):
        imports = set(extract_imports(path, postimages[path]))
        forbidden = sorted(imports & INTERNAL_DESTINATIONS)
        if forbidden:
            raise RenderError(f"{path}: public aggregate imports internal leaves: {forbidden}")
        historical = sorted(imports & HISTORICAL_OWNERS)
        if historical:
            raise RenderError(f"{path}: public aggregate imports historical owners: {historical}")
    algorithms_imports = extract_imports(
        "NumStability/Algorithms.lean", postimages["NumStability/Algorithms.lean"]
    )
    missing_algorithms_umbrellas = sorted(
        set(ALGORITHMS_ADDITIONS) - set(algorithms_imports)
    )
    if missing_algorithms_umbrellas:
        raise RenderError(
            "Algorithms lacks exact R07 public umbrella imports: "
            f"{missing_algorithms_umbrellas}"
        )
    analysis_imports = set(
        extract_imports("NumStability/Analysis.lean", postimages["NumStability/Analysis.lean"])
    )
    if set(ANALYSIS_ADDITIONS) - analysis_imports:
        raise RenderError("Analysis lacks the exact-source R07 public umbrella")
    source_count = sum(
        module.startswith("NumStability.Source.") for module in algorithms_imports
    )
    if source_count != 73:
        raise RenderError(
            f"Algorithms Source direct-import count {source_count} != pinned ceiling witness 73"
        )


def render_artifacts(
    compatibility_postimage: bytes | None,
    *,
    verify_replay: bool = True,
) -> RenderedArtifacts:
    """Return all exact R0011 bytes in memory.

    ``compatibility_postimage`` must be an externally reviewed complete file;
    this helper intentionally has no prose generator.
    """

    preimages = validate_base_contract()
    postimages = render_mechanical_postimages(preimages)
    if compatibility_postimage is None:
        raise RenderBlocked(
            "exact externally reviewed COMPATIBILITY.md postimage bytes are required; "
            "the renderer will not invent compatibility prose"
        )
    validate_compatibility_postimage(
        preimages[COMPATIBILITY_PATH], compatibility_postimage
    )
    postimages[COMPATIBILITY_PATH] = compatibility_postimage
    postimages = dict(sorted(postimages.items()))
    if set(postimages) != ALL_PATHS:
        raise RenderError("complete postimage set differs from exact R0011 paths")
    validate_public_boundary(postimages)
    request_plan = build_request_plan()
    import_manifest = build_import_manifest(preimages, postimages)
    ledger = build_postimage_ledger(preimages, postimages)
    patch = zero_context_patch(preimages, postimages)
    forward_tree = (
        verify_temp_index_replay(patch, preimages, postimages)
        if verify_replay
        else "<not-replayed>"
    )
    return RenderedArtifacts(
        postimages=postimages,
        patch=patch,
        postimage_ledger=ledger,
        import_manifest=import_manifest,
        request_plan=request_plan,
        forward_tree=forward_tree,
    )


def _synthetic_reviewed_compatibility(base: bytes) -> bytes:
    """Create in-memory fixture rows only for self-testing renderer mechanics."""

    text = base.decode("utf-8")
    lines = text.splitlines(keepends=True)
    pattern = re.compile(r"^\| `([^`]+)` \| (.+) \|\n$")
    row_indices = [index for index, line in enumerate(lines) if pattern.fullmatch(line)]
    if not row_indices:
        raise RenderError("self-test could not locate compatibility table rows")
    first, last = row_indices[0], row_indices[-1]
    if row_indices != list(range(first, last + 1)):
        raise RenderError("self-test compatibility rows are not contiguous")
    rows = {pattern.fullmatch(lines[index]).group(1): lines[index] for index in row_indices}  # type: ignore[union-attr]
    for owner in HISTORICAL_OWNERS:
        rows[owner] = f"| `{owner}` | `NumStability.Core` |\n"
    return "".join(
        [*lines[:first], *(rows[key] for key in sorted(rows)), *lines[last + 1 :]]
    ).encode("utf-8")


def self_test() -> None:
    validate_static_contract()
    preimages = validate_base_contract()
    mechanical = render_mechanical_postimages(preimages)
    if len(mechanical) != 45:
        raise RenderError("self-test mechanical postimage count drift")
    plan = build_request_plan()
    if not plan.startswith(("\t".join(REQUEST_PLAN_HEADER) + "\n").encode()):
        raise RenderError("self-test request-plan header drift")
    manifest = build_import_manifest(preimages, mechanical)
    if not manifest.startswith(("\t".join(IMPORT_MANIFEST_HEADER) + "\n").encode()):
        raise RenderError("self-test import-manifest header drift")
    synthetic = _synthetic_reviewed_compatibility(preimages[COMPATIBILITY_PATH])
    rendered = render_artifacts(synthetic, verify_replay=True)
    if len(rendered.postimages) != EXPECTED_PATH_COUNT:
        raise RenderError("self-test complete postimage count drift")
    if b"new file mode 100644\n" not in rendered.patch or b"--- /dev/null\n" not in rendered.patch:
        raise RenderError("self-test did not exercise correct new-file patch headers")
    try:
        render_artifacts(None, verify_replay=False)
    except RenderBlocked:
        pass
    else:
        raise RenderError("self-test missing compatibility input did not block")
    bad = synthetic.replace(
        b"`NumStability.Core` |\n",
        (
            "`NumStability.Analysis.LinearOperators.NumericalRadius.Core.Internal."
            "EuclideanSpaceNotation` |\n"
        ).encode(),
        1,
    )
    try:
        validate_compatibility_postimage(preimages[COMPATIBILITY_PATH], bad)
    except RenderError:
        pass
    else:
        raise RenderError("self-test accepted an advertised internal leaf")


def partial_check_report() -> dict[str, Any]:
    preimages = validate_base_contract()
    mechanical = render_mechanical_postimages(preimages)
    import_manifest = build_import_manifest(preimages, mechanical)
    request_plan = build_request_plan()
    return {
        "base_checkpoint_id": BASE_CHECKPOINT,
        "base_sha": BASE_SHA,
        "blockers": [
            "exact externally reviewed COMPATIBILITY.md postimage bytes are required; "
            "no compatibility prose was guessed"
        ],
        "existing_path_count": len(BASE_EXISTING_OIDS),
        "import_manifest_sha256": sha256_bytes(import_manifest),
        "mechanical_postimage_count": len(mechanical),
        "mechanical_postimages": {
            path: sha256_bytes(payload) for path, payload in mechanical.items()
        },
        "new_path_count": len(PUBLIC_UMBRELLAS),
        "path_count": len(ALL_PATHS),
        "path_list_sha256": path_list_sha256(ALL_PATHS),
        "request_plan_sha256": sha256_bytes(request_plan),
        "status": "blocked",
    }


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="read-only check (the default action)",
    )
    parser.add_argument(
        "--compatibility-postimage",
        type=Path,
        help="externally reviewed exact COMPATIBILITY.md postimage; read only",
    )
    parser.add_argument("--self-test", action="store_true")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        if args.self_test:
            self_test()
            print("R0011 shared-postimage renderer self-test passed")
            return 0
        if args.compatibility_postimage is None:
            print(canonical_report_json(partial_check_report()).decode("utf-8"), end="")
            return 2
        compatibility = args.compatibility_postimage.resolve().read_bytes()
        rendered = render_artifacts(compatibility, verify_replay=True)
        print(canonical_report_json(rendered.hash_report()).decode("utf-8"), end="")
        return 0
    except (OSError, RenderError, UnicodeError, json.JSONDecodeError) as error:
        report = {"error": str(error), "status": "failed"}
        print(canonical_report_json(report).decode("utf-8"), end="", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
