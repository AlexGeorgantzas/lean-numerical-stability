#!/usr/bin/env python3
"""Generate and check the frozen Higham Chapter 6 Phase 11B2 ownership map."""

from __future__ import annotations

import argparse
import csv
import hashlib
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path


OLD_LEMMA06 = "NumStability.Algorithms.Chapter06Lemma66"
OLD_ASIDES = "NumStability.Analysis.Higham6Asides"
OLD_BLOCK = "NumStability.Analysis.Higham6BlockAntidiag"
OLD_DUALITY = "NumStability.Analysis.HighamChapter6Duality"

LEMMA06 = "NumStability.Source.Higham.Chapter06.Lemma06"
EQUATION01 = "NumStability.Source.Higham.Chapter06.Equation01"
EQUATION02 = "NumStability.Source.Higham.Chapter06.Equation02"
EUCLIDEAN = (
    "NumStability.Source.Higham.Chapter06.Asides."
    "EuclideanNormDifferentiability"
)
UNITARY = "NumStability.Source.Higham.Chapter06.Asides.UnitaryInvariance"
CONDITION = "NumStability.Source.Higham.Chapter06.Asides.ConditionNumberBounds"
MAX_NORM = "NumStability.Source.Higham.Chapter06.Asides.MaxNormInconsistency"
OPERATOR_TWO = (
    "NumStability.Source.Higham.Chapter06.BlockAntidiagonalNorm.OperatorTwo"
)
INDUCED_LP = (
    "NumStability.Source.Higham.Chapter06.BlockAntidiagonalNorm.InducedLp"
)

HISTORICAL_OWNERS = {OLD_LEMMA06, OLD_ASIDES, OLD_BLOCK, OLD_DUALITY}
DESTINATIONS = (
    LEMMA06,
    EQUATION01,
    EQUATION02,
    EUCLIDEAN,
    UNITARY,
    CONDITION,
    MAX_NORM,
    OPERATOR_TWO,
    INDUCED_LP,
)

ASIDES = "NumStability.Source.Higham.Chapter06.Asides"
BLOCK_ANTIDIAGONAL = (
    "NumStability.Source.Higham.Chapter06.BlockAntidiagonalNorm"
)
CHAPTER06 = "NumStability.Source.Higham.Chapter06"
CHAPTER06_NORMS = "NumStability.Source.Higham.Chapter06.Norms"

EXPECTED_IMPORT_ONLY = {
    OLD_LEMMA06: (LEMMA06,),
    OLD_ASIDES: (ASIDES,),
    OLD_BLOCK: (INDUCED_LP,),
    OLD_DUALITY: (EQUATION02,),
    ASIDES: (
        CONDITION,
        EUCLIDEAN,
        MAX_NORM,
        UNITARY,
        OPERATOR_TWO,
        EQUATION01,
    ),
    BLOCK_ANTIDIAGONAL: (INDUCED_LP, OPERATOR_TWO),
    CHAPTER06: (ASIDES, BLOCK_ANTIDIAGONAL, EQUATION02, LEMMA06, CHAPTER06_NORMS),
    CHAPTER06_NORMS: (
        "NumStability.Source.Higham.Chapter06.Problem01",
        "NumStability.Source.Higham.Chapter06.Problem05",
        "NumStability.Source.Higham.Chapter06.Problem09",
        "NumStability.Source.Higham.Chapter06.Problem10",
        "NumStability.Source.Higham.Chapter06.Theorem04",
    ),
}
STRUCTURAL_MODULES = set(EXPECTED_IMPORT_ONLY)

MATRIX_BASIC = "NumStability.Analysis.MatrixNorms.Basic"
MATRIX_COMPARISONS = "NumStability.Analysis.MatrixNorms.Comparisons"
MATRIX_LP = "NumStability.Analysis.MatrixNorms.Lp"
OPERATOR_BASIC = "NumStability.Analysis.OperatorNorms.Basic"
SINGULAR_BASIC = "NumStability.Analysis.SingularValues.Basic"
VECTOR_BASIC = "NumStability.Analysis.VectorNorms.Basic"
VECTOR_DUALITY = "NumStability.Analysis.VectorNorms.Duality"

ALLOWED_PROJECT_IMPORTS = {
    LEMMA06: {MATRIX_BASIC, MATRIX_COMPARISONS, SINGULAR_BASIC, VECTOR_BASIC},
    EQUATION01: {VECTOR_BASIC},
    EQUATION02: {VECTOR_BASIC, VECTOR_DUALITY},
    EUCLIDEAN: set(),
    UNITARY: {MATRIX_BASIC, SINGULAR_BASIC},
    CONDITION: {MATRIX_BASIC, SINGULAR_BASIC, UNITARY},
    MAX_NORM: {MATRIX_BASIC, SINGULAR_BASIC},
    OPERATOR_TWO: {MATRIX_BASIC, SINGULAR_BASIC, UNITARY},
    INDUCED_LP: {
        MATRIX_BASIC,
        MATRIX_COMPARISONS,
        MATRIX_LP,
        OPERATOR_BASIC,
        VECTOR_BASIC,
    },
}
EXPECTED_DIRECT_SOURCE_IMPORTS = {
    owner: set() for owner in DESTINATIONS
}
EXPECTED_DIRECT_SOURCE_IMPORTS[CONDITION] = {UNITARY}
EXPECTED_DIRECT_SOURCE_IMPORTS[OPERATOR_TWO] = {UNITARY}

ASIDES_EXTERNAL_IMPORTS = {
    "Mathlib.Analysis.CStarAlgebra.Matrix",
    "Mathlib.Analysis.Calculus.FDeriv.Norm",
    "Mathlib.Analysis.InnerProductSpace.Calculus",
    "Mathlib.Analysis.SpecialFunctions.Sqrt",
}
ALLOWED_EXTERNAL_IMPORTS = {
    LEMMA06: set(),
    EQUATION01: ASIDES_EXTERNAL_IMPORTS,
    EQUATION02: {"Mathlib.Analysis.Normed.Module.Dual"},
    EUCLIDEAN: ASIDES_EXTERNAL_IMPORTS,
    UNITARY: ASIDES_EXTERNAL_IMPORTS,
    CONDITION: ASIDES_EXTERNAL_IMPORTS,
    MAX_NORM: ASIDES_EXTERNAL_IMPORTS,
    OPERATOR_TWO: ASIDES_EXTERNAL_IMPORTS,
    INDUCED_LP: {
        "Mathlib.Analysis.Normed.Lp.PiLp",
        "Mathlib.Analysis.Normed.Operator.Basic",
    },
}

EXPECTED_TEST_IMPORTS = {
    "NumStabilityTest/Import/Source/Chapter06/AsidesConditionNumberBounds.lean": CONDITION,
    "NumStabilityTest/Import/Source/Chapter06/AsidesEuclideanNormDifferentiability.lean": EUCLIDEAN,
    "NumStabilityTest/Import/Source/Chapter06/AsidesMaxNormInconsistency.lean": MAX_NORM,
    "NumStabilityTest/Import/Source/Chapter06/AsidesUnitaryInvariance.lean": UNITARY,
    "NumStabilityTest/Import/Source/Chapter06/BlockAntidiagonalNormInducedLp.lean": INDUCED_LP,
    "NumStabilityTest/Import/Source/Chapter06/BlockAntidiagonalNormOperatorTwo.lean": OPERATOR_TWO,
    "NumStabilityTest/Import/Source/Chapter06/Equation01.lean": EQUATION01,
    "NumStabilityTest/Import/Source/Chapter06/Equation02.lean": EQUATION02,
    "NumStabilityTest/Import/Source/Chapter06/Lemma06.lean": LEMMA06,
    "NumStabilityTest/Import/Source/Chapter06/Asides.lean": ASIDES,
    "NumStabilityTest/Import/Source/Chapter06/BlockAntidiagonalNorm.lean": BLOCK_ANTIDIAGONAL,
    "NumStabilityTest/Import/Compatibility/Source/Chapter06/AlgorithmsChapter06Lemma66.lean": OLD_LEMMA06,
    "NumStabilityTest/Import/Compatibility/Source/Chapter06/AnalysisHigham6Asides.lean": OLD_ASIDES,
    "NumStabilityTest/Import/Compatibility/Source/Chapter06/AnalysisHigham6BlockAntidiag.lean": OLD_BLOCK,
    "NumStabilityTest/Import/Compatibility/Source/Chapter06/AnalysisHighamChapter6Duality.lean": OLD_DUALITY,
}

EXPECTED_CONSUMER_IMPORTS = {
    "NumStability/Algorithms/Ch10Ch14Lemma66Op2Bridge.lean": {LEMMA06},
    "NumStability/Algorithms/QR/Higham19Theorem5SourceClosure.lean": {LEMMA06},
    "NumStability/Algorithms.lean": {LEMMA06, ASIDES, BLOCK_ANTIDIAGONAL},
    "NumStability/Analysis.lean": {CHAPTER06},
}

EXPECTED_CROSS_OWNER_EDGES = Counter(
    {
        ("body", CONDITION, UNITARY): 1,
        ("body", OPERATOR_TWO, UNITARY): 1,
    }
)
EXPECTED_CROSS_EDGE_WITNESSES = Counter(
    {
        (
            "body",
            "NumStability.ch6aside_op2_mul_le",
            "NumStability.ch6aside_op2_eq_l2",
        ): 1,
        (
            "body",
            "NumStability.ch6aside_blockAntidiag_op2_eq",
            "NumStability.ch6aside_op2_eq_l2",
        ): 1,
    }
)

EXPECTED_PRIVATE_CANDIDATE_NAMES = {
    "_private.<module>.NumStability.ch6aside_l2_one": (
        "_private.NumStability.Source.Higham.Chapter06.Asides."
        "UnitaryInvariance.0.NumStability.ch6aside_l2_one"
    ),
    "_private.<module>.NumStability.ch6aside_l2_unitary": (
        "_private.NumStability.Source.Higham.Chapter06.Asides."
        "UnitaryInvariance.0.NumStability.ch6aside_l2_unitary"
    ),
    "_private.<module>.NumStability.ch6aside_withLpBlockSwapCLM_bound": (
        "_private.NumStability.Source.Higham.Chapter06.BlockAntidiagonalNorm."
        "InducedLp.0.NumStability.ch6aside_withLpBlockSwapCLM_bound"
    ),
}

BASELINE_TSV_SHA256 = (
    "89A22BFBB70513DE4FEE3734AABC1FDADA3FC7C737164923808CBCD4FC79EB30"
)
EXPECTED_GLOBAL_DECLARATIONS = 81_950
EXPECTED_GLOBAL_SIGNATURE_EDGES = 305_425
EXPECTED_GLOBAL_BODY_EDGES = 439_195
EXPECTED_GLOBAL_UNION_EDGES = 491_557

EXPECTED_MANIFEST_ROWS = 69
EXPECTED_MANIFEST_BYTES = 11_091
EXPECTED_MANIFEST_SHA256 = (
    "28FDFD53016CDD5365ED32089DED59625F1E37007C119F9705B7F7C26B948581"
)
EXPECTED_MANIFEST_FILE_BYTES = 11_100
EXPECTED_MANIFEST_FILE_SHA256 = (
    "33A67750AD55F9C1E856A3B8FF2868CF81EBE0E5144BF75EA992BB905E77E8FD"
)

# total, public, internal, private, definition, theorem
EXPECTED_COUNTS = {
    LEMMA06: (20, 18, 2, 0, 3, 17),
    EQUATION01: (4, 4, 0, 0, 0, 4),
    EQUATION02: (3, 3, 0, 0, 1, 2),
    EUCLIDEAN: (2, 2, 0, 0, 0, 2),
    UNITARY: (6, 4, 0, 2, 0, 6),
    CONDITION: (7, 7, 0, 0, 0, 7),
    MAX_NORM: (6, 5, 1, 0, 0, 6),
    OPERATOR_TWO: (3, 3, 0, 0, 0, 3),
    INDUCED_LP: (18, 10, 7, 1, 3, 15),
}

EXPECTED_OWNER_SHA256 = {
    LEMMA06: "08C77AA876C1D5DBC767DED90FDB42510386FEA897D9D651A8CB642EE61F2400",
    EQUATION01: "460A1CBD4E90F589D70E0E68A0FF358956A9D6661460AAF31F0DEF483B388982",
    EQUATION02: "75C241CE3D081F2214F7D83983B20B8FE7BB186EE9BDECA069D20B22F63C7E51",
    EUCLIDEAN: "695CBBF866C7FD21D6290CFAC51D5F535CC424DA812D348E42FBD5B08EB71D41",
    UNITARY: "3B9F10235FCCD6AABF742540D67EE22BC6F3EA043146B200FFCC82C590C5DECA",
    CONDITION: "34C09E384B1771AFC1275EBB81A4D0CAC3FABC6CDD6FE6245935D7525FC8B75B",
    MAX_NORM: "7F96196D10AD8E32BC4DBB6594D4D5719254EF17C33A8A668D4013C2165A1122",
    OPERATOR_TWO: "EFFE3B5EF1596589492B0D1166F9D3151015D20EDCDE5B06677C1362BAEE69A1",
    INDUCED_LP: "8D5E9471EA378AB94096C0F2734F5EFF88EE2D58D4AF4BDD2BAA4374B01D0D17",
}

EXPECTED_INCIDENT_EDGES = 440
EXPECTED_SIGNATURE_INCIDENT_EDGES = 158
EXPECTED_BODY_INCIDENT_EDGES = 282
EXPECTED_INCIDENT_EDGE_BYTES = 40_382
EXPECTED_INCIDENT_EDGE_SHA256 = (
    "9E879119F3FEB28FC64A6B554C59F110C685AFDB9C8BAE83D918709536950C28"
)
EXPECTED_INTERNAL_EDGES = 126
EXPECTED_SIGNATURE_INTERNAL_EDGES = 37
EXPECTED_BODY_INTERNAL_EDGES = 89
EXPECTED_INTERNAL_EDGE_BYTES = 12_627
EXPECTED_INTERNAL_EDGE_SHA256 = (
    "880A472E8600F18DCA192C89FB7B3AF0A2157E395FB93426281646C4028C9987"
)

UNITARY_NAMES = {
    "NumStability.ch6aside_op2_eq_l2",
    "NumStability.ch6aside_op2_two_sided_unitary_invariant",
    "NumStability.ch6aside_frobeniusSq_eq_trace",
    "NumStability.ch6aside_frobenius_two_sided_unitary_invariant",
}
CONDITION_NAMES = {
    "NumStability.ch6aside_complexMatrixMul_eq_matMul",
    "NumStability.ch6aside_conditionNumber_ge_one",
    "NumStability.ch6aside_op2_mul_le",
    "NumStability.ch6aside_op2_conditionNumber_ge_one",
    "NumStability.ch6aside_frobenius_one",
    "NumStability.ch6aside_frobenius_mul_le",
    "NumStability.ch6aside_conditionF_ge_sqrt_n",
}
OPERATOR_TWO_NAMES = {
    "NumStability.ch6aside_blockAntidiag_hermitian",
    "NumStability.ch6aside_blockAntidiag_sq",
    "NumStability.ch6aside_blockAntidiag_op2_eq",
}


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
    expected_module: str
    kind: str
    visibility: str


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def logical_name(name: str, actual_module: str) -> str:
    """Normalize only the module component of a Lean private name.

    The numeric private-scope ordinal is part of Lean's module-encoded private
    prefix and is discarded consistently with the Phase 11B1 checker.
    Generated ``.eq_*`` and ``._proof_*`` suffixes are never normalized.
    """

    prefix = f"_private.{actual_module}."
    if not name.startswith(prefix):
        return name
    private_scope, separator, suffix = name[len(prefix) :].partition(".")
    if not separator or not private_scope.isdigit() or not suffix:
        raise ValueError(f"unexpected private name: {name}")
    return f"_private.<module>.{suffix}"


def destination_for(declaration: Declaration) -> str:
    name = declaration.name
    module = declaration.module
    if module == OLD_LEMMA06:
        return LEMMA06
    if module == OLD_BLOCK:
        return INDUCED_LP
    if module == OLD_DUALITY:
        return EQUATION02
    if module != OLD_ASIDES:
        raise ValueError(f"unexpected historical owner: {module}")

    if name.startswith("NumStability.higham6_holder_"):
        return EQUATION01
    if name.startswith("NumStability.higham6_euclideanNorm_"):
        return EUCLIDEAN
    if (
        name in UNITARY_NAMES
        or name.endswith(".NumStability.ch6aside_l2_one")
        or name.endswith(".NumStability.ch6aside_l2_unitary")
    ):
        return UNITARY
    if name in CONDITION_NAMES:
        return CONDITION
    if name.startswith("NumStability.ch6aside_maxNorm_"):
        return MAX_NORM
    if name in OPERATOR_TWO_NAMES:
        return OPERATOR_TWO
    raise ValueError(f"unassigned Higham6Asides constant: {name}")


def read_tsv(path: Path) -> tuple[list[Declaration], list[tuple[str, str, str]]]:
    declarations: list[Declaration] = []
    edges: list[tuple[str, str, str]] = []
    saw_format = False
    with path.open(encoding="utf-8", newline="") as stream:
        for row in csv.reader(stream, delimiter="\t"):
            if not row:
                continue
            if row == ["format", "2"]:
                if saw_format or declarations or edges:
                    raise ValueError("misplaced or duplicate format row")
                saw_format = True
            elif row[0] == "declaration" and len(row) == 5:
                declarations.append(Declaration(*row[1:]))
            elif row[0] == "edge" and len(row) == 4:
                edges.append((row[1], row[2], row[3]))
            else:
                raise ValueError(f"malformed dependency row: {row!r}")
    if not saw_format:
        raise ValueError("dependency TSV must start with 'format\\t2'")
    return declarations, edges


def strip_lean_comments(lines: list[str]) -> list[str]:
    """Remove nested block comments and line comments from Lean source."""

    result: list[str] = []
    depth = 0
    for source_line in lines:
        output: list[str] = []
        index = 0
        while index < len(source_line):
            if depth:
                if source_line.startswith("/-", index):
                    depth += 1
                    index += 2
                elif source_line.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            else:
                if source_line.startswith("--", index):
                    break
                if source_line.startswith("/-", index):
                    depth = 1
                    index += 2
                else:
                    output.append(source_line[index])
                    index += 1
        result.append("".join(output))
    if depth:
        raise ValueError("unterminated Lean block comment")
    return result


def module_path(project_root: Path, module: str) -> Path:
    return project_root / (module.replace(".", "/") + ".lean")


def ordered_direct_imports(path: Path) -> tuple[str, ...]:
    if not path.is_file():
        raise ValueError(f"missing Lean module: {path}")
    imports: list[str] = []
    source_lines = path.read_text(encoding="utf-8").splitlines()
    for original, code in zip(
        source_lines, strip_lean_comments(source_lines), strict=True
    ):
        stripped = code.strip()
        if not stripped:
            continue
        fields = stripped.split()
        if len(fields) == 2 and fields[0] == "import":
            imports.append(fields[1])
        elif len(fields) == 3 and fields[:2] == ["public", "import"]:
            imports.append(fields[2])
        elif fields[0] == "import" or (
            len(fields) > 1 and fields[:2] == ["public", "import"]
        ):
            raise ValueError(f"unparsed import command in {path}: {original!r}")
    return tuple(imports)


def validate_import_only(path: Path, expected: tuple[str, ...]) -> None:
    source = path.read_text(encoding="utf-8")
    if "/-!" not in source:
        raise ValueError(f"import-only module lacks a module docstring: {path}")
    source_lines = source.splitlines()
    imports: list[str] = []
    for original, code in zip(
        source_lines, strip_lean_comments(source_lines), strict=True
    ):
        stripped = code.strip()
        if not stripped:
            continue
        fields = stripped.split()
        if len(fields) == 2 and fields[0] == "import":
            imports.append(fields[1])
        elif len(fields) == 3 and fields[:2] == ["public", "import"]:
            imports.append(fields[2])
        else:
            raise ValueError(
                f"import-only module contains non-import code in {path}: {original!r}"
            )
    actual = tuple(imports)
    if actual != expected:
        raise ValueError(
            f"{path}: expected ordered imports {expected}, found {actual}"
        )


def validate_declaration_module_docstring(path: Path) -> None:
    source_lines = path.read_text(encoding="utf-8").splitlines()
    namespace_index = next(
        (
            index
            for index, line in enumerate(source_lines)
            if line.strip().startswith("namespace ")
        ),
        len(source_lines),
    )
    if "/-!" not in "\n".join(source_lines[:namespace_index]):
        raise ValueError(
            f"declaration module lacks a module docstring before its namespace: {path}"
        )


def validate_source_import_contracts(project_root: Path) -> None:
    for module, expected in EXPECTED_IMPORT_ONLY.items():
        validate_import_only(module_path(project_root, module), expected)

    for owner in DESTINATIONS:
        path = module_path(project_root, owner)
        validate_declaration_module_docstring(path)
        imports = set(ordered_direct_imports(path))
        allowed = ALLOWED_PROJECT_IMPORTS[owner] | ALLOWED_EXTERNAL_IMPORTS[owner]
        unexpected = sorted(imports - allowed)
        if unexpected:
            raise ValueError(
                f"{owner} has imports outside the frozen allowlist: {unexpected}"
            )
        actual_source_imports = imports & set(DESTINATIONS)
        if actual_source_imports != EXPECTED_DIRECT_SOURCE_IMPORTS[owner]:
            raise ValueError(
                f"{owner}: expected direct source-owner imports "
                f"{sorted(EXPECTED_DIRECT_SOURCE_IMPORTS[owner])}, found "
                f"{sorted(actual_source_imports)}"
            )


def validate_test_import_contracts(project_root: Path) -> None:
    for relative_path, target in EXPECTED_TEST_IMPORTS.items():
        path = project_root / relative_path
        imports = ordered_direct_imports(path)
        if imports != (target,):
            raise ValueError(
                f"{path}: isolated test must import only {target}; found {imports}"
            )


def validate_consumer_retargets(project_root: Path) -> None:
    historical_imports: list[tuple[Path, str]] = []
    production_root = project_root / "NumStability"
    for path in production_root.rglob("*.lean"):
        for imported in ordered_direct_imports(path):
            if imported in HISTORICAL_OWNERS:
                historical_imports.append((path, imported))
    if historical_imports:
        rendered = ", ".join(f"{path}: {module}" for path, module in historical_imports)
        raise ValueError(f"production modules still import historical paths: {rendered}")

    for relative_path, required in EXPECTED_CONSUMER_IMPORTS.items():
        path = project_root / relative_path
        imports = set(ordered_direct_imports(path))
        missing = sorted(required - imports)
        if missing:
            raise ValueError(f"{path} lacks canonical imports: {missing}")

    algorithms_imports = set(
        ordered_direct_imports(project_root / "NumStability/Algorithms.lean")
    )
    if EQUATION02 in algorithms_imports or CHAPTER06 in algorithms_imports:
        raise ValueError(
            "Algorithms aggregate must preserve the bounded historical surface "
            "without Equation02 or the complete Chapter06 aggregate"
        )


def manifest_payload(records: dict[str, ManifestRow]) -> bytes:
    return "".join(
        "\t".join(
            (
                row.logical_name,
                row.historical_module,
                row.expected_module,
                row.kind,
                row.visibility,
            )
        )
        + "\n"
        for _, row in sorted(records.items())
    ).encode("utf-8")


def validate_manifest(records: dict[str, ManifestRow]) -> bytes:
    if len(records) != EXPECTED_MANIFEST_ROWS:
        raise ValueError(f"expected 69 ownership rows, found {len(records)}")
    if {row.expected_module for row in records.values()} != set(DESTINATIONS):
        raise ValueError("manifest destination set differs from the frozen map")
    if {row.historical_module for row in records.values()} != HISTORICAL_OWNERS:
        raise ValueError("manifest historical-owner set differs from the frozen map")

    counts: dict[str, Counter[str]] = defaultdict(Counter)
    for row in records.values():
        counter = counts[row.expected_module]
        counter["total"] += 1
        counter[row.visibility] += 1
        counter[row.kind] += 1
    for owner, expected in EXPECTED_COUNTS.items():
        counter = counts[owner]
        actual = (
            counter["total"],
            counter["public"],
            counter["internal"],
            counter["private"],
            counter["definition"],
            counter["theorem"],
        )
        if actual != expected:
            raise ValueError(f"{owner}: expected counts {expected}, found {actual}")
        owner_records = {
            name: row
            for name, row in records.items()
            if row.expected_module == owner
        }
        digest = sha256_bytes(manifest_payload(owner_records))
        if digest != EXPECTED_OWNER_SHA256[owner]:
            raise ValueError(f"{owner}: unexpected ownership hash {digest}")

    payload = manifest_payload(records)
    if len(payload) != EXPECTED_MANIFEST_BYTES:
        raise ValueError(
            f"expected {EXPECTED_MANIFEST_BYTES} manifest bytes, found {len(payload)}"
        )
    digest = sha256_bytes(payload)
    if digest != EXPECTED_MANIFEST_SHA256:
        raise ValueError(f"unexpected manifest payload hash {digest}")
    return payload


def edge_payloads(
    edges: list[tuple[str, str, str]], actual_to_logical: dict[str, str]
) -> tuple[bytes, Counter[str], bytes, Counter[str]]:
    incident_rows: list[str] = []
    internal_rows: list[str] = []
    incident_kinds: Counter[str] = Counter()
    internal_kinds: Counter[str] = Counter()
    for edge_kind, source, target in edges:
        source_inside = source in actual_to_logical
        target_inside = target in actual_to_logical
        if not source_inside and not target_inside:
            continue
        row = "\t".join(
            (
                "edge",
                edge_kind,
                actual_to_logical.get(source, source),
                actual_to_logical.get(target, target),
            )
        )
        incident_rows.append(row)
        incident_kinds[edge_kind] += 1
        if source_inside and target_inside:
            internal_rows.append(row)
            internal_kinds[edge_kind] += 1

    incident = ("\n".join(sorted(incident_rows)) + "\n").encode("utf-8")
    internal = ("\n".join(sorted(internal_rows)) + "\n").encode("utf-8")
    return incident, incident_kinds, internal, internal_kinds


def validate_edge_evidence(
    edges: list[tuple[str, str, str]], actual_to_logical: dict[str, str]
) -> None:
    incident, incident_kinds, internal, internal_kinds = edge_payloads(
        edges, actual_to_logical
    )
    if sum(incident_kinds.values()) != EXPECTED_INCIDENT_EDGES:
        raise ValueError("incident-edge count differs from the frozen graph")
    if incident_kinds != Counter(
        {
            "signature": EXPECTED_SIGNATURE_INCIDENT_EDGES,
            "body": EXPECTED_BODY_INCIDENT_EDGES,
        }
    ):
        raise ValueError(f"unexpected incident-edge kinds: {incident_kinds}")
    if (
        len(incident) != EXPECTED_INCIDENT_EDGE_BYTES
        or sha256_bytes(incident) != EXPECTED_INCIDENT_EDGE_SHA256
    ):
        raise ValueError("incident-edge payload differs from the frozen graph")

    if sum(internal_kinds.values()) != EXPECTED_INTERNAL_EDGES:
        raise ValueError("internal-edge count differs from the frozen graph")
    if internal_kinds != Counter(
        {
            "signature": EXPECTED_SIGNATURE_INTERNAL_EDGES,
            "body": EXPECTED_BODY_INTERNAL_EDGES,
        }
    ):
        raise ValueError(f"unexpected internal-edge kinds: {internal_kinds}")
    if (
        len(internal) != EXPECTED_INTERNAL_EDGE_BYTES
        or sha256_bytes(internal) != EXPECTED_INTERNAL_EDGE_SHA256
    ):
        raise ValueError("internal-edge payload differs from the frozen graph")


def generate_manifest(
    dependency_tsv: Path,
) -> tuple[dict[str, ManifestRow], dict[str, str]]:
    if sha256_file(dependency_tsv) != BASELINE_TSV_SHA256:
        raise ValueError("dependency TSV is not the frozen Phase 11B1 stream")
    declarations, edges = read_tsv(dependency_tsv)
    edge_kinds = Counter(kind for kind, _, _ in edges)
    union_edges = len({(source, target) for _, source, target in edges})
    if (
        len(declarations) != EXPECTED_GLOBAL_DECLARATIONS
        or edge_kinds["signature"] != EXPECTED_GLOBAL_SIGNATURE_EDGES
        or edge_kinds["body"] != EXPECTED_GLOBAL_BODY_EDGES
        or union_edges != EXPECTED_GLOBAL_UNION_EDGES
    ):
        raise ValueError("global declaration graph differs from Phase 11B1")

    frozen = [d for d in declarations if d.module in HISTORICAL_OWNERS]
    records: dict[str, ManifestRow] = {}
    actual_to_logical: dict[str, str] = {}
    for declaration in frozen:
        logical = logical_name(declaration.name, declaration.module)
        if logical in records:
            raise ValueError(f"duplicate logical declaration name: {logical}")
        records[logical] = ManifestRow(
            logical,
            declaration.module,
            destination_for(declaration),
            declaration.kind,
            declaration.visibility,
        )
        actual_to_logical[declaration.name] = logical

    validate_manifest(records)
    validate_edge_evidence(edges, actual_to_logical)
    return records, actual_to_logical


def read_manifest(path: Path) -> dict[str, ManifestRow]:
    raw = path.read_bytes()
    if len(raw) != EXPECTED_MANIFEST_FILE_BYTES:
        raise ValueError(
            f"expected {EXPECTED_MANIFEST_FILE_BYTES} manifest bytes, found {len(raw)}"
        )
    if sha256_bytes(raw) != EXPECTED_MANIFEST_FILE_SHA256:
        raise ValueError("tracked ownership-manifest hash differs from the frozen file")
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["format", "1"]:
        raise ValueError("ownership manifest must start with 'format\\t1'")
    records: dict[str, ManifestRow] = {}
    for row in rows[1:]:
        if len(row) != 5:
            raise ValueError(f"malformed ownership row: {row!r}")
        record = ManifestRow(*row)
        if record.logical_name in records:
            raise ValueError(f"duplicate ownership row: {record.logical_name}")
        records[record.logical_name] = record
    validate_manifest(records)
    return records


def write_manifest(path: Path, records: dict[str, ManifestRow]) -> None:
    payload = b"format\t1\n" + validate_manifest(records)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(payload)


def validate_cross_owner_graph(
    edges: list[tuple[str, str, str]],
    actual_to_logical: dict[str, str],
    records: dict[str, ManifestRow],
) -> None:
    owner_edges: Counter[tuple[str, str, str]] = Counter()
    witnesses: Counter[tuple[str, str, str]] = Counter()
    for edge_kind, source, target in edges:
        source_logical = actual_to_logical.get(source)
        target_logical = actual_to_logical.get(target)
        if source_logical is None or target_logical is None:
            continue
        source_owner = records[source_logical].expected_module
        target_owner = records[target_logical].expected_module
        if source_owner == target_owner:
            continue
        owner_edges[(edge_kind, source_owner, target_owner)] += 1
        witnesses[(edge_kind, source_logical, target_logical)] += 1

    if owner_edges != EXPECTED_CROSS_OWNER_EDGES:
        raise ValueError(
            f"cross-owner dependency graph differs: expected "
            f"{EXPECTED_CROSS_OWNER_EDGES}, found {owner_edges}"
        )
    if witnesses != EXPECTED_CROSS_EDGE_WITNESSES:
        raise ValueError(
            f"cross-owner edge witnesses differ: expected "
            f"{EXPECTED_CROSS_EDGE_WITNESSES}, found {witnesses}"
        )

    graph: dict[str, set[str]] = {owner: set() for owner in DESTINATIONS}
    for _, source_owner, target_owner in owner_edges:
        graph[source_owner].add(target_owner)
    temporary: set[str] = set()
    permanent: set[str] = set()

    def visit(owner: str) -> None:
        if owner in permanent:
            return
        if owner in temporary:
            raise ValueError(f"candidate owner cycle through {owner}")
        temporary.add(owner)
        for target in graph[owner]:
            visit(target)
        temporary.remove(owner)
        permanent.add(owner)

    for owner in DESTINATIONS:
        visit(owner)


def check_post_ownership(
    records: dict[str, ManifestRow],
    declarations: list[Declaration],
    edges: list[tuple[str, str, str]],
) -> dict[str, str]:
    structural = [
        declaration
        for declaration in declarations
        if declaration.module in STRUCTURAL_MODULES
    ]
    if structural:
        raise ValueError(
            "wrappers or aggregates own declarations: "
            + ", ".join(declaration.name for declaration in structural[:10])
        )

    actual_records: dict[str, Declaration] = {}
    actual_to_logical: dict[str, str] = {}
    for declaration in declarations:
        if declaration.module not in DESTINATIONS:
            continue
        logical = logical_name(declaration.name, declaration.module)
        if logical in actual_records:
            raise ValueError(f"duplicate candidate logical name: {logical}")
        actual_records[logical] = declaration
        actual_to_logical[declaration.name] = logical

    if set(actual_records) != set(records):
        missing = sorted(set(records) - set(actual_records))
        extra = sorted(set(actual_records) - set(records))
        raise ValueError(
            f"candidate ownership set differs: missing={missing[:20]}; "
            f"extra={extra[:20]}"
        )

    for logical, expected in records.items():
        actual = actual_records[logical]
        actual_metadata = (actual.module, actual.kind, actual.visibility)
        expected_metadata = (
            expected.expected_module,
            expected.kind,
            expected.visibility,
        )
        if actual_metadata != expected_metadata:
            raise ValueError(
                f"{logical}: expected {expected_metadata}, found {actual_metadata}"
            )
        if expected.visibility == "private":
            expected_actual_name = EXPECTED_PRIVATE_CANDIDATE_NAMES.get(logical)
            if expected_actual_name is None or actual.name != expected_actual_name:
                raise ValueError(
                    f"{logical}: expected exact private name "
                    f"{expected_actual_name}, found {actual.name}"
                )

    if set(EXPECTED_PRIVATE_CANDIDATE_NAMES) != {
        logical for logical, row in records.items() if row.visibility == "private"
    }:
        raise ValueError("private-name contract does not cover the manifest exactly")

    validate_manifest(
        {
            logical: ManifestRow(
                logical,
                records[logical].historical_module,
                declaration.module,
                declaration.kind,
                declaration.visibility,
            )
            for logical, declaration in actual_records.items()
        }
    )
    validate_edge_evidence(edges, actual_to_logical)
    validate_cross_owner_graph(edges, actual_to_logical, records)
    return actual_to_logical


def compare_full_graph(
    baseline_tsv: Path,
    candidate_tsv: Path,
    candidate_actual_to_logical: dict[str, str],
    records: dict[str, ManifestRow],
) -> None:
    if sha256_file(baseline_tsv) != BASELINE_TSV_SHA256:
        raise ValueError("baseline TSV is not the frozen Phase 11B1 stream")

    baseline_name_by_logical: dict[str, str] = {}
    with baseline_tsv.open(encoding="utf-8", newline="") as stream:
        for row in csv.reader(stream, delimiter="\t"):
            if len(row) != 5 or row[0] != "declaration":
                continue
            name, module = row[1], row[2]
            if module not in HISTORICAL_OWNERS:
                continue
            logical = logical_name(name, module)
            if logical in baseline_name_by_logical:
                raise ValueError(f"duplicate baseline logical name: {logical}")
            baseline_name_by_logical[logical] = name
    if set(baseline_name_by_logical) != set(records):
        raise ValueError("baseline ownership set differs from the tracked manifest")

    candidate_name_to_baseline = {
        actual: baseline_name_by_logical[logical]
        for actual, logical in candidate_actual_to_logical.items()
    }
    candidate_name_to_historical_module = {
        actual: records[logical].historical_module
        for actual, logical in candidate_actual_to_logical.items()
    }

    delta: Counter[str] = Counter()
    with baseline_tsv.open(encoding="utf-8") as stream:
        for raw in stream:
            delta[raw.rstrip("\r\n")] += 1

    with candidate_tsv.open(encoding="utf-8") as stream:
        for raw in stream:
            fields = raw.rstrip("\r\n").split("\t")
            if fields[0] == "declaration" and fields[1] in candidate_name_to_baseline:
                candidate_name = fields[1]
                fields[1] = candidate_name_to_baseline[candidate_name]
                fields[2] = candidate_name_to_historical_module[candidate_name]
            elif fields[0] == "edge" and len(fields) == 4:
                fields[2] = candidate_name_to_baseline.get(fields[2], fields[2])
                fields[3] = candidate_name_to_baseline.get(fields[3], fields[3])
            row = "\t".join(fields)
            delta[row] -= 1
            if delta[row] == 0:
                del delta[row]

    if delta:
        missing = sum(count for count in delta.values() if count > 0)
        extra = -sum(count for count in delta.values() if count < 0)
        details = "; ".join(
            f"{count:+d} {row}" for row, count in sorted(delta.items())[:12]
        )
        raise ValueError(
            f"normalized full graph differs: missing={missing}, extra={extra}; "
            f"{details}"
        )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("pre", "post"), required=True)
    parser.add_argument("--dependency-tsv", type=Path, required=True)
    parser.add_argument(
        "--manifest",
        type=Path,
        default=Path(
            "docs/architecture/declaration-ownership/chapter06-phase11b2.tsv"
        ),
    )
    parser.add_argument(
        "--write-manifest",
        action="store_true",
        help="write the frozen manifest; valid only in pre-migration mode",
    )
    parser.add_argument(
        "--baseline-tsv",
        type=Path,
        help="frozen Phase 11B1 TSV required for post-migration full-graph comparison",
    )
    parser.add_argument(
        "--project-root",
        type=Path,
        default=Path("."),
        help="repository root used for import, wrapper, consumer, and test checks",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.write_manifest and args.mode != "pre":
        raise ValueError("--write-manifest is valid only in pre-migration mode")

    if args.mode == "pre":
        records, _ = generate_manifest(args.dependency_tsv)
        if args.write_manifest:
            write_manifest(args.manifest, records)
        tracked = read_manifest(args.manifest)
        if tracked != records:
            raise ValueError("tracked manifest differs from the frozen generator output")
        print(
            "Phase 11B2 pre-migration ownership passed: "
            f"{len(records)} constants, {EXPECTED_INCIDENT_EDGES} incident edges, "
            f"inventory {EXPECTED_MANIFEST_SHA256}"
        )
        return 0

    if args.baseline_tsv is None:
        raise ValueError("post-migration mode requires --baseline-tsv")
    records = read_manifest(args.manifest)
    declarations, edges = read_tsv(args.dependency_tsv)
    candidate_actual_to_logical = check_post_ownership(records, declarations, edges)
    validate_source_import_contracts(args.project_root)
    validate_test_import_contracts(args.project_root)
    validate_consumer_retargets(args.project_root)
    compare_full_graph(
        args.baseline_tsv,
        args.dependency_tsv,
        candidate_actual_to_logical,
        records,
    )
    print(
        "Phase 11B2 post-migration ownership passed: "
        f"{len(records)} constants and exact full graph preserved"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError) as error:
        print(f"ownership check failed: {error}", file=sys.stderr)
        raise SystemExit(1)
