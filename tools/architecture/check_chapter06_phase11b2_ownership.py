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
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.mode != "pre":
        raise ValueError("post-migration mode is not available before the map commit")
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


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError) as error:
        print(f"ownership check failed: {error}", file=sys.stderr)
        raise SystemExit(1)
