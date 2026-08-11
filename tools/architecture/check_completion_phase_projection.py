#!/usr/bin/env python3
"""Compare a frozen format-2 declaration projection with a candidate graph.

Every declaration row in the frozen projection selects one declaration.  The
projection's edge rows are its complete typed incident graph: each edge must
have at least one selected endpoint, while its other endpoint may be outside
the projection.  The candidate must preserve selected declaration names,
kinds, visibility, and the exact signature/body incident edge sets.  Only the
owning module may change, and every candidate owner must match an exact module
or namespace prefix declared on the command line.

An optional hash-pinned private normalization map permits selected private
names to change.  It is total over the projection's private declarations and
also pins each normalized declaration's destination owner.

Both inputs may be plain TSV or deterministic gzip (no optional gzip header
fields and an all-zero timestamp).  Exit status is 0 for a match, 1 for a
semantic mismatch, and 2 for malformed input, duplicate data, or bad frozen
hash evidence.
"""

from __future__ import annotations

import argparse
import csv
import gzip
import hashlib
import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Iterator, Sequence, TextIO


FORMAT_ROW = ("format", "2")
EDGE_KINDS = {"signature", "body"}
VISIBILITIES = {"public", "private", "internal"}
MODULE_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")
SHA256_RE = re.compile(r"^[0-9A-Fa-f]{64}$")
GZIP_MAGIC = b"\x1f\x8b"


class InputError(ValueError):
    """The input stream or its frozen evidence is malformed."""


@dataclass(frozen=True)
class Declaration:
    name: str
    module: str
    kind: str
    visibility: str


@dataclass(frozen=True, order=True)
class Edge:
    kind: str
    source: str
    target: str


@dataclass
class ParsedGraph:
    declarations: dict[str, Declaration]
    incident_edges: set[Edge]
    declaration_count: int
    edge_count: int


@dataclass(frozen=True)
class PrivateNormalization:
    old_private: str
    new_private: str
    destination_module: str


@dataclass(frozen=True)
class PrivateNormalizationMap:
    by_old: dict[str, PrivateNormalization]
    by_new: dict[str, PrivateNormalization]
    sha256: str


@dataclass(frozen=True)
class AllowedOwners:
    exact_modules: tuple[str, ...]
    prefixes: tuple[str, ...]

    def contains(self, module: str) -> bool:
        return module in self.exact_modules or any(module.startswith(prefix) for prefix in self.prefixes)


@dataclass
class Comparison:
    errors: list[str]
    relocated: int
    signature_edges: int
    body_edges: int
    private_normalizations: int = 0
    private_map_sha256: str | None = None


def sha256_path(path: Path) -> str:
    digest = hashlib.sha256()
    try:
        with path.open("rb") as stream:
            while chunk := stream.read(1024 * 1024):
                digest.update(chunk)
    except OSError as error:
        raise InputError(f"cannot read {path}: {error}") from error
    return digest.hexdigest().upper()


def gzip_input(path: Path) -> bool:
    try:
        with path.open("rb") as stream:
            header = stream.read(10)
    except OSError as error:
        raise InputError(f"cannot read {path}: {error}") from error
    compressed = header.startswith(GZIP_MAGIC)
    if path.suffix.lower() == ".gz" and not compressed:
        raise InputError(f"{path}: .gz input does not contain a gzip stream")
    if not compressed:
        return False
    if len(header) != 10 or header[2] != 8:
        raise InputError(f"{path}: malformed or unsupported gzip header")
    flags = header[3]
    if flags != 0:
        raise InputError(
            f"{path}: gzip is not deterministic: optional header flags are 0x{flags:02x}, expected 0"
        )
    mtime = int.from_bytes(header[4:8], "little")
    if mtime != 0:
        raise InputError(
            f"{path}: gzip is not deterministic: timestamp is {mtime}, expected 0"
        )
    return True


def open_text(path: Path) -> tuple[TextIO, bool]:
    compressed = gzip_input(path)
    try:
        if compressed:
            return gzip.open(path, mode="rt", encoding="utf-8", newline=""), True
        return path.open(mode="r", encoding="utf-8", newline=""), False
    except OSError as error:
        raise InputError(f"cannot open {path}: {error}") from error


def validate_module(module: str, context: str) -> None:
    if not MODULE_RE.fullmatch(module):
        raise InputError(f"{context}: invalid Lean module name {module!r}")


def edge_sort_key(edge: Edge) -> tuple[str, int, str]:
    return (edge.source, 0 if edge.kind == "signature" else 1, edge.target)


def rows(path: Path) -> Iterator[tuple[int, list[str]]]:
    stream, compressed = open_text(path)
    try:
        reader = csv.reader(stream, delimiter="\t", quoting=csv.QUOTE_NONE, strict=True)
        try:
            for line_number, row in enumerate(reader, start=1):
                yield line_number, row
        except (csv.Error, UnicodeError, gzip.BadGzipFile, EOFError) as error:
            kind = "gzip payload" if compressed else "TSV"
            raise InputError(f"{path}: malformed {kind}: {error}") from error
    finally:
        try:
            stream.close()
        except (OSError, gzip.BadGzipFile, EOFError) as error:
            raise InputError(f"{path}: malformed gzip trailer: {error}") from error


def parse_projection(path: Path) -> ParsedGraph:
    declarations: dict[str, Declaration] = {}
    edges: set[Edge] = set()
    declaration_order: list[str] = []
    edge_order: list[Edge] = []
    saw_format = False
    saw_edge = False
    saw_any = False
    for line_number, row in rows(path):
        context = f"{path}:{line_number}"
        if not row:
            raise InputError(f"{context}: blank rows are not allowed")
        saw_any = True
        if tuple(row) == FORMAT_ROW:
            if saw_format or line_number != 1:
                raise InputError(f"{context}: duplicate or misplaced format row")
            saw_format = True
            continue
        if not saw_format:
            raise InputError(f"{context}: stream must begin with 'format\\t2'")
        if row[0] == "declaration" and len(row) == 5:
            if saw_edge:
                raise InputError(f"{context}: declaration appears after an edge")
            declaration = Declaration(*row[1:])
            if not all((declaration.name, declaration.module, declaration.kind, declaration.visibility)):
                raise InputError(f"{context}: declaration fields must be nonempty")
            validate_module(declaration.module, context)
            if declaration.visibility not in VISIBILITIES:
                raise InputError(
                    f"{context}: visibility must be one of {sorted(VISIBILITIES)}"
                )
            if declaration.name in declarations:
                raise InputError(
                    f"{context}: duplicate selected declaration {declaration.name}"
                )
            declarations[declaration.name] = declaration
            declaration_order.append(declaration.name)
            continue
        if row[0] == "edge" and len(row) == 4:
            saw_edge = True
            kind, source, target = row[1:]
            if kind not in EDGE_KINDS or not source or not target:
                raise InputError(f"{context}: malformed typed edge")
            edge = Edge(kind, source, target)
            if edge in edges:
                raise InputError(
                    f"{context}: duplicate {kind} edge {source} -> {target}"
                )
            edges.add(edge)
            edge_order.append(edge)
            continue
        raise InputError(f"{context}: malformed format-2 row {row!r}")
    if not saw_any or not saw_format:
        raise InputError(f"{path}: missing 'format\\t2' row")
    if not declarations:
        raise InputError(f"{path}: projection selects no declarations")
    if declaration_order != sorted(declaration_order):
        raise InputError(f"{path}: projection declarations must be sorted by name")
    if edge_order != sorted(edge_order, key=edge_sort_key):
        raise InputError(
            f"{path}: projection edges must be ordered by source, signature before body, then target"
        )
    selected = set(declarations)
    for edge in sorted(edges):
        if edge.source not in selected and edge.target not in selected:
            raise InputError(
                f"{path}: projection edge is not incident to a selected declaration: "
                f"{edge.kind} {edge.source} -> {edge.target}"
            )
    return ParsedGraph(
        declarations=declarations,
        incident_edges=edges,
        declaration_count=len(declarations),
        edge_count=len(edges),
    )


def parse_private_normalization_map(
    path: Path,
    projection: ParsedGraph,
    sha256: str,
) -> PrivateNormalizationMap:
    expected_header = ("old_private", "new_private", "destination_module")
    by_old: dict[str, PrivateNormalization] = {}
    by_new: dict[str, PrivateNormalization] = {}
    saw_header = False
    for line_number, row in rows(path):
        context = f"{path}:{line_number}"
        if line_number == 1:
            if tuple(row) != expected_header:
                raise InputError(
                    f"{context}: expected exact header " + "\\t".join(expected_header)
                )
            saw_header = True
            continue
        if len(row) != 3 or not all(row):
            raise InputError(f"{context}: expected three nonempty TSV fields")
        entry = PrivateNormalization(*row)
        validate_module(entry.destination_module, context)
        if entry.old_private in by_old:
            raise InputError(
                f"{context}: duplicate old_private {entry.old_private!r}"
            )
        if entry.new_private in by_new:
            previous = by_new[entry.new_private].old_private
            raise InputError(
                f"{context}: non-injective new_private {entry.new_private!r}; "
                f"already mapped from {previous!r}"
            )
        by_old[entry.old_private] = entry
        by_new[entry.new_private] = entry
    if not saw_header:
        raise InputError(f"{path}: missing exact private normalization map header")

    expected_private = {
        name
        for name, declaration in projection.declarations.items()
        if declaration.visibility == "private"
    }
    actual = set(by_old)
    if actual != expected_private:
        missing = sorted(expected_private - actual)
        unexpected = sorted(actual - expected_private)
        details: list[str] = []
        if missing:
            details.append("missing " + ", ".join(missing))
        if unexpected:
            details.append("not selected-private " + ", ".join(unexpected))
        raise InputError(
            f"{path}: private map domain must equal every selected private declaration: "
            + "; ".join(details)
        )
    return PrivateNormalizationMap(by_old=by_old, by_new=by_new, sha256=sha256)


def parse_candidate(
    path: Path,
    selected: set[str],
    private_map: PrivateNormalizationMap | None = None,
) -> ParsedGraph:
    selected_declarations: dict[str, Declaration] = {}
    all_names: set[str] = set()
    normalized_names: set[str] = set()
    all_edges: set[Edge] = set()
    incident_edges: set[Edge] = set()
    saw_format = False
    saw_edge = False
    saw_any = False
    declaration_count = 0
    edge_count = 0
    for line_number, row in rows(path):
        context = f"{path}:{line_number}"
        if not row:
            raise InputError(f"{context}: blank rows are not allowed")
        saw_any = True
        if tuple(row) == FORMAT_ROW:
            if saw_format or line_number != 1:
                raise InputError(f"{context}: duplicate or misplaced format row")
            saw_format = True
            continue
        if not saw_format:
            raise InputError(f"{context}: stream must begin with 'format\\t2'")
        if row[0] == "declaration" and len(row) == 5:
            if saw_edge:
                raise InputError(f"{context}: declaration appears after an edge")
            declaration = Declaration(*row[1:])
            if not all((declaration.name, declaration.module, declaration.kind, declaration.visibility)):
                raise InputError(f"{context}: declaration fields must be nonempty")
            validate_module(declaration.module, context)
            if declaration.visibility not in VISIBILITIES:
                raise InputError(
                    f"{context}: visibility must be one of {sorted(VISIBILITIES)}"
                )
            if declaration.name in all_names:
                raise InputError(f"{context}: duplicate declaration {declaration.name}")
            all_names.add(declaration.name)
            normalization = (
                private_map.by_new.get(declaration.name)
                if private_map is not None
                else None
            )
            normalized_name = (
                normalization.old_private if normalization is not None else declaration.name
            )
            if normalized_name in normalized_names:
                raise InputError(
                    f"{context}: declarations collide after private normalization at "
                    f"{normalized_name!r}"
                )
            normalized_names.add(normalized_name)
            declaration_count += 1
            if normalized_name in selected:
                if (
                    private_map is None
                    or normalized_name not in private_map.by_old
                    or normalization is not None
                ):
                    selected_declarations[normalized_name] = Declaration(
                        normalized_name,
                        declaration.module,
                        declaration.kind,
                        declaration.visibility,
                    )
            continue
        if row[0] == "edge" and len(row) == 4:
            saw_edge = True
            kind, source, target = row[1:]
            if kind not in EDGE_KINDS or not source or not target:
                raise InputError(f"{context}: malformed typed edge")
            if source not in all_names or target not in all_names:
                raise InputError(
                    f"{context}: edge references an unknown or not-yet-declared endpoint: "
                    f"{source} -> {target}"
                )
            normalized_source = source
            normalized_target = target
            if private_map is not None:
                source_entry = private_map.by_new.get(source)
                target_entry = private_map.by_new.get(target)
                if source_entry is not None:
                    normalized_source = source_entry.old_private
                if target_entry is not None:
                    normalized_target = target_entry.old_private
            edge = Edge(kind, normalized_source, normalized_target)
            if edge in all_edges:
                raise InputError(
                    f"{context}: duplicate {kind} edge after private normalization: "
                    f"{normalized_source} -> {normalized_target}"
                )
            all_edges.add(edge)
            edge_count += 1
            if normalized_source in selected or normalized_target in selected:
                incident_edges.add(edge)
            continue
        raise InputError(f"{context}: malformed format-2 row {row!r}")
    if not saw_any or not saw_format:
        raise InputError(f"{path}: missing 'format\\t2' row")
    return ParsedGraph(
        declarations=selected_declarations,
        incident_edges=incident_edges,
        declaration_count=declaration_count,
        edge_count=edge_count,
    )


def normalize_allowed_owners(
    exact_modules: Iterable[str], prefixes: Iterable[str]
) -> AllowedOwners:
    exact = list(exact_modules)
    prefix_list = list(prefixes)
    if len(exact) != len(set(exact)):
        raise InputError("duplicate --allow-module value")
    if len(prefix_list) != len(set(prefix_list)):
        raise InputError("duplicate --allow-prefix value")
    for module in exact:
        validate_module(module, "--allow-module")
    for prefix in prefix_list:
        if not prefix.endswith("."):
            raise InputError(
                f"--allow-prefix {prefix!r} must end with '.' to make the namespace boundary explicit"
            )
        validate_module(prefix[:-1], "--allow-prefix")
    if not exact and not prefix_list:
        raise InputError("at least one --allow-module or --allow-prefix is required")
    return AllowedOwners(tuple(sorted(exact)), tuple(sorted(prefix_list)))


def compare_graphs(
    projection: ParsedGraph,
    candidate: ParsedGraph,
    allowed: AllowedOwners,
    private_map: PrivateNormalizationMap | None = None,
) -> Comparison:
    errors: list[str] = []
    relocated = 0
    for name, baseline in sorted(projection.declarations.items()):
        current = candidate.declarations.get(name)
        if current is None:
            errors.append(f"missing declaration: {name}")
            continue
        if current.kind != baseline.kind:
            errors.append(
                f"kind drift: {name}: baseline {baseline.kind!r}, candidate {current.kind!r}"
            )
        if current.visibility != baseline.visibility:
            errors.append(
                f"visibility drift: {name}: baseline {baseline.visibility!r}, "
                f"candidate {current.visibility!r}"
            )
        if not allowed.contains(current.module):
            errors.append(
                f"owner not allowed: {name}: baseline {baseline.module}, candidate {current.module}"
            )
        if private_map is not None and name in private_map.by_old:
            expected_owner = private_map.by_old[name].destination_module
            if current.module != expected_owner:
                errors.append(
                    f"private normalization owner mismatch: {name}: "
                    f"map {expected_owner}, candidate {current.module}"
                )
        if current.module != baseline.module:
            relocated += 1

    missing_edges = projection.incident_edges - candidate.incident_edges
    extra_edges = candidate.incident_edges - projection.incident_edges
    for edge in sorted(missing_edges):
        errors.append(
            f"missing {edge.kind} edge: {edge.source} -> {edge.target}"
        )
    for edge in sorted(extra_edges):
        errors.append(
            f"unexpected {edge.kind} edge: {edge.source} -> {edge.target}"
        )
    return Comparison(
        errors=sorted(errors),
        relocated=relocated,
        signature_edges=sum(edge.kind == "signature" for edge in projection.incident_edges),
        body_edges=sum(edge.kind == "body" for edge in projection.incident_edges),
        private_normalizations=0 if private_map is None else len(private_map.by_old),
        private_map_sha256=None if private_map is None else private_map.sha256,
    )


def check_expected_hash(path: Path, expected: str | None, label: str) -> str:
    actual = sha256_path(path)
    if expected is not None and actual != expected.upper():
        raise InputError(
            f"{label} SHA-256 mismatch for {path}: expected {expected.upper()}, actual {actual}"
        )
    return actual


def check(
    projection_path: Path,
    projection_sha256: str,
    candidate_path: Path,
    candidate_sha256: str | None,
    allowed: AllowedOwners,
    private_map_path: Path | None = None,
    private_map_sha256: str | None = None,
) -> tuple[Comparison, str, str, ParsedGraph, ParsedGraph]:
    projection_digest = check_expected_hash(
        projection_path, projection_sha256, "projection"
    )
    candidate_digest = check_expected_hash(
        candidate_path, candidate_sha256, "candidate"
    )
    projection = parse_projection(projection_path)
    private_map = None
    if private_map_path is None and private_map_sha256 is not None:
        raise InputError("--private-map is required with --private-map-sha256")
    if private_map_path is not None:
        if private_map_sha256 is None:
            raise InputError("--private-map-sha256 is required with --private-map")
        private_map_digest = check_expected_hash(
            private_map_path, private_map_sha256, "private map"
        )
        private_map = parse_private_normalization_map(
            private_map_path, projection, private_map_digest
        )
    candidate = parse_candidate(
        candidate_path, set(projection.declarations), private_map
    )
    comparison = compare_graphs(projection, candidate, allowed, private_map)
    return comparison, projection_digest, candidate_digest, projection, candidate


def write_deterministic_gzip(path: Path, payload: bytes) -> None:
    with path.open("wb") as raw:
        with gzip.GzipFile(
            filename="",
            mode="wb",
            fileobj=raw,
            compresslevel=9,
            mtime=0,
        ) as stream:
            stream.write(payload)


def projection_fixture() -> bytes:
    return (
        "format\t2\n"
        "declaration\tDemo.alpha\tLegacy.Owner\tdefinition\tpublic\n"
        "declaration\tDemo.beta\tLegacy.Owner\ttheorem\tprivate\n"
        "edge\tsignature\tDemo.alpha\tExternal.gamma\n"
        "edge\tbody\tDemo.alpha\tDemo.beta\n"
        "edge\tbody\tExternal.gamma\tDemo.beta\n"
    ).encode("utf-8")


def candidate_fixture(
    *,
    extra_edge: bool = False,
    bad_owner: bool = False,
    private_name: str = "Demo.beta",
    private_owner: str | None = None,
) -> bytes:
    owner = private_owner or (
        "Forbidden.Owner" if bad_owner else "Canonical.Family.Detail"
    )
    rows = [
        "format\t2",
        "declaration\tDemo.alpha\tCanonical.Exact\tdefinition\tpublic",
        f"declaration\t{private_name}\t{owner}\ttheorem\tprivate",
        "declaration\tExternal.gamma\tExternal.Library\ttheorem\tinternal",
        "edge\tsignature\tDemo.alpha\tExternal.gamma",
        f"edge\tbody\tDemo.alpha\t{private_name}",
        f"edge\tbody\tExternal.gamma\t{private_name}",
    ]
    if extra_edge:
        rows.insert(-1, f"edge\tbody\t{private_name}\tExternal.gamma")
    return ("\n".join(rows) + "\n").encode("utf-8")


def private_map_fixture(
    *,
    destination: str = "Canonical.Family.Detail",
    old_private: str = "Demo.beta",
    new_private: str = "Demo.betaNormalized",
) -> bytes:
    return (
        "old_private\tnew_private\tdestination_module\n"
        f"{old_private}\t{new_private}\t{destination}\n"
    ).encode("utf-8")


def run_self_test() -> int:
    try:
        with tempfile.TemporaryDirectory(prefix="numstability-projection-selftest-") as temporary:
            root = Path(temporary)
            projection_plain = root / "projection.tsv"
            projection_gzip = root / "projection.tsv.gz"
            candidate = root / "candidate.tsv"
            projection_plain.write_bytes(projection_fixture())
            write_deterministic_gzip(projection_gzip, projection_fixture())
            candidate.write_bytes(candidate_fixture())
            allowed = normalize_allowed_owners(
                ["Canonical.Exact"], ["Canonical.Family."]
            )
            for projection_path in (projection_plain, projection_gzip):
                comparison, *_rest = check(
                    projection_path,
                    sha256_path(projection_path),
                    candidate,
                    None,
                    allowed,
                )
                if comparison.errors:
                    raise AssertionError(
                        f"valid {projection_path.name} fixture was rejected: "
                        + "; ".join(comparison.errors)
                    )

            private_map_path = root / "private-map.tsv"
            private_map_path.write_bytes(private_map_fixture())
            candidate.write_bytes(
                candidate_fixture(private_name="Demo.betaNormalized")
            )
            normalized, *_rest = check(
                projection_plain,
                sha256_path(projection_plain),
                candidate,
                None,
                allowed,
                private_map_path,
                sha256_path(private_map_path),
            )
            if normalized.errors:
                raise AssertionError(
                    "valid private normalization was rejected: "
                    + "; ".join(normalized.errors)
                )
            if normalized.private_normalizations != 1:
                raise AssertionError("private normalization count was not reported")

            candidate.write_bytes(
                candidate_fixture(
                    private_name="Demo.betaNormalized",
                    private_owner="Canonical.Exact",
                )
            )
            private_owner_mismatch, *_rest = check(
                projection_plain,
                sha256_path(projection_plain),
                candidate,
                None,
                allowed,
                private_map_path,
                sha256_path(private_map_path),
            )
            if not any(
                "private normalization owner mismatch" in error
                for error in private_owner_mismatch.errors
            ):
                raise AssertionError("private map destination owner drift was not rejected")

            candidate.write_bytes(candidate_fixture())
            unnormalized, *_rest = check(
                projection_plain,
                sha256_path(projection_plain),
                candidate,
                None,
                allowed,
                private_map_path,
                sha256_path(private_map_path),
            )
            if not any("missing declaration: Demo.beta" in error for error in unnormalized.errors):
                raise AssertionError("an unnormalized private candidate name was accepted")

            try:
                check(
                    projection_plain,
                    sha256_path(projection_plain),
                    candidate,
                    None,
                    allowed,
                    private_map_path,
                    "0" * 64,
                )
            except InputError as error:
                if "private map SHA-256 mismatch" not in str(error):
                    raise AssertionError(
                        f"private map hash rejection had an unexpected diagnostic: {error}"
                    ) from error
            else:
                raise AssertionError("a bad private map hash was accepted")

            private_map_path.write_bytes(
                private_map_fixture(old_private="Demo.alpha")
            )
            try:
                check(
                    projection_plain,
                    sha256_path(projection_plain),
                    candidate,
                    None,
                    allowed,
                    private_map_path,
                    sha256_path(private_map_path),
                )
            except InputError as error:
                if "domain must equal every selected private declaration" not in str(error):
                    raise AssertionError(
                        f"private map domain rejection had an unexpected diagnostic: {error}"
                    ) from error
            else:
                raise AssertionError("a private map containing a public declaration was accepted")

            private_map_path.write_bytes(
                (
                    "old_private\tnew_private\tdestination_module\n"
                    "Demo.beta\tDemo.same\tCanonical.Family.Detail\n"
                    "Demo.alpha\tDemo.same\tCanonical.Exact\n"
                ).encode("utf-8")
            )
            try:
                parse_private_normalization_map(
                    private_map_path,
                    parse_projection(projection_plain),
                    sha256_path(private_map_path),
                )
            except InputError as error:
                if "non-injective new_private" not in str(error):
                    raise AssertionError(
                        f"private map injectivity rejection had an unexpected diagnostic: {error}"
                    ) from error
            else:
                raise AssertionError("a non-injective private map was accepted")

            candidate.write_bytes(candidate_fixture(extra_edge=True))
            mismatch, *_rest = check(
                projection_plain,
                sha256_path(projection_plain),
                candidate,
                None,
                allowed,
            )
            if not any("unexpected body edge" in error for error in mismatch.errors):
                raise AssertionError("extra incident edge was not rejected")

            candidate.write_bytes(candidate_fixture(bad_owner=True))
            owner_mismatch, *_rest = check(
                projection_plain,
                sha256_path(projection_plain),
                candidate,
                None,
                allowed,
            )
            if not any("owner not allowed" in error for error in owner_mismatch.errors):
                raise AssertionError("unapproved owner was not rejected")

            duplicate = candidate_fixture() + b"edge\tbody\tDemo.alpha\tDemo.beta\n"
            candidate.write_bytes(duplicate)
            try:
                parse_candidate(candidate, {"Demo.alpha", "Demo.beta"})
            except InputError as error:
                if "duplicate body edge" not in str(error):
                    raise AssertionError(
                        f"duplicate rejection had an unexpected diagnostic: {error}"
                    ) from error
            else:
                raise AssertionError("duplicate edge was not rejected")

            nondeterministic = bytearray(projection_gzip.read_bytes())
            nondeterministic[4:8] = (1).to_bytes(4, "little")
            projection_gzip.write_bytes(nondeterministic)
            try:
                parse_projection(projection_gzip)
            except InputError as error:
                if "timestamp" not in str(error):
                    raise AssertionError(
                        f"gzip rejection had an unexpected diagnostic: {error}"
                    ) from error
            else:
                raise AssertionError("nondeterministic gzip timestamp was not rejected")
    except (InputError, AssertionError, OSError) as error:
        print(f"projection checker self-test failed: {error}", file=sys.stderr)
        return 1
    print(
        "phase projection self-test passed: plain/gzip and private normalization "
        "matches accepted; edge, owner, map, duplicate, and deterministic-gzip "
        "violations rejected"
    )
    return 0


def sha256_argument(value: str) -> str:
    if not SHA256_RE.fullmatch(value):
        raise argparse.ArgumentTypeError("expected 64 hexadecimal SHA-256 characters")
    return value.upper()


def positive_integer(value: str) -> int:
    try:
        parsed = int(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError("expected a positive integer") from error
    if parsed <= 0:
        raise argparse.ArgumentTypeError("expected a positive integer")
    return parsed


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--projection",
        type=Path,
        help="frozen format-2 projection TSV or deterministic gzip",
    )
    parser.add_argument(
        "--projection-sha256",
        type=sha256_argument,
        help="required SHA-256 of the exact frozen projection file bytes",
    )
    parser.add_argument(
        "--candidate",
        type=Path,
        help="candidate full format-2 declaration dependency TSV or deterministic gzip",
    )
    parser.add_argument(
        "--candidate-sha256",
        type=sha256_argument,
        help="optional SHA-256 of the exact candidate file bytes",
    )
    parser.add_argument(
        "--private-map",
        type=Path,
        help=(
            "optional exact-header TSV mapping every selected private declaration "
            "to its candidate name and destination owner"
        ),
    )
    parser.add_argument(
        "--private-map-sha256",
        type=sha256_argument,
        help="required SHA-256 of --private-map when private normalization is used",
    )
    parser.add_argument(
        "--allow-module",
        action="append",
        default=[],
        metavar="MODULE",
        help="allow an exact candidate owner module; repeat as needed",
    )
    parser.add_argument(
        "--allow-prefix",
        action="append",
        default=[],
        metavar="PREFIX.",
        help="allow candidate owner descendants below an explicit dot-terminated namespace prefix",
    )
    parser.add_argument(
        "--max-errors",
        type=positive_integer,
        default=50,
        help="maximum sorted semantic mismatch diagnostics to print (default: 50)",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="run isolated positive and negative parser/comparison tests",
    )
    args = parser.parse_args(argv)
    if (args.private_map is None) != (args.private_map_sha256 is None):
        parser.error("--private-map and --private-map-sha256 must be supplied together")
    if not args.self_test:
        missing = [
            flag
            for flag, value in (
                ("--projection", args.projection),
                ("--projection-sha256", args.projection_sha256),
                ("--candidate", args.candidate),
            )
            if value is None
        ]
        if missing:
            parser.error("the following arguments are required unless --self-test is used: " + ", ".join(missing))
    return args


def print_success(
    comparison: Comparison,
    projection_digest: str,
    candidate_digest: str,
    projection: ParsedGraph,
    candidate: ParsedGraph,
    allowed: AllowedOwners,
) -> None:
    print("phase projection contract passed")
    print(f"projection_sha256: {projection_digest}")
    print(f"candidate_sha256: {candidate_digest}")
    print(f"selected_declarations: {projection.declaration_count}")
    print(f"relocated_declarations: {comparison.relocated}")
    print(f"signature_edges: {comparison.signature_edges}")
    print(f"body_edges: {comparison.body_edges}")
    print(f"candidate_declarations_scanned: {candidate.declaration_count}")
    print(f"candidate_edges_scanned: {candidate.edge_count}")
    print(f"allowed_exact_modules: {len(allowed.exact_modules)}")
    print(f"allowed_prefixes: {len(allowed.prefixes)}")
    if comparison.private_map_sha256 is not None:
        print(f"private_map_sha256: {comparison.private_map_sha256}")
        print(f"private_normalizations: {comparison.private_normalizations}")


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    if args.self_test:
        return run_self_test()
    try:
        allowed = normalize_allowed_owners(args.allow_module, args.allow_prefix)
        comparison, projection_digest, candidate_digest, projection, candidate = check(
            args.projection,
            args.projection_sha256,
            args.candidate,
            args.candidate_sha256,
            allowed,
            args.private_map,
            args.private_map_sha256,
        )
    except InputError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    if comparison.errors:
        visible = comparison.errors[: args.max_errors]
        for error in visible:
            print(f"error: {error}", file=sys.stderr)
        remaining = len(comparison.errors) - len(visible)
        if remaining:
            print(f"error: ... {remaining} additional mismatch(es) omitted", file=sys.stderr)
        print(
            f"projection comparison failed: {len(comparison.errors)} mismatch(es), "
            f"{projection.declaration_count} selected declaration(s), "
            f"{len(projection.incident_edges)} incident edge(s)",
            file=sys.stderr,
        )
        return 1
    print_success(
        comparison,
        projection_digest,
        candidate_digest,
        projection,
        candidate,
        allowed,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
