#!/usr/bin/env python3
"""Compare a frozen format-2 declaration projection with a candidate graph.

Every declaration row in the frozen projection selects one declaration.  The
projection's edge rows are its complete typed incident graph: each edge must
have at least one selected endpoint, while its other endpoint may be outside
the projection.  The candidate must preserve selected declaration names,
kinds, visibility, and the exact signature/body incident edge sets.  Only the
owning module may change, and every candidate owner must match an exact module
or namespace prefix declared on the command line.

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


def parse_candidate(path: Path, selected: set[str]) -> ParsedGraph:
    selected_declarations: dict[str, Declaration] = {}
    all_names: set[str] = set()
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
            declaration_count += 1
            if declaration.name in selected:
                selected_declarations[declaration.name] = declaration
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
            edge = Edge(kind, source, target)
            if edge in all_edges:
                raise InputError(
                    f"{context}: duplicate {kind} edge {source} -> {target}"
                )
            all_edges.add(edge)
            edge_count += 1
            if source in selected or target in selected:
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
) -> tuple[Comparison, str, str, ParsedGraph, ParsedGraph]:
    projection_digest = check_expected_hash(
        projection_path, projection_sha256, "projection"
    )
    candidate_digest = check_expected_hash(
        candidate_path, candidate_sha256, "candidate"
    )
    projection = parse_projection(projection_path)
    candidate = parse_candidate(candidate_path, set(projection.declarations))
    comparison = compare_graphs(projection, candidate, allowed)
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


def candidate_fixture(*, extra_edge: bool = False, bad_owner: bool = False) -> bytes:
    owner = "Forbidden.Owner" if bad_owner else "Canonical.Family.Detail"
    rows = [
        "format\t2",
        "declaration\tDemo.alpha\tCanonical.Exact\tdefinition\tpublic",
        f"declaration\tDemo.beta\t{owner}\ttheorem\tprivate",
        "declaration\tExternal.gamma\tExternal.Library\ttheorem\tinternal",
        "edge\tsignature\tDemo.alpha\tExternal.gamma",
        "edge\tbody\tDemo.alpha\tDemo.beta",
        "edge\tbody\tExternal.gamma\tDemo.beta",
    ]
    if extra_edge:
        rows.insert(-1, "edge\tbody\tDemo.beta\tExternal.gamma")
    return ("\n".join(rows) + "\n").encode("utf-8")


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
        "phase projection self-test passed: plain/gzip matches accepted; edge drift, "
        "owner drift, duplicates, and nondeterministic gzip rejected"
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
