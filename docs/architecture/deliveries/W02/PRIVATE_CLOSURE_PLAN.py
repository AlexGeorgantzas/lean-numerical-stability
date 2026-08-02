#!/usr/bin/env python3
"""Compute W02's command-granular private-declaration retention plan.

This planner is deliberately read-only except for its TSV output.  It reads
the frozen owner sources from Git, command spans from baseline ``.ilean``
files, and declarations/edges from the exact P0002 projection.  A command is
retained in its historical owner when it declares a genuine Lean private name
or (transitively) depends on any retained command.  Every other command is a
move candidate.

The output is a plan, not a Lean source rewriter.  Reconstruction should copy
whole command spans according to ``decision`` while separately preserving the
owner's imports, namespace/section scaffolding, options, comments, and trivia.
After reconstruction, rerun P0002 and the normal W02 build/static gates.

Typical use from the repository root::

    python docs/architecture/deliveries/W02/PRIVATE_CLOSURE_PLAN.py

If the checked-out historical base predates the committed P0002 contract,
point at the integrator's exact hash-pinned artifact::

    python docs/architecture/deliveries/W02/PRIVATE_CLOSURE_PLAN.py \
      --projection C:/path/to/P0002.tsv.gz

The ``.ilean`` files must have been built from the frozen W02 base.  Use
``--ilean-root`` to select a baseline cache when the working tree has since
been reorganized.
"""

from __future__ import annotations

import argparse
import csv
import gzip
import hashlib
import heapq
import io
import json
import re
import subprocess
import sys
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path


FROZEN_BASE = "e6ef0107edb873f7a05ad8282df7efdf41a986d3"
P0002_SHA256 = "EA781015CD00CDC9EC152D71BE9D6F2993148294E8B3EBEF28B56E81C9C002DB"
EXPECTED_DECLARATIONS = 4_195
EXPECTED_SIGNATURE_EDGES = 18_256
EXPECTED_BODY_EDGES = 30_343
EXPECTED_PHYSICAL_DECLARATIONS = 2_478
EXPECTED_ILEAN_COMMANDS = 2_265
EXPECTED_SOURCE_ALIAS_COMMANDS = 3
EXPECTED_PRIVATE_SEEDS = 125
EXPECTED_RETAINED_COMMANDS = 258

PHYSICAL_OWNERS = (
    "NumStability.Algorithms.HighamChapter8",
    "NumStability.Algorithms.HighamChapter8FanInClosure",
    "NumStability.Algorithms.IterativeRefinement",
    "NumStability.Algorithms.LU.Doolittle",
    "NumStability.Algorithms.NeumaierCompensatedFiniteFormat",
    "NumStability.Algorithms.PriestFiniteFormat",
    "NumStability.Algorithms.TriangularArbitraryOrder",
    "NumStability.Algorithms.TriangularNoGuard",
    "NumStability.Analysis.CramersRule",
    "NumStability.Analysis.DoubleRounding",
    "NumStability.Analysis.Error",
    "NumStability.Analysis.FusedMultiplyAdd",
    "NumStability.Analysis.HighamChapter7",
    "NumStability.Analysis.HighamChapter7Rectangular",
    "NumStability.Analysis.Midpoint",
    "NumStability.Analysis.ProblemDependentStability",
    "NumStability.Analysis.RoundingProductBounds",
    "NumStability.Analysis.SampleVariance",
    "NumStability.Analysis.TrigCancellation",
)


class PlanError(RuntimeError):
    """Raised when an input is not the frozen W02 planning input."""


@dataclass(frozen=True)
class Declaration:
    name: str
    module: str
    kind: str
    visibility: str


@dataclass(frozen=True)
class Edge:
    kind: str
    source: str
    target: str


@dataclass
class Command:
    owner: str
    root: str
    span_origin: str
    start_line: int
    start_column: int
    end_line: int
    end_column: int
    start_offset: int
    end_offset: int
    declarations: list[str] = field(default_factory=list)

    @property
    def key(self) -> tuple[str, str]:
        return (self.owner, self.root)


@dataclass(frozen=True)
class OwnerEvidence:
    module: str
    source_path: str
    source_blob_sha1: str
    source_sha256: str
    ilean_path: str
    ilean_sha256: str


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


def run_git(repo: Path, *arguments: str, binary: bool = False) -> str | bytes:
    result = subprocess.run(
        ["git", "-C", str(repo), *arguments],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if result.returncode:
        detail = result.stderr.decode("utf-8", errors="replace").strip()
        raise PlanError(f"git {' '.join(arguments)} failed: {detail}")
    if binary:
        return result.stdout
    return result.stdout.decode("utf-8", errors="strict").strip()


def module_path(module: str, suffix: str) -> Path:
    return Path(*module.split(".")).with_suffix(suffix)


def read_projection(path: Path) -> tuple[dict[str, Declaration], tuple[Edge, ...]]:
    if not path.is_file():
        raise PlanError(
            f"P0002 was not found at {path}; pass --projection with the exact "
            "hash-pinned P0002.tsv.gz"
        )
    payload = path.read_bytes()
    digest = sha256_bytes(payload)
    if digest != P0002_SHA256:
        raise PlanError(
            f"P0002 SHA-256 differs: expected {P0002_SHA256}, found {digest}"
        )

    opener = gzip.open if path.suffix == ".gz" else open
    declarations: dict[str, Declaration] = {}
    edges: set[Edge] = set()
    saw_format = False
    with opener(path, "rt", encoding="utf-8", newline="") as stream:
        for line_number, row in enumerate(csv.reader(stream, delimiter="\t"), 1):
            if not row:
                continue
            if row == ["format", "2"]:
                if saw_format or line_number != 1:
                    raise PlanError(f"{path}:{line_number}: misplaced format row")
                saw_format = True
            elif len(row) == 5 and row[0] == "declaration":
                if not saw_format or not all(row[1:]):
                    raise PlanError(f"{path}:{line_number}: malformed declaration")
                declaration = Declaration(*row[1:])
                if declaration.name in declarations:
                    raise PlanError(
                        f"{path}:{line_number}: duplicate declaration {declaration.name}"
                    )
                if declaration.visibility not in {"public", "private", "internal"}:
                    raise PlanError(
                        f"{path}:{line_number}: invalid visibility "
                        f"{declaration.visibility!r}"
                    )
                declarations[declaration.name] = declaration
            elif len(row) == 4 and row[0] == "edge":
                if not saw_format or row[1] not in {"signature", "body"}:
                    raise PlanError(f"{path}:{line_number}: malformed edge")
                edge = Edge(*row[1:])
                if edge in edges:
                    raise PlanError(
                        f"{path}:{line_number}: duplicate {edge.kind} edge "
                        f"{edge.source} -> {edge.target}"
                    )
                edges.add(edge)
            else:
                raise PlanError(f"{path}:{line_number}: malformed format-2 row")

    if not saw_format:
        raise PlanError(f"{path}: missing format\t2")
    if len(declarations) != EXPECTED_DECLARATIONS:
        raise PlanError(
            f"expected {EXPECTED_DECLARATIONS} P0002 declarations, "
            f"found {len(declarations)}"
        )
    signature_count = sum(edge.kind == "signature" for edge in edges)
    body_count = sum(edge.kind == "body" for edge in edges)
    if signature_count != EXPECTED_SIGNATURE_EDGES:
        raise PlanError(
            f"expected {EXPECTED_SIGNATURE_EDGES} signature edges, "
            f"found {signature_count}"
        )
    if body_count != EXPECTED_BODY_EDGES:
        raise PlanError(
            f"expected {EXPECTED_BODY_EDGES} body edges, found {body_count}"
        )
    return declarations, tuple(sorted(edges, key=lambda edge: (
        edge.kind, edge.source, edge.target
    )))


def source_offsets(source: str) -> tuple[list[str], list[int]]:
    lines = source.splitlines(keepends=True)
    starts: list[int] = []
    offset = 0
    for line in lines:
        starts.append(offset)
        offset += len(line)
    if offset != len(source):
        raise PlanError("source line accounting failed")
    return lines, starts


def coordinate_offset(
    lines: list[str], starts: list[int], line: int, column: int
) -> int:
    if line < 0 or line >= len(lines) or column < 0:
        raise PlanError(f"invalid source coordinate {line}:{column}")
    physical = lines[line]
    content = physical[:-1] if physical.endswith("\n") else physical
    if content.endswith("\r"):
        content = content[:-1]
    # Version-5 .ilean coordinates use the same UTF-16 code-unit columns as
    # Lean's editor/LSP ranges.  Astral mathematical symbols therefore occupy
    # two columns even though Python represents them as one code point.
    units = 0
    for index, character in enumerate(content):
        if units == column:
            return starts[line] + index
        units += 2 if ord(character) > 0xFFFF else 1
        if units > column:
            raise PlanError(f"source coordinate {line}:{column} splits a surrogate pair")
    if units == column:
        return starts[line] + len(content)
    raise PlanError(
        f"source coordinate {line}:{column} exceeds UTF-16 line length {units}"
    )


def utf16_length(text: str) -> int:
    return sum(2 if ord(character) > 0xFFFF else 1 for character in text)


def real_private_name(name: str, owner: str) -> bool:
    return re.fullmatch(
        rf"_private\.{re.escape(owner)}\.\d+\..+", name
    ) is not None


def read_base_source(repo: Path, base: str, source_path: str) -> tuple[bytes, str, str]:
    blob = str(run_git(repo, "rev-parse", f"{base}:{source_path}"))
    payload = run_git(repo, "cat-file", "blob", blob, binary=True)
    assert isinstance(payload, bytes)
    try:
        source = payload.decode("utf-8")
    except UnicodeDecodeError as error:
        raise PlanError(f"{source_path}: frozen source is not UTF-8") from error
    if "\r" in source:
        raise PlanError(f"{source_path}: frozen source unexpectedly contains CR")
    return payload, source, blob


def read_ilean(path: Path, owner: str) -> tuple[dict[str, object], str]:
    if not path.is_file():
        raise PlanError(
            f"missing baseline .ilean for {owner}: {path}; build the frozen base "
            "or pass --ilean-root"
        )
    payload = path.read_bytes()
    try:
        parsed = json.loads(payload.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise PlanError(f"{path}: invalid .ilean JSON") from error
    if not isinstance(parsed, dict) or parsed.get("version") != 5:
        raise PlanError(f"{path}: expected .ilean JSON version 5")
    if parsed.get("module") != owner:
        raise PlanError(
            f"{path}: owner is {parsed.get('module')!r}, expected {owner!r}"
        )
    if not isinstance(parsed.get("decls"), dict):
        raise PlanError(f"{path}: missing declaration-command map")
    return parsed, sha256_bytes(payload)


def commands_from_ilean(
    owner: str, ilean: dict[str, object], source: str
) -> dict[tuple[str, str], Command]:
    raw_declarations = ilean["decls"]
    assert isinstance(raw_declarations, dict)
    lines, starts = source_offsets(source)
    commands: dict[tuple[str, str], Command] = {}
    for root, raw_span in raw_declarations.items():
        if not isinstance(root, str) or not isinstance(raw_span, list):
            raise PlanError(f"{owner}: malformed .ilean declaration span")
        if len(raw_span) != 8 or any(not isinstance(value, int) for value in raw_span):
            raise PlanError(f"{owner}:{root}: expected an eight-integer span")
        start_line, start_column, end_line, end_column = raw_span[:4]
        if start_column != 0:
            raise PlanError(f"{owner}:{root}: command does not begin in column zero")
        start = coordinate_offset(lines, starts, start_line, start_column)
        end = coordinate_offset(lines, starts, end_line, end_column)
        if end <= start:
            raise PlanError(f"{owner}:{root}: empty or reversed source span")
        physical_end = lines[end_line]
        if physical_end.endswith("\n"):
            physical_end = physical_end[:-1]
        end_line_offset = coordinate_offset(lines, starts, end_line, end_column)
        end_index = end_line_offset - starts[end_line]
        if physical_end[end_index:].strip():
            raise PlanError(f"{owner}:{root}: nonblank text follows recorded end")
        command = Command(
            owner=owner,
            root=root,
            span_origin="ilean",
            start_line=start_line,
            start_column=start_column,
            end_line=end_line,
            end_column=end_column,
            start_offset=start,
            end_offset=end,
        )
        commands[command.key] = command

    ordered = sorted(commands.values(), key=lambda command: (
        command.start_offset, command.end_offset, command.root
    ))
    for previous, current in zip(ordered, ordered[1:]):
        if current.start_offset < previous.end_offset:
            raise PlanError(
                f"{owner}: overlapping commands {previous.root} and {current.root}"
            )
    return commands


def find_source_alias_command(owner: str, actual_name: str, source: str) -> Command | None:
    """Return a validated span for a simple alias omitted from `.ilean.decls`."""

    leaf = actual_name.rsplit(".", 1)[-1]
    pattern = re.compile(rf"^alias[ \t]+{re.escape(leaf)}[ \t]*:=")
    lines, starts = source_offsets(source)
    matches = [index for index, line in enumerate(lines) if pattern.match(line.rstrip("\n"))]
    if not matches:
        return None
    if len(matches) != 1:
        raise PlanError(f"{owner}:{actual_name}: ambiguous source alias")
    start_line = matches[0]
    first = lines[start_line].rstrip("\n")
    rhs = first.split(":=", 1)[1].strip()
    end_line = start_line
    if not rhs:
        cursor = start_line + 1
        while cursor < len(lines) and not lines[cursor].strip():
            cursor += 1
        if cursor >= len(lines) or not lines[cursor][:1].isspace():
            raise PlanError(f"{owner}:{actual_name}: alias lacks an indented RHS")
        end_line = cursor
        next_nonblank = cursor + 1
        while next_nonblank < len(lines) and not lines[next_nonblank].strip():
            next_nonblank += 1
        if next_nonblank < len(lines) and lines[next_nonblank][:1].isspace():
            raise PlanError(
                f"{owner}:{actual_name}: multiline alias needs an explicit parser"
            )
    end_content = lines[end_line].rstrip("\n")
    end_column = utf16_length(end_content)
    return Command(
        owner=owner,
        root=actual_name,
        span_origin="source_alias",
        start_line=start_line,
        start_column=0,
        end_line=end_line,
        end_column=end_column,
        start_offset=starts[start_line],
        end_offset=starts[end_line] + len(end_content),
    )


def command_text(command: Command, sources: dict[str, str]) -> str:
    return sources[command.owner][command.start_offset:command.end_offset]


def build_command_map(
    declarations: dict[str, Declaration],
    edges: tuple[Edge, ...],
    commands: dict[tuple[str, str], Command],
    sources: dict[str, str],
) -> dict[str, tuple[str, str]]:
    roots: dict[str, list[str]] = defaultdict(list)
    for owner, root in commands:
        roots[owner].append(root)
    for owner in roots:
        roots[owner].sort(key=lambda root: (-len(root), root))

    physical = {
        name: declaration
        for name, declaration in declarations.items()
        if declaration.module in PHYSICAL_OWNERS
    }
    if len(physical) != EXPECTED_PHYSICAL_DECLARATIONS:
        raise PlanError(
            f"expected {EXPECTED_PHYSICAL_DECLARATIONS} physical-owner declarations, "
            f"found {len(physical)}"
        )

    mapped: dict[str, tuple[str, str]] = {}
    unmapped: list[str] = []
    for name, declaration in sorted(physical.items()):
        candidates = [
            root
            for root in roots[declaration.module]
            if name == root or name.startswith(root + ".")
        ]
        if candidates:
            longest = len(candidates[0])
            winners = [root for root in candidates if len(root) == longest]
            if len(winners) != 1:
                raise PlanError(f"{name}: ambiguous longest command roots {winners}")
            mapped[name] = (declaration.module, winners[0])
        else:
            unmapped.append(name)

    # Lean's .ilean declaration map omits alias commands.  Recover only simple,
    # source-visible aliases and record that their span did not come from .ilean.
    still_unmapped: list[str] = []
    for name in unmapped:
        declaration = physical[name]
        alias = find_source_alias_command(
            declaration.module, name, sources[declaration.module]
        )
        if alias is None:
            still_unmapped.append(name)
            continue
        if alias.key in commands:
            raise PlanError(f"{name}: recovered alias collides with a command root")
        commands[alias.key] = alias
        roots[declaration.module].append(alias.root)
        roots[declaration.module].sort(key=lambda root: (-len(root), root))
        mapped[name] = alias.key

    for owner in PHYSICAL_OWNERS:
        ordered = sorted(
            (command for command in commands.values() if command.owner == owner),
            key=lambda command: (
                command.start_offset, command.end_offset, command.root
            ),
        )
        for previous, current in zip(ordered, ordered[1:]):
            if current.start_offset < previous.end_offset:
                raise PlanError(
                    f"{owner}: recovered source command {current.root} overlaps "
                    f"{previous.root}"
                )

    # The remaining omitted declarations are products of `deriving`.  Their
    # projection dependencies identify the unique source command containing
    # the relevant inductive declaration.  Requiring `deriving` in that exact
    # command prevents a dependency-only guess from becoming a silent mapping.
    outgoing: dict[str, set[str]] = defaultdict(set)
    for edge in edges:
        outgoing[edge.source].add(edge.target)
    unresolved: list[str] = []
    for name in still_unmapped:
        declaration = physical[name]
        dependency_commands = {
            mapped[target]
            for target in outgoing.get(name, set())
            if target in mapped and mapped[target][0] == declaration.module
        }
        deriving_commands = {
            key
            for key in dependency_commands
            if re.search(r"\bderiving\b", command_text(commands[key], sources))
        }
        named_commands = {
            key
            for key in deriving_commands
            if key[1].rsplit(".", 1)[-1] in name
        }
        candidates = named_commands or deriving_commands
        if len(candidates) != 1:
            unresolved.append(name)
            continue
        mapped[name] = next(iter(candidates))

    if unresolved:
        raise PlanError(
            "selected declarations without a validated source command: "
            + ", ".join(unresolved)
        )
    if len(mapped) != len(physical):
        raise PlanError("physical declaration-to-command mapping is incomplete")

    for name, key in mapped.items():
        commands[key].declarations.append(name)
    empty = sorted(command.root for command in commands.values() if not command.declarations)
    if empty:
        raise PlanError(
            ".ilean/source commands without selected P0002 declarations: "
            + ", ".join(empty[:20])
        )
    for command in commands.values():
        command.declarations.sort()
    return mapped


def compute_closure(
    declarations: dict[str, Declaration],
    edges: tuple[Edge, ...],
    commands: dict[tuple[str, str], Command],
    declaration_commands: dict[str, tuple[str, str]],
) -> tuple[
    dict[tuple[str, str], int],
    dict[tuple[str, str], tuple[str, str]],
    dict[tuple[tuple[str, str], tuple[str, str]], tuple[str, str, str]],
]:
    for name, key in declaration_commands.items():
        declaration = declarations[name]
        is_private = real_private_name(name, declaration.module)
        if is_private != (declaration.visibility == "private"):
            raise PlanError(
                f"{name}: actual private identity and projection visibility disagree"
            )

    seeds = {
        key
        for key, command in commands.items()
        if any(declarations[name].visibility == "private" for name in command.declarations)
    }
    if len(seeds) != EXPECTED_PRIVATE_SEEDS:
        raise PlanError(
            f"expected {EXPECTED_PRIVATE_SEEDS} private command seeds, found {len(seeds)}"
        )
    real_private_roots = {
        key
        for key, command in commands.items()
        if real_private_name(command.root, command.owner)
    }
    if seeds != real_private_roots:
        missing = sorted(real_private_roots - seeds)
        extra = sorted(seeds - real_private_roots)
        raise PlanError(
            "private declarations and genuine private command roots disagree: "
            f"missing={missing[:10]}, extra={extra[:10]}"
        )

    command_edges: dict[tuple[str, str], set[tuple[str, str]]] = defaultdict(set)
    witnesses: dict[
        tuple[tuple[str, str], tuple[str, str]], list[tuple[str, str, str]]
    ] = defaultdict(list)
    for edge in edges:
        source = declaration_commands.get(edge.source)
        target = declaration_commands.get(edge.target)
        if source is None or target is None or source == target:
            continue
        command_edges[source].add(target)
        witnesses[(source, target)].append((edge.kind, edge.source, edge.target))

    reverse_edges: dict[tuple[str, str], set[tuple[str, str]]] = defaultdict(set)
    for source, targets in command_edges.items():
        for target in targets:
            reverse_edges[target].add(source)

    depth = {seed: 0 for seed in seeds}
    queue = [(0, seed[0], seed[1]) for seed in seeds]
    heapq.heapify(queue)
    while queue:
        target_depth, owner, root = heapq.heappop(queue)
        target = (owner, root)
        if depth.get(target) != target_depth:
            continue
        for source in sorted(reverse_edges.get(target, set())):
            candidate = target_depth + 1
            if candidate < depth.get(source, sys.maxsize):
                depth[source] = candidate
                heapq.heappush(queue, (candidate, source[0], source[1]))

    retained = set(depth)
    if len(retained) != EXPECTED_RETAINED_COMMANDS:
        raise PlanError(
            f"expected {EXPECTED_RETAINED_COMMANDS} retained commands, "
            f"found {len(retained)}"
        )
    leaks = sorted(
        (source, target)
        for source, targets in command_edges.items()
        if source not in retained
        for target in targets
        if target in retained
    )
    if leaks:
        source, target = leaks[0]
        raise PlanError(
            f"closure incomplete: move command {source} depends on retained {target}"
        )

    chosen_target: dict[tuple[str, str], tuple[str, str]] = {}
    chosen_witness: dict[
        tuple[tuple[str, str], tuple[str, str]], tuple[str, str, str]
    ] = {}
    for source, source_depth in sorted(depth.items()):
        if source_depth == 0:
            continue
        candidates = sorted(
            target
            for target in command_edges.get(source, set())
            if depth.get(target) == source_depth - 1
        )
        if not candidates:
            raise PlanError(f"{source}: retained command lacks a closure predecessor")
        target = candidates[0]
        chosen_target[source] = target
        chosen_witness[(source, target)] = sorted(witnesses[(source, target)])[0]
    return depth, chosen_target, chosen_witness


def render_plan(
    base: str,
    declarations: dict[str, Declaration],
    commands: dict[tuple[str, str], Command],
    evidence: dict[str, OwnerEvidence],
    depth: dict[tuple[str, str], int],
    chosen_target: dict[tuple[str, str], tuple[str, str]],
    chosen_witness: dict[
        tuple[tuple[str, str], tuple[str, str]], tuple[str, str, str]
    ],
) -> str:
    output = io.StringIO(newline="")
    writer = csv.writer(output, delimiter="\t", lineterminator="\n")
    retained_count = len(depth)
    writer.writerow(["format", "1"])
    for key, value in (
        ("generated_by", "docs/architecture/deliveries/W02/PRIVATE_CLOSURE_PLAN.py"),
        ("base_revision", base),
        ("projection_id", "P0002"),
        ("projection_sha256", P0002_SHA256),
        ("owner_count", str(len(PHYSICAL_OWNERS))),
        ("command_count", str(len(commands))),
        ("private_seed_count", str(EXPECTED_PRIVATE_SEEDS)),
        ("retained_command_count", str(retained_count)),
        ("move_candidate_count", str(len(commands) - retained_count)),
        (
            "closure_scope",
            "P0002 command edges induced by the 19 physical W02 owners",
        ),
        (
            "coordinate_convention",
            "lines=1-based; columns=UTF-16-code-units-0-based; end=half-open",
        ),
    ):
        writer.writerow(["metadata", key, value])
    writer.writerow([
        "columns",
        "owner",
        "module",
        "source_path",
        "source_blob_sha1",
        "source_sha256",
        "ilean_path",
        "ilean_sha256",
        "command_count",
        "retained_command_count",
        "move_candidate_count",
        "private_seed_count",
    ])
    writer.writerow([
        "columns",
        "command",
        "owner_module",
        "command_root",
        "span_origin",
        "start_line",
        "start_column",
        "end_line",
        "end_column",
        "decision",
        "reason",
        "closure_depth",
        "witness_owner",
        "witness_root",
        "witness_edge_kind",
        "witness_source_declaration",
        "witness_target_declaration",
        "selected_declaration_count",
        "private_declaration_count",
        "selected_declarations_json",
    ])

    for owner in PHYSICAL_OWNERS:
        owner_commands = [command for command in commands.values() if command.owner == owner]
        retained = sum(command.key in depth for command in owner_commands)
        seeds = sum(depth.get(command.key) == 0 for command in owner_commands)
        item = evidence[owner]
        writer.writerow([
            "owner",
            owner,
            item.source_path,
            item.source_blob_sha1,
            item.source_sha256,
            item.ilean_path,
            item.ilean_sha256,
            str(len(owner_commands)),
            str(retained),
            str(len(owner_commands) - retained),
            str(seeds),
        ])

    for owner in PHYSICAL_OWNERS:
        owner_commands = sorted(
            (command for command in commands.values() if command.owner == owner),
            key=lambda command: (
                command.start_line,
                command.start_column,
                command.end_line,
                command.end_column,
                command.root,
            ),
        )
        for command in owner_commands:
            key = command.key
            if key not in depth:
                decision = "move_candidate"
                reason = "closure_free"
                closure_depth = ""
                target_owner = target_root = witness_kind = witness_source = witness_target = ""
            elif depth[key] == 0:
                decision = "retain_historical"
                reason = "private_seed"
                closure_depth = "0"
                target_owner = target_root = witness_kind = witness_source = witness_target = ""
            else:
                decision = "retain_historical"
                reason = "depends_on_retained_command"
                closure_depth = str(depth[key])
                target = chosen_target[key]
                target_owner, target_root = target
                witness_kind, witness_source, witness_target = chosen_witness[(key, target)]
            private_count = sum(
                declarations[name].visibility == "private" for name in command.declarations
            )
            writer.writerow([
                "command",
                owner,
                command.root,
                command.span_origin,
                str(command.start_line + 1),
                str(command.start_column),
                str(command.end_line + 1),
                str(command.end_column),
                decision,
                reason,
                closure_depth,
                target_owner,
                target_root,
                witness_kind,
                witness_source,
                witness_target,
                str(len(command.declarations)),
                str(private_count),
                json.dumps(command.declarations, ensure_ascii=False, separators=(",", ":")),
            ])
    return output.getvalue()


def parse_arguments() -> argparse.Namespace:
    script = Path(__file__).resolve()
    default_repo = script.parents[4]
    default_projection = (
        default_repo
        / "docs/architecture/phases/2026-08-repository-reorganization"
        / "projections/P0002.tsv.gz"
    )
    default_output = script.with_name("PRIVATE_CLOSURE.tsv")
    parser = argparse.ArgumentParser(
        description="Compute the frozen W02 private-command reverse closure.",
        epilog=(
            "The TSV begins with format/metadata/columns records, then one owner "
            "record per physical module and one command record per atomic source "
            "command. Reconstruct the historical facade from retain_historical "
            "spans and use move_candidate spans as inputs to semantic destination "
            "routing. Preserve imports, namespace/section scaffolding, options, "
            "comments, and trivia separately; this planner intentionally does not "
            "assign destination modules or rewrite Lean source."
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--repo-root", type=Path, default=default_repo)
    parser.add_argument("--base", default=FROZEN_BASE)
    parser.add_argument("--projection", type=Path, default=default_projection)
    parser.add_argument(
        "--ilean-root",
        type=Path,
        default=default_repo / ".lake/build/lib/lean",
        help="root containing baseline NumStability/**/*.ilean files",
    )
    parser.add_argument("--output", type=Path, default=default_output)
    parser.add_argument(
        "--check",
        action="store_true",
        help="verify that --output already equals the deterministic result",
    )
    return parser.parse_args()


def execute(args: argparse.Namespace) -> tuple[Path, int, int]:
    repo = args.repo_root.resolve()
    delivery = repo / "docs/architecture/deliveries/W02"
    output = args.output.resolve()
    if output.parent != delivery.resolve():
        raise PlanError(f"output must remain inside {delivery}")
    resolved_base = str(run_git(repo, "rev-parse", f"{args.base}^{{commit}}"))
    if resolved_base != FROZEN_BASE:
        raise PlanError(
            f"W02 base differs: expected {FROZEN_BASE}, found {resolved_base}"
        )

    declarations, edges = read_projection(args.projection.resolve())
    commands: dict[tuple[str, str], Command] = {}
    sources: dict[str, str] = {}
    evidence: dict[str, OwnerEvidence] = {}
    for owner in PHYSICAL_OWNERS:
        relative_source = module_path(owner, ".lean").as_posix()
        source_payload, source, blob = read_base_source(repo, resolved_base, relative_source)
        sources[owner] = source
        relative_ilean = module_path(owner, ".ilean")
        ilean_path = args.ilean_root.resolve() / relative_ilean
        ilean, ilean_digest = read_ilean(ilean_path, owner)
        owner_commands = commands_from_ilean(owner, ilean, source)
        overlap = set(commands).intersection(owner_commands)
        if overlap:
            raise PlanError(f"duplicate command keys: {sorted(overlap)[:5]}")
        commands.update(owner_commands)
        evidence[owner] = OwnerEvidence(
            module=owner,
            source_path=relative_source,
            source_blob_sha1=blob,
            source_sha256=sha256_bytes(source_payload),
            ilean_path=(Path(".lake/build/lib/lean") / relative_ilean).as_posix(),
            ilean_sha256=ilean_digest,
        )

    initial_command_count = len(commands)
    if initial_command_count != EXPECTED_ILEAN_COMMANDS:
        raise PlanError(
            f"expected {EXPECTED_ILEAN_COMMANDS} .ilean commands, "
            f"found {initial_command_count}"
        )
    declaration_commands = build_command_map(
        declarations, edges, commands, sources
    )
    alias_count = sum(
        command.span_origin == "source_alias" for command in commands.values()
    )
    if alias_count != EXPECTED_SOURCE_ALIAS_COMMANDS:
        raise PlanError(
            f"expected {EXPECTED_SOURCE_ALIAS_COMMANDS} recovered aliases, "
            f"found {alias_count}"
        )
    depth, chosen_target, chosen_witness = compute_closure(
        declarations, edges, commands, declaration_commands
    )
    rendered = render_plan(
        resolved_base,
        declarations,
        commands,
        evidence,
        depth,
        chosen_target,
        chosen_witness,
    )

    if args.check:
        if not output.is_file():
            raise PlanError(f"--check output is missing: {output}")
        current = output.read_text(encoding="utf-8")
        if current != rendered:
            raise PlanError(f"{output} is stale; regenerate without --check")
    else:
        output.write_text(rendered, encoding="utf-8", newline="")
    return output, len(commands), len(depth)


def main() -> int:
    args = parse_arguments()
    try:
        output, command_count, retained_count = execute(args)
    except PlanError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    action = "verified" if args.check else "wrote"
    print(
        f"{action} {output}: {command_count} commands, "
        f"{retained_count} retained, {command_count - retained_count} movable"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
