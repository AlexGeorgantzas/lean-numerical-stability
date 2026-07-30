#!/usr/bin/env python3
"""Shared, dependency-free helpers for the classification proposal lane."""

from __future__ import annotations

import csv
import hashlib
import json
import re
import subprocess
import zipfile
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parents[3]
BASE_SHA = "6487fc33088523b8f27ecde9ad613515b78f9977"
EVIDENCE_HEAD = "9e7c8e32437d6ea28bf297fc4f08756288df9b26"
PROPOSAL_ROOT = ROOT / "docs/architecture/lane-proposals/claude-classification"
CLASSIFICATION_ROOT = PROPOSAL_ROOT / "classification"

IMPORT_RE = re.compile(
    r"(?m)^\s*(?:(?:public|private)\s+)?import\s+([A-Za-z0-9_'.]+)\s*$"
)
DECL_RE = re.compile(
    r"(?m)^\s*((?:(?:private|protected|noncomputable|unsafe|scoped|local)\s+)*)"
    r"(def|theorem|lemma|abbrev|opaque|axiom|inductive|structure|class|instance)"
    r"\s+([^\s({:\[]+)"
)
MODULE_DOC_RE = re.compile(r"/-!\s*(?:\r?\n)?\s*#?\s*([^\r\n]+)")
SOURCE_NAME_RE = re.compile(
    r"(?i)(?:higham|(?:^|[_.])ch\d|(?:^|[_.])chapter\d|"
    r"(?:^|[_.])problem_?\d|(?:^|[_.])eq(?:uation)?_?\d|"
    r"(?:^|[_.])theorem_?\d|(?:^|[_.])source|printed|discrepancy)"
)
NUMBERED_TEXT_RE = re.compile(
    r"(?i)\b(?:chapter|section|theorem|lemma|problem|equation|algorithm|"
    r"corollary|table)\s*[Â§#]?[ (]*\d"
)


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


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def stable_json(value: object) -> str:
    return json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as stream:
        return list(csv.DictReader(stream, delimiter="\t"))


def write_tsv(path: Path, fieldnames: list[str], rows: Iterable[dict[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(
            stream, fieldnames=fieldnames, delimiter="\t", lineterminator="\n"
        )
        writer.writeheader()
        for row in rows:
            writer.writerow(row)


def git(*args: str, text: bool = True) -> str | bytes:
    return subprocess.check_output(["git", *args], cwd=ROOT, text=text)


def git_show_bytes(revision: str, path: str) -> bytes:
    return subprocess.check_output(
        ["git", "show", f"{revision}:{path}"], cwd=ROOT
    )


def module_from_path(path: str) -> str:
    if not path.endswith(".lean"):
        raise ValueError(f"not a Lean path: {path}")
    return path[:-5].replace("/", ".")


def path_from_module(module: str) -> str:
    return module.replace(".", "/") + ".lean"


def remove_lean_comments(text: str) -> str:
    """Remove nested Lean comments while preserving line/column geometry."""

    chars = list(text)
    depth = 0
    index = 0
    in_string = False
    escaped = False
    while index < len(chars):
        pair = text[index : index + 2]
        if depth == 0 and in_string:
            if escaped:
                escaped = False
            elif text[index] == "\\":
                escaped = True
            elif text[index] == '"':
                in_string = False
            index += 1
            continue
        if depth == 0 and text[index] == '"':
            in_string = True
            index += 1
            continue
        if depth == 0 and pair == "--":
            end = text.find("\n", index)
            if end == -1:
                end = len(chars)
            for position in range(index, end):
                chars[position] = " "
            index = end
            continue
        if pair == "/-":
            depth += 1
            chars[index] = chars[index + 1] = " "
            index += 2
            continue
        if pair == "-/" and depth:
            depth -= 1
            chars[index] = chars[index + 1] = " "
            index += 2
            continue
        if depth and chars[index] not in "\r\n":
            chars[index] = " "
        index += 1
    if depth:
        raise ValueError("unterminated Lean block comment")

    return "".join(chars)


def source_declarations(text: str) -> list[tuple[str, str, str]]:
    uncommented = remove_lean_comments(text)
    return [
        (name.rstrip("`.,;"), kind, "private" if "private" in modifiers.split() else "public")
        for modifiers, kind, name in DECL_RE.findall(uncommented)
    ]


def source_analysis_from_bytes(data: bytes) -> dict[str, object]:
    text = data.decode("utf-8-sig")
    uncommented = remove_lean_comments(text)
    declarations = source_declarations(text)
    title_match = MODULE_DOC_RE.search(text)
    title = " ".join(title_match.group(1).split()) if title_match else "(no module title)"
    imports = [item for item in IMPORT_RE.findall(uncommented) if item.startswith("NumStability")]
    source_names = [name for name, _, _ in declarations if SOURCE_NAME_RE.search(name)]
    generic_names = [name for name, _, _ in declarations if not SOURCE_NAME_RE.search(name)]
    return {
        "title": title,
        "imports": imports,
        "declarations": declarations,
        "source_names": source_names,
        "generic_names": generic_names,
        "higham_tokens": len(re.findall(r"(?i)\bhigham\b", text)),
        "numbered_tokens": len(NUMBERED_TEXT_RE.findall(text)),
        "line_count": len(text.splitlines()),
        "source_sha256": sha256_bytes(data),
    }


def source_analysis(path: Path) -> dict[str, object]:
    return source_analysis_from_bytes(path.read_bytes())


def read_format2_zip(path: Path) -> tuple[dict[str, Declaration], list[Edge], str, int]:
    with zipfile.ZipFile(path) as archive:
        names = archive.namelist()
        if len(names) != 1:
            raise ValueError(f"{path}: expected one format-2 member")
        payload = archive.read(names[0])
    declarations: dict[str, Declaration] = {}
    edges: list[Edge] = []
    for line_number, raw in enumerate(payload.decode("utf-8").splitlines(), 1):
        fields = raw.split("\t")
        if line_number == 1:
            if fields != ["format", "2"]:
                raise ValueError(f"{path}: not format 2")
            continue
        if fields[:1] == ["declaration"] and len(fields) == 5:
            declaration = Declaration(*fields[1:])
            if declaration.name in declarations:
                raise ValueError(f"{path}:{line_number}: duplicate declaration")
            declarations[declaration.name] = declaration
        elif fields[:1] == ["edge"] and len(fields) == 4:
            if fields[1] not in {"signature", "body"}:
                raise ValueError(f"{path}:{line_number}: unknown edge kind")
            edges.append(Edge(*fields[1:]))
        else:
            raise ValueError(f"{path}:{line_number}: malformed format-2 row")
    return declarations, edges, sha256_bytes(payload), len(payload)


def read_ilean_entries(path: Path, expected_module: str) -> dict[str, tuple[int, ...]]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("module") != expected_module:
        raise ValueError(f"{path}: unexpected module {payload.get('module')!r}")
    decls = payload.get("decls")
    if not isinstance(decls, dict):
        raise ValueError(f"{path}: missing declaration map")
    result: dict[str, tuple[int, ...]] = {}
    for name, span in decls.items():
        if not isinstance(name, str) or not isinstance(span, list) or len(span) != 8:
            raise ValueError(f"{path}: malformed declaration range")
        if any(not isinstance(value, int) or value < 0 for value in span):
            raise ValueError(f"{path}: malformed declaration coordinate")
        result[name] = tuple(span)
    return result


def normalized_source_bytes(data: bytes) -> bytes:
    return data.replace(b"\r\n", b"\n").replace(b"\r", b"\n")


class SourceCommandIndex:
    """One-pass byte/character index for many `.ilean` source spans."""

    def __init__(self, payload: bytes):
        self.payload = payload
        self.lines = payload.splitlines(keepends=True) or [b""]
        self.offsets = [0]
        for line in self.lines:
            self.offsets.append(self.offsets[-1] + len(line))

    def command(self, span: tuple[int, ...]) -> bytes:
        payload, lines, offsets = self.payload, self.lines, self.offsets

        def offset(line: int, column: int) -> int:
            if line == len(lines) and column == 0:
                return len(payload)
            if line >= len(lines):
                raise ValueError(f"source coordinate line {line} exceeds {len(lines)}")
            content = lines[line].rstrip(b"\n").decode("utf-8")
            if column > len(content):
                raise ValueError(f"source column {column} exceeds line {line}")
            return offsets[line] + len(content[:column].encode("utf-8"))

        start = offset(span[0], span[1])
        end = offset(span[2], span[3])
        if end <= start:
            raise ValueError(f"empty source span: {span}")
        return payload[start:end]


def source_command_bytes(payload: bytes, span: tuple[int, ...]) -> bytes:
    return SourceCommandIndex(payload).command(span)


def authoritative_root(
    declaration_name: str, entries: dict[str, tuple[int, ...]]
) -> str:
    candidate = declaration_name
    while True:
        if candidate in entries:
            return candidate
        if "." not in candidate:
            break
        candidate = candidate.rsplit(".", 1)[0]
    candidates: list[str] = []
    if not candidates:
        # Named deriving instances are emitted as, for example,
        # `instDecidableEqFoo` beside the authored `Foo` command instead of
        # below `Foo.*`. Associate only an unambiguous longest leaf suffix.
        declaration_leaf = declaration_name.rsplit(".", 1)[-1].casefold()
        candidates = [
            name
            for name in entries
            if declaration_leaf.endswith(name.rsplit(".", 1)[-1].casefold())
        ]
    if not candidates and ".inst" in declaration_name.casefold():
        folded = declaration_name.casefold()
        candidates = [
            name
            for name in entries
            if name.rsplit(".", 1)[-1].casefold() in folded
        ]
    if not candidates:
        raise ValueError(f"{declaration_name}: no authoritative .ilean root")
    longest = max(map(len, candidates))
    roots = [name for name in candidates if len(name) == longest]
    if len(roots) != 1:
        raise ValueError(f"{declaration_name}: ambiguous roots {roots}")
    return roots[0]


def augment_entries_from_source(
    payload: bytes,
    module: str,
    declaration_names: Iterable[str],
    entries: dict[str, tuple[int, ...]],
) -> dict[str, tuple[int, ...]]:
    """Add exact source spans for authored commands omitted by `.ilean`.

    Lean's info tree does not assign declaration ranges to `alias` commands,
    although aliases are present in the environment graph. This conservative
    fallback adds only a declaration's own command when no longest-prefix
    `.ilean` root exists. It never replaces compiler-provided spans.
    """

    result = dict(entries)
    text = payload.decode("utf-8-sig")
    lines = text.splitlines()
    command_words = (
        "alias",
        "def",
        "theorem",
        "lemma",
        "abbrev",
        "opaque",
        "axiom",
        "inductive",
        "structure",
        "class",
        "instance",
    )
    for name in sorted(declaration_names):
        try:
            authoritative_root(name, result)
            continue
        except ValueError:
            pass
        leaf = name.rsplit(".", 1)[-1]
        token = re.compile(rf"(?<![A-Za-z0-9_']){re.escape(leaf)}(?![A-Za-z0-9_'])")
        candidates = [
            index
            for index, line in enumerate(lines)
            if token.search(line) and re.search(rf"\b(?:{'|'.join(command_words)})\b", line)
        ]
        if len(candidates) != 1:
            raise ValueError(
                f"{name}: no .ilean root and expected one authored source command, "
                f"found lines {candidates}"
            )
        start = candidates[0]
        line = lines[start]
        if ":=" in line and line.rstrip().endswith(":=") and start + 1 < len(lines):
            end = start + 2
            span = (start, 0, end, 0, start, 0, start, len(line))
        else:
            span = (start, 0, start, len(line), start, 0, start, len(line))
        result[name] = span
    return result


def safe_cell(value: object) -> str:
    return " ".join(str(value).replace("\t", " ").replace("\r", " ").replace("\n", " ").split())
