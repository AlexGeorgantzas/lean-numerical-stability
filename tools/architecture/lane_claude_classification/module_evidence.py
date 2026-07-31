#!/usr/bin/env python3
"""Deterministic source-level evidence extraction for the classification lane.

This module is the single source of truth for every mechanical column of the
classification proposal.  It is intentionally self-contained (standard library
only, no import of shared repository tooling) so the proposal and its checker
stay reproducible after the external handoff packet has been removed.

The extractor never writes to the repository and never inspects build output.
It reads Lean sources, strips comments while preserving offsets, and reports:

* the module docstring (the first ``/-! ... -/`` block);
* the ordered direct import list, split into project and upstream imports;
* every authored declaration with its kind, visibility, and namespaced name;
* deterministic source-correspondence and reusable-mathematics markers;
* the repository import graph, hence direct downstream consumers.

Nothing here is a classification decision.  The tier column of the proposal is
a reviewed human judgement recorded in ``modules.tsv``; this file only supplies
the evidence that the checker re-derives and compares byte-for-byte.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Iterator, Sequence


PROJECT_PREFIX = "NumStability"

SOURCE_ROOTS: tuple[str, ...] = (
    "NumStability.lean",
    "NumStability",
    "NumStabilityTest.lean",
    "NumStabilityTest",
    "examples",
)

IMPORT_RE = re.compile(
    r"(?m)^[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+([A-Za-z0-9_'.]+)"
)

ATTRIBUTE_RE = re.compile(r"@\[[^\]]*\]", re.DOTALL)

DECLARATION_KINDS: tuple[str, ...] = (
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "instance",
    "structure",
    "class",
    "inductive",
    "opaque",
    "axiom",
    "example",
    # `alias new := old` authors a genuine public declaration and is exactly the
    # source-alias shape this migration cares about, so it must be extracted.
    "alias",
)

MODIFIERS: tuple[str, ...] = (
    "private",
    "protected",
    "scoped",
    "local",
    "noncomputable",
    "unsafe",
    "partial",
    "nonrec",
    "mutual",
)

DECLARATION_RE = re.compile(
    r"(?m)^(?P<indent>[ \t]*)"
    r"(?P<mods>(?:(?:" + "|".join(MODIFIERS) + r")[ \t]+)*)"
    r"(?P<kind>" + "|".join(DECLARATION_KINDS) + r")"
    r"(?=[ \t\n]|$)"
    r"[ \t\n]*(?P<name>[^\s(){}\[\]:⦃⟨,]*)"
)

NAMESPACE_RE = re.compile(r"(?m)^[ \t]*namespace[ \t]+([A-Za-z0-9_'.]+)[ \t]*$")
SECTION_RE = re.compile(r"(?m)^[ \t]*section(?:[ \t]+([A-Za-z0-9_'.]+))?[ \t]*$")
END_RE = re.compile(r"(?m)^[ \t]*end(?:[ \t]+([A-Za-z0-9_'.]+))?[ \t]*$")

MODULE_DOCSTRING_RE = re.compile(r"/-!(.*?)-/", re.DOTALL)

# --- source-correspondence markers -------------------------------------------

# Numbered locators that appear in module basenames or declaration names.
NAME_LOCATOR_RE = re.compile(
    r"(?:^|[._])(?:"
    r"[Cc]h(?:apter)?\d+"
    r"|[Hh]igham(?:[Cc]hapter)?\d+"
    r"|[Tt]h(?:eo)?m?(?:eorem)?\d+"
    r"|[Ll]emma\d+"
    r"|[Pp]roblem\d+"
    r"|[Cc]or(?:ollary)?\d+"
    r"|[Ee]q(?:uation)?\d+"
    r"|[Aa]lg(?:orithm)?\d+"
    r"|[Tt]able\d+"
    r"|[Ee]xample\d+"
    r"|[Ss]ection\d+"
    r")"
)

# Process words the repository uses for source-correspondence scaffolding.
PROCESS_WORD_RE = re.compile(
    r"(?:Actual|Bridge|Closure|Discrepancy|Endpoint|Operational|Printed|Prose"
    r"|Remaining|SourceClosure|SourceCorrection|Whole"
    r"|_actual|_bridge|_closure|_discrepancy|_printed|_prose|_source)"
)

# Prose markers inside doc comments.
DOC_NUMBERED_RE = re.compile(
    r"(?:Theorem|Lemma|Problem|Corollary|Equation|Algorithm|Table|Example|"
    r"Section|display|Display)[ \t]*\(?\d+[.–-]\d+"
)
DOC_HIGHAM_RE = re.compile(r"Higham")
DOC_BOOK_RE = re.compile(r"(?:the book|the source|printed|as printed|the text)")
DOC_DISPLAY_RE = re.compile(r"\(\d{1,2}\.\d{1,3}[a-z]?\)")

# Reusable-mathematics markers.
REUSABLE_DOC_RE = re.compile(
    r"(?:reusable|general|generic|source-independent|source-neutral|arbitrary"
    r"|for any|holds for all)"
)

PLACEHOLDER_RE = re.compile(r"\b(?:sorry|admit)\b")


def strip_comments(text: str) -> tuple[str, list[str]]:
    """Blank out Lean comments, returning code and the comment payloads.

    Newlines are preserved so line-anchored regexes still see the original
    line structure.  Nested block comments and string literals are handled.
    """

    out: list[str] = []
    comments: list[str] = []
    index = 0
    depth = 0
    start = 0
    in_string = False
    escaped = False
    length = len(text)
    while index < length:
        char = text[index]
        pair = text[index : index + 2]
        if depth:
            if pair == "/-":
                depth += 1
                out.append("  ")
                index += 2
                continue
            if pair == "-/":
                depth -= 1
                out.append("  ")
                index += 2
                if depth == 0:
                    comments.append(text[start:index])
                continue
            out.append("\n" if char == "\n" else " ")
            index += 1
            continue
        if in_string:
            out.append(char)
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if char == '"':
            in_string = True
            out.append(char)
            index += 1
            continue
        if pair == "/-":
            depth = 1
            start = index
            out.append("  ")
            index += 2
            continue
        if pair == "--":
            stop = text.find("\n", index)
            if stop == -1:
                stop = length
            comments.append(text[index:stop])
            out.append(" " * (stop - index))
            index = stop
            continue
        out.append(char)
        index += 1
    return "".join(out), comments


def read_source(path: Path) -> str:
    return path.read_text(encoding="utf-8-sig", errors="replace")


@dataclass(frozen=True)
class Declaration:
    kind: str
    name: str
    qualified_name: str
    is_private: bool
    line: int

    @property
    def is_anonymous(self) -> bool:
        return not self.name


@dataclass(frozen=True)
class ModuleEvidence:
    module: str
    path: str
    line_count: int
    byte_count: int
    imports: tuple[str, ...]
    project_imports: tuple[str, ...]
    upstream_imports: tuple[str, ...]
    module_docstring: str
    doc_comments: tuple[str, ...]
    declarations: tuple[Declaration, ...]
    is_import_only: bool
    has_placeholder: bool

    # ---- derived counts -----------------------------------------------------

    @property
    def public_declarations(self) -> tuple[Declaration, ...]:
        return tuple(d for d in self.declarations if not d.is_private)

    @property
    def private_declarations(self) -> tuple[Declaration, ...]:
        return tuple(d for d in self.declarations if d.is_private)

    @property
    def public_declaration_count(self) -> int:
        return len(self.public_declarations)

    @property
    def private_declaration_count(self) -> int:
        return len(self.private_declarations)

    @property
    def direct_project_import_count(self) -> int:
        return len(self.project_imports)

    def kind_counts(self) -> dict[str, int]:
        counts: dict[str, int] = {}
        for declaration in self.declarations:
            counts[declaration.kind] = counts.get(declaration.kind, 0) + 1
        return dict(sorted(counts.items()))

    # ---- markers ------------------------------------------------------------

    @property
    def basename(self) -> str:
        return self.module.rsplit(".", 1)[-1]

    def source_marker_fields(self) -> dict[str, int | str]:
        basename_locator = NAME_LOCATOR_RE.search(self.basename)
        basename_process = PROCESS_WORD_RE.search(self.basename)
        located = sum(
            1
            for declaration in self.declarations
            if NAME_LOCATOR_RE.search(declaration.name)
            or PROCESS_WORD_RE.search(declaration.name)
        )
        docs = "\n".join(self.doc_comments)
        return {
            "name_locator": basename_locator.group(0).lstrip("._") if basename_locator else "",
            "name_process_word": basename_process.group(0) if basename_process else "",
            "located_declarations": located,
            "declarations": len(self.declarations),
            "doc_numbered_refs": len(DOC_NUMBERED_RE.findall(docs)),
            "doc_higham_refs": len(DOC_HIGHAM_RE.findall(docs)),
            "doc_book_refs": len(DOC_BOOK_RE.findall(docs)),
            "doc_display_refs": len(DOC_DISPLAY_RE.findall(docs)),
            "source_tier_imports": sum(
                1
                for name in self.project_imports
                if name.startswith(("NumStability.Source", "NumStability.Higham"))
            ),
        }

    def reusable_marker_fields(self) -> dict[str, int | str]:
        neutral = sum(
            1
            for declaration in self.public_declarations
            if not NAME_LOCATOR_RE.search(declaration.name)
            and not PROCESS_WORD_RE.search(declaration.name)
        )
        docs = "\n".join(self.doc_comments)
        kinds = self.kind_counts()
        return {
            "neutral_public_declarations": neutral,
            "public_declarations": self.public_declaration_count,
            "definitional_declarations": (
                kinds.get("def", 0)
                + kinds.get("abbrev", 0)
                + kinds.get("structure", 0)
                + kinds.get("class", 0)
                + kinds.get("inductive", 0)
                + kinds.get("instance", 0)
            ),
            "doc_generality_refs": len(REUSABLE_DOC_RE.findall(docs)),
            "reusable_tier_imports": sum(
                1
                for name in self.project_imports
                if not name.startswith(("NumStability.Source", "NumStability.Higham"))
            ),
        }

    def source_markers(self) -> str:
        return render_markers(self.source_marker_fields())

    def reusable_markers(self) -> str:
        return render_markers(self.reusable_marker_fields())


def render_markers(fields: dict[str, int | str]) -> str:
    """Render marker fields as a stable ``key=value`` semicolon list."""

    parts = []
    for key, value in fields.items():
        text = str(value)
        if any(ch in text for ch in ";=\t\n"):
            raise ValueError(f"marker value for {key!r} is not renderable: {value!r}")
        parts.append(f"{key}={text}")
    return ";".join(parts)


def module_docstring(text: str) -> str:
    match = MODULE_DOCSTRING_RE.search(text)
    return match.group(1).strip() if match else ""


def _split_module_name(path: str) -> str:
    return ".".join(Path(path).with_suffix("").parts)


def declarations_of(code: str) -> tuple[Declaration, ...]:
    """Extract authored declarations with namespace-qualified names.

    ``code`` must already have comments blanked out by :func:`strip_comments`.
    Attribute blocks are blanked first so ``@[simp]\\ntheorem foo`` is matched.
    """

    cleaned = ATTRIBUTE_RE.sub(lambda m: re.sub(r"[^\n]", " ", m.group(0)), code)
    events: list[tuple[int, str, str]] = []
    for match in NAMESPACE_RE.finditer(cleaned):
        events.append((match.start(), "namespace", match.group(1)))
    for match in SECTION_RE.finditer(cleaned):
        events.append((match.start(), "section", match.group(1) or ""))
    for match in END_RE.finditer(cleaned):
        events.append((match.start(), "end", match.group(1) or ""))
    for match in DECLARATION_RE.finditer(cleaned):
        events.append((match.start(), "decl", match.group(0)))
    events.sort(key=lambda item: item[0])

    line_starts = [0]
    for index, char in enumerate(cleaned):
        if char == "\n":
            line_starts.append(index + 1)

    def line_of(offset: int) -> int:
        low, high = 0, len(line_starts) - 1
        while low < high:
            mid = (low + high + 1) // 2
            if line_starts[mid] <= offset:
                low = mid
            else:
                high = mid - 1
        return low + 1

    stack: list[tuple[str, str]] = []
    found: list[Declaration] = []
    for offset, kind, payload in events:
        if kind == "namespace":
            stack.append(("namespace", payload))
            continue
        if kind == "section":
            stack.append(("section", payload))
            continue
        if kind == "end":
            if stack:
                stack.pop()
            continue
        match = DECLARATION_RE.match(payload)
        if match is None:  # pragma: no cover - payload came from the same regex
            continue
        modifiers = match.group("mods").split()
        name = match.group("name").strip()
        if name in {"where", "extends", "deriving"}:
            name = ""
        prefix = ".".join(
            value for entry, value in stack if entry == "namespace" and value
        )
        qualified = f"{prefix}.{name}" if prefix and name else name
        found.append(
            Declaration(
                kind=match.group("kind"),
                name=name,
                qualified_name=qualified,
                is_private="private" in modifiers,
                line=line_of(offset),
            )
        )
    return tuple(found)


def evidence_for(repo: Path, relative_path: str) -> ModuleEvidence:
    path = repo / relative_path
    text = read_source(path)
    code, comments = strip_comments(text)
    imports = tuple(IMPORT_RE.findall(code))
    project = tuple(
        name
        for name in imports
        if name == PROJECT_PREFIX or name.startswith(PROJECT_PREFIX + ".")
    )
    upstream = tuple(name for name in imports if name not in set(project))
    declarations = declarations_of(code)
    stripped_structure = re.sub(
        r"(?m)^[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+[A-Za-z0-9_'.]+[ \t]*$"
        r"|^[ \t]*module[ \t]*$",
        "",
        code,
    )
    return ModuleEvidence(
        module=_split_module_name(relative_path),
        path=relative_path,
        line_count=text.count("\n") + (0 if text.endswith("\n") or not text else 1),
        byte_count=len(path.read_bytes()),
        imports=imports,
        project_imports=project,
        upstream_imports=upstream,
        module_docstring=module_docstring(text),
        doc_comments=tuple(comments),
        declarations=declarations,
        is_import_only=not stripped_structure.strip(),
        has_placeholder=bool(PLACEHOLDER_RE.search(code)),
    )


def iter_repository_lean_paths(repo: Path) -> Iterator[str]:
    for root in SOURCE_ROOTS:
        target = repo / root
        if target.is_file() and target.suffix == ".lean":
            yield root
            continue
        if not target.is_dir():
            continue
        for path in sorted(target.rglob("*.lean")):
            yield path.relative_to(repo).as_posix()


def repository_import_graph(repo: Path) -> tuple[dict[str, tuple[str, ...]], dict[str, tuple[str, ...]]]:
    """Return ``(imports, consumers)`` keyed by module name across the repository."""

    imports: dict[str, tuple[str, ...]] = {}
    for relative in iter_repository_lean_paths(repo):
        code, _ = strip_comments(read_source(repo / relative))
        imports[_split_module_name(relative)] = tuple(IMPORT_RE.findall(code))
    consumers: dict[str, list[str]] = {name: [] for name in imports}
    for name, targets in imports.items():
        for target in targets:
            if target in consumers:
                consumers[target].append(name)
    return imports, {name: tuple(sorted(values)) for name, values in consumers.items()}


def read_tsv(path: Path) -> tuple[tuple[str, ...], list[dict[str, str]]]:
    lines = path.read_text(encoding="utf-8").splitlines()
    if not lines:
        raise ValueError(f"empty TSV: {path}")
    header = tuple(lines[0].split("\t"))
    rows: list[dict[str, str]] = []
    for number, line in enumerate(lines[1:], start=2):
        if not line:
            continue
        fields = line.split("\t")
        if len(fields) != len(header):
            raise ValueError(
                f"{path}:{number}: expected {len(header)} fields, found {len(fields)}"
            )
        rows.append(dict(zip(header, fields)))
    return header, rows


def write_tsv(path: Path, header: Sequence[str], rows: Iterable[Sequence[str]]) -> None:
    body = ["\t".join(header)]
    for row in rows:
        values = [str(value) for value in row]
        for value in values:
            if "\t" in value or "\n" in value:
                raise ValueError(f"TSV field contains a separator: {value!r}")
        body.append("\t".join(values))
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(body) + "\n", encoding="utf-8")
