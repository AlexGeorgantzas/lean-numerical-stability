#!/usr/bin/env python3
"""Build a deterministic, task-neutral NumStability declaration atlas.

The atlas is a discovery aid, not trusted Lean input.  It reduces repeated
task-time source scans by mapping searchable concepts to declaration names,
owning modules, source locations, and compact declaration signatures.  The
frozen source and compiled OLean trees remain authoritative.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
from typing import Any, Iterable

from common import BenchmarkError, canonical_json_bytes, sha256_file, write_bytes_atomic, write_json_atomic


SCHEMA_VERSION = "numstability-library-atlas-1"
DECLARATION_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)"
)
SCOPE_RE = re.compile(r"^\s*(namespace|section)\s*([A-Za-z_][A-Za-z0-9_']*)?\s*$")
END_RE = re.compile(r"^\s*end(?:\s+([A-Za-z_][A-Za-z0-9_']*))?\s*$")
MAX_SIGNATURE_LINES = 80
MAX_SIGNATURE_BYTES = 8 * 1024

QUERY_SCRIPT = r'''#!/usr/bin/env python3
"""Rank a bounded set of frozen declaration-atlas hits."""
from __future__ import annotations
import argparse
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("terms", nargs="+")
parser.add_argument("--limit", type=int, default=30)
parser.add_argument("--any", action="store_true")
args = parser.parse_args()
if args.limit < 1 or args.limit > 100:
    parser.error("--limit must be between 1 and 100")
terms = [term.casefold() for term in args.terms]
hits = []
path = Path(__file__).with_name("declarations.jsonl")
for line in path.read_text(encoding="utf-8").splitlines():
    record = json.loads(line)
    fields = {
        "name": str(record["name"]).casefold(),
        "module": str(record["module"]).casefold(),
        "signature": str(record["signature"]).casefold(),
        "documentation": str(record["documentation"]).casefold(),
    }
    present = [any(term in value for value in fields.values()) for term in terms]
    if not (any(present) if args.any else all(present)):
        continue
    score = 0
    for term in terms:
        score += 12 if fields["name"] == term else 0
        score += 8 if term in fields["name"] else 0
        score += 4 if term in fields["module"] else 0
        score += 3 if term in fields["documentation"] else 0
        score += 2 if term in fields["signature"] else 0
    compact = {
        key: record[key]
        for key in ("name", "kind", "module", "source_file", "source_line", "signature")
    }
    if record.get("documentation"):
        compact["documentation"] = record["documentation"]
    hits.append((-score, record["module"], record["name"], compact))
hits.sort(key=lambda item: item[:3])
for _, _, _, record in hits[: args.limit]:
    print(json.dumps(record, sort_keys=True, ensure_ascii=False))
print(f"matched={len(hits)} returned={min(len(hits), args.limit)}", file=__import__("sys").stderr)
'''


def _module_name(source_root: Path, path: Path) -> str:
    relative = path.relative_to(source_root.parent).with_suffix("")
    return ".".join(relative.parts)


def _signature(lines: list[str], start: int) -> str:
    collected: list[str] = []
    depth = 0
    for line in lines[start : start + MAX_SIGNATURE_LINES]:
        collected.append(line.rstrip())
        code = line.split("--", 1)[0]
        depth += sum(code.count(char) for char in "([{⟨")
        depth -= sum(code.count(char) for char in ")] }⟩".replace(" ", ""))
        if ":=" in code or re.search(r"\bwhere\s*$", code):
            break
        if len("\n".join(collected).encode("utf-8")) > MAX_SIGNATURE_BYTES:
            break
        if len(collected) > 1 and depth <= 0 and code.rstrip().endswith(("Prop", "Type")):
            break
    rendered = "\n".join(collected).strip()
    if ":=" in rendered:
        rendered = rendered.split(":=", 1)[0].rstrip()
    return rendered[:MAX_SIGNATURE_BYTES]


def _doc_context(lines: list[str], start: int) -> str:
    context: list[str] = []
    cursor = start - 1
    while cursor >= 0 and len(context) < 12:
        stripped = lines[cursor].strip()
        if not stripped:
            if context:
                break
            cursor -= 1
            continue
        if stripped.startswith(("--", "/-", "*", "-/")):
            context.append(stripped.lstrip("/-* ").rstrip("-/ "))
            cursor -= 1
            continue
        break
    return " ".join(reversed([item for item in context if item]))[:2048]


def _declarations(source_root: Path, root_module: Path | None) -> Iterable[dict[str, Any]]:
    paths = sorted(source_root.rglob("*.lean"))
    if root_module is not None and root_module.is_file():
        paths = [root_module, *paths]
    for path in paths:
        if path.is_symlink() or not path.is_file():
            raise BenchmarkError(f"unsafe library source in atlas input: {path}")
        text = path.read_text(encoding="utf-8")
        lines = text.splitlines()
        scopes: list[tuple[str, str | None]] = []
        module = _module_name(source_root, path)
        relative = path.relative_to(source_root.parent).as_posix()
        for index, line in enumerate(lines):
            scope = SCOPE_RE.match(line)
            if scope:
                scopes.append((scope.group(1), scope.group(2)))
                continue
            if END_RE.match(line):
                if scopes:
                    scopes.pop()
                continue
            match = DECLARATION_RE.match(line)
            if not match:
                continue
            kind, display_name = match.groups()
            namespaces = [name for scope_kind, name in scopes if scope_kind == "namespace" and name]
            qualified_name = (
                display_name
                if "." in display_name or not namespaces
                else ".".join([*namespaces, display_name])
            )
            signature = _signature(lines, index)
            doc = _doc_context(lines, index)
            yield {
                "kind": kind,
                "name": qualified_name,
                "display_name": display_name,
                "module": module,
                "source_file": relative,
                "source_line": index + 1,
                "signature": signature,
                "documentation": doc,
            }


def build_library_atlas(
    *, source_root: Path, root_module: Path | None, output_root: Path, library_commit: str
) -> dict[str, Any]:
    source_root = source_root.resolve()
    root_module = root_module.resolve() if root_module is not None else None
    if not source_root.is_dir() or source_root.is_symlink():
        raise BenchmarkError("library atlas source root is missing or unsafe")
    if output_root.exists():
        raise BenchmarkError("library atlas output already exists")
    output_root.mkdir(parents=True, mode=0o700)
    records = sorted(
        _declarations(source_root, root_module),
        key=lambda item: (item["module"], item["name"], item["source_line"]),
    )
    if not records:
        raise BenchmarkError("library atlas found no declarations")
    jsonl = b"".join(canonical_json_bytes(record) for record in records)
    write_bytes_atomic(output_root / "declarations.jsonl", jsonl, mode=0o400)
    modules: dict[str, int] = {}
    for record in records:
        modules[record["module"]] = modules.get(record["module"], 0) + 1
    module_lines = [
        f"{module}\t{count}" for module, count in sorted(modules.items())
    ]
    write_bytes_atomic(
        output_root / "modules.tsv",
        ("module\tdeclaration_count\n" + "\n".join(module_lines) + "\n").encode("utf-8"),
        mode=0o400,
    )
    source_files = sorted(
        [*(source_root.rglob("*.lean")), *([root_module] if root_module else [])],
        key=lambda path: path.as_posix(),
    )
    source_digest = hashlib.sha256()
    for path in source_files:
        relative = path.relative_to(source_root.parent).as_posix()
        source_digest.update(relative.encode("utf-8") + b"\0")
        source_digest.update(bytes.fromhex(sha256_file(path)))
    metadata = {
        "schema_version": SCHEMA_VERSION,
        "library_commit": library_commit,
        "declaration_count": len(records),
        "module_count": len(modules),
        "source_file_count": len(source_files),
        "source_closure_sha256": source_digest.hexdigest(),
        "declarations_sha256": sha256_file(output_root / "declarations.jsonl"),
    }
    write_json_atomic(output_root / "atlas.json", metadata, mode=0o400)
    write_bytes_atomic(output_root / "query.py", QUERY_SCRIPT.encode("utf-8"), mode=0o500)
    guide = f"""# NumStability library guide

This read-only, task-neutral atlas indexes the frozen NumStability snapshot.
It contains {len(records)} declarations from {len(modules)} modules. The Lean
source and compiled OLean files remain authoritative.

## Reuse-first workflow

1. Translate the paper statement into a short concept list before defining local
   numerical objects (for example: gamma, floating-point model, residual,
   backward error, Cholesky, Strassen, or norm).
2. Search the compact atlas first. The ranked query requires every term and
   returns at most 30 hits by default:
   `/usr/bin/python3 /library-index/query.py gamma root product`
   If that has no result, retry once with fewer terms or `--any --limit 30`.
3. Inspect only the returned source locations under `/library/NumStability` and
   confirm promising declarations with a tiny temporary `#check` file.
4. Prefer importing and reusing a semantically compatible declaration or theorem.
   Define a local replacement only when the paper materially differs; explain
   that mismatch in a nearby Lean comment.
5. Do not scan the whole library unless the atlas has no plausible hit.

Files:
- `/library-index/declarations.jsonl`: one searchable JSON object per declaration.
- `/library-index/query.py`: ranked, bounded atlas lookup (limit 1-100).
- `/library-index/modules.tsv`: module inventory and declaration counts.
- `/library-index/atlas.json`: frozen identity and closure statistics.
"""
    write_bytes_atomic(output_root / "GUIDE.md", guide.encode("utf-8"), mode=0o400)
    for path in output_root.iterdir():
        path.chmod(0o500 if path.name == "query.py" else 0o400)
    output_root.chmod(0o500)
    return metadata


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--root-module", type=Path)
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--library-commit", required=True)
    args = parser.parse_args()
    result = build_library_atlas(
        source_root=args.source_root,
        root_module=args.root_module,
        output_root=args.output_root,
        library_commit=args.library_commit,
    )
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
