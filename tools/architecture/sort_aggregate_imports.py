#!/usr/bin/env python3
"""Sort and deduplicate the import block of an import-only Lean aggregate."""

from __future__ import annotations

import argparse
from pathlib import Path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("path", type=Path, help="Lean aggregate to inspect")
    parser.add_argument(
        "--write",
        action="store_true",
        help="rewrite the file; the default is a read-only check",
    )
    return parser.parse_args()


def sorted_aggregate(text: str) -> str:
    lines = text.splitlines()
    import_indexes = [i for i, line in enumerate(lines) if line.startswith("import ")]
    if not import_indexes:
        raise ValueError("no Lean imports found")

    first, last = import_indexes[0], import_indexes[-1]
    unexpected = [
        line for line in lines[first : last + 1] if line and not line.startswith("import ")
    ]
    if unexpected:
        raise ValueError("the import block is not contiguous")

    imports = sorted({lines[i] for i in import_indexes}, key=str.casefold)
    result = lines[:first] + imports + lines[last + 1 :]
    return "\n".join(result) + "\n"


def main() -> int:
    args = parse_args()
    original = args.path.read_text(encoding="utf-8-sig")
    normalized = sorted_aggregate(original)
    if normalized == original:
        print(f"aggregate imports already sorted: {args.path}")
        return 0
    if not args.write:
        print(f"aggregate imports need sorting: {args.path}")
        return 1
    args.path.write_text(normalized, encoding="utf-8", newline="\n")
    print(f"sorted aggregate imports: {args.path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
