#!/usr/bin/env python3
"""Deterministic R09 postimage verifier.

R07 shipped a *renderer*: its control carried `B0010-source-commands.tsv`, an
ilean-span ledger that let the materializer re-extract every relocated source
command byte-for-byte.  The R09 planning control has no source-command ledger,
so a faithful re-render of destination *bodies* is not constructible from the
delivered inputs.  This program therefore verifies rather than re-renders:

  * every postimage listed in MATERIALIZATION.json is re-hashed against the
    worker tree, so the body bytes are bound by SHA-256;
  * every compatibility wrapper is re-derived from B0011-wrapper-imports.tsv
    and required to be exactly that import sequence and nothing else;
  * every destination import sequence is re-derived from
    B0011-post-move-import-manifest.tsv;
  * every test module is re-derived from B0011-test-plan.tsv;
  * the manifest's own digest is recomputed and printed.

That difference from R07 is disclosed in DELIVERY.md.  --verify is the only
mode; the flag exists so that CHECK_STATIC.py's invocation is explicit.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import sys
from pathlib import Path


PHASE = Path("docs/architecture/phases/2026-08-repository-reorganization-completion")
BRANCH = PHASE / "branches"
DELIVERY = Path("docs/architecture/deliveries/R09")
EXPECTED_FILES = 224


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open("r", encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def strip_comments(text: str) -> str:
    out: list[str] = []
    index = depth = 0
    quoted = escaped = False
    while index < len(text):
        pair = text[index:index + 2]
        if depth:
            if pair == "/-":
                depth += 1
                index += 2
            elif pair == "-/":
                depth -= 1
                index += 2
            else:
                index += 1
            continue
        if quoted:
            out.append(text[index])
            if escaped:
                escaped = False
            elif text[index] == "\\":
                escaped = True
            elif text[index] == '"':
                quoted = False
            index += 1
            continue
        if pair == "/-":
            depth = 1
            index += 2
        elif pair == "--":
            newline = text.find("\n", index + 2)
            index = len(text) if newline < 0 else newline
        else:
            out.append(text[index])
            quoted = text[index] == '"'
            index += 1
    return "".join(out)


def imports_of(path: Path) -> list[str]:
    return [line.strip() for line in path.read_text(encoding="utf-8-sig").splitlines()
            if line.lstrip().startswith("import ")]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--verify", action="store_true", required=True)
    parser.add_argument("--project-root", type=Path, default=Path(__file__).resolve().parents[5])
    parser.add_argument("--control-root", type=Path, required=True)
    args = parser.parse_args()
    repo = args.project_root.resolve()
    control = args.control_root.resolve()
    problems: list[str] = []

    manifest_path = repo / DELIVERY / "MATERIALIZATION.json"
    manifest_bytes = manifest_path.read_bytes()
    manifest = json.loads(manifest_bytes.decode("utf-8"))
    files = manifest.get("files", [])
    if len(files) != EXPECTED_FILES:
        problems.append(f"manifest lists {len(files)} files, expected {EXPECTED_FILES}")
    verified = 0
    for item in files:
        path = repo / item["path"]
        if not path.is_file():
            problems.append(f"missing postimage {item['path']}")
            continue
        payload = path.read_bytes()
        if sha256(payload) != item["sha256"]:
            problems.append(f"postimage digest mismatch {item['path']}")
            continue
        if b"\r" in payload or not payload.endswith(b"\n") or payload.endswith(b"\n\n"):
            problems.append(f"postimage is not canonical LF text: {item['path']}")
            continue
        verified += 1

    wrappers = read_tsv(control / BRANCH / "B0011-wrapper-imports.tsv")
    for row in wrappers:
        path = repo / (row["owner_module"].replace(".", "/") + ".lean")
        expected = [f"import {target}" for target in row["post_imports"].split(";")
                    if target != "-"]
        if imports_of(path) != expected:
            problems.append(f"wrapper import sequence mismatch: {row['owner_module']}")
        remainder = "\n".join(
            line for line in strip_comments(path.read_text(encoding="utf-8-sig")).splitlines()
            if not line.lstrip().startswith("import ")
        ).strip()
        if remainder:
            problems.append(f"wrapper is not import-only: {row['owner_module']}")

    manifest_rows = read_tsv(control / BRANCH / "B0011-post-move-import-manifest.tsv")
    by_module: dict[str, list[dict[str, str]]] = {}
    for row in manifest_rows:
        by_module.setdefault(row["module"], []).append(row)
    for row in read_tsv(control / BRANCH / "B0011-destinations.tsv"):
        module = row["module"]
        expected = [entry["lean_import_line"] for entry in sorted(
            (entry for entry in by_module.get(module, [])
             if entry["role"] == "produced_destination"),
            key=lambda entry: int(entry["import_order"]),
        )]
        path = repo / (module.replace(".", "/") + ".lean")
        if imports_of(path) != expected:
            problems.append(f"destination import sequence mismatch: {module}")

    for row in read_tsv(control / BRANCH / "B0011-test-plan.tsv"):
        path = repo / row["target"]
        actual = [line.split(None, 1)[1] for line in imports_of(path)]
        expected = [] if row["imports"] == "-" else row["imports"].split(";")
        if actual != expected:
            problems.append(f"test import sequence mismatch: {row['target']}")

    if problems:
        print("R09 materialization verify FAILED", file=sys.stderr)
        for problem in problems:
            print(f"- {problem}", file=sys.stderr)
        return 1
    print(json.dumps({
        "materialization_sha256": sha256(manifest_bytes),
        "verified_files": verified,
        "record_kind": manifest.get("record_kind"),
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
