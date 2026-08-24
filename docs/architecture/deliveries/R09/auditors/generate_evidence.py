#!/usr/bin/env python3
"""Regenerate the byte-derived R09 delivery ledgers.

Two inputs only: the activated control checkout and the worker tree rooted at
the exact C0006 code commit.  Default mode verifies that the committed
evidence is reproducible; --write materializes it.  Wave-independent in
structure; only the identity pins and closed totals are R09-specific.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path


BASE_SHA = "fda296b2079acae3bf1d3565b2dc6e45dc8f6ef5"
PHASE = Path("docs/architecture/phases/2026-08-repository-reorganization-completion")
BRANCH = PHASE / "branches"
DELIVERY = Path("docs/architecture/deliveries/R09")
TEST_PREFIX = "NumStabilityTest/Reorganization/R09/"
COPIES = {
    "DECLARATION_ROUTES.tsv": "B0011-declaration-routes.tsv",
    "PRIVATE_CLOSURE.tsv": "B0011-private-closure.tsv",
    "PRIVATE_NORMALIZATION.tsv": "B0011-private-normalization.tsv",
    "REALIZED_IMPORTS.tsv": "B0011-post-move-import-manifest.tsv",
    "TEST_MATRIX.tsv": "B0011-test-plan.tsv",
}
EXPECTED_EVIDENCE = {
    "CHANGED_PATHS.md",
    "DECLARATION_ROUTES.tsv",
    "DELIVERY.md",
    "GATE_RESULTS.tsv",
    "INTEGRATOR_REQUESTS.md",
    "MATERIALIZATION.json",
    "PRIVATE_CLOSURE.md",
    "PRIVATE_CLOSURE.tsv",
    "PRIVATE_NORMALIZATION.tsv",
    "PROJECTION.md",
    "REALIZED_IMPORTS.tsv",
    "RETENTION.tsv",
    "ROUTING.md",
    "TEST_MATRIX.tsv",
    "auditors/generate_evidence.py",
    "auditors/materialize_worker.py",
}
EXPECTED_TOTALS = {
    "baseline_declarations": 570,
    "public_declarations": 405,
    "private_declarations": 165,
    "relocated_declarations": 570,
    "retained_declarations": 0,
}
EXPECTED_ROWS = 72
EXPECTED_CHANGES = Counter({"modified": 68, "byte_identical": 4})


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def run(root: Path, *args: str, text: bool = True):
    return subprocess.run(
        list(args), cwd=root, check=True, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, text=text,
    ).stdout


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open("r", encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def render_tsv(fields: list[str], rows: list[dict[str, object]]) -> bytes:
    out = io.StringIO(newline="")
    writer = csv.DictWriter(out, fieldnames=fields, delimiter="\t", lineterminator="\n")
    writer.writeheader()
    writer.writerows(rows)
    return out.getvalue().encode("utf-8")


def verify_control(control: Path) -> None:
    record = control / BRANCH / "B0011.json"
    if not record.is_file():
        raise RuntimeError("activated B0011.json is missing from the control checkout")
    payload = json.loads(record.read_text(encoding="utf-8"))
    if payload.get("base_sha") != BASE_SHA:
        raise RuntimeError("B0011 is not based on the exact C0006 code commit")
    if payload.get("status") not in {"active", "accepted"}:
        raise RuntimeError(f"B0011 status is {payload.get('status')!r}")
    for item in payload.get("refresh", {}).get("evidence", []):
        artifact = control / item["path"]
        actual = sha256(artifact.read_bytes()) if artifact.is_file() else "MISSING"
        if actual != item["sha256"]:
            raise RuntimeError(f"control evidence mismatch: {item['path']}: {actual}")


def retention_bytes(repo: Path, control: Path) -> bytes:
    inventory = read_tsv(control / BRANCH / "B0011-inventory.tsv")
    module_routes = {row["owner_module"]: row
                     for row in read_tsv(control / BRANCH / "B0011-module-routes.tsv")}
    routes = read_tsv(control / BRANCH / "B0011-declaration-routes.tsv")
    by_owner: dict[str, list[dict[str, str]]] = defaultdict(list)
    for route in routes:
        by_owner[route["baseline_owner_module"]].append(route)

    rows: list[dict[str, object]] = []
    for owner in inventory:
        module = owner["module"]
        route_row = module_routes[module]
        declarations = by_owner[module]
        if len(declarations) != int(route_row["declaration_count"]):
            raise RuntimeError(f"inventory/route declaration mismatch for {module}")
        public = sum(row["visibility"] == "public" for row in declarations)
        private = sum(row["visibility"] == "private" for row in declarations)
        current = repo / owner["path"]
        if not current.is_file():
            raise RuntimeError(f"historical owner missing: {owner['path']}")
        base = run(repo, "git", "show", f"{BASE_SHA}:{owner['path']}", text=False)
        rows.append({
            "owner_module": module,
            "path": owner["path"],
            "base_blob_oid": owner["base_blob_oid"],
            "baseline_declarations": len(declarations),
            "public_declarations": public,
            "private_declarations": private,
            "relocated_declarations": len(declarations),
            "retained_declarations": 0,
            "destination_modules": ";".join(
                sorted({row["destination_module"] for row in declarations},
                       key=lambda value: (value.casefold(), value))
            ) or "-",
            "wrapper_action": route_row["compatibility_action"],
            "worker_change": "modified" if current.read_bytes() != base else "byte_identical",
            "postimage_sha256": sha256(current.read_bytes()),
        })

    totals: Counter = Counter()
    for row in rows:
        for key in EXPECTED_TOTALS:
            totals[key] += int(row[key])
    if totals != Counter(EXPECTED_TOTALS):
        raise RuntimeError(f"unexpected retention totals: {dict(totals)}")
    changes = Counter(row["worker_change"] for row in rows)
    if len(rows) != EXPECTED_ROWS or changes != EXPECTED_CHANGES:
        raise RuntimeError(f"unexpected retention shape: rows={len(rows)} changes={dict(changes)}")
    return render_tsv([
        "owner_module", "path", "base_blob_oid", "baseline_declarations",
        "public_declarations", "private_declarations", "relocated_declarations",
        "retained_declarations", "destination_modules", "wrapper_action",
        "worker_change", "postimage_sha256",
    ], rows)


def changed_paths(repo: Path) -> dict[str, str]:
    statuses: dict[str, str] = {}
    for line in run(repo, "git", "diff", "--name-status", "--no-renames", BASE_SHA).splitlines():
        if not line:
            continue
        status, path = line.split("\t", 1)
        statuses[path.replace("\\", "/")] = status
    for path in run(repo, "git", "ls-files", "--others", "--exclude-standard").splitlines():
        statuses[path.replace("\\", "/")] = "A"
    for relative in EXPECTED_EVIDENCE:
        statuses.setdefault((DELIVERY / relative).as_posix(), "A")
    return statuses


def changed_paths_bytes(repo: Path) -> bytes:
    statuses = changed_paths(repo)
    by_status = Counter(statuses.values())
    groups: Counter = Counter()
    for path in statuses:
        if path.startswith(TEST_PREFIX):
            groups["tests"] += 1
        elif path.startswith(DELIVERY.as_posix() + "/"):
            groups["evidence"] += 1
        elif path.startswith("NumStability/"):
            groups["production"] += 1
        else:
            groups["outside"] += 1
    lines = [
        "# R09 changed paths", "",
        f"Base code: `{BASE_SHA}`", "",
        f"Closed delivery set: **{len(statuses)} paths** "
        f"({by_status['M']} modified, {by_status['A']} added).", "",
        f"Production: {groups['production']}; tests: {groups['tests']}; "
        f"delivery evidence: {groups['evidence']}; outside scope: {groups['outside']}.", "",
        "| Status | Path |", "|---|---|",
    ]
    lines.extend(f"| {statuses[path]} | `{path}` |"
                 for path in sorted(statuses, key=lambda value: (value.casefold(), value)))
    lines.append("")
    return "\n".join(lines).encode("utf-8")


def outputs(repo: Path, control: Path) -> dict[Path, bytes]:
    result = {DELIVERY / name: (control / BRANCH / source).read_bytes()
              for name, source in COPIES.items()}
    result[DELIVERY / "RETENTION.tsv"] = retention_bytes(repo, control)
    result[DELIVERY / "CHANGED_PATHS.md"] = changed_paths_bytes(repo)
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parents[5])
    parser.add_argument("--control-root", type=Path, required=True)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    repo = args.repo_root.resolve()
    control = args.control_root.resolve()
    verify_control(control)
    rendered = outputs(repo, control)
    problems: list[str] = []
    for relative, data in rendered.items():
        target = repo / relative
        if args.write:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        elif not target.is_file():
            problems.append(f"missing {relative.as_posix()}")
        elif target.read_bytes() != data:
            problems.append(
                f"non-reproducible {relative.as_posix()}: "
                f"actual={sha256(target.read_bytes())} expected={sha256(data)}"
            )
    if problems:
        print("R09 evidence generation check failed:", file=sys.stderr)
        for problem in problems:
            print(f"- {problem}", file=sys.stderr)
        return 1
    for relative, data in sorted(rendered.items(), key=lambda item: item[0].as_posix()):
        rows = data.count(b"\n") - (1 if relative.suffix == ".tsv" else 0)
        print(f"{relative.as_posix()}\t{sha256(data)}\tbytes={len(data)}\trows={rows}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
