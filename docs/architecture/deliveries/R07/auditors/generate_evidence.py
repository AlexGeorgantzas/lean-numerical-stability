#!/usr/bin/env python3
"""Generate the byte-derived R07 delivery ledgers.

The generator deliberately has only two inputs: the activated control checkout and
the worker tree rooted at the exact C0005 code commit.  In normal mode it checks
that committed/copied evidence is reproducible; ``--write`` materializes it.
"""

from __future__ import annotations

import argparse
import csv
import difflib
import hashlib
import importlib.util
import io
import json
import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path


BASE_SHA = "ad92bbfae62d538f3e52829a269a846688a8e213"
CONTROL_HEAD = "35cb1a7c5f136f291398dddd99d8012dcf38f967"
BRANCH_SHA256 = "007CD9A2CF7A886B0789CCD0BE3CCF42A35EFC2D310B8EA3C1A20177C21231D2"
PHASE = Path("docs/architecture/phases/2026-08-repository-reorganization-completion")
BRANCH = PHASE / "branches"
DELIVERY = Path("docs/architecture/deliveries/R07")
CORRECTION_PATH = "R0011-CORRECTION.patch"

COPIES = {
    "DECLARATION_ROUTES.tsv": "B0010-declaration-routes.tsv",
    "PRIVATE_CLOSURE.tsv": "B0010-private-closure.tsv",
    "PRIVATE_NORMALIZATION.tsv": "B0010-private-normalization.tsv",
    "REALIZED_IMPORTS.tsv": "B0010-post-move-import-manifest.tsv",
    "TEST_MATRIX.tsv": "B0010-test-plan.tsv",
}

EXPECTED_EVIDENCE = {
    "MATERIALIZATION.json",
    "auditors/materialize_worker.py",
    "auditors/generate_evidence.py",
    "CHECK_SCOPE.py",
    "CHECK_STATIC.py",
    "CHECK_PROJECTION.py",
    "CHECK_REQUEST_REPLAY.py",
    "DECLARATION_ROUTES.tsv",
    "PRIVATE_CLOSURE.tsv",
    "PRIVATE_NORMALIZATION.tsv",
    "REALIZED_IMPORTS.tsv",
    "RETENTION.tsv",
    "TEST_MATRIX.tsv",
    "CHANGED_PATHS.md",
    "DELIVERY.md",
    "GATE_RESULTS.tsv",
    "INTEGRATOR_REQUESTS.md",
    "PRIVATE_CLOSURE.md",
    "PROJECTION.md",
    "ROUTING.md",
    CORRECTION_PATH,
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def run(root: Path, *args: str, text: bool = True) -> str | bytes:
    result = subprocess.run(
        list(args), cwd=root, check=True, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, text=text,
    )
    return result.stdout


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open("r", encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def render_tsv(fields: list[str], rows: list[dict[str, object]]) -> bytes:
    out = io.StringIO(newline="")
    writer = csv.DictWriter(out, fieldnames=fields, delimiter="\t", lineterminator="\n")
    writer.writeheader()
    writer.writerows(rows)
    return out.getvalue().encode("utf-8")


def module_path(module: str) -> str:
    return module.replace(".", "/") + ".lean"


def git_blob_oid(payload: bytes) -> str:
    header = f"blob {len(payload)}\0".encode("ascii")
    return hashlib.sha1(header + payload).hexdigest()


def load_renderer(control: Path):
    path = control / "tools/architecture/r07_shared_postimages.py"
    spec = importlib.util.spec_from_file_location("r07_delivery_renderer", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load authenticated R0011 renderer")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def casefold_sorted_imports(path: str, payload: bytes) -> bytes:
    lines = payload.decode("utf-8").splitlines(keepends=True)
    pattern = re.compile(r"^import ([A-Za-z0-9_'.]+)\n$")
    indexed = [(index, match.group(1)) for index, line in enumerate(lines)
               if (match := pattern.fullmatch(line))]
    if not indexed:
        raise RuntimeError(f"{path}: correction could not find imports")
    names = [name for _, name in indexed]
    expected = sorted(set(names), key=str.casefold)
    if len(expected) != len(names):
        raise RuntimeError(f"{path}: correction found duplicate imports")
    if names == expected:
        raise RuntimeError(f"{path}: correction is unexpectedly a no-op")
    for (index, _), name in zip(indexed, expected, strict=True):
        lines[index] = f"import {name}\n"
    result = "".join(lines).encode("utf-8")
    if b"\r" in result or not result.endswith(b"\n"):
        raise RuntimeError(f"{path}: corrected aggregate is not canonical LF text")
    return result


def zero_context_patch(preimages: dict[str, bytes], postimages: dict[str, bytes]) -> bytes:
    if set(preimages) != set(postimages):
        raise RuntimeError("correction preimage/postimage path sets differ")
    chunks: list[bytes] = []
    for path in sorted(postimages):
        before, after = preimages[path], postimages[path]
        if before == after:
            raise RuntimeError(f"correction contains a no-op: {path}")
        chunks.append(f"diff --git a/{path} b/{path}\n".encode("utf-8"))
        chunks.append(
            f"index {git_blob_oid(before)}..{git_blob_oid(after)} 100644\n".encode("ascii")
        )
        diff = difflib.unified_diff(
            before.decode("utf-8").splitlines(keepends=True),
            after.decode("utf-8").splitlines(keepends=True),
            fromfile=f"a/{path}", tofile=f"b/{path}", n=0, lineterm="\n",
        )
        chunks.append("".join(diff).encode("utf-8"))
    result = b"".join(chunks)
    if b"\r" in result or not result.endswith(b"\n"):
        raise RuntimeError("correction patch is not canonical LF text")
    return result


def correction_patch_bytes(repo: Path, control: Path) -> bytes:
    renderer = load_renderer(control)
    compatibility = (
        control / PHASE / "reviews/R07-COMPATIBILITY-postimage.md"
    ).read_bytes()
    rendered = renderer.render_artifacts(compatibility, verify_replay=False)
    aggregate_paths = ("NumStability/Algorithms.lean", "NumStability/Analysis.lean")
    preimages = {path: rendered.postimages[path] for path in aggregate_paths}
    postimages = {
        path: casefold_sorted_imports(path, preimages[path]) for path in aggregate_paths
    }

    layout_path = "docs/architecture/layout-exceptions.json"
    layout_preimage = rendered.postimages[layout_path]
    layout = json.loads(layout_preimage)
    ceilings = layout.get("direct_import_ceilings", {}).get("NumStability.Algorithms", {})
    if ceilings.get("NumStability.Source.") != 72:
        raise RuntimeError("R0011 layout postimage source-import ceiling is not 72")
    ceilings["NumStability.Source."] = 73
    layout_postimage = (json.dumps(layout, indent=2, ensure_ascii=False) + "\n").encode("utf-8")
    preimages[layout_path] = layout_preimage
    postimages[layout_path] = layout_postimage

    checker_path = "tools/architecture/check_layout.py"
    checker_preimage = run(repo, "git", "show", f"{BASE_SHA}:{checker_path}", text=False)
    marker = (
        b"                if name.startswith(contract) and name not in structural\n"
    )
    replacement = (
        b"                if (\n"
        b"                    name.startswith(contract)\n"
        b"                    and name not in structural\n"
        b"                    and assignment.get(name) != \"internal\"\n"
        b"                )\n"
    )
    if checker_preimage.count(marker) != 1:
        raise RuntimeError("layout checker completeness marker is not unique")
    checker_postimage = checker_preimage.replace(marker, replacement)
    preimages[checker_path] = checker_preimage
    postimages[checker_path] = checker_postimage
    return zero_context_patch(preimages, postimages)


def verify_control(control: Path) -> None:
    head = run(control, "git", "rev-parse", "HEAD").strip()
    if head != CONTROL_HEAD:
        raise RuntimeError(f"control HEAD {head}, expected {CONTROL_HEAD}")
    record = control / BRANCH / "B0010.json"
    if sha256(record.read_bytes()) != BRANCH_SHA256:
        raise RuntimeError("B0010.json hash differs from the activated control")
    payload = json.loads(record.read_text(encoding="utf-8"))
    if payload.get("status") != "active" or payload.get("base_sha") != BASE_SHA:
        raise RuntimeError("B0010 is not active at exact C0005")
    evidence = payload.get("refresh", {}).get("evidence", [])
    if len(evidence) != 61:
        raise RuntimeError(f"B0010 refresh evidence has {len(evidence)} rows, expected 61")
    for item in evidence:
        artifact = control / item["path"]
        actual = sha256(artifact.read_bytes()) if artifact.is_file() else "MISSING"
        if actual != item["sha256"]:
            raise RuntimeError(f"control evidence mismatch: {item['path']}: {actual}")


def retention_bytes(repo: Path, control: Path) -> bytes:
    inventory = read_tsv(control / BRANCH / "B0010-inventory.tsv")
    module_routes = {
        row["owner_module"]: row
        for row in read_tsv(control / BRANCH / "B0010-module-routes.tsv")
    }
    routes = read_tsv(control / BRANCH / "B0010-declaration-routes.tsv")
    by_owner: dict[str, list[dict[str, str]]] = defaultdict(list)
    for route in routes:
        by_owner[route["baseline_owner_module"]].append(route)

    rows: list[dict[str, object]] = []
    for owner in inventory:
        module = owner["module"]
        module_route = module_routes[module]
        path = owner["path"]
        declarations = by_owner[module]
        if len(declarations) != int(module_route["declaration_count"]):
            raise RuntimeError(f"inventory/route declaration mismatch for {module}")
        public = sum(row["visibility"] == "public" for row in declarations)
        private = sum(row["visibility"] == "private" for row in declarations)
        destinations = sorted({row["destination_module"] for row in declarations})
        current = repo / path
        if not current.is_file():
            raise RuntimeError(f"historical owner missing: {path}")
        base = run(repo, "git", "show", f"{BASE_SHA}:{path}", text=False)
        changed = current.read_bytes() != base
        rows.append({
            "owner_module": module,
            "path": path,
            "base_blob_oid": owner["base_blob_oid"],
            "baseline_declarations": len(declarations),
            "public_declarations": public,
            "private_declarations": private,
            "relocated_declarations": len(declarations),
            "retained_declarations": 0,
            "destination_modules": ";".join(destinations) if destinations else "-",
            "wrapper_action": module_route["compatibility_action"],
            "worker_change": "modified" if changed else "byte_identical",
            "postimage_sha256": sha256(current.read_bytes()),
        })

    totals = Counter()
    for row in rows:
        for key in ("baseline_declarations", "public_declarations", "private_declarations",
                    "relocated_declarations", "retained_declarations"):
            totals[key] += int(row[key])
    expected = {
        "baseline_declarations": 194, "public_declarations": 150,
        "private_declarations": 44, "relocated_declarations": 194,
        "retained_declarations": 0,
    }
    if totals != Counter(expected):
        raise RuntimeError(f"unexpected retention totals: {dict(totals)}")
    changes = Counter(row["worker_change"] for row in rows)
    if len(rows) != 45 or changes != Counter({"modified": 13, "byte_identical": 32}):
        raise RuntimeError(f"unexpected retention shape: rows={len(rows)}, changes={dict(changes)}")
    fields = [
        "owner_module", "path", "base_blob_oid", "baseline_declarations",
        "public_declarations", "private_declarations", "relocated_declarations",
        "retained_declarations", "destination_modules", "wrapper_action",
        "worker_change", "postimage_sha256",
    ]
    return render_tsv(fields, rows)


def changed_paths(repo: Path) -> dict[str, str]:
    statuses: dict[str, str] = {}
    raw = run(repo, "git", "diff", "--name-status", "--no-renames", BASE_SHA)
    for line in raw.splitlines():
        if not line:
            continue
        status, path = line.split("\t", 1)
        statuses[path.replace("\\", "/")] = status
    untracked = run(repo, "git", "ls-files", "--others", "--exclude-standard")
    for path in untracked.splitlines():
        statuses[path.replace("\\", "/")] = "A"
    for relative in EXPECTED_EVIDENCE:
        statuses.setdefault((DELIVERY / relative).as_posix(), "A")
    return statuses


def changed_paths_bytes(repo: Path) -> bytes:
    statuses = changed_paths(repo)
    by_status = Counter(statuses.values())
    groups = Counter()
    for path in statuses:
        if path.startswith("NumStabilityTest/Reorganization/R07/"):
            groups["tests"] += 1
        elif path.startswith(DELIVERY.as_posix() + "/"):
            groups["evidence"] += 1
        elif path.startswith("NumStability/"):
            groups["production"] += 1
        else:
            groups["outside"] += 1
    lines = [
        "# R07 changed paths", "",
        f"Base code: `{BASE_SHA}`", "",
        f"Closed delivery set: **{len(statuses)} paths** "
        f"({by_status['M']} modified, {by_status['A']} added).", "",
        f"Production: {groups['production']}; tests: {groups['tests']}; "
        f"delivery evidence: {groups['evidence']}; outside scope: {groups['outside']}.", "",
        "| Status | Path |", "|---|---|",
    ]
    lines.extend(f"| {statuses[path]} | `{path}` |" for path in sorted(statuses, key=str.casefold))
    lines.append("")
    return "\n".join(lines).encode("utf-8")


def outputs(repo: Path, control: Path) -> dict[Path, bytes]:
    result = {
        DELIVERY / name: (control / BRANCH / source).read_bytes()
        for name, source in COPIES.items()
    }
    result[DELIVERY / "RETENTION.tsv"] = retention_bytes(repo, control)
    result[DELIVERY / CORRECTION_PATH] = correction_patch_bytes(repo, control)
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
        print("R07 evidence generation check failed:", file=sys.stderr)
        for problem in problems:
            print(f"- {problem}", file=sys.stderr)
        return 1
    for relative, data in sorted(rendered.items(), key=lambda item: item[0].as_posix()):
        rows = data.count(b"\n") - (1 if relative.suffix == ".tsv" else 0)
        print(f"{relative.as_posix()}\t{sha256(data)}\tbytes={len(data)}\trows={rows}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
