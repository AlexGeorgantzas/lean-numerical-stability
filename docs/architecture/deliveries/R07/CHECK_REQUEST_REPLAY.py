#!/usr/bin/env python3
"""Replay R0011 reversibly and inspect the disposable worker+integrator overlay."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import re
import shutil
import stat
import subprocess
import sys
import tempfile
from collections import Counter
from pathlib import Path, PurePosixPath


BASE = "ad92bbfae62d538f3e52829a269a846688a8e213"
CONTROL_HEAD = "35cb1a7c5f136f291398dddd99d8012dcf38f967"
PHASE = Path("docs/architecture/phases/2026-08-repository-reorganization-completion")
REQUEST = PHASE / "requests"
DELIVERY = Path("docs/architecture/deliveries/R07")
EXPECTED = {
    "request_json": "EA1DB32ACE4243F8223696D2A2AFAAB43C24AC97187861D0A07462B722E4C28C",
    "patch": "6C4BCAFDEB8CF97197F7A46D2CAA5BF05F5A1F81A1DAC4284A615B5AD8E9C122",
    "postimages": "C7B86B602A290650F8ABEA64281DF02A7C6DF94202C4C3FEB5694566A748D0DE",
    "imports": "3F25D0F9A5F1BE095870F96ADD1F6A8E3341176668CB770D4AC917796A69D853",
    "plan": "9316DE9A594E7E924CC2213692ED23B49DCBB5BCCD21285642A60D5B0E09E35D",
    "paths": "C05FA858BF0B5CC3A23F06DEC83F0738780566EA89A172DCA446D4F7129CB901",
    "renderer": "3ECC5D64FF466E2982CAF750B49F183F11907F460C3625744825ACB522FA5C86",
    "compatibility": "FB8C43F1FB8AB3974B0DF4AB1A646A440BCCDBB519D59E2B01773EFDA5B37D67",
    "baseline": "2FC0C95FFECF114A2EDB8C14DB8C2874BDBB85FCEBA722C345AA084B3E97C02A",
    "module_routes": "A3025D8DF5940D206280E6B12DB892952111F46E31616FCA7D3D99105D6C074D",
    "destinations": "36DDEFC49A8D94D02DF08866343E2210E9D525B89535482A47EEE6E4BE9FA976",
    "planned_contract": "387FCF34A62D1C07E1EBB41E96D0BC57E7BF17B099396F7A87C797B52BA13D7C",
    "scope": "05C2DFB3F1A99F928E90DB3E3EA0C2277320DD3985C476ACB1D529762410776F",
}
FORWARD_TREE = "1f5daf23bec193dc68c932f854f754a6b6bcb01e"
CORRECTION_PATH = DELIVERY / "R0011-CORRECTION.patch"
CORRECTION_SHA256 = "DFF0256BCDAB3DA2A3248D85A5A390E345AE5C49D45C6E099E26E315CF03B909"
CORRECTED_TREE = "6c1127df3be9221aa9b51e3b93bfd20ef168f3a6"
CORRECTED_POSTIMAGES = {
    "NumStability/Algorithms.lean":
        "2A3D0971877BDCB5A9FEF1C35F0897242BE75B51E4B12F30348BA4009F5B737F",
    "NumStability/Analysis.lean":
        "E7E0DA9DAA5C8E7EC88212BDF68B94A9F55FABBA09E65A23ADB6E7CB410ABD57",
    "docs/architecture/layout-exceptions.json":
        "FD58D44C5C9150A3EE2AC4007B4F1D4523735DAFD6CAE93B7D4538E796E96CE6",
    "tools/architecture/check_layout.py":
        "FDDED75CF63F0C59EA09E345E4062DBB55E99CA34ABC1289EB2AE5DEEFBF878D",
}
MATERIALIZATION_SHA256 = "05C738043A6D990B7E2BBBE9B200E2A4B54AB8B042AFE9A308A6ACD1FF71A5FA"
MATERIALIZATION_COUNTS = {
    "destinations": 30,
    "historical_wrappers_rewritten": 13,
    "historical_wrappers_unchanged": 32,
    "source_commands": 194,
    "tests": 102,
}
PROJECTED_CLASSIFICATION = {
    "production": 2860,
    "classified": 2770,
    "unclassified": 90,
    "mixed": 0,
}
PROJECTED_QUEUE = {"R09": 72, "R10": 18}
SHA256_RE = re.compile(r"[0-9A-F]{64}\Z")
WINDOWS_LEGACY_MAX_PATH = 260


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def rows(path: Path) -> list[dict[str, str]]:
    with path.open("r", encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def run(
    root: Path,
    command: list[str],
    *,
    check: bool = True,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command, cwd=root, check=check, text=True, encoding="utf-8", errors="strict",
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=env,
    )


def imports(path: Path) -> list[str]:
    return [line.split(None, 1)[1].strip() for line in path.read_text(encoding="utf-8-sig").splitlines()
            if line.lstrip().startswith("import ")]


def graph(repo: Path) -> tuple[dict[str, list[str]], set[tuple[str, str]]]:
    source_paths = list((repo / "NumStability").rglob("*.lean"))
    umbrella = repo / "NumStability.lean"
    if umbrella.is_file():
        source_paths.append(umbrella)
    paths = {
        path.relative_to(repo).as_posix()[:-5].replace("/", "."): path
        for path in source_paths
    }
    result: dict[str, list[str]] = {}
    unresolved: set[tuple[str, str]] = set()
    for module, path in paths.items():
        result[module] = []
        for target in imports(path):
            if target in paths:
                result[module].append(target)
            elif target == "NumStability" or target.startswith("NumStability."):
                unresolved.add((module, target))
    return result, unresolved


def reaches(g: dict[str, list[str]], start: str, targets: set[str]) -> bool:
    todo = list(g.get(start, []))
    seen: set[str] = set()
    while todo:
        current = todo.pop()
        if current in targets:
            return True
        if current not in seen:
            seen.add(current)
            todo.extend(g.get(current, []))
    return False


def checked_command(
    root: Path,
    command: list[str],
    label: str,
    failures: list[str],
    *,
    env: dict[str, str] | None = None,
) -> str:
    result = run(root, command, check=False, env=env)
    if result.returncode:
        failures.append(f"{label} failed ({result.returncode}):\n{result.stdout.rstrip()}")
    return result.stdout


def audit_windows_lake_output_paths(overlay: Path, failures: list[str]) -> None:
    """Keep Lake's longest atomic output path below legacy Windows MAX_PATH."""

    if os.name != "nt":
        return
    sources = list((overlay / "NumStability").rglob("*.lean"))
    sources.extend((overlay / "NumStabilityTest").rglob("*.lean"))
    for root_module in (overlay / "NumStability.lean", overlay / "NumStabilityTest.lean"):
        if root_module.is_file():
            sources.append(root_module)
    longest: tuple[int, Path] | None = None
    for source in sources:
        relative = source.relative_to(overlay).with_suffix("")
        output = overlay / ".lake" / "build" / "lib" / "lean" / relative
        # Lake/Lean use adjacent atomic files while publishing `.olean.hash`.
        # Reserve an eight-character nonce as well as the longest known suffix.
        candidate = Path(str(output) + ".olean.hash.tmp-XXXXXXXX")
        item = (len(str(candidate)), candidate)
        if longest is None or item[0] > longest[0]:
            longest = item
    if longest is not None and longest[0] >= WINDOWS_LEGACY_MAX_PATH:
        failures.append(
            "disposable Lake output may exceed Windows MAX_PATH: "
            f"length={longest[0]} path={longest[1]}"
        )


def audit_isolated_artifacts(overlay: Path, failures: list[str], stage: str) -> None:
    """Reject links, hardlinks, and special files in disposable Lake/cache trees."""

    try:
        overlay_real = overlay.resolve(strict=True)
    except OSError as error:
        failures.append(f"{stage}: cannot resolve disposable overlay: {error}")
        return
    reparse = getattr(stat, "FILE_ATTRIBUTE_REPARSE_POINT", 0)
    for relative in (Path(".lake"), Path(".cache")):
        root = overlay / relative
        if not os.path.lexists(root):
            continue
        pending = [root]
        while pending:
            current = pending.pop()
            try:
                info = os.lstat(current)
            except OSError as error:
                failures.append(f"{stage}: cannot lstat {current.relative_to(overlay)}: {error}")
                return
            attrs = getattr(info, "st_file_attributes", 0)
            if stat.S_ISLNK(info.st_mode) or (reparse and attrs & reparse):
                failures.append(
                    f"{stage}: disposable artifact is a link/reparse point: "
                    f"{current.relative_to(overlay)}"
                )
                return
            if not stat.S_ISDIR(info.st_mode):
                failures.append(
                    f"{stage}: disposable artifact root is not a directory: "
                    f"{current.relative_to(overlay)}"
                )
                return
            try:
                entries = list(os.scandir(current))
            except OSError as error:
                failures.append(f"{stage}: cannot scan {current.relative_to(overlay)}: {error}")
                return
            for entry in entries:
                path = Path(entry.path)
                try:
                    # On Windows, DirEntry.stat() can report st_nlink=0 even
                    # for ordinary files. os.lstat() performs the complete
                    # metadata query needed by the hardlink gate.
                    entry_info = os.lstat(path)
                except OSError as error:
                    failures.append(f"{stage}: cannot lstat {path.relative_to(overlay)}: {error}")
                    return
                entry_attrs = getattr(entry_info, "st_file_attributes", 0)
                if stat.S_ISLNK(entry_info.st_mode) or (reparse and entry_attrs & reparse):
                    failures.append(
                        f"{stage}: disposable artifact is a link/reparse point: "
                        f"{path.relative_to(overlay)}"
                    )
                    return
                if stat.S_ISDIR(entry_info.st_mode):
                    pending.append(path)
                elif stat.S_ISREG(entry_info.st_mode):
                    if entry_info.st_nlink != 1:
                        failures.append(
                            f"{stage}: disposable artifact has {entry_info.st_nlink} hard links: "
                            f"{path.relative_to(overlay)}"
                        )
                        return
                else:
                    failures.append(
                        f"{stage}: unsupported disposable artifact type: "
                        f"{path.relative_to(overlay)}"
                    )
                    return
        try:
            root.resolve(strict=True).relative_to(overlay_real)
        except (OSError, ValueError) as error:
            failures.append(f"{stage}: artifact root escapes overlay: {relative}: {error}")
            return


def canonical_relative(raw: object) -> Path:
    """Return a canonical, platform-safe relative path or reject it."""

    if not isinstance(raw, str) or not raw:
        raise ValueError("path must be a nonempty string")
    if "\\" in raw or "//" in raw:
        raise ValueError("path must use single forward-slash separators")
    pure = PurePosixPath(raw)
    if pure.is_absolute() or raw != pure.as_posix():
        raise ValueError("path is absolute or has a noncanonical spelling")
    if not pure.parts or any(part in {"", ".", ".."} for part in pure.parts):
        raise ValueError("path contains an empty, dot, or dot-dot component")
    if any(":" in part or part.rstrip(" .") != part for part in pure.parts):
        raise ValueError("path contains a platform alias component")
    native = Path(*pure.parts)
    if native.is_absolute() or native.drive or native.root:
        raise ValueError("path has a platform-specific root or drive")
    return native


def contained_path(root: Path, relative: Path, *, must_exist: bool) -> Path:
    resolved_root = root.resolve(strict=True)
    candidate = root.joinpath(*relative.parts)
    resolved = candidate.resolve(strict=must_exist)
    try:
        resolved.relative_to(resolved_root)
    except ValueError as error:
        raise ValueError(f"path escapes {resolved_root}") from error
    return candidate


def production_classification(repo: Path) -> tuple[dict[str, int], set[str]]:
    source_paths = [repo / "NumStability.lean"]
    source_paths.extend(sorted((repo / "NumStability").rglob("*.lean")))
    modules = {
        ".".join(path.relative_to(repo).with_suffix("").parts)
        for path in source_paths if path.is_file()
    }
    manifest = json.loads((repo / "docs/architecture/tiers.json").read_text(encoding="utf-8"))
    if manifest.get("schema_version") != 1:
        raise ValueError("tier manifest schema is not 1")
    tiers = manifest.get("tiers")
    exact = manifest.get("exact")
    prefixes = manifest.get("prefixes")
    if (
        not isinstance(tiers, list)
        or not all(isinstance(tier, str) for tier in tiers)
        or not isinstance(exact, dict)
        or not all(isinstance(name, str) and isinstance(tier, str) for name, tier in exact.items())
        or not isinstance(prefixes, list)
    ):
        raise ValueError("tier manifest has an invalid exact/prefix schema")
    allowed = set(tiers)
    parsed_prefixes: list[tuple[str, str]] = []
    for rule in prefixes:
        if not isinstance(rule, dict) or set(rule) != {"prefix", "tier"}:
            raise ValueError("tier manifest has a malformed prefix rule")
        prefix, tier = rule.get("prefix"), rule.get("tier")
        if not isinstance(prefix, str) or not isinstance(tier, str) or tier not in allowed:
            raise ValueError("tier manifest has an invalid prefix rule")
        parsed_prefixes.append((prefix.rstrip("."), tier))
    if any(tier not in allowed for tier in exact.values()):
        raise ValueError("tier manifest exact map uses an unknown tier")
    missing_exact = set(exact) - modules
    if missing_exact:
        raise ValueError(f"tier manifest names missing modules: {sorted(missing_exact)[:5]}")
    parsed_prefixes.sort(key=lambda item: (-len(item[0]), item[0]))
    assignment: dict[str, str] = {}
    for module in sorted(modules):
        if module in exact:
            assignment[module] = exact[module]
            continue
        for prefix, tier in parsed_prefixes:
            if module == prefix or module.startswith(prefix + "."):
                assignment[module] = tier
                break
    unclassified = modules - set(assignment)
    counts = Counter(assignment.values())
    return {
        "production": len(modules),
        "classified": len(assignment),
        "unclassified": len(unclassified),
        "mixed": counts["mixed"],
    }, unclassified


def prepare_isolated_lake_packages(repo: Path, overlay: Path, failures: list[str]) -> None:
    """Clone pinned dependency sources without caches or links to the live worker."""

    try:
        manifest = json.loads((overlay / "lake-manifest.json").read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        failures.append(f"cannot read disposable lake-manifest.json: {error}")
        return
    packages = manifest.get("packages")
    if manifest.get("packagesDir") != ".lake/packages" or not isinstance(packages, list):
        failures.append("disposable Lake manifest has an unexpected packagesDir/packages schema")
        return
    package_names: set[str] = set()
    package_specs: list[tuple[str, str]] = []
    for item in packages:
        if not isinstance(item, dict) or item.get("type") != "git":
            failures.append("disposable Lake manifest contains a non-git dependency")
            continue
        name, revision = item.get("name"), item.get("rev")
        if (
            not isinstance(name, str)
            or not isinstance(revision, str)
            or not re.fullmatch(r"[A-Za-z0-9_-]+", name)
            or not re.fullmatch(r"[0-9a-f]{40}", revision)
            or name.casefold() in package_names
        ):
            failures.append(f"invalid or duplicate Lake dependency identity: {name!r}")
            continue
        package_names.add(name.casefold())
        package_specs.append((name, revision))
    if failures:
        return

    live_packages = repo / ".lake" / "packages"
    disposable_packages = overlay / ".lake" / "packages"
    disposable_packages.mkdir(parents=True, exist_ok=False)
    for name, revision in package_specs:
        source = live_packages / name
        target = disposable_packages / name
        try:
            contained_path(repo, source.relative_to(repo), must_exist=True)
        except (OSError, ValueError) as error:
            failures.append(f"live dependency {name} is not contained in the worker: {error}")
            break
        head = run(source, ["git", "rev-parse", "HEAD"], check=False)
        if head.returncode or head.stdout.strip() != revision:
            failures.append(
                f"live dependency {name} is not at pinned revision {revision}: "
                f"{head.stdout.strip() or 'git failure'}"
            )
            break
        clone = run(
            disposable_packages,
            ["git", "clone", "--quiet", "--local", "--no-hardlinks", "--no-checkout", str(source), str(target)],
            check=False,
        )
        if clone.returncode:
            failures.append(f"isolated clone of dependency {name} failed:\n{clone.stdout.rstrip()}")
            break
        alternates = target / ".git" / "objects" / "info" / "alternates"
        if alternates.exists():
            failures.append(f"isolated clone of dependency {name} retained object alternates")
            break
        run(target, ["git", "config", "core.autocrlf", "false"])
        checkout = run(target, ["git", "checkout", "--quiet", "--detach", revision], check=False)
        if checkout.returncode:
            failures.append(f"isolated checkout of dependency {name} failed:\n{checkout.stdout.rstrip()}")
            break

    if failures:
        return
    audit_isolated_artifacts(overlay, failures, "post-clone")


def main() -> int:
    for stream in (sys.stdout, sys.stderr):
        reconfigure = getattr(stream, "reconfigure", None)
        if callable(reconfigure):
            reconfigure(encoding="utf-8", errors="strict")
    parser = argparse.ArgumentParser()
    parser.add_argument("--control-root", type=Path, required=True)
    parser.add_argument("--full", action="store_true", help="run layout, compatibility, provenance, and strict-source in the overlay")
    parser.add_argument("--full-build", action="store_true", help="also run the full Lake build and test gates in the disposable clone")
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[4]
    control = args.control_root.resolve()
    failures: list[str] = []
    if run(control, ["git", "rev-parse", "HEAD"]).stdout.strip() != CONTROL_HEAD:
        failures.append("control checkout is not the activated R07 control commit")
    control_status = run(
        control,
        ["git", "status", "--porcelain=v1", "--untracked-files=all"],
        check=False,
    )
    if control_status.returncode:
        failures.append("cannot determine activated control checkout cleanliness")
    elif control_status.stdout:
        failures.append(
            "activated control checkout is not clean:\n" + control_status.stdout.rstrip()
        )

    artifacts = {
        "request_json": control / REQUEST / "R0011.json",
        "patch": control / REQUEST / "R0011.patch",
        "postimages": control / REQUEST / "R0011-postimages.tsv",
        "imports": control / REQUEST / "R0011-import-manifest.tsv",
        "plan": control / REQUEST / "R0011-request-plan.tsv",
        "paths": control / PHASE / "branches" / "B0010-shared-request-paths.txt",
        "renderer": control / "tools/architecture/r07_shared_postimages.py",
        "compatibility": control / PHASE / "reviews" / "R07-COMPATIBILITY-postimage.md",
        "baseline": control / PHASE / "baselines" / "C0005-combined.json",
        "module_routes": control / PHASE / "branches" / "B0010-module-routes.tsv",
        "destinations": control / PHASE / "branches" / "B0010-destinations.tsv",
        "planned_contract": control / PHASE / "reviews" / "R07-planned-control-contract.json",
        "scope": control / PHASE / "scope.tsv",
    }
    for name, path in artifacts.items():
        actual = sha(path) if path.is_file() else "MISSING"
        if actual != EXPECTED[name]:
            failures.append(f"control {name} hash {actual}, expected {EXPECTED[name]}")

    materialization_path = repo / DELIVERY / "MATERIALIZATION.json"
    materialization_actual = sha(materialization_path) if materialization_path.is_file() else "MISSING"
    if materialization_actual != MATERIALIZATION_SHA256:
        failures.append(
            f"MATERIALIZATION.json hash {materialization_actual}, expected {MATERIALIZATION_SHA256}"
        )
    correction_path = repo / CORRECTION_PATH
    correction_actual = sha(correction_path) if correction_path.is_file() else "MISSING"
    if correction_actual != CORRECTION_SHA256:
        failures.append(
            f"R0011 correction hash {correction_actual}, expected {CORRECTION_SHA256}"
        )
    else:
        correction_text = correction_path.read_text(encoding="utf-8")
        correction_paths = {
            match.group(1)
            for match in re.finditer(r"(?m)^diff --git a/(\S+) b/\1$", correction_text)
        }
        if correction_paths != set(CORRECTED_POSTIMAGES) or correction_text.count("diff --git ") != 4:
            failures.append("R0011 correction does not contain exactly its four reviewed paths")
    if failures:
        print("R0011 preflight FAILED")
        for failure in failures:
            print(f"- {failure}")
        return 1

    materialization = json.loads(materialization_path.read_text(encoding="utf-8"))
    expected_materialization_keys = {
        "base_code_sha", "control_head_sha", "counts", "files", "record_kind", "schema_version",
    }
    if not isinstance(materialization, dict) or set(materialization) != expected_materialization_keys:
        failures.append("MATERIALIZATION.json does not have the exact schema-1 top-level fields")
    if (
        materialization.get("schema_version") != 1
        or materialization.get("record_kind") != "r07_worker_materialization"
        or materialization.get("base_code_sha") != BASE
        or materialization.get("control_head_sha") != CONTROL_HEAD
        or materialization.get("counts") != MATERIALIZATION_COUNTS
    ):
        failures.append("MATERIALIZATION.json schema/base/control/counts do not match the frozen contract")

    materialized_items = materialization.get("files")
    worker_files: list[tuple[str, Path, str]] = []
    materialized_paths: set[str] = set()
    materialized_aliases: set[str] = set()
    if not isinstance(materialized_items, list) or len(materialized_items) != 145:
        failures.append("MATERIALIZATION.json must contain exactly 145 file records")
    else:
        raw_order: list[str] = []
        for index, item in enumerate(materialized_items):
            if not isinstance(item, dict) or set(item) != {"path", "sha256"}:
                failures.append(f"materialization file record {index} has an invalid schema")
                continue
            raw_path, expected_hash = item.get("path"), item.get("sha256")
            try:
                relative = canonical_relative(raw_path)
            except ValueError as error:
                failures.append(f"materialization path {raw_path!r} is not canonical: {error}")
                continue
            assert isinstance(raw_path, str)
            alias = raw_path.casefold()
            if raw_path in materialized_paths or alias in materialized_aliases:
                failures.append(f"duplicate/aliased materialization path: {raw_path}")
                continue
            materialized_paths.add(raw_path)
            materialized_aliases.add(alias)
            raw_order.append(raw_path)
            if not isinstance(expected_hash, str) or not SHA256_RE.fullmatch(expected_hash):
                failures.append(f"materialization hash for {raw_path} is not canonical SHA-256")
                continue
            try:
                source = contained_path(repo, relative, must_exist=True)
            except (OSError, ValueError) as error:
                failures.append(f"materialized worker file {raw_path} is not contained: {error}")
                continue
            if not source.is_file():
                failures.append(f"materialized worker path is not a file: {raw_path}")
                continue
            actual_hash = sha(source)
            if actual_hash != expected_hash:
                failures.append(
                    f"live worker hash mismatch before replay {raw_path}: "
                    f"{actual_hash}, expected {expected_hash}"
                )
                continue
            worker_files.append((raw_path, relative, expected_hash))
        if raw_order != sorted(raw_order):
            failures.append("MATERIALIZATION.json file records are not in canonical sorted order")
    if len(materialized_paths) != 145 or len(worker_files) != 145:
        failures.append(
            f"MATERIALIZATION.json yielded {len(materialized_paths)} unique paths and "
            f"{len(worker_files)} authenticated live files, expected 145/145"
        )

    request = json.loads(artifacts["request_json"].read_text(encoding="utf-8"))
    raw_request_paths = request.get("paths") if isinstance(request, dict) else None
    request_paths: set[str] = set()
    request_aliases: set[str] = set()
    if not isinstance(raw_request_paths, list) or len(raw_request_paths) != 46:
        failures.append("R0011 request must contain exactly 46 paths")
    else:
        for raw_path in raw_request_paths:
            try:
                canonical_relative(raw_path)
            except ValueError as error:
                failures.append(f"R0011 request path {raw_path!r} is not canonical: {error}")
                continue
            assert isinstance(raw_path, str)
            request_paths.add(raw_path)
            request_aliases.add(raw_path.casefold())
        if len(request_paths) != 46 or len(request_aliases) != 46:
            failures.append("R0011 request paths are not exactly 46 unique canonical paths")
    overlap = materialized_paths & request_paths
    alias_overlap = materialized_aliases & request_aliases
    if overlap or alias_overlap:
        failures.append(f"request/worker scope overlap: {sorted(materialized_paths & request_paths)}")
    ledger = rows(artifacts["postimages"])
    if (
        len(ledger) != 46
        or {row.get("path") for row in ledger} != request_paths
        or any(not isinstance(row.get("postimage_sha256"), str)
               or not SHA256_RE.fullmatch(row["postimage_sha256"]) for row in ledger)
    ):
        failures.append("R0011 postimage ledger does not cover exactly 46 request paths")
    request_plan = rows(artifacts["plan"])
    if len(request_plan) != 46 or {row.get("path") for row in request_plan} != request_paths:
        failures.append("R0011 request plan does not have exactly 46 rows")

    baseline = json.loads(artifacts["baseline"].read_text(encoding="utf-8"))
    baseline_source = baseline.get("source", {})
    baseline_audit = baseline_source.get("tier_audit", {})
    baseline_tier_counts = baseline_audit.get("module_counts_by_tier", {})
    baseline_classification = {
        "production": baseline_source.get("module_count"),
        "classified": baseline_audit.get("classified_module_count"),
        "unclassified": baseline_audit.get("unclassified_module_count"),
        "mixed": baseline_tier_counts.get("mixed"),
    }
    if (
        baseline.get("schema_version") != 1
        or baseline.get("metadata", {}).get("commit") != BASE
        or baseline_classification != {
            "production": 2818, "classified": 2685, "unclassified": 133, "mixed": 0,
        }
    ):
        failures.append(f"authenticated C0005 classification is invalid: {baseline_classification}")
    baseline_unclassified = baseline_audit.get("unclassified_modules")
    if not isinstance(baseline_unclassified, list) or len(set(baseline_unclassified)) != 133:
        failures.append("authenticated C0005 unclassified module list is not an exact 133-set")
        baseline_unclassified_set: set[str] = set()
    else:
        baseline_unclassified_set = set(baseline_unclassified)

    module_routes = rows(artifacts["module_routes"])
    route_owners = {row.get("owner_module") for row in module_routes}
    r07_unclassified = {
        row.get("owner_module") for row in module_routes if row.get("current_tier") == "unclassified"
    }
    if (
        len(module_routes) != 45
        or len(route_owners) != 45
        or len(r07_unclassified) != 43
        or Counter(row.get("current_tier") for row in module_routes)
        != Counter({"unclassified": 43, "reusable": 2})
        or any(row.get("review_status") != "reviewed" for row in module_routes)
    ):
        failures.append("authenticated B0010 module routes do not bind 43 unclassified + 2 naming owners")
    if not r07_unclassified <= baseline_unclassified_set:
        failures.append("B0010 unclassified owners are not a subset of the C0005 unclassified set")

    destinations = rows(artifacts["destinations"])
    destination_modules = {row.get("module") for row in destinations}
    if (
        len(destinations) != 30
        or len(destination_modules) != 30
        or Counter(row.get("tier") for row in destinations)
        != Counter({"reusable": 26, "internal": 3, "source": 1})
    ):
        failures.append("authenticated B0010 destinations are not the exact 30 non-mixed modules")
    created_aggregates = [
        row for row in request_plan if row.get("transform") == "create_public_family_aggregate"
    ]
    if len(created_aggregates) != 12 or any(row.get("base_blob_oid") != "-" for row in created_aggregates):
        failures.append("authenticated R0011 plan does not create exactly 12 public family aggregates")

    planned_contract = json.loads(artifacts["planned_contract"].read_text(encoding="utf-8"))
    if (
        planned_contract.get("schema_version") != 1
        or planned_contract.get("record_kind") != "r07_planned_control_contract"
        or planned_contract.get("base_checkpoint_id") != "C0005"
        or planned_contract.get("base_code_sha") != BASE
        or planned_contract.get("projection_id") != "P0010"
        or planned_contract.get("wave_id") != "R07"
        or planned_contract.get("projected_remaining_queue") != PROJECTED_QUEUE
    ):
        failures.append("authenticated R07 planned-control contract has invalid identity or queue")

    expected_remaining = baseline_unclassified_set - r07_unclassified
    scope_rows = rows(artifacts["scope"])
    queue_modules: dict[str, set[str]] = {}
    for wave in PROJECTED_QUEUE:
        queue_modules[wave] = {
            row.get("module") for row in scope_rows
            if row.get("wave_id") == wave and row.get("current_tier") == "unclassified"
        }
    authenticated_queue = {wave: len(modules) for wave, modules in queue_modules.items()}
    if (
        authenticated_queue != PROJECTED_QUEUE
        or set().union(*queue_modules.values()) != expected_remaining
        or queue_modules["R09"] & queue_modules["R10"]
    ):
        failures.append(
            f"authenticated residual scope does not partition the projected queue: {authenticated_queue}"
        )

    derived_classification = {
        "production": baseline_classification["production"] + len(destinations) + len(created_aggregates),
        "classified": baseline_classification["classified"] + len(r07_unclassified)
        + len(destinations) + len(created_aggregates),
        "unclassified": baseline_classification["unclassified"] - len(r07_unclassified),
        "mixed": baseline_classification["mixed"],
    }
    if derived_classification != PROJECTED_CLASSIFICATION:
        failures.append(
            f"authenticated controls derive classification {derived_classification}, "
            f"expected {PROJECTED_CLASSIFICATION}"
        )

    if not failures:
        renderer = run(
            control,
            [sys.executable, "-B", str(artifacts["renderer"]), "--check",
             "--compatibility-postimage", str(artifacts["compatibility"])],
            check=False,
        )
        if renderer.returncode:
            failures.append("R0011 renderer replay failed:\n" + renderer.stdout.rstrip())
        else:
            try:
                rendered = json.loads(renderer.stdout)
            except json.JSONDecodeError as error:
                failures.append(f"R0011 renderer did not return JSON: {error}")
            else:
                expected_render = {
                    "status": "ready", "base_checkpoint_id": "C0005", "base_sha": BASE,
                    "path_count": 46, "path_list_sha256": EXPECTED["paths"],
                    "patch_sha256": EXPECTED["patch"],
                    "postimage_ledger_sha256": EXPECTED["postimages"],
                    "import_manifest_sha256": EXPECTED["imports"],
                    "request_plan_sha256": EXPECTED["plan"], "forward_tree": FORWARD_TREE,
                }
                for key, value in expected_render.items():
                    if rendered.get(key) != value:
                        failures.append(f"renderer {key}={rendered.get(key)!r}, expected {value!r}")

    if failures:
        print("R0011 preflight FAILED")
        for failure in failures:
            print(f"- {failure}")
        return 1

    # The short disposable names are part of the Windows gate contract: the
    # longest R03/R07/R11 test module otherwise crosses MAX_PATH while Lake
    # publishes its adjacent `.olean.hash` temporary file.
    with tempfile.TemporaryDirectory(prefix="r7-") as temporary:
        overlay = Path(temporary) / "o"
        clone = run(
            Path(temporary),
            ["git", "clone", "--quiet", "--local", "--no-hardlinks", "--no-checkout",
             str(repo), str(overlay)],
            check=False,
        )
        if clone.returncode:
            print("R0011 replay FAILED\n- local clone failed:\n" + clone.stdout)
            return 1
        if (overlay / ".git/objects/info/alternates").exists():
            print("R0011 replay FAILED\n- disposable clone retained object alternates")
            return 1
        run(overlay, ["git", "config", "core.autocrlf", "false"])
        run(overlay, ["git", "config", "core.eol", "lf"])
        run(overlay, ["git", "checkout", "--quiet", "--detach", BASE])
        patch = artifacts["patch"]
        checked_command(overlay, ["git", "apply", "--unidiff-zero", "--check", str(patch)], "forward patch check", failures)
        if not failures:
            checked_command(overlay, ["git", "apply", "--unidiff-zero", "--index", str(patch)], "forward patch apply", failures)
        if not failures:
            tree = run(overlay, ["git", "write-tree"]).stdout.strip()
            if tree != FORWARD_TREE:
                failures.append(f"forward tree {tree}, expected {FORWARD_TREE}")
            for row in ledger:
                path = overlay / row["path"]
                actual = sha(path) if path.is_file() else "MISSING"
                if actual != row["postimage_sha256"]:
                    failures.append(f"postimage mismatch after apply {row['path']}: {actual}")
        if not failures:
            checked_command(overlay, ["git", "apply", "--unidiff-zero", "--reverse", "--check", str(patch)], "reverse patch check", failures)
            checked_command(overlay, ["git", "apply", "--unidiff-zero", "--reverse", "--index", str(patch)], "reverse patch apply", failures)
        if not failures:
            base_tree = run(overlay, ["git", "rev-parse", f"{BASE}^{{tree}}"]).stdout.strip()
            if run(overlay, ["git", "write-tree"]).stdout.strip() != base_tree:
                failures.append("reverse replay did not reproduce exact base tree")
            if run(overlay, ["git", "status", "--porcelain=v1"]).stdout:
                failures.append("reverse replay left a dirty disposable tree")
        if not failures:
            checked_command(overlay, ["git", "apply", "--unidiff-zero", "--index", str(patch)], "second forward patch apply", failures)
        if not failures:
            checked_command(
                overlay,
                ["git", "apply", "--unidiff-zero", "--check", str(correction_path)],
                "integrator correction check",
                failures,
            )
        if not failures:
            checked_command(
                overlay,
                ["git", "apply", "--unidiff-zero", "--index", str(correction_path)],
                "integrator correction apply",
                failures,
            )
        if not failures:
            corrected_tree = run(overlay, ["git", "write-tree"]).stdout.strip()
            if corrected_tree != CORRECTED_TREE:
                failures.append(
                    f"corrected integrator tree {corrected_tree}, expected {CORRECTED_TREE}"
                )
            for path, expected_hash in CORRECTED_POSTIMAGES.items():
                actual = sha(overlay / path) if (overlay / path).is_file() else "MISSING"
                if actual != expected_hash:
                    failures.append(f"corrected postimage mismatch {path}: {actual}")
        if not failures:
            for raw_path, relative, expected_hash in worker_files:
                source = contained_path(repo, relative, must_exist=True)
                target = contained_path(overlay, relative, must_exist=False)
                actual_source_hash = sha(source) if source.is_file() else "MISSING"
                if actual_source_hash != expected_hash:
                    failures.append(
                        f"live worker hash changed before copy {raw_path}: "
                        f"{actual_source_hash}, expected {expected_hash}"
                    )
                    break
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source, target)
                if sha(target) != expected_hash:
                    failures.append(f"worker overlay copy mismatch: {raw_path}")
                    break
            if not failures:
                for row in ledger:
                    path = overlay / row["path"]
                    actual = sha(path) if path.is_file() else "MISSING"
                    expected_hash = CORRECTED_POSTIMAGES.get(
                        row["path"], row["postimage_sha256"]
                    )
                    if actual != expected_hash:
                        failures.append(
                            f"R0011 postimage changed after worker overlay copy {row['path']}: {actual}"
                        )
            if not failures:
                run(overlay, ["git", "add", "-A"])

        if not failures:
            g, unresolved_project_imports = graph(overlay)
            if unresolved_project_imports:
                failures.append(
                    "overlay has unresolved NumStability imports: "
                    + repr(sorted(unresolved_project_imports)[:20])
                )
            branch_dir = control / PHASE / "branches"
            owners = {row["owner_module"] for row in rows(branch_dir / "B0010-module-routes.tsv")}
            destinations = rows(branch_dir / "B0010-destinations.tsv")
            destination_modules = {row["module"] for row in destinations}
            backreach = {module for module in destination_modules if reaches(g, module, owners)}
            if backreach:
                failures.append("overlay canonical destinations reach historical owners: " + repr(sorted(backreach)))
            source = {module for module in g if module.startswith("NumStability.Source.")}
            bad_source = {
                row["module"] for row in destinations
                if row["tier"] in {"reusable", "internal"} and reaches(g, row["module"], source)
            }
            if bad_source:
                failures.append("overlay reusable/internal destinations reach Source: " + repr(sorted(bad_source)))

            tiers = json.loads((overlay / "docs/architecture/tiers.json").read_text(encoding="utf-8"))
            tier_counts = Counter(tiers["exact"].values())
            expected_tiers = Counter({
                "aggregate": 395, "compatibility": 622, "internal": 5,
                "reusable": 425, "source": 448,
            })
            if len(tiers["exact"]) != 1895 or len(tiers["prefixes"]) != 27 or tier_counts != expected_tiers:
                failures.append(f"overlay tier counts drifted: exact={len(tiers['exact'])}, prefixes={len(tiers['prefixes'])}, counts={dict(tier_counts)}")
            test_import_count = len(imports(overlay / "NumStabilityTest.lean"))
            if test_import_count != 573:
                failures.append(f"overlay NumStabilityTest.lean direct imports={test_import_count}, expected 573")
            try:
                actual_classification, actual_unclassified = production_classification(overlay)
            except (OSError, ValueError, json.JSONDecodeError) as error:
                failures.append(f"cannot validate overlay production classification: {error}")
            else:
                if actual_classification != PROJECTED_CLASSIFICATION:
                    failures.append(
                        f"overlay production classification={actual_classification}, "
                        f"expected {PROJECTED_CLASSIFICATION}"
                    )
                if actual_unclassified != expected_remaining:
                    failures.append(
                        "overlay unclassified set is not the authenticated R09/R10 residual partition"
                    )

        if args.full and not failures:
            commands = [
                ([sys.executable, "-B", "tools/architecture/check_layout.py"], "layout"),
                ([sys.executable, "-B", "tools/architecture/check_compatibility.py"], "compatibility"),
                ([sys.executable, "-B", "tools/architecture/check_provenance.py"], "provenance"),
                ([sys.executable, "-B", "tools/architecture/generate_baseline.py", "--skip-declarations",
                  "--strict-source", "--output-dir", "benchmark-results/architecture",
                  "--name", "r07-request-overlay"], "strict-source baseline"),
            ]
            for command, label in commands:
                output = checked_command(overlay, command, label, failures)
                if output:
                    print(f"[{label}]\n{output.rstrip()}")
        if args.full_build and not failures:
            audit_windows_lake_output_paths(overlay, failures)
        if args.full_build and not failures:
            prepare_isolated_lake_packages(repo, overlay, failures)
            build_env = os.environ.copy()
            for variable in (
                "LEAN_PATH",
                "LEAN_SRC_PATH",
                "LAKE_PACKAGES_DIR",
                "LAKE_BUILD_DIR",
                "MATHLIB_CACHE_GET_URL",
                "MATHLIB_CACHE_USE_CLOUDFLARE",
                "MATHLIB_CACHE_PUT_URL",
                "MATHLIB_CACHE_S3_TOKEN",
                "MATHLIB_CACHE_SAS",
            ):
                build_env.pop(variable, None)
            build_env["XDG_CACHE_HOME"] = str(overlay / ".cache")
            build_env["MATHLIB_CACHE_DIR"] = str(overlay / ".cache" / "mathlib")
            if not failures:
                output = checked_command(
                    overlay,
                    ["lake", "exe", "cache", "get", "--repo=leanprover-community/mathlib4"],
                    "isolated mathlib cache fetch",
                    failures,
                    env=build_env,
                )
                if output:
                    print(f"[isolated mathlib cache fetch]\n{output.rstrip()}")
            if not failures:
                audit_isolated_artifacts(overlay, failures, "post-cache")
            for command, label in [
                (["lake", "build", "NumStability", "NumStabilityTest"], "full build"),
                (["lake", "test"], "lake test"),
            ]:
                if not failures:
                    output = checked_command(overlay, command, label, failures, env=build_env)
                    if output:
                        print(f"[{label}]\n{output.rstrip()}")
            if not failures:
                audit_isolated_artifacts(overlay, failures, "post-build")

    if failures:
        print("R0011 disposable overlay replay FAILED")
        for failure in failures:
            print(f"- {failure}")
        return 1
    print("R0011 disposable overlay replay passed")
    print(
        f"request_paths=46 forward_tree={FORWARD_TREE} reverse_tree=exact-base "
        f"correction_paths=4 corrected_tree={CORRECTED_TREE}"
    )
    print("worker_overlap=0 canonical_historical_reach=0 reusable_internal_source_reach=0")
    print("tiers_exact=1895 prefixes=27 test_root_imports=573")
    print("production=2860 classified=2770 unclassified=90 mixed=0")
    print("authenticated_projected_queue=R09:72,R10:18")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
