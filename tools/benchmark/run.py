#!/usr/bin/env python3
"""Measure reproducible clean, warm, incremental and test-driver profiles (EVID-01).

Standard library only. Results and complete Lake logs are written below
``benchmark-results/``.

The measured sequence is fixed, so two runs are comparable:

  1. tracked-clean assertion, staged and unstaged proven separately;
  2. root-package-clean build of the declared targets;
  3. immediate warm build;
  4. up-to-date incremental baseline;
  5. reusable-scenario comment edit, then verified byte-for-byte restore;
  6. fresh up-to-date baseline;
  7. source-scenario comment edit, then verified byte-for-byte restore;
  8. explicit `lake test`, which compiling the test library can never replace;
  9. final tracked-clean assertion.

Cache policy: `lake clean <package>` removes only root-package build output and
retains the pinned dependency checkout under `.lake/packages`, which is never
deleted by this protocol. The policy is recorded in the summary rather than
implied.

Resource fields the platform does not expose are recorded as ``null`` with a
reason, never silently omitted.

usage:
  python tools/benchmark/run.py [--mode all|clean|warm|incremental|test]
  python tools/benchmark/run.py --self-test
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import platform
import shlex
import shutil
import subprocess
import sys
import time
from typing import Any

ROOT = Path(__file__).resolve().parents[2]

# Scenario roles, per EVID-01. The `source` role deliberately edits the
# CANONICAL chapter module: the historical path
# `NumStability/Higham/Chapter02/Problem04.lean` is a compatibility forwarder,
# so an incremental edit there measures a two-line stub instead of a source
# module and its dependents.
DEFAULT_SCENARIOS = {
    "reusable": Path("NumStability/FloatingPoint/Model.lean"),
    "source": Path("NumStability/Source/Higham/Chapter02/Problem04.lean"),
}
# Pinned at the post-M13 candidate. A mismatch means the scenario file changed
# and the profile is not comparable with earlier records.
SCENARIO_SHA256 = {
    "reusable": "19b3c29688f19f6de78f71c2bd82ebfb85914ae51048eae322f4a23020551423",
    "source": "f607e91336d6bde583868fdb6f7ea9c070f88ad1915092531bc28b137089fde9",
}
CACHE_POLICY = (
    "lake clean <package> removes root-package build output only; the pinned "
    "dependency checkout under .lake/packages is retained and never deleted by "
    "this protocol"
)


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("all", "clean", "warm", "incremental", "test"),
                        default="all", help="benchmark mode (default: all)")
    parser.add_argument("--target", action="append", dest="targets",
                        help="Lake build target; repeat for multiple targets")
    parser.add_argument("--package", default="numStability",
                        help="root package passed to `lake clean` (default: numStability)")
    parser.add_argument("--scenario", action="append", metavar="NAME=PATH",
                        help="incremental edit scenario; repeat to replace the defaults")
    parser.add_argument("--results-dir", type=Path,
                        help="output directory (default: benchmark-results/<UTC timestamp>)")
    parser.add_argument("--allow-dirty-scenarios", action="store_true",
                        help="allow a scenario file with Git changes; disqualifies the "
                             "record as acceptance evidence")
    parser.add_argument("--skip-pin-check", action="store_true",
                        help="do not require the pinned scenario digests; disqualifies the "
                             "record as acceptance evidence")
    parser.add_argument("--keep-going", action="store_true",
                        help="continue after a failed measured command")
    parser.add_argument("--self-test", action="store_true",
                        help="check the runner's own invariants and exit")
    return parser.parse_args(argv)


def capture(command: list[str]) -> str:
    completed = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, check=False)
    return completed.stdout.strip()


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def tracked_clean() -> dict[str, Any]:
    """Prove zero unstaged and zero staged tracked changes, separately."""
    unstaged = subprocess.run(["git", "diff", "--quiet"], cwd=ROOT, check=False).returncode
    staged = subprocess.run(["git", "diff", "--cached", "--quiet"], cwd=ROOT, check=False).returncode
    return {
        "unstaged_tracked_changes": unstaged != 0,
        "staged_tracked_changes": staged != 0,
        "clean": unstaged == 0 and staged == 0,
        "porcelain": capture(["git", "status", "--porcelain"]),
    }


def physical_memory_bytes() -> tuple[int | None, str | None]:
    if hasattr(os, "sysconf") and "SC_PAGE_SIZE" in os.sysconf_names and "SC_PHYS_PAGES" in os.sysconf_names:
        try:
            return os.sysconf("SC_PAGE_SIZE") * os.sysconf("SC_PHYS_PAGES"), None
        except (OSError, ValueError):
            pass
    if sys.platform == "win32":
        out = capture(["powershell.exe", "-NoProfile", "-Command",
                       "(Get-CimInstance Win32_ComputerSystem).TotalPhysicalMemory"])
        digits = "".join(ch for ch in out if ch.isdigit())
        if digits:
            return int(digits), None
        return None, "TotalPhysicalMemory query returned no value"
    return None, f"no stdlib physical-memory source on platform {sys.platform}"


def peak_rss_bytes() -> tuple[int | None, str | None]:
    """Peak RSS of child processes, where the platform exposes it."""
    try:
        import resource  # POSIX only
    except ImportError:
        return None, (f"peak RSS unavailable: platform {sys.platform} has no `resource` "
                      "module and the runner is standard-library only")
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    scale = 1 if sys.platform == "darwin" else 1024
    return int(usage.ru_maxrss) * scale, None


def dependency_revisions() -> list[dict[str, Any]]:
    manifest = ROOT / "lake-manifest.json"
    if not manifest.is_file():
        return []
    doc = json.loads(manifest.read_text(encoding="utf-8"))
    return [{"name": p.get("name"), "rev": p.get("rev"), "inherited": p.get("inherited"),
             "input_rev": p.get("inputRev")} for p in doc.get("packages", [])]


def parse_scenarios(values: list[str] | None) -> dict[str, Path]:
    if not values:
        return dict(DEFAULT_SCENARIOS)
    scenarios: dict[str, Path] = {}
    for value in values:
        name, separator, raw_path = value.partition("=")
        if not separator or not name or not raw_path:
            raise ValueError(f"invalid scenario {value!r}; expected NAME=PATH")
        if name in scenarios:
            raise ValueError(f"duplicate scenario name: {name}")
        scenarios[name] = Path(raw_path)
    return scenarios


class BenchmarkRunner:
    def __init__(self, args: argparse.Namespace, results_dir: Path) -> None:
        self.args = args
        self.results_dir = results_dir
        self.results: list[dict[str, Any]] = []
        self.targets = args.targets or ["NumStability", "NumStabilityTest"]
        self.restores: list[dict[str, Any]] = []

    def run_command(self, label: str, command: list[str], *, measured: bool = True) -> dict[str, Any]:
        log_path = self.results_dir / f"{label}.log"
        try:
            displayed_log = str(log_path.relative_to(ROOT))
        except ValueError:
            displayed_log = str(log_path)
        printable = shlex.join(command)
        print(f"[{label}] {printable}", flush=True)
        started_wall = dt.datetime.now(dt.timezone.utc).isoformat()
        started = time.perf_counter()
        with log_path.open("w", encoding="utf-8", newline="") as log:
            log.write(f"$ {printable}\n\n")
            completed = subprocess.run(command, cwd=ROOT, stdout=log,
                                       stderr=subprocess.STDOUT, check=False)
        elapsed = time.perf_counter() - started
        finished_wall = dt.datetime.now(dt.timezone.utc).isoformat()
        rss, rss_reason = peak_rss_bytes()
        result = {
            "label": label,
            "command": command,
            "seconds": round(elapsed, 3),
            "started_at_utc": started_wall,
            "finished_at_utc": finished_wall,
            "exit_code": completed.returncode,
            "measured": measured,
            "log": displayed_log,
            "peak_rss_bytes_cumulative": rss,
            "peak_rss_unavailable_reason": rss_reason,
        }
        self.results.append(result)
        print(f"[{label}] exit={completed.returncode} elapsed={elapsed:.3f}s", flush=True)
        if completed.returncode != 0 and not self.args.keep_going:
            raise RuntimeError(f"{label} failed; see {log_path}")
        return result

    def build(self, label: str, *, measured: bool = True) -> dict[str, Any]:
        return self.run_command(label, ["lake", "build", *self.targets], measured=measured)

    def clean(self) -> None:
        self.run_command("clean-reset", ["lake", "clean", self.args.package], measured=False)
        self.build("clean-build")

    def warm(self) -> None:
        self.build("warm-build")

    def test(self) -> None:
        # The declared test driver, run explicitly. Compiling NumStabilityTest is
        # compilation evidence and can never substitute for executing `lake test`.
        self.run_command("test-driver", ["lake", "test"])

    def check_scenario_path(self, name: str, relative_path: Path) -> Path:
        source = (ROOT / relative_path).resolve()
        try:
            source.relative_to(ROOT)
        except ValueError as error:
            raise ValueError(f"scenario path escapes repository: {relative_path}") from error
        if not source.is_file() or source.suffix != ".lean":
            raise ValueError(f"scenario is not a Lean source file: {relative_path}")
        if not self.args.allow_dirty_scenarios:
            status = capture(["git", "status", "--porcelain", "--", str(relative_path)])
            if status:
                raise ValueError(
                    f"scenario file has Git changes: {relative_path}; commit or stash them, "
                    "or pass --allow-dirty-scenarios and accept that the record is not "
                    "acceptance evidence"
                )
        expected = SCENARIO_SHA256.get(name)
        if expected and not self.args.skip_pin_check:
            actual = sha256_file(source)
            if actual != expected:
                raise ValueError(
                    f"scenario {name} digest {actual} does not match the pinned {expected}; "
                    "the file changed, so this profile is not comparable with earlier records"
                )
        return source

    def incremental(self, scenarios: dict[str, Path]) -> None:
        for name, relative_path in scenarios.items():
            # A fresh up-to-date baseline before each edit, so each incremental
            # figure measures one edit rather than the tail of the previous one.
            self.build(f"incremental-baseline-{name}", measured=False)
            source = self.check_scenario_path(name, relative_path)
            original = source.read_bytes()
            before_digest = hashlib.sha256(original).hexdigest()
            original_stat = source.stat()
            marker = f"\n-- benchmark-only edit ({name}); restored automatically\n".encode("utf-8")
            try:
                source.write_bytes(original + marker)
                self.build(f"incremental-{name}")
            finally:
                source.write_bytes(original)
                os.utime(source, ns=(original_stat.st_atime_ns, original_stat.st_mtime_ns))
                after_digest = sha256_file(source)
                record = {
                    "scenario": name,
                    "path": str(relative_path),
                    "digest_before": before_digest,
                    "digest_after": after_digest,
                    "restored_byte_for_byte": before_digest == after_digest,
                }
                self.restores.append(record)
                if before_digest != after_digest:
                    raise RuntimeError(
                        f"scenario {name} was not restored byte for byte: "
                        f"{before_digest} became {after_digest}"
                    )
                self.build(f"restore-{name}", measured=False)


def self_test() -> list[str]:
    problems: list[str] = []
    if set(DEFAULT_SCENARIOS) != set(SCENARIO_SHA256):
        problems.append("every default scenario must carry a pinned digest")
    source_path = DEFAULT_SCENARIOS.get("source")
    if source_path is None or "Source" not in source_path.parts:
        problems.append("the source scenario must edit a canonical Source module, "
                        "not a historical compatibility forwarder")
    for name, relative in DEFAULT_SCENARIOS.items():
        path = ROOT / relative
        if not path.is_file():
            problems.append(f"scenario {name} file is missing: {relative}")
            continue
        actual = sha256_file(path)
        if actual != SCENARIO_SHA256[name]:
            problems.append(f"scenario {name} digest {actual} does not match its pin")
    try:
        parse_scenarios(["bad"])
    except ValueError:
        pass
    else:
        problems.append("a malformed --scenario value must be rejected")
    try:
        parse_scenarios(["a=x", "a=y"])
    except ValueError:
        pass
    else:
        problems.append("a duplicate scenario name must be rejected")
    memory, memory_reason = physical_memory_bytes()
    if memory is None and not memory_reason:
        problems.append("an unavailable resource field must carry a reason")
    rss, rss_reason = peak_rss_bytes()
    if rss is None and not rss_reason:
        problems.append("an unavailable peak RSS must carry a reason")
    if not CACHE_POLICY.startswith("lake clean"):
        problems.append("the cache policy must be recorded verbatim")
    return problems


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    if args.self_test:
        problems = self_test()
        if problems:
            for problem in problems:
                print(f"error: {problem}", file=sys.stderr)
            return 1
        print("benchmark runner self-test passed: scenario roles pinned and canonical, "
              "malformed and duplicate scenarios rejected, unavailable resource fields "
              "carry reasons, cache policy recorded")
        return 0

    if not (ROOT / "lakefile.toml").is_file():
        print(f"error: expected lakefile.toml below {ROOT}", file=sys.stderr)
        return 2
    if shutil.which("lake") is None:
        print("error: `lake` is not available on PATH", file=sys.stderr)
        return 2

    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    results_dir = (args.results_dir or ROOT / "benchmark-results" / stamp).resolve()
    results_dir.mkdir(parents=True, exist_ok=False)

    try:
        scenarios = parse_scenarios(args.scenario)
    except ValueError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2

    runner = BenchmarkRunner(args, results_dir)
    memory, memory_reason = physical_memory_bytes()
    clean_before = tracked_clean()
    acceptance = (clean_before["clean"] and not args.allow_dirty_scenarios
                  and not args.skip_pin_check and args.mode == "all")
    summary: dict[str, Any] = {
        "schema_version": 2,
        "started_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "repository": str(ROOT),
        "git_commit": capture(["git", "rev-parse", "HEAD"]),
        "tracked_clean_before": clean_before,
        "acceptance_evidence": acceptance,
        "acceptance_disqualifiers": [
            reason for reason, hit in (
                ("tracked changes present before the run", not clean_before["clean"]),
                ("--allow-dirty-scenarios used", args.allow_dirty_scenarios),
                ("--skip-pin-check used", args.skip_pin_check),
                ("partial mode: the fixed sequence was not run end to end", args.mode != "all"),
            ) if hit
        ],
        "environment": {
            "platform": platform.platform(),
            "processor": platform.processor(),
            "cpu_count": os.cpu_count(),
            "physical_memory_bytes": memory,
            "physical_memory_unavailable_reason": memory_reason,
            "lake_version": capture(["lake", "--version"]),
            "lean_version": capture(["lean", "--version"]),
            "lean_toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
            if (ROOT / "lean-toolchain").is_file() else None,
            "dependency_revisions": dependency_revisions(),
        },
        "cache_policy": CACHE_POLICY,
        "mode": args.mode,
        "targets": runner.targets,
        "scenarios": {name: {"path": str(path), "pinned_sha256": SCENARIO_SHA256.get(name)}
                      for name, path in scenarios.items()},
        "runs": runner.results,
        "restores": runner.restores,
    }
    exit_code = 0
    try:
        if not clean_before["clean"] and not args.allow_dirty_scenarios:
            raise RuntimeError(
                "refusing to measure a tree with tracked changes: "
                f"unstaged={clean_before['unstaged_tracked_changes']} "
                f"staged={clean_before['staged_tracked_changes']}"
            )
        if args.mode in ("all", "clean"):
            runner.clean()
        if args.mode in ("all", "warm"):
            runner.warm()
        if args.mode in ("all", "incremental"):
            runner.incremental(scenarios)
        if args.mode in ("all", "test"):
            runner.test()
        if any(run["exit_code"] != 0 for run in runner.results):
            exit_code = 1
    except (OSError, RuntimeError, ValueError) as error:
        summary["error"] = str(error)
        print(f"error: {error}", file=sys.stderr)
        exit_code = 1
    finally:
        summary["finished_at_utc"] = dt.datetime.now(dt.timezone.utc).isoformat()
        clean_after = tracked_clean()
        summary["tracked_clean_after"] = clean_after
        if not clean_after["clean"]:
            summary["acceptance_evidence"] = False
            summary["acceptance_disqualifiers"].append(
                "tracked changes remained after the run"
            )
        summary_path = results_dir / "summary.json"
        summary_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n",
                                encoding="utf-8")
        print(f"summary: {summary_path}", flush=True)
        print(f"acceptance evidence: {summary['acceptance_evidence']}", flush=True)
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
