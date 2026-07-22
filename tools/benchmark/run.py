#!/usr/bin/env python3
"""Measure clean, warm, and representative incremental Lake builds.

The runner uses only the Python standard library.  Results and complete Lake
logs are written below ``benchmark-results/`` by default.
"""

from __future__ import annotations

import argparse
import datetime as dt
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
DEFAULT_SCENARIOS = {
    "foundation": Path("NumStability/FloatingPoint/Model.lean"),
    "endpoint": Path("NumStability/Higham/Chapter02/Problem04.lean"),
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--mode",
        choices=("all", "clean", "warm", "incremental"),
        default="all",
        help="benchmark mode (default: all)",
    )
    parser.add_argument(
        "--target",
        action="append",
        dest="targets",
        help="Lake build target; repeat for multiple targets",
    )
    parser.add_argument(
        "--package",
        default="numStability",
        help="root package passed to `lake clean` (default: numStability)",
    )
    parser.add_argument(
        "--scenario",
        action="append",
        metavar="NAME=PATH",
        help="incremental edit scenario; repeat to replace the defaults",
    )
    parser.add_argument(
        "--results-dir",
        type=Path,
        help="output directory (default: benchmark-results/<UTC timestamp>)",
    )
    parser.add_argument(
        "--allow-dirty-scenarios",
        action="store_true",
        help="allow a scenario source file that already has Git changes",
    )
    parser.add_argument(
        "--keep-going",
        action="store_true",
        help="continue after a failed measured command",
    )
    return parser.parse_args()


def capture(command: list[str]) -> str:
    completed = subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    return completed.stdout.strip()


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

    def run_command(
        self, label: str, command: list[str], *, measured: bool = True
    ) -> dict[str, Any]:
        log_path = self.results_dir / f"{label}.log"
        try:
            displayed_log = str(log_path.relative_to(ROOT))
        except ValueError:
            displayed_log = str(log_path)
        printable = shlex.join(command)
        print(f"[{label}] {printable}", flush=True)
        started = time.perf_counter()
        with log_path.open("w", encoding="utf-8", newline="") as log:
            log.write(f"$ {printable}\n\n")
            completed = subprocess.run(
                command,
                cwd=ROOT,
                stdout=log,
                stderr=subprocess.STDOUT,
                check=False,
            )
        elapsed = time.perf_counter() - started
        result = {
            "label": label,
            "command": command,
            "seconds": round(elapsed, 3),
            "exit_code": completed.returncode,
            "measured": measured,
            "log": displayed_log,
        }
        self.results.append(result)
        print(
            f"[{label}] exit={completed.returncode} elapsed={elapsed:.3f}s",
            flush=True,
        )
        if completed.returncode != 0 and not self.args.keep_going:
            raise RuntimeError(f"{label} failed; see {log_path}")
        return result

    def build(self, label: str, *, measured: bool = True) -> dict[str, Any]:
        return self.run_command(
            label, ["lake", "build", *self.targets], measured=measured
        )

    def clean(self) -> None:
        self.run_command(
            "clean-reset", ["lake", "clean", self.args.package], measured=False
        )
        self.build("clean-build")

    def warm(self) -> None:
        self.build("warm-build")

    def check_scenario_path(self, relative_path: Path) -> Path:
        source = (ROOT / relative_path).resolve()
        try:
            source.relative_to(ROOT)
        except ValueError as error:
            raise ValueError(f"scenario path escapes repository: {relative_path}") from error
        if not source.is_file() or source.suffix != ".lean":
            raise ValueError(f"scenario is not a Lean source file: {relative_path}")
        if not self.args.allow_dirty_scenarios:
            status = capture(
                ["git", "status", "--porcelain", "--", str(relative_path)]
            )
            if status:
                raise ValueError(
                    f"scenario file has Git changes: {relative_path}; "
                    "commit/stash them or pass --allow-dirty-scenarios"
                )
        return source

    def incremental(self, scenarios: dict[str, Path]) -> None:
        # Establish a common up-to-date baseline before simulating edits.
        self.build("incremental-baseline", measured=False)
        for name, relative_path in scenarios.items():
            source = self.check_scenario_path(relative_path)
            original = source.read_bytes()
            original_stat = source.stat()
            marker = (
                f"\n-- benchmark-only edit ({name}); restored automatically\n"
            ).encode("utf-8")
            try:
                source.write_bytes(original + marker)
                self.build(f"incremental-{name}")
            finally:
                source.write_bytes(original)
                os.utime(
                    source,
                    ns=(original_stat.st_atime_ns, original_stat.st_mtime_ns),
                )
                # Re-establish a correct trace for the restored source before
                # the next scenario and even when the measured build fails.
                self.build(f"restore-{name}", measured=False)


def main() -> int:
    args = parse_args()
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
    summary: dict[str, Any] = {
        "started_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "repository": str(ROOT),
        "git_commit": capture(["git", "rev-parse", "HEAD"]),
        "git_status_before": capture(["git", "status", "--short"]),
        "lake_version": capture(["lake", "--version"]),
        "platform": platform.platform(),
        "processor": platform.processor(),
        "cpu_count": os.cpu_count(),
        "mode": args.mode,
        "targets": runner.targets,
        "scenarios": {name: str(path) for name, path in scenarios.items()},
        "runs": runner.results,
    }
    exit_code = 0
    try:
        if args.mode in ("all", "clean"):
            runner.clean()
        if args.mode in ("all", "warm"):
            runner.warm()
        if args.mode in ("all", "incremental"):
            runner.incremental(scenarios)
        if any(run["exit_code"] != 0 for run in runner.results):
            exit_code = 1
    except (OSError, RuntimeError, ValueError) as error:
        summary["error"] = str(error)
        print(f"error: {error}", file=sys.stderr)
        exit_code = 1
    finally:
        summary["finished_at_utc"] = dt.datetime.now(dt.timezone.utc).isoformat()
        summary["git_status_after"] = capture(["git", "status", "--short"])
        summary_path = results_dir / "summary.json"
        summary_path.write_text(
            json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        print(f"summary: {summary_path}", flush=True)
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
