from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import BenchmarkError  # noqa: E402
from measure_library_build import (  # noqa: E402
    _counter_delta,
    cgroup_statistics,
    measure_build,
    parse_gnu_time_verbose,
    validate_build_record,
)


GNU_TIME_FIXTURE = """
\tCommand being timed: \"lake build NumStability\"
\tUser time (seconds): 12.50
\tSystem time (seconds): 1.25
\tPercent of CPU this job got: 725%
\tElapsed (wall clock) time (h:mm:ss or m:ss): 0:01.93
\tMaximum resident set size (kbytes): 2048
\tMajor (requiring I/O) page faults: 2
\tMinor (reclaiming a frame) page faults: 300
\tVoluntary context switches: 40
\tInvoluntary context switches: 5
\tSwaps: 0
\tFile system inputs: 16
\tFile system outputs: 32
\tSocket messages sent: 0
\tSocket messages received: 0
\tSignals delivered: 0
\tExit status: 0
"""


class GnuTimeParsingTests(unittest.TestCase):
    def test_extracts_resource_metrics_and_converts_peak_memory(self) -> None:
        parsed = parse_gnu_time_verbose(GNU_TIME_FIXTURE)
        self.assertEqual(parsed["user_cpu_seconds"], 12.5)
        self.assertEqual(parsed["system_cpu_seconds"], 1.25)
        self.assertEqual(parsed["cpu_percent"], 725.0)
        self.assertEqual(parsed["elapsed_wall_clock_text"], "0:01.93")
        self.assertEqual(parsed["maximum_resident_set_bytes"], 2 * 1024 * 1024)
        self.assertEqual(parsed["major_page_faults"], 2)
        self.assertEqual(parsed["exit_status"], 0)

    def test_rejects_an_incomplete_time_record(self) -> None:
        with self.assertRaisesRegex(BenchmarkError, "missing fields"):
            parse_gnu_time_verbose("User time (seconds): 1.0\n")

    def test_rejects_a_malformed_metric(self) -> None:
        with self.assertRaisesRegex(BenchmarkError, "malformed GNU time field"):
            parse_gnu_time_verbose(
                GNU_TIME_FIXTURE.replace("Exit status: 0", "Exit status: success")
            )

    def test_build_record_keeps_only_logical_paths_and_allowlisted_environment(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            checkout = root / "private-transient-checkout"
            artifact_root = root / "artifacts"
            toolchain = root / "toolchain"
            (checkout / "NumStability").mkdir(parents=True)
            (checkout / "NumStability" / "Core.lean").write_text(
                "def core := 1\n", encoding="utf-8"
            )
            (checkout / "NumStability.lean").write_text(
                "import NumStability.Core\n", encoding="utf-8"
            )
            mathlib = checkout / ".lake" / "packages" / "mathlib"
            mathlib.mkdir(parents=True)
            dependency_build = mathlib / ".lake" / "build" / "lib" / "lean"
            dependency_build.mkdir(parents=True)
            (dependency_build / "Mathlib.olean").write_bytes(b"cached-olean")
            (checkout / "lakefile.toml").write_text(
                'name = "fixture"\n', encoding="utf-8"
            )
            (checkout / "lean-toolchain").write_text(
                "leanprover/lean4:test\n", encoding="utf-8"
            )
            (toolchain / "bin").mkdir(parents=True)
            for name in ("lake", "lean"):
                (toolchain / "bin" / name).write_bytes((name + "\n").encode("ascii"))

            source_commit = "a" * 40
            mathlib_commit = "b" * 40
            (checkout / "lake-manifest.json").write_text(
                json.dumps(
                    {
                        "version": "1.1.0",
                        "packages": [
                            {
                                "name": "mathlib",
                                "rev": mathlib_commit,
                                "url": "https://example.invalid/mathlib",
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )

            metadata_environments: list[dict[str, str]] = []

            def small_command(
                command: list[str], *, cwd: Path, environment=None
            ) -> str:
                metadata_environments.append(dict(environment or {}))
                if command[:2] == ["/usr/bin/git", "status"]:
                    return ""
                if command[:3] == ["/usr/bin/git", "rev-parse", "HEAD"]:
                    return mathlib_commit if cwd.name == "mathlib" else source_commit
                if command[0] == "/usr/bin/time":
                    return "time (GNU Time) fixture"
                return "fixture-version"

            bounded_environments: list[dict[str, str]] = []

            def bounded(command, *, cwd, environment, timeout_seconds, maximum_output_bytes):
                del cwd, timeout_seconds, maximum_output_bytes
                bounded_environments.append(dict(environment))
                if command[-1] == "clean":
                    return {
                        "returncode": 0,
                        "timed_out": False,
                        "output_limit_exceeded": False,
                    }
                if command[-3:] == ["exe", "cache", "get"]:
                    output = b"cache prepared\n"
                    return {
                        "returncode": 0,
                        "output": output.decode("utf-8"),
                        "output_sha256": hashlib.sha256(output).hexdigest(),
                        "output_bytes_observed": len(output),
                        "output_limit_exceeded": False,
                        "timed_out": False,
                        "resource_limit_exceeded": False,
                    }
                time_path = Path(command[command.index("-o") + 1])
                time_path.write_text(GNU_TIME_FIXTURE, encoding="utf-8")
                built = checkout / ".lake" / "build" / "lib" / "lean"
                built.mkdir(parents=True)
                (built / "NumStability.olean").write_bytes(b"olean")
                output = b"build succeeded\n"
                return {
                    "returncode": 0,
                    "output": output.decode("utf-8"),
                    "output_sha256": hashlib.sha256(output).hexdigest(),
                    "output_bytes_observed": len(output),
                    "output_limit_exceeded": False,
                    "timed_out": False,
                    "resource_limit_exceeded": False,
                }

            args = SimpleNamespace(
                checkout=str(checkout),
                artifact_root=str(artifact_root),
                toolchain_root=str(toolchain),
                expected_commit=source_commit,
                mathlib_commit=mathlib_commit,
                lean_toolchain="leanprover/lean4:test",
            )
            hardware = {"admitted": True, "cgroup_v2_path": "/ignored"}
            cgroup_before = {
                "cpu_stat": {"usage_usec": 10, "user_usec": 7, "system_usec": 3},
                "memory_current_bytes": 1024,
                "memory_peak_bytes": 2048,
                "memory_events": {"low": 0, "high": 0, "max": 0, "oom": 0, "oom_kill": 0},
                "memory_swap_current_bytes": 0,
                "pids_current": 1,
                "pids_events": {"max": 0},
            }
            cgroup_after = {
                **cgroup_before,
                "cpu_stat": {"usage_usec": 30, "user_usec": 22, "system_usec": 8},
            }
            with mock.patch(
                "measure_library_build._small_command", side_effect=small_command
            ), mock.patch(
                "measure_library_build.run_bounded_command", side_effect=bounded
            ), mock.patch(
                "measure_library_build.snapshot_hardware", return_value=hardware
            ), mock.patch(
                "measure_library_build.cgroup_statistics",
                side_effect=[cgroup_before, cgroup_after],
            ), mock.patch.dict(
                os.environ, {"UNRELATED_SECRET_FOR_TEST": "must-not-be-recorded"}
            ):
                result = measure_build(args)

            record = json.loads(result.read_text(encoding="utf-8"))
            serialized = json.dumps(record)
            self.assertNotIn(str(checkout), serialized)
            self.assertNotIn("UNRELATED_SECRET_FOR_TEST", serialized)
            self.assertNotIn("must-not-be-recorded", serialized)
            self.assertEqual(record["logical_command"], ["lake", "build", "NumStability"])
            self.assertEqual(record["generated_olean"]["file_count"], 1)
            self.assertEqual(
                record["cache_state"]["dependency_closure_before"][
                    "dependency_olean_file_count"
                ],
                1,
            )
            self.assertEqual(record["build_output"]["relative_path"], "build-output.log")
            self.assertFalse(record["benchmark_charged"])
            self.assertEqual(record["build_environment"]["HOME"], "/nonexistent")
            self.assertTrue(metadata_environments)
            self.assertTrue(bounded_environments)
            for environment in metadata_environments + bounded_environments:
                self.assertNotIn("UNRELATED_SECRET_FOR_TEST", environment)
                self.assertNotIn("HIGHAMBENCH_COMMAND_CGROUP_PROCS", environment)

            tampered = json.loads(json.dumps(record))
            incomplete_cgroup = {
                "memory_current_bytes": 0,
                "memory_peak_bytes": 0,
                "memory_swap_current_bytes": 0,
                "pids_current": 1,
            }
            tampered["cgroup_before"] = incomplete_cgroup
            tampered["cgroup_after"] = incomplete_cgroup
            with self.assertRaisesRegex(BenchmarkError, "resource counters are malformed"):
                validate_build_record(
                    tampered,
                    expected_source_commit=source_commit,
                    expected_mathlib_commit=mathlib_commit,
                    expected_toolchain="leanprover/lean4:test",
                    expected_tool_hashes=record["tool_hashes"],
                )

            tampered = json.loads(json.dumps(record))
            tampered["tool_hashes"]["lean_sha256"] = "0" * 64
            with self.assertRaisesRegex(BenchmarkError, "tool identity"):
                validate_build_record(
                    tampered,
                    expected_source_commit=source_commit,
                    expected_mathlib_commit=mathlib_commit,
                    expected_toolchain="leanprover/lean4:test",
                    expected_tool_hashes=record["tool_hashes"],
                )


class CgroupAccountingTests(unittest.TestCase):
    def _write_fixture(self, root: Path) -> None:
        (root / "cpu.stat").write_text(
            "usage_usec 30\nuser_usec 20\nsystem_usec 10\n", encoding="ascii"
        )
        (root / "memory.current").write_text("1024\n", encoding="ascii")
        (root / "memory.peak").write_text("2048\n", encoding="ascii")
        (root / "memory.events").write_text(
            "low 0\nhigh 0\nmax 0\noom 0\noom_kill 0\n", encoding="ascii"
        )
        (root / "memory.swap.current").write_text("0\n", encoding="ascii")
        (root / "pids.current").write_text("2\n", encoding="ascii")
        (root / "pids.events").write_text("max 0\n", encoding="ascii")

    def test_requires_complete_numeric_resource_counters(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self._write_fixture(root)
            record = cgroup_statistics({"cgroup_v2_path": str(root)})
            self.assertEqual(record["memory_events"]["oom_kill"], 0)
            (root / "memory.events").write_text("max 0\noom broken\n", encoding="ascii")
            with self.assertRaisesRegex(BenchmarkError, "malformed cgroup counter"):
                cgroup_statistics({"cgroup_v2_path": str(root)})

    def test_rejects_missing_and_regressed_counters(self) -> None:
        with self.assertRaisesRegex(BenchmarkError, "keys changed"):
            _counter_delta({"max": 0}, {})
        with self.assertRaisesRegex(BenchmarkError, "regressed"):
            _counter_delta({"max": 2}, {"max": 1})


if __name__ == "__main__":
    unittest.main()
