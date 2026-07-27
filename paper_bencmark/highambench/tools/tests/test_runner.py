from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import BenchmarkToolError, write_json  # noqa: E402
from hashes import create_manifest  # noqa: E402
from runner import (  # noqa: E402
    NETWORK_VIOLATION_MARKER_ENV,
    read_token_usage,
    run_one,
)


SIGNATURE = "theorem target (n : Nat) : n = n := by\n  rfl\n"


class RunnerTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.base = self.root / "base"
        self.base.mkdir()
        (self.base / "README.txt").write_text("minimal Lean workspace\n", encoding="utf-8")
        self.task = self.root / "task-source"
        self.task.mkdir()
        (self.task / "Canonical.lean").write_text(SIGNATURE, encoding="utf-8")
        self.manifest = self.root / "controlled.json"
        write_json(self.manifest, create_manifest(self.task))

        self.agent = self.root / "agent.py"
        self.agent.write_text(
            "from pathlib import Path\n"
            "import json, os, sys\n"
            "workspace = Path(os.environ['HIGHAMBENCH_WORKSPACE'])\n"
            "(workspace / 'usage.json').write_text(json.dumps({\n"
            "  'input_tokens': 30, 'cached_input_tokens': 10, 'output_tokens': 12\n"
            "}))\n"
            f"Path(sys.argv[1]).write_text({SIGNATURE!r})\n",
            encoding="utf-8",
        )
        self.compiler = self.root / "compiler.py"
        self.compiler.write_text(
            "from pathlib import Path\n"
            "import sys\n"
            "source = Path(sys.argv[1])\n"
            "text = source.read_text()\n"
            "if source.name.startswith('HighamBenchChecked_'):\n"
            "  assert '#check target' in text\n"
            "Path(sys.argv[2]).write_bytes(b'fake olean')\n"
            "print('axioms: []')\n",
            encoding="utf-8",
        )
        self.probe = self.root / "probe.py"
        self.probe.write_text(
            "print(\"error: unknown module prefix 'NumStability'\")\n"
            "raise SystemExit(1)\n",
            encoding="utf-8",
        )
        self.audit = self.root / "audit.py"
        self.audit.write_text(
            "import sys\n"
            "candidate, expected, condition = sys.argv[1:]\n"
            "print('format\\t2')\n"
            "print(f'typeeq\\t{candidate}\\t{expected}\\ttrue')\n"
            "print(f'target\\t{candidate}\\tHighamBenchChecked')\n"
            "if condition == 'L':\n"
            "  print('library\\tNumStability.reused\\tNumStability.Basic\\t1')\n"
            "print('visited\\t2')\n"
            "print(f'summary\\t{1 if condition == \"L\" else 0}\\t0')\n",
            encoding="utf-8",
        )

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def args(self, condition: str) -> argparse.Namespace:
        return argparse.Namespace(
            condition=condition,
            task_id="paper-1-t1",
            paper_id="paper-1",
            paper_sha256="a" * 64,
            tier="T1",
            repetition_id="rep-01",
            seed=17,
            pair_id="paper-1-t1-seed-17",
            pair_order="N-first",
            order_index=1 if condition == "N" else 2,
            run_id=f"integration-{condition}",
            agent_id="fake-agent",
            agent_version="1",
            model="fake-model",
            reasoning_effort="medium",
            environment_id="test-environment",
            freeze_check_json=json.dumps(
                {
                    "schema_version": 1,
                    "kind": "highambench-frozen-run-verification",
                    "ok": True,
                    "environment_id": "test-environment",
                },
                sort_keys=True,
                separators=(",", ":"),
            ),
            base_workspace=self.base,
            task_root=self.task,
            controlled_manifest=self.manifest,
            task_dest="task",
            workspace_parent=self.root / "workspaces",
            logs_dir=self.root / "logs",
            raw_jsonl=self.root / "runs.jsonl",
            keep_workspace=False,
            submission_relative="Submission.lean",
            canonical_relative="task/Canonical.lean",
            target_theorem="target",
            local_source_relative=[],
            forbidden_import_prefix=[],
            submission_module="Submission",
            audit_helper=None,
            prompt_relative=None,
            usage_relative="usage.json",
            agent_command_json=json.dumps(
                [sys.executable, str(self.agent), "{submission}"]
            ),
            compile_command_json=json.dumps(
                [
                    sys.executable,
                    str(self.compiler),
                    "{checked_submission}",
                    "{checked_olean}",
                ]
            ),
            audit_command_json=(
                json.dumps(
                    [
                        sys.executable,
                        str(self.audit),
                        "{target_theorem}",
                        "{expected_theorem}",
                        condition,
                    ]
                )
                if condition == "L"
                else json.dumps(
                    [
                        sys.executable,
                        str(self.audit),
                        "{target_theorem}",
                        "{expected_theorem}",
                        condition,
                    ]
                )
            ),
            n_probe_command_json=(
                json.dumps([sys.executable, str(self.probe)]) if condition == "N" else None
            ),
            n_marker=[],
            n_probe_timeout_seconds=2.0,
            hidden_parent=None,
            validation_timeout_seconds=2.0,
            audit_timeout_seconds=2.0,
            poll_seconds=0.01,
            usage_grace_seconds=0.5,
            time_limit_seconds=5.0,
            token_limit=1_000,
            fresh_conversation=True,
            filesystem_isolated=True,
            network_disabled=True,
            seed_enforced=True,
            token_enforced=True,
            library_available=condition == "L",
            strict_protocol=True,
        )

    def test_runs_fresh_n_and_l_conditions(self) -> None:
        n_result = run_one(self.args("N"))
        l_result = run_one(self.args("L"))
        self.assertTrue(n_result["pass"], n_result)
        self.assertTrue(l_result["pass"], l_result)
        self.assertTrue(n_result["scored"], n_result)
        self.assertTrue(l_result["scored"], l_result)
        self.assertTrue(n_result["useful_work_started"])
        self.assertTrue(l_result["useful_work_started"])
        self.assertTrue(n_result["n_preflight"]["ok"])
        staging = n_result["n_preflight"]["controlled_task_staging"]
        self.assertTrue(staging["complete"])
        self.assertEqual(staging["verified_files"], len(create_manifest(self.task)["files"]))
        self.assertEqual(staging["verified_files"], staging["expected_files"])
        self.assertGreaterEqual(
            n_result["n_preflight"]["filesystem_scan"]["regular_file_count"],
            staging["expected_files"],
        )
        self.assertFalse(n_result["library_use"])
        self.assertTrue(l_result["library_use"])
        self.assertEqual(
            l_result["library_declarations"], ["NumStability.reused"]
        )
        self.assertEqual(n_result["token_usage"]["model_tokens"], 42)
        self.assertIsNone(n_result["workspace"])
        self.assertEqual(list((self.root / "workspaces").iterdir()), [])

    def test_token_accounting_does_not_double_count_cached_input(self) -> None:
        usage_path = self.root / "usage.json"
        usage_path.write_text(
            json.dumps(
                {
                    "calls": [
                        {
                            "input_tokens": 20,
                            "cached_input_tokens": 8,
                            "output_tokens": 5,
                        },
                        {
                            "input_tokens": 7,
                            "cached_input_tokens": 0,
                            "output_tokens": 3,
                        },
                    ]
                }
            ),
            encoding="utf-8",
        )
        usage = read_token_usage(usage_path)
        self.assertEqual(usage["input_tokens"], 27)
        self.assertEqual(usage["cached_input_tokens"], 8)
        self.assertEqual(usage["model_tokens"], 35)

        usage_path.write_text(
            json.dumps(
                {"input_tokens": 2, "cached_input_tokens": 3, "output_tokens": 0}
            ),
            encoding="utf-8",
        )
        with self.assertRaises(BenchmarkToolError):
            read_token_usage(usage_path)

    def test_post_acceptance_grace_captures_delayed_completed_turn_usage(self) -> None:
        delayed_agent = self.root / "delayed_agent.py"
        delayed_agent.write_text(
            "from pathlib import Path\n"
            "import json, os, sys, time\n"
            "workspace = Path(os.environ['HIGHAMBENCH_WORKSPACE'])\n"
            f"Path(sys.argv[1]).write_text({SIGNATURE!r})\n"
            "time.sleep(0.15)\n"
            "(workspace / 'usage.json').write_text(json.dumps({\n"
            "  'input_tokens': 60, 'cached_input_tokens': 20, 'output_tokens': 15\n"
            "}))\n",
            encoding="utf-8",
        )
        args = self.args("N")
        args.agent_command_json = json.dumps(
            [sys.executable, str(delayed_agent), "{submission}"]
        )
        args.usage_grace_seconds = 1.0
        result = run_one(args)
        self.assertTrue(result["pass"], result)
        self.assertTrue(result["scored"], result)
        self.assertEqual(result["token_usage"]["model_tokens"], 75)
        capture = result["token_measurement"]["capture_grace"]
        self.assertTrue(capture["attempted"])
        self.assertTrue(capture["usage_captured_during_grace"])
        self.assertGreater(capture["waited_seconds"], 0)
        self.assertEqual(result["scored_elapsed_seconds"], result["first_valid_seconds"])
        self.assertGreater(
            result["actual_stop_seconds"], result["first_valid_seconds"] + 0.05
        )
        self.assertFalse(result["token_measurement"]["aligned_exactly_to_first_valid"])
        self.assertIn("may include tokens", result["token_measurement"]["deviation_note"])
        self.assertTrue(Path(result["accepted_submission_log"]).is_file())
        self.assertFalse(result["submission_changed_after_acceptance"])

    def test_network_attempt_marker_overrides_a_valid_proof(self) -> None:
        violating_agent = self.root / "violating_agent.py"
        violating_agent.write_text(
            "from pathlib import Path\n"
            "import json, os, sys\n"
            "workspace = Path(os.environ['HIGHAMBENCH_WORKSPACE'])\n"
            "Path(os.environ['HIGHAMBENCH_NETWORK_VIOLATION_MARKER']).write_bytes(b'N')\n"
            "(workspace / 'usage.json').write_text(json.dumps({\n"
            "  'input_tokens': 30, 'cached_input_tokens': 10, 'output_tokens': 12\n"
            "}))\n"
            f"Path(sys.argv[1]).write_text({SIGNATURE!r})\n",
            encoding="utf-8",
        )
        args = self.args("N")
        args.agent_command_json = json.dumps(
            [sys.executable, str(violating_agent), "{submission}"]
        )
        result = run_one(args)
        self.assertFalse(result["pass"], result)
        self.assertEqual(result["failure_code"], "RULE_VIOLATION")
        self.assertTrue(result["network_violation"]["detected"])
        self.assertTrue(result["network_violation"]["integrity_ok"])
        self.assertEqual(result["network_violation"]["event_count"], 1)
        self.assertGreaterEqual(
            result["network_violation"]["kernel_event_count"], 1
        )
        self.assertIsNotNone(result["first_valid_seconds"])
        self.assertEqual(result["scored_elapsed_seconds"], 5.0)
        self.assertTrue(result["scored"])
        saved = Path(result["network_violation"]["saved_marker_log"])
        self.assertEqual(saved.read_bytes(), b"N")

    def test_truncating_marker_cannot_erase_trusted_kernel_event(self) -> None:
        clearing_agent = self.root / "clearing_agent.py"
        clearing_agent.write_text(
            "from pathlib import Path\n"
            "import json, os, sys\n"
            "workspace = Path(os.environ['HIGHAMBENCH_WORKSPACE'])\n"
            "marker = Path(os.environ['HIGHAMBENCH_NETWORK_VIOLATION_MARKER'])\n"
            "marker.write_bytes(b'N')\n"
            "marker.write_bytes(b'')\n"
            "(workspace / 'usage.json').write_text(json.dumps({\n"
            "  'input_tokens': 30, 'cached_input_tokens': 10, 'output_tokens': 12\n"
            "}))\n"
            f"Path(sys.argv[1]).write_text({SIGNATURE!r})\n",
            encoding="utf-8",
        )
        args = self.args("N")
        args.agent_command_json = json.dumps(
            [sys.executable, str(clearing_agent), "{submission}"]
        )
        result = run_one(args)
        self.assertFalse(result["pass"], result)
        self.assertEqual(result["failure_code"], "RULE_VIOLATION")
        self.assertTrue(result["network_violation"]["detected"])
        self.assertFalse(result["network_violation"]["integrity_ok"])
        self.assertIn("later cleared", result["network_violation"]["note"])
        self.assertFalse(result["scored"])

    def test_no_submission_has_priority_over_network_rule_violation(self) -> None:
        no_submission_agent = self.root / "no_submission_agent.py"
        no_submission_agent.write_text(
            "from pathlib import Path\n"
            "import json, os\n"
            "workspace = Path(os.environ['HIGHAMBENCH_WORKSPACE'])\n"
            "Path(os.environ['HIGHAMBENCH_NETWORK_VIOLATION_MARKER']).write_bytes(b'N')\n"
            "(workspace / 'usage.json').write_text(json.dumps({\n"
            "  'input_tokens': 30, 'cached_input_tokens': 10, 'output_tokens': 12\n"
            "}))\n",
            encoding="utf-8",
        )
        args = self.args("N")
        args.agent_command_json = json.dumps(
            [sys.executable, str(no_submission_agent)]
        )
        result = run_one(args)
        self.assertFalse(result["pass"], result)
        self.assertEqual(result["failure_code"], "NO_SUBMISSION")
        self.assertTrue(result["useful_work_started"])
        self.assertTrue(result["network_violation"]["detected"])

    def test_agent_startup_failure_remains_a_system_error(self) -> None:
        args = self.args("N")
        args.agent_command_json = json.dumps([str(self.root / "missing-agent")])
        result = run_one(args)
        self.assertFalse(result["pass"], result)
        self.assertEqual(result["failure_code"], "SYSTEM_ERROR")
        self.assertFalse(result["useful_work_started"])
        self.assertIn("No such file", result["failure_note"])
        self.assertFalse(result["network_violation"]["detected"])

    def test_n_preflight_scans_the_staged_controlled_task(self) -> None:
        (self.task / "leaked-context.md").write_text(
            "A forbidden NumStability declaration name is visible.\n", encoding="utf-8"
        )
        write_json(self.manifest, create_manifest(self.task))
        result = run_one(self.args("N"))
        self.assertFalse(result["pass"], result)
        self.assertEqual(result["failure_code"], "SYSTEM_ERROR")
        self.assertFalse(result["useful_work_started"])
        self.assertTrue(result["n_preflight"]["filesystem_leaks"])

    def test_system_error_after_agent_start_is_a_charged_final_failure(self) -> None:
        with mock.patch("runner.validate", side_effect=BenchmarkToolError("validator crashed")):
            result = run_one(self.args("N"))
        self.assertFalse(result["pass"], result)
        self.assertEqual(result["failure_code"], "SYSTEM_ERROR")
        self.assertTrue(result["useful_work_started"])
        self.assertTrue(result["scored"])
        self.assertEqual(result["scored_elapsed_seconds"], 5.0)


if __name__ == "__main__":
    unittest.main()
