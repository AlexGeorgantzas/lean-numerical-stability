from __future__ import annotations

import json
import hashlib
from pathlib import Path
import sys
import tempfile
import types
import unittest
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import BenchmarkError, sha256_file  # noqa: E402
import design18_matched  # noqa: E402
from design18_matched import _qualified, run  # noqa: E402
from design18_model_qualify import PROMPT as QUALIFICATION_PROMPT  # noqa: E402


class Pilot18MatchedTests(unittest.TestCase):
    def test_model_gate_requires_exact_sol_and_binary(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            binary = root / "codex"
            binary.write_bytes(b"synthetic-codex")
            record = root / "qualification.json"
            value = {
                "schema_version": "pilot-18-model-qualification-1",
                "status": "PASS", "model": "gpt-6-sol",
                "reasoning_effort": "xhigh",
                "codex_binary_sha256": sha256_file(binary),
                "code_mode_host_sha256": "a" * 64,
                "qualification_prompt_sha256": hashlib.sha256(
                    QUALIFICATION_PROMPT.encode("utf-8")
                ).hexdigest(),
                "usage_complete": True,
            }
            record.write_text(json.dumps(value), encoding="utf-8")
            self.assertEqual(_qualified(record, binary=binary,
                                        code_mode_host_sha256="a" * 64), value)
            value["model"] = "gpt-6-astra"
            record.write_text(json.dumps(value), encoding="utf-8")
            with self.assertRaises(BenchmarkError):
                _qualified(record, binary=binary,
                           code_mode_host_sha256="a" * 64)

    def test_unadmitted_release_stops_before_output_or_model(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            output = Path(raw) / "pair"
            with self.assertRaisesRegex(BenchmarkError, "not admitted"):
                run(types.SimpleNamespace(task_id="HM19-3-2", output_root=output))
            self.assertFalse(output.exists())

    def test_provider_free_pair_orchestration_preserves_prompt_prefix_and_order(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            design = root / "design18"
            (design / "sources").mkdir(parents=True)
            (design / "packets").mkdir()
            (design / "prompts").mkdir()
            pdf = design / "sources" / "paper.pdf"
            pdf.write_bytes(b"synthetic paper")
            packet = {"task_id": "TEST-1", "paper_pdf": {
                "path_basename": "paper.pdf", "sha256": sha256_file(pdf),
            }}
            (design / "packets" / "TEST-1.json").write_text(
                json.dumps(packet), encoding="utf-8"
            )
            (design / "prompts" / "common.md").write_bytes(b"common prompt\n")
            (design / "prompts" / "library_appendix.md").write_bytes(b"\nL guidance\n")
            (design / "prompts" / "scout.md").write_bytes(b"task-neutral scout\n")
            atlas = root / "numstability-atlas"
            atlas.mkdir()
            (atlas / "declarations.jsonl").write_bytes(b"{}\n")
            binary = root / "codex"
            binary.write_bytes(b"synthetic-codex")
            qualification = root / "qualification.json"
            qualification.write_text("{}", encoding="utf-8")
            warm = root / "warm"
            warm.mkdir()
            (warm / "warm-root.json").write_text(json.dumps({
                "schema_version": "pilot-18-warm-root-1", "status": "READY",
                "model": "gpt-6-sol", "reasoning_effort": "xhigh",
                "scout_prompt_sha256": sha256_file(design / "prompts" / "scout.md"),
                "library_atlas_sha256": sha256_file(atlas / "declarations.jsonl"),
                "codex_binary_sha256": sha256_file(binary),
                "code_mode_host_sha256": "a" * 64,
                "model_qualification_sha256": sha256_file(qualification),
            }), encoding="utf-8")
            args = types.SimpleNamespace(
                task_id="TEST-1", output_root=root / "pair",
                deployment=root / "deployment.json", mathlib_atlas=root / "mathlib",
                numstability_atlas=atlas,
                model_qualification=qualification, warm_root=warm,
                condition_order="R1,R0",
            )
            seen = []

            def fake_run_condition(**kwargs):
                seen.append((kwargs["spec"].name, kwargs["prompt"]))
                return {
                    "result_status": "ACCEPTED_FAITHFUL",
                    "retrieval_wall_seconds": 1,
                    "contestant_active_seconds": 2,
                    "contestant_system_wall_seconds": 3,
                    "formalizer_wall_seconds": 2,
                    "net_new_tokens": 10,
                    "candidate_lines": 5,
                    "submission_count": 1,
                }

            corpus = {"status": "ADMITTED_FOR_MEASUREMENT",
                      "scheduled_order": ["OTHER", "TEST-1"]}
            with (
                mock.patch.object(design18_matched, "DESIGN_ROOT", design),
                mock.patch.object(design18_matched, "check_corpus", return_value=(corpus, [packet], [])),
                mock.patch.object(design18_matched, "load_deployment", return_value=types.SimpleNamespace(
                    codex_binary=binary, library_atlas=atlas,
                    code_mode_host_sha256="a" * 64,
                )),
                mock.patch.object(design18_matched, "bind_release_atlases",
                                  side_effect=lambda deployment, **_: (deployment, root / "mathlib")),
                mock.patch.object(design18_matched, "_qualified", return_value={}),
                mock.patch.object(design18_matched, "condition_spec", side_effect=lambda condition, **_: types.SimpleNamespace(name=condition)),
                mock.patch.object(design18_matched, "snapshot_hardware", return_value={"test": True}),
                mock.patch.object(design18_matched, "_run_condition", side_effect=fake_run_condition),
            ):
                pair = run(args)
            self.assertEqual([condition for condition, _ in seen], ["R1", "R0"])
            self.assertEqual(seen[0][1], seen[1][1] + b"\nL guidance\n")
            self.assertEqual(pair["status"], "AUDITED_FAITHFUL_PAIR")
            self.assertEqual(pair["comparison"]["r1_over_r0"]["net_new_tokens"], 1.0)


if __name__ == "__main__":
    unittest.main()
