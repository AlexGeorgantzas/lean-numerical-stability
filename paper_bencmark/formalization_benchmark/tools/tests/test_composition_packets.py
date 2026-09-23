from __future__ import annotations

import json
from pathlib import Path
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from composition_packets import build_composition_packet  # noqa: E402


class CompositionPacketTests(unittest.TestCase):
    def test_unrouted_open_snapshot_does_not_rank_or_expose_declarations(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            packet = root / "task.json"
            packet.write_text(json.dumps({"task_id": "TEST-1"}), encoding="utf-8")
            atlas = root / "declarations.jsonl"
            atlas.write_text("not parsed by this policy\n", encoding="utf-8")
            result, markdown = build_composition_packet(
                source_packet_path=packet,
                atlas_paths=[atlas],
                corpus_id="test-corpus",
                root_limit=0,
                dependency_limit=0,
                selection_policy="no-automatic-retrieval",
                open_library_access=True,
            )
            self.assertEqual(result["retrieved_roots"], [])
            self.assertEqual(result["retrieval_candidate_count"], 0)
            self.assertFalse(result["policy"]["automatic"])
            self.assertIn(b"No task-specific declarations", markdown)
            with self.assertRaisesRegex(Exception, "requires open access"):
                build_composition_packet(
                    source_packet_path=packet,
                    atlas_paths=[atlas],
                    corpus_id="test-corpus",
                    root_limit=0,
                    dependency_limit=0,
                    selection_policy="no-automatic-retrieval",
                    open_library_access=False,
                )

    def test_ranks_relevant_card_and_emits_bounded_packet(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            packet = root / "task.json"
            packet.write_text(
                json.dumps(
                    {
                        "task_id": "H5-5",
                        "selected_result": "Rounded root product polynomial error bound",
                        "task_clarification": [
                            "The computed root product has a gamma coefficient."
                        ],
                        "scope_constraints": [
                            "Represent the rounded evaluation algorithm."
                        ],
                    }
                ),
                encoding="utf-8",
            )
            records = [
                {
                    "kind": "theorem",
                    "name": "NumStability.fl_rootProductEval_forward_error_bound",
                    "display_name": "fl_rootProductEval_forward_error_bound",
                    "module": "NumStability.Algorithms.Horner",
                    "source_file": "NumStability/Algorithms/Horner.lean",
                    "source_line": 10,
                    "signature": "theorem fl_rootProductEval_forward_error_bound (fp : FPModel) : Prop",
                    "documentation": "Rounded root-product evaluation gamma error bound.",
                },
                {
                    "kind": "def",
                    "name": "NumStability.unrelatedMatrix",
                    "display_name": "unrelatedMatrix",
                    "module": "NumStability.Other",
                    "source_file": "NumStability/Other.lean",
                    "source_line": 2,
                    "signature": "def unrelatedMatrix : Nat := 0",
                    "documentation": "Unrelated matrix helper.",
                },
            ]
            atlas = root / "declarations.jsonl"
            atlas.write_text(
                "".join(json.dumps(record) + "\n" for record in records),
                encoding="utf-8",
            )
            result, markdown = build_composition_packet(
                source_packet_path=packet,
                atlas_paths=[atlas],
                corpus_id="mathlib-plus-numstability",
                root_limit=1,
                maximum_markdown_bytes=8192,
            )
            self.assertEqual(
                result["retrieved_roots"][0]["declaration"]["name"],
                "NumStability.fl_rootProductEval_forward_error_bound",
            )
            self.assertIn(b"complete task-time retrieval interface", markdown)
            self.assertLessEqual(len(markdown), 8192)
            self.assertFalse(result["policy"]["task_time_search_permitted"])
            open_result, open_markdown = build_composition_packet(
                source_packet_path=packet,
                atlas_paths=[atlas],
                corpus_id="mathlib-plus-numstability",
                root_limit=1,
                maximum_markdown_bytes=8192,
                open_library_access=True,
            )
            self.assertTrue(open_result["policy"]["task_time_search_permitted"])
            self.assertFalse(open_result["policy"]["packet_is_exhaustive_interface"])
            self.assertIn(b"starting suggestions, not an access whitelist", open_markdown)
            self.assertNotIn(b"complete task-time retrieval interface", open_markdown)
            canonical = (
                "NumStability.fl_rootProductEval_forward_error_bound : "
                "NumStability.FPModel → Prop"
            )
            canonical_result, canonical_markdown = build_composition_packet(
                source_packet_path=packet,
                atlas_paths=[atlas],
                corpus_id="mathlib-plus-numstability",
                root_limit=1,
                maximum_markdown_bytes=8192,
                exposed_signature_overrides={
                    "NumStability.fl_rootProductEval_forward_error_bound": canonical
                },
            )
            self.assertIn(canonical.encode("utf-8"), canonical_markdown)
            self.assertNotIn(b"(fp : FPModel) : Prop", canonical_markdown)
            self.assertEqual(
                canonical_result["policy"]["exposed_signature_source"],
                "elaborated-constant-type",
            )

    def test_conservative_no_route_hides_weak_lexical_hits(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            packet = root / "task.json"
            packet.write_text(
                json.dumps(
                    {
                        "task_id": "H7-12",
                        "selected_result": "Symmetric backward error for a linear system",
                        "task_clarification": [],
                        "scope_constraints": [],
                    }
                ),
                encoding="utf-8",
            )
            atlas = root / "decls.jsonl"
            atlas.write_text(
                json.dumps(
                    {
                        "kind": "theorem",
                        "name": "N.symmetric_backward_error_for_lyapunov",
                        "module": "N.Lyapunov",
                        "source_file": "N/Lyapunov.lean",
                        "source_line": 1,
                        "signature": "theorem symmetric_backward_error_for_lyapunov : True",
                        "documentation": "",
                    }
                )
                + "\n",
                encoding="utf-8",
            )
            result, markdown = build_composition_packet(
                source_packet_path=packet,
                atlas_paths=[atlas],
                corpus_id="test",
            )
            self.assertEqual(result["route_status"], "NO_ROUTE")
            self.assertEqual(result["retrieved_roots"], [])
            self.assertIn(b"Do not search for a substitute", markdown)

    def test_is_deterministic(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            packet = root / "task.json"
            packet.write_text(
                json.dumps(
                    {
                        "task_id": "X",
                        "selected_result": "symmetric perturbation norm bound",
                        "task_clarification": [],
                        "scope_constraints": [],
                    }
                ),
                encoding="utf-8",
            )
            atlas = root / "decls.jsonl"
            atlas.write_text(
                json.dumps(
                    {
                        "kind": "theorem",
                        "name": "N.symmetric_perturbation_bound",
                        "module": "N.Perturbation",
                        "source_file": "N/Perturbation.lean",
                        "source_line": 1,
                        "signature": "theorem symmetric_perturbation_bound : True",
                        "documentation": "norm bound",
                    }
                )
                + "\n",
                encoding="utf-8",
            )
            first = build_composition_packet(
                source_packet_path=packet,
                atlas_paths=[atlas],
                corpus_id="test",
            )
            second = build_composition_packet(
                source_packet_path=packet,
                atlas_paths=[atlas],
                corpus_id="test",
            )
            self.assertEqual(first, second)

    def test_component_policy_allows_honest_empty_control_route(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            packet = root / "task.json"
            packet.write_text(json.dumps({
                "task_id": "TEST", "selected_result": "probabilistic inner product bound",
                "task_clarification": [], "scope_constraints": [],
            }), encoding="utf-8")
            atlas = root / "decls.jsonl"
            atlas.write_text(json.dumps({
                "kind": "theorem", "name": "Mathlib.unrelated",
                "module": "Mathlib.Data.Nat.Basic",
                "signature": "theorem unrelated : True",
            }) + "\n", encoding="utf-8")
            result, _ = build_composition_packet(
                source_packet_path=packet, atlas_paths=[atlas], corpus_id="test",
                selection_policy="component-roles-1",
            )
            self.assertEqual(result["route_status"], "NO_ROUTE")
            self.assertEqual(result["retrieved_roots"], [])


if __name__ == "__main__":
    unittest.main()
