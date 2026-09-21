from __future__ import annotations

from pathlib import Path
import sys
import unittest


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from evaluation_gate import evaluate_gate  # noqa: E402


class FakeController:
    def __init__(self, states):
        self.states = states

    def status(self, task_id):
        return self.states.get(task_id, {"task_id": task_id, "status": "NOT_STARTED"})


def complete(n_time, l_time, n_tokens, l_tokens):
    return {
        "status": "COMPLETE",
        "conditions": {
            "N": {
                "status": "ACCEPTED_FAITHFUL",
                "active_seconds": n_time,
                "contestant_net_new_usage": {"net_new_tokens": n_tokens},
            },
            "L": {
                "status": "ACCEPTED_FAITHFUL",
                "active_seconds": l_time,
                "contestant_net_new_usage": {"net_new_tokens": l_tokens},
                "library_uptake": {"library_uptake": True},
            },
        },
    }


class EvaluationGateTests(unittest.TestCase):
    def setUp(self):
        self.config = {
            "pilot_id": "test",
            "evaluation_gate": {
                "primary_task_ids": ["A", "B", "C", "D"],
                "minimum_time_positive_pairs": 3,
                "minimum_median_time_reduction_fraction": 0.2,
                "minimum_median_net_new_token_reduction_fraction": 0.2,
                "require_both_conditions_faithful": True,
                "forbid_incident_pairs": True,
                "canary_task_id": "H00-00",
                "canary_excluded_from_scientific_results": True,
            },
        }

    def test_passes_substantive_four_task_effect(self):
        states = {
            task: complete(100, l_time, 1000, l_tokens)
            for task, l_time, l_tokens in (
                ("A", 60, 500), ("B", 70, 700), ("C", 75, 750), ("D", 110, 900)
            )
        }
        result = evaluate_gate(FakeController(states), self.config)
        self.assertEqual(result["status"], "PASSED")
        self.assertEqual(result["time_positive_pairs"], 3)

    def test_pending_is_not_a_pass(self):
        result = evaluate_gate(FakeController({}), self.config)
        self.assertEqual(result["status"], "PENDING")


if __name__ == "__main__":
    unittest.main()
