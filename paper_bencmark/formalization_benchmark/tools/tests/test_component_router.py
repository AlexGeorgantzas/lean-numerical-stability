from __future__ import annotations

import unittest

from component_router import select_component_roots


def item(name: str, kind: str, module: str, score: float) -> dict:
    return {
        "score": score,
        "matched_terms": ["round", "error"],
        "field_matches": {"name": ["error"]},
        "record": {"name": name, "kind": kind, "module": module},
    }


class ComponentRouterTests(unittest.TestCase):
    def test_role_balance_beats_one_target_shaped_theorem(self) -> None:
        ranked = [
            item("NumStability.target_like_backward_error", "theorem", "NumStability.Algorithms.LU", 500),
            item("NumStability.fl_dotProduct", "def", "NumStability.Algorithms.DotProduct", 200),
            item("NumStability.dotProduct_backward_error", "theorem", "NumStability.Algorithms.DotProduct", 190),
            item("NumStability.FPModel", "structure", "NumStability.FloatingPoint.Model", 150),
            item("NumStability.FiniteProbability.eventProb", "def", "NumStability.Analysis.FiniteProbability", 120),
            item("NumStability.vecNorm2", "def", "NumStability.Analysis.Norms", 110),
        ]
        selected = select_component_roots(
            ranked, records=[entry["record"] for entry in ranked],
            source_text="stochastic rounding dot product forward error", limit=5
        )
        self.assertEqual(
            [entry["component_role"] for entry in selected],
            ["algorithm", "floating_point", "probability", "deterministic_error"],
        )

    def test_inductive_algorithm_and_no_irrelevant_fill(self) -> None:
        ranked = [
            item("NumStability.SumTree", "inductive", "NumStability.Algorithms.Summation.Tree.Core", 50),
            item("Mathlib.unrelated", "theorem", "Mathlib.Data.List.Basic", 49),
        ]
        selected = select_component_roots(
            ranked, records=[entry["record"] for entry in ranked],
            source_text="pairwise summation tree", limit=7
        )
        self.assertEqual([entry["record"]["name"] for entry in selected], ["NumStability.SumTree"])

    def test_limit_and_duplicate_module(self) -> None:
        ranked = [
            item(f"NumStability.fl_{index}", "def", "NumStability.Algorithms.Arithmetic", 100 - index)
            for index in range(5)
        ]
        self.assertEqual(len(select_component_roots(
            ranked, records=[entry["record"] for entry in ranked],
            source_text="a rounded arithmetic algorithm", limit=7
        )), 0)
        with self.assertRaises(ValueError):
            select_component_roots(ranked, records=[], source_text="", limit=0)

    def test_source_vocabulary_activates_core_not_target_shaped_name(self) -> None:
        ranked = [
            item("NumStability.unrelated_probabilistic_horner_forward_error", "theorem",
                 "NumStability.Algorithms.Horner", 900),
            item("fl_hornerDesc", "def", "NumStability.Algorithms.Horner", 30),
            item("fl_hornerDesc_forward_error_bound", "theorem", "NumStability.Algorithms.Horner", 20),
            item("NumStability.FPModel", "structure", "NumStability.FloatingPoint.Model", 10),
        ]
        selected = select_component_roots(
            ranked, records=[entry["record"] for entry in ranked],
            source_text="Horner evaluation with stochastic rounding", limit=4
        )
        self.assertEqual(selected[0]["record"]["name"], "fl_hornerDesc")
        self.assertNotIn("NumStability.unrelated_probabilistic_horner_forward_error",
                         [entry["record"]["name"] for entry in selected])

    def test_foundational_anchor_need_not_rank_lexically(self) -> None:
        ranked = [item("fl_hornerDesc", "def", "NumStability.Algorithms.Horner", 30)]
        atlas = [entry["record"] for entry in ranked] + [
            item("NumStability.FPModel", "structure", "NumStability.FloatingPoint.Model", 0)["record"]
        ]
        selected = select_component_roots(
            ranked, records=atlas, source_text="Horner under stochastic rounding", limit=4
        )
        self.assertEqual([entry["record"]["name"] for entry in selected],
                         ["fl_hornerDesc", "NumStability.FPModel"])


if __name__ == "__main__":
    unittest.main()
