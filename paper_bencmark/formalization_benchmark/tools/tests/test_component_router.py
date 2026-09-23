from __future__ import annotations

import unittest

from component_router import routing_anchor_text, select_component_roots


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
            item("NumStability.fl_hornerDesc", "def", "NumStability.Algorithms.Horner", 30),
            item("NumStability.fl_hornerDesc_forward_error_bound", "theorem", "NumStability.Algorithms.Horner", 20),
            item("NumStability.FPModel", "structure", "NumStability.FloatingPoint.Model", 10),
        ]
        selected = select_component_roots(
            ranked, records=[entry["record"] for entry in ranked],
            source_text="Horner evaluation with stochastic rounding", limit=4
        )
        self.assertEqual(selected[0]["record"]["name"], "NumStability.fl_hornerDesc")
        self.assertNotIn("NumStability.unrelated_probabilistic_horner_forward_error",
                         [entry["record"]["name"] for entry in selected])

    def test_foundational_anchor_need_not_rank_lexically(self) -> None:
        ranked = [item("NumStability.fl_hornerDesc", "def", "NumStability.Algorithms.Horner", 30)]
        atlas = [entry["record"] for entry in ranked] + [
            item("NumStability.FPModel", "structure", "NumStability.FloatingPoint.Model", 0)["record"]
        ]
        selected = select_component_roots(
            ranked, records=atlas, source_text="Horner under stochastic rounding", limit=4
        )
        self.assertEqual([entry["record"]["name"] for entry in selected],
                         ["NumStability.fl_hornerDesc", "NumStability.FPModel"])

    def test_negative_scope_does_not_activate_forbidden_algorithm(self) -> None:
        packet = {
            "selected_result": "probabilistic error bound for general summation trees",
            "scope_constraints": [
                "Do not specialize to recursive summation or pairwise summation."
            ],
        }
        ranked = [
            item("NumStability.SumTree", "inductive", "NumStability.Algorithms.Summation.Tree.Core", 20),
            item("NumStability.fl_recursiveSum", "def", "NumStability.Algorithms.Summation.Recursive.Core", 19),
            item("NumStability.SumTree.statisticalRunningErrorContribution_rms_le", "theorem",
                 "NumStability.Algorithms.Summation.Tree.Core", 18),
        ]
        selected = select_component_roots(
            ranked, records=[entry["record"] for entry in ranked],
            source_text=routing_anchor_text(packet), limit=10,
        )
        self.assertEqual(
            [entry["record"]["name"] for entry in selected],
            ["NumStability.SumTree",
             "NumStability.SumTree.statisticalRunningErrorContribution_rms_le"],
        )

    def test_hyphenated_algorithm_title_matches_public_family(self) -> None:
        ranked = [
            item("NumStability.DoolittleLU", "structure", "NumStability.Algorithms.LU", 20),
        ]
        selected = select_component_roots(
            ranked, records=[entry["record"] for entry in ranked],
            source_text="probabilistic Gaussian-elimination solution bound", limit=10,
        )
        self.assertEqual([entry["record"]["name"] for entry in selected],
                         ["NumStability.DoolittleLU"])

    def test_least_squares_backward_error_exposes_quantity_not_result(self) -> None:
        names = (
            "NumStability.lsNormwiseBackwardErrorMatrixOnlyEtaF",
            "NumStability.RectLSNormalEquations",
            "NumStability.RectLSNormalEquations.iff_isLeastSquaresMinimizer",
            "NumStability.lsNormwiseBackwardErrorEtaF_tendsto_matrixOnlyEtaF_atTop",
        )
        ranked = [item(name, "def" if index < 2 else "theorem",
                       "NumStability.Algorithms.LeastSquares.LSQRSolve", 20 - index)
                  for index, name in enumerate(names)]
        selected = select_component_roots(
            ranked, records=[entry["record"] for entry in ranked],
            source_text="matrix-only least-squares backward error at zero vector",
            limit=10,
        )
        self.assertEqual([entry["record"]["name"] for entry in selected[:3]],
                         list(names[:3]))
        self.assertNotIn(names[3], [entry["record"]["name"] for entry in selected])

    def test_block_summation_routes_arbitrary_length_composition_components(self) -> None:
        names = (
            "NumStability.fl_recursiveSum",
            "NumStability.fl_higherPrecisionRecursiveSum",
            "NumStability.fl_clog2PairwiseSum",
            "NumStability.clog2PairwiseSum_backward_error",
            "NumStability.FPModel",
            "NumStability.gamma",
        )
        ranked = [item(name, "theorem" if "backward_error" in name else "def",
                       "NumStability.Algorithms.Summation", 20 - index)
                  for index, name in enumerate(names)]
        records = [entry["record"] for entry in ranked]
        high = select_component_roots(
            ranked, records=records,
            source_text="recursive block sums and extended-precision recursive accumulation",
            limit=10,
        )
        pair = select_component_roots(
            ranked, records=records,
            source_text="recursive block sums and pairwise accumulation",
            limit=10,
        )
        self.assertEqual([entry["record"]["name"] for entry in high[:2]],
                         [names[0], names[1]])
        self.assertEqual([entry["record"]["name"] for entry in pair[:2]],
                         [names[0], names[2]])
        self.assertIn(names[3], [entry["record"]["name"] for entry in pair])

    def test_contextual_policy_omits_stochastic_cards_for_deterministic_source(self) -> None:
        ranked = [
            item("NumStability.fl_clog2PairwiseSum", "def",
                 "NumStability.Algorithms.Summation.Pairwise.Core", 30),
            item("NumStability.FiniteProbability.eventProb", "def",
                 "NumStability.Analysis.FiniteProbability", 29),
            item("NumStability.SumTree.statisticalRunningErrorContribution_rms_le",
                 "theorem", "NumStability.Algorithms.Summation.Tree.Core", 28),
        ]
        selected = select_component_roots(
            ranked, records=[entry["record"] for entry in ranked],
            source_text="pairwise summation deterministic backward error",
            limit=10, strict_stochastic_roles=True,
        )
        self.assertEqual([entry["record"]["name"] for entry in selected],
                         ["NumStability.fl_clog2PairwiseSum"])

    def test_composite_compensated_title_routes_both_algorithms(self) -> None:
        names = ("NumStability.fl_recursiveSum", "NumStability.fl_kahanSum",
                 "NumStability.FPModel")
        ranked = [item(name, "def", "NumStability.Algorithms.Summation", 20 - i)
                  for i, name in enumerate(names)]
        selected = select_component_roots(
            ranked, records=[entry["record"] for entry in ranked],
            source_text="recursive working-precision block sums and compensated accumulation",
            limit=10, strict_stochastic_roles=True,
        )
        self.assertEqual([entry["record"]["name"] for entry in selected[:2]],
                         list(names[:2]))

    def test_superblock_title_routes_base_and_two_level_components(self) -> None:
        names = ("NumStability.fl_dotProduct", "NumStability.fl_blockDotProduct")
        ranked = [item(name, "def", "NumStability.Algorithms.DotProduct", 20 - i)
                  for i, name in enumerate(names)]
        selected = select_component_roots(
            ranked, records=[entry["record"] for entry in ranked],
            source_text="three-level superblock dot product forward error",
            limit=10, strict_stochastic_roles=True,
        )
        self.assertEqual([entry["record"]["name"] for entry in selected[:2]],
                         list(names))

    def test_nearest_rounding_title_exposes_finite_format_without_target(self) -> None:
        names = (
            "NumStability.fl_recursiveSum",
            "NumStability.FloatingPointFormat",
            "NumStability.FloatingPointFormat.finiteSystem",
            "NumStability.FloatingPointFormat.nearestRoundingToFinite",
            "NumStability.FPModel",
            "NumStability.gamma",
            "NumStability.recursiveSum_forward_error_bound",
        )
        ranked = [item(name, "def", "NumStability.Analysis.FloatingPointArithmetic", 20 - i)
                  for i, name in enumerate(names)]
        selected = select_component_roots(
            ranked, records=[entry["record"] for entry in ranked],
            source_text="unrestricted recursive summation in rounding to nearest",
            limit=12, strict_stochastic_roles=True,
        )
        selected_names = [entry["record"]["name"] for entry in selected]
        self.assertEqual(selected_names[:6], list(names[:6]))
        self.assertIn(names[6], selected_names)

    def test_generic_rounding_title_does_not_add_finite_format_cards(self) -> None:
        names = (
            "NumStability.fl_hornerDesc", "NumStability.FPModel",
            "NumStability.gamma", "NumStability.FloatingPointFormat",
        )
        ranked = [item(name, "def", "NumStability.Analysis.FloatingPointArithmetic", 20 - i)
                  for i, name in enumerate(names)]
        selected = select_component_roots(
            ranked, records=[entry["record"] for entry in ranked],
            source_text="Horner forward error under a generic rounding model",
            limit=12, strict_stochastic_roles=True,
        )
        self.assertNotIn(names[3], [entry["record"]["name"] for entry in selected])


if __name__ == "__main__":
    unittest.main()
