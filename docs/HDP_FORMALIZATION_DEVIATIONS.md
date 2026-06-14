# HDP Formalization Deviations and Corrections

This file records places where the Lean formalization intentionally differs from
the printed HDP statement, or where a book statement needs an additional
hypothesis, corrected constant, corrected formulation, or formalization note.

The goal is to keep a complete audit trail while the book is formalized. Each
entry should explain what changed, why the printed statement could not be
formalized as written, where the corrected source came from, and which Lean
names implement the corrected result.

## Chapter 2

| Book item | Status | Difference from printed statement | Reason | Corrected/formalized statement | Lean names |
|---|---|---|---|---|---|
| Exercise 2.4.5, very sparse random graph lower degree bound | Corrected and formalized | The unqualified printed `d = O(1)` version is not formalized as stated. The formal theorem uses the corrected `d = Θ(1)` hypothesis. | The unqualified statement is false when the expected degree is allowed to vanish; for example, `p = 0` gives no high-degree vertices. | The corrected theorem assumes eventual bounds `0 < d0 ≤ d ≤ D` and proves the displayed lower bound `(1/8) * log n / log log n` with probability tending to one, using the witness count `⌊(1/4) * log n / log log n⌋₊`. The correction and proof source is `helper_lean_code/exercises_2_4_4_2_4_5_solutions.pdf`. | `very_sparse_graphs_far_from_regular_probability_tendsto_one_corrected`, with supporting definitions `verySparseCorrectedWitnessScale`, `verySparseCorrectedWitnessCount`, `verySparseCorrectedLowerScale` in `LeanFpAnalysis/HDP/Probability/Concentration/RandomGraphs.lean`. |

## Entry Template

| Book item | Status | Difference from printed statement | Reason | Corrected/formalized statement | Lean names |
|---|---|---|---|---|---|
| Chapter/section/theorem/exercise | Pending/Corrected/Formalized/Not formalized | What changed | Why the printed statement needs adjustment | Exact corrected statement or summary | Main Lean declarations and file |
