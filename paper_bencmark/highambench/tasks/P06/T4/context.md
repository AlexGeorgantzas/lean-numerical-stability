# P06-T4 whole-paper context

Source: Michael P. Connolly and Nicholas J. Higham, “Probabilistic Rounding
Error Analysis of Householder QR Factorization,” SIAM Journal on Matrix
Analysis and Applications 44(3), 2023, pp. 1146–1163,
DOI 10.1137/22M1514817.

This T4 corpus follows the paper in source order. It records the standard
floating-point model, deterministic and probabilistic signed-product bounds,
Householder-vector and transformation-sequence semantics, the symmetric
dilation, matrix concentration results, the first-order perturbed-product
expansion, the comparison of higher-order size restrictions, two-sided
transformation composition, compact WY updating, the weighted QR backward
error, the weighted Procrustes result, and the exact experiment controls and
reported counts.

The paper assumes (m \ge n), unit roundoff (u), and mean-independent,
mean-zero rounding errors for its probabilistic analysis. Its key technical
qualification is that the local Householder perturbation bound used after
Lemma 4.1 is assumed to hold with probability one. The authors explicitly say
that removing this assumption would require a concentration result not then
available.

The conditional-expectation semantics additionally requires every generated
rounding or matrix history to be a sub-sigma-algebra of the ambient measurable
space. This is the standard well-formedness condition implicit in the paper's
use of random variables and prevents null-set representatives from making a
conditional-mean hypothesis vacuous.

The source-implicit unit-roundoff condition `u < 1` is explicit in the Lean
statement of Lemma 1.4. The rescaled Theorem 3.2 has a distinct source issue:
at `sigma = 0`, `r = 0`, and positive one-by-one dimensions, its event is
certain while its stated exponential upper bound is below one for sufficiently
large `lambda`. The literal assertion is therefore retained as a transparent
non-proof-bearing source report, not silently repaired with an extra premise.

Many displayed backward-error bounds contain unspecified “integer constants
of modest size” (c_i) and asymptotic (O(u^2)) terms. The source inventory
records those claims and their exact anchors, but does not invent numerical
constants or remainder quantifiers. Such source-underdetermined formulas are
not converted into proof obligations. Exact algebraic cores and fully
determinate named results retain controlled proof placeholders.

Sections 5 and 7 distinguish proved results from expectations and empirical
observations. The controlled semantics preserves the compact WY update,
two-sided composition, experiment parameters, and exact SuiteSparse counts.
Qualitative phrases such as “virtually identical,” “better indicator,”
“sufficiently large,” and “same order of magnitude” remain explicitly
non-theorem source records because the paper supplies no numerical threshold
that would determine a proposition.

The controlled target imports exactly `HighamBench.P06Definitions`. That
paper-local module supplies every custom statement-facing object and imports
only direct upstream Mathlib modules. It contains no NumStability reference,
proof helper, axiom, or proof hole.

