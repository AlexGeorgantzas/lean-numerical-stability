# Higham Chapter 22 Source Coverage

- Source: `References/1.9780898718027.ch22.pdf`, printed pp. 415--431.
- Core status: **PASS (fresh strict re-audit)**.
- Exhaustive row inventory: `docs/chapter22/CHAPTER22_SOURCE_INVENTORY.md`.

| Source | Status and Lean surface |
|---|---|
| Vandermonde definition, Algorithm 22.1, (22.1)--(22.4) | PROVED end to end |
| Table 22.1 V1--V6 | SKIP-FIGURE-TABLE in core mode: these are literature-summary rows whose only source occurrence is the visual table; V7 remains a useful independently formalized extra |
| Table 22.1 V7 and Table 22.2 | PROVED |
| (22.5)--(22.17), Algorithm 22.2 | PROVED; repeated-node Hermite factorization and final solve |
| Algorithm 22.3 | PROVED for the separate printed natural-indexed executor via `higham22_algorithm22_3_eq_factorized`, with literal primal solve `higham22Hermite_algorithm22_3_solve` |
| (22.18)--(22.21), Theorem 22.4 | PROVED from the actual primitive rounded graph |
| (22.22), Corollary 22.5 | PROVED: `higham22_eq22_22_four_node_six_factor` is the literal four-node `U₀U₁U₂L₂L₁L₀` display, and the generic checkerboard/no-cancellation result is proved for all four named source bases |
| (22.23)--(22.25), Theorem 22.6 | PROVED conditional exactly on the source's general simplifying assumption (22.24) |
| Problem 22.8, Corollary 22.7 | PROVED: `higham22Closure_eq22_24_monomial` identifies every actual state-dependent rounded monomial Stage-II factor with the structured complex bidiagonal perturbation, proves nonsingularity and the inverse-entry coefficient, and `higham22_corollary22_7_monomial_residual_closed` supplies the source-facing residual endpoint without a target-bearing premise |
| Algorithm 22.8 / Problem 22.10 | PROVED |
| Refinement consequence on printed p. 428 | **SOURCE-DISCREPANCY + PROVED corrected finite path.** The literal claim that (12.9) holds with its conventional `γ_(n+1)/u` coefficient is false in the stated abstract standard model: `ch22b_literal12_9_gamma5_counterexample` supplies a valid `u = 1/100` model and proves, for the `n = 4` first-derivative row `[0,1,2,3]` and coefficients `[0,0,0,1]`, that the actual rounded Algorithm 5.2 plus final-subtraction error strictly exceeds `γ_5 (|b|+|A||x|)`. The faithful correction is the (12.8) residual-accuracy certificate with `t = generatedBudget/u`: `ch22b_horner_higher_derivative_higham12_8_certificate` covers every real derivative order, while `ch22bComplexConfluent_higham12_8_certificate` covers every complex node/multiplicity slot and identifies the executor with the existing confluent matrix row. `ch22bComplexConfluent_theorem12_3_exact_q_bound` composes the latter with the correction-solve and rounded-update models through the complex-norm Theorem 12.3 calculation to exact finite (12.10). The unquantified final asymptotic backward-stability sentence remains `DEFER-MISSING-PRECISE-STATEMENT`; the older geometric-convergence lemma is only a conditional corollary because it assumes `hcontract`. |

The source's *general* simplifying assumption (22.24) is represented by
`Higham22Eq22_24`, which is appropriate for conditional Theorem 22.6.  For
monomials, the new closure module derives that assumption from the actual
primitive rounded execution and Problem 22.8.  Table 22.1 remains a visual
literature-summary artifact under the core-mode figure/table rule, while the
unquantified refinement sentence is deferred rather than promoted into an
invented theorem.  The numbered p. 428 reference is not silently weakened:
the literal coefficient is terminated by a compiled counterexample, and the
corrected generated-budget (12.8) route is formalized for arbitrary derivative
order over both `ℝ` and the source's `ℂ` domain, including the final rounded
subtraction and exact finite (12.10), without circular premises. All selected
Chapter 22 obligations are therefore closed.
