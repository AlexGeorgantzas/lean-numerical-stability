# Chapter 21 Not-Proved Ledger

## Selected-Scope Gate

**PASS.** All 21 selected mathematical and algorithmic source rows are proved.
The Givens alternative in Theorem 21.4, square scalar Q-method boundary, and
actual Householder SNE equation (21.11) each passed focused compilation and
source/axiom review. The SNE row is closed by the fixed-radius theorem
`higham21_sne_householder_actual_output_source_relative_q_uniform` and its
explicit unit-roundoff-squared corollary
`higham21_sne_householder_actual_output_source_relative_unit_roundoff_sq`, not
by a conditional replay certificate, target-shaped transferred-envelope
premise, or fixed-precision tautological remainder. This ledger now records
only the intentional exclusions and honest model boundaries below; no selected
row is unproved.

## Intentional Exclusions

| Category | Source rows | Reason |
|---|---|---|
| Qualitative negative/approximate prose | SNE negative warning; corrected-MGS “essentially” stable sentence | No precise theorem or coefficient is stated |
| Empirical output | Vandermonde experiment and Table 21.1 | Historical execution is underspecified |
| Editorial catalogue | LAPACK descriptions | Documentation rather than mathematical claims |
| Optional problem | Problem 21.1 and (21.12)–(21.14) | Not selected in core mode |

## Honest Model Boundaries

- `FPModel` is the repository’s abstract rounded-operation semantics, not a
  reconstruction of the historical experiment.
- For the final SNE relative theorem, `hm`, `hn`, `hdet`, and `hb` are
  source/domain assumptions: positive and sufficient dimensions, full row
  rank through Gram nonsingularity, and a nonzero right-hand side for relative
  normalization.
- Its `gammaValid` premises (`hvalidQR` and `hmGamma`) are floating-point
  validity assumptions; `hdiag` is the computed triangular nonbreakdown guard;
  and `hrho_pos` asserts positivity of the Householder perturbation scale.
- The source-facing uniform theorem uses a fixed master radius with
  `gamma_m + rho ≤ tau < 1`,
  `higham21Eq21_11UniformGramContraction A tau < 1`, and
  `tau * higham21SNEQUniformSolveMultiplier A tau ≤ 1/2`. The explicit
  `fp.u²` corollary additionally assumes `(m : ℝ) * fp.u ≤ 1/2` and the
  corresponding Householder QR-index product with `fp.u` is at most `1/2`.
- The SNE claim is a forward result only. No nearby minimum-norm
  backward-stability result or general residual theorem is asserted for SNE.
- The final SNE theorem derives a source-defined quadratic coefficient that
  depends only on `A`, `b`, the dimensions, and `tau`; the explicit corollary
  multiplies it by `fp.u²`. No active QR direction, nearby factor, or rounded
  normal solution occurs in that coefficient. This is a pointwise finite
  unit-roundoff theorem rather than a separate `Asymptotics.IsBigO` family
  declaration.
- Legacy records and coarse Gram-envelope theorems in
  `UnderdeterminedSpec.lean` and `UnderdeterminedSolve.lean` are compatibility
  surfaces, not the evidence used to close the selected source rows.
