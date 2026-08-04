import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import NumStability.Analysis.LinearOperators.NumericalRadius.Core.Basic

/-!
# Analysis.NumericalRadius

Historical declaration-bearing facade. Genuine-private and ambient-context retention closure remains here with its original identity.
-/

/-
Analysis/NumericalRadius.lean

The matrix numerical radius `r(A)` and its norm sandwich, formalizing the
auxiliary bounds of Higham, *Accuracy and Stability of Numerical Algorithms*,
2nd ed., Section 18.1 (Matrix Powers).

Higham §18.1 records, for `A ∈ ℂ^{n×n}`, the field of values / numerical range
`W(A) = { z*Az / z*z : z ≠ 0 }` and the numerical radius `r(A) = max |W(A)|`,
together with:

  * the sandwich          `‖A‖₂ / 2 ≤ r(A) ≤ ‖A‖₂`                     (§18.1)
  * the power bound        `‖A^k‖₂ ≤ 2 · r(A)^k`                        (§18.1)

which in turn factors through Berger's power inequality `r(A^k) ≤ r(A)^k`.

This file delivers, over `ℂ` (the numerical radius is degenerate over `ℝ`: for a
real matrix `W(A)` collapses to a real interval and the factor of two is
vacuous):

  * `numericalRadius A`               -- `r(A)` as `⨆ x, ‖⟪Ax, x⟫‖ / ‖x‖²`
  * `numericalRadius_nonneg`
  * `numericalRadius_le_opNorm`       -- `r(A) ≤ ‖A‖₂`   (Cauchy–Schwarz, §18.1)
  * `opNorm_le_two_mul_numericalRadius`
                                      -- `‖A‖₂ ≤ 2 · r(A)`   (§18.1, polarization)
  * `norm_pow_le_two_mul_numericalRadius_pow_of_le`
                                      -- `‖A^k‖₂ ≤ 2 · r(A)^k` GIVEN Berger's
                                         inequality `r(A^k) ≤ r(A)^k` as a
                                         hypothesis (honest conditional closure).

The matrix 2-norm `‖A‖₂` used here is Mathlib's `l2` operator norm on finite
complex matrices (`Matrix.instL2OpNormedAddCommGroup`, scope
`Matrix.Norms.L2Operator`), transported to `EuclideanSpace ℂ (Fin n)` through the
star-algebra equivalence `Matrix.toEuclideanCLM`.

SCOPE / DEFERRAL.  Berger's power inequality `r(A^k) ≤ r(A)^k` is *genuinely
absent* from Mathlib and is NOT proved here.  Its standard proof relies on the
unitary-dilation / power-inequality machinery (equivalently the positivity
characterization `Re (I - zA)⁻¹ ≥ 0` for `‖A‖ ≤ 1`), none of which is available:
Mathlib has no numerical range, numerical radius, field of values, or unitary
dilation development (a grep for `numericalRange` / `numericalRadius` /
`fieldOfValues` returns zero hits).  Consequently the unconditional §18.1 target
`‖A^k‖₂ ≤ 2 · r(A)^k` cannot be assembled here; we expose the achievable half
`‖A^k‖₂ ≤ 2 · r(A^k)` and the conditional closure that consumes Berger's
inequality as an explicit hypothesis.
-/





open scoped Matrix.Norms.L2Operator InnerProductSpace
open RCLike ComplexConjugate

namespace NumStability

noncomputable section

variable {n : ℕ}

/-- The complex Euclidean space `ℂⁿ` used as the ambient inner-product space for
the numerical range.  A local abbreviation to keep signatures short. -/
local notation "𝔼" => EuclideanSpace ℂ (Fin n)

/-!
### The numerical radius of a continuous linear operator on `ℂⁿ`

We first develop everything for a continuous linear map `T : ℂⁿ →L[ℂ] ℂⁿ` and
then transport to matrices through `Matrix.toEuclideanCLM`.
-/



































































































































/-!
### The numerical radius of a complex matrix

We transport the operator definition through `Matrix.toEuclideanCLM`, the
star-algebra equivalence `Matrix (Fin n) (Fin n) ℂ ≃⋆ₐ[ℂ] (ℂⁿ →L[ℂ] ℂⁿ)`, whose
image operator has the same `l2` operator norm (`Matrix.l2_opNorm_toEuclideanCLM`)
and respects powers (`map_pow`).
-/









































/-!
### Matrix powers (Higham §18.1)

The achievable half of the §18.1 power bound `‖A^k‖₂ ≤ 2 · r(A)^k`, plus its
honest conditional closure.
-/
































end

end NumStability
