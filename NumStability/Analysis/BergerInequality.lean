import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.LinearAlgebra.Matrix.Hermitian
import NumStability.Analysis.LinearOperators.NumericalRadius.Berger.Hermitian
import NumStability.Analysis.NumericalRadius

/-!
# Analysis.BergerInequality

Historical declaration-bearing facade. Genuine-private and ambient-context retention closure remains here with its original identity.
-/

/-
Analysis/BergerInequality.lean

Berger's power inequality for the numerical radius, `r(A^k) ≤ r(A)^k`, from
Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., Section 18.1
(Matrix Powers), p. 345.

The file `Analysis/NumericalRadius.lean` develops the matrix numerical radius
`r(A) = ⨆ x, ‖⟪A x, x⟫‖ / ‖x‖²` and the norm sandwich `‖A‖₂/2 ≤ r(A) ≤ ‖A‖₂`,
and closes the §18.1 power bound `‖A^k‖₂ ≤ 2 · r(A)^k` *conditionally* on
Berger's inequality `r(A^k) ≤ r(A)^k`
(`norm_pow_le_two_mul_numericalRadius_pow_of_le`).

Berger's inequality in full generality (Higham §18.1, p. 345) rests on the
unitary-dilation / power-inequality machinery, which is genuinely absent from
Mathlib v4.29 (no numerical range, field of values, or unitary dilation
development: a grep for `numericalRange` / `fieldOfValues` / `unitaryDilation`
returns zero hits).  This file establishes the inequality **unconditionally on
the self-adjoint (Hermitian) subclass**, which is the case in which Berger's
inequality is elementary and where it in fact holds with equality-flavoured
strength; and it packages the resulting *unconditional* §18.1 power bound for
Hermitian matrices.

The mechanism is the identity

  `r(T) = ‖T‖`   for self-adjoint `T`                         (Hermitian case)

which for the numerical radius `r(T) = ⨆ ‖⟪T x, x⟫‖/‖x‖²` follows from Mathlib's
Rayleigh-quotient norm formula `ContinuousLinearMap.norm_eq_iSup_rayleighQuotient`
together with the reality `⟪T x, x⟫ ∈ ℝ` of the quadratic form of a symmetric
operator (`LinearMap.IsSymmetric.coe_reApplyInnerSelf_apply`).  Berger for the
Hermitian class is then

  `r(A^k) = ‖A^k‖ ≤ ‖A‖^k = r(A)^k`,

the middle step being sub-multiplicativity of the operator norm
(`norm_pow_le`), valid in any normed ring, and `A^k` being Hermitian whenever
`A` is (`IsSelfAdjoint.pow`).

Main results (all over `ℂ`, no `sorry`/`axiom`, standard axioms only):

  * `numericalRadiusCLM_eq_opNorm_of_isSelfAdjoint`
        -- `r(T) = ‖T‖` for self-adjoint operators `T` on `ℂⁿ`.
  * `numericalRadius_eq_opNorm_of_isHermitian`
        -- `r(A) = ‖A‖₂` for Hermitian matrices `A`.
  * `numericalRadius_pow_le_of_isHermitian`
        -- Berger's inequality `r(A^k) ≤ r(A)^k`, UNCONDITIONALLY, for Hermitian
           `A` (Higham §18.1, p. 345).
  * `norm_pow_le_two_mul_numericalRadius_pow_of_isHermitian`
        -- the full §18.1 power bound `‖A^k‖₂ ≤ 2 · r(A)^k`, UNCONDITIONALLY,
           for Hermitian `A`.

HONEST SCOPE.  Berger's inequality for *general* complex `A` is NOT proved here;
that requires unitary-dilation machinery absent from Mathlib.  What is
unconditional here is the Hermitian case (a genuine, standard sub-result), which
discharges the `hBerger` hypothesis of
`NumericalRadius.norm_pow_le_two_mul_numericalRadius_pow_of_le` on that subclass.
Nothing is smuggled: the Hermitian hypothesis is a real restriction, stated
explicitly, and the conclusion is the printed §18.1 bound at full strength on it.
-/






open scoped Matrix.Norms.L2Operator InnerProductSpace
open RCLike ComplexConjugate

namespace NumStability

noncomputable section

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℂ (Fin n)

/-!
### The Hermitian identity `r(T) = ‖T‖`

For a self-adjoint operator the quadratic form `x ↦ ⟪T x, x⟫` is real, so the
numerical radius (which measures `‖⟪T x, x⟫‖`) coincides with the supremum of the
absolute Rayleigh quotient, which Mathlib identifies with the operator norm.
-/












































/-!
### Berger's inequality for the Hermitian class (Higham §18.1, p. 345)
-/























































end

end NumStability
