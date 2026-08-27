import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Matrix.Normed

namespace HighamBench

open scoped BigOperators

/-- Paper-scoped vector infinity norm used in the row and column scalings
around equations (3.1)--(3.4). -/
noncomputable def p20InfNormVec {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ‖x‖

/-- Scale a finite row or column by a real power-of-two factor. -/
def p20ScaleVec {n : ℕ} (lambda : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => lambda * x i

/-- Paper-scoped rectangular infinity norm (maximum absolute row sum). -/
noncomputable def p20InfNormRect {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : ℝ :=
  let rowSum : Fin m → NNReal :=
    fun i => ∑ j : Fin n, ‖A i j‖₊
  ((Finset.univ.sup rowSum : NNReal) : ℝ)

/-- The input-underflow part of the simplified single-word bound (3.26). -/
noncomputable def p20SingleInputUnderflowBound {m n q : ℕ}
    (theta gmin : ℝ) (A : Fin m → Fin n → ℝ)
    (B : Fin n → Fin q → ℝ) : ℝ :=
  (4 * (n : ℝ) ^ 2 * theta⁻¹ * gmin) *
    p20InfNormRect A * p20InfNormRect B

/-- The accumulation-underflow part of the simplified single-word bound
(3.26). -/
noncomputable def p20SingleAccumUnderflowBound {m n q : ℕ}
    (theta Gmin : ℝ) (A : Fin m → Fin n → ℝ)
    (B : Fin n → Fin q → ℝ) : ℝ :=
  (4 * (n : ℝ) ^ 2 * (theta⁻¹) ^ 2 * Gmin) *
    p20InfNormRect A * p20InfNormRect B

/-- The range-unrestricted coefficient in the multiword bound (4.33). -/
def p20MultiRangeFreeCoefficient (n p : ℕ) (u U : ℝ) : ℝ :=
  ((p : ℝ) + 1) * u ^ p + ((n : ℝ) + (p : ℝ) ^ 2) * U

/-- The input-underflow term added in the multiword bound (4.32). -/
noncomputable def p20MultiInputUnderflowCoefficient
    (n p : ℕ) (u theta gmin : ℝ) : ℝ :=
  4 * (n : ℝ) * u ^ (p - 1) * theta⁻¹ * gmin

/-- The accumulation-underflow term added in the multiword bound (4.32). -/
noncomputable def p20MultiAccumUnderflowCoefficient
    (n p : ℕ) (theta Gmin : ℝ) : ℝ :=
  2 * (p : ℝ) * ((p : ℝ) + 1) * (n : ℝ) ^ 2 *
    (theta⁻¹) ^ 2 * Gmin

/-- The complete narrow-range coefficient in the multiword bound (4.32). -/
noncomputable def p20MultiNarrowCoefficient
    (n p : ℕ) (u U theta gmin Gmin : ℝ) : ℝ :=
  p20MultiRangeFreeCoefficient n p u U +
    p20MultiInputUnderflowCoefficient n p u theta gmin +
      p20MultiAccumUnderflowCoefficient n p theta Gmin

/-- Apply a scalar coefficient to the product of the two rectangular matrix
infinity norms appearing in (3.26), (4.32), and (4.33). -/
noncomputable def p20NormwiseEnvelope {m n q : ℕ}
    (coefficient : ℝ) (A : Fin m → Fin n → ℝ)
    (B : Fin n → Fin q → ℝ) : ℝ :=
  coefficient * p20InfNormRect A * p20InfNormRect B

end HighamBench
