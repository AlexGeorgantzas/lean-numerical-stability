import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic

namespace HighamBench

open scoped BigOperators

/-- The Lagrange-form value at a fixed evaluation point, with the values of
the Lagrange basis functions supplied as `ell`. -/
noncomputable def p13InterpolationValue {n : ℕ}
    (ell f : Fin n → ℝ) : ℝ :=
  ∑ i, ell i * f i

/-- Higham's componentwise condition number (2.2) for interpolation with
fixed nodes and evaluation point. -/
noncomputable def p13Condition {n : ℕ}
    (ell f : Fin n → ℝ) : ℝ :=
  (∑ i, |ell i * f i|) / |p13InterpolationValue ell f|

/-- The exact second barycentric formula, with `coeff i = w_i/(x-x_i)`. -/
noncomputable def p13BarycentricValue {n : ℕ}
    (coeff f : Fin n → ℝ) : ℝ :=
  p13InterpolationValue coeff f / p13InterpolationValue coeff (fun _ => 1)

/-- A finite certificate for a computed second barycentric formula: the
numerator terms and denominator terms receive separate additive errors. -/
noncomputable def p13BarycentricComputed {n : ℕ}
    (coeff f deltaNum deltaDen : Fin n → ℝ) : ℝ :=
  (∑ i, (coeff i * f i + deltaNum i)) /
    (∑ i, (coeff i + deltaDen i))

/-- Componentwise relative perturbation of a finite family of terms. -/
def p13TermPerturbation {n : ℕ}
    (v delta : Fin n → ℝ) (epsilon : ℝ) : Prop :=
  ∀ i, |delta i| ≤ epsilon * |v i|

end HighamBench
