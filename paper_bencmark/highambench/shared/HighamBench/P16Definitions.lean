import HighamBench.Core
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Matrix.Normed

/-!
# HighamBench P16 definitions

Paper-scoped finite-dimensional notation for the modular backward-error
analysis of GMRES and restarted GMRES.
-/

namespace HighamBench

open scoped BigOperators Matrix.Norms.Frobenius

/-- A finite square real matrix in the P16 model. -/
abbrev P16Matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- A finite real vector in the P16 model. -/
abbrev P16Vector (n : ℕ) := Fin n → ℝ

/-- Exact finite matrix-vector multiplication. -/
noncomputable def p16MatVec {n : ℕ} (A : P16Matrix n)
    (x : P16Vector n) : P16Vector n :=
  fun i ↦ ∑ j : Fin n, A i j * x j

/-- Frobenius norm used in the paper's normwise backward error. -/
noncomputable def p16FrobNorm {n : ℕ} (A : P16Matrix n) : ℝ :=
  ‖A‖

/-- Euclidean vector norm. -/
noncomputable def p16VecNorm {n : ℕ} (x : P16Vector n) : ℝ :=
  Real.sqrt (∑ i : Fin n, x i ^ 2)

/-- Exact residual `b - A x`. -/
noncomputable def p16Residual {n : ℕ} (A : P16Matrix n)
    (b x : P16Vector n) : P16Vector n :=
  b - p16MatVec A x

/-- A square matrix is nonsingular when its exact matrix-vector action is a
bijection. -/
def p16IsNonsingular {n : ℕ} (A : P16Matrix n) : Prop :=
  Function.Bijective (p16MatVec A)

/-- The shared relative perturbation condition in the paper's normwise
backward-error definition. -/
def p16NormwiseBackwardErrorAdmissible {n : ℕ}
    (A : P16Matrix n) (b xHat : P16Vector n) (epsilon : ℝ) : Prop :=
  ∃ deltaA : P16Matrix n, ∃ deltaB : P16Vector n,
    p16MatVec (A + deltaA) xHat = b + deltaB ∧
      p16FrobNorm deltaA ≤ epsilon * p16FrobNorm A ∧
      p16VecNorm deltaB ≤ epsilon * p16VecNorm b

/-- The normalized residual on the right-hand side of the paper's exact
normwise backward-error formula. -/
noncomputable def p16NormalizedResidual {n : ℕ}
    (A : P16Matrix n) (b xHat : P16Vector n) : ℝ :=
  p16VecNorm (p16Residual A b xHat) /
    (p16FrobNorm A * p16VecNorm xHat + p16VecNorm b)

/-- A scalar remainder that is second order in `scale` along `l`. Dimensions
and the fixed refinement iteration are outside the limit, so the hidden Big-O
constant may depend on them exactly as in the paper's convention. -/
def p16SecondOrderAt {ι : Type*} (l : Filter ι) (scale remainder : ι → ℝ) : Prop :=
  remainder =O[l] fun t ↦ scale t ^ 2

/-- A precise interpretation of the paper's `≲`: the inequality holds after
adding an otherwise unspecified second-order remainder. -/
def p16FirstOrderLeAt {ι : Type*} (l : Filter ι) (scale lhs rhs : ι → ℝ) : Prop :=
  ∃ remainder : ι → ℝ,
    p16SecondOrderAt l scale remainder ∧
      ∀ᶠ t in l, lhs t ≤ rhs t + |remainder t|

/-- One computed generic iterative-refinement step in the backward-error
clause of Lemma 4.2. It records exactly the normwise operation models (4.1),
(4.2), and (4.14), together with the first-order iterate comparison used in
the proof of (4.15). -/
structure P16Lemma42BackwardStep {n : ℕ} {ι : Type*}
    (l : Filter ι) (scale : ι → ℝ)
    (A : P16Matrix n) (b : P16Vector n) (_iteration : ℕ) where
  xHat : ι → P16Vector n
  correctionHat : ι → P16Vector n
  xHatNext : ι → P16Vector n
  residualHat : ι → P16Vector n
  deltaR : ι → P16Vector n
  deltaX : ι → P16Vector n
  epsilonR : ι → ℝ
  epsilonU : ι → ℝ
  w : ι → ℝ
  omega : ι → ℝ
  residual_equation : ∀ t,
    residualHat t = p16Residual A b (xHat t) + deltaR t
  update_equation : ∀ t,
    xHatNext t = xHat t + correctionHat t + deltaX t
  correction_residual_bound : ∀ t,
    p16VecNorm (residualHat t - p16MatVec A (correctionHat t)) ≤
      w t * p16VecNorm (p16Residual A b (xHat t)) +
        omega t *
          (p16VecNorm b + p16FrobNorm A * p16VecNorm (xHatNext t))
  residual_error_bound : ∀ t,
    p16VecNorm (deltaR t) ≤
      epsilonR t *
        (p16VecNorm b + p16FrobNorm A * p16VecNorm (xHat t))
  update_error_bound : ∀ t,
    p16VecNorm (deltaX t) ≤ epsilonU t * p16VecNorm (xHatNext t)
  epsilonR_nonneg : ∀ t, 0 ≤ epsilonR t
  epsilonU_nonneg : ∀ t, 0 ≤ epsilonU t
  w_nonneg : ∀ t, 0 ≤ w t
  omega_nonneg : ∀ t, 0 ≤ omega t
  epsilonR_tendsto_zero : Filter.Tendsto epsilonR l (nhds 0)
  epsilonU_tendsto_zero : Filter.Tendsto epsilonU l (nhds 0)
  iterate_norm_comparison :
    p16FirstOrderLeAt l scale
      (fun t ↦ p16VecNorm (xHat t))
      (fun t ↦ p16VecNorm (xHatNext t))

/-- Frobenius condition-number factor represented by a matrix and a supplied
inverse. The T3 target needs only its exact nonnegativity. -/
noncomputable def p16ConditionNumberF {n : ℕ}
    (A Ainv : P16Matrix n) : ℝ :=
  p16FrobNorm A * p16FrobNorm Ainv

/-- The mixed-precision contraction factor from Theorem 6.3. -/
noncomputable def p16MixedContraction {n : ℕ}
    (c uLow : ℝ) (A Ainv : P16Matrix n) : ℝ :=
  c * uLow * p16ConditionNumberF A Ainv

/-- High-precision backward-error floor from Theorem 6.3. -/
noncomputable def p16BackwardFloor (c uHigh : ℝ) : ℝ :=
  c * uHigh

/-- High-precision forward-error floor from Theorem 6.3. -/
noncomputable def p16ForwardFloor {n : ℕ}
    (c uHigh : ℝ) (A Ainv : P16Matrix n) : ℝ :=
  c * uHigh * p16ConditionNumberF A Ainv

end HighamBench
