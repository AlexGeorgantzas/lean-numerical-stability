import HighamBench.Core
import Mathlib.Analysis.Matrix.Normed

/-!
# HighamBench P03 definitions

Condition-neutral finite matrix/vector notation and the execution contract for
the Carson--Higham three-precision iterative-refinement tasks. This file
contains no evaluated-library import.
-/

namespace HighamBench

open scoped BigOperators

/-- Finite real matrix-vector multiplication used in the P03 paper model. -/
noncomputable def p03MatVec {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j : Fin n, A i j * x j

/-- Finite real matrix multiplication used in the P03 paper model. -/
noncomputable def p03MatMul {n : ℕ}
    (A B : Fin n → Fin n → ℝ) (i k : Fin n) : ℝ :=
  ∑ j : Fin n, A i j * B j k

/-- Componentwise absolute value of a P03 vector. -/
noncomputable def p03VecAbs {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => |x i|

/-- Componentwise absolute value of a P03 matrix. -/
noncomputable def p03MatAbs {n : ℕ}
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => |A i j|

/-- Vector infinity norm used in P03. -/
noncomputable def p03VecInfNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ‖x‖

/-- Induced matrix infinity norm used in P03. -/
noncomputable def p03MatInfNorm {n : ℕ}
    (A : Fin n → Fin n → ℝ) : ℝ :=
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℝ)
  ‖(Matrix.of A : Matrix (Fin n) (Fin n) ℝ)‖

/-- Number of nonzeros in one row of the augmented matrix `[A b]`. -/
noncomputable def p03AugmentedRowNnz {n : ℕ}
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ) (i : Fin n) : ℕ :=
  (Finset.univ.filter fun j : Fin n => A i j ≠ 0).card +
    if b i ≠ 0 then 1 else 0

/-- Maximum number `p` of nonzeros in a row of `[A b]`. -/
noncomputable def p03MaxAugmentedRowNnz {n : ℕ}
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ) : ℕ :=
  Finset.univ.sup (p03AugmentedRowNnz A b)

/-- A complete real-valued execution certificate for the unscaled Algorithm
1.1 model used in P03 Theorem 4.1. The equations and inequalities are the
exact error representations (3.3), (3.6), and solver condition (2.4).
Real-valued states encode the paper's finite standard-model regime, in which
underflow and overflow are excluded. -/
structure P03NormwiseIRRun (n : ℕ) where
  dimension_pos : 0 < n
  A : Fin n → Fin n → ℝ
  Ainv : Fin n → Fin n → ℝ
  b : Fin n → ℝ
  x : ℕ → Fin n → ℝ
  rHat : ℕ → Fin n → ℝ
  dHat : ℕ → Fin n → ℝ
  deltaR : ℕ → Fin n → ℝ
  deltaX : ℕ → Fin n → ℝ
  uR : ℝ
  u : ℝ
  uS : ℝ
  uF : ℝ
  c1 : ℕ → ℝ
  c2 : ℕ → ℝ
  uR_nonneg : 0 ≤ uR
  uR_le_u : uR ≤ u
  u_le_uS : u ≤ uS
  uS_le_uF : uS ≤ uF
  gamma_valid : GammaValid uR (p03MaxAugmentedRowNnz A b)
  c1_nonneg : ∀ i, 0 ≤ c1 i
  c2_nonneg : ∀ i, 0 ≤ c2 i
  inverse_action : ∀ (z : Fin n → ℝ) (j : Fin n),
    p03MatVec Ainv (p03MatVec A z) j = z j
  residual_equation : ∀ (i : ℕ) (j : Fin n),
    rHat i j = b j - p03MatVec A (x i) j + deltaR i j
  residual_error_bound : ∀ (i : ℕ) (j : Fin n),
    |deltaR i j| ≤
      uS * |b j - p03MatVec A (x i) j| +
        (1 + uS) * gamma uR (p03MaxAugmentedRowNnz A b) *
          (|b j| + p03MatVec (p03MatAbs A) (p03VecAbs (x i)) j)
  correction_solver_bound : ∀ i : ℕ,
    p03VecInfNorm (fun j => rHat i j - p03MatVec A (dHat i) j) ≤
      uS *
        (c1 i * p03MatInfNorm A * p03VecInfNorm (dHat i) +
          c2 i * p03VecInfNorm (rHat i))
  update_equation : ∀ (i : ℕ) (j : Fin n),
    x (i + 1) j = x i j + dHat i j + deltaX i j
  update_error_bound : ∀ (i : ℕ) (j : Fin n),
    |deltaX i j| ≤ u * |x (i + 1) j|
  denominator_condition : ∀ i : ℕ,
    c1 i * (p03MatInfNorm Ainv * p03MatInfNorm A) * uS < 1

/-- Exact residual of the stored iterate for the original system. -/
noncomputable def p03ExactResidual {n : ℕ}
    (run : P03NormwiseIRRun n) (i : ℕ) : Fin n → ℝ :=
  fun j => run.b j - p03MatVec run.A (run.x i) j

/-- Residual of the computed correction equation. -/
noncomputable def p03CorrectionDefect {n : ℕ}
    (run : P03NormwiseIRRun n) (i : ℕ) : Fin n → ℝ :=
  fun j => run.rHat i j - p03MatVec run.A (run.dHat i) j

/-- `κ_∞(A) = ‖A⁻¹‖_∞ ‖A‖_∞` for a certified P03 run. -/
noncomputable def p03KappaInf {n : ℕ} (run : P03NormwiseIRRun n) : ℝ :=
  p03MatInfNorm run.Ainv * p03MatInfNorm run.A

/-- The correction-solver quotient in P03 Theorem 4.1. -/
noncomputable def p03CorrectionRatio {n : ℕ}
    (run : P03NormwiseIRRun n) (i : ℕ) : ℝ :=
  (run.c1 i * p03KappaInf run + run.c2 i) /
    (1 - run.c1 i * p03KappaInf run * run.uS)

/-- The coefficient `α_i` in P03 Theorem 4.1. -/
noncomputable def p03Alpha {n : ℕ}
    (run : P03NormwiseIRRun n) (i : ℕ) : ℝ :=
  run.uS * (1 + (1 + run.uS) * p03CorrectionRatio run i)

/-- The additive term `β_i` in P03 Theorem 4.1. -/
noncomputable def p03Beta {n : ℕ}
    (run : P03NormwiseIRRun n) (i : ℕ) : ℝ :=
  (1 + run.uS * p03CorrectionRatio run i) * (1 + run.uS) *
      gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
        (p03VecInfNorm run.b +
          p03MatInfNorm run.A * p03VecInfNorm (run.x i)) +
    run.u * p03MatInfNorm run.A * p03VecInfNorm (run.x (i + 1))

/-- A proof-carrying execution of the unscaled Algorithm 1.1 refinement loop
for the componentwise analysis in P03 Theorem 5.1. In addition to the exact
models (3.3), (3.6), and (2.5), it records the iteration-dependent M-matrix
inverse `M₁` whose
existence, nonnegativity, and norm bound are derived from condition (5.6) in
the paragraph preceding the theorem. -/
structure P03ComponentwiseIRRun (n : ℕ) where
  dimension_pos : 0 < n
  A : Fin n → Fin n → ℝ
  Ainv : Fin n → Fin n → ℝ
  b : Fin n → ℝ
  x : ℕ → Fin n → ℝ
  rHat : ℕ → Fin n → ℝ
  dHat : ℕ → Fin n → ℝ
  deltaR : ℕ → Fin n → ℝ
  deltaX : ℕ → Fin n → ℝ
  G : ℕ → Fin n → Fin n → ℝ
  uR : ℝ
  u : ℝ
  uS : ℝ
  uF : ℝ
  uR_nonneg : 0 ≤ uR
  uR_le_u : uR ≤ u
  u_le_uS : u ≤ uS
  uS_le_uF : uS ≤ uF
  gamma_valid : GammaValid uR (p03MaxAugmentedRowNnz A b)
  G_nonneg : ∀ i j k, 0 ≤ G i j k
  left_inverse_action : ∀ (z : Fin n → ℝ) (j : Fin n),
    p03MatVec Ainv (p03MatVec A z) j = z j
  right_inverse_action : ∀ (z : Fin n → ℝ) (j : Fin n),
    p03MatVec A (p03MatVec Ainv z) j = z j
  residual_equation : ∀ (i : ℕ) (j : Fin n),
    rHat i j = b j - p03MatVec A (x i) j + deltaR i j
  residual_error_bound : ∀ (i : ℕ) (j : Fin n),
    |deltaR i j| ≤
      uS * |b j - p03MatVec A (x i) j| +
        (1 + uS) * gamma uR (p03MaxAugmentedRowNnz A b) *
          (|b j| + p03MatVec (p03MatAbs A) (p03VecAbs (x i)) j)
  correction_solver_bound : ∀ (i : ℕ) (j : Fin n),
    |rHat i j - p03MatVec A (dHat i) j| ≤
      uS * p03MatVec (G i) (p03VecAbs (dHat i)) j
  update_equation : ∀ (i : ℕ) (j : Fin n),
    x (i + 1) j = x i j + dHat i j + deltaX i j
  update_error_bound : ∀ (i : ℕ) (j : Fin n),
    |deltaX i j| ≤ u * |x (i + 1) j|
  M1 : ℕ → Fin n → Fin n → ℝ
  condition_5_6 : ∀ i : ℕ,
    uS * p03MatInfNorm (p03MatMul (G i) (p03MatAbs Ainv)) +
        (1 + uS) * gamma uR (p03MaxAugmentedRowNnz A b) *
          p03MatInfNorm (p03MatMul (p03MatAbs A) (p03MatAbs Ainv)) ≤
      (1 : ℝ) / 2
  M1_nonneg : ∀ i j k, 0 ≤ M1 i j k
  M1_resolvent_action : ∀ (i : ℕ) (z : Fin n → ℝ) (j : Fin n),
    p03MatVec (M1 i)
      (fun k => z k -
        p03MatVec
          (p03MatMul
            (fun row col =>
              uS * G i row col +
                (1 + uS) * gamma uR (p03MaxAugmentedRowNnz A b) * |A row col|)
            (p03MatAbs Ainv)) z k) j = z j
  M1_norm_bound : ∀ i : ℕ, p03MatInfNorm (M1 i) ≤ 2

/-- Exact original-system residual at a computed P03 componentwise iterate. -/
noncomputable def p03ComponentwiseExactResidual {n : ℕ}
    (run : P03ComponentwiseIRRun n) (i : ℕ) : Fin n → ℝ :=
  fun j => run.b j - p03MatVec run.A (run.x i) j

/-- The nonnegative data vector `|b| + |A||x̂ᵢ|` from P03 section 5. -/
noncomputable def p03ComponentwiseData {n : ℕ}
    (run : P03ComponentwiseIRRun n) (i : ℕ) : Fin n → ℝ :=
  fun j => |run.b j| +
    p03MatVec (p03MatAbs run.A) (p03VecAbs (run.x i)) j

/-- The iteration-dependent matrix `Z₁ = uₛGᵢ + (1+uₛ)γₚʳ|A|` in (5.3).
The paper's `Z₁` depends on `i` through `Gᵢ`; the Lean name exposes that
dependency through its iteration argument. -/
noncomputable def p03Z {n : ℕ}
    (run : P03ComponentwiseIRRun n) (i : ℕ) : Fin n → Fin n → ℝ :=
  fun j k =>
    run.uS * run.G i j k +
      (1 + run.uS) * gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
        |run.A j k|

/-- The nonnegative matrix `Pᵢ = Zᵢ|A⁻¹|` used in (5.4)--(5.6). -/
noncomputable def p03P {n : ℕ}
    (run : P03ComponentwiseIRRun n) (i : ℕ) : Fin n → Fin n → ℝ :=
  p03MatMul (p03Z run i) (p03MatAbs run.Ainv)

/-- The bracketed source vector in equation (5.4). -/
noncomputable def p03CorrectionSource {n : ℕ}
    (run : P03ComponentwiseIRRun n) (i : ℕ) : Fin n → ℝ :=
  fun j =>
    (1 + run.uS) * |p03ComponentwiseExactResidual run i j| +
      (1 + run.uS) * (1 + run.u) *
        gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
          p03ComponentwiseData run (i + 1) j

/-- The correction contribution `Zᵢ|d̂ᵢ|` in equations (5.2) and (5.4). -/
noncomputable def p03CorrectionMagnitude {n : ℕ}
    (run : P03ComponentwiseIRRun n) (i : ℕ) : Fin n → ℝ :=
  p03MatVec (p03Z run i) (p03VecAbs (run.dHat i))

/-- The exact matrix `Wᵢ = uₛI + (1+uₛ)MᵢZᵢ|A⁻¹|` in Theorem 5.1. -/
noncomputable def p03W {n : ℕ}
    (run : P03ComponentwiseIRRun n) (i : ℕ) : Fin n → Fin n → ℝ :=
  fun j k =>
    run.uS * (if j = k then 1 else 0) +
      (1 + run.uS) * p03MatMul (run.M1 i) (p03P run i) j k

/-- The exact additive vector `yᵢ` in Theorem 5.1. -/
noncomputable def p03Y {n : ℕ}
    (run : P03ComponentwiseIRRun n) (i : ℕ) : Fin n → ℝ :=
  fun j =>
    (1 + run.uS) * (1 + run.u) *
        gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
      (p03ComponentwiseData run (i + 1) j +
        p03MatVec (p03MatMul (run.M1 i) (p03P run i))
          (p03ComponentwiseData run (i + 1)) j) +
    run.u * p03MatVec (p03MatAbs run.A)
      (p03VecAbs (run.x (i + 1))) j

end HighamBench
