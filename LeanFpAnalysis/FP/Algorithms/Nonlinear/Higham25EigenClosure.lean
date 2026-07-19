/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QED
-/
import LeanFpAnalysis.FP.Algorithms.Nonlinear.Higham25
import LeanFpAnalysis.FP.Algorithms.DotProduct

namespace LeanFpAnalysis.FP

open scoped BigOperators

/-! # Higham Chapter 25: eigenproblem specialization closure

This module supplies the concrete bridges following equation (25.10): the
displayed bordered Jacobian and its exact Taylor identity, a source-domain
simple-eigenpair certificate implying bordered-Jacobian nonsingularity, and a
literal rounded residual evaluator satisfying the printed `ψ` budget in the
infinity norm. It also records a formal counterexample to the source's
unqualified coefficient `2 ‖A‖`, which is zero for `A=0` even though the
Jacobian varies with `λ`.
-/

section EigenRoundedResidual

variable {n : ℕ}

noncomputable def higham25EigenResidualDotLeft
    (A : Fin n → Fin n → ℝ) (lambda : ℝ) (i : Fin n) : Fin (n + 1) → ℝ :=
  Fin.lastCases (-lambda) (fun j => A i j)

noncomputable def higham25EigenResidualDotRight
    (x : Fin n → ℝ) (i : Fin n) : Fin (n + 1) → ℝ :=
  Fin.lastCases (x i) x

noncomputable def higham25EigenRoundedResidual
    (fp : FPModel) (A : Fin n → Fin n → ℝ) (s : Fin n)
    (x : Fin n → ℝ) (lambda : ℝ) : (Fin n → ℝ) × ℝ :=
  (fun i => fl_dotProduct fp (n + 1)
      (higham25EigenResidualDotLeft A lambda i)
      (higham25EigenResidualDotRight x i),
    fp.fl_sub (x s) 1)

theorem higham25EigenResidualDot_exact
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (lambda : ℝ) (i : Fin n) :
    (∑ k : Fin (n + 1),
      higham25EigenResidualDotLeft A lambda i k *
        higham25EigenResidualDotRight x i k) =
      (∑ j : Fin n, A i j * x j) - lambda * x i := by
  rw [Fin.sum_univ_castSucc]
  simp [higham25EigenResidualDotLeft, higham25EigenResidualDotRight]
  ring

theorem higham25EigenResidualDot_abs_sum
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (lambda : ℝ) (i : Fin n) :
    (∑ k : Fin (n + 1),
      |higham25EigenResidualDotLeft A lambda i k| *
        |higham25EigenResidualDotRight x i k|) =
      (∑ j : Fin n, |A i j| * |x j|) + |lambda| * |x i| := by
  rw [Fin.sum_univ_castSucc]
  simp [higham25EigenResidualDotLeft, higham25EigenResidualDotRight]

theorem higham25EigenResidualDot_abs_sum_le
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (lambda : ℝ) (i : Fin n) :
    (∑ k : Fin (n + 1),
      |higham25EigenResidualDotLeft A lambda i k| *
        |higham25EigenResidualDotRight x i k|) ≤
      (infNorm A + |lambda|) * infNormVec x := by
  rw [higham25EigenResidualDot_abs_sum]
  have hx : 0 ≤ infNormVec x := infNormVec_nonneg x
  have hrow : ∑ j : Fin n, |A i j| ≤ infNorm A := row_sum_le_infNorm A i
  have hsum : (∑ j : Fin n, |A i j| * |x j|) ≤
      (∑ j : Fin n, |A i j|) * infNormVec x := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (abs_le_infNormVec x j) (abs_nonneg _)
  have hsum' : (∑ j : Fin n, |A i j| * |x j|) ≤
      infNorm A * infNormVec x :=
    hsum.trans (mul_le_mul_of_nonneg_right hrow hx)
  have hlast : |lambda| * |x i| ≤ |lambda| * infNormVec x :=
    mul_le_mul_of_nonneg_left (abs_le_infNormVec x i) (abs_nonneg _)
  calc
    (∑ j : Fin n, |A i j| * |x j|) + |lambda| * |x i| ≤
        infNorm A * infNormVec x + |lambda| * infNormVec x :=
      add_le_add hsum' hlast
    _ = (infNorm A + |lambda|) * infNormVec x := by ring

theorem higham25EigenRoundedResidual_first_error
    (fp : FPModel) (A : Fin n → Fin n → ℝ) (s : Fin n)
    (x : Fin n → ℝ) (lambda : ℝ)
    (hgamma : gammaValid fp (n + 1)) (i : Fin n) :
    |(higham25EigenRoundedResidual fp A s x lambda).1 i -
        (higham25EigenResidual A s x lambda).1 i| ≤
      gamma fp (n + 1) *
        (infNorm A + |lambda|) * infNormVec x := by
  have hdot := dotProduct_error_bound fp (n + 1)
    (higham25EigenResidualDotLeft A lambda i)
    (higham25EigenResidualDotRight x i) hgamma
  rw [higham25EigenResidualDot_exact] at hdot
  have hsum := higham25EigenResidualDot_abs_sum_le A x lambda i
  have hgamma0 : 0 ≤ gamma fp (n + 1) := gamma_nonneg fp hgamma
  calc
    |(higham25EigenRoundedResidual fp A s x lambda).1 i -
        (higham25EigenResidual A s x lambda).1 i| =
      |fl_dotProduct fp (n + 1)
          (higham25EigenResidualDotLeft A lambda i)
          (higham25EigenResidualDotRight x i) -
        ((∑ j : Fin n, A i j * x j) - lambda * x i)| := by
          rfl
    _ ≤ gamma fp (n + 1) *
        (∑ k : Fin (n + 1),
          |higham25EigenResidualDotLeft A lambda i k| *
            |higham25EigenResidualDotRight x i k|) := hdot
    _ ≤ gamma fp (n + 1) *
        ((infNorm A + |lambda|) * infNormVec x) :=
      mul_le_mul_of_nonneg_left hsum hgamma0
    _ = gamma fp (n + 1) *
        (infNorm A + |lambda|) * infNormVec x := by ring

theorem higham25EigenRoundedResidual_last_error
    (fp : FPModel) (A : Fin n → Fin n → ℝ) (s : Fin n)
    (x : Fin n → ℝ) (lambda : ℝ) :
    |(higham25EigenRoundedResidual fp A s x lambda).2 -
        (higham25EigenResidual A s x lambda).2| ≤
      fp.u * |(higham25EigenResidual A s x lambda).2| := by
  obtain ⟨delta, hdelta, hfl⟩ := fp.model_sub (x s) 1
  rw [show (higham25EigenRoundedResidual fp A s x lambda).2 =
      fp.fl_sub (x s) 1 by rfl,
    show (higham25EigenResidual A s x lambda).2 = x s - 1 by rfl,
    hfl]
  calc
    |(x s - 1) * (1 + delta) - (x s - 1)| =
        |x s - 1| * |delta| := by rw [show (x s - 1) * (1 + delta) -
          (x s - 1) = (x s - 1) * delta by ring, abs_mul]
    _ ≤ |x s - 1| * fp.u :=
      mul_le_mul_of_nonneg_left hdelta (abs_nonneg _)
    _ = fp.u * |x s - 1| := by ring

noncomputable def higham25EigenResidualInfNorm
    (r : (Fin n → ℝ) × ℝ) : ℝ :=
  max (infNormVec r.1) |r.2|

theorem higham25EigenResidualInfNorm_nonneg
    (r : (Fin n → ℝ) × ℝ) :
    0 ≤ higham25EigenResidualInfNorm r := by
  exact le_max_of_le_left (infNormVec_nonneg r.1)

theorem higham25EigenRoundedResidual_error_bound
    (fp : FPModel) (A : Fin n → Fin n → ℝ) (s : Fin n)
    (x : Fin n → ℝ) (lambda : ℝ)
    (hgamma : gammaValid fp (n + 1)) :
    higham25EigenResidualInfNorm
        ((higham25EigenRoundedResidual fp A s x lambda).1 -
            (higham25EigenResidual A s x lambda).1,
          (higham25EigenRoundedResidual fp A s x lambda).2 -
            (higham25EigenResidual A s x lambda).2) ≤
      fp.u * higham25EigenResidualInfNorm
          (higham25EigenResidual A s x lambda) +
        gamma fp (n + 1) *
          (infNorm A + |lambda|) * infNormVec x := by
  let psi := gamma fp (n + 1) * (infNorm A + |lambda|) * infNormVec x
  let Fnorm := higham25EigenResidualInfNorm (higham25EigenResidual A s x lambda)
  have hpsi : 0 ≤ psi := by
    dsimp [psi]
    exact mul_nonneg
      (mul_nonneg (gamma_nonneg fp hgamma)
        (add_nonneg (infNorm_nonneg A) (abs_nonneg lambda)))
      (infNormVec_nonneg x)
  have hF : 0 ≤ Fnorm := by
    exact higham25EigenResidualInfNorm_nonneg _
  have hu : 0 ≤ fp.u := fp.u_nonneg
  have hfirstPoint : ∀ i : Fin n,
      |((higham25EigenRoundedResidual fp A s x lambda).1 -
          (higham25EigenResidual A s x lambda).1) i| ≤ psi := by
    intro i
    simpa [Pi.sub_apply, psi] using
      higham25EigenRoundedResidual_first_error fp A s x lambda hgamma i
  have hfirst : infNormVec
      ((higham25EigenRoundedResidual fp A s x lambda).1 -
        (higham25EigenResidual A s x lambda).1) ≤ psi :=
    infNormVec_le_of_abs_le _ hfirstPoint hpsi
  have hlastRaw := higham25EigenRoundedResidual_last_error fp A s x lambda
  have hlastF : |(higham25EigenResidual A s x lambda).2| ≤ Fnorm := by
    exact le_max_right _ _
  have hlast :
      |(higham25EigenRoundedResidual fp A s x lambda).2 -
        (higham25EigenResidual A s x lambda).2| ≤ fp.u * Fnorm :=
    hlastRaw.trans (mul_le_mul_of_nonneg_left hlastF hu)
  unfold higham25EigenResidualInfNorm
  apply max_le
  · exact hfirst.trans (le_add_of_nonneg_left (mul_nonneg hu hF))
  · exact hlast.trans (le_add_of_nonneg_right hpsi)

end EigenRoundedResidual

section EigenJacobian

variable {n : ℕ}

/-- The bordered Jacobian displayed immediately after equation (25.10). -/
noncomputable def higham25EigenJacobian
    (A : Fin n → Fin n → ℝ) (s : Fin n)
    (x : Fin n → ℝ) (lambda : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun r c =>
    Fin.lastCases
      (Fin.lastCases 0 (fun j => if j = s then 1 else 0) c)
      (fun i => Fin.lastCases (-x i)
        (fun j => A i j - if i = j then lambda else 0) c)
      r

@[simp]
theorem higham25EigenJacobian_castSucc_castSucc
    (A : Fin n → Fin n → ℝ) (s : Fin n)
    (x : Fin n → ℝ) (lambda : ℝ) (i j : Fin n) :
    higham25EigenJacobian A s x lambda i.castSucc j.castSucc =
      A i j - if i = j then lambda else 0 := by
  simp [higham25EigenJacobian]

@[simp]
theorem higham25EigenJacobian_castSucc_last
    (A : Fin n → Fin n → ℝ) (s : Fin n)
    (x : Fin n → ℝ) (lambda : ℝ) (i : Fin n) :
    higham25EigenJacobian A s x lambda i.castSucc (Fin.last n) = -x i := by
  simp [higham25EigenJacobian]

@[simp]
theorem higham25EigenJacobian_last_castSucc
    (A : Fin n → Fin n → ℝ) (s : Fin n)
    (x : Fin n → ℝ) (lambda : ℝ) (j : Fin n) :
    higham25EigenJacobian A s x lambda (Fin.last n) j.castSucc =
      if j = s then 1 else 0 := by
  simp [higham25EigenJacobian]

@[simp]
theorem higham25EigenJacobian_last_last
    (A : Fin n → Fin n → ℝ) (s : Fin n)
    (x : Fin n → ℝ) (lambda : ℝ) :
    higham25EigenJacobian A s x lambda (Fin.last n) (Fin.last n) = 0 := by
  simp [higham25EigenJacobian]

/-- Source-shaped action of the bordered Jacobian on `(dx,dλ)`. -/
noncomputable def higham25EigenJacobianAction
    (A : Fin n → Fin n → ℝ) (s : Fin n)
    (x : Fin n → ℝ) (lambda : ℝ)
    (dv : (Fin n → ℝ) × ℝ) : (Fin n → ℝ) × ℝ :=
  (fun i => (∑ j : Fin n, A i j * dv.1 j) -
      lambda * dv.1 i - dv.2 * x i,
    dv.1 s)

theorem higham25EigenJacobian_mulVec_eq_action
    (A : Fin n → Fin n → ℝ) (s : Fin n)
    (x dx : Fin n → ℝ) (lambda dlambda : ℝ) :
    Matrix.mulVec (higham25EigenJacobian A s x lambda)
        (Fin.lastCases dlambda dx) =
      Fin.lastCases
        (higham25EigenJacobianAction A s x lambda (dx, dlambda)).2
        (higham25EigenJacobianAction A s x lambda (dx, dlambda)).1 := by
  funext r
  refine Fin.lastCases ?_ (fun i => ?_) r
  · change (∑ j : Fin (n + 1),
        higham25EigenJacobian A s x lambda (Fin.last n) j *
          Fin.lastCases dlambda dx j) = _
    rw [Fin.sum_univ_castSucc]
    simp [higham25EigenJacobianAction]
  · change (∑ j : Fin (n + 1),
        higham25EigenJacobian A s x lambda i.castSucc j *
          Fin.lastCases dlambda dx j) = _
    rw [Fin.sum_univ_castSucc]
    simp [higham25EigenJacobianAction]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    simp
    ring

/-- Exact Taylor identity: the only remainder is the bilinear term
`-dλ dx`.  This proves that the displayed bordered matrix is the derivative
of (25.10), without postulating a derivative formula. -/
theorem higham25EigenResidual_taylor_exact_first
    (A : Fin n → Fin n → ℝ) (s : Fin n)
    (x dx : Fin n → ℝ) (lambda dlambda : ℝ) (i : Fin n) :
    (higham25EigenResidual A s (fun j => x j + dx j)
        (lambda + dlambda)).1 i =
      (higham25EigenResidual A s x lambda).1 i +
        (higham25EigenJacobianAction A s x lambda (dx, dlambda)).1 i -
          dlambda * dx i := by
  simp only [higham25EigenResidual, higham25EigenJacobianAction]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  ring

theorem higham25EigenResidual_taylor_exact_last
    (A : Fin n → Fin n → ℝ) (s : Fin n)
    (x dx : Fin n → ℝ) (lambda dlambda : ℝ) :
    (higham25EigenResidual A s (fun j => x j + dx j)
        (lambda + dlambda)).2 =
      (higham25EigenResidual A s x lambda).2 +
        (higham25EigenJacobianAction A s x lambda (dx, dlambda)).2 := by
  simp [higham25EigenResidual, higham25EigenJacobianAction]
  ring

/-- An explicit algebraic certificate for a simple normalized real eigenpair.
The left eigenvector excludes generalized eigenvectors, while
`eigenspace_oneDimensional` records that the eigenspace is spanned by `x`.
These are standard source-domain facts, not a bordered-Jacobian conclusion. -/
structure Higham25SimpleEigenpairCertificate
    (A : Fin n → Fin n → ℝ) (s : Fin n)
    (x : Fin n → ℝ) (lambda : ℝ) where
  left : Fin n → ℝ
  normalized : x s = 1
  rightEigen : ∀ i, ∑ j : Fin n, A i j * x j = lambda * x i
  leftEigen : ∀ j, ∑ i : Fin n, left i * A i j = lambda * left j
  leftRight_nonzero : (∑ i : Fin n, left i * x i) ≠ 0
  eigenspace_oneDimensional :
    ∀ z : Fin n → ℝ,
      (∀ i, ∑ j : Fin n, A i j * z j = lambda * z i) →
        ∃ c : ℝ, z = c • x

theorem Higham25SimpleEigenpairCertificate.left_annihilates
    {A : Fin n → Fin n → ℝ} {s : Fin n}
    {x : Fin n → ℝ} {lambda : ℝ}
    (h : Higham25SimpleEigenpairCertificate A s x lambda)
    (z : Fin n → ℝ) :
    (∑ i : Fin n, h.left i *
      ((∑ j : Fin n, A i j * z j) - lambda * z i)) = 0 := by
  calc
    (∑ i : Fin n, h.left i *
      ((∑ j : Fin n, A i j * z j) - lambda * z i)) =
        ∑ i : Fin n,
          ((∑ j : Fin n, (h.left i * A i j) * z j) -
            lambda * (h.left i * z i)) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [mul_sub]
              rw [Finset.mul_sum]
              ring
    _ = (∑ i : Fin n, ∑ j : Fin n,
          (h.left i * A i j) * z j) -
        ∑ i : Fin n, lambda * (h.left i * z i) := by
          rw [Finset.sum_sub_distrib]
    _ = (∑ j : Fin n, (∑ i : Fin n, h.left i * A i j) * z j) -
          lambda * (∑ i : Fin n, h.left i * z i) := by
            rw [Finset.sum_comm, Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.sum_mul]
    _ = (∑ j : Fin n, (lambda * h.left j) * z j) -
          lambda * (∑ i : Fin n, h.left i * z i) := by
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            rw [h.leftEigen j]
    _ = 0 := by rw [Finset.mul_sum]; ring

/-- A simple eigenvalue makes the bordered Jacobian nonsingular at the
normalized solution, as asserted after (25.10). -/
theorem higham25EigenJacobian_kernel_eq_zero_of_simple
    (A : Fin n → Fin n → ℝ) (s : Fin n)
    (x : Fin n → ℝ) (lambda : ℝ)
    (h : Higham25SimpleEigenpairCertificate A s x lambda)
    (dv : (Fin n → ℝ) × ℝ)
    (hkernel : higham25EigenJacobianAction A s x lambda dv = (0, 0)) :
    dv = (0, 0) := by
  have hfirstFun := congrArg Prod.fst hkernel
  have hlast := congrArg Prod.snd hkernel
  have hfirst : ∀ i : Fin n,
      (∑ j : Fin n, A i j * dv.1 j) - lambda * dv.1 i = dv.2 * x i := by
    intro i
    have hi := congrFun hfirstFun i
    simp only [higham25EigenJacobianAction, Pi.zero_apply] at hi
    linarith
  have hweighted : dv.2 * (∑ i : Fin n, h.left i * x i) = 0 := by
    have hann := h.left_annihilates dv.1
    have hsubst :
        (∑ i : Fin n, h.left i *
          ((∑ j : Fin n, A i j * dv.1 j) - lambda * dv.1 i)) =
          dv.2 * (∑ i : Fin n, h.left i * x i) := by
      calc
        (∑ i : Fin n, h.left i *
          ((∑ j : Fin n, A i j * dv.1 j) - lambda * dv.1 i)) =
            ∑ i : Fin n, h.left i * (dv.2 * x i) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hfirst i]
        _ = dv.2 * (∑ i : Fin n, h.left i * x i) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
    linarith
  have hdlambda : dv.2 = 0 :=
    (mul_eq_zero.mp hweighted).resolve_right h.leftRight_nonzero
  have hdxeigen : ∀ i : Fin n,
      ∑ j : Fin n, A i j * dv.1 j = lambda * dv.1 i := by
    intro i
    have := hfirst i
    rw [hdlambda, zero_mul] at this
    exact sub_eq_zero.mp this
  obtain ⟨c, hc⟩ := h.eigenspace_oneDimensional dv.1 hdxeigen
  have hdxs : dv.1 s = 0 := by
    simpa [higham25EigenJacobianAction] using hlast
  have hc0 : c = 0 := by
    have := congrFun hc s
    simp only [Pi.smul_apply, smul_eq_mul, h.normalized, mul_one] at this
    linarith
  apply Prod.ext
  · rw [hc, hc0]
    simp
  · simp [hdlambda]

/-- Literal infinity-norm reading of the printed claim that the bordered
Jacobian has Lipschitz constant `2 ‖A‖`. -/
def Higham25EigenJacobianSourceLipschitz
    (A : Fin n → Fin n → ℝ) : Prop :=
  ∀ (s : Fin n) (x y : Fin n → ℝ) (lambda mu : ℝ),
    infNorm (fun i j =>
      higham25EigenJacobian A s x lambda i j -
        higham25EigenJacobian A s y mu i j) ≤
      (2 * infNorm A) *
        max (infNormVec (x - y)) |lambda - mu|

/-- Correct universal infinity-norm Lipschitz bound for the bordered
Jacobian.  The coefficient is `2`, independent of `A`: changing the state
changes only the `-λI` block and the `-x` column. -/
theorem higham25EigenJacobian_lipschitz_two_inf
    (A : Fin n → Fin n → ℝ) (s : Fin n)
    (x y : Fin n → ℝ) (lambda mu : ℝ) :
    infNorm (fun i j =>
      higham25EigenJacobian A s x lambda i j -
        higham25EigenJacobian A s y mu i j) ≤
      2 * max (infNormVec (x - y)) |lambda - mu| := by
  let E : Fin (n + 1) → Fin (n + 1) → ℝ := fun i j =>
    higham25EigenJacobian A s x lambda i j -
      higham25EigenJacobian A s y mu i j
  let M := max (infNormVec (x - y)) |lambda - mu|
  apply infNorm_le_of_row_sum_le
  · intro r
    refine Fin.lastCases ?_ (fun i => ?_) r
    · rw [Fin.sum_univ_castSucc]
      simp
    · rw [Fin.sum_univ_castSucc]
      have hsquare :
          (∑ j : Fin n, |E i.castSucc j.castSucc|) = |lambda - mu| := by
        rw [Finset.sum_eq_single i]
        · simp [E, abs_sub_comm]
        · intro j hj hji
          have hij : i ≠ j := Ne.symm hji
          simp [E, hij]
        · simp
      rw [hsquare]
      simp only [higham25EigenJacobian_castSucc_last, sub_neg_eq_add]
      have hxcomponent : |x i - y i| ≤ infNormVec (x - y) := by
        simpa [Pi.sub_apply] using abs_le_infNormVec (x - y) i
      have hxM : |x i - y i| ≤ M :=
        hxcomponent.trans (le_max_left _ _)
      have hlambdaM : |lambda - mu| ≤ M := le_max_right _ _
      rw [show -x i + y i = -(x i - y i) by ring, abs_neg]
      linarith
  · dsimp [M]
    positivity

/-- The source coefficient `2 ‖A‖` is false without a scaling assumption on
`A`: for the zero `1×1` matrix it is zero, although changing `λ` changes the
Jacobian.  This formal counterexample prevents the false coefficient from
being hidden behind an assumption. -/
theorem higham25EigenJacobian_source_lipschitz_counterexample :
    ¬ Higham25EigenJacobianSourceLipschitz
      (fun _ : Fin 1 => fun _ : Fin 1 => (0 : ℝ)) := by
  let A : Fin 1 → Fin 1 → ℝ := fun _ _ => 0
  let s : Fin 1 := 0
  let x : Fin 1 → ℝ := fun _ => 0
  let Jdiff : Fin 2 → Fin 2 → ℝ := fun i j =>
    higham25EigenJacobian A s x 0 i j -
      higham25EigenJacobian A s x 1 i j
  have hA : infNorm A = 0 := by
    apply le_antisymm
    · apply infNorm_le_of_row_sum_le
      · intro i
        simp [A]
      · norm_num
    · exact infNorm_nonneg A
  have h00 :
      Jdiff (Fin.castSucc (0 : Fin 1)) (Fin.castSucc (0 : Fin 1)) = 1 := by
    simp only [Jdiff]
    rw [higham25EigenJacobian_castSucc_castSucc,
      higham25EigenJacobian_castSucc_castSucc]
    norm_num [A]
  have h01 :
      Jdiff (Fin.castSucc (0 : Fin 1)) (Fin.last 1) = 0 := by
    simp only [Jdiff]
    rw [higham25EigenJacobian_castSucc_last,
      higham25EigenJacobian_castSucc_last]
    norm_num [x]
  have hrowEq : (∑ j : Fin 2, |Jdiff 0 j|) = 1 := by
    rw [Fin.sum_univ_two]
    change
      |Jdiff (Fin.castSucc (0 : Fin 1)) (Fin.castSucc (0 : Fin 1))| +
        |Jdiff (Fin.castSucc (0 : Fin 1)) (Fin.last 1)| = 1
    rw [h00, h01]
    norm_num
  intro hsource
  have hupper := hsource s x x 0 1
  change infNorm Jdiff ≤ _ at hupper
  rw [hA] at hupper
  simp at hupper
  have hrow := row_sum_le_infNorm Jdiff (0 : Fin 2)
  rw [hrowEq] at hrow
  linarith

end EigenJacobian

end LeanFpAnalysis.FP
