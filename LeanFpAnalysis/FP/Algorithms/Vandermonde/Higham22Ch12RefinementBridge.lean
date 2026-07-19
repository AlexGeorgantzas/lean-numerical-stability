/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QED
-/
import LeanFpAnalysis.FP.Algorithms.HighamChapter12
import LeanFpAnalysis.FP.Algorithms.Horner
import LeanFpAnalysis.FP.Algorithms.Vandermonde.Higham22

/-! # Bridge B4: Chapter 12 iterative refinement → Chapter 22 Vandermonde
refinement convergence.

Higham, 2nd ed., §22.3 (printed p. 428) justifies iterative refinement of a
Vandermonde solve "with the aid of Theorem 12.3": the one-step residual bound of
Theorem 12.3 (equation (12.14), formalized as
`higham12_3_exact_one_step_residual_bound`) is what makes the refinement residual
contract, and its geometric decay to zero is the abstract model
`higham22_refinement_converges` proves.

This module supplies a *genuine* dependency edge between the two.  The standalone
Chapter 22 lemma `higham22_refinement_converges` consumes an abstract contraction
factor `q < 1`; here we produce the per-step contraction of the *actual* iterative
refinement residual sequence by applying Chapter 12 Theorem 12.3 at every step,
then hand the resulting geometric majorant to the Chapter 22 convergence result.
Thus the Chapter 22 refinement convergence is *derived from* Chapter 12
Theorem 12.3, matching the source's "justified with the aid of Theorem 12.3".

The finite Horner residual bounds below are the actual bridge from (5.3)/(5.7)
to the residual-accuracy premise (12.9).  The separate modeling hypothesis
`hcontract` says that the *whole* Chapter 12 one-step envelope (including the
correction solve and update) is at most `q` times the previous residual.  This
is the finite replacement for the source's later asymptotic `q = O(u) < 1`;
it does not follow from residual formation alone. -/

namespace LeanFpAnalysis.FP.Ch22B

open scoped BigOperators Topology
open Filter

/-! ## The genuine (5.3)/(5.7) -> (12.9) residual-formation edge -/

/-- A standard Vandermonde residual component formed by evaluating the
coefficient vector with rounded Horner and then performing one rounded
subtraction from the right-hand side. -/
noncomputable def ch22bHornerResidual
    (fp : FPModel) (x b : ℝ) (coeffsDesc : List ℝ) : ℝ :=
  fp.fl_sub b (fl_hornerDesc fp x coeffsDesc)

/-- Finite residual-formation budget obtained from Higham (5.3), including
the final rounded subtraction.  This is the standard-Vandermonde instance of
the accuracy shape used in (12.9). -/
noncomputable def ch22bHornerResidualBudget
    (fp : FPModel) (x b : ℝ) (coeffsDesc : List ℝ) : ℝ :=
  let g := gamma fp (2 * (coeffsDesc.length - 1))
  let m := polyDescAbs x coeffsDesc
  g * m + fp.u * (|b| + (1 + g) * m)

/-- The claim on printed p. 428 that standard Vandermonde residual formation
satisfies (12.9), derived directly from the Chapter 5 producer (5.3) and the
standard model for the final subtraction. -/
theorem ch22b_horner_residual_error_via_higham5_3
    (fp : FPModel) (x b : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    |ch22bHornerResidual fp x b coeffsDesc -
        (b - polyDesc x coeffsDesc)| ≤
      ch22bHornerResidualBudget fp x b coeffsDesc := by
  let phat := fl_hornerDesc fp x coeffsDesc
  let p := polyDesc x coeffsDesc
  let m := polyDescAbs x coeffsDesc
  let g := gamma fp (2 * (coeffsDesc.length - 1))
  have hg : 0 ≤ g := by
    exact gamma_nonneg fp hvalid
  have hm : 0 ≤ m := by
    exact polyDescAbs_nonneg x coeffsDesc
  have heval : |phat - p| ≤ g * m := by
    simpa [phat, p, g, m] using
      fl_hornerDesc_forward_error_bound fp x coeffsDesc hvalid
  have hp : |p| ≤ m := by
    simpa [p, m] using abs_polyDesc_le_polyDescAbs x coeffsDesc
  have hphat : |phat| ≤ (1 + g) * m := by
    calc
      |phat| = |(phat - p) + p| := by ring_nf
      _ ≤ |phat - p| + |p| := abs_add_le _ _
      _ ≤ g * m + m := add_le_add heval hp
      _ = (1 + g) * m := by ring
  obtain ⟨δ, hδ, hsub⟩ := fp.model_sub b phat
  have hbp : |b - phat| ≤ |b| + (1 + g) * m := by
    exact (abs_sub b phat).trans (add_le_add (le_refl |b|) hphat)
  have hround : |δ| * |b - phat| ≤
      fp.u * (|b| + (1 + g) * m) := by
    exact mul_le_mul hδ hbp (abs_nonneg _) fp.u_nonneg
  change |fp.fl_sub b phat - (b - p)| ≤ _
  rw [hsub]
  have hid : (b - phat) * (1 + δ) - (b - p) =
      (p - phat) + δ * (b - phat) := by ring
  rw [hid]
  calc
    |(p - phat) + δ * (b - phat)| ≤
        |p - phat| + |δ * (b - phat)| := abs_add_le _ _
    _ = |p - phat| + |δ| * |b - phat| := by rw [abs_mul]
    _ ≤ g * m + fp.u * (|b| + (1 + g) * m) :=
      add_le_add (by simpa [abs_sub_comm] using heval) hround
    _ = ch22bHornerResidualBudget fp x b coeffsDesc := by
      simp [ch22bHornerResidualBudget, g, m]

/-- Confluent rows use the first-derivative Horner recurrence.  This is the
corresponding residual-accuracy contribution derived from Higham (5.7).  The
final subtraction can be added exactly as in
`ch22b_horner_residual_error_via_higham5_3`. -/
theorem ch22b_horner_derivative_error_via_higham5_7
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    |(fl_hornerDerivativeDesc fp x coeffsDesc).2 -
        polyDescDeriv x coeffsDesc| ≤
      gamma fp (2 * (coeffsDesc.length - 1)) *
        polyDescDerivAbs x coeffsDesc :=
  fl_hornerDerivativeDesc_snd_forward_error_bound_coupled
    fp x coeffsDesc hvalid

/-- Residual formation can be exact while a bad correction leaves a nonzero
residual unchanged.  Thus (5.3)/(5.7), which control residual formation, cannot
by themselves produce the geometric contraction hypothesis used below; a
correction-solve hypothesis is mathematically necessary. -/
theorem ch22b_residual_accuracy_alone_not_contraction :
    ¬ ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ |(1 : ℝ)| ≤ q * |(1 : ℝ)| := by
  rintro ⟨q, _hq0, hq1, hq⟩
  norm_num at hq
  linarith

/-- **Bridge B4.** Convergence of the fixed-precision iterative-refinement
residual sequence for a Chapter 22 solve, with the per-step contraction supplied
by Chapter 12 Theorem 12.3.

`xseq k` is the `k`-th computed iterate, `dseq k` its correction, `rseq k` /
`rhatseq k` the exact / computed residuals, `f2seq k` the update-rounding error,
and `gseq/hseq/tseq k` the Chapter 12 residual/solver terms at step `k`.  The
hypotheses `hr, hy, hf1, hDeltaR, hf2` are the per-step Chapter 12 models of
Theorem 12.3.  `hcontract` records the separate requirement that the complete
Theorem 12.3 residual envelope at step `k` is at most `q` times the residual at
step `k`.  The Horner theorems above produce residual-formation accuracy, but
not this correction-solve contraction.

The conclusion is that the tracked residual component tends to `0`.  The proof
applies `higham12_3_exact_one_step_residual_bound` at each step to obtain
`e (k+1) ≤ q · e k`, and closes via the Chapter 22 geometric-decay convergence
`higham22_refinement_converges`. -/
theorem ch22b_refinement_converges_via_ch12
    (n : ℕ) (i : Fin n)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (xseq dseq rseq rhatseq f2seq : ℕ → Fin n → ℝ)
    (gseq hseq tseq : ℕ → Fin n → ℝ)
    (u q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hr : ∀ k, ∀ i' : Fin n,
      rseq k i' = b i' - ∑ j : Fin n, A i' j * xseq k j)
    (hy : ∀ k, ∀ i' : Fin n,
      xseq (k + 1) i' = xseq k i' + dseq k i' + f2seq k i')
    (hf1 : ∀ k, ∀ i' : Fin n,
      |rhatseq k i' - ∑ j : Fin n, A i' j * dseq k j| ≤
        u * (gseq k i' + hseq k i'))
    (hDeltaR : ∀ k, ∀ i' : Fin n,
      |rhatseq k i' - rseq k i'| ≤ u * tseq k i')
    (hf2 : ∀ k, ∀ j : Fin n,
      |f2seq k j| ≤ u * (|xseq k j| + |dseq k j|))
    (hcontract : ∀ k,
      u * (gseq k i + hseq k i) + u * tseq k i +
          u * ∑ j : Fin n, |A i j| * (|xseq k j| + |dseq k j|) ≤
        q * |b i - ∑ j : Fin n, A i j * xseq k j|) :
    Tendsto (fun k => |b i - ∑ j : Fin n, A i j * xseq k j|) atTop (𝓝 0) := by
  set e : ℕ → ℝ := fun k => |b i - ∑ j : Fin n, A i j * xseq k j| with he
  -- Per-step contraction of the *actual* residual, produced by Theorem 12.3.
  have hstep : ∀ k, e (k + 1) ≤ q * e k := by
    intro k
    have hch12 := higham12_3_exact_one_step_residual_bound n A
      (xseq k) (dseq k) b (rseq k) (rhatseq k) (f2seq k) (xseq (k + 1))
      u (gseq k) (hseq k) (tseq k)
      (fun i' => hr k i') (fun i' => hy k i')
      (fun i' => hf1 k i') (fun i' => hDeltaR k i')
      (fun j => hf2 k j) i
    exact le_trans hch12 (hcontract k)
  -- The residual is dominated by the Chapter 22 geometric-decay majorant.
  have hmaj : ∀ k, e k ≤ higham22RefinementError q (e 0) k := by
    intro k
    induction k with
    | zero => simp [higham22RefinementError]
    | succ k ih =>
        calc
          e (k + 1) ≤ q * e k := hstep k
          _ ≤ q * higham22RefinementError q (e 0) k :=
                mul_le_mul_of_nonneg_left ih hq0
          _ = higham22RefinementError q (e 0) (k + 1) := by
                rw [higham22RefinementError]
  have hnn : ∀ k, 0 ≤ e k := fun _ => abs_nonneg _
  have hconv : Tendsto (higham22RefinementError q (e 0)) atTop (𝓝 0) :=
    higham22_refinement_converges q (e 0) hq0 hq1
  exact squeeze_zero hnn hmaj hconv

end LeanFpAnalysis.FP.Ch22B
