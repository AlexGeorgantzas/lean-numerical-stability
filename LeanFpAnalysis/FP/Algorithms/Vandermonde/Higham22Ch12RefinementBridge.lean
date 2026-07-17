/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QED
-/
import LeanFpAnalysis.FP.Algorithms.HighamChapter12
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

The single modeling hypothesis `hcontract` — that the Chapter 12 one-step residual
envelope is at most `q` times the previous residual — is precisely the reduction
that Higham states holds "for standard Vandermonde matrices" because "(12.9) holds
in view of (5.3) and (5.7)".  It is the honest replacement for the source's
asymptotic `q = O(u) < 1`. -/

namespace LeanFpAnalysis.FP.Ch22B

open scoped BigOperators Topology
open Filter

/-- **Bridge B4.** Convergence of the fixed-precision iterative-refinement
residual sequence for a Chapter 22 solve, with the per-step contraction supplied
by Chapter 12 Theorem 12.3.

`xseq k` is the `k`-th computed iterate, `dseq k` its correction, `rseq k` /
`rhatseq k` the exact / computed residuals, `f2seq k` the update-rounding error,
and `gseq/hseq/tseq k` the Chapter 12 residual/solver terms at step `k`.  The
hypotheses `hr, hy, hf1, hDeltaR, hf2` are the per-step Chapter 12 models of
Theorem 12.3.  `hcontract` records that the Theorem 12.3 residual envelope at
step `k` is at most `q` times the residual at step `k` (the reduction the source
attributes to Theorem 12.3 for Vandermonde systems).

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
