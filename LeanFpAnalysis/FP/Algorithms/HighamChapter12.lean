-- Algorithms/HighamChapter12.lean
--
-- Source-facing entry points for Higham Chapter 12, "Iterative Refinement".
-- The reusable one-step refinement proofs live in `IterativeRefinement`; this
-- file gives stable Chapter 12 labels and closes the exact local problem lemma
-- used in the chapter's Appendix A solution.

import Mathlib.Tactic
import LeanFpAnalysis.FP.Algorithms.HighamChapter11
import LeanFpAnalysis.FP.Algorithms.IterativeRefinement

namespace LeanFpAnalysis.FP

open scoped BigOperators

/-! ## §12.1 Behaviour of the Forward Error -/

/-- **Equation (12.1)** source model for one approximate linear solve:
`(A + DeltaA) y = c` and `|DeltaA| <= u W` componentwise. -/
def higham12_1_SolverWBound (n : ℕ)
    (A W : Fin n → Fin n → ℝ) (u : ℝ)
    (c y : Fin n → ℝ) : Prop :=
  ∃ DeltaA : Fin n → Fin n → ℝ,
    (∀ i j : Fin n, |DeltaA i j| ≤ u * W i j) ∧
    (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * y j = c i)

/-- **Equation (12.2)** residual perturbation bound after rewriting
`x_i = x + (x_i - x)`.  This is the exact algebraic component of the
displayed bound; the residual computation model supplies `hDelta`. -/
theorem higham12_2_residual_delta_bound (n : ℕ)
    (A : Fin n → Fin n → ℝ) (x x_i b DeltaR : Fin n → ℝ)
    (u gammaBar : ℝ)
    (hu : 0 ≤ u) (hc : 0 ≤ (1 + u) * gammaBar)
    (hAx : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hDelta : ∀ i : Fin n,
      |DeltaR i| ≤
        u * |b i - ∑ j : Fin n, A i j * x_i j| +
          (1 + u) * gammaBar *
            (|b i| + ∑ j : Fin n, |A i j| * |x_i j|)) :
    ∀ i : Fin n,
      |DeltaR i| ≤
        (u + (1 + u) * gammaBar) *
            ∑ j : Fin n, |A i j| * |x j - x_i j| +
          2 * (1 + u) * gammaBar *
            ∑ j : Fin n, |A i j| * |x j| := by
  intro i
  set E := ∑ j : Fin n, |A i j| * |x j - x_i j|
  set X := ∑ j : Fin n, |A i j| * |x j|
  have hresid : |b i - ∑ j : Fin n, A i j * x_i j| ≤ E := by
    have hrewrite :
        b i - ∑ j : Fin n, A i j * x_i j =
          ∑ j : Fin n, A i j * (x j - x_i j) := by
      rw [← hAx i, ← Finset.sum_sub_distrib]
      congr 1
      ext j
      ring
    rw [hrewrite]
    calc
      |∑ j : Fin n, A i j * (x j - x_i j)|
          ≤ ∑ j : Fin n, |A i j * (x j - x_i j)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = E := by
            simp [E, abs_mul]
  have hb : |b i| ≤ X := by
    rw [← hAx i]
    calc
      |∑ j : Fin n, A i j * x j|
          ≤ ∑ j : Fin n, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
      _ = X := by
            simp [X, abs_mul]
  have hxi : ∑ j : Fin n, |A i j| * |x_i j| ≤ E + X := by
    have hterm : ∀ j : Fin n, |x_i j| ≤ |x j - x_i j| + |x j| := by
      intro j
      have hx : x_i j = (x_i j - x j) + x j := by ring
      rw [hx]
      have htri := abs_add_three_le (x_i j - x j) (x j) 0
      simpa [abs_sub_comm] using htri
    calc
      ∑ j : Fin n, |A i j| * |x_i j|
          ≤ ∑ j : Fin n, |A i j| * (|x j - x_i j| + |x j|) :=
            Finset.sum_le_sum (fun j _ =>
              mul_le_mul_of_nonneg_left (hterm j) (abs_nonneg _))
      _ = E + X := by
            simp [E, X, mul_add, Finset.sum_add_distrib]
  have hsource := hDelta i
  calc
    |DeltaR i|
        ≤ u * |b i - ∑ j : Fin n, A i j * x_i j| +
            (1 + u) * gammaBar *
              (|b i| + ∑ j : Fin n, |A i j| * |x_i j|) := hsource
    _ ≤ u * E + (1 + u) * gammaBar * (X + (E + X)) := by
          have hleft := mul_le_mul_of_nonneg_left hresid hu
          have hright_arg : |b i| + ∑ j : Fin n, |A i j| * |x_i j| ≤ X + (E + X) := by
            linarith
          have hright := mul_le_mul_of_nonneg_left hright_arg hc
          linarith
    _ = (u + (1 + u) * gammaBar) * E + 2 * (1 + u) * gammaBar * X := by
          ring

/-- **Equations (12.3)-(12.5)** source-facing exact contraction skeleton:
if the componentwise error sizes satisfy a one-step affine recurrence, then the
scalar infinity-norm error obeys the same recurrence.  The book's printed
Theorems 12.1 and 12.2 use qualitative approximations on top of this skeleton. -/
theorem higham12_forward_error_linear_contraction (a : ℕ → ℝ) (eta tau : ℝ)
    (heta_nonneg : 0 ≤ eta) (heta_lt : eta < 1) (htau_nonneg : 0 ≤ tau)
    (hstep : ∀ k, a (k + 1) ≤ eta * a k + tau) :
    ∀ k, a k ≤ eta ^ k * a 0 + tau / (1 - eta) :=
  linear_contraction a eta tau heta_nonneg heta_lt htau_nonneg hstep

/-- Uniform steady-state consequence of the Chapter 12 contraction skeleton. -/
theorem higham12_forward_error_steady_state (a : ℕ → ℝ) (eta tau : ℝ)
    (heta_nonneg : 0 ≤ eta) (heta_lt : eta < 1) (htau_nonneg : 0 ≤ tau)
    (hstep : ∀ k, a (k + 1) ≤ eta * a k + tau)
    (ha0 : 0 ≤ a 0) :
    ∀ k, a k ≤ a 0 + tau / (1 - eta) :=
  linear_contraction_steady_state a eta tau
    heta_nonneg heta_lt htau_nonneg hstep ha0

/-! ## §12.2 Iterative Refinement Implies Stability -/

/-- **Equation (12.7)** source model for the initial computed solution:
`|b - A x_hat| <= u (g |x_hat| + h)` componentwise. -/
def higham12_7_initialResidualBound (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b x_hat : Fin n → ℝ)
    (u : ℝ) (g : Fin n → Fin n → ℝ) (h : Fin n → ℝ) : Prop :=
  ∀ i : Fin n,
    |b i - ∑ j : Fin n, A i j * x_hat j| ≤
      u * (∑ j : Fin n, g i j * |x_hat j| + h i)

/-- **Equation (12.8)** source model for computed residual accuracy. -/
def higham12_8_residualComputationBound (n : ℕ)
    (r r_hat t : Fin n → ℝ) (u : ℝ) : Prop :=
  ∀ i : Fin n, |r_hat i - r i| ≤ u * t i

/-- **Equation (12.9)** conventional residual computation bound, reusing the
repository's floating-point residual theorem. -/
theorem higham12_9_conventional_residual_error (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (x_hat b : Fin n → ℝ)
    (hn : gammaValid fp n) (hn1 : gammaValid fp (n + 1)) :
    ∀ i : Fin n,
      |fl_residual fp n A x_hat b i -
          (b i - ∑ j : Fin n, A i j * x_hat j)| ≤
        gamma fp (n + 1) *
          (|b i| + ∑ j : Fin n, |A i j| * |x_hat j|) :=
  conventional_residual_error fp n A x_hat b hn hn1

/-- **Theorem 12.3 / equation (12.14)** exact one-step residual bound before
the book's asymptotic `q = O(u)` interpretation. -/
theorem higham12_3_exact_one_step_residual_bound (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (x_hat d_hat : Fin n → ℝ) (b r r_hat : Fin n → ℝ)
    (f2 : Fin n → ℝ) (y : Fin n → ℝ)
    (u : ℝ) (gTerm hTerm tTerm : Fin n → ℝ)
    (hr : ∀ i : Fin n, r i = b i - ∑ j : Fin n, A i j * x_hat j)
    (hy : ∀ i : Fin n, y i = x_hat i + d_hat i + f2 i)
    (hf1 : ∀ i : Fin n,
      |r_hat i - ∑ j : Fin n, A i j * d_hat j| ≤
        u * (gTerm i + hTerm i))
    (hDeltaR : ∀ i : Fin n, |r_hat i - r i| ≤ u * tTerm i)
    (hf2 : ∀ j : Fin n, |f2 j| ≤ u * (|x_hat j| + |d_hat j|)) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * y j| ≤
        u * (gTerm i + hTerm i) + u * tTerm i +
          u * ∑ j : Fin n, |A i j| * (|x_hat j| + |d_hat j|) := by
  intro i
  have hbase := thm_11_3_specialized n A x_hat d_hat b r r_hat f2 y hr hy
    (fun i => u * (gTerm i + hTerm i)) hf1
    (fun i => u * tTerm i) hDeltaR
    (fun j => u * (|x_hat j| + |d_hat j|)) hf2 i
  have hpull :
      ∑ j : Fin n, |A i j| * (u * (|x_hat j| + |d_hat j|)) =
        u * ∑ j : Fin n, |A i j| * (|x_hat j| + |d_hat j|) := by
    rw [Finset.mul_sum]
    congr 1
    ext j
    ring
  linarith

/-- **Equation (12.14)** identity form:
`b - A y = (r_hat - A d_hat) - (r_hat - r) - A f2`. -/
theorem higham12_14_residual_identity (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (x_hat d_hat : Fin n → ℝ) (b r r_hat : Fin n → ℝ)
    (f2 : Fin n → ℝ) (y : Fin n → ℝ)
    (hr : ∀ i : Fin n, r i = b i - ∑ j : Fin n, A i j * x_hat j)
    (hy : ∀ i : Fin n, y i = x_hat i + d_hat i + f2 i) :
    ∀ i : Fin n, b i - ∑ j : Fin n, A i j * y j =
      (r_hat i - ∑ j : Fin n, A i j * d_hat j) - (r_hat i - r i) -
        ∑ j : Fin n, A i j * f2 j :=
  thm_11_3_identity n A x_hat d_hat b r r_hat f2 y hr hy

/-- **Equation (12.14)** triangle-inequality form. -/
theorem higham12_14_residual_bound (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (x_hat d_hat : Fin n → ℝ) (b r r_hat : Fin n → ℝ)
    (f2 : Fin n → ℝ) (y : Fin n → ℝ)
    (hr : ∀ i : Fin n, r i = b i - ∑ j : Fin n, A i j * x_hat j)
    (hy : ∀ i : Fin n, y i = x_hat i + d_hat i + f2 i) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * y j| ≤
        |r_hat i - ∑ j : Fin n, A i j * d_hat j| +
        |r_hat i - r i| +
        ∑ j : Fin n, |A i j| * |f2 j| :=
  thm_11_3_bound n A x_hat d_hat b r r_hat f2 y hr hy

/-- **Equation (12.17)** update-rounding bound in multiplied form. -/
theorem higham12_17_update_bound (n : ℕ) (fp : FPModel)
    (x_hat d_hat y f2 : Fin n → ℝ)
    (hy : ∀ i : Fin n, y i = x_hat i + d_hat i + f2 i)
    (hf2 : ∀ j : Fin n, |f2 j| ≤ fp.u * (|x_hat j| + |d_hat j|))
    (hu_lt : fp.u < 1) :
    ∀ j : Fin n,
      (1 - fp.u) * |x_hat j| ≤ |y j| + (1 + fp.u) * |d_hat j| :=
  eq_11_15 n fp x_hat d_hat y f2 hy hf2 hu_lt

/-- **Equation (12.17)** update-rounding bound in divided form. -/
theorem higham12_17_update_bound_div (n : ℕ) (fp : FPModel)
    (x_hat d_hat y f2 : Fin n → ℝ)
    (hy : ∀ i : Fin n, y i = x_hat i + d_hat i + f2 i)
    (hf2 : ∀ j : Fin n, |f2 j| ≤ fp.u * (|x_hat j| + |d_hat j|))
    (hu_lt : fp.u < 1) :
    ∀ j : Fin n,
      |x_hat j| ≤ (|y j| + (1 + fp.u) * |d_hat j|) / (1 - fp.u) :=
  eq_11_15_div n fp x_hat d_hat y f2 hy hf2 hu_lt

/-- **Equation (12.18)** residual absolute bound obtained from the
conventional residual error and an initial backward-error bound. -/
theorem higham12_18_residual_abs_bound (n : ℕ) (fp : FPModel)
    (A : Fin n → Fin n → ℝ) (b x_hat : Fin n → ℝ)
    (r r_hat : Fin n → ℝ)
    (hr : ∀ i : Fin n, r i = b i - ∑ j : Fin n, A i j * x_hat j)
    (hres : ∀ i : Fin n, |r_hat i - r i| ≤
      gamma fp (n + 1) * (|b i| + ∑ j : Fin n, |A i j| * |x_hat j|))
    (hn1 : gammaValid fp (n + 1))
    (omega0 : ℝ) (homega0_nonneg : 0 ≤ omega0)
    (hbw0 : ∀ i : Fin n,
      |r i| ≤ omega0 * (∑ j : Fin n, |A i j| * |x_hat j| + |b i|)) :
    ∀ i : Fin n,
      |r_hat i| ≤ (gamma fp (n + 1) + omega0) *
        (∑ j : Fin n, |A i j| * |x_hat j| + |b i|) :=
  eq_11_16 n fp A b x_hat r r_hat hr hres hn1 omega0 homega0_nonneg hbw0

/-- **Equation (12.19)** combined coefficient bound before the correction
vector is eliminated. -/
theorem higham12_19_combined_coefficients (n : ℕ) (fp : FPModel)
    (A : Fin n → Fin n → ℝ)
    (x_hat d_hat : Fin n → ℝ) (b r r_hat : Fin n → ℝ)
    (f2 : Fin n → ℝ) (y : Fin n → ℝ)
    (DeltaA_solve : Fin n → Fin n → ℝ)
    (mu : ℝ) (hmu_nonneg : 0 ≤ mu)
    (hr : ∀ i : Fin n, r i = b i - ∑ j : Fin n, A i j * x_hat j)
    (hy : ∀ i : Fin n, y i = x_hat i + d_hat i + f2 i)
    (hsolve : ∀ i : Fin n,
      ∑ j : Fin n, (A i j + DeltaA_solve i j) * d_hat j = r_hat i)
    (hDeltaA : ∀ i j : Fin n, |DeltaA_solve i j| ≤ mu * |A i j|)
    (hres : ∀ i : Fin n, |r_hat i - r i| ≤
      gamma fp (n + 1) * (|b i| + ∑ j : Fin n, |A i j| * |x_hat j|))
    (hf2 : ∀ j : Fin n, |f2 j| ≤ fp.u * (|x_hat j| + |d_hat j|))
    (hn1 : gammaValid fp (n + 1)) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * y j| ≤
        (gamma fp (n + 1) + fp.u) * ∑ j : Fin n, |A i j| * |x_hat j| +
        (mu + fp.u) * ∑ j : Fin n, |A i j| * |d_hat j| +
        gamma fp (n + 1) * |b i| :=
  eq_11_17 n fp A x_hat d_hat b r r_hat f2 y DeltaA_solve mu
    hmu_nonneg hr hy hsolve hDeltaA hres hf2 hn1

/-- **Equations (12.20)-(12.21)** correction-vector bound via an abstract
resolver for the perturbed correction equation. -/
theorem higham12_20_correction_via_resolver (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ)
    (d_hat r_hat : Fin n → ℝ)
    (DeltaA : Fin n → Fin n → ℝ)
    (mu : ℝ) (hmu_nonneg : 0 ≤ mu)
    (hsolve : ∀ i : Fin n,
      ∑ j : Fin n, (A i j + DeltaA i j) * d_hat j = r_hat i)
    (hDeltaA : ∀ i j : Fin n, |DeltaA i j| ≤ mu * |A i j|)
    (hA_inv : ∀ (v w : Fin n → ℝ),
      (∀ i : Fin n, ∑ j : Fin n, A i j * v j = w i) →
      ∀ i : Fin n, |v i| ≤ ∑ j : Fin n, |A_inv i j| * |w j|)
    (C : Fin n → Fin n → ℝ)
    (hC_nonneg : ∀ i j : Fin n, 0 ≤ C i j)
    (hC : ∀ (v w : Fin n → ℝ),
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * v j = w i) →
      ∀ i : Fin n, |v i| ≤ ∑ j : Fin n, C i j * |w j|) :
    ∀ i : Fin n, |d_hat i| ≤ ∑ j : Fin n, C i j * |r_hat j| :=
  eq_11_18 n A A_inv d_hat r_hat DeltaA mu hmu_nonneg
    hsolve hDeltaA hA_inv C hC_nonneg hC

/-- **Equation (12.21)** product form: multiply the correction resolver by
`|A|` row-wise. -/
theorem higham12_21_correction_product_bound (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (d_hat r_hat : Fin n → ℝ)
    (C : Fin n → Fin n → ℝ)
    (hC_nonneg : ∀ i j : Fin n, 0 ≤ C i j)
    (hd_bound : ∀ j : Fin n,
      |d_hat j| ≤ ∑ k : Fin n, C j k * |r_hat k|) :
    ∀ i : Fin n, ∑ j : Fin n, |A i j| * |d_hat j| ≤
      ∑ j : Fin n, |A i j| * ∑ k : Fin n, C j k * |r_hat k| :=
  correction_product_bound n A d_hat r_hat C hC_nonneg hd_bound

/-- **Theorem 12.4 / equation (12.22)** exact conditional two-gamma
conclusion.  The source's printed sufficient condition is approximate; here the
needed dominance inequality is explicit. -/
theorem higham12_4_conditional_two_gamma_bound (n : ℕ) (fp : FPModel)
    (A : Fin n → Fin n → ℝ)
    (x_hat d_hat r_hat : Fin n → ℝ)
    (DeltaA_solve : Fin n → Fin n → ℝ)
    (mu nu : ℝ) (omega : Fin n → ℝ)
    (b : Fin n → ℝ)
    (r : Fin n → ℝ)
    (hr : ∀ i : Fin n, r i = b i - ∑ j : Fin n, A i j * x_hat j)
    (hres : ∀ i : Fin n, |r_hat i - r i| ≤ nu * |r i| + omega i)
    (hsolve : ∀ i : Fin n,
      ∑ j : Fin n, (A i j + DeltaA_solve i j) * d_hat j = r_hat i)
    (hDeltaA : ∀ i j : Fin n, |DeltaA_solve i j| ≤ mu * |A i j|)
    (y : Fin n → ℝ)
    (hy : ∀ i : Fin n, y i = x_hat i + d_hat i)
    (hmu_nonneg : 0 ≤ mu) (hnu_nonneg : 0 ≤ nu)
    (homega_nonneg : ∀ i : Fin n, 0 ≤ omega i)
    (hdom : ∀ i : Fin n,
      mu * ∑ j : Fin n, |A i j| * |d_hat j| + nu * |r i| + omega i ≤
        (2 * gamma fp (n + 1)) * ∑ j : Fin n, |A i j| * |y j|) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * y j| ≤
        (2 * gamma fp (n + 1)) * ∑ j : Fin n, |A i j| * |y j| :=
  refinement_two_gamma_bound n A x_hat d_hat r_hat DeltaA_solve mu nu omega
    b r hr hres hsolve hDeltaA y hy hmu_nonneg hnu_nonneg homega_nonneg
    (2 * gamma fp (n + 1)) hdom

/-! ## Problems and Appendix A -/

/-- Component skewness `max_i |x_i| / min_i |x_i|` used in Problem 12.1.
It is defined only for nonempty finite vectors; positivity of all components is
carried by theorems that use it. -/
noncomputable def higham12_vectorAbsSkew {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : ℝ :=
  let hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  Finset.sup' Finset.univ hne (fun i : Fin n => |x i|) /
    Finset.inf' Finset.univ hne (fun i : Fin n => |x i|)

/-- The component skewness is nonnegative when every component is nonzero. -/
theorem higham12_vectorAbsSkew_nonneg {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hpos : ∀ i : Fin n, 0 < |x i|) :
    0 ≤ higham12_vectorAbsSkew hn x := by
  unfold higham12_vectorAbsSkew
  let hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hmin_pos : 0 < Finset.inf' Finset.univ hne (fun i : Fin n => |x i|) := by
    rw [Finset.lt_inf'_iff]
    intro i _
    exact hpos i
  have hmax_nonneg :
      0 ≤ Finset.sup' Finset.univ hne (fun i : Fin n => |x i|) := by
    exact le_trans (le_of_lt (hpos ⟨0, hn⟩))
      (Finset.le_sup' (fun i : Fin n => |x i|) (Finset.mem_univ ⟨0, hn⟩))
  exact div_nonneg hmax_nonneg (le_of_lt hmin_pos)

/-- The max/min skewness bounds any component by any other component after
scaling. -/
theorem higham12_vectorAbsSkew_entry_bound {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hpos : ∀ i : Fin n, 0 < |x i|)
    (i j : Fin n) :
    |x j| ≤ higham12_vectorAbsSkew hn x * |x i| := by
  unfold higham12_vectorAbsSkew
  let hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  let xmax := Finset.sup' Finset.univ hne (fun k : Fin n => |x k|)
  let xmin := Finset.inf' Finset.univ hne (fun k : Fin n => |x k|)
  have hmin_pos : 0 < xmin := by
    dsimp [xmin]
    rw [Finset.lt_inf'_iff]
    intro k _
    exact hpos k
  have hj_le : |x j| ≤ xmax := by
    exact Finset.le_sup' (fun k : Fin n => |x k|) (Finset.mem_univ j)
  have hmin_le_i : xmin ≤ |x i| := by
    exact Finset.inf'_le (fun k : Fin n => |x k|) (Finset.mem_univ i)
  have hmax_nonneg : 0 ≤ xmax := by
    exact le_trans (le_of_lt (hpos ⟨0, hn⟩))
      (Finset.le_sup' (fun k : Fin n => |x k|) (Finset.mem_univ ⟨0, hn⟩))
  have hratio_nonneg : 0 ≤ xmax / xmin :=
    div_nonneg hmax_nonneg (le_of_lt hmin_pos)
  have hscale : xmax = (xmax / xmin) * xmin := by
    field_simp [ne_of_gt hmin_pos]
  have hmax_le : xmax ≤ (xmax / xmin) * |x i| := by
    have hmul : (xmax / xmin) * xmin ≤ (xmax / xmin) * |x i| :=
      mul_le_mul_of_nonneg_left hmin_le_i hratio_nonneg
    linarith
  exact le_trans hj_le hmax_le

/-- **Problem 12.1**, square form used by the Appendix solution:
`|A||x| <= sigma ||A||_inf |x|`, where
`sigma = max_i |x_i| / min_i |x_i|`.  The printed problem states `A` as
rectangular, but the displayed right-hand vector has the same index type as
`x`; this theorem records the dimension-compatible form actually used. -/
theorem higham12_problem_12_1_square {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hpos : ∀ i : Fin n, 0 < |x i|) :
    ∀ i : Fin n,
      ∑ j : Fin n, |A i j| * |x j| ≤
        higham12_vectorAbsSkew hn x * infNorm A * |x i| := by
  intro i
  let sigma := higham12_vectorAbsSkew hn x
  have hsigma_nonneg : 0 ≤ sigma :=
    higham12_vectorAbsSkew_nonneg hn x hpos
  have hsigmax_nonneg : 0 ≤ sigma * |x i| :=
    mul_nonneg hsigma_nonneg (abs_nonneg _)
  calc
    ∑ j : Fin n, |A i j| * |x j|
        ≤ ∑ j : Fin n, |A i j| * (sigma * |x i|) :=
          Finset.sum_le_sum (fun j _ =>
            mul_le_mul_of_nonneg_left
              (higham12_vectorAbsSkew_entry_bound hn x hpos i j)
              (abs_nonneg _))
    _ = (∑ j : Fin n, |A i j|) * (sigma * |x i|) := by
          rw [Finset.sum_mul]
    _ ≤ infNorm A * (sigma * |x i|) :=
          mul_le_mul_of_nonneg_right (row_sum_le_infNorm A i) hsigmax_nonneg
    _ = higham12_vectorAbsSkew hn x * infNorm A * |x i| := by
          ring

end LeanFpAnalysis.FP
