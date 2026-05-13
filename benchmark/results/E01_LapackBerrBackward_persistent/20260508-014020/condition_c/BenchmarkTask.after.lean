import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

noncomputable def lapackBerrDenom (n : ℕ)
    (A : Fin n → Fin n → ℝ) (x b : Fin n → ℝ) (i : Fin n) : ℝ :=
  |b i| + ∑ j : Fin n, |A i j| * |x j|

def componentwiseBackwardCompatible (n : ℕ)
    (A : Fin n → Fin n → ℝ) (x b : Fin n → ℝ) (eta : ℝ) : Prop :=
  ∃ DeltaA : Fin n → Fin n → ℝ,
  ∃ Deltab : Fin n → ℝ,
    (∀ i j, |DeltaA i j| ≤ eta * |A i j|) ∧
    (∀ i, |Deltab i| ≤ eta * |b i|) ∧
    ∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x j = b i + Deltab i

theorem lapackBerr_backward_certificate
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (x b : Fin n → ℝ)
    (eta : ℝ)
    (hn : gammaValid fp n)
    (hn1 : gammaValid fp (n + 1))
    (heta_nonneg : 0 ≤ eta)
    (hcert : ∀ i : Fin n,
      |fl_residual fp n A x b i| +
        gamma fp (n + 1) * lapackBerrDenom n A x b i ≤
          eta * lapackBerrDenom n A x b i) :
    componentwiseBackwardCompatible n A x b eta := by
  classical
  let r : Fin n → ℝ := fun i => b i - ∑ j : Fin n, A i j * x j
  let denom : Fin n → ℝ := fun i => lapackBerrDenom n A x b i
  have hdenom_nonneg : ∀ i, 0 ≤ denom i := by
    intro i
    have hs : 0 ≤ ∑ j : Fin n, |A i j| * |x j| :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    simp [denom, lapackBerrDenom, add_nonneg (abs_nonneg (b i)) hs]
  have hr_bound : ∀ i, |r i| ≤ eta * denom i := by
    intro i
    have hconv := conventional_residual_error fp n A x b hn hn1 i
    have htri : |r i| ≤
        |fl_residual fp n A x b i| +
          |fl_residual fp n A x b i - r i| := by
      have := abs_add_le (fl_residual fp n A x b i - r i)
        (-(fl_residual fp n A x b i))
      have hrewrite :
          (fl_residual fp n A x b i - r i) +
              (-(fl_residual fp n A x b i)) = -r i := by ring
      have h1 :
          |r i| ≤ |fl_residual fp n A x b i - r i| +
            |fl_residual fp n A x b i| := by
        simpa [hrewrite, abs_neg] using this
      simpa [add_comm] using h1
    calc
      |r i| ≤ |fl_residual fp n A x b i| +
          |fl_residual fp n A x b i - r i| := htri
      _ ≤ |fl_residual fp n A x b i| +
          gamma fp (n + 1) * denom i := by
          have hconv' :
              |fl_residual fp n A x b i - r i| ≤
                gamma fp (n + 1) * denom i := by
            simpa [r, denom, lapackBerrDenom] using hconv
          simpa [add_comm] using
            (add_le_add_right hconv' |fl_residual fp n A x b i|)
      _ ≤ eta * denom i := hcert i
  let coeff : Fin n → ℝ := fun i =>
    if denom i = 0 then 0 else r i / denom i
  let DeltaA : Fin n → Fin n → ℝ := fun i j =>
    coeff i * |A i j| * if x j = 0 then 0 else |x j| / x j
  let Deltab : Fin n → ℝ := fun i => -coeff i * |b i|
  refine ⟨DeltaA, Deltab, ?_, ?_, ?_⟩
  · intro i j
    by_cases hzero : denom i = 0
    · have hc : coeff i = 0 := by simp [coeff, hzero]
      simp [DeltaA, hc, mul_nonneg heta_nonneg (abs_nonneg (A i j))]
    · have hpos : 0 < denom i := lt_of_le_of_ne (hdenom_nonneg i) (Ne.symm hzero)
      have hc_abs : |coeff i| ≤ eta := by
        have h := hr_bound i
        have hdiv : |r i / denom i| ≤ eta := by
          rw [abs_div]
          rw [abs_of_pos hpos]
          rw [div_le_iff₀ hpos]
          simpa [mul_comm, mul_left_comm, mul_assoc] using h
        simpa [coeff, hzero] using hdiv
      by_cases hx : x j = 0
      · simp [DeltaA, hx, mul_nonneg heta_nonneg (abs_nonneg (A i j))]
      · have hfactor_abs : |(|x j| / x j)| = 1 := by
          rw [abs_div, abs_abs]
          exact div_self (abs_ne_zero.mpr hx)
        calc
          |DeltaA i j| =
              |coeff i| * |A i j| := by
                simp [DeltaA, hx, abs_mul, hfactor_abs, mul_assoc]
          _ ≤ eta * |A i j| :=
              mul_le_mul_of_nonneg_right hc_abs (abs_nonneg _)
  · intro i
    by_cases hzero : denom i = 0
    · have hc : coeff i = 0 := by simp [coeff, hzero]
      simp [Deltab, hc, mul_nonneg heta_nonneg (abs_nonneg (b i))]
    · have hpos : 0 < denom i := lt_of_le_of_ne (hdenom_nonneg i) (Ne.symm hzero)
      have hc_abs : |coeff i| ≤ eta := by
        have h := hr_bound i
        have hdiv : |r i / denom i| ≤ eta := by
          rw [abs_div]
          rw [abs_of_pos hpos]
          rw [div_le_iff₀ hpos]
          simpa [mul_comm, mul_left_comm, mul_assoc] using h
        simpa [coeff, hzero] using hdiv
      calc
        |Deltab i| = |coeff i| * |b i| := by simp [Deltab, abs_mul]
        _ ≤ eta * |b i| := mul_le_mul_of_nonneg_right hc_abs (abs_nonneg _)
  · intro i
    by_cases hzero : denom i = 0
    · have hb_abs : |b i| = 0 := by
        have hnonneg_sum :
            0 ≤ ∑ j : Fin n, |A i j| * |x j| :=
          Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
        have h := hzero
        simp [denom, lapackBerrDenom] at h
        linarith [abs_nonneg (b i), hnonneg_sum]
      have hb : b i = 0 := abs_eq_zero.mp hb_abs
      have hs_abs :
          ∑ j : Fin n, |A i j| * |x j| = 0 := by
        have hnonneg_sum :
            0 ≤ ∑ j : Fin n, |A i j| * |x j| :=
          Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
        have h := hzero
        simp [denom, lapackBerrDenom, hb_abs] at h
        linarith
      have hterms_zero : ∀ j : Fin n, A i j * x j = 0 := by
        intro j
        have hterm_nonneg : 0 ≤ |A i j| * |x j| :=
          mul_nonneg (abs_nonneg _) (abs_nonneg _)
        have hterm_le_sum :
            |A i j| * |x j| ≤ ∑ k : Fin n, |A i k| * |x k| :=
          by
            simpa using
              (Finset.single_le_sum
                (s := (Finset.univ : Finset (Fin n)))
                (f := fun k : Fin n => |A i k| * |x k|)
                (fun k _ => mul_nonneg (abs_nonneg (A i k)) (abs_nonneg (x k)))
                (Finset.mem_univ j))
        have hterm_zero : |A i j| * |x j| = 0 := by linarith
        have habs_prod : |A i j * x j| = 0 := by
          rw [abs_mul]
          exact hterm_zero
        exact abs_eq_zero.mp habs_prod
      have hc : coeff i = 0 := by simp [coeff, hzero]
      simp [DeltaA, Deltab, hc, hb, hterms_zero]
    · have hpos : 0 < denom i := lt_of_le_of_ne (hdenom_nonneg i) (Ne.symm hzero)
      have hc : coeff i * denom i = r i := by
        simp [coeff, hzero]
      have hDelta_sum :
          ∑ j : Fin n, DeltaA i j * x j =
            coeff i * ∑ j : Fin n, |A i j| * |x j| := by
        calc
          ∑ j : Fin n, DeltaA i j * x j =
              ∑ j : Fin n, coeff i * (|A i j| * |x j|) := by
                apply Finset.sum_congr rfl
                intro j _
                by_cases hx : x j = 0
                · simp [DeltaA, hx]
                · have hxdiv : (|x j| / x j) * x j = |x j| := by
                    exact div_mul_cancel₀ (|x j|) hx
                  calc
                    DeltaA i j * x j =
                        (coeff i * |A i j|) * ((|x j| / x j) * x j) := by
                          simp [DeltaA, hx, mul_assoc, mul_left_comm, mul_comm]
                    _ = coeff i * (|A i j| * |x j|) := by
                          rw [hxdiv]
                          ring
          _ = coeff i * ∑ j : Fin n, |A i j| * |x j| := by
                rw [Finset.mul_sum]
      have hmain :
          ∑ j : Fin n, DeltaA i j * x j - Deltab i = r i := by
        rw [hDelta_sum]
        have hden :
            denom i = |b i| + ∑ j : Fin n, |A i j| * |x j| := by
          rfl
        change coeff i * (∑ j : Fin n, |A i j| * |x j|) -
            (-coeff i * |b i|) = r i
        have hc' :
            coeff i * (|b i| + ∑ j : Fin n, |A i j| * |x j|) = r i := by
          rw [← hden]
          exact hc
        calc
          coeff i * (∑ j : Fin n, |A i j| * |x j|) -
              (-coeff i * |b i|)
              = coeff i * (|b i| + ∑ j : Fin n, |A i j| * |x j|) := by ring
          _ = r i := hc'
      calc
        ∑ j : Fin n, (A i j + DeltaA i j) * x j
            = ∑ j : Fin n, A i j * x j + ∑ j : Fin n, DeltaA i j * x j := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = b i + Deltab i := by
              have hr : r i = b i - ∑ j : Fin n, A i j * x j := rfl
              linarith

end LeanFpAnalysis.FP
