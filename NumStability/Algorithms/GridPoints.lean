-- Algorithms/GridPoints.lean
--
-- Higham Chapter 4, Problem 4.9.

import Mathlib.Tactic
import NumStability.Analysis.Summation

namespace NumStability

open scoped BigOperators

/-!
# Equally Spaced Grid Points

Higham Chapter 4, Problem 4.9 compares three ways to form grid points
`x_i = a + i*h`, where `h = (b-a)/n` and `a`, `b` are floating-point values
but `h` need not be.  The theorem surface separates two effects:

* methods based on a stored step `hhat` inherit the representation error
  `i*|hhat - h|`;
* the convex-combination formula uses `a` and `b` directly and therefore has
  no stored-step error term in its exact target, though it still has ordinary
  rounded multiplication/addition error.
-/

/-- Exact grid point formed from an exact interval `[a,b]`. -/
noncomputable def gridPointExact (a b : ℝ) (n i : ℕ) : ℝ :=
  a + (i : ℝ) * ((b - a) / (n : ℝ))

/-- Exact grid point formed from a stored step `hhat`. -/
noncomputable def gridPointFromStep (a hhat : ℝ) (i : ℕ) : ℝ :=
  a + (i : ℝ) * hhat

/-- Exact convex-combination grid expression. -/
noncomputable def gridPointConvex (a b : ℝ) (n i : ℕ) : ℝ :=
  (1 - (i : ℝ) / (n : ℝ)) * a + ((i : ℝ) / (n : ℝ)) * b

/-- The convex-combination expression is algebraically the same exact grid
point when `n` is nonzero. -/
theorem gridPointConvex_eq_exact (a b : ℝ) (n i : ℕ) :
    gridPointConvex a b n i = gridPointExact a b n i := by
  simp [gridPointConvex, gridPointExact]
  ring

/-- Stored-step exact grid points differ from the exact `[a,b]` grid by the
stored-step error amplified by the index. -/
theorem gridPointFromStep_error_eq (a b hhat : ℝ) (n i : ℕ) :
    |gridPointFromStep a hhat i - gridPointExact a b n i| =
      (i : ℝ) * |hhat - (b - a) / (n : ℝ)| := by
  have hi_nonneg : 0 ≤ (i : ℝ) := by positivity
  simp [gridPointFromStep, gridPointExact]
  rw [← mul_sub, abs_mul, abs_of_nonneg hi_nonneg]

/-- Floating-point recurrence `x_{j+1}=fl(x_j+hhat)`, starting from `a`. -/
noncomputable def fl_gridRecurrence (fp : FPModel)
    (a hhat : ℝ) (i : ℕ) : ℝ :=
  Fin.foldl i (fun acc _ => fp.fl_add acc hhat) a

/-- Floating-point direct route `fl(a + fl(i*hhat))`. -/
noncomputable def fl_gridDirect (fp : FPModel)
    (a hhat : ℝ) (i : ℕ) : ℝ :=
  fp.fl_add a (fp.fl_mul (i : ℝ) hhat)

/-- Floating-point convex route
`fl(fl((1-i/n)*a) + fl((i/n)*b))`. -/
noncomputable def fl_gridConvex (fp : FPModel)
    (a b : ℝ) (n i : ℕ) : ℝ :=
  let t : ℝ := (i : ℝ) / (n : ℝ)
  fp.fl_add (fp.fl_mul (1 - t) a) (fp.fl_mul t b)

/-- Rounding error of the recurrence route relative to the stored-step grid. -/
theorem fl_gridRecurrence_storedStep_error_bound (fp : FPModel)
    (a hhat : ℝ) (i : ℕ) (hγ : gammaValid fp i) :
    |fl_gridRecurrence fp a hhat i - gridPointFromStep a hhat i| ≤
      gamma fp i * (|a| + (i : ℝ) * |hhat|) := by
  obtain ⟨Θ, θ, hΘ, hθ, hfold⟩ :=
    fl_sum_error_init fp i (fun _ : Fin i => hhat) a hγ
  have hsum_const : (∑ _ : Fin i, hhat) = (i : ℝ) * hhat := by
    simp
  have habs_sum_const : (∑ _ : Fin i, |hhat|) = (i : ℝ) * |hhat| := by
    simp
  have hsum_expand :
      (∑ j : Fin i, hhat * (1 + θ j)) =
        (i : ℝ) * hhat + ∑ j : Fin i, hhat * θ j := by
    rw [← hsum_const]
    simp [mul_add, Finset.sum_add_distrib]
  calc
    |fl_gridRecurrence fp a hhat i - gridPointFromStep a hhat i|
        = |a * Θ + ∑ j : Fin i, hhat * θ j| := by
            rw [fl_gridRecurrence, hfold, gridPointFromStep, hsum_expand]
            ring_nf
    _ ≤ |a * Θ| + |∑ j : Fin i, hhat * θ j| := abs_add_le _ _
    _ ≤ |a| * gamma fp i + ∑ j : Fin i, |hhat| * gamma fp i := by
        exact add_le_add
          (by
            simpa [abs_mul] using
              mul_le_mul_of_nonneg_left hΘ (abs_nonneg a))
          (by
            calc
              |∑ j : Fin i, hhat * θ j|
                  ≤ ∑ j : Fin i, |hhat * θ j| :=
                    Finset.abs_sum_le_sum_abs _ _
              _ = ∑ j : Fin i, |hhat| * |θ j| := by
                    apply Finset.sum_congr rfl
                    intro j _hj
                    rw [abs_mul]
              _ ≤ ∑ j : Fin i, |hhat| * gamma fp i :=
                    Finset.sum_le_sum fun j _hj =>
                      mul_le_mul_of_nonneg_left (hθ j) (abs_nonneg hhat))
    _ = gamma fp i * (|a| + (i : ℝ) * |hhat|) := by
        rw [← Finset.sum_mul, habs_sum_const]
        ring

/-- Recurrence route error against the exact `[a,b]` grid, exposing the stored
step error. -/
theorem fl_gridRecurrence_error_bound (fp : FPModel)
    (a b hhat : ℝ) (n i : ℕ) (hγ : gammaValid fp i) :
    |fl_gridRecurrence fp a hhat i - gridPointExact a b n i| ≤
      gamma fp i * (|a| + (i : ℝ) * |hhat|) +
        (i : ℝ) * |hhat - (b - a) / (n : ℝ)| := by
  have hround := fl_gridRecurrence_storedStep_error_bound fp a hhat i hγ
  have hstep := gridPointFromStep_error_eq a b hhat n i
  calc
    |fl_gridRecurrence fp a hhat i - gridPointExact a b n i|
        ≤ |fl_gridRecurrence fp a hhat i - gridPointFromStep a hhat i| +
          |gridPointFromStep a hhat i - gridPointExact a b n i| := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            abs_add_le
              (fl_gridRecurrence fp a hhat i - gridPointFromStep a hhat i)
              (gridPointFromStep a hhat i - gridPointExact a b n i)
    _ ≤ gamma fp i * (|a| + (i : ℝ) * |hhat|) +
        (i : ℝ) * |hhat - (b - a) / (n : ℝ)| := by
        rw [hstep]
        exact add_le_add hround (le_refl _)

/-- Direct route error relative to the stored-step grid. -/
theorem fl_gridDirect_storedStep_error_bound (fp : FPModel)
    (a hhat : ℝ) (i : ℕ) (hγ : gammaValid fp 2) :
    |fl_gridDirect fp a hhat i - gridPointFromStep a hhat i| ≤
      gamma fp 2 * (|a| + |(i : ℝ) * hhat|) := by
  obtain ⟨δmul, hδmul, hmul⟩ := fp.model_mul (i : ℝ) hhat
  obtain ⟨δadd, hδadd, hadd⟩ := fp.model_add a (fp.fl_mul (i : ℝ) hhat)
  have hγ1 : gammaValid fp 1 := gammaValid_mono fp (by norm_num) hγ
  have hδmulγ1 : |δmul| ≤ gamma fp 1 :=
    le_trans hδmul (u_le_gamma fp (by norm_num) hγ1)
  have hδaddγ1 : |δadd| ≤ gamma fp 1 :=
    le_trans hδadd (u_le_gamma fp (by norm_num) hγ1)
  have hδaddγ2 : |δadd| ≤ gamma fp 2 :=
    le_trans hδadd (u_le_gamma fp (by norm_num) hγ)
  obtain ⟨θ, hθ, hθeq⟩ :=
    gamma_mul fp 1 1 δmul δadd hδmulγ1 hδaddγ1 hγ
  have hprod :
      ((i : ℝ) * hhat) * (1 + δmul) * (1 + δadd) =
        ((i : ℝ) * hhat) * (1 + θ) := by
    calc
      ((i : ℝ) * hhat) * (1 + δmul) * (1 + δadd)
          = ((i : ℝ) * hhat) * ((1 + δmul) * (1 + δadd)) := by ring
      _ = ((i : ℝ) * hhat) * (1 + θ) := by rw [hθeq]
  have hdirect_eq :
      (a + ((i : ℝ) * hhat) * (1 + δmul)) * (1 + δadd) -
          (a + (i : ℝ) * hhat) =
        a * δadd + ((i : ℝ) * hhat) * θ := by
    calc
      (a + ((i : ℝ) * hhat) * (1 + δmul)) * (1 + δadd) -
          (a + (i : ℝ) * hhat)
          = a * δadd +
              (((i : ℝ) * hhat) * (1 + δmul) * (1 + δadd) -
                (i : ℝ) * hhat) := by ring
      _ = a * δadd + (((i : ℝ) * hhat) * (1 + θ) -
            (i : ℝ) * hhat) := by rw [hprod]
      _ = a * δadd + ((i : ℝ) * hhat) * θ := by ring
  have ha : |a * δadd| ≤ |a| * gamma fp 2 := by
    simpa [abs_mul] using
      mul_le_mul_of_nonneg_left hδaddγ2 (abs_nonneg a)
  have hm : |((i : ℝ) * hhat) * θ| ≤ |(i : ℝ) * hhat| * gamma fp 2 := by
    simpa [abs_mul] using
      mul_le_mul_of_nonneg_left hθ (abs_nonneg ((i : ℝ) * hhat))
  calc
    |fl_gridDirect fp a hhat i - gridPointFromStep a hhat i|
        = |a * δadd + ((i : ℝ) * hhat) * θ| := by
            rw [fl_gridDirect, gridPointFromStep, hadd, hmul]
            rw [hdirect_eq]
    _ ≤ |a * δadd| + |((i : ℝ) * hhat) * θ| := abs_add_le _ _
    _ ≤ |a| * gamma fp 2 + |(i : ℝ) * hhat| * gamma fp 2 :=
        add_le_add ha hm
    _ = gamma fp 2 * (|a| + |(i : ℝ) * hhat|) := by ring

/-- Direct route error against the exact `[a,b]` grid, exposing the stored-step
error. -/
theorem fl_gridDirect_error_bound (fp : FPModel)
    (a b hhat : ℝ) (n i : ℕ) (hγ : gammaValid fp 2) :
    |fl_gridDirect fp a hhat i - gridPointExact a b n i| ≤
      gamma fp 2 * (|a| + |(i : ℝ) * hhat|) +
        (i : ℝ) * |hhat - (b - a) / (n : ℝ)| := by
  have hround := fl_gridDirect_storedStep_error_bound fp a hhat i hγ
  have hstep := gridPointFromStep_error_eq a b hhat n i
  calc
    |fl_gridDirect fp a hhat i - gridPointExact a b n i|
        ≤ |fl_gridDirect fp a hhat i - gridPointFromStep a hhat i| +
          |gridPointFromStep a hhat i - gridPointExact a b n i| := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            abs_add_le
              (fl_gridDirect fp a hhat i - gridPointFromStep a hhat i)
              (gridPointFromStep a hhat i - gridPointExact a b n i)
    _ ≤ gamma fp 2 * (|a| + |(i : ℝ) * hhat|) +
        (i : ℝ) * |hhat - (b - a) / (n : ℝ)| := by
        rw [hstep]
        exact add_le_add hround (le_refl _)

/-- Convex-combination route error against the exact `[a,b]` grid.  No
stored-step error appears. -/
theorem fl_gridConvex_error_bound (fp : FPModel)
    (a b : ℝ) {n i : ℕ} (_hn : n ≠ 0) (hγ : gammaValid fp 2) :
    |fl_gridConvex fp a b n i - gridPointExact a b n i| ≤
      gamma fp 2 *
        (|(1 - (i : ℝ) / (n : ℝ)) * a| +
          |((i : ℝ) / (n : ℝ)) * b|) := by
  let t : ℝ := (i : ℝ) / (n : ℝ)
  obtain ⟨δa, hδa, hmula⟩ := fp.model_mul (1 - t) a
  obtain ⟨δb, hδb, hmulb⟩ := fp.model_mul t b
  obtain ⟨δadd, hδadd, hadd⟩ :=
    fp.model_add (fp.fl_mul (1 - t) a) (fp.fl_mul t b)
  have hγ1 : gammaValid fp 1 := gammaValid_mono fp (by norm_num) hγ
  have hδaγ1 : |δa| ≤ gamma fp 1 :=
    le_trans hδa (u_le_gamma fp (by norm_num) hγ1)
  have hδbγ1 : |δb| ≤ gamma fp 1 :=
    le_trans hδb (u_le_gamma fp (by norm_num) hγ1)
  have hδaddγ1 : |δadd| ≤ gamma fp 1 :=
    le_trans hδadd (u_le_gamma fp (by norm_num) hγ1)
  obtain ⟨θa, hθa, hθaeq⟩ :=
    gamma_mul fp 1 1 δa δadd hδaγ1 hδaddγ1 hγ
  obtain ⟨θb, hθb, hθbeq⟩ :=
    gamma_mul fp 1 1 δb δadd hδbγ1 hδaddγ1 hγ
  have hproda :
      ((1 - t) * a) * (1 + δa) * (1 + δadd) =
        ((1 - t) * a) * (1 + θa) := by
    calc
      ((1 - t) * a) * (1 + δa) * (1 + δadd)
          = ((1 - t) * a) * ((1 + δa) * (1 + δadd)) := by ring
      _ = ((1 - t) * a) * (1 + θa) := by rw [hθaeq]
  have hprodb :
      (t * b) * (1 + δb) * (1 + δadd) =
        (t * b) * (1 + θb) := by
    calc
      (t * b) * (1 + δb) * (1 + δadd)
          = (t * b) * ((1 + δb) * (1 + δadd)) := by ring
      _ = (t * b) * (1 + θb) := by rw [hθbeq]
  have hconv_eq :
      (((1 - t) * a) * (1 + δa) + (t * b) * (1 + δb)) *
          (1 + δadd) - (((1 - t) * a) + t * b) =
        ((1 - t) * a) * θa + (t * b) * θb := by
    calc
      (((1 - t) * a) * (1 + δa) + (t * b) * (1 + δb)) *
          (1 + δadd) - (((1 - t) * a) + t * b)
          = (((1 - t) * a) * (1 + δa) * (1 + δadd) -
              ((1 - t) * a)) +
            ((t * b) * (1 + δb) * (1 + δadd) - t * b) := by ring
      _ = (((1 - t) * a) * (1 + θa) - ((1 - t) * a)) +
            ((t * b) * (1 + θb) - t * b) := by rw [hproda, hprodb]
      _ = ((1 - t) * a) * θa + (t * b) * θb := by ring
  have ha :
      |((1 - t) * a) * θa| ≤ |(1 - t) * a| * gamma fp 2 := by
    simpa [abs_mul] using
      mul_le_mul_of_nonneg_left hθa (abs_nonneg ((1 - t) * a))
  have hb : |(t * b) * θb| ≤ |t * b| * gamma fp 2 := by
    simpa [abs_mul] using
      mul_le_mul_of_nonneg_left hθb (abs_nonneg (t * b))
  have hexact : gridPointConvex a b n i = gridPointExact a b n i :=
    gridPointConvex_eq_exact a b n i
  calc
    |fl_gridConvex fp a b n i - gridPointExact a b n i|
        = |((1 - t) * a) * θa + (t * b) * θb| := by
            rw [← hexact]
            simp [fl_gridConvex, gridPointConvex, t]
            rw [hadd, hmula, hmulb]
            rw [hconv_eq]
    _ ≤ |((1 - t) * a) * θa| + |(t * b) * θb| := abs_add_le _ _
    _ ≤ |(1 - t) * a| * gamma fp 2 + |t * b| * gamma fp 2 :=
        add_le_add ha hb
    _ = gamma fp 2 * (|(1 - t) * a| + |t * b|) := by ring

end NumStability
