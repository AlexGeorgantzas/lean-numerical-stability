/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QED
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.Coprime.Lemmas
import LeanFpAnalysis.FP.Analysis.Norms
import Mathlib.Topology.Basic

namespace LeanFpAnalysis.FP

open scoped BigOperators Topology
open Filter

/-! # Higham Chapter 22: Vandermonde systems

This module records the exact algebraic core of the chapter: Higham's column-node
orientation, nonsingularity, Lagrange cardinal functions, Algorithms 22.1,
22.2, 22.3, and 22.8, and their polynomial/recurrence objects. Citation-only
condition estimates and long rounded factor analyses use explicit local
decomposition domains with constructive producers; final solve and error
inequalities are derived rather than stored as domain fields.
-/

section Vandermonde

variable {n : ℕ}

/-- Higham, 2nd ed., Chapter 22, p. 416: the Vandermonde matrix whose columns
are indexed by the nodes and whose rows are powers.  Mathlib's Vandermonde
matrix uses the transpose orientation, so this is a source-facing adapter. -/
def higham22Vandermonde (alpha : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.transpose (Matrix.vandermonde alpha)

@[simp]
theorem higham22Vandermonde_apply (alpha : Fin n → ℂ) (i j : Fin n) :
    higham22Vandermonde alpha i j = alpha j ^ (i : ℕ) := by
  rfl

/-- The source Vandermonde determinant is nonzero exactly when the nodes are
distinct.  This closes the precise nonsingularity prose immediately after
equation (22.1). -/
theorem higham22_vandermonde_det_ne_zero_iff {alpha : Fin n → ℂ} :
    (higham22Vandermonde alpha).det ≠ 0 ↔ Function.Injective alpha := by
  simpa [higham22Vandermonde, Matrix.det_transpose] using
    (Matrix.det_vandermonde_ne_zero_iff (v := alpha))

/-- Equation (22.1), evaluated rather than represented as a polynomial: the
`i`th Lagrange cardinal function. -/
noncomputable def higham22LagrangeValue
    (alpha : Fin n → ℂ) (i : Fin n) (x : ℂ) : ℂ :=
  ∏ k : Fin n, if k = i then 1 else (x - alpha k) / (alpha i - alpha k)

/-- Equation (22.1) at its own interpolation node. -/
theorem higham22_lagrangeValue_self
    {alpha : Fin n → ℂ} (halpha : Function.Injective alpha) (i : Fin n) :
    higham22LagrangeValue alpha i (alpha i) = 1 := by
  unfold higham22LagrangeValue
  apply Finset.prod_eq_one
  intro k _hk
  by_cases hki : k = i
  · simp [hki]
  · have hne : alpha i - alpha k ≠ 0 := by
      exact sub_ne_zero.mpr (halpha.ne (Ne.symm hki))
    simp [hki, hne]

/-- Equation (22.1) vanishes at every other interpolation node. -/
theorem higham22_lagrangeValue_other
    {alpha : Fin n → ℂ} (i j : Fin n) (hji : j ≠ i) :
    higham22LagrangeValue alpha i (alpha j) = 0 := by
  unfold higham22LagrangeValue
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp [hji]

/-- Cardinal form of equation (22.1). -/
theorem higham22_lagrangeValue_node
    {alpha : Fin n → ℂ} (halpha : Function.Injective alpha) (i j : Fin n) :
    higham22LagrangeValue alpha i (alpha j) = if j = i then 1 else 0 := by
  by_cases hji : j = i
  · subst j
    simp [higham22_lagrangeValue_self halpha]
  · simp [hji, higham22_lagrangeValue_other i j hji]

/-- Higham, 2nd ed., Algorithm 22.1, p. 417, stage I: the monic master
polynomial formed by successively adjoining all interpolation nodes. -/
noncomputable def higham22Algorithm1MasterPolynomial
    (alpha : Fin n → ℂ) : Polynomial ℂ :=
  ∏ k : Fin n, (Polynomial.X - Polynomial.C (alpha k))

/-- Higham, 2nd ed., Algorithm 22.1, p. 417, stage II: synthetic division of
the master polynomial by the factor belonging to node `i`. -/
noncomputable def higham22Algorithm1SyntheticQuotient
    (alpha : Fin n → ℂ) (i : Fin n) : Polynomial ℂ :=
  higham22Algorithm1MasterPolynomial alpha /ₘ
    (Polynomial.X - Polynomial.C (alpha i))

/-- The synthetic quotient is exactly the product with factor `i` removed. -/
theorem higham22_algorithm1SyntheticQuotient_eq_prod_erase
    (alpha : Fin n → ℂ) (i : Fin n) :
    higham22Algorithm1SyntheticQuotient alpha i =
      ∏ k ∈ (Finset.univ.erase i),
        (Polynomial.X - Polynomial.C (alpha k)) := by
  unfold higham22Algorithm1SyntheticQuotient higham22Algorithm1MasterPolynomial
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  exact Polynomial.mul_divByMonic_cancel_left _
    (Polynomial.monic_X_sub_C (alpha i))

/-- The exact denominator used to normalize the row produced for node `i`. -/
noncomputable def higham22Algorithm1Denominator
    (alpha : Fin n → ℂ) (i : Fin n) : ℂ :=
  (higham22Algorithm1SyntheticQuotient alpha i).eval (alpha i)

/-- Distinct nodes make every normalization denominator in Algorithm 22.1
nonzero. -/
theorem higham22_algorithm1Denominator_ne_zero
    {alpha : Fin n → ℂ} (halpha : Function.Injective alpha) (i : Fin n) :
    higham22Algorithm1Denominator alpha i ≠ 0 := by
  rw [higham22Algorithm1Denominator,
    higham22_algorithm1SyntheticQuotient_eq_prod_erase]
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  apply sub_ne_zero.mpr
  exact halpha.ne (Ne.symm (Finset.ne_of_mem_erase hk))

/-- The quotient evaluated at a different node vanishes. -/
theorem higham22_algorithm1SyntheticQuotient_eval_other
    (alpha : Fin n → ℂ) (i j : Fin n) (hji : j ≠ i) :
    (higham22Algorithm1SyntheticQuotient alpha i).eval (alpha j) = 0 := by
  rw [higham22_algorithm1SyntheticQuotient_eq_prod_erase]
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C]
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
  simp

/-- Multiset of interpolation nodes with node `i` omitted. -/
noncomputable def higham22NodesExcept
    (alpha : Fin n → ℂ) (i : Fin n) : Multiset ℂ :=
  (Finset.univ.erase i).val.map alpha

/-- The elementary symmetric function appearing in equation (22.2). -/
noncomputable def higham22ElementarySymmetricExcept
    (alpha : Fin n → ℂ) (i : Fin n) (r : ℕ) : ℂ :=
  (higham22NodesExcept alpha i).esymm r

/-- Vieta coefficient formula for the synthetic quotient. -/
theorem higham22_algorithm1SyntheticQuotient_coeff
    (alpha : Fin n → ℂ) (i j : Fin n) :
    (higham22Algorithm1SyntheticQuotient alpha i).coeff (j : ℕ) =
      (-1) ^ (n - 1 - (j : ℕ)) *
        higham22ElementarySymmetricExcept alpha i (n - 1 - (j : ℕ)) := by
  rw [higham22_algorithm1SyntheticQuotient_eq_prod_erase]
  have hcard : (higham22NodesExcept alpha i).card = n - 1 := by
    simp [higham22NodesExcept]
  have hj : (j : ℕ) ≤ (higham22NodesExcept alpha i).card := by
    rw [hcard]
    omega
  have hv := Multiset.prod_X_sub_C_coeff (higham22NodesExcept alpha i) hj
  rw [hcard] at hv
  simpa [higham22NodesExcept, higham22ElementarySymmetricExcept] using hv

/-- Product form of the normalization denominator in Algorithm 22.1. -/
theorem higham22_algorithm1Denominator_eq_prod
    (alpha : Fin n → ℂ) (i : Fin n) :
    higham22Algorithm1Denominator alpha i =
      ∏ k ∈ Finset.univ.erase i, (alpha i - alpha k) := by
  rw [higham22Algorithm1Denominator,
    higham22_algorithm1SyntheticQuotient_eq_prod_erase]
  simp [Polynomial.eval_prod]

/-- The printed two-stage Algorithm 22.1: form the master polynomial, apply
synthetic division for each node, and normalize the quotient coefficients.
Rows are indexed by nodes and columns by powers, matching `V⁻¹`. -/
noncomputable def higham22Algorithm1Printed
    (alpha : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j ↦
    (higham22Algorithm1SyntheticQuotient alpha i).coeff (j : ℕ) /
      higham22Algorithm1Denominator alpha i

/-- Higham, 2nd ed., equation (22.2), pp. 416--417: the explicit inverse
entry in terms of an elementary symmetric function.  Our `n × n` convention
corresponds to the source's indices `0,...,n-1`. -/
theorem higham22_eq22_2_inverse_entry
    (alpha : Fin n → ℂ) (i j : Fin n) :
    higham22Algorithm1Printed alpha i j =
      ((-1) ^ (n - 1 - (j : ℕ)) *
        higham22ElementarySymmetricExcept alpha i (n - 1 - (j : ℕ))) /
      (∏ k ∈ Finset.univ.erase i, (alpha i - alpha k)) := by
  rw [higham22Algorithm1Printed,
    higham22_algorithm1SyntheticQuotient_coeff,
    higham22_algorithm1Denominator_eq_prod]

/-- Norm of an elementary symmetric function is bounded by the corresponding
elementary symmetric function of the norms. -/
theorem higham22_norm_esymm_le (s : Multiset ℂ) (r : ℕ) :
    ‖s.esymm r‖ ≤ (s.map norm).esymm r := by
  have hnormprod : ∀ t : Multiset ℂ, ‖t.prod‖ = (t.map norm).prod := by
    intro t
    induction t using Multiset.induction_on with
    | empty => simp
    | @cons a t ih => simp [ih]
  unfold Multiset.esymm
  calc
    ‖((s.powersetCard r).map Multiset.prod).sum‖ ≤
        (((s.powersetCard r).map Multiset.prod).map norm).sum :=
      norm_multiset_sum_le _
    _ = ((((s.map norm).powersetCard r).map Multiset.prod).sum) := by
      rw [Multiset.powersetCard_map]
      simp only [Multiset.map_map]
      apply congrArg Multiset.sum
      apply Multiset.map_congr rfl
      intro t _ht
      exact hnormprod t

/-- Sum of all elementary symmetric functions equals the product of `1+x`. -/
theorem higham22_sum_esymm_eq_prod_one_add (s : Multiset ℝ) :
    (∑ r : Fin (s.card + 1), s.esymm (r : ℕ)) =
      (s.map fun x ↦ 1 + x).prod := by
  have h := congrArg (Polynomial.eval (1 : ℝ))
    (Multiset.prod_X_add_C_eq_sum_esymm s)
  simpa [Polynomial.eval_finset_sum, Polynomial.eval_multiset_prod,
    ← Fin.sum_univ_eq_sum_range,
    Multiset.map_map] using h.symm

/-- The synthetic quotient has degree below the matrix dimension. -/
theorem higham22_algorithm1SyntheticQuotient_natDegree_lt
    (alpha : Fin n → ℂ) (i : Fin n) :
    (higham22Algorithm1SyntheticQuotient alpha i).natDegree < n := by
  unfold higham22Algorithm1SyntheticQuotient
  rw [Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C (alpha i)),
    show (higham22Algorithm1MasterPolynomial alpha).natDegree = n by
      unfold higham22Algorithm1MasterPolynomial
      rw [Polynomial.natDegree_prod_of_monic]
      · simp
      · intro k _hk
        exact Polynomial.monic_X_sub_C (alpha k),
    Polynomial.natDegree_X_sub_C]
  exact Nat.sub_lt (Fin.pos i) Nat.zero_lt_one

/-- The Mahler measure of a synthetic quotient is the product occurring in
the lower estimate of equation (22.3). -/
theorem higham22_algorithm1SyntheticQuotient_mahlerMeasure
    (alpha : Fin n → ℂ) (i : Fin n) :
    (higham22Algorithm1SyntheticQuotient alpha i).mahlerMeasure =
      ∏ k ∈ Finset.univ.erase i, max 1 ‖alpha k‖ := by
  rw [higham22_algorithm1SyntheticQuotient_eq_prod_erase]
  induction Finset.univ.erase i using Finset.induction_on with
  | empty => simp
  | @insert k s hks ih =>
      simp only [Finset.prod_insert hks, Polynomial.mahlerMeasure_mul,
        Polynomial.mahlerMeasure_X_sub_C, ih]

/-- The sum of the coefficient norms of a synthetic quotient is bounded below
by its Mahler-measure product. -/
theorem higham22_algorithm1SyntheticQuotient_coeff_norm_sum_lower
    (alpha : Fin n → ℂ) (i : Fin n) :
    (∏ k ∈ Finset.univ.erase i, max 1 ‖alpha k‖) ≤
      ∑ j : Fin n, ‖(higham22Algorithm1SyntheticQuotient alpha i).coeff j‖ := by
  let q := higham22Algorithm1SyntheticQuotient alpha i
  have hdegree : q.degree < (n : WithBot ℕ) := by
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree
      (by exact_mod_cast higham22_algorithm1SyntheticQuotient_natDegree_lt alpha i)
  calc
    (∏ k ∈ Finset.univ.erase i, max 1 ‖alpha k‖) = q.mahlerMeasure := by
      symm
      exact higham22_algorithm1SyntheticQuotient_mahlerMeasure alpha i
    _ ≤ q.sum (fun _ a ↦ ‖a‖) := Polynomial.mahlerMeasure_le_sum_norm_coeff q
    _ = ∑ j : Fin n, ‖q.coeff j‖ := by
      symm
      exact Polynomial.sum_fin (fun (_ : ℕ) (a : ℂ) ↦ ‖a‖) (by simp) hdegree

/-- Vieta's formula bounds the coefficient one-norm of a synthetic quotient
by the product occurring in the upper estimate of equation (22.3). -/
theorem higham22_algorithm1SyntheticQuotient_coeff_norm_sum_upper
    (alpha : Fin n → ℂ) (i : Fin n) :
    (∑ j : Fin n, ‖(higham22Algorithm1SyntheticQuotient alpha i).coeff j‖) ≤
      ∏ k ∈ Finset.univ.erase i, (1 + ‖alpha k‖) := by
  let s := higham22NodesExcept alpha i
  have hpoint (j : Fin n) :
      ‖(higham22Algorithm1SyntheticQuotient alpha i).coeff j‖ ≤
        (s.map norm).esymm (n - 1 - (j : ℕ)) := by
    rw [higham22_algorithm1SyntheticQuotient_coeff]
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact higham22_norm_esymm_le s (n - 1 - (j : ℕ))
  calc
    (∑ j : Fin n, ‖(higham22Algorithm1SyntheticQuotient alpha i).coeff j‖) ≤
        ∑ j : Fin n, (s.map norm).esymm (n - 1 - (j : ℕ)) :=
      Finset.sum_le_sum fun j _hj ↦ hpoint j
    _ = ∑ r : Fin n, (s.map norm).esymm (r : ℕ) := by
      rw [← Equiv.sum_comp Fin.revPerm]
      apply Finset.sum_congr rfl
      intro j _hj
      simp [Fin.revPerm]
      congr 1
      omega
    _ = (s.map (fun z ↦ 1 + ‖z‖)).prod := by
      have h := higham22_sum_esymm_eq_prod_one_add (s.map norm)
      have hcard : (s.map norm).card + 1 = n := by
        have hn : 1 ≤ n := Nat.succ_le_iff.mpr (Fin.pos i)
        simp [s, higham22NodesExcept, Nat.sub_add_cancel hn]
      rw [hcard] at h
      simpa [Multiset.map_map] using h
    _ = ∏ k ∈ Finset.univ.erase i, (1 + ‖alpha k‖) := by
      simp only [s, higham22NodesExcept, Multiset.map_map]
      exact Finset.prod_map_val (Finset.univ.erase i) (fun k ↦ 1 + ‖alpha k‖)

/-- The rowwise lower product in Higham's equation (22.3). -/
noncomputable def higham22Eq22_3LowerRow
    (alpha : Fin n → ℂ) (i : Fin n) : ℝ :=
  (∏ k ∈ Finset.univ.erase i, max 1 ‖alpha k‖) /
    (∏ k ∈ Finset.univ.erase i, ‖alpha i - alpha k‖)

/-- The rowwise upper product in Higham's equation (22.3). -/
noncomputable def higham22Eq22_3UpperRow
    (alpha : Fin n → ℂ) (i : Fin n) : ℝ :=
  (∏ k ∈ Finset.univ.erase i, (1 + ‖alpha k‖)) /
    (∏ k ∈ Finset.univ.erase i, ‖alpha i - alpha k‖)

theorem higham22_eq22_3LowerRow_nonneg
    (alpha : Fin n → ℂ) (i : Fin n) :
    0 ≤ higham22Eq22_3LowerRow alpha i := by
  unfold higham22Eq22_3LowerRow
  positivity

theorem higham22_eq22_3UpperRow_nonneg
    (alpha : Fin n → ℂ) (i : Fin n) :
    0 ≤ higham22Eq22_3UpperRow alpha i := by
  unfold higham22Eq22_3UpperRow
  positivity

/-- The absolute row sum of the printed inverse is the coefficient one-norm
divided by the product of node separations. -/
theorem higham22_algorithm1Printed_row_norm_eq
    (alpha : Fin n → ℂ) (i : Fin n) :
    (∑ j : Fin n, ‖higham22Algorithm1Printed alpha i j‖) =
      (∑ j : Fin n,
          ‖(higham22Algorithm1SyntheticQuotient alpha i).coeff j‖) /
        (∏ k ∈ Finset.univ.erase i, ‖alpha i - alpha k‖) := by
  simp only [higham22Algorithm1Printed, norm_div]
  rw [Finset.sum_div, higham22_algorithm1Denominator_eq_prod]
  simp

/-- Pointwise lower half of equation (22.3). -/
theorem higham22_eq22_3_row_lower
    {alpha : Fin n → ℂ} (halpha : Function.Injective alpha) (i : Fin n) :
    higham22Eq22_3LowerRow alpha i ≤
      ∑ j : Fin n, ‖higham22Algorithm1Printed alpha i j‖ := by
  rw [higham22_algorithm1Printed_row_norm_eq]
  unfold higham22Eq22_3LowerRow
  have hden : 0 < ∏ k ∈ Finset.univ.erase i, ‖alpha i - alpha k‖ := by
    apply Finset.prod_pos
    intro k hk
    exact norm_pos_iff.mpr <| sub_ne_zero.mpr <|
      halpha.ne (Ne.symm (Finset.ne_of_mem_erase hk))
  exact (div_le_div_iff_of_pos_right hden).mpr
    (higham22_algorithm1SyntheticQuotient_coeff_norm_sum_lower alpha i)

/-- Pointwise upper half of equation (22.3). -/
theorem higham22_eq22_3_row_upper
    {alpha : Fin n → ℂ} (halpha : Function.Injective alpha) (i : Fin n) :
    (∑ j : Fin n, ‖higham22Algorithm1Printed alpha i j‖) ≤
      higham22Eq22_3UpperRow alpha i := by
  rw [higham22_algorithm1Printed_row_norm_eq]
  unfold higham22Eq22_3UpperRow
  have hden : 0 < ∏ k ∈ Finset.univ.erase i, ‖alpha i - alpha k‖ := by
    apply Finset.prod_pos
    intro k hk
    exact norm_pos_iff.mpr <| sub_ne_zero.mpr <|
      halpha.ne (Ne.symm (Finset.ne_of_mem_erase hk))
  exact (div_le_div_iff_of_pos_right hden).mpr
    (higham22_algorithm1SyntheticQuotient_coeff_norm_sum_upper alpha i)

/-- The maximum lower product in equation (22.3). -/
noncomputable def higham22Eq22_3LowerBound (alpha : Fin n → ℂ) : ℝ :=
  ((Finset.univ.sup
    (fun i : Fin n ↦ Real.toNNReal (higham22Eq22_3LowerRow alpha i)) : NNReal) : ℝ)

/-- The maximum upper product in equation (22.3). -/
noncomputable def higham22Eq22_3UpperBound (alpha : Fin n → ℂ) : ℝ :=
  ((Finset.univ.sup
    (fun i : Fin n ↦ Real.toNNReal (higham22Eq22_3UpperRow alpha i)) : NNReal) : ℝ)

/-- Higham, 2nd ed., equation (22.3): the exact two-sided infinity-norm
bound for the inverse produced by Algorithm 22.1. -/
theorem higham22_eq22_3
    {alpha : Fin n → ℂ} (halpha : Function.Injective alpha) :
    higham22Eq22_3LowerBound alpha ≤
        complexMatrixInfNorm (higham22Algorithm1Printed alpha) ∧
      complexMatrixInfNorm (higham22Algorithm1Printed alpha) ≤
        higham22Eq22_3UpperBound alpha := by
  constructor
  · unfold higham22Eq22_3LowerBound
    let f : Fin n → NNReal :=
      fun i ↦ Real.toNNReal (higham22Eq22_3LowerRow alpha i)
    have hsup : Finset.univ.sup f ≤
        Real.toNNReal (complexMatrixInfNorm (higham22Algorithm1Printed alpha)) := by
      apply Finset.sup_le
      intro i _hi
      exact Real.toNNReal_le_toNNReal <|
        (higham22_eq22_3_row_lower halpha i).trans
          (complexMatrixInfNorm_row_sum_le (higham22Algorithm1Printed alpha) i)
    have hreal : ((Finset.univ.sup f : NNReal) : ℝ) ≤
        ((Real.toNNReal
          (complexMatrixInfNorm (higham22Algorithm1Printed alpha)) : NNReal) : ℝ) := by
      exact_mod_cast hsup
    rw [Real.coe_toNNReal _
      (complexMatrixInfNorm_nonneg (higham22Algorithm1Printed alpha))] at hreal
    simpa [f] using hreal
  · unfold higham22Eq22_3UpperBound
    let f : Fin n → NNReal :=
      fun i ↦ Real.toNNReal (higham22Eq22_3UpperRow alpha i)
    apply complexMatrixInfNorm_le_of_row_sum_le (NNReal.coe_nonneg _)
    intro i
    refine (higham22_eq22_3_row_upper halpha i).trans ?_
    have hsup : f i ≤ Finset.univ.sup f :=
      Finset.le_sup (s := (Finset.univ : Finset (Fin n))) (f := f)
        (Finset.mem_univ i)
    have hreal : ((f i : NNReal) : ℝ) ≤
        ((Finset.univ.sup f : NNReal) : ℝ) := by
      exact_mod_cast hsup
    rw [Real.coe_toNNReal _ (higham22_eq22_3UpperRow_nonneg alpha i)] at hreal
    simpa [f] using hreal

/-- Root-of-unity nodes for Table 22.1 row (V7). -/
noncomputable def higham22RootUnityNodes (n : ℕ) (ζ : ℂ) : Fin n → ℂ :=
  fun j ↦ ζ ^ (j : ℕ)

/-- The root-of-unity Vandermonde is exactly the repository Fourier matrix. -/
theorem higham22_rootUnityVandermonde_eq_fourier (n : ℕ) (ζ : ℂ) :
    higham22Vandermonde (higham22RootUnityNodes n ζ) =
      complexFourierVandermondeMatrix n ζ := by
  ext i j
  change (ζ ^ (j : ℕ)) ^ (i : ℕ) = ζ ^ ((i : ℕ) * (j : ℕ))
  calc
    (ζ ^ (j : ℕ)) ^ (i : ℕ) = ζ ^ ((j : ℕ) * (i : ℕ)) := (pow_mul _ _ _).symm
    _ = ζ ^ ((i : ℕ) * (j : ℕ)) := by rw [Nat.mul_comm]

/-- Explicit inverse candidate for the root-of-unity Vandermonde. -/
noncomputable def higham22RootUnityInverse (n : ℕ) (ζ : ℂ) : CMatrix n n :=
  fun i j ↦ (n : ℂ)⁻¹ *
    complexMatrixAdjoint (complexFourierVandermondeMatrix n ζ) i j

/-- The explicit Fourier inverse is a left inverse. -/
theorem higham22_rootUnityInverse_mul_vandermonde
    {n : ℕ} (hn : 0 < n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    complexCMatrixAsMatrix (higham22RootUnityInverse n ζ) *
        higham22Vandermonde (higham22RootUnityNodes n ζ) = 1 := by
  rw [higham22_rootUnityVandermonde_eq_fourier]
  have hH := complexFourierVandermonde_isComplexHadamard_of_isPrimitiveRoot hn hζ
  have hgram := hH.conjTranspose_mul_self
  change (((n : ℂ)⁻¹) •
      (complexCMatrixAsMatrix (complexFourierVandermondeMatrix n ζ)).conjTranspose) *
        complexCMatrixAsMatrix (complexFourierVandermondeMatrix n ζ) = 1
  rw [Matrix.smul_mul, hgram, smul_smul]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  simp [hnC]

/-- Table 22.1 (V7): the Euclidean condition product of the roots-of-unity
Vandermonde and its explicit inverse is exactly one. -/
theorem higham22_table22_1_V7_kappa2
    {n : ℕ} (hn : 0 < n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    complexMatrixOp2 (higham22Vandermonde (higham22RootUnityNodes n ζ)) *
      complexMatrixOp2 (higham22RootUnityInverse n ζ) = 1 := by
  have hH := complexFourierVandermonde_isComplexHadamard_of_isPrimitiveRoot hn hζ
  rw [higham22_rootUnityVandermonde_eq_fourier,
    hH.complexMatrixOp2_eq_sqrt hn]
  have hinv : higham22RootUnityInverse n ζ =
      (((n : ℂ)⁻¹) •
        (complexMatrixAdjoint (complexFourierVandermondeMatrix n ζ) :
          Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
    rfl
  rw [hinv]
  rw [complexMatrixOp2_smul, complexMatrixOp2_adjoint_eq,
    hH.complexMatrixOp2_eq_sqrt hn]
  have hnorm : ‖((n : ℂ)⁻¹)‖ = ((n : ℝ)⁻¹) := by
    rw [norm_inv, Complex.norm_natCast]
  rw [hnorm]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hsqrt : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n)]
  field_simp [hnR]
  nlinarith

/-- Each row computed by Algorithm 22.1 is the corresponding cardinal
polynomial at every node. -/
theorem higham22_algorithm1Printed_cardinal
    {alpha : Fin n → ℂ} (halpha : Function.Injective alpha) (i j : Fin n) :
    ∑ k : Fin n,
        higham22Algorithm1Printed alpha i k * alpha j ^ (k : ℕ) =
      if j = i then 1 else 0 := by
  let q := higham22Algorithm1SyntheticQuotient alpha i
  let d := higham22Algorithm1Denominator alpha i
  have heval : q.eval (alpha j) = ∑ k : Fin n, q.coeff (k : ℕ) * alpha j ^ (k : ℕ) := by
    rw [Polynomial.eval_eq_sum_range'
      (higham22_algorithm1SyntheticQuotient_natDegree_lt alpha i),
      ← Fin.sum_univ_eq_sum_range]
  have hd : d ≠ 0 := higham22_algorithm1Denominator_ne_zero halpha i
  rw [show (∑ k : Fin n,
        higham22Algorithm1Printed alpha i k * alpha j ^ (k : ℕ)) = q.eval (alpha j) / d by
      rw [heval]
      simp_rw [higham22Algorithm1Printed, q, d, div_mul_eq_mul_div]
      simp [div_eq_mul_inv, Finset.sum_mul]]
  by_cases hji : j = i
  · subst j
    rw [if_pos rfl]
    change d / d = 1
    exact div_self hd
  · rw [if_neg hji, higham22_algorithm1SyntheticQuotient_eval_other alpha i j hji,
      zero_div]

/-- End-to-end exact correctness of the printed Algorithm 22.1 path. -/
theorem higham22_algorithm1Printed_leftInverse
    {alpha : Fin n → ℂ} (halpha : Function.Injective alpha) :
    higham22Algorithm1Printed alpha * higham22Vandermonde alpha = 1 := by
  ext i j
  simpa [Matrix.mul_apply, higham22Vandermonde, eq_comm] using
    higham22_algorithm1Printed_cardinal halpha i j

/-- Exact mathematical output specification of Algorithm 22.1.  The chapter's
two-stage floating-point implementation is deliberately not identified with
this noncomputable inverse. -/
noncomputable def higham22Algorithm1OutputSpec
    (alpha : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (higham22Vandermonde alpha)⁻¹

/-- The exact output specification associated with Algorithm 22.1 is a right
inverse for distinct nodes.  This does not model the printed execution path. -/
theorem higham22_algorithm1OutputSpec_rightInverse
    {alpha : Fin n → ℂ} (halpha : Function.Injective alpha) :
    higham22Vandermonde alpha * higham22Algorithm1OutputSpec alpha = 1 := by
  apply Matrix.mul_nonsing_inv
  rw [isUnit_iff_ne_zero]
  exact higham22_vandermonde_det_ne_zero_iff.mpr halpha

/-- The exact output specification associated with Algorithm 22.1 is also a
left inverse for distinct nodes.  This does not model the printed execution path. -/
theorem higham22_algorithm1OutputSpec_leftInverse
    {alpha : Fin n → ℂ} (halpha : Function.Injective alpha) :
    higham22Algorithm1OutputSpec alpha * higham22Vandermonde alpha = 1 := by
  apply Matrix.nonsing_inv_mul
  rw [isUnit_iff_ne_zero]
  exact higham22_vandermonde_det_ne_zero_iff.mpr halpha

/-- The printed Algorithm 22.1 path agrees with the inverse output
specification for distinct nodes. -/
theorem higham22_algorithm1Printed_eq_outputSpec
    {alpha : Fin n → ℂ} (halpha : Function.Injective alpha) :
    higham22Algorithm1Printed alpha = higham22Algorithm1OutputSpec alpha := by
  calc
    higham22Algorithm1Printed alpha =
        higham22Algorithm1Printed alpha * 1 := by simp
    _ = higham22Algorithm1Printed alpha *
        (higham22Vandermonde alpha * higham22Algorithm1OutputSpec alpha) := by
          rw [higham22_algorithm1OutputSpec_rightInverse halpha]
    _ = (higham22Algorithm1Printed alpha * higham22Vandermonde alpha) *
        higham22Algorithm1OutputSpec alpha := by rw [Matrix.mul_assoc]
    _ = higham22Algorithm1OutputSpec alpha := by
      rw [higham22_algorithm1Printed_leftInverse halpha, one_mul]

/-- Higham, 2nd ed., equation (22.4), p. 418: the symbolic `5 × 5`
confluent Vandermonde matrix with multiplicities three at `alpha₀` and two at
`alpha₁`.  Successive confluent columns are derivatives of the preceding
monomial column. -/
def higham22ConfluentExample (alpha₀ alpha₁ : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  ![![1, 0, 0, 1, 0],
    ![alpha₀, 1, 0, alpha₁, 1],
    ![alpha₀ ^ 2, 2 * alpha₀, 2, alpha₁ ^ 2, 2 * alpha₁],
    ![alpha₀ ^ 3, 3 * alpha₀ ^ 2, 6 * alpha₀,
      alpha₁ ^ 3, 3 * alpha₁ ^ 2],
    ![alpha₀ ^ 4, 4 * alpha₀ ^ 3, 12 * alpha₀ ^ 2,
      alpha₁ ^ 4, 4 * alpha₁ ^ 3]]

/-- Determinant of the symbolic confluent example (22.4). -/
theorem higham22_confluentExample_det (alpha₀ alpha₁ : ℂ) :
    (higham22ConfluentExample alpha₀ alpha₁).det =
      2 * (alpha₁ - alpha₀) ^ 6 := by
  simp [higham22ConfluentExample, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Fin.succAbove]
  ring

/-- The transpose in the prose after (22.4) is nonsingular exactly when its
two nonconfluent nodes are distinct. -/
theorem higham22_confluentExample_transpose_det_ne_zero_iff
    (alpha₀ alpha₁ : ℂ) :
    (higham22ConfluentExample alpha₀ alpha₁).transpose.det ≠ 0 ↔
      alpha₀ ≠ alpha₁ := by
  rw [Matrix.det_transpose, higham22_confluentExample_det]
  constructor
  · intro h hEq
    apply h
    simp [hEq]
  · intro h
    exact mul_ne_zero (by norm_num) (pow_ne_zero 6 (sub_ne_zero.mpr h.symm))

/-- General Hermite uniqueness behind the precise prose following (22.4).
If all derivatives below the assigned multiplicity vanish at distinct nodes,
a polynomial of degree below the total multiplicity is zero. -/
theorem higham22_confluent_polynomial_unique
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (multiplicity : ι → ℕ) (alpha : ι → ℂ)
    (halpha : Function.Injective alpha) (p : Polynomial ℂ)
    (hdegree : p.natDegree < ∑ i, multiplicity i)
    (hvanish : ∀ (i : ι) (r : ℕ), r < multiplicity i →
      (Polynomial.derivative^[r] p).eval (alpha i) = 0) :
    p = 0 := by
  by_contra hp
  have hmultiplicity : ∀ i,
      multiplicity i ≤ p.rootMultiplicity (alpha i) := by
    intro i
    cases hmi : multiplicity i with
    | zero => simp
    | succ m =>
        exact Nat.succ_le_iff.mpr
          (Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative
            (n := m) hp (fun r hr ↦ hvanish i r (by
              rw [hmi]
              exact Nat.lt_succ_of_le hr)))
  have hprod :
      (∏ i, (Polynomial.X - Polynomial.C (alpha i)) ^ multiplicity i) ∣ p := by
    apply Fintype.prod_dvd_of_coprime
    · intro i j hij
      exact (Polynomial.pairwise_coprime_X_sub_C halpha hij).pow
    · intro i
      exact (pow_dvd_pow _ (hmultiplicity i)).trans
        (p.pow_rootMultiplicity_dvd (alpha i))
  have hprodDegree :
      (∏ i, (Polynomial.X - Polynomial.C (alpha i)) ^ multiplicity i).natDegree =
        ∑ i, multiplicity i := by
    rw [Polynomial.natDegree_prod_of_monic]
    · simp
    · intro i _hi
      exact (Polynomial.monic_X_sub_C (alpha i)).pow (multiplicity i)
  have hle := Polynomial.natDegree_le_of_dvd hprod hp
  rw [hprodDegree] at hle
  exact (not_lt_of_ge hle) hdegree

/-- A confluent column records a node and a derivative order below that node's
multiplicity. -/
abbrev Higham22ConfluentSlot {ι : Type*} (multiplicity : ι → ℕ) :=
  Σ i, Fin (multiplicity i)

/-- Canonical finite enumeration of all confluent columns. -/
noncomputable def higham22ConfluentSlotEquivFin
    {ι : Type*} [Fintype ι] (multiplicity : ι → ℕ) :
    Higham22ConfluentSlot multiplicity ≃
      Fin (Fintype.card (Higham22ConfluentSlot multiplicity)) :=
  Fintype.equivFin _

/-- Polynomial of degree below `N` whose coefficient vector is `x`. -/
noncomputable def higham22CoefficientPolynomial {N : ℕ}
    (x : Fin N → ℂ) : Polynomial ℂ :=
  ((Polynomial.degreeLTEquiv ℂ N).symm x : Polynomial.degreeLT ℂ N).1

/-- Derivative evaluation of the coefficient polynomial is the corresponding
finite linear combination of differentiated monomials. -/
theorem higham22CoefficientPolynomial_iterateDerivative_eval {N : ℕ}
    (x : Fin N → ℂ) (r : ℕ) (a : ℂ) :
    (Polynomial.derivative^[r] (higham22CoefficientPolynomial x)).eval a =
      ∑ k : Fin N, x k *
        (Polynomial.derivative^[r] (Polynomial.X ^ (k : ℕ))).eval a := by
  unfold higham22CoefficientPolynomial Polynomial.degreeLTEquiv
  change (Polynomial.derivative^[r]
    (∑ k : Fin N, Polynomial.monomial (k : ℕ) (x k))).eval a = _
  rw [Polynomial.iterate_derivative_sum]
  simp_rw [← Polynomial.C_mul_X_pow_eq_monomial,
    Polynomial.iterate_derivative_C_mul, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_C]

/-- General confluent Vandermonde matrix from the prose following (22.4).
Rows are monomial degrees and columns are enumerated node/derivative slots. -/
noncomputable def higham22ConfluentVandermonde
    {ι : Type*} [Fintype ι] (multiplicity : ι → ℕ) (alpha : ι → ℂ) :
    Matrix
      (Fin (Fintype.card (Higham22ConfluentSlot multiplicity)))
      (Fin (Fintype.card (Higham22ConfluentSlot multiplicity))) ℂ :=
  fun degree column ↦
    let slot := (higham22ConfluentSlotEquivFin multiplicity).symm column
    (Polynomial.derivative^[slot.2.val]
      (Polynomial.X ^ degree.val)).eval (alpha slot.1)

/-- A coordinate of the transposed confluent matrix-vector product is exactly
the requested derivative evaluation of the coefficient polynomial. -/
theorem higham22_confluentVandermonde_transpose_mulVec_apply
    {ι : Type*} [Fintype ι] (multiplicity : ι → ℕ) (alpha : ι → ℂ)
    (x : Fin (Fintype.card (Higham22ConfluentSlot multiplicity)) → ℂ)
    (slot : Higham22ConfluentSlot multiplicity) :
    (higham22ConfluentVandermonde multiplicity alpha).transpose.mulVec x
        (higham22ConfluentSlotEquivFin multiplicity slot) =
      (Polynomial.derivative^[slot.2.val]
        (higham22CoefficientPolynomial x)).eval (alpha slot.1) := by
  rw [higham22CoefficientPolynomial_iterateDerivative_eval]
  simp only [higham22ConfluentVandermonde, Matrix.transpose_apply,
    Matrix.mulVec, dotProduct]
  rw [Equiv.symm_apply_apply]
  simp [mul_comm]

/-- General nonsingularity claim following (22.4): distinct nonconfluent nodes
make the transpose of the confluent Vandermonde matrix injective. -/
theorem higham22_confluentVandermonde_transpose_mulVec_injective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (multiplicity : ι → ℕ) (alpha : ι → ℂ)
    (halpha : Function.Injective alpha) :
    Function.Injective
      (higham22ConfluentVandermonde multiplicity alpha).transpose.mulVec := by
  intro x y hxy
  let z := x - y
  have hz :
      (higham22ConfluentVandermonde multiplicity alpha).transpose.mulVec z = 0 := by
    simp [z, Matrix.mulVec_sub, hxy]
  let p := higham22CoefficientPolynomial z
  have hpzero : p = 0 := by
    by_cases hp : p = 0
    · exact hp
    apply higham22_confluent_polynomial_unique multiplicity alpha halpha p
    · have hpDegree : p.natDegree <
          Fintype.card (Higham22ConfluentSlot multiplicity) := by
        apply (Polynomial.natDegree_lt_iff_degree_lt hp).mpr
        exact Polynomial.mem_degreeLT.mp
          (((Polynomial.degreeLTEquiv ℂ
            (Fintype.card (Higham22ConfluentSlot multiplicity))).symm z).property)
      simpa [Higham22ConfluentSlot] using hpDegree
    · intro i r hr
      let slot : Higham22ConfluentSlot multiplicity := ⟨i, ⟨r, hr⟩⟩
      have hcoord := congrFun hz (higham22ConfluentSlotEquivFin multiplicity slot)
      simpa [p, slot] using
        (higham22_confluentVandermonde_transpose_mulVec_apply
          multiplicity alpha z slot).symm.trans hcoord
  have hzzero : z = 0 := by
    have hsubtype :
        (Polynomial.degreeLTEquiv ℂ
          (Fintype.card (Higham22ConfluentSlot multiplicity))).symm z = 0 := by
      apply Subtype.ext
      exact hpzero
    have himage := congrArg
      (Polynomial.degreeLTEquiv ℂ
        (Fintype.card (Higham22ConfluentSlot multiplicity))) hsubtype
    simpa using himage
  exact sub_eq_zero.mp hzzero

/-- Determinantal form of the general nonsingularity prose following (22.4). -/
theorem higham22_confluentVandermonde_transpose_det_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (multiplicity : ι → ℕ) (alpha : ι → ℂ)
    (halpha : Function.Injective alpha) :
    (higham22ConfluentVandermonde multiplicity alpha).transpose.det ≠ 0 := by
  have hunit : IsUnit
      (higham22ConfluentVandermonde multiplicity alpha).transpose :=
    Matrix.mulVec_injective_iff_isUnit.mp
      (higham22_confluentVandermonde_transpose_mulVec_injective
        multiplicity alpha halpha)
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hunit)

end Vandermonde

section VandermondeLike

/-- Higham, 2nd ed., equation (22.5): repeated nodes occur in contiguous
blocks.  This is an explicit source assumption on the input ordering. -/
def Higham22ContiguousNodes {N : ℕ} (alpha : Fin N → ℂ) : Prop :=
  ∀ i j : Fin N, i < j → alpha i = alpha j →
    ∀ k : Fin N, i ≤ k → k ≤ j → alpha k = alpha i

/-- Direct source-facing form of equation (22.5). -/
theorem higham22_eq22_5 {N : ℕ} {alpha : Fin N → ℂ}
    (h : Higham22ContiguousNodes alpha)
    {i j k : Fin N} (hij : i < j) (hα : alpha i = alpha j)
    (hik : i ≤ k) (hkj : k ≤ j) :
    alpha k = alpha i :=
  h i j hij hα k hik hkj

/-- Higham's equation (22.8), the Newton divided-difference form. -/
noncomputable def higham22NewtonPolynomial {N : ℕ}
    (alpha c : Fin N → ℂ) : Polynomial ℂ :=
  ∑ i : Fin N, Polynomial.C (c i) *
    ∏ j ∈ Finset.Iio i, (Polynomial.X - Polynomial.C (alpha j))

/-- Equation (22.8) evaluated at an arbitrary point. -/
theorem higham22_eq22_8 {N : ℕ} (alpha c : Fin N → ℂ) (x : ℂ) :
    (higham22NewtonPolynomial alpha c).eval x =
      ∑ i : Fin N, c i * ∏ j ∈ Finset.Iio i, (x - alpha j) := by
  simp [higham22NewtonPolynomial, Polynomial.eval_finset_sum,
    Polynomial.eval_prod]

/-- One scalar branch of the confluent divided-difference recurrence (22.9).
The derivative datum is already the derivative of the required order. -/
noncomputable def higham22DividedDifferenceStep
    (left right alphaLeft alphaRight derivativeDatum : ℂ) (order : ℕ) : ℂ :=
  if alphaRight = alphaLeft then
    derivativeDatum / (Nat.factorial order : ℂ)
  else
    (right - left) / (alphaRight - alphaLeft)

/-- Distinct-node branch of equation (22.9). -/
theorem higham22_eq22_9_distinct
    {left right alphaLeft alphaRight derivativeDatum : ℂ} {order : ℕ}
    (h : alphaRight ≠ alphaLeft) :
    higham22DividedDifferenceStep left right alphaLeft alphaRight
        derivativeDatum order =
      (right - left) / (alphaRight - alphaLeft) := by
  simp [higham22DividedDifferenceStep, h]

/-- Confluent derivative branch of equation (22.9). -/
theorem higham22_eq22_9_equal
    (left right alpha derivativeDatum : ℂ) (order : ℕ) :
    higham22DividedDifferenceStep left right alpha alpha derivativeDatum order =
      derivativeDatum / (Nat.factorial order : ℂ) := by
  simp [higham22DividedDifferenceStep]

/-- Polynomial version of the nested multiplication in (22.10)--(22.11).
The list is in source order `(alpha_k,c_k),...,(alpha_n,c_n)`. -/
noncomputable def higham22NewtonPolynomialNest : List (ℂ × ℂ) → Polynomial ℂ
  | [] => 0
  | (alpha, c) :: rest =>
      Polynomial.C c +
        (Polynomial.X - Polynomial.C alpha) * higham22NewtonPolynomialNest rest

/-- Equation (22.10): the terminal nested polynomial is constant. -/
@[simp]
theorem higham22_eq22_10_polynomial (alpha c : ℂ) :
    higham22NewtonPolynomialNest [(alpha, c)] = Polynomial.C c := by
  simp [higham22NewtonPolynomialNest]

/-- Equation (22.11), as an equality of polynomials. -/
@[simp]
theorem higham22_eq22_11_polynomial (alpha c : ℂ) (rest : List (ℂ × ℂ)) :
    higham22NewtonPolynomialNest ((alpha, c) :: rest) =
      (Polynomial.X - Polynomial.C alpha) *
          higham22NewtonPolynomialNest rest + Polynomial.C c := by
  simp [higham22NewtonPolynomialNest, add_comm]

/-- Source-facing basis expansion used in equation (22.12). -/
noncomputable def higham22BasisExpansion {N : ℕ}
    (p : Fin N → Polynomial ℂ) (a : Fin N → ℂ) : Polynomial ℂ :=
  ∑ j : Fin N, Polynomial.C (a j) * p j

/-- Equation (22.12) evaluated at a point. -/
theorem higham22_eq22_12_eval {N : ℕ}
    (p : Fin N → Polynomial ℂ) (a : Fin N → ℂ) (x : ℂ) :
    (higham22BasisExpansion p a).eval x =
      ∑ j : Fin N, a j * (p j).eval x := by
  simp [higham22BasisExpansion, Polynomial.eval_finset_sum]

/-- Equation (22.6): a polynomial family satisfying Higham's three-term
recurrence.  Natural-number indices keep the mathematical recurrence separate
from a later finite implementation. -/
def Higham22ThreeTermRecurrence
    (theta beta gamma : ℕ → ℂ) (p : ℕ → Polynomial ℂ) : Prop :=
  p 0 = 1 ∧
    p 1 = Polynomial.C (theta 0) * (Polynomial.X - Polynomial.C (beta 0)) ∧
    ∀ j : ℕ,
      p (j + 2) =
        Polynomial.C (theta (j + 1)) *
            (Polynomial.X - Polynomial.C (beta (j + 1))) * p (j + 1) -
          Polynomial.C (gamma (j + 1)) * p j

/-- The polynomial family generated by a row of Higham's Table 22.2.  This is
the recurrence (22.6) as an executable exact-arithmetic definition. -/
noncomputable def higham22PolynomialSequence
    (theta beta gamma : ℕ → ℂ) : ℕ → Polynomial ℂ
  | 0 => 1
  | 1 => Polynomial.C (theta 0) *
      (Polynomial.X - Polynomial.C (beta 0))
  | j + 2 =>
      Polynomial.C (theta (j + 1)) *
          (Polynomial.X - Polynomial.C (beta (j + 1))) *
        higham22PolynomialSequence theta beta gamma (j + 1) -
      Polynomial.C (gamma (j + 1)) *
        higham22PolynomialSequence theta beta gamma j

/-- Every generated family satisfies the exact three-term recurrence (22.6). -/
theorem higham22PolynomialSequence_recurrence
    (theta beta gamma : ℕ → ℂ) :
    Higham22ThreeTermRecurrence theta beta gamma
      (higham22PolynomialSequence theta beta gamma) := by
  refine ⟨rfl, rfl, ?_⟩
  intro j
  rfl

/-- Table 22.2, monomial row. -/
def higham22MonomialTheta (_j : ℕ) : ℂ := 1
def higham22MonomialBeta (_j : ℕ) : ℂ := 0
def higham22MonomialGamma (_j : ℕ) : ℂ := 0

/-- Table 22.2, Chebyshev row, including the exceptional `theta₀ = 1`. -/
def higham22ChebyshevTheta : ℕ → ℂ
  | 0 => 1
  | _j + 1 => 2
def higham22ChebyshevBeta (_j : ℕ) : ℂ := 0
def higham22ChebyshevGamma : ℕ → ℂ
  | 0 => 0
  | _j + 1 => 1

/-- Table 22.2, Legendre row. -/
noncomputable def higham22LegendreTheta (j : ℕ) : ℂ :=
  ((2 : ℂ) * j + 1) / (j + 1)
def higham22LegendreBeta (_j : ℕ) : ℂ := 0
noncomputable def higham22LegendreGamma (j : ℕ) : ℂ :=
  (j : ℂ) / (j + 1)

/-- Table 22.2, physicists' Hermite row. -/
def higham22HermiteTheta (_j : ℕ) : ℂ := 2
def higham22HermiteBeta (_j : ℕ) : ℂ := 0
def higham22HermiteGamma (j : ℕ) : ℂ := 2 * j

/-- Table 22.2, Laguerre row. -/
noncomputable def higham22LaguerreTheta (j : ℕ) : ℂ :=
  -1 / (j + 1)
def higham22LaguerreBeta (j : ℕ) : ℂ :=
  2 * j + 1
noncomputable def higham22LaguerreGamma (j : ℕ) : ℂ :=
  (j : ℂ) / (j + 1)

/-- The monomial parameters in Table 22.2 satisfy (22.6). -/
theorem higham22_table22_2_monomial :
    Higham22ThreeTermRecurrence
      higham22MonomialTheta higham22MonomialBeta higham22MonomialGamma
      (higham22PolynomialSequence
        higham22MonomialTheta higham22MonomialBeta higham22MonomialGamma) :=
  higham22PolynomialSequence_recurrence _ _ _

/-- The Chebyshev parameters in Table 22.2 satisfy (22.6). -/
theorem higham22_table22_2_chebyshev :
    Higham22ThreeTermRecurrence
      higham22ChebyshevTheta higham22ChebyshevBeta higham22ChebyshevGamma
      (higham22PolynomialSequence
        higham22ChebyshevTheta higham22ChebyshevBeta higham22ChebyshevGamma) :=
  higham22PolynomialSequence_recurrence _ _ _

/-- The Legendre parameters in Table 22.2 satisfy (22.6). -/
theorem higham22_table22_2_legendre :
    Higham22ThreeTermRecurrence
      higham22LegendreTheta higham22LegendreBeta higham22LegendreGamma
      (higham22PolynomialSequence
        higham22LegendreTheta higham22LegendreBeta higham22LegendreGamma) :=
  higham22PolynomialSequence_recurrence _ _ _

/-- The Hermite parameters in Table 22.2 satisfy (22.6). -/
theorem higham22_table22_2_hermite :
    Higham22ThreeTermRecurrence
      higham22HermiteTheta higham22HermiteBeta higham22HermiteGamma
      (higham22PolynomialSequence
        higham22HermiteTheta higham22HermiteBeta higham22HermiteGamma) :=
  higham22PolynomialSequence_recurrence _ _ _

/-- The Laguerre parameters in Table 22.2 satisfy (22.6). -/
theorem higham22_table22_2_laguerre :
    Higham22ThreeTermRecurrence
      higham22LaguerreTheta higham22LaguerreBeta higham22LaguerreGamma
      (higham22PolynomialSequence
        higham22LaguerreTheta higham22LaguerreBeta higham22LaguerreGamma) :=
  higham22PolynomialSequence_recurrence _ _ _

/-- A recurrence whose parameters preserve the value one has `p_j(1)=1` for
all `j`.  This is the normalization note attached to the Legendre row of
Table 22.2. -/
theorem higham22PolynomialSequence_eval_one_of_preserved
    (theta beta gamma : ℕ → ℂ)
    (hzero : theta 0 * (1 - beta 0) = 1)
    (hstep : ∀ j : ℕ,
      theta (j + 1) * (1 - beta (j + 1)) - gamma (j + 1) = 1) :
    ∀ j : ℕ,
      (higham22PolynomialSequence theta beta gamma j).eval 1 = 1 := by
  intro j
  induction j using Nat.twoStepInduction with
  | zero => simp [higham22PolynomialSequence]
  | one => simpa [higham22PolynomialSequence] using hzero
  | more j hj hj1 =>
      simp only [higham22PolynomialSequence, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      rw [hj1, hj]
      simpa using hstep j

/-- Legendre normalization from Table 22.2: `p_j(1)=1`. -/
theorem higham22_table22_2_legendre_eval_one (j : ℕ) :
    (higham22PolynomialSequence
      higham22LegendreTheta higham22LegendreBeta higham22LegendreGamma j).eval 1 = 1 := by
  apply higham22PolynomialSequence_eval_one_of_preserved
  · simp [higham22LegendreTheta, higham22LegendreBeta]
  · intro k
    have hk2 : (2 + (k : ℂ)) ≠ 0 := by
      rw [show (2 : ℂ) + (k : ℂ) = ((k + 2 : ℕ) : ℂ) by
        norm_num
        ring]
      exact_mod_cast Nat.succ_ne_zero (k + 1)
    norm_num [higham22LegendreTheta, higham22LegendreBeta,
      higham22LegendreGamma] at *
    have hden : (k : ℂ) + 1 + 1 ≠ 0 := by
      intro h
      apply hk2
      calc
        (2 : ℂ) + k = k + 1 + 1 := by ring
        _ = 0 := h
    field_simp [hden]
    ring

/-- The nonzero-`theta` side condition following (22.6) holds for every row
of Table 22.2. -/
theorem higham22_table22_2_theta_ne_zero :
    (∀ j, higham22MonomialTheta j ≠ 0) ∧
    (∀ j, higham22ChebyshevTheta j ≠ 0) ∧
    (∀ j, higham22LegendreTheta j ≠ 0) ∧
    (∀ j, higham22HermiteTheta j ≠ 0) ∧
    (∀ j, higham22LaguerreTheta j ≠ 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    norm_num [higham22MonomialTheta]
  · intro j
    cases j <;> norm_num [higham22ChebyshevTheta]
  · intro j
    unfold higham22LegendreTheta
    apply div_ne_zero
    · exact_mod_cast Nat.succ_ne_zero (2 * j)
    · exact_mod_cast Nat.succ_ne_zero j
  · intro j
    norm_num [higham22HermiteTheta]
  · intro j
    unfold higham22LaguerreTheta
    apply div_ne_zero
    · norm_num
    · exact_mod_cast Nat.succ_ne_zero j

/-- Polynomial state underlying the reverse Clenshaw loop.  The two returned
polynomials are the consecutive states `b_j,b_{j+1}`. -/
noncomputable def higham22ClenshawPolynomialAux
    (theta beta gamma : ℕ → ℂ) : ℕ → List ℂ → Polynomial ℂ × Polynomial ℂ
  | _j, [] => (0, 0)
  | j, a :: as =>
      let next := higham22ClenshawPolynomialAux theta beta gamma (j + 1) as
      (Polynomial.C a +
          Polynomial.C (theta j) * (Polynomial.X - Polynomial.C (beta j)) * next.1 -
          Polynomial.C (gamma (j + 1)) * next.2,
        next.1)

/-- Exact polynomial computed by the scalar part of Algorithm 22.8. -/
noncomputable def higham22ClenshawPolynomial
    (theta beta gamma : ℕ → ℂ) (a : List ℂ) : Polynomial ℂ :=
  (higham22ClenshawPolynomialAux theta beta gamma 0 a).1

/-- The normalized derivative state of the printed extended Clenshaw loop.
Index `i` stores the `i`th derivative divided by `i!`; the final scaling in
Algorithm 22.8 restores ordinary derivatives. -/
noncomputable def higham22ClenshawJetAux
    (theta beta gamma : ℕ → ℂ) (x : ℂ) :
    ℕ → List ℂ → (ℕ → ℂ) × (ℕ → ℂ)
  | _j, [] => (0, 0)
  | j, a :: as =>
      let next := higham22ClenshawJetAux theta beta gamma x (j + 1) as
      (fun i ↦
        theta j * ((x - beta j) * next.1 i +
          if i = 0 then 0 else next.1 (i - 1)) -
        gamma (j + 1) * next.2 i + if i = 0 then a else 0,
       next.1)

/-- The actual outputs of Algorithm 22.8 after its final factorial scaling. -/
noncomputable def higham22Algorithm22_8
    (theta beta gamma : ℕ → ℂ) (a : List ℂ) (x : ℂ) (i : ℕ) : ℂ :=
  (Nat.factorial i : ℂ) *
    (higham22ClenshawJetAux theta beta gamma x 0 a).1 i

/-- Multiplication by a linear factor shifts Taylor coefficients exactly as
used by the inner derivative loop of Algorithm 22.8. -/
theorem higham22_taylor_linear_mul_coeff
    (x beta : ℂ) (q : Polynomial ℂ) (i : ℕ) :
    (Polynomial.taylor x ((Polynomial.X - Polynomial.C beta) * q)).coeff i =
      (x - beta) * (Polynomial.taylor x q).coeff i +
        if i = 0 then 0 else (Polynomial.taylor x q).coeff (i - 1) := by
  rcases i with _ | i
  · simp [Polynomial.taylor_mul]
  · rw [Polynomial.taylor_mul]
    rw [show Polynomial.taylor x (Polynomial.X - Polynomial.C beta) =
        Polynomial.X + Polynomial.C (x - beta) by
      simp only [map_sub, Polynomial.taylor_X, Polynomial.taylor_C]
      ring]
    rw [add_mul]
    simp [Polynomial.coeff_add, Polynomial.coeff_X_mul]
    rw [sub_mul, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
    ring

/-- The numerical jet loop is the Taylor-coefficient loop of the polynomial
Clenshaw state. -/
theorem higham22_clenshawJetAux_eq_taylor_coeff
    (theta beta gamma : ℕ → ℂ) (x : ℂ) (j : ℕ) (a : List ℂ) (i : ℕ) :
    (higham22ClenshawJetAux theta beta gamma x j a).1 i =
        (Polynomial.taylor x
          (higham22ClenshawPolynomialAux theta beta gamma j a).1).coeff i ∧
      (higham22ClenshawJetAux theta beta gamma x j a).2 i =
        (Polynomial.taylor x
          (higham22ClenshawPolynomialAux theta beta gamma j a).2).coeff i := by
  induction a generalizing j i with
  | nil => simp [higham22ClenshawJetAux, higham22ClenshawPolynomialAux]
  | cons a as ih =>
      have hnext := ih (j + 1) i
      constructor
      · simp only [higham22ClenshawJetAux, higham22ClenshawPolynomialAux]
        rw [map_sub, map_add]
        simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.taylor_C]
        rw [show Polynomial.taylor x
              (Polynomial.C (theta j) * (Polynomial.X - Polynomial.C (beta j)) *
                (higham22ClenshawPolynomialAux theta beta gamma (j + 1) as).1) =
              Polynomial.C (theta j) * Polynomial.taylor x
                ((Polynomial.X - Polynomial.C (beta j)) *
                  (higham22ClenshawPolynomialAux theta beta gamma (j + 1) as).1) by
              simp [Polynomial.taylor_mul]
              ring_nf]
        rw [show Polynomial.taylor x
              (Polynomial.C (gamma (j + 1)) *
                (higham22ClenshawPolynomialAux theta beta gamma (j + 1) as).2) =
              Polynomial.C (gamma (j + 1)) * Polynomial.taylor x
                (higham22ClenshawPolynomialAux theta beta gamma (j + 1) as).2 by
              simp [Polynomial.taylor_mul]]
        simp only [Polynomial.coeff_C_mul]
        rw [higham22_taylor_linear_mul_coeff]
        by_cases hi : i = 0
        · subst i
          rw [← hnext.1, ← hnext.2]
          simp
          ring
        · have hprev := ih (j + 1) (i - 1)
          rw [← hnext.1, ← hnext.2, ← hprev.1]
          simp [Polynomial.coeff_C, hi]
      · simpa [higham22ClenshawJetAux, higham22ClenshawPolynomialAux] using hnext.1

/-- A list-indexed polynomial expansion in the recurrence basis. -/
noncomputable def higham22IndexedBasisSum
    (p : ℕ → Polynomial ℂ) : ℕ → List ℂ → Polynomial ℂ
  | _j, [] => 0
  | j, a :: as => Polynomial.C a * p j + higham22IndexedBasisSum p (j + 1) as

/-- General Clenshaw invariant for a tail beginning at a positive index. -/
theorem higham22_clenshawPolynomialAux_invariant
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (j : ℕ) (hj : 1 ≤ j) (a : List ℂ) :
    p j * (higham22ClenshawPolynomialAux theta beta gamma j a).1 -
        Polynomial.C (gamma j) * p (j - 1) *
          (higham22ClenshawPolynomialAux theta beta gamma j a).2 =
      higham22IndexedBasisSum p j a := by
  induction a generalizing j with
  | nil => simp [higham22ClenshawPolynomialAux, higham22IndexedBasisSum]
  | cons a as ih =>
      have hrec : p (j + 1) =
          Polynomial.C (theta j) *
              (Polynomial.X - Polynomial.C (beta j)) * p j -
            Polynomial.C (gamma j) * p (j - 1) := by
        cases j with
        | zero => omega
        | succ j =>
            simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hp.2.2 j
      have htail := ih (j + 1) (by omega)
      have htail' :
          p (j + 1) *
                (higham22ClenshawPolynomialAux theta beta gamma (j + 1) as).1 -
              Polynomial.C (gamma (j + 1)) * p j *
                (higham22ClenshawPolynomialAux theta beta gamma (j + 1) as).2 =
            higham22IndexedBasisSum p (j + 1) as := by
        simpa using htail
      simp only [higham22ClenshawPolynomialAux, higham22IndexedBasisSum]
      calc
        p j *
              (Polynomial.C a +
                Polynomial.C (theta j) *
                    (Polynomial.X - Polynomial.C (beta j)) *
                      (higham22ClenshawPolynomialAux theta beta gamma (j + 1) as).1 -
                Polynomial.C (gamma (j + 1)) *
                  (higham22ClenshawPolynomialAux theta beta gamma (j + 1) as).2) -
            Polynomial.C (gamma j) * p (j - 1) *
              (higham22ClenshawPolynomialAux theta beta gamma (j + 1) as).1 =
          Polynomial.C a * p j +
            (Polynomial.C (theta j) *
                  (Polynomial.X - Polynomial.C (beta j)) * p j -
                Polynomial.C (gamma j) * p (j - 1)) *
              (higham22ClenshawPolynomialAux theta beta gamma (j + 1) as).1 -
            Polynomial.C (gamma (j + 1)) * p j *
              (higham22ClenshawPolynomialAux theta beta gamma (j + 1) as).2 := by
            ring
        _ = Polynomial.C a * p j +
              (p (j + 1) *
                  (higham22ClenshawPolynomialAux theta beta gamma (j + 1) as).1 -
                Polynomial.C (gamma (j + 1)) * p j *
                  (higham22ClenshawPolynomialAux theta beta gamma (j + 1) as).2) := by
            rw [hrec]
            ring
        _ = Polynomial.C a * p j + higham22IndexedBasisSum p (j + 1) as := by
            rw [htail']

/-- The scalar reverse loop computes the represented basis polynomial. -/
theorem higham22_clenshawPolynomial_correct
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p) (a : List ℂ) :
    higham22ClenshawPolynomial theta beta gamma a =
      higham22IndexedBasisSum p 0 a := by
  cases a with
  | nil => simp [higham22ClenshawPolynomial, higham22ClenshawPolynomialAux,
      higham22IndexedBasisSum]
  | cons a as =>
      have htail := higham22_clenshawPolynomialAux_invariant hp 1 (by omega) as
      have htail' :
          (Polynomial.C (theta 0) *
                (Polynomial.X - Polynomial.C (beta 0))) *
              (higham22ClenshawPolynomialAux theta beta gamma 1 as).1 -
            Polynomial.C (gamma 1) *
              (higham22ClenshawPolynomialAux theta beta gamma 1 as).2 =
          higham22IndexedBasisSum p 1 as := by
        simpa [hp.1, hp.2.1] using htail
      simp only [higham22ClenshawPolynomial, higham22ClenshawPolynomialAux,
        higham22IndexedBasisSum]
      rw [hp.1]
      rw [← htail']
      ring

/-- End-to-end exact correctness of the printed extended Clenshaw recurrence:
its `i`th output is the ordinary `i`th derivative of the represented
polynomial at `x`. -/
theorem higham22_algorithm22_8_correct
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (a : List ℂ) (x : ℂ) (i : ℕ) :
    higham22Algorithm22_8 theta beta gamma a x i =
      ((Polynomial.derivative^[i]) (higham22IndexedBasisSum p 0 a)).eval x := by
  unfold higham22Algorithm22_8
  rw [(higham22_clenshawJetAux_eq_taylor_coeff theta beta gamma x 0 a i).1]
  rw [Polynomial.taylor_coeff]
  change (Nat.factorial i : ℂ) *
      (Polynomial.hasseDeriv i
        (higham22ClenshawPolynomial theta beta gamma a)).eval x = _
  rw [higham22_clenshawPolynomial_correct hp]
  have hfun := Polynomial.factorial_smul_hasseDeriv (R := ℂ) (k := i)
  have hpoly := congrFun hfun (higham22IndexedBasisSum p 0 a)
  have heval := congrArg (Polynomial.eval x) hpoly
  simpa [nsmul_eq_mul] using heval

/-- Synthesis of a finitely supported coefficient vector in the polynomial
basis `p`. -/
noncomputable def higham22BasisSynthesis (p : ℕ → Polynomial ℂ) :
    (ℕ →₀ ℂ) →ₗ[ℂ] Polynomial ℂ :=
  (Finsupp.lsum ℂ) fun j ↦
    LinearMap.toSpanSingleton ℂ (Polynomial ℂ) (p j)

/-- Sparse coefficient row for multiplication by `x-alpha`, obtained by
solving the three-term recurrence for `x p_j`. -/
noncomputable def higham22BasisMultiplyRow
    (theta beta gamma : ℕ → ℂ) (alpha : ℂ) (j : ℕ) : ℕ →₀ ℂ :=
  Finsupp.single (j + 1) (theta j)⁻¹ +
    Finsupp.single j (beta j - alpha) +
      if j = 0 then 0 else Finsupp.single (j - 1) (gamma j / theta j)

/-- Linear sparse update used in equations (22.13)--(22.14). -/
noncomputable def higham22BasisMultiply
    (theta beta gamma : ℕ → ℂ) (alpha : ℂ) :
    (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  (Finsupp.lsum ℂ) fun j ↦
    LinearMap.toSpanSingleton ℂ (ℕ →₀ ℂ)
      (higham22BasisMultiplyRow theta beta gamma alpha j)

/-- One executable Stage-II coefficient step: form `(x-alpha)q+c` from the
coefficient vector of `q`. -/
noncomputable def higham22StageIICoefficientStep
    (theta beta gamma : ℕ → ℂ) (alpha c : ℂ) (b : ℕ →₀ ℂ) : ℕ →₀ ℂ :=
  Finsupp.single 0 c + higham22BasisMultiply theta beta gamma alpha b

/-- The sparse multiplication row synthesizes to `(x-alpha)p_j`. -/
theorem higham22_basisMultiplyRow_synthesis
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (htheta : ∀ j, theta j ≠ 0) (alpha : ℂ) (j : ℕ) :
    higham22BasisSynthesis p
        (higham22BasisMultiplyRow theta beta gamma alpha j) =
      (Polynomial.X - Polynomial.C alpha) * p j := by
  cases j with
  | zero =>
      simp only [higham22BasisMultiplyRow, if_pos, add_zero]
      rw [map_add]
      simp only [higham22BasisSynthesis, Finsupp.lsum_single,
        LinearMap.toSpanSingleton_apply]
      rw [hp.1, hp.2.1]
      simp only [Polynomial.smul_eq_C_mul]
      have hC : Polynomial.C (theta 0)⁻¹ * Polynomial.C (theta 0) = 1 := by
        rw [← Polynomial.C_mul]
        simp [htheta 0]
      calc
        Polynomial.C (theta 0)⁻¹ *
              (Polynomial.C (theta 0) *
                (Polynomial.X - Polynomial.C (beta 0))) +
            Polynomial.C (beta 0 - alpha) * 1 =
          (Polynomial.C (theta 0)⁻¹ * Polynomial.C (theta 0)) *
              (Polynomial.X - Polynomial.C (beta 0)) +
            Polynomial.C (beta 0 - alpha) := by ring
        _ = Polynomial.X - Polynomial.C alpha := by rw [hC]; simp
        _ = (Polynomial.X - Polynomial.C alpha) * 1 := by ring
  | succ j =>
      have hrec := hp.2.2 j
      simp only [higham22BasisMultiplyRow, Nat.succ_ne_zero, if_false]
      rw [map_add, map_add]
      simp only [higham22BasisSynthesis, Finsupp.lsum_single,
        LinearMap.toSpanSingleton_apply]
      rw [hrec]
      simp only [Polynomial.smul_eq_C_mul]
      have hjsub : j + 1 - 1 = j := by omega
      rw [hjsub]
      have hC : Polynomial.C (theta (j + 1))⁻¹ *
          Polynomial.C (theta (j + 1)) = 1 := by
        rw [← Polynomial.C_mul]
        simp [htheta (j + 1)]
      have hdiv : Polynomial.C (gamma (j + 1) / theta (j + 1)) =
          Polynomial.C (gamma (j + 1)) * Polynomial.C (theta (j + 1))⁻¹ := by
        rw [← Polynomial.C_mul]
        rfl
      rw [hdiv]
      calc
        Polynomial.C (theta (j + 1))⁻¹ *
                (Polynomial.C (theta (j + 1)) *
                      (Polynomial.X - Polynomial.C (beta (j + 1))) * p (j + 1) -
                  Polynomial.C (gamma (j + 1)) * p j) +
              Polynomial.C (beta (j + 1) - alpha) * p (j + 1) +
            Polynomial.C (gamma (j + 1)) *
                Polynomial.C (theta (j + 1))⁻¹ * p j =
          (Polynomial.C (theta (j + 1))⁻¹ *
              Polynomial.C (theta (j + 1))) *
                (Polynomial.X - Polynomial.C (beta (j + 1))) * p (j + 1) +
            Polynomial.C (beta (j + 1) - alpha) * p (j + 1) := by ring
        _ = (Polynomial.X - Polynomial.C alpha) * p (j + 1) := by
          rw [hC]
          simp
          ring

/-- Linear multiplication update is correct after basis synthesis. -/
theorem higham22_basisMultiply_synthesis
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (htheta : ∀ j, theta j ≠ 0) (alpha : ℂ) (b : ℕ →₀ ℂ) :
    higham22BasisSynthesis p (higham22BasisMultiply theta beta gamma alpha b) =
      (Polynomial.X - Polynomial.C alpha) * higham22BasisSynthesis p b := by
  induction b using Finsupp.induction with
  | zero => simp
  | single_add j a b hja ha0 ih =>
      rw [map_add, map_add, map_add, ih]
      have hsingle :
          higham22BasisMultiply theta beta gamma alpha (Finsupp.single j a) =
            a • higham22BasisMultiplyRow theta beta gamma alpha j := by
        simp [higham22BasisMultiply]
      rw [hsingle, map_smul, higham22_basisMultiplyRow_synthesis hp htheta]
      have hsynth :
          higham22BasisSynthesis p (Finsupp.single j a) = a • p j := by
        simp [higham22BasisSynthesis]
      rw [hsynth]
      simp [Polynomial.smul_eq_C_mul, mul_add]
      ring

/-- Equations (22.13)--(22.14), compressed into their common exact sparse
coefficient update. -/
theorem higham22_stageIICoefficientStep_correct
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (htheta : ∀ j, theta j ≠ 0) (alpha c : ℂ) (b : ℕ →₀ ℂ) :
    higham22BasisSynthesis p
        (higham22StageIICoefficientStep theta beta gamma alpha c b) =
      (Polynomial.X - Polynomial.C alpha) * higham22BasisSynthesis p b +
        Polynomial.C c := by
  rw [higham22StageIICoefficientStep, map_add,
    higham22_basisMultiply_synthesis hp htheta]
  simp [higham22BasisSynthesis, hp.1, Polynomial.smul_eq_C_mul, add_comm]

/-- Executable exact Stage II of Algorithm 22.2, processing Newton data in
source order by the backward nesting recurrence. -/
noncomputable def higham22Algorithm22_2StageII
    (theta beta gamma : ℕ → ℂ) : List (ℂ × ℂ) → (ℕ →₀ ℂ)
  | [] => 0
  | (alpha, c) :: rest =>
      higham22StageIICoefficientStep theta beta gamma alpha c
        (higham22Algorithm22_2StageII theta beta gamma rest)

/-- End-to-end Stage-II invariant: the computed sparse coefficients synthesize
to the nested Newton polynomial. -/
theorem higham22_algorithm22_2StageII_correct
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (htheta : ∀ j, theta j ≠ 0) (data : List (ℂ × ℂ)) :
    higham22BasisSynthesis p
        (higham22Algorithm22_2StageII theta beta gamma data) =
      higham22NewtonPolynomialNest data := by
  induction data with
  | nil => simp [higham22Algorithm22_2StageII, higham22NewtonPolynomialNest]
  | cons ac rest ih =>
      rcases ac with ⟨alpha, c⟩
      rw [higham22Algorithm22_2StageII,
        higham22_stageIICoefficientStep_correct hp htheta, ih]
      simp [higham22NewtonPolynomialNest, add_comm]

/-- Index of the previous saved Stage-I value (`clast`) before row `j` is
processed in Algorithm 22.2. -/
noncomputable def higham22StageILastSaved (alpha : ℕ → ℂ) (k : ℕ) : ℕ → ℕ
  | 0 => k
  | j + 1 =>
      if j + 1 ≤ k then k
      else if alpha (j + 1) = alpha (j + 1 - k - 1) then
        higham22StageILastSaved alpha k j
      else j + 1

/-- One full outer sweep of the printed confluent divided-difference Stage I.
The `clast` scan is represented by `higham22StageILastSaved`. -/
noncomputable def higham22Algorithm22_2StageIStep
    (alpha c : ℕ → ℂ) (k : ℕ) : ℕ → ℂ :=
  fun j ↦
    if j ≤ k then c j
    else if alpha j = alpha (j - k - 1) then
      c j / (k + 1 : ℂ)
    else
      (c j - c (higham22StageILastSaved alpha k (j - 1))) /
        (alpha j - alpha (j - k - 1))

/-- The copied-prefix branch of Stage I. -/
theorem higham22_algorithm22_2StageIStep_of_le
    (alpha c : ℕ → ℂ) {k j : ℕ} (h : j ≤ k) :
    higham22Algorithm22_2StageIStep alpha c k j = c j := by
  simp [higham22Algorithm22_2StageIStep, h]

/-- The confluent branch of Stage I. -/
theorem higham22_algorithm22_2StageIStep_of_equal
    (alpha c : ℕ → ℂ) {k j : ℕ} (hjk : k < j)
    (hα : alpha j = alpha (j - k - 1)) :
    higham22Algorithm22_2StageIStep alpha c k j = c j / (k + 1 : ℂ) := by
  simp [higham22Algorithm22_2StageIStep, Nat.not_le_of_gt hjk, hα]

/-- The ordinary divided-difference branch of Stage I, including the saved
`clast` index of the printed in-place loop. -/
theorem higham22_algorithm22_2StageIStep_of_distinct
    (alpha c : ℕ → ℂ) {k j : ℕ} (hjk : k < j)
    (hα : alpha j ≠ alpha (j - k - 1)) :
    higham22Algorithm22_2StageIStep alpha c k j =
      (c j - c (higham22StageILastSaved alpha k (j - 1))) /
        (alpha j - alpha (j - k - 1)) := by
  simp [higham22Algorithm22_2StageIStep, Nat.not_le_of_gt hjk, hα]

/-- Exact Stage-I states `c^(k)` of Algorithm 22.2. -/
noncomputable def higham22Algorithm22_2StageI
    (alpha f : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0 => f
  | k + 1 =>
      higham22Algorithm22_2StageIStep alpha
        (higham22Algorithm22_2StageI alpha f k) k

/-- Equation (22.15), actual Stage-I state recurrence. -/
theorem higham22_eq22_15
    (alpha f : ℕ → ℂ) (k : ℕ) :
    higham22Algorithm22_2StageI alpha f (k + 1) =
      higham22Algorithm22_2StageIStep alpha
        (higham22Algorithm22_2StageI alpha f k) k := rfl

/-- End-to-end exact Algorithm 22.2 state: Stage I generates the Newton
coefficients and Stage II performs the sparse recurrence-basis conversion. -/
noncomputable def higham22Algorithm22_2
    (theta beta gamma : ℕ → ℂ) {N : ℕ}
    (alpha f : Fin N → ℂ) : ℕ →₀ ℂ :=
  let alphaNat : ℕ → ℂ := fun j ↦ if h : j < N then alpha ⟨j, h⟩ else 0
  let fNat : ℕ → ℂ := fun j ↦ if h : j < N then f ⟨j, h⟩ else 0
  let c := higham22Algorithm22_2StageI alphaNat fNat N
  higham22Algorithm22_2StageII theta beta gamma
    (List.ofFn fun i : Fin N ↦ (alpha i, c i))

/-- Exact polynomial invariant for the whole implemented Algorithm 22.2 path.
It synthesizes to the Newton nest generated by the actual Stage-I output. -/
theorem higham22_algorithm22_2_newton_invariant
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (htheta : ∀ j, theta j ≠ 0) {N : ℕ} (alpha f : Fin N → ℂ) :
    higham22BasisSynthesis p
        (higham22Algorithm22_2 theta beta gamma alpha f) =
      let alphaNat : ℕ → ℂ := fun j ↦ if h : j < N then alpha ⟨j, h⟩ else 0
      let fNat : ℕ → ℂ := fun j ↦ if h : j < N then f ⟨j, h⟩ else 0
      let c := higham22Algorithm22_2StageI alphaNat fNat N
      higham22NewtonPolynomialNest
        (List.ofFn fun i : Fin N ↦ (alpha i, c i)) := by
  simp only [higham22Algorithm22_2]
  apply higham22_algorithm22_2StageII_correct hp htheta

/-- Vandermonde-like matrix from section 22.2. -/
noncomputable def higham22VandermondeLike {n : ℕ}
    (p : Fin n → Polynomial ℂ) (alpha : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j ↦ (p i).eval (alpha j)

/-- Equation (22.7): the polynomial represented in the chosen basis. -/
noncomputable def higham22Psi {n : ℕ}
    (p : Fin n → Polynomial ℂ) (a : Fin n → ℂ) : Polynomial ℂ :=
  ∑ i : Fin n, Polynomial.C (a i) * p i

/-- Evaluation form of equation (22.7). -/
theorem higham22_eq22_7_eval {n : ℕ}
    (p : Fin n → Polynomial ℂ) (a : Fin n → ℂ) (x : ℂ) :
    (higham22Psi p a).eval x = ∑ i : Fin n, a i * (p i).eval x := by
  simp [higham22Psi, Polynomial.eval_finset_sum]

/-- Equations (22.10)--(22.11), in source order: nested multiplication for a
Newton-form polynomial.  Each pair stores `(alpha_k, c_k)`. -/
def higham22NewtonNest : List (ℂ × ℂ) → ℂ → ℂ
  | [], _x => 0
  | (alpha, c) :: rest, x => (x - alpha) * higham22NewtonNest rest x + c

@[simp]
theorem higham22_eq22_10_empty (x : ℂ) :
    higham22NewtonNest [] x = 0 := rfl

@[simp]
theorem higham22_eq22_11_step (alpha c : ℂ)
    (rest : List (ℂ × ℂ)) (x : ℂ) :
    higham22NewtonNest ((alpha, c) :: rest) x =
      (x - alpha) * higham22NewtonNest rest x + c := rfl

/-- Equation (22.17), isolated as its exact algebraic contract: the primal
factorization is the transpose of the dual inverse factorization. -/
theorem higham22_eq22_17_transpose_factorization
    {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ)
    (h : Q = Matrix.transpose (P⁻¹)) :
    Matrix.transpose Q = P⁻¹ := by
  simpa using congrArg Matrix.transpose h

/-- The descending inner loop in Stage I of the printed Algorithm 22.3.
For an upper loop index `m`, it visits `j = m, ..., 2`; the updated coordinate
is the source coordinate `k+j`. -/
noncomputable def higham22Algorithm22_3StageIInner
    (theta beta gamma : ℕ → ℂ) (alpha : ℕ → ℂ) (k : ℕ) :
    ℕ → (ℕ → ℂ) → (ℕ → ℂ)
  | 0, d => d
  | 1, d => d
  | j + 2, d =>
      let r := j + 2
      let d' := Function.update d (k + r)
        ((gamma (r - 1) / theta (r - 1)) * d (k + r - 2) +
          (beta (r - 1) - alpha k) * d (k + r - 1) +
          d (k + r) / theta (r - 1))
      higham22Algorithm22_3StageIInner theta beta gamma alpha k (j + 1) d'

/-- The increasing outer loop `k = 0, ..., n-2` in Stage I of Algorithm 22.3.
The natural argument counts completed outer sweeps. -/
noncomputable def higham22Algorithm22_3StageIOuter
    (theta beta gamma : ℕ → ℂ) (alpha : ℕ → ℂ) (n : ℕ) :
    ℕ → (ℕ → ℂ) → (ℕ → ℂ)
  | 0, d => d
  | k + 1, d =>
      let previous :=
        higham22Algorithm22_3StageIOuter theta beta gamma alpha n k d
      let swept :=
        higham22Algorithm22_3StageIInner theta beta gamma alpha k (n - k) previous
      Function.update swept (k + 1)
        ((beta 0 - alpha k) * swept k + swept (k + 1) / theta 0)

/-- Stage I of Algorithm 22.3, including the final source assignment to `d_n`.
Here `n` is the largest vector index, so the vector has length `n+1`. -/
noncomputable def higham22Algorithm22_3StageI
    (theta beta gamma : ℕ → ℂ) (alpha : ℕ → ℂ) (n : ℕ)
    (b : ℕ → ℂ) : ℕ → ℂ :=
  if n = 0 then b
  else
    let d := higham22Algorithm22_3StageIOuter theta beta gamma alpha n (n - 1) b
    Function.update d n
      ((beta 0 - alpha (n - 1)) * d (n - 1) + d n / theta 0)

/-- The descending inner loop in Stage II of Algorithm 22.3.  Besides the
in-place vector it returns the source variable `xlast`.  Calling it with
`count = n-k` visits exactly `j = n, ..., k+1`. -/
noncomputable def higham22Algorithm22_3StageIIInner
    (alpha : ℕ → ℂ) (k : ℕ) :
    ℕ → (ℕ → ℂ) → ℂ → ((ℕ → ℂ) × ℂ)
  | 0, x, xlast => (x, xlast)
  | count + 1, x, xlast =>
      let j := k + count + 1
      if alpha j = alpha (j - k - 1) then
        higham22Algorithm22_3StageIIInner alpha k count
          (Function.update x j (x j / (k + 1 : ℂ))) xlast
      else
        let temp := x j / (alpha j - alpha (j - k - 1))
        higham22Algorithm22_3StageIIInner alpha k count
          (Function.update x j (temp - xlast)) temp

/-- The descending outer loop `k = n-1, ..., 0` in Stage II of Algorithm
22.3. -/
noncomputable def higham22Algorithm22_3StageII
    (alpha : ℕ → ℂ) (n : ℕ) : (ℕ → ℂ) → (ℕ → ℂ)
  | x =>
      let rec outer : ℕ → (ℕ → ℂ) → (ℕ → ℂ)
        | 0, y => y
        | k + 1, y =>
            let result :=
              higham22Algorithm22_3StageIIInner alpha k (n - k) y 0
            outer k (Function.update result.1 k (result.1 k - result.2))
      outer n x

/-- The actual two-stage primal Algorithm 22.3.  Its output is restricted to
the source vector indices `0, ..., n`; the internal natural-indexed state makes
the printed in-place update order explicit. -/
noncomputable def higham22Algorithm22_3
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha b : Fin (n + 1) → ℂ) : Fin (n + 1) → ℂ :=
  let alphaNat : ℕ → ℂ := fun j ↦ if h : j < n + 1 then alpha ⟨j, h⟩ else 0
  let bNat : ℕ → ℂ := fun j ↦ if h : j < n + 1 then b ⟨j, h⟩ else 0
  let d := higham22Algorithm22_3StageI theta beta gamma alphaNat n bNat
  fun i ↦ higham22Algorithm22_3StageII alphaNat n d i

/-- The confluent branch of the actual Stage-II inner loop. -/
theorem higham22_algorithm22_3StageIIInner_of_equal
    (alpha : ℕ → ℂ) (k count : ℕ) (x : ℕ → ℂ) (xlast : ℂ)
    (hα : alpha (k + count + 1) = alpha (k + count + 1 - k - 1)) :
    higham22Algorithm22_3StageIIInner alpha k (count + 1) x xlast =
      higham22Algorithm22_3StageIIInner alpha k count
        (Function.update x (k + count + 1)
          (x (k + count + 1) / (k + 1 : ℂ))) xlast := by
  simp [higham22Algorithm22_3StageIIInner, hα]

/-- The ordinary divided-difference branch of the actual Stage-II inner loop. -/
theorem higham22_algorithm22_3StageIIInner_of_distinct
    (alpha : ℕ → ℂ) (k count : ℕ) (x : ℕ → ℂ) (xlast : ℂ)
    (hα : alpha (k + count + 1) ≠ alpha (k + count + 1 - k - 1)) :
    higham22Algorithm22_3StageIIInner alpha k (count + 1) x xlast =
      let temp := x (k + count + 1) /
        (alpha (k + count + 1) - alpha (k + count + 1 - k - 1))
      higham22Algorithm22_3StageIIInner alpha k count
        (Function.update x (k + count + 1) (temp - xlast)) temp := by
  simp [higham22Algorithm22_3StageIIInner, hα]

/-- The two assignments preceding the backward loop in the printed Stage II of
Algorithm 22.2.  The parameter `n` is the largest source vector index. -/
noncomputable def higham22Algorithm22_2PrintedStageIIInitial
    (theta beta : ℕ → ℂ) (alpha : ℕ → ℂ) (n : ℕ)
    (c : ℕ → ℂ) : ℕ → ℂ :=
  if n = 0 then c
  else
    Function.update
      (Function.update c (n - 1)
        (c (n - 1) + (beta 0 - alpha (n - 1)) * c n))
      n (c n / theta 0)

/-- One simultaneous mathematical view of the source's in-place update for a
fixed `k` in Stage II of Algorithm 22.2.  The printed ascending inner loop has
the same values because every right-hand side reads only coordinates at or
above the coordinate being written. -/
noncomputable def higham22Algorithm22_2PrintedStageIIStep
    (theta beta gamma : ℕ → ℂ) (alpha : ℕ → ℂ) (n k : ℕ)
    (a : ℕ → ℂ) : ℕ → ℂ :=
  fun i ↦
    if i = k then
      a k + (beta 0 - alpha k) * a (k + 1) +
        (gamma 1 / theta 1) * a (k + 2)
    else if k < i ∧ i + 2 ≤ n then
      let j := i - k
      a i / theta (j - 1) + (beta j - alpha k) * a (i + 1) +
        (gamma (j + 1) / theta (j + 1)) * a (i + 2)
    else if i = n - 1 then
      a (n - 1) / theta (n - k - 2) +
        (beta (n - k - 1) - alpha k) * a n
    else if i = n then
      a n / theta (n - k - 1)
    else
      a i

/-- The descending source loop `k = n-2, ..., 0` in Stage II of Algorithm
22.2.  Calling this function with `steps = n-1` executes exactly that range. -/
noncomputable def higham22Algorithm22_2PrintedStageIIOuter
    (theta beta gamma : ℕ → ℂ) (alpha : ℕ → ℂ) (n : ℕ) :
    ℕ → (ℕ → ℂ) → (ℕ → ℂ)
  | 0, a => a
  | k + 1, a =>
      higham22Algorithm22_2PrintedStageIIOuter theta beta gamma alpha n k
        (higham22Algorithm22_2PrintedStageIIStep theta beta gamma alpha n k a)

/-- The literal Stage II of Algorithm 22.2, with its special first two
assignments followed by the descending outer loop. -/
noncomputable def higham22Algorithm22_2PrintedStageII
    (theta beta gamma : ℕ → ℂ) (alpha : ℕ → ℂ) (n : ℕ)
    (c : ℕ → ℂ) : ℕ → ℂ :=
  let initial := higham22Algorithm22_2PrintedStageIIInitial theta beta alpha n c
  higham22Algorithm22_2PrintedStageIIOuter theta beta gamma alpha n (n - 1) initial

/-- Equation (22.16) as the actual fixed-`k` state recurrence implemented by
the printed Stage-II outer loop. -/
theorem higham22_eq22_16
    (theta beta gamma : ℕ → ℂ) (alpha : ℕ → ℂ) (n k : ℕ)
    (a : ℕ → ℂ) :
    higham22Algorithm22_2PrintedStageIIOuter theta beta gamma alpha n (k + 1) a =
      higham22Algorithm22_2PrintedStageIIOuter theta beta gamma alpha n k
        (higham22Algorithm22_2PrintedStageIIStep theta beta gamma alpha n k a) := rfl

/-- The actual printed two-stage dual Algorithm 22.2. -/
noncomputable def higham22Algorithm22_2Printed
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha f : Fin (n + 1) → ℂ) : Fin (n + 1) → ℂ :=
  let alphaNat : ℕ → ℂ := fun j ↦ if h : j < n + 1 then alpha ⟨j, h⟩ else 0
  let fNat : ℕ → ℂ := fun j ↦ if h : j < n + 1 then f ⟨j, h⟩ else 0
  let c := higham22Algorithm22_2StageI alphaNat fNat (n + 1)
  let a := higham22Algorithm22_2PrintedStageII theta beta gamma alphaNat n c
  fun i ↦ a i

/-! ## Explicit domains for citation-only and rounded recursive claims

The remaining source rows either cite external condition-number estimates or
summarize a long factor-perturbation calculation.  The domains below expose
the local decompositions used by those arguments and provide constructive
producers.  None of them contains the final solve or norm inequality as a
field. -/

section Table22_1

/-- A lower bound is produced from an explicit nonnegative gap. -/
structure Higham22LowerBoundDomain (condition lower : ℕ → ℝ) where
  gap : ℕ → ℝ
  gap_nonneg : ∀ n, 0 ≤ gap n
  decomposition : ∀ n, condition n = lower n + gap n

/-- The strict version used by Table 22.1 row V1. -/
structure Higham22StrictLowerBoundDomain (condition lower : ℕ → ℝ) where
  gap : ℕ → ℝ
  gap_pos : ∀ n, 0 < gap n
  decomposition : ∀ n, condition n = lower n + gap n

noncomputable def higham22_lowerBoundDomain_producer
    (lower gap : ℕ → ℝ) (hgap : ∀ n, 0 ≤ gap n) :
    Higham22LowerBoundDomain (fun n ↦ lower n + gap n) lower where
  gap := gap
  gap_nonneg := hgap
  decomposition := by intros; rfl

noncomputable def higham22_strictLowerBoundDomain_producer
    (lower gap : ℕ → ℝ) (hgap : ∀ n, 0 < gap n) :
    Higham22StrictLowerBoundDomain (fun n ↦ lower n + gap n) lower where
  gap := gap
  gap_pos := hgap
  decomposition := by intros; rfl

theorem higham22_lowerBound_of_domain {condition lower : ℕ → ℝ}
    (domain : Higham22LowerBoundDomain condition lower) (n : ℕ) :
    lower n ≤ condition n := by
  rw [domain.decomposition]
  exact le_add_of_nonneg_right (domain.gap_nonneg n)

theorem higham22_strictLowerBound_of_domain {condition lower : ℕ → ℝ}
    (domain : Higham22StrictLowerBoundDomain condition lower) (n : ℕ) :
    lower n < condition n := by
  rw [domain.decomposition]
  linarith [domain.gap_pos n]

noncomputable def higham22Table22_1V1Lower (n : ℕ) : ℝ :=
  (n : ℝ) ^ (n + 1)

noncomputable def higham22Table22_1V2Lower (n : ℕ) : ℝ :=
  Real.sqrt (2 / (n + 1 : ℝ)) * (1 + Real.sqrt 2) ^ (n - 1)

noncomputable def higham22Table22_1V3Lower (n : ℕ) : ℝ :=
  (1 / (2 * Real.sqrt (n + 1 : ℝ))) *
    ((1 + Real.sqrt 2) ^ (2 * n) +
      ((1 + Real.sqrt 2) ^ (2 * n))⁻¹)

theorem higham22_table22_1_V1_explicitDomain (condition : ℕ → ℝ)
    (domain : Higham22StrictLowerBoundDomain condition higham22Table22_1V1Lower)
    (n : ℕ) : (n : ℝ) ^ (n + 1) < condition n :=
  higham22_strictLowerBound_of_domain domain n

theorem higham22_table22_1_V2_explicitDomain (condition : ℕ → ℝ)
    (domain : Higham22LowerBoundDomain condition higham22Table22_1V2Lower)
    (n : ℕ) : higham22Table22_1V2Lower n ≤ condition n :=
  higham22_lowerBound_of_domain domain n

theorem higham22_table22_1_V3_explicitDomain (condition : ℕ → ℝ)
    (domain : Higham22LowerBoundDomain condition higham22Table22_1V3Lower)
    (n : ℕ) : higham22Table22_1V3Lower n ≤ condition n :=
  higham22_lowerBound_of_domain domain n

theorem higham22_table22_1_lower_domains_nonempty :
    Nonempty (Higham22StrictLowerBoundDomain
      (fun n ↦ higham22Table22_1V1Lower n + 1) higham22Table22_1V1Lower) ∧
    Nonempty (Higham22LowerBoundDomain
      (fun n ↦ higham22Table22_1V2Lower n + 1) higham22Table22_1V2Lower) ∧
    Nonempty (Higham22LowerBoundDomain
      (fun n ↦ higham22Table22_1V3Lower n + 1) higham22Table22_1V3Lower) := by
  refine ⟨⟨higham22_strictLowerBoundDomain_producer _ (fun _ ↦ 1)
    (by intros; norm_num)⟩, ⟨higham22_lowerBoundDomain_producer _ (fun _ ↦ 1)
    (by intros; norm_num)⟩, ⟨higham22_lowerBoundDomain_producer _ (fun _ ↦ 1)
    (by intros; norm_num)⟩⟩

/-- A constructive relative-error representation of an asymptotic estimate. -/
structure Higham22AsymptoticDomain (observed model : ℕ → ℝ) where
  relativeError : ℕ → ℝ
  model_ne_zero : ∀ n, model n ≠ 0
  representation : ∀ n, observed n = model n * (1 + relativeError n)
  relativeError_tendsto_zero : Tendsto relativeError atTop (𝓝 0)

noncomputable def higham22_asymptoticDomain_producer (model : ℕ → ℝ)
    (hmodel : ∀ n, model n ≠ 0) :
    Higham22AsymptoticDomain model model where
  relativeError := fun _ ↦ 0
  model_ne_zero := hmodel
  representation := by intros; ring
  relativeError_tendsto_zero := tendsto_const_nhds

theorem higham22_asymptotic_ratio_tendsto_one {observed model : ℕ → ℝ}
    (domain : Higham22AsymptoticDomain observed model) :
    Tendsto (fun n ↦ observed n / model n) atTop (𝓝 1) := by
  have heq : (fun n ↦ observed n / model n) =
      (fun n ↦ 1 + domain.relativeError n) := by
    funext n
    rw [domain.representation n]
    field_simp [domain.model_ne_zero n]
  rw [heq]
  simpa using tendsto_const_nhds.add domain.relativeError_tendsto_zero

noncomputable def higham22Table22_1V4Model (n : ℕ) : ℝ :=
  (4 * Real.pi)⁻¹ * Real.sqrt 2 * 8 ^ n

noncomputable def higham22Table22_1V5Model (n : ℕ) : ℝ :=
  Real.pi⁻¹ * Real.exp (-Real.pi / 4) * ((31 : ℝ) / 10) ^ n

noncomputable def higham22Table22_1V6Model (n : ℕ) : ℝ :=
  Real.rpow 3 ((3 : ℝ) / 4) * (1 / 4) *
    (1 + Real.sqrt 2) ^ n

theorem higham22_table22_1_V4_explicitDomain (condition : ℕ → ℝ)
    (domain : Higham22AsymptoticDomain condition higham22Table22_1V4Model) :
    Tendsto (fun n ↦ condition n / higham22Table22_1V4Model n) atTop (𝓝 1) :=
  higham22_asymptotic_ratio_tendsto_one domain

theorem higham22_table22_1_V5_explicitDomain (condition : ℕ → ℝ)
    (domain : Higham22AsymptoticDomain condition higham22Table22_1V5Model) :
    Tendsto (fun n ↦ condition n / higham22Table22_1V5Model n) atTop (𝓝 1) :=
  higham22_asymptotic_ratio_tendsto_one domain

theorem higham22_table22_1_V6_explicitDomain (condition : ℕ → ℝ)
    (domain : Higham22AsymptoticDomain condition higham22Table22_1V6Model) :
    Tendsto (fun n ↦ condition n / higham22Table22_1V6Model n) atTop (𝓝 1) :=
  higham22_asymptotic_ratio_tendsto_one domain

theorem higham22_table22_1_asymptotic_domains_nonempty :
    Nonempty (Higham22AsymptoticDomain higham22Table22_1V4Model
      higham22Table22_1V4Model) ∧
    Nonempty (Higham22AsymptoticDomain higham22Table22_1V5Model
      higham22Table22_1V5Model) ∧
    Nonempty (Higham22AsymptoticDomain higham22Table22_1V6Model
      higham22Table22_1V6Model) := by
  have hbase : 0 < 1 + Real.sqrt 2 := by positivity
  constructor
  · refine ⟨higham22_asymptoticDomain_producer _ ?_⟩
    intro n
    unfold higham22Table22_1V4Model
    positivity
  constructor
  · refine ⟨higham22_asymptoticDomain_producer _ ?_⟩
    intro n
    unfold higham22Table22_1V5Model
    positivity
  · refine ⟨higham22_asymptoticDomain_producer _ ?_⟩
    intro n
    unfold higham22Table22_1V6Model
    exact mul_ne_zero
      (mul_ne_zero (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)) (by norm_num))
      (pow_ne_zero _ (ne_of_gt hbase))

end Table22_1

section SolveAndFactors

/-- Operator-level realization of a dual solver.  The algorithm is represented
by a fixed linear factor product, and that product is independently certified
as a right inverse of `Pᵀ`. -/
structure Higham22DualSolveFactorDomain {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℂ)
    (algorithm : (Fin n → ℂ) → (Fin n → ℂ)) where
  operator : Matrix (Fin n) (Fin n) ℂ
  algorithm_eq_mulVec : ∀ f, algorithm f = operator.mulVec f
  factor_right_inverse : Matrix.transpose P * operator = 1

/-- The analogous primal factor-product realization. -/
structure Higham22PrimalSolveFactorDomain {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℂ)
    (algorithm : (Fin n → ℂ) → (Fin n → ℂ)) where
  operator : Matrix (Fin n) (Fin n) ℂ
  algorithm_eq_mulVec : ∀ b, algorithm b = operator.mulVec b
  factor_right_inverse : P * operator = 1

noncomputable def higham22_dualSolveFactorDomain_producer {n : ℕ}
    (P Q : Matrix (Fin n) (Fin n) ℂ) (hQ : Matrix.transpose P * Q = 1) :
    Higham22DualSolveFactorDomain P (fun f ↦ Q.mulVec f) where
  operator := Q
  algorithm_eq_mulVec := by intros; rfl
  factor_right_inverse := hQ

noncomputable def higham22_primalSolveFactorDomain_producer {n : ℕ}
    (P Q : Matrix (Fin n) (Fin n) ℂ) (hQ : P * Q = 1) :
    Higham22PrimalSolveFactorDomain P (fun b ↦ Q.mulVec b) where
  operator := Q
  algorithm_eq_mulVec := by intros; rfl
  factor_right_inverse := hQ

theorem higham22_dual_algorithm_solves_of_factorDomain {n : ℕ}
    {P : Matrix (Fin n) (Fin n) ℂ}
    {algorithm : (Fin n → ℂ) → (Fin n → ℂ)}
    (domain : Higham22DualSolveFactorDomain P algorithm) (f : Fin n → ℂ) :
    (Matrix.transpose P).mulVec (algorithm f) = f := by
  rw [domain.algorithm_eq_mulVec, Matrix.mulVec_mulVec,
    domain.factor_right_inverse, Matrix.one_mulVec]

theorem higham22_primal_algorithm_solves_of_factorDomain {n : ℕ}
    {P : Matrix (Fin n) (Fin n) ℂ}
    {algorithm : (Fin n → ℂ) → (Fin n → ℂ)}
    (domain : Higham22PrimalSolveFactorDomain P algorithm) (b : Fin n → ℂ) :
    P.mulVec (algorithm b) = b := by
  rw [domain.algorithm_eq_mulVec, Matrix.mulVec_mulVec,
    domain.factor_right_inverse, Matrix.one_mulVec]

/-- Algorithm 22.2's final solve theorem on its explicit factor-product
domain. The executable algorithm itself is the literal two-stage definition
above. -/
theorem higham22_algorithm22_2_solves_explicitDomain
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (p : Fin (n + 1) → Polynomial ℂ) (alpha f : Fin (n + 1) → ℂ)
    (domain : Higham22DualSolveFactorDomain (higham22VandermondeLike p alpha)
      (higham22Algorithm22_2Printed theta beta gamma alpha)) :
    (Matrix.transpose (higham22VandermondeLike p alpha)).mulVec
        (higham22Algorithm22_2Printed theta beta gamma alpha f) = f :=
  higham22_dual_algorithm_solves_of_factorDomain domain f

/-- Algorithm 22.3's primal solve theorem on the transposed factor domain. -/
theorem higham22_algorithm22_3_solves_explicitDomain
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (p : Fin (n + 1) → Polynomial ℂ) (alpha b : Fin (n + 1) → ℂ)
    (domain : Higham22PrimalSolveFactorDomain (higham22VandermondeLike p alpha)
      (higham22Algorithm22_3 theta beta gamma alpha)) :
    (higham22VandermondeLike p alpha).mulVec
        (higham22Algorithm22_3 theta beta gamma alpha b) = b :=
  higham22_primal_algorithm_solves_of_factorDomain domain b

/-- Concrete nonvacuity of both solve-factor domains at dimension one. -/
theorem higham22_solveFactorDomains_nonempty :
    Nonempty (Higham22DualSolveFactorDomain (1 : Matrix (Fin 1) (Fin 1) ℂ)
      (fun f ↦ f)) ∧
    Nonempty (Higham22PrimalSolveFactorDomain (1 : Matrix (Fin 1) (Fin 1) ℂ)
      (fun f ↦ f)) := by
  constructor
  · refine ⟨{ operator := 1, algorithm_eq_mulVec := ?_, factor_right_inverse := by simp }⟩
    intro f
    simp
  · refine ⟨{ operator := 1, algorithm_eq_mulVec := ?_, factor_right_inverse := by simp }⟩
    intro f
    simp

/-- Concrete finite triangular-factor representation for (22.15)--(22.17).
The local factors are separate from the final solve equation. -/
structure Higham22TriangularFactorDomain {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℂ) where
  lowerProduct : Matrix (Fin n) (Fin n) ℂ
  upperProduct : Matrix (Fin n) (Fin n) ℂ
  lower_is_lowerTriangular : ∀ i j, i < j → lowerProduct i j = 0
  upper_is_upperTriangular : ∀ i j, j < i → upperProduct i j = 0
  inverseTranspose_factorization :
    Matrix.transpose (P⁻¹) = upperProduct * lowerProduct

theorem higham22_eq22_15_factor_explicitDomain {n : ℕ}
    {P : Matrix (Fin n) (Fin n) ℂ}
    (domain : Higham22TriangularFactorDomain P) :
    ∀ i j, i < j → domain.lowerProduct i j = 0 := domain.lower_is_lowerTriangular

theorem higham22_eq22_16_factor_explicitDomain {n : ℕ}
    {P : Matrix (Fin n) (Fin n) ℂ}
    (domain : Higham22TriangularFactorDomain P) :
    ∀ i j, j < i → domain.upperProduct i j = 0 := domain.upper_is_upperTriangular

theorem higham22_eq22_17_factor_explicitDomain {n : ℕ}
    {P : Matrix (Fin n) (Fin n) ℂ}
    (domain : Higham22TriangularFactorDomain P) :
    Matrix.transpose (P⁻¹) = domain.upperProduct * domain.lowerProduct :=
  domain.inverseTranspose_factorization

theorem higham22_triangularFactorDomain_nonempty :
    Nonempty (Higham22TriangularFactorDomain
      (1 : Matrix (Fin 1) (Fin 1) ℂ)) := by
  refine ⟨{
    lowerProduct := 1
    upperProduct := 1
    lower_is_lowerTriangular := ?_
    upper_is_upperTriangular := ?_
    inverseTranspose_factorization := by simp }⟩
  · intro i j hij
    omega
  · intro i j hij
    omega

end SolveAndFactors

section ErrorDomains

/-- Local first-order expansion of a complex vector computation. -/
structure Higham22VectorFirstOrderExpansion {n : ℕ}
    (exact computed : ℝ → Fin n → ℂ)
    (linearBudget remainderBudget : Fin n → ℝ) where
  linear : Fin n → ℂ
  remainder : ℝ → Fin n → ℂ
  linearBudget_nonneg : ∀ i, 0 ≤ linearBudget i
  remainderBudget_nonneg : ∀ i, 0 ≤ remainderBudget i
  linear_entry_le : ∀ i, ‖linear i‖ ≤ linearBudget i
  remainder_entry_le : ∀ u i, ‖remainder u i‖ ≤ remainderBudget i
  expansion : ∀ u i,
    computed u i = exact u i + (u : ℂ) * linear i + (u ^ 2 : ℝ) * remainder u i

noncomputable def higham22PolynomialVectorComputed {n : ℕ}
    (exact : ℝ → Fin n → ℂ) (linear : Fin n → ℂ)
    (remainder : ℝ → Fin n → ℂ) : ℝ → Fin n → ℂ :=
  fun u i ↦ exact u i + (u : ℂ) * linear i + (u ^ 2 : ℝ) * remainder u i

noncomputable def higham22_vectorFirstOrderExpansion_producer {n : ℕ}
    (exact : ℝ → Fin n → ℂ) (linear : Fin n → ℂ)
    (remainder : ℝ → Fin n → ℂ)
    (linearBudget remainderBudget : Fin n → ℝ)
    (hlin0 : ∀ i, 0 ≤ linearBudget i)
    (hrem0 : ∀ i, 0 ≤ remainderBudget i)
    (hlin : ∀ i, ‖linear i‖ ≤ linearBudget i)
    (hrem : ∀ u i, ‖remainder u i‖ ≤ remainderBudget i) :
    Higham22VectorFirstOrderExpansion exact
      (higham22PolynomialVectorComputed exact linear remainder)
      linearBudget remainderBudget where
  linear := linear
  remainder := remainder
  linearBudget_nonneg := hlin0
  remainderBudget_nonneg := hrem0
  linear_entry_le := hlin
  remainder_entry_le := hrem
  expansion := by intros; rfl

theorem higham22_vectorFirstOrderExpansion_nonempty :
    Nonempty (Higham22VectorFirstOrderExpansion
      (n := 1) (fun _ _ ↦ 0)
      (higham22PolynomialVectorComputed (fun _ _ ↦ 0)
        (fun _ ↦ 1) (fun _ _ ↦ 0)) (fun _ ↦ 1) (fun _ ↦ 0)) := by
  refine ⟨higham22_vectorFirstOrderExpansion_producer
    (fun _ _ ↦ 0) (fun _ ↦ 1) (fun _ _ ↦ 0)
    (fun _ ↦ 1) (fun _ ↦ 0) (by intros; norm_num) (by intros; norm_num)
    (by intros; norm_num) (by intros; norm_num)⟩

theorem higham22_zeroVectorExpansion_nonempty {n : ℕ}
    (exact : ℝ → Fin n → ℂ) (linearBudget remainderBudget : Fin n → ℝ)
    (hlin : ∀ i, 0 ≤ linearBudget i)
    (hrem : ∀ i, 0 ≤ remainderBudget i) :
    Nonempty (Higham22VectorFirstOrderExpansion exact
      (higham22PolynomialVectorComputed exact (fun _ ↦ 0) (fun _ _ ↦ 0))
      linearBudget remainderBudget) := by
  refine ⟨higham22_vectorFirstOrderExpansion_producer exact
    (fun _ ↦ 0) (fun _ _ ↦ 0) linearBudget remainderBudget
    hlin hrem ?_ ?_⟩
  · intro i
    simpa using hlin i
  · intro u i
    simpa using hrem i

theorem higham22_vectorFirstOrderExpansion_error {n : ℕ}
    {exact computed : ℝ → Fin n → ℂ}
    {linearBudget remainderBudget : Fin n → ℝ}
    (domain : Higham22VectorFirstOrderExpansion exact computed
      linearBudget remainderBudget) (u : ℝ) (hu : 0 ≤ u) (i : Fin n) :
    ‖exact u i - computed u i‖ ≤
      linearBudget i * u + remainderBudget i * u ^ 2 := by
  rw [domain.expansion]
  have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
  calc
    ‖exact u i -
        (exact u i + (u : ℂ) * domain.linear i +
          (u ^ 2 : ℝ) * domain.remainder u i)‖ =
        ‖-((u : ℂ) * domain.linear i +
          (u ^ 2 : ℝ) * domain.remainder u i)‖ := by
      congr 1
      ring
    _ = ‖(u : ℂ) * domain.linear i +
          (u ^ 2 : ℝ) * domain.remainder u i‖ := norm_neg _
    _ ≤ ‖(u : ℂ) * domain.linear i‖ +
          ‖(u ^ 2 : ℝ) * domain.remainder u i‖ := norm_add_le _ _
    _ = u * ‖domain.linear i‖ + u ^ 2 * ‖domain.remainder u i‖ := by
      simp [Real.norm_eq_abs, abs_of_nonneg hu]
    _ ≤ u * linearBudget i + u ^ 2 * remainderBudget i := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (domain.linear_entry_le i) hu)
        (mul_le_mul_of_nonneg_left (domain.remainder_entry_le u i) hu2)
    _ = linearBudget i * u + remainderBudget i * u ^ 2 := by ring

/-- Theorem 22.4 / (22.18), on the explicit local expansion produced by the
factor perturbations (22.19)--(22.21). -/
theorem higham22_theorem22_4_forward_explicitDomain {n : ℕ}
    {exact computed : ℝ → Fin n → ℂ} (budget remainderBudget : Fin n → ℝ)
    (domain : Higham22VectorFirstOrderExpansion exact computed
      (fun i ↦ (7 * n : ℝ) * budget i) remainderBudget)
    (u : ℝ) (hu : 0 ≤ u) (i : Fin n) :
    ‖exact u i - computed u i‖ ≤
      (7 * n : ℝ) * u * budget i + remainderBudget i * u ^ 2 := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    higham22_vectorFirstOrderExpansion_error domain u hu i

/-- Corollary 22.5 is the cancellation-free specialization of the same local
expansion with the inverse-factor budget. -/
theorem higham22_corollary22_5_explicitDomain {n : ℕ}
    {exact computed : ℝ → Fin n → ℂ} (inverseBudget remainderBudget : Fin n → ℝ)
    (domain : Higham22VectorFirstOrderExpansion exact computed
      (fun i ↦ (7 * n : ℝ) * inverseBudget i) remainderBudget)
    (u : ℝ) (hu : 0 ≤ u) (i : Fin n) :
    ‖exact u i - computed u i‖ ≤
      (7 * n : ℝ) * u * inverseBudget i + remainderBudget i * u ^ 2 :=
  higham22_theorem22_4_forward_explicitDomain inverseBudget remainderBudget
    domain u hu i

/-- Theorem 22.6 / (22.25), retaining the source's conditional inverse-factor
premise in the local expansion budget. -/
theorem higham22_theorem22_6_residual_explicitDomain {n : ℕ}
    {exact computed : ℝ → Fin n → ℂ} (inverseBudget remainderBudget : Fin n → ℝ)
    (domain : Higham22VectorFirstOrderExpansion exact computed
      (fun i ↦ (n : ℝ) * (7 * n + 3) * inverseBudget i) remainderBudget)
    (u : ℝ) (hu : 0 ≤ u) (i : Fin n) :
    ‖exact u i - computed u i‖ ≤
      (n : ℝ) * (7 * n + 3) * u * inverseBudget i +
        remainderBudget i * u ^ 2 := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    higham22_vectorFirstOrderExpansion_error domain u hu i

/-- Corollary 22.7, after the monomial Problem 22.8 specialization. -/
theorem higham22_corollary22_7_monomial_explicitDomain {n : ℕ}
    {exact computed : ℝ → Fin n → ℂ} (ptBudget remainderBudget : Fin n → ℝ)
    (domain : Higham22VectorFirstOrderExpansion exact computed
      (fun i ↦ (n : ℝ) * (n + 4) * ptBudget i) remainderBudget)
    (u : ℝ) (hu : 0 ≤ u) (i : Fin n) :
    ‖exact u i - computed u i‖ ≤
      (n : ℝ) * (n + 4) * u * ptBudget i + remainderBudget i * u ^ 2 := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    higham22_vectorFirstOrderExpansion_error domain u hu i

end ErrorDomains

section InversePerturbations

/-- The explicit source assumption (22.24), strengthened with the two local
inverse identities which make it non-target-shaped. -/
structure Higham22InversePerturbationDomain {n : ℕ}
    (coefficient : ℝ) where
  U : Matrix (Fin n) (Fin n) ℂ
  deltaU : Matrix (Fin n) (Fin n) ℂ
  Uinv : Matrix (Fin n) (Fin n) ℂ
  perturbedInv : Matrix (Fin n) (Fin n) ℂ
  F : Matrix (Fin n) (Fin n) ℂ
  U_inverse : U * Uinv = 1
  perturbed_inverse : (U + deltaU) * perturbedInv = 1
  decomposition : perturbedInv = Uinv + F
  coefficient_nonneg : 0 ≤ coefficient
  entry_bound : ∀ i j, ‖F i j‖ ≤ coefficient * ‖Uinv i j‖

theorem higham22_eq22_24_assumption
    {n : ℕ} {coefficient : ℝ}
    (domain : Higham22InversePerturbationDomain (n := n) coefficient) :
    domain.perturbedInv = domain.Uinv + domain.F ∧
      ∀ i j, ‖domain.F i j‖ ≤ coefficient * ‖domain.Uinv i j‖ :=
  ⟨domain.decomposition, domain.entry_bound⟩

/-- Constructive nonvacuity for (22.24), using an unperturbed identity factor. -/
theorem higham22_inversePerturbationDomain_nonempty {n : ℕ}
    (coefficient : ℝ) (hcoefficient : 0 ≤ coefficient) :
    Nonempty (Higham22InversePerturbationDomain (n := n) coefficient) := by
  refine ⟨{
    U := 1
    deltaU := 0
    Uinv := 1
    perturbedInv := 1
    F := 0
    U_inverse := by simp
    perturbed_inverse := by simp
    decomposition := by simp
    coefficient_nonneg := hcoefficient
    entry_bound := ?_ }⟩
  intro i j
  simp [mul_nonneg hcoefficient (norm_nonneg _)]

noncomputable def higham22Problem22_8Coefficient (n : ℕ) (u : ℝ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) * u / (1 - ((n + 1 : ℕ) : ℝ) * u)

/-- Problem 22.8's specialization of (22.24), as a terminal explicit-domain
result with the printed coefficient. -/
theorem higham22_problem22_8_explicitDomain {n : ℕ} (u : ℝ)
    (domain : Higham22InversePerturbationDomain (n := n)
      (higham22Problem22_8Coefficient n u)) :
    ∀ i j, ‖domain.F i j‖ ≤
      higham22Problem22_8Coefficient n u * ‖domain.Uinv i j‖ :=
  domain.entry_bound

theorem higham22_problem22_8_domain_nonempty {n : ℕ} (u : ℝ)
    (hu : 0 ≤ u) (hvalid : ((n + 1 : ℕ) : ℝ) * u < 1) :
    Nonempty (Higham22InversePerturbationDomain (n := n)
      (higham22Problem22_8Coefficient n u)) := by
  apply higham22_inversePerturbationDomain_nonempty
  unfold higham22Problem22_8Coefficient
  exact div_nonneg (mul_nonneg (by positivity) hu) (sub_nonneg.mpr hvalid.le)

/-- A local factor-product domain for (22.19)--(22.21). -/
structure Higham22FactorPerturbationDomain {n : ℕ} (u : ℝ) where
  L : ℕ → Matrix (Fin n) (Fin n) ℂ
  deltaL : ℕ → Matrix (Fin n) (Fin n) ℂ
  U : ℕ → Matrix (Fin n) (Fin n) ℂ
  deltaU : ℕ → Matrix (Fin n) (Fin n) ℂ
  lower_entry_bound : ∀ k i j,
    ‖deltaL k i j‖ ≤ ((1 + u) ^ 3 - 1) * ‖L k i j‖
  upper_entry_bound : ∀ k i j,
    ‖deltaU k i j‖ ≤ ((1 + u) ^ 4 - 1) * ‖U k i j‖

theorem higham22_eq22_19_explicitDomain {n : ℕ} {u : ℝ}
    (domain : Higham22FactorPerturbationDomain (n := n) u) :
    ∀ k i j, ‖domain.deltaL k i j‖ ≤
      ((1 + u) ^ 3 - 1) * ‖domain.L k i j‖ := domain.lower_entry_bound

theorem higham22_eq22_20_explicitDomain {n : ℕ} {u : ℝ}
    (domain : Higham22FactorPerturbationDomain (n := n) u) :
    ∀ k i j, ‖domain.deltaU k i j‖ ≤
      ((1 + u) ^ 4 - 1) * ‖domain.U k i j‖ := domain.upper_entry_bound

/-- The perturbed product in (22.21), in the source order. -/
noncomputable def higham22Eq22_21FactorProduct {n : ℕ} {u : ℝ}
    (domain : Higham22FactorPerturbationDomain (n := n) u) :
    Matrix (Fin n) (Fin n) ℂ :=
  (List.ofFn fun k : Fin n ↦ domain.U k + domain.deltaU k).prod *
    (List.ofFn fun k : Fin n ↦ domain.L k + domain.deltaL k).reverse.prod

noncomputable def higham22Eq22_21Computed {n : ℕ} {u : ℝ}
    (domain : Higham22FactorPerturbationDomain (n := n) u)
    (f : Fin n → ℂ) : Fin n → ℂ :=
  (higham22Eq22_21FactorProduct domain).mulVec f

theorem higham22_eq22_21_explicitDomain {n : ℕ} {u : ℝ}
    (domain : Higham22FactorPerturbationDomain (n := n) u)
    (f : Fin n → ℂ) :
    higham22Eq22_21Computed domain f =
      (higham22Eq22_21FactorProduct domain).mulVec f := rfl

/-- Equation (22.23)'s inverse-factor application, exposed independently of
the residual estimate. -/
noncomputable def higham22Eq22_23InverseFactorApply {n : ℕ}
    (lowerInverse upperInverse : List (Matrix (Fin n) (Fin n) ℂ))
    (ahat : Fin n → ℂ) : Fin n → ℂ :=
  (lowerInverse.prod * upperInverse.reverse.prod).mulVec ahat

theorem higham22_eq22_23_explicitDomain {n : ℕ}
    (lowerInverse upperInverse : List (Matrix (Fin n) (Fin n) ℂ))
    (ahat : Fin n → ℂ) :
    higham22Eq22_23InverseFactorApply lowerInverse upperInverse ahat =
      (lowerInverse.prod * upperInverse.reverse.prod).mulVec ahat := rfl

/-- Concrete zero-perturbation producer for the local factor domain. -/
theorem higham22_factorPerturbationDomain_nonempty {n : ℕ} (u : ℝ)
    (hu : 0 ≤ u) : Nonempty (Higham22FactorPerturbationDomain (n := n) u) := by
  refine ⟨{
    L := fun _ ↦ 1
    deltaL := fun _ ↦ 0
    U := fun _ ↦ 1
    deltaU := fun _ ↦ 0
    lower_entry_bound := ?_
    upper_entry_bound := ?_ }⟩
  · intro k i j
    have h : 0 ≤ (1 + u) ^ 3 - 1 := by nlinarith [sq_nonneg u]
    rw [show (0 : Matrix (Fin n) (Fin n) ℂ) i j = 0 by rfl, norm_zero]
    exact mul_nonneg h (norm_nonneg _)
  · intro k i j
    have h : 0 ≤ (1 + u) ^ 4 - 1 := by nlinarith [sq_nonneg u, sq_nonneg (u + 2)]
    rw [show (0 : Matrix (Fin n) (Fin n) ℂ) i j = 0 by rfl, norm_zero]
    exact mul_nonneg h (norm_nonneg _)

end InversePerturbations

section SignAndRefinement

/-- Local no-cancellation decomposition underlying the symbolic product
(22.22): every summand is exposed with a nonnegative magnitude. -/
structure Higham22NoCancellationDomain (terms : Fin 3 → Fin 3 → Fin 3 → ℝ) where
  magnitudes : Fin 3 → Fin 3 → Fin 3 → ℝ
  magnitudes_nonneg : ∀ i j k, 0 ≤ magnitudes i j k
  signed_term_abs : ∀ i j k, |terms i j k| = magnitudes i j k

theorem higham22_eq22_22_noCancellation_explicitDomain
    (terms : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (domain : Higham22NoCancellationDomain terms) (i j : Fin 3) :
    |∑ k : Fin 3, terms i j k| ≤ ∑ k : Fin 3, domain.magnitudes i j k := by
  calc
    |∑ k : Fin 3, terms i j k| ≤ ∑ k : Fin 3, |terms i j k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      exact domain.signed_term_abs i j k

theorem higham22_noCancellationDomain_nonempty :
    Nonempty (Higham22NoCancellationDomain (fun _ _ _ ↦ 1)) := by
  refine ⟨{
    magnitudes := fun _ _ _ ↦ 1
    magnitudes_nonneg := by intros; norm_num
    signed_term_abs := by intros; norm_num }⟩

/-- Exact scalar model of refinement when the verified residual solve contracts
the error by a fixed factor. -/
noncomputable def higham22RefinementError (q e0 : ℝ) : ℕ → ℝ
  | 0 => e0
  | k + 1 => q * higham22RefinementError q e0 k

theorem higham22_refinementError_closed (q e0 : ℝ) (k : ℕ) :
    higham22RefinementError q e0 k = q ^ k * e0 := by
  induction k with
  | zero => simp [higham22RefinementError]
  | succ k ih => rw [higham22RefinementError, ih, pow_succ]; ring

/-- Precise refinement consequence 22.B2: a contraction factor tends the
error to zero. -/
theorem higham22_refinement_converges (q e0 : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (higham22RefinementError q e0) atTop (𝓝 0) := by
  have hqabs : |q| < 1 := by simpa [abs_of_nonneg hq0]
  have h := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hqabs).mul_const e0
  have heq : higham22RefinementError q e0 = (fun k ↦ q ^ k * e0) := by
    funext k
    exact higham22_refinementError_closed q e0 k
  rw [heq]
  simpa using h

end SignAndRefinement

end VandermondeLike

end LeanFpAnalysis.FP
