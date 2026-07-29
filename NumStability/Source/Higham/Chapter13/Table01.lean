import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.LU.BlockLU.DiagonalDominance
import NumStability.Analysis.FirstOrder.FixedPrecision
import NumStability.Source.Higham.Chapter13.Equation22
import NumStability.Source.Higham.Chapter13.Equation23
import NumStability.Source.Higham.Chapter13.Table01.Families
import NumStability.Source.Higham.Chapter13.Theorem05.FamilyErrorAnalysis
import NumStability.Source.Higham.Chapter13.Theorem06.Computation

namespace NumStability

open Filter Asymptotics
open scoped Topology

/-!
# Higham Chapter 13, Table 13.1

Source-derived uniform endpoints for Table 13.1. This module composes the
concrete Implementation-1 theorem and derives the table rows' product
transfers from their printed component bounds.
-/

/-! ## Product transfers derived from the source row data -/

/-- Higham, 2nd ed., Chapter 13, §13.3.1, p. 253:
    scalar product consequence of column block diagonal dominance.  Once
    Theorems 13.7--13.8 and condition (13.19) have supplied
    `‖L‖ ≤ m` and `‖U‖ ≤ m^2 ‖A‖`, the printed bound
    `‖L‖‖U‖ ≤ m^3 ‖A‖` follows. -/
theorem higham13_col_bdd_stability_bound
    (normL normU normA : ℝ) (m : ℕ)
    (hU : 0 ≤ normU)
    (hNormL : normL ≤ (m : ℝ))
    (hNormU : normU ≤ (m : ℝ) ^ 2 * normA) :
    normL * normU ≤ (m : ℝ) ^ 3 * normA := by
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  calc
    normL * normU ≤ (m : ℝ) * normU :=
      mul_le_mul_of_nonneg_right hNormL hU
    _ ≤ (m : ℝ) * ((m : ℝ) ^ 2 * normA) :=
      mul_le_mul_of_nonneg_left hNormU hm
    _ = (m : ℝ) ^ 3 * normA := by ring

/-- **Point diagonal-dominance column stability** (Table 13.1):
    ‖L‖ · ‖U‖ ≤ 2 · ‖A‖ for point column diag dominant matrices.
    Since every Schur complement is point column diag dominant (Thm 9.8),
    ‖L_{ij}‖ ≤ 1 for i > j (Problem 13.5), so ‖L‖ = 1.
    Also ρ_n ≤ 2 (Thm 9.9/13.8), so ‖U‖ ≤ 2‖A‖ by eq. 13.21. -/
theorem block_lu_stability_point_diagDom_col
    (normL normU normA : ℝ)
    (_hL : 0 ≤ normL) (hU : 0 ≤ normU) (_hA : 0 ≤ normA)
    (hNormL : normL ≤ 1)
    (hNormU : normU ≤ 2 * normA) :
    normL * normU ≤ 2 * normA := by
  nlinarith [mul_le_mul hNormL hNormU hU (by linarith : (0 : ℝ) ≤ 1)]

/-- Column block-diagonal-dominance product transfer from the two component
bounds printed before Table 13.1. -/
theorem higham13_table13_1_col_bdd_product_family_from_source_norms
    {ι : Type*} {l : Filter ι} (Uround : RoundoffFamily ι l)
    (m : ℕ) (normA normL normU : ι → ℝ)
    (hU : ∀ t, 0 ≤ normU t)
    (hNormL : ∀ t, normL t ≤ (m : ℝ))
    (hNormU : ∀ t, normU t ≤ (m : ℝ) ^ 2 * normA t) :
    FamilyLinearRemainderLe l Uround.unit
      (fun t => (m : ℝ) ^ 3 * normA t)
      (fun t => normL t * normU t) := by
  apply FamilyLinearRemainderLe.of_le
  intro t
  exact higham13_col_bdd_stability_bound
    (normL t) (normU t) (normA t) m (hU t) (hNormL t) (hNormU t)

/-- Point column-diagonal-dominance product transfer from its source lower-
and upper-factor bounds. -/
theorem higham13_table13_1_point_col_bdd_product_family_from_source_norms
    {ι : Type*} {l : Filter ι} (Uround : RoundoffFamily ι l)
    (normA normL normU : ι → ℝ)
    (hL : ∀ t, 0 ≤ normL t) (hU : ∀ t, 0 ≤ normU t)
    (hA : ∀ t, 0 ≤ normA t)
    (hNormL : ∀ t, normL t ≤ 1)
    (hNormU : ∀ t, normU t ≤ 2 * normA t) :
    FamilyLinearRemainderLe l Uround.unit
      (fun t => 2 * normA t) (fun t => normL t * normU t) := by
  apply FamilyLinearRemainderLe.of_le
  intro t
  exact block_lu_stability_point_diagDom_col
    (normL t) (normU t) (normA t)
    (hL t) (hU t) (hA t) (hNormL t) (hNormU t)

/-- Arbitrary-matrix (and block-row-BDD) equation-(13.22) product transfer
from the source growth/condition component estimates. -/
theorem higham13_table13_1_arbitrary_product_family_from_eq13_22_source_norms
    {ι : Type*} {l : Filter ι} (Uround : RoundoffFamily ι l)
    (n : ℕ) (rho kappa : ι → ℝ) (normA normL normU : ι → ℝ)
    (hU : ∀ t, 0 ≤ normU t) (hRho : ∀ t, 0 ≤ rho t)
    (hKappa : ∀ t, 0 ≤ kappa t)
    (hNormL : ∀ t,
      normL t ≤ (n : ℝ) * (rho t) ^ 2 * kappa t)
    (hNormU : ∀ t, normU t ≤ rho t * normA t) :
    FamilyLinearRemainderLe l Uround.unit
      (fun t => (n : ℝ) * (rho t) ^ 3 * kappa t * normA t)
      (fun t => normL t * normU t) := by
  apply FamilyLinearRemainderLe.of_le
  intro t
  exact block_lu_normLU_bound_general_higham_13_22
    (normL t) (normU t) (normA t) (rho t) (kappa t) n
    (hU t) (hRho t) (hKappa t) (hNormL t) (hNormU t)

/-- Point row-diagonal-dominance equation-(13.23) product transfer, including
the proved source growth specialization `rho <= 2`. -/
theorem higham13_table13_1_point_row_product_family_from_eq13_23_source_norms
    {ι : Type*} {l : Filter ι} (Uround : RoundoffFamily ι l)
    (n : ℕ) (rho kappa : ι → ℝ) (normA normL normU : ι → ℝ)
    (hU : ∀ t, 0 ≤ normU t) (hA : ∀ t, 0 ≤ normA t)
    (hRho : ∀ t, 0 ≤ rho t) (hRhoTwo : ∀ t, rho t ≤ 2)
    (hKappa : ∀ t, 0 ≤ kappa t)
    (hNormL : ∀ t,
      normL t ≤ (n : ℝ) * (rho t) ^ 2 * kappa t)
    (hNormU : ∀ t, normU t ≤ rho t * normA t) :
    FamilyLinearRemainderLe l Uround.unit
      (fun t => 8 * (n : ℝ) * kappa t * normA t)
      (fun t => normL t * normU t) := by
  apply FamilyLinearRemainderLe.of_le
  intro t
  exact higham13_eq13_23_point_row_from_growth
    (normL t) (normU t) (normA t) (rho t) (kappa t) n
    (hU t) (hA t) (hRho t) (hRhoTwo t) (hKappa t)
    (hNormL t) (hNormU t)

/-- SPD equation-(13.24) product transfer from the two displayed factor
bounds. -/
theorem higham13_table13_1_spd_product_family_from_eq13_24_source_norms
    {ι : Type*} {l : Filter ι} (Uround : RoundoffFamily ι l)
    (m : ℕ) (kappa normA normL normU : ι → ℝ)
    (hU : ∀ t, 0 ≤ normU t)
    (hNormL : ∀ t, normL t ≤ 1 + (m : ℝ) * Real.sqrt (kappa t))
    (hNormU : ∀ t, normU t ≤ Real.sqrt (m : ℝ) * normA t) :
    FamilyLinearRemainderLe l Uround.unit
      (fun t => Real.sqrt (m : ℝ) *
        (1 + (m : ℝ) * Real.sqrt (kappa t)) * normA t)
      (fun t => normL t * normU t) := by
  apply FamilyLinearRemainderLe.of_le
  intro t
  have hLbound0 : 0 ≤ 1 + (m : ℝ) * Real.sqrt (kappa t) := by
    positivity
  have hmul := mul_le_mul (hNormL t) (hNormU t) (hU t) hLbound0
  calc
    normL t * normU t ≤
        (1 + (m : ℝ) * Real.sqrt (kappa t)) *
          (Real.sqrt (m : ℝ) * normA t) := hmul
    _ = Real.sqrt (m : ℝ) *
        (1 + (m : ℝ) * Real.sqrt (kappa t)) * normA t := by ring

/-! ## Concrete Theorem 13.6 to Table 13.1 -/

/-- Table 13.1 for the actual conventional Implementation-1 solve.

The recursive factor computation and conventional solve are executed by the
uniform concrete Theorem 13.6 endpoint.  The only table-specific premise is
the source's `O(u)` comparison between the computed factor product and the
class value; the preceding row lemmas construct this comparison directly when
the printed class factor bounds apply. -/
theorem
    higham13_table13_1_implementation1_family_from_partitioned_computation_and_product_transfer
    {ι : Type*} {l : Filter ι} (Uround : RoundoffFamily ι l)
    (fp : ι → FPModel) (hfp : ∀ t, (fp t).u = Uround.unit t)
    {m r q : ℕ} (hm : 0 < m) (hr : 0 < r)
    (c₁ c₂ c₃ dFact dn tableValue : ℝ)
    (A DeltaFact : ι → Matrix (Fin (m * r)) (Fin (m * r)) ℝ)
    (Lhat U : ι → Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (b : ι → Fin (m * r) → ℝ)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hδ : blockErrorDelta q ≤ dFact)
    (hθ : blockErrorTheta c₁ c₂ c₃ q ≤ dFact)
    (hdFact : dFact ≤ dn)
    (hdSolve : higham13DHSUniformSolveCoefficient dFact m r ≤ dn)
    (hFactComputation : ∀ t,
      PartitionedLUComputationFirstOrder
        (Uround.unit t) c₁ c₂ c₃ q
        (maxEntryNorm (Nat.mul_pos hm hr) (A t))
        (maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin (Lhat t)))
        (maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin (U t)))
        (maxEntryNorm (Nat.mul_pos hm hr) (DeltaFact t))
        (A t) (DeltaFact t)
        (blockMatrixFlatFin (Lhat t)) (blockMatrixFlatFin (U t)))
    (hScalar : Higham13PartitionedLUScalarFamilyComputation
      Uround c₁ c₂ c₃ q
      (fun t => maxEntryNorm (Nat.mul_pos hm hr) (A t))
      (fun t => maxEntryNorm (Nat.mul_pos hm hr)
        (blockMatrixFlatFin (Lhat t)))
      (fun t => maxEntryNorm (Nat.mul_pos hm hr)
        (blockMatrixFlatFin (U t)))
      (fun t => maxEntryNorm (Nat.mul_pos hm hr) (DeltaFact t)))
    (hSmallProduct : ∀ t,
      (((m * r : ℕ) : ℝ) * Uround.unit t) ≤ 1 / 2)
    (hLdiag : ∀ t, ∀ i : Fin (m * r),
      blockMatrixFlatFin (Lhat t) i i ≠ 0)
    (hLower : ∀ t, ∀ i j : Fin (m * r), i.val < j.val →
      blockMatrixFlatFin (Lhat t) i j = 0)
    (hUUpper : ∀ t, ∀ i j : Fin m, j.val < i.val → U t i j = 0)
    (hDiag : ∀ t, ∀ i : Fin m, ∀ a : Fin r, U t i i a a ≠ 0)
    (hUpper : ∀ t, ∀ i : Fin m, ∀ a b' : Fin r,
      b'.val < a.val → U t i i a b' = 0)
    (hProductTransfer : FamilyLinearRemainderLe l Uround.unit
      (fun t => tableValue * maxEntryNorm (Nat.mul_pos hm hr) (A t))
      (fun t =>
        maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin (Lhat t)) *
          maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin (U t)))) :
    ∃ (DeltaL : ι → Matrix (Fin (m * r)) (Fin (m * r)) ℝ)
      (DeltaU : ι → Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ),
      (∀ t, blockMatrixFlatFin (Lhat t) * blockMatrixFlatFin (U t) =
        A t + DeltaFact t) ∧
      (∀ t,
        (A t +
            (DeltaFact t + DeltaL t * blockMatrixFlatFin (U t) +
              blockMatrixFlatFin (Lhat t) * blockMatrixFlatFin (DeltaU t) +
              DeltaL t * blockMatrixFlatFin (DeltaU t))) *
            blockMatrixRowsFlatFin
              (dhsBlockBackConventionalSolution (fp t) (U t)
                (dhsBlockForwardConventionalSolution (fp t) (Lhat t) (b t))) =
          (fun i (_k : Fin 1) => b t i)) ∧
      FamilyFirstOrderLe l Uround.unit
        (fun t => dn * Uround.unit t *
          ((1 + tableValue) * maxEntryNorm (Nat.mul_pos hm hr) (A t)))
        (fun t => maxEntryNorm (Nat.mul_pos hm hr) (DeltaFact t)) ∧
      FamilyFirstOrderLe l Uround.unit
        (fun t => dn * Uround.unit t *
          ((1 + tableValue) * maxEntryNorm (Nat.mul_pos hm hr) (A t)))
        (fun t => maxEntryNorm (Nat.mul_pos hm hr)
          (DeltaFact t + DeltaL t * blockMatrixFlatFin (U t) +
            blockMatrixFlatFin (Lhat t) * blockMatrixFlatFin (DeltaU t) +
            DeltaL t * blockMatrixFlatFin (DeltaU t))) ∧
      FamilyFirstOrderLe l Uround.unit
        (fun t => dn * Uround.unit t *
          ((1 + tableValue) * maxEntryNorm (Nat.mul_pos hm hr) (A t)))
        (fun t => max
          (maxEntryNorm (Nat.mul_pos hm hr) (DeltaFact t))
          (maxEntryNorm (Nat.mul_pos hm hr)
            (DeltaFact t + DeltaL t * blockMatrixFlatFin (U t) +
              blockMatrixFlatFin (Lhat t) * blockMatrixFlatFin (DeltaU t) +
              DeltaL t * blockMatrixFlatFin (DeltaU t)))) := by
  rcases
      higham13_theorem13_6_implementation1_family_from_partitioned_computation_and_conventional_recursive_solve
        Uround fp hfp hm hr c₁ c₂ c₃ dFact dn A DeltaFact Lhat U b
        hc₁ hc₂ hc₃ hδ hθ hdFact hdSolve hFactComputation hScalar
        hSmallProduct hLdiag hLower hUUpper hDiag hUpper with
    ⟨_DeltaDiag, DeltaL, DeltaU, _hDeltaDiag, _hDeltaL, _hDiagonal,
      hFactSpec, _hForwardEquation, _hBackEquation, hSolveEquation,
      hFactBound, hSolveBound, _hMaxBound⟩
  have hdFact0 : 0 ≤ dFact :=
    le_trans (blockErrorDelta_nonneg q) hδ
  have hdn0 : 0 ≤ dn := le_trans hdFact0 hdFact
  have hTableFact := higham13_table13_1_family_actual_maxEntry
    Uround (Nat.mul_pos hm hr) dn tableValue A
    (fun t => blockMatrixFlatFin (Lhat t))
    (fun t => blockMatrixFlatFin (U t)) DeltaFact hdn0
    hFactBound hProductTransfer
  let DeltaSolve : ι → Matrix (Fin (m * r)) (Fin (m * r)) ℝ := fun t =>
    DeltaFact t + DeltaL t * blockMatrixFlatFin (U t) +
      blockMatrixFlatFin (Lhat t) * blockMatrixFlatFin (DeltaU t) +
      DeltaL t * blockMatrixFlatFin (DeltaU t)
  have hTableSolve : FamilyFirstOrderLe l Uround.unit
      (fun t => dn * Uround.unit t *
        ((1 + tableValue) * maxEntryNorm (Nat.mul_pos hm hr) (A t)))
      (fun t => maxEntryNorm (Nat.mul_pos hm hr) (DeltaSolve t)) := by
    exact higham13_table13_1_family_actual_maxEntry
      Uround (Nat.mul_pos hm hr) dn tableValue A
      (fun t => blockMatrixFlatFin (Lhat t))
      (fun t => blockMatrixFlatFin (U t)) DeltaSolve hdn0
      (by simpa only [DeltaSolve] using hSolveBound) hProductTransfer
  have hTableMax := FamilyFirstOrderLe.combineMax hTableFact hTableSolve
  refine ⟨DeltaL, DeltaU, hFactSpec.equation, hSolveEquation,
    hTableFact, ?_, ?_⟩
  · simpa only [DeltaSolve] using hTableSolve
  · exact (hTableMax.mono_leading (fun _ => (max_self _).le)).mono_value
      (fun _ => le_rfl)



/-- Higham, 2nd ed., Chapter 13, Table 13.1:
    generic scalar bridge from a product bound to the first-order backward-error
    quantity tabulated in the table.

    If Theorem 13.6 has supplied
    `err ≤ c_n u (‖A‖ + ‖L‖‖U‖) + O(u^2)` and a matrix class has supplied
    `‖L‖‖U‖ ≤ tableValue * ‖A‖`, then the table entry gives the corresponding
    first-order bound with leading term
    `c_n u ((1 + tableValue) * ‖A‖)`.  The source's `c_n` absorbs dimension-only
    polynomial factors; this theorem keeps the exact scalar leading term visible
    instead of hiding it in prose. -/
theorem higham13_table13_1_backward_error_from_product_bound
    (err u c_n normA normLU tableValue : ℝ)
    (hu : 0 ≤ u) (hc : 0 ≤ c_n)
    (hErr : FirstOrderLe u (c_n * u * (normA + normLU)) err)
    (hLU : normLU ≤ tableValue * normA) :
    FirstOrderLe u (c_n * u * ((1 + tableValue) * normA)) err := by
  refine hErr.mono_leading ?_
  have hinside : normA + normLU ≤ (1 + tableValue) * normA := by
    nlinarith
  have hcoef : 0 ≤ c_n * u := mul_nonneg hc hu
  exact mul_le_mul_of_nonneg_left hinside hcoef

/-- Higham, 2nd ed., Chapter 13, Table 13.1:
    column block-diagonal-dominance row.

    From a Theorem 13.6-style first-order backward-error premise and the
    source product premises `‖L‖ ≤ m`, `‖U‖ ≤ m^2 ‖A‖`, the table's visible
    leading term is `c_n u (1 + m^3) ‖A‖`.  The Schur-stage proof of those
    product premises remains separate. -/
theorem higham13_table13_1_col_bdd_backward_error
    (err u c_n normA normL normU : ℝ) (m : ℕ)
    (hu : 0 ≤ u) (hc : 0 ≤ c_n) (hU : 0 ≤ normU)
    (hErr : FirstOrderLe u (c_n * u * (normA + normL * normU)) err)
    (hNormL : normL ≤ (m : ℝ))
    (hNormU : normU ≤ (m : ℝ) ^ 2 * normA) :
    FirstOrderLe u (c_n * u * ((1 + (m : ℝ) ^ 3) * normA)) err := by
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hLU : normL * normU ≤ (m : ℝ) ^ 3 * normA := by
    calc
      normL * normU ≤ (m : ℝ) * normU :=
        mul_le_mul_of_nonneg_right hNormL hU
      _ ≤ (m : ℝ) * ((m : ℝ) ^ 2 * normA) :=
        mul_le_mul_of_nonneg_left hNormU hm
      _ = (m : ℝ) ^ 3 * normA := by ring
  exact higham13_table13_1_backward_error_from_product_bound
    err u c_n normA (normL * normU) ((m : ℝ) ^ 3) hu hc hErr hLU

/-- Higham, 2nd ed., Chapter 13, Table 13.1:
    point column-diagonal-dominance row.

    From the source product premises `‖L‖ ≤ 1`, `‖U‖ ≤ 2 ‖A‖`, the table's
    first-order leading term is `c_n u (3 ‖A‖)`. -/
theorem higham13_table13_1_point_col_bdd_backward_error
    (err u c_n normA normL normU : ℝ)
    (hu : 0 ≤ u) (hc : 0 ≤ c_n)
    (hU : 0 ≤ normU)
    (hErr : FirstOrderLe u (c_n * u * (normA + normL * normU)) err)
    (hNormL : normL ≤ 1)
    (hNormU : normU ≤ 2 * normA) :
    FirstOrderLe u (c_n * u * ((1 + 2) * normA)) err := by
  have hLU : normL * normU ≤ 2 * normA := by
    have hmul := mul_le_mul hNormL hNormU hU (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  exact higham13_table13_1_backward_error_from_product_bound
    err u c_n normA (normL * normU) 2 hu hc hErr hLU

/-- Higham, 2nd ed., Chapter 13, Table 13.1:
    point row-diagonal-dominance row, via equation (13.23).

    This keeps the Problem 13.4/Eq.13.21 product premises explicit through the
    growth-factor hypotheses used by `higham13_eq13_23_point_row_from_growth`. -/
theorem higham13_table13_1_point_row_backward_error_from_growth
    (err u c_n normA normL normU rho kappa : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (hc : 0 ≤ c_n)
    (hU : 0 ≤ normU) (hA : 0 ≤ normA)
    (hRho_nonneg : 0 ≤ rho) (hRho_le_two : rho ≤ 2)
    (hKappa : 0 ≤ kappa)
    (hErr : FirstOrderLe u (c_n * u * (normA + normL * normU)) err)
    (hNormL : normL ≤ (n : ℝ) * rho ^ 2 * kappa)
    (hNormU : normU ≤ rho * normA) :
    FirstOrderLe u
      (c_n * u * ((1 + 8 * (n : ℝ) * kappa) * normA)) err := by
  have hLU :=
    higham13_eq13_23_point_row_from_growth
      normL normU normA rho kappa n hU hA hRho_nonneg hRho_le_two hKappa
      hNormL hNormU
  exact higham13_table13_1_backward_error_from_product_bound
    err u c_n normA (normL * normU) (8 * (n : ℝ) * kappa) hu hc hErr hLU

/-- Higham, 2nd ed., Chapter 13, Table 13.1:
    arbitrary-matrix row, via equation (13.22).

    The printed table records the factor `ρ_n^3 κ(A)` and absorbs
    dimension-only polynomial factors into `c_n`.  This scalar wrapper keeps the
    exact Eq. (13.22) dimension factor visible in the leading term:
    `c_n u (1 + n ρ_n^3 κ(A)) ‖A‖`.  Deriving the growth-factor and
    condition-number premises remains the separate Problem 13.4/Eq.13.21
    obligation. -/
theorem higham13_table13_1_arbitrary_backward_error_from_growth
    (err u c_n normA normL normU rho kappa : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (hc : 0 ≤ c_n)
    (hU : 0 ≤ normU) (hRho_nonneg : 0 ≤ rho) (hKappa : 0 ≤ kappa)
    (hErr : FirstOrderLe u (c_n * u * (normA + normL * normU)) err)
    (hNormL : normL ≤ (n : ℝ) * rho ^ 2 * kappa)
    (hNormU : normU ≤ rho * normA) :
    FirstOrderLe u
      (c_n * u * ((1 + (n : ℝ) * rho ^ 3 * kappa) * normA)) err := by
  have hLU :
      normL * normU ≤ (n : ℝ) * rho ^ 3 * kappa * normA :=
    block_lu_normLU_bound_general_higham_13_22
      normL normU normA rho kappa n hU hRho_nonneg hKappa hNormL hNormU
  exact higham13_table13_1_backward_error_from_product_bound
    err u c_n normA (normL * normU) ((n : ℝ) * rho ^ 3 * kappa)
    hu hc hErr hLU

/-- Higham, 2nd ed., Chapter 13, Table 13.1:
    block row-diagonal-dominance row, via the same growth-factor route as the
    arbitrary-matrix row.

    The source discussion notes that row block diagonal dominance does not
    control `‖L‖`; the row therefore inherits the general Eq. (13.22) product
    mechanism.  As above, the theorem keeps the exact dimension factor visible
    instead of hiding it in the table's dimension-dependent constant. -/
theorem higham13_table13_1_block_row_bdd_backward_error_from_growth
    (err u c_n normA normL normU rho kappa : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (hc : 0 ≤ c_n)
    (hU : 0 ≤ normU) (hRho_nonneg : 0 ≤ rho) (hKappa : 0 ≤ kappa)
    (hErr : FirstOrderLe u (c_n * u * (normA + normL * normU)) err)
    (hNormL : normL ≤ (n : ℝ) * rho ^ 2 * kappa)
    (hNormU : normU ≤ rho * normA) :
    FirstOrderLe u
      (c_n * u * ((1 + (n : ℝ) * rho ^ 3 * kappa) * normA)) err :=
  higham13_table13_1_arbitrary_backward_error_from_growth
    err u c_n normA normL normU rho kappa n hu hc hU hRho_nonneg hKappa hErr
    hNormL hNormU

/-- Higham, 2nd ed., Chapter 13, Table 13.1:
    SPD row, via equation (13.24).

    From the source SPD product premises
    `‖L‖₂ ≤ 1 + m κ₂(A)^{1/2}` and `‖U‖₂ ≤ √m ‖A‖₂`, the table's first-order
    leading term is
    `c_n u (1 + √m(1 + m κ₂(A)^{1/2})) ‖A‖₂`. -/
theorem higham13_table13_1_spd_backward_error
    (err u c_n normA2 normL2 normU2 kappa2 : ℝ) (m : ℕ)
    (hu : 0 ≤ u) (hc : 0 ≤ c_n)
    (hU : 0 ≤ normU2)
    (hErr : FirstOrderLe u (c_n * u * (normA2 + normL2 * normU2)) err)
    (hNormL : normL2 ≤ 1 + (m : ℝ) * Real.sqrt kappa2)
    (hNormU : normU2 ≤ Real.sqrt (m : ℝ) * normA2) :
    FirstOrderLe u
      (c_n * u *
        ((1 + Real.sqrt (m : ℝ) * (1 + (m : ℝ) * Real.sqrt kappa2)) *
          normA2)) err := by
  have hLbound_nonneg : 0 ≤ 1 + (m : ℝ) * Real.sqrt kappa2 := by
    linarith [mul_nonneg (Nat.cast_nonneg m) (Real.sqrt_nonneg kappa2)]
  have hLU : normL2 * normU2 ≤
      Real.sqrt (m : ℝ) * (1 + (m : ℝ) * Real.sqrt kappa2) * normA2 := by
    have hmul := mul_le_mul hNormL hNormU hU hLbound_nonneg
    calc
      normL2 * normU2
          ≤ (1 + (m : ℝ) * Real.sqrt kappa2) *
              (Real.sqrt (m : ℝ) * normA2) := hmul
      _ = Real.sqrt (m : ℝ) * (1 + (m : ℝ) * Real.sqrt kappa2) * normA2 := by
        ring
  exact higham13_table13_1_backward_error_from_product_bound
    err u c_n normA2 (normL2 * normU2)
      (Real.sqrt (m : ℝ) * (1 + (m : ℝ) * Real.sqrt kappa2)) hu hc hErr hLU

/-- **Block column diagonal-dominance stability** (Table 13.1, p. 256):
    ‖L‖ ≤ m and ‖U‖ ≤ m² · ‖A‖ so ‖L‖ · ‖U‖ ≤ m³ · ‖A‖.
    From Theorems 13.7--13.8: each sub-diagonal block column of L has norm ≤ 1
    (by eq. 13.17 + 13.19), so ‖L‖ ≤ m; each block of U satisfies
    ‖U_{ij}‖ ≤ 2‖A‖ (by Theorem 13.8), so ‖U‖ ≤ m² · 2‖A‖ (crude).
    The table value of "1" means unconditionally stable (polynomial factors in cₙ). -/
theorem block_lu_stability_block_diagDom_col
    (normL normU normA : ℝ) (m : ℕ)
    (_hL : 0 ≤ normL) (hU : 0 ≤ normU) (_hA : 0 ≤ normA)
    (hm : 0 ≤ (m : ℝ))
    -- From Thm 13.7 + eq. 13.17+13.19: ‖L‖ ≤ m
    (hNormL : normL ≤ (m : ℝ))
    -- From Thm 13.8 + eq. 13.19: each block of U bounded, giving ‖U‖ ≤ bound
    (normU_bound : ℝ) (_hUBound : 0 ≤ normU_bound)
    (hNormU : normU ≤ normU_bound) :
    normL * normU ≤ (m : ℝ) * normU_bound :=
  mul_le_mul hNormL hNormU hU hm

/-- Higham, 2nd ed., Chapter 13, §13.3.1, p. 254:
    source one-norm refinement for column block diagonal dominance.  From the
    source-derived premises `‖L‖₁ ≤ m` and `‖U‖₁ ≤ 2‖A‖₁`, the displayed
    product bound `‖L‖₁‖U‖₁ ≤ 2m‖A‖₁` is just scalar algebra. -/
theorem higham13_col_bdd_oneNorm_stability_bound
    (normL normU normA : ℝ) (m : ℕ)
    (hU : 0 ≤ normU)
    (hNormL : normL ≤ (m : ℝ))
    (hNormU : normU ≤ 2 * normA) :
    normL * normU ≤ 2 * (m : ℝ) * normA := by
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  calc
    normL * normU ≤ (m : ℝ) * normU :=
      mul_le_mul_of_nonneg_right hNormL hU
    _ ≤ (m : ℝ) * (2 * normA) :=
      mul_le_mul_of_nonneg_left hNormU hm
    _ = 2 * (m : ℝ) * normA := by ring

/-- Higham, 2nd ed., Chapter 13, §13.3.1, p. 254:
    source infinity-norm refinement for column block diagonal dominance.  From
    `‖L‖∞ ≤ m` and `‖U‖∞ ≤ 2m‖A‖∞`, the printed product bound
    `‖L‖∞‖U‖∞ ≤ 2m^2‖A‖∞` follows. -/
theorem higham13_col_bdd_infNorm_stability_bound
    (normL normU normA : ℝ) (m : ℕ)
    (hU : 0 ≤ normU)
    (hNormL : normL ≤ (m : ℝ))
    (hNormU : normU ≤ 2 * (m : ℝ) * normA) :
    normL * normU ≤ 2 * (m : ℝ) ^ 2 * normA := by
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  calc
    normL * normU ≤ (m : ℝ) * normU :=
      mul_le_mul_of_nonneg_right hNormL hU
    _ ≤ (m : ℝ) * (2 * (m : ℝ) * normA) :=
      mul_le_mul_of_nonneg_left hNormU hm
    _ = 2 * (m : ℝ) ^ 2 * normA := by ring

/-- **Block row diagonal-dominance stability** (Table 13.1):
    For block row diag dominant: ‖U‖ ≤ 2‖A‖ (Thm 13.8) but ‖L‖ can be
    arbitrarily large. With growth factor ρ_n:
    ‖L‖ · ‖U‖ ≤ n · ρ_n³ · κ(A) · ‖A‖ (eq. 13.22). -/
theorem block_lu_stability_block_diagDom_row
    (normL normU normA rho kappa : ℝ) (n : ℕ)
    (_hL : 0 ≤ normL) (hU : 0 ≤ normU)
    (_hA : 0 ≤ normA) (_hRho : 0 ≤ rho) (hKappa : 0 ≤ kappa)
    -- ‖U‖ ≤ 2‖A‖ from Thm 13.8
    (hNormU : normU ≤ 2 * normA)
    -- ‖L‖ bounded by ρ_n³ · κ(A) · n (worst case, from eq. 13.22)
    (hNormL : normL ≤ (n : ℝ) * rho ^ 2 * kappa) :
    normL * normU ≤ 2 * (n : ℝ) * rho ^ 2 * kappa * normA := by
  have hLU := mul_le_mul hNormL hNormU hU
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg rho)) hKappa)
  nlinarith

/-- Scalar-block specialization of Higham's row-dominant large-`L` example:
    `A = [[eps, 0], [1/2, 1]]`. -/
noncomputable def higham13_rowdom_largeL_A (eps : ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun i j =>
    if i = 0 then
      if j = 0 then eps else 0
    else
      if j = 0 then (1 / 2 : ℝ) else 1

/-- The corresponding lower factor
    `L = [[1, 0], [1/(2 eps), 1]]`. -/
noncomputable def higham13_rowdom_largeL_L (eps : ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun i j =>
    if i = 0 then
      if j = 0 then 1 else 0
    else
      if j = 0 then 1 / (2 * eps) else 1

/-- The corresponding upper factor `U = [[eps, 0], [0, 1]]`. -/
noncomputable def higham13_rowdom_largeL_U (eps : ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun i j =>
    if i = 0 then
      if j = 0 then eps else 0
    else
      if j = 0 then 0 else 1

/-- Higham, 2nd ed., Chapter 13, p. 254: the scalar-block example is row block
    diagonally dominant.  The scalar block norm is absolute value, and the
    diagonal inverse-norm reciprocal is the absolute diagonal entry. -/
theorem higham13_rowdom_largeL_row_block_diag_dom (eps : ℝ) :
    IsBlockDiagDomRow 2
      (fun i j : Fin 2 => |higham13_rowdom_largeL_A eps i j|)
      (fun i : Fin 2 => |higham13_rowdom_largeL_A eps i i|) := by
  intro i
  fin_cases i
  · simp [higham13_rowdom_largeL_A]
  · norm_num [higham13_rowdom_largeL_A]

/-- Higham's displayed factorization for the scalar-block row-dominant example:
    `[[eps,0],[1/2,1]] = [[1,0],[1/(2eps),1]][[eps,0],[0,1]]`. -/
theorem higham13_rowdom_largeL_reconstructs (eps : ℝ) (heps : eps ≠ 0) :
    ∀ i j : Fin 2,
      ∑ k : Fin 2,
        higham13_rowdom_largeL_L eps i k * higham13_rowdom_largeL_U eps k j =
          higham13_rowdom_largeL_A eps i j := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_two, higham13_rowdom_largeL_A, higham13_rowdom_largeL_L,
      higham13_rowdom_largeL_U]
  field_simp [heps]

/-- The subdiagonal entry of the lower factor is `1/(2 eps)`. -/
theorem higham13_rowdom_largeL_subdiagonal_entry (eps : ℝ) :
    higham13_rowdom_largeL_L eps 1 0 = 1 / (2 * eps) := by
  norm_num [higham13_rowdom_largeL_L]

/-- Higham, 2nd ed., Chapter 13, p. 254: in the row block diagonally dominant
    family, the lower factor can be arbitrarily large.  For every nonnegative
    threshold `M`, choose `eps = 1/(2(M+1))`; then the subdiagonal entry of `L`
    has absolute value `M+1`. -/
theorem higham13_rowdom_largeL_arbitrarily_large (M : ℝ) (hM : 0 ≤ M) :
    ∃ eps : ℝ, eps ≠ 0 ∧
      M < |higham13_rowdom_largeL_L eps 1 0| := by
  let eps : ℝ := 1 / (2 * (M + 1))
  have hM1pos : 0 < M + 1 := by linarith
  have heps_ne : eps ≠ 0 := by
    exact ne_of_gt (by positivity)
  have hLval : higham13_rowdom_largeL_L eps 1 0 = M + 1 := by
    simp [higham13_rowdom_largeL_L, eps]
    field_simp [hM1pos.ne']
  refine ⟨eps, heps_ne, ?_⟩
  rw [hLval, abs_of_pos hM1pos]
  linarith

/-- **Point row diagonal-dominance stability** (Table 13.1, eq. 13.23):
    For point row diag dominant: ρ_n ≤ 2, ‖L‖ ≤ n · 4 · κ(A),
    so ‖L‖ · ‖U‖ ≤ 8nκ(A) · ‖A‖. -/
theorem block_lu_stability_point_diagDom_row
    (normL normU normA kappa : ℝ) (n : ℕ)
    (_hL : 0 ≤ normL) (hU : 0 ≤ normU) (_hA : 0 ≤ normA)
    (hKappa : 0 ≤ kappa)
    (hNormL : normL ≤ 4 * (n : ℝ) * kappa)
    (hNormU : normU ≤ 2 * normA) :
    normL * normU ≤ 8 * (n : ℝ) * kappa * normA := by
  have hLU := mul_le_mul hNormL hNormU hU (by positivity)
  nlinarith

/-- **SPD stability** (Table 13.1, eq. 13.24):
    ‖L‖₂ · ‖U‖₂ ≤ √m · (1 + m · κ₂(A)^{1/2}) · ‖A‖₂.
    From Lemmas 13.9--13.10: each sub-diagonal block of L bounded in 2-norm
    by κ₂(A)^{1/2}, so ‖L‖₂ ≤ 1 + mκ₂(A)^{1/2}. Also ‖U‖₂ ≤ √m · ‖A‖₂. -/
theorem block_lu_stability_spd
    (normL2 normU2 normA2 kappa2 : ℝ) (m : ℕ)
    (hU : 0 ≤ normU2)
    (hNormL : normL2 ≤ 1 + (m : ℝ) * Real.sqrt kappa2)
    (hNormU : normU2 ≤ Real.sqrt (m : ℝ) * normA2) :
    normL2 * normU2 ≤
      (1 + (m : ℝ) * Real.sqrt kappa2) * (Real.sqrt (m : ℝ) * normA2) :=
  mul_le_mul hNormL hNormU hU
    (by linarith [Real.sqrt_nonneg kappa2,
      mul_nonneg (Nat.cast_nonneg m) (Real.sqrt_nonneg kappa2)])
end NumStability
