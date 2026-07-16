/-
  Algorithms/LU/BlockLUTable13_1Families.lean

  Source-derived uniform endpoints for Higham Table 13.1.

  The generic family adapter in `BlockLUFirstOrderFamilies` is intentionally
  small, but by itself it accepts both the completed Theorem 13.6 estimate
  and a completed product transfer.  This module supplies the missing source
  composition: the concrete Implementation-1 theorem is executed here, and
  the class rows below derive product transfers from their printed component
  bounds rather than accepting the final product inequality.
-/

import LeanFpAnalysis.FP.Algorithms.LU.BlockLUComputationSourceClosure
import LeanFpAnalysis.FP.Algorithms.LU.BlockLUSPDFamilies

namespace LeanFpAnalysis.FP

open Filter Asymptotics
open scoped Topology

/-! ## Product transfers derived from the source row data -/

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

/-- Equation (13.25) for the actual conventional Implementation-1 solve,
with Theorem 13.6 derived rather than supplied.

The max-entry concrete theorem is converted to the exact Euclidean operator
norm with its explicit scalar-dimension factor.  Equation (13.24) then derives
the SPD factor-product class bound internally.  The sole comparison premise
left is the source's explicit first-order exact/computed product comparison. -/
theorem
    higham13_eq13_25_implementation1_spd_family_from_partitioned_computation
    {ι : Type*} {l : Filter ι} (Uround : RoundoffFamily ι l)
    (fp : ι → FPModel) (hfp : ∀ t, (fp t).u = Uround.unit t)
    {m r q : ℕ} (hm : 0 < m) (hr : 0 < r)
    (c₁ c₂ c₃ dFact dn : ℝ)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hSPD : IsSymPosDef (m * r) (blockMatrixFlatFin Ablk))
    (DeltaFact : ι → Matrix (Fin (m * r)) (Fin (m * r)) ℝ)
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
        (maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
        (maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin (Lhat t)))
        (maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin (U t)))
        (maxEntryNorm (Nat.mul_pos hm hr) (DeltaFact t))
        (blockMatrixFlatFin Ablk) (DeltaFact t)
        (blockMatrixFlatFin (Lhat t)) (blockMatrixFlatFin (U t)))
    (hScalar : Higham13PartitionedLUScalarFamilyComputation
      Uround c₁ c₂ c₃ q
      (fun _t => maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Ablk))
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
      (fun _ =>
        opNorm2
            (blockMatrixFlatFin
              (higham13_algorithm13_3_lowerFromMatrixStages Ablk
                (Classical.choose
                  (higham13_eq13_24_algorithm13_3_spd hr Ablk hSPD)))) *
          opNorm2
            (blockMatrixFlatFin
              (higham13_algorithm13_3_upperFromMatrixStages Ablk
                (Classical.choose
                  (higham13_eq13_24_algorithm13_3_spd hr Ablk hSPD)))))
      (fun t =>
        opNorm2 (blockMatrixFlatFin (Lhat t)) *
          opNorm2 (blockMatrixFlatFin (U t)))) :
    ∃ (DeltaL : ι → Matrix (Fin (m * r)) (Fin (m * r)) ℝ)
      (DeltaU : ι → Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ),
      (∀ t, blockMatrixFlatFin (Lhat t) * blockMatrixFlatFin (U t) =
        blockMatrixFlatFin Ablk + DeltaFact t) ∧
      (∀ t,
        (blockMatrixFlatFin Ablk +
            (DeltaFact t + DeltaL t * blockMatrixFlatFin (U t) +
              blockMatrixFlatFin (Lhat t) * blockMatrixFlatFin (DeltaU t) +
              DeltaL t * blockMatrixFlatFin (DeltaU t))) *
            blockMatrixRowsFlatFin
              (dhsBlockBackConventionalSolution (fp t) (U t)
                (dhsBlockForwardConventionalSolution (fp t) (Lhat t) (b t))) =
          (fun i (_k : Fin 1) => b t i)) ∧
      FamilyFirstOrderLe l Uround.unit
        (fun t => (((m * r : ℕ) : ℝ) * dn) * Real.sqrt (m : ℝ) *
          Uround.unit t * opNorm2 (blockMatrixFlatFin Ablk) *
          (2 + (m : ℝ) *
            Real.sqrt
              (kappa2 (blockMatrixFlatFin Ablk)
                (nonsingInv (m * r) (blockMatrixFlatFin Ablk)))))
        (fun t => opNorm2 (DeltaFact t)) ∧
      FamilyFirstOrderLe l Uround.unit
        (fun t => (((m * r : ℕ) : ℝ) * dn) * Real.sqrt (m : ℝ) *
          Uround.unit t * opNorm2 (blockMatrixFlatFin Ablk) *
          (2 + (m : ℝ) *
            Real.sqrt
              (kappa2 (blockMatrixFlatFin Ablk)
                (nonsingInv (m * r) (blockMatrixFlatFin Ablk)))))
        (fun t => opNorm2
          (DeltaFact t + DeltaL t * blockMatrixFlatFin (U t) +
            blockMatrixFlatFin (Lhat t) * blockMatrixFlatFin (DeltaU t) +
            DeltaL t * blockMatrixFlatFin (DeltaU t))) ∧
      FamilyFirstOrderLe l Uround.unit
        (fun t => (((m * r : ℕ) : ℝ) * dn) * Real.sqrt (m : ℝ) *
          Uround.unit t * opNorm2 (blockMatrixFlatFin Ablk) *
          (2 + (m : ℝ) *
            Real.sqrt
              (kappa2 (blockMatrixFlatFin Ablk)
                (nonsingInv (m * r) (blockMatrixFlatFin Ablk)))))
        (fun t => max (opNorm2 (DeltaFact t))
          (opNorm2
            (DeltaFact t + DeltaL t * blockMatrixFlatFin (U t) +
              blockMatrixFlatFin (Lhat t) * blockMatrixFlatFin (DeltaU t) +
              DeltaL t * blockMatrixFlatFin (DeltaU t)))) := by
  let A : ι → Matrix (Fin (m * r)) (Fin (m * r)) ℝ :=
    fun _t => blockMatrixFlatFin Ablk
  rcases
      higham13_theorem13_6_implementation1_family_from_partitioned_computation_and_conventional_recursive_solve
        Uround fp hfp hm hr c₁ c₂ c₃ dFact dn A DeltaFact Lhat U b
        hc₁ hc₂ hc₃ hδ hθ hdFact hdSolve
        (by simpa only [A] using hFactComputation)
        (by simpa only [A] using hScalar)
        hSmallProduct hLdiag hLower hUUpper hDiag hUpper with
    ⟨_DeltaDiag, DeltaL, DeltaU, _hDeltaDiag, _hDeltaL, _hDiagonal,
      hFactSpec, _hForwardEquation, _hBackEquation, hSolveEquation,
      hFactMax, hSolveMax, _hBothMax⟩
  have hdFact0 : 0 ≤ dFact :=
    le_trans (blockErrorDelta_nonneg q) hδ
  have hdn0 : 0 ≤ dn := le_trans hdFact0 hdFact
  let Lflat : ι → Matrix (Fin (m * r)) (Fin (m * r)) ℝ :=
    fun t => blockMatrixFlatFin (Lhat t)
  let Uflat : ι → Matrix (Fin (m * r)) (Fin (m * r)) ℝ :=
    fun t => blockMatrixFlatFin (U t)
  let DeltaSolve : ι → Matrix (Fin (m * r)) (Fin (m * r)) ℝ := fun t =>
    DeltaFact t + DeltaL t * Uflat t +
      Lflat t * blockMatrixFlatFin (DeltaU t) +
      DeltaL t * blockMatrixFlatFin (DeltaU t)
  have hFactOp := higham13_theorem13_6_opNorm2_family_from_maxEntry
    Uround (Nat.mul_pos hm hr) dn A Lflat Uflat DeltaFact hdn0
    (by simpa only [A, Lflat, Uflat] using hFactMax)
  have hSolveOp : FamilyFirstOrderLe l Uround.unit
      (fun t => (((m * r : ℕ) : ℝ) * dn) * Uround.unit t *
        (opNorm2 (A t) + opNorm2 (Lflat t) * opNorm2 (Uflat t)))
      (fun t => opNorm2 (DeltaSolve t)) :=
    higham13_theorem13_6_opNorm2_family_from_maxEntry
      Uround (Nat.mul_pos hm hr) dn A Lflat Uflat DeltaSolve hdn0
      (by simpa only [DeltaSolve, A, Lflat, Uflat] using hSolveMax)
  let xhat : ι → Matrix (Fin (m * r)) (Fin 1) ℝ := fun t =>
    blockMatrixRowsFlatFin
      (dhsBlockBackConventionalSolution (fp t) (U t)
        (dhsBlockForwardConventionalSolution (fp t) (Lhat t) (b t)))
  let bmat : ι → Matrix (Fin (m * r)) (Fin 1) ℝ :=
    fun t i _k => b t i
  have hEq1325 :=
    higham13_eq13_25_algorithm13_3_spd_family_actual_factor_and_solve
      Uround hm hr Ablk hSPD Lflat Uflat DeltaFact DeltaSolve xhat bmat
      (((m * r : ℕ) : ℝ) * dn)
      (mul_nonneg (Nat.cast_nonneg (m * r)) hdn0)
      (by simpa only [A, Lflat, Uflat] using hFactSpec.equation)
      (by simpa only [A, DeltaSolve, xhat, bmat, Lflat, Uflat] using
        hSolveEquation)
      (by simpa only [Lflat, Uflat] using hProductTransfer)
      (by simpa only [A, Lflat, Uflat] using hFactOp)
      (by simpa only [A, Lflat, Uflat] using hSolveOp)
  refine ⟨DeltaL, DeltaU, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Lflat, Uflat] using hEq1325.1
  · simpa only [DeltaSolve, xhat, bmat, Lflat, Uflat] using hEq1325.2.1
  · simpa only using hEq1325.2.2.1
  · simpa only [DeltaSolve] using hEq1325.2.2.2.1
  · simpa only [DeltaSolve] using hEq1325.2.2.2.2

end LeanFpAnalysis.FP
