import LeanFpAnalysis.FP.Algorithms.LU.BlockLU

namespace LeanFpAnalysis.FP

theorem scratch_higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_pivot_right_inverse_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin (m * r)) (Fin (m * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hN : 0 < m * r := Nat.mul_pos hm hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (n : ℝ) *
          (growthFactorEntry hN (blockMatrixFlatFin Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN hm hr Ablk pivotInv) hApos) ^ 2 *
          (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
            maxEntryNormRect hN hN
              (nonsingInv (m * r) (blockMatrixFlatFin Ablk)))) →
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          (n : ℝ) *
            (growthFactorEntry hN (blockMatrixFlatFin Ablk)
              (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
                hN hm hr Ablk pivotInv) hApos) ^ 3 *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro hLower
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
  have hRight :
      IsRightInverse (m * r) (blockMatrixFlatFin Ablk)
        (nonsingInv (m * r) (blockMatrixFlatFin Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero
      (m * r) (blockMatrixFlatFin Ablk) hdet).2
  exact
    higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hPivotRight hApos hRight n hNn hLower

theorem scratch_higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_pivot_right_inverse_of_det_ne_zero
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (Ablk : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hPivotRight : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩)
        (pivotInv k))
    (hdet :
      Matrix.det (blockMatrixFlatFin Ablk :
        Matrix (Fin (m * r)) (Fin (m * r)) ℝ) ≠ 0)
    (n : ℕ) (hNn : ((m * r : ℕ) : ℝ) ≤ (n : ℝ)) :
    let hN : 0 < m * r := Nat.mul_pos hm hr
    let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
      maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
    (∀ i j : Fin m, j.val < i.val →
      maxEntryNorm hr
          (higham13_algorithm13_3_schurStageMatrixBlock Ablk pivotInv j.val i j *
            pivotInv j.val) ≤
        (n : ℝ) *
          (growthFactorEntry hN (blockMatrixFlatFin Ablk)
            (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
              hN hm hr Ablk pivotInv) hApos) ^ 2 *
          (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
            maxEntryNormRect hN hN
              (nonsingInv (m * r) (blockMatrixFlatFin Ablk)))) →
    (growthFactorEntry hN (blockMatrixFlatFin Ablk)
        (higham13_algorithm13_3_matrixStageHistoryGrowthMatrix
          hN hm hr Ablk pivotInv) hApos ≤ 2) →
    ∃ L U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r Ablk L U ∧
        blockMaxNorm hm hr L * blockMaxNorm hm hr U ≤
          8 * (n : ℝ) *
            (maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) *
              maxEntryNormRect hN hN
                (nonsingInv (m * r) (blockMatrixFlatFin Ablk))) *
            maxEntryNormRect hN hN (blockMatrixFlatFin Ablk) := by
  dsimp only
  intro hLower hRho
  let hN : 0 < m * r := Nat.mul_pos hm hr
  let hApos : 0 < maxEntryNorm hN (blockMatrixFlatFin Ablk) :=
    maxEntryNorm_pos_of_det_ne_zero hN (blockMatrixFlatFin Ablk) hdet
  have hRight :
      IsRightInverse (m * r) (blockMatrixFlatFin Ablk)
        (nonsingInv (m * r) (blockMatrixFlatFin Ablk)) :=
    (isInverse_nonsingInv_of_det_ne_zero
      (m * r) (blockMatrixFlatFin Ablk) hdet).2
  exact
    higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_pivot_right_inverse
      hm hr Ablk pivotInv
      (nonsingInv (m * r) (blockMatrixFlatFin Ablk))
      hPivotRight hApos hRight n hNn hLower hRho

end LeanFpAnalysis.FP
