import NumStability.Algorithms.TestMatrices.Higham28PascalSpectral
import NumStability.Algorithms.TestMatrices.Higham28PascalTotalPositivity
import NumStability.Analysis.TestMatrices.Pascal.PascalOscillation
import NumStability.Source.Higham.Chapter28.Section04.Pascal.PascalOscillation

/-!
# Higham28PascalOscillation (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.TestMatrices.Higham28PascalOscillation`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

namespace NumStability

open scoped BigOperators

open Set

@[simp]
theorem pascalSortedEigenbasis_apply (n : ℕ) (i : Fin n) :
    ⇑(pascalSortedEigenbasis n i) = pascalSortedEigenvector n i := by
  let hP := IsSymmetricFiniteMatrix.to_matrix_isHermitian
    (pascalMatrix n) (pascalMatrix_isSymmetricFiniteMatrix n)
  have h := OrthonormalBasis.reindex_apply hP.eigenvectorBasis
    (pascalSortedEigenEquiv n).symm i
  change ⇑((hP.eigenvectorBasis.reindex
    (pascalSortedEigenEquiv n).symm) i) =
      ⇑(hP.eigenvectorBasis (pascalSortedEigenIndex n i))
  have h' : (hP.eigenvectorBasis.reindex
      (pascalSortedEigenEquiv n).symm) i =
      hP.eigenvectorBasis (pascalSortedEigenIndex n i) := by
    simpa using h
  exact congrArg (fun x : EuclideanSpace ℝ (Fin n) => ⇑x) h'

@[simp]
theorem pascalSortedEigenvectorMatrix_apply (n : ℕ) (i j : Fin n) :
    pascalSortedEigenvectorMatrix n i j = pascalSortedEigenvector n j i := by
  change (EuclideanSpace.basisFun (Fin n) ℝ).repr
      ((pascalSortedEigenbasis n).toBasis j) i = _
  rw [EuclideanSpace.basisFun_repr]
  exact congrFun (pascalSortedEigenbasis_apply n j) i

theorem pascalMatrix_mul_sortedEigenvectorMatrix (n : ℕ) :
    pascalMatrix n * pascalSortedEigenvectorMatrix n =
      pascalSortedEigenvectorMatrix n * pascalSortedEigenvalueDiagonal n := by
  ext i j
  have heig := congrFun (pascalMatrix_mulVec_sortedEigenvector j) i
  rw [Matrix.mul_apply]
  have hrhs :
      (pascalSortedEigenvectorMatrix n *
        pascalSortedEigenvalueDiagonal n) i j =
          pascalSortedEigenvector n j i * pascalSortedEigenvalue n j := by
    rw [Matrix.mul_apply]
    simp [pascalSortedEigenvalueDiagonal,
      Matrix.diagonal_apply, pascalSortedEigenvectorMatrix_apply]
  rw [hrhs]
  simpa [Matrix.mulVec, dotProduct,
    pascalSortedEigenvectorMatrix_apply, mul_comm] using heig

theorem compoundMatrix_pascal_pos
    {n k : ℕ} (hk : 0 < k)
    (s t : Set.powersetCard (Fin n) k) :
    0 < compoundMatrix n k (pascalMatrix n) s t := by
  rw [compoundMatrix_apply]
  exact pascalMatrix_isStrictlyTotallyPositive n k hk
    (Set.powersetCard.ofFinEmbEquiv.symm s)
    (Set.powersetCard.ofFinEmbEquiv.symm t)
    (Set.powersetCard.ofFinEmbEquiv.symm s).strictMono
    (Set.powersetCard.ofFinEmbEquiv.symm t).strictMono

theorem compoundMatrix_pascal_mul_leadingPlucker
    {n k : ℕ} (hkn : k ≤ n) :
    Matrix.mulVec (compoundMatrix n k (pascalMatrix n))
        (pascalLeadingPlucker n k hkn) =
      pascalLeadingEigenvalueProduct n k hkn •
        pascalLeadingPlucker n k hkn := by
  have hmat :
      compoundMatrix n k (pascalMatrix n) *
          compoundMatrix n k (pascalSortedEigenvectorMatrix n) =
        compoundMatrix n k (pascalSortedEigenvectorMatrix n) *
          compoundMatrix n k (pascalSortedEigenvalueDiagonal n) := by
    calc
      compoundMatrix n k (pascalMatrix n) *
          compoundMatrix n k (pascalSortedEigenvectorMatrix n) =
        compoundMatrix n k
          (pascalMatrix n * pascalSortedEigenvectorMatrix n) := by
            rw [compoundMatrix_mul]
      _ = compoundMatrix n k
          (pascalSortedEigenvectorMatrix n *
            pascalSortedEigenvalueDiagonal n) := by
              rw [pascalMatrix_mul_sortedEigenvectorMatrix]
      _ = compoundMatrix n k (pascalSortedEigenvectorMatrix n) *
          compoundMatrix n k (pascalSortedEigenvalueDiagonal n) := by
            rw [compoundMatrix_mul]
  funext s
  have hs := congrArg
    (fun M : Matrix (Set.powersetCard (Fin n) k)
      (Set.powersetCard (Fin n) k) ℝ => M s (initialPowerset hkn)) hmat
  simp only [Matrix.mul_apply] at hs
  simpa [Matrix.mulVec, dotProduct, pascalLeadingPlucker,
    compoundMatrix_sortedEigenvalueDiagonal_initial_column,
    Pi.smul_apply, smul_eq_mul, mul_comm] using hs

end NumStability
