import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Rank
import NumStability.Algorithms.TestMatrices.Higham28Asymptotics
import NumStability.Algorithms.TestMatrices.Higham28Pascal
import NumStability.Algorithms.TestMatrices.Higham28Probability
import NumStability.Algorithms.TestMatrices.Higham28RandsvdNorm
import NumStability.Analysis.TestMatrices.Cauchy.Contracts
import NumStability.Analysis.TestMatrices.Companion.Contracts
import NumStability.Analysis.TestMatrices.Pascal.Contracts
import NumStability.Analysis.TestMatrices.Toeplitz.Contracts
import NumStability.Source.Higham.Chapter09.Problems
import NumStability.Source.Higham.Chapter09.Section01
import NumStability.Source.Higham.Chapter09.Section02
import NumStability.Source.Higham.Chapter09.Section03
import NumStability.Source.Higham.Chapter09.Section04
import NumStability.Source.Higham.Chapter09.Section05
import NumStability.Source.Higham.Chapter09.Section06
import NumStability.Source.Higham.Chapter09.Section08
import NumStability.Source.Higham.Chapter09.Section10
import NumStability.Source.Higham.Chapter09.Section11

/-!
# Higham28Contracts (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.TestMatrices.Higham28Contracts`
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

private theorem sin_neighbor_identity (x θ : ℝ) :
    Real.sin (x - θ) + Real.sin (x + θ) =
      2 * Real.cos θ * Real.sin x := by
  rw [Real.sin_sub, Real.sin_add]
  ring

private theorem toeplitzSineVector_angle
    {n : ℕ} (k i : Fin n) :
    toeplitzSineVector n k i =
      Real.sin (((i.val + 1 : ℕ) : ℝ) *
        ((((k.val + 1 : ℕ) : ℝ) * Real.pi) / ((n + 1 : ℕ) : ℝ))) := by
  unfold toeplitzSineVector
  congr 1
  push_cast
  ring

private theorem toeplitz_sine_boundary
    {n : ℕ} (k : Fin n) :
    Real.sin (((n + 1 : ℕ) : ℝ) *
      ((((k.val + 1 : ℕ) : ℝ) * Real.pi) / ((n + 1 : ℕ) : ℝ))) = 0 := by
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [show (((n + 1 : ℕ) : ℝ) *
      ((((k.val + 1 : ℕ) : ℝ) * Real.pi) / ((n + 1 : ℕ) : ℝ))) =
      ((k.val + 1 : ℕ) : ℝ) * Real.pi by field_simp]
  exact Real.sin_nat_mul_pi (k.val + 1)

/-- Higham, p. 522: the displayed sine vector is an actual eigenvector of the
symmetric tridiagonal Toeplitz matrix.  The trigonometric recurrence and both
boundary cases are proved here, rather than supplied as a hypothesis. -/
theorem symmetricToeplitz_sine_eigenpair
    {n : ℕ} (c d : ℝ) (k : Fin n) :
    Matrix.mulVec (tridiagonalToeplitz n c d c)
        (toeplitzSineVector n k) =
      symmetricToeplitzEigenvalue n c d k • toeplitzSineVector n k := by
  funext i
  rw [tridiagonalToeplitz_mulVec_apply]
  rw [show symmetricToeplitzEigenvalue n c d k =
      d + 2 * c * Real.cos
        (((k.val + 1 : ℕ) : ℝ) * Real.pi / ((n + 1 : ℕ) : ℝ)) by rfl]
  simp only [Pi.smul_apply, smul_eq_mul]
  simp_rw [toeplitzSineVector_angle]
  let θ : ℝ := (((k.val + 1 : ℕ) : ℝ) * Real.pi) / ((n + 1 : ℕ) : ℝ)
  let x : ℝ := ((i.val + 1 : ℕ) : ℝ) * θ
  rw [show (((k.val + 1 : ℕ) : ℝ) * Real.pi / ((n + 1 : ℕ) : ℝ)) = θ by rfl]
  by_cases hs : i.val + 1 < n
  · by_cases hp : 0 < i.val
    · simp only [hs, hp, ↓reduceDIte]
      have hcur : ((i.val + 1 : ℕ) : ℝ) * θ = x := rfl
      have hsucc :
          ((i.val + 1 + 1 : ℕ) : ℝ) * θ = x + θ := by
        dsimp [x]
        push_cast
        ring
      have hpred :
          ((i.val - 1 + 1 : ℕ) : ℝ) * θ = x - θ := by
        rw [Nat.sub_add_cancel hp]
        dsimp [x]
        push_cast
        ring
      change d * Real.sin (((i.val + 1 : ℕ) : ℝ) * θ) +
          c * Real.sin (((i.val + 1 + 1 : ℕ) : ℝ) * θ) +
          c * Real.sin (((i.val - 1 + 1 : ℕ) : ℝ) * θ) =
        (d + 2 * c * Real.cos θ) *
          Real.sin (((i.val + 1 : ℕ) : ℝ) * θ)
      rw [hcur, hsucc, hpred]
      have hrec := sin_neighbor_identity x θ
      linear_combination c * hrec
    · have hi0 : i.val = 0 := by omega
      simp only [hs, hp, ↓reduceDIte]
      change d * Real.sin (((i.val + 1 : ℕ) : ℝ) * θ) +
          c * Real.sin (((i.val + 1 + 1 : ℕ) : ℝ) * θ) + 0 =
        (d + 2 * c * Real.cos θ) *
          Real.sin (((i.val + 1 : ℕ) : ℝ) * θ)
      rw [hi0]
      norm_num
      rw [show 2 * θ = θ + θ by ring, Real.sin_add]
      ring
  · have hilast : i.val + 1 = n := by omega
    by_cases hp : 0 < i.val
    · simp only [hs, hp, ↓reduceDIte]
      have hcur : ((i.val + 1 : ℕ) : ℝ) * θ = x := rfl
      have hpred :
          ((i.val - 1 + 1 : ℕ) : ℝ) * θ = x - θ := by
        rw [Nat.sub_add_cancel hp]
        dsimp [x]
        push_cast
        ring
      have hboundary : Real.sin (x + θ) = 0 := by
        rw [show x + θ = ((n + 1 : ℕ) : ℝ) * θ by
          dsimp [x]
          rw [show ((i.val + 1 : ℕ) : ℝ) = (n : ℝ) by exact_mod_cast hilast]
          push_cast
          ring]
        exact toeplitz_sine_boundary k
      change d * Real.sin (((i.val + 1 : ℕ) : ℝ) * θ) + 0 +
          c * Real.sin (((i.val - 1 + 1 : ℕ) : ℝ) * θ) =
        (d + 2 * c * Real.cos θ) *
          Real.sin (((i.val + 1 : ℕ) : ℝ) * θ)
      rw [hcur, hpred]
      have hrec := sin_neighbor_identity x θ
      rw [hboundary] at hrec
      linear_combination c * hrec
    · have hn1 : n = 1 := by omega
      subst n
      fin_cases i
      fin_cases k
      dsimp [θ, x]
      norm_num [toeplitzSineVector, symmetricToeplitzEigenvalue]

/-- The displayed sine eigenvector is nonzero; its first component has angle
strictly between zero and pi. -/
theorem toeplitzSineVector_ne_zero
    {n : ℕ} (k : Fin n) : toeplitzSineVector n k ≠ 0 := by
  let i0 : Fin n := ⟨0, Nat.zero_lt_of_lt k.isLt⟩
  let θ : ℝ := (((k.val + 1 : ℕ) : ℝ) * Real.pi) / ((n + 1 : ℕ) : ℝ)
  have hden : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hθpos : 0 < θ := by
    dsimp [θ]
    positivity
  have hratio : ((k.val + 1 : ℕ) : ℝ) < ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_lt_succ k.isLt
  have hθlt : θ < Real.pi := by
    dsimp [θ]
    rw [div_lt_iff₀ hden]
    nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθpos hθlt
  intro hzero
  have hz := congrFun hzero i0
  have hi : toeplitzSineVector n k i0 = Real.sin θ := by
    rw [toeplitzSineVector_angle]
    simp [i0, θ]
  rw [hi] at hz
  exact (ne_of_gt hsin) hz

private theorem scaledSineColumn_eq
    {n : ℕ} (k : Fin n) :
    (fun i : Fin n => higham9_12_sineMatrix n i k) =
      Real.sqrt (2 / ((n : ℝ) + 1)) • toeplitzSineVector n k := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  unfold higham9_12_sineMatrix toeplitzSineVector
  congr 2
  norm_num [Nat.cast_add]

/-- The normalized discrete-sine columns are eigenvectors as well. -/
theorem symmetricToeplitz_scaled_sine_eigenpair
    {n : ℕ} (c d : ℝ) (k : Fin n) :
    Matrix.mulVec (tridiagonalToeplitz n c d c)
        (fun i => higham9_12_sineMatrix n i k) =
      symmetricToeplitzEigenvalue n c d k •
        (fun i => higham9_12_sineMatrix n i k) := by
  rw [scaledSineColumn_eq]
  rw [Matrix.mulVec_smul, symmetricToeplitz_sine_eigenpair]
  simp [smul_smul, mul_comm]

/-- The normalized sine matrix is orthogonal, reusing the independently
proved finite sine-product identity from Chapter 9. -/
theorem higham9_sineMatrix_isOrthogonal
    {n : ℕ} (hn : 0 < n) : IsOrthogonal n (higham9_12_sineMatrix n) := by
  apply IsOrthogonal.of_col_orthonormal
  intro i j
  simpa [higham9_12_sineMatrix_symm] using
    higham9_12_sineMatrix_mul_self hn i j

/-- Exact orthogonal diagonalization of every nonempty symmetric tridiagonal
Toeplitz matrix.  This supplies the complete symmetric-family eigenvalue
multiset without an assumed component identity or independence hypothesis. -/
theorem symmetricToeplitz_orthogonal_diagonalization
    {n : ℕ} (hn : 0 < n) (c d : ℝ) :
    tridiagonalToeplitz n c d c =
      finiteMatMul (higham9_12_sineMatrix n)
        (finiteMatMul (finiteDiagonal (symmetricToeplitzEigenvalue n c d))
          (matTranspose (higham9_12_sineMatrix n))) := by
  apply finiteMatrix_eq_orthogonal_diagonalization_of_orthonormal_eigenvectors
  · intro i j
    exact (higham9_sineMatrix_isOrthogonal hn).col_orthonormal i j
  · intro k
    simpa [finiteMatVec, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using
      symmetricToeplitz_scaled_sine_eigenpair c d k

/-- One transpose-companion step sends the reverse basis vector indexed by
`k` to the reverse basis vector indexed by `k+1`. -/
private theorem companion_transpose_reverseBasis_step
    {n k : ℕ} (a : ℕ → ℂ) (hk : k + 1 < n) :
    Matrix.mulVec (companionMatrix n a).transpose
        (Pi.single (Fin.rev ⟨k, by omega⟩ : Fin n) 1) =
      Pi.single (Fin.rev ⟨k + 1, hk⟩ : Fin n) 1 := by
  rw [Matrix.mulVec_single_one]
  funext i
  simp only [Matrix.col_apply, Matrix.transpose_apply]
  have hjpos : 0 < (Fin.rev ⟨k, by omega⟩ : Fin n).val := by
    simp [Fin.rev]
    omega
  rw [companionMatrix]
  simp only [if_neg (ne_of_gt hjpos)]
  simp only [Pi.single_apply]
  by_cases hidx : (Fin.rev ⟨k, by omega⟩ : Fin n).val = i.val + 1
  · rw [if_pos hidx]
    rw [if_pos]
    apply Fin.ext
    change i.val = n - ((k + 1) + 1)
    change n - (k + 1) = i.val + 1 at hidx
    omega
  · rw [if_neg hidx]
    rw [if_neg]
    intro hi
    apply hidx
    change n - (k + 1) = i.val + 1
    have hiv : i.val = n - ((k + 1) + 1) := by
      have := congrArg Fin.val hi
      simpa only [Fin.val_rev, Fin.val_mk] using this
    omega

private theorem companion_transpose_pow_seed_nat
    {n : ℕ} (hn : 0 < n) (a : ℕ → ℂ) (k : ℕ) (hk : k < n) :
    Matrix.mulVec ((companionMatrix n a).transpose ^ k)
        (Pi.single (Fin.rev ⟨0, hn⟩ : Fin n) 1) =
      Pi.single (Fin.rev ⟨k, hk⟩ : Fin n) 1 := by
  induction k with
  | zero =>
      rw [pow_zero, Matrix.one_mulVec]
  | succ k ih =>
      rw [pow_succ']
      rw [← Matrix.mulVec_mulVec]
      rw [ih (by omega)]
      exact companion_transpose_reverseBasis_step a hk

/-- The entire transpose Krylov family is exactly the reversed standard
basis; no cyclicity premise is assumed. -/
theorem companion_transpose_krylov_eq_reverseBasis
    {n : ℕ} (hn : 0 < n) (a : ℕ → ℂ) (k : Fin n) :
    Matrix.mulVec ((companionMatrix n a).transpose ^ k.val)
        (Pi.single (Fin.rev ⟨0, hn⟩ : Fin n) 1) =
      Pi.single k.rev 1 := by
  simpa using companion_transpose_pow_seed_nat hn a k.val k.isLt

theorem companion_transpose_krylov_linearIndependent
    {n : ℕ} (hn : 0 < n) (a : ℕ → ℂ) :
    LinearIndependent ℂ (fun k : Fin n =>
      Matrix.mulVec ((companionMatrix n a).transpose ^ k.val)
        (Pi.single (Fin.rev ⟨0, hn⟩ : Fin n) 1)) := by
  have hstd : LinearIndependent ℂ
      (fun k : Fin n => (Pi.single k.rev (1 : ℂ) : Fin n → ℂ)) := by
    simpa [Function.comp_def] using
      (Pi.linearIndependent_single_one (Fin n) ℂ).comp Fin.rev
        Fin.revPerm.injective
  convert hstd using 1
  funext k
  exact companion_transpose_krylov_eq_reverseBasis hn a k

/-- Every positive-order companion matrix has the explicit left cyclic vector
`e_n`.  This is the genuine finite construction behind nonderogatoriness. -/
theorem companion_hasLeftCyclicVector
    {n : ℕ} (hn : 0 < n) (a : ℕ → ℂ) :
    HasLeftCyclicVector (companionMatrix n a) := by
  refine ⟨Pi.single (Fin.rev ⟨0, hn⟩ : Fin n) 1, ?_⟩
  exact companion_transpose_krylov_linearIndependent hn a

private theorem companionMatrix_sub_scalar_rank_ge_succ
    (n : ℕ) (a : ℕ → ℂ) (lambda : ℂ) :
    n ≤ Matrix.rank
      (companionMatrix (n + 1) a -
        lambda • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) := by
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    companionMatrix (n + 1) a - lambda • 1
  let B : Matrix (Fin n) (Fin (n + 1)) ℂ :=
    A.submatrix Fin.succ (Equiv.refl _)
  have hrows : Matrix.rank B ≤ Matrix.rank A := by
    exact Matrix.rank_submatrix_le Fin.succ (Equiv.refl _) A
  have hcols :
      Matrix.rank
          (B.transpose.submatrix Fin.castSucc (Equiv.refl (Fin n))) ≤
        Matrix.rank B.transpose := by
    exact Matrix.rank_submatrix_le Fin.castSucc (Equiv.refl (Fin n)) B.transpose
  have hminor :
      B.transpose.submatrix Fin.castSucc (Equiv.refl (Fin n)) =
        (companionRankMinor n a lambda).transpose := by
    ext i j
    rfl
  rw [hminor, Matrix.rank_transpose, Matrix.rank_transpose] at hcols
  have hunit : IsUnit (companionRankMinor n a lambda) := by
    rw [Matrix.isUnit_iff_isUnit_det, companionRankMinor_det]
    exact isUnit_one
  have hrank := Matrix.rank_of_isUnit (companionRankMinor n a lambda) hunit
  have hrank' : Matrix.rank (companionRankMinor n a lambda) = n := by
    simpa using hrank
  change n ≤ Matrix.rank A
  calc
    n = Matrix.rank (companionRankMinor n a lambda) := hrank'.symm
    _ ≤ Matrix.rank B := hcols
    _ ≤ Matrix.rank A := hrows

/-- Higham, p. 523: every scalar shift of a companion matrix has rank at
least `n - 1`, the printed rank characterization of nonderogatoriness. -/
theorem companionMatrix_sub_scalar_rank_ge
    (n : ℕ) (a : ℕ → ℂ) (lambda : ℂ) :
    n - 1 ≤ Matrix.rank
      (companionMatrix n a -
        lambda • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  cases n with
  | zero => simp
  | succ n =>
      simpa [Nat.succ_eq_add_one] using
        companionMatrix_sub_scalar_rank_ge_succ n a lambda

end NumStability
