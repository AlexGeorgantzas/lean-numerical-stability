/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QED
-/
import LeanFpAnalysis.FP.Algorithms.FFT.Higham24
import LeanFpAnalysis.FP.Analysis.ComplexArithmetic
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace LeanFpAnalysis.FP

open scoped BigOperators Matrix.Norms.L2Operator Matrix
open ComplexConjugate

/-! # Literal radix-2 FFT execution for Higham Chapter 24

Binary indices expose the input least-significant bit and output
most-significant bit at every recursion.  This is the recursive form of the
bit-reversal permutation in Theorem 24.1.
-/

/-- A length-`t` binary index, stored from the bit exposed at the current FFT
recursion to the remaining bits. -/
def Higham24BitIndex : ℕ → Type
  | 0 => Unit
  | t + 1 => Fin 2 × Higham24BitIndex t

instance higham24BitIndexFintype : ∀ t, Fintype (Higham24BitIndex t)
  | 0 => by
      change Fintype Unit
      infer_instance
  | t + 1 => by
      change Fintype (Fin 2 × Higham24BitIndex t)
      letI := higham24BitIndexFintype t
      infer_instance

instance higham24BitIndexDecidableEq : ∀ t, DecidableEq (Higham24BitIndex t)
  | 0 => by
      change DecidableEq Unit
      infer_instance
  | t + 1 => by
      change DecidableEq (Fin 2 × Higham24BitIndex t)
      letI := higham24BitIndexDecidableEq t
      infer_instance

/-- Interpret the recursive bits from least significant to most significant.
This is the input order consumed by decimation in time. -/
def higham24BitIndexLEValue : ∀ t, Higham24BitIndex t → ℕ
  | 0, _ => 0
  | t + 1, p => p.1.val + 2 * higham24BitIndexLEValue t p.2

/-- Interpret the same recursive bits from most significant to least
significant.  This is the natural output order of the recursion. -/
def higham24BitIndexBEValue : ∀ t, Higham24BitIndex t → ℕ
  | 0, _ => 0
  | t + 1, p => p.1.val * 2 ^ t + higham24BitIndexBEValue t p.2

@[simp] theorem higham24BitIndexLEValue_zero (i : Higham24BitIndex 0) :
    higham24BitIndexLEValue 0 i = 0 := rfl

@[simp] theorem higham24BitIndexLEValue_succ (t : ℕ)
    (b : Fin 2) (i : Higham24BitIndex t) :
    higham24BitIndexLEValue (t + 1) (b, i) =
      b.val + 2 * higham24BitIndexLEValue t i := rfl

@[simp] theorem higham24BitIndexBEValue_zero (i : Higham24BitIndex 0) :
    higham24BitIndexBEValue 0 i = 0 := rfl

@[simp] theorem higham24BitIndexBEValue_succ (t : ℕ)
    (b : Fin 2) (i : Higham24BitIndex t) :
    higham24BitIndexBEValue (t + 1) (b, i) =
      b.val * 2 ^ t + higham24BitIndexBEValue t i := rfl

/-- The scalar Fourier weight `exp(-2*pi*i/n)`. -/
noncomputable def higham24FourierRoot (n : ℕ) : ℂ :=
  Complex.exp (((((-2 : ℝ) * Real.pi / (n : ℝ) : ℝ) : ℂ) * Complex.I))

theorem higham24FourierRoot_pow_card (n : ℕ) (hn : 0 < n) :
    higham24FourierRoot n ^ n = 1 := by
  simpa [higham24FourierRoot] using
    higham9_13_fourierRoot_pow_card n 1 hn

theorem higham24FourierRoot_double (m : ℕ) (hm : 0 < m) :
    higham24FourierRoot (2 * m) ^ 2 = higham24FourierRoot m := by
  unfold higham24FourierRoot
  rw [← Complex.exp_nat_mul]
  congr 1
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hm
  simp only [Complex.ext_iff, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  constructor
  · norm_num
  · norm_num
    field_simp [hmR]

/-- The source butterfly block
`B = [[I, Ω], [I, -Ω]]`, indexed without flattening the two block rows.
The diagonal entries of `Ω` are the exact Fourier weights. -/
noncomputable def higham24ButterflyMatrix (k : ℕ) :
    Matrix (Fin 2 × Fin (2 ^ k)) (Fin 2 × Fin (2 ^ k)) ℂ :=
  fun p q => if p.2 = q.2 then
    if q.1 = 0 then 1
    else if p.1 = 0 then higham24FourierRoot (2 ^ (k + 1)) ^ q.2.val
    else -(higham24FourierRoot (2 ^ (k + 1)) ^ q.2.val)
  else 0

/-- Every diagonal Fourier weight in the Chapter 24 butterfly has modulus one. -/
theorem higham24_butterfly_weight_unit (k : ℕ) (j : Fin (2 ^ k)) :
    conj (higham24FourierRoot (2 ^ (k + 1))) ^ j.val *
        higham24FourierRoot (2 ^ (k + 1)) ^ j.val = 1 := by
  rw [← mul_pow]
  have hbase : conj (higham24FourierRoot (2 ^ (k + 1))) *
      higham24FourierRoot (2 ^ (k + 1)) = 1 := by
    have hnorm : ‖higham24FourierRoot (2 ^ (k + 1))‖ = 1 := by
      unfold higham24FourierRoot
      let a : ℝ := (-2 : ℝ) * Real.pi / ((2 ^ (k + 1) : ℕ) : ℝ)
      change ‖Complex.exp ((a : ℂ) * Complex.I)‖ = 1
      have hre : ((a : ℂ) * Complex.I).re = 0 := by
        simp [Complex.mul_re]
      rw [Complex.norm_exp, hre, Real.exp_zero]
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  rw [hbase, one_pow]

/-- Exact orthogonality of the columns of one source butterfly block. -/
theorem higham24_butterfly_gram (k : ℕ) :
    Matrix.conjTranspose (higham24ButterflyMatrix k) *
        higham24ButterflyMatrix k = (2 : ℂ) • 1 := by
  ext q s
  rw [Matrix.mul_apply]
  change (∑ p : Fin 2 × Fin (2 ^ k),
    conj (higham24ButterflyMatrix k p q) *
      higham24ButterflyMatrix k p s) = _
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  rcases q with ⟨qb, qj⟩
  rcases s with ⟨sb, sj⟩
  by_cases hj : qj = sj
  · subst sj
    fin_cases qb <;> fin_cases sb <;>
      simp [higham24ButterflyMatrix, Matrix.smul_apply,
        higham24_butterfly_weight_unit] <;> norm_num
  · simp [higham24ButterflyMatrix, Matrix.smul_apply, hj, Ne.symm hj]

/-- The first norm identity used in (24.3): `‖B‖₂ = √2`. -/
theorem higham24_butterfly_norm (k : ℕ) :
    ‖higham24ButterflyMatrix k‖ = Real.sqrt 2 := by
  have hgram := congrArg norm (higham24_butterfly_gram k)
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hgram
  have hrhs : ‖(2 : ℂ) • (1 : Matrix (Fin 2 × Fin (2 ^ k))
      (Fin 2 × Fin (2 ^ k)) ℂ)‖ = 2 := by
    have hone : ‖(1 : Matrix (Fin 2 × Fin (2 ^ k))
        (Fin 2 × Fin (2 ^ k)) ℂ)‖ = 1 := by
      rw [show (1 : Matrix (Fin 2 × Fin (2 ^ k))
          (Fin 2 × Fin (2 ^ k)) ℂ) =
            Matrix.diagonal (fun _ => (1 : ℂ)) from Matrix.diagonal_one.symm,
        Matrix.l2_opNorm_diagonal, Pi.norm_def,
        Finset.sup_const Finset.univ_nonempty]
      simp
    rw [norm_smul, hone]
    norm_num
  rw [hrhs] at hgram
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  nlinarith [norm_nonneg (higham24ButterflyMatrix k)]

/-- Entrywise absolute value of the butterfly, represented over `ℂ`. -/
noncomputable def higham24AbsButterflyMatrix (k : ℕ) :
    Matrix (Fin 2 × Fin (2 ^ k)) (Fin 2 × Fin (2 ^ k)) ℂ :=
  fun p q => if p.2 = q.2 then 1 else 0

/-- The preceding definition is literally the entrywise modulus of `B`. -/
theorem higham24_absButterfly_eq_entrywise_norm (k : ℕ) :
    (fun p q => (‖higham24ButterflyMatrix k p q‖ : ℂ)) =
      higham24AbsButterflyMatrix k := by
  ext p q
  rcases p with ⟨pb, pj⟩
  rcases q with ⟨qb, qj⟩
  by_cases h : pj = qj
  · subst qj
    have hroot : ‖higham24FourierRoot (2 ^ (k + 1))‖ = 1 := by
      unfold higham24FourierRoot
      let a : ℝ := (-2 : ℝ) * Real.pi / ((2 ^ (k + 1) : ℕ) : ℝ)
      change ‖Complex.exp ((a : ℂ) * Complex.I)‖ = 1
      have hre : ((a : ℂ) * Complex.I).re = 0 := by
        simp [Complex.mul_re]
      rw [Complex.norm_exp, hre, Real.exp_zero]
    fin_cases pb <;> fin_cases qb <;>
      simp [higham24ButterflyMatrix, higham24AbsButterflyMatrix,
        hroot, norm_pow]
  · simp [higham24ButterflyMatrix, higham24AbsButterflyMatrix, h]

/-- The absolute butterfly satisfies `|B|ᴴ |B| = 2 |B|`. -/
theorem higham24_abs_butterfly_gram (k : ℕ) :
    Matrix.conjTranspose (higham24AbsButterflyMatrix k) *
        higham24AbsButterflyMatrix k =
      (2 : ℂ) • higham24AbsButterflyMatrix k := by
  ext q s
  rw [Matrix.mul_apply]
  change (∑ p : Fin 2 × Fin (2 ^ k),
    conj (higham24AbsButterflyMatrix k p q) *
      higham24AbsButterflyMatrix k p s) = _
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  by_cases h : q.2 = s.2
  · simp [higham24AbsButterflyMatrix, h, Matrix.smul_apply]
    norm_num
  · simp [higham24AbsButterflyMatrix, h, Ne.symm h, Matrix.smul_apply]

/-- The butterfly half of the absolute-value identity in (24.3). -/
theorem higham24_abs_butterfly_norm (k : ℕ) :
    ‖higham24AbsButterflyMatrix k‖ = 2 := by
  have hgram := congrArg norm (higham24_abs_butterfly_gram k)
  rw [Matrix.l2_opNorm_conjTranspose_mul_self, norm_smul] at hgram
  norm_num at hgram
  have hne : higham24AbsButterflyMatrix k ≠ 0 := by
    intro hzero
    have hentry := congrFun (congrFun hzero (0, 0)) (0, 0)
    simp [higham24AbsButterflyMatrix] at hentry
  rcases hgram with hnorm | hzero
  · exact hnorm
  · exact (hne hzero).elim

/-- The source stage `A_k = I_(2^(t-k)) ⊗ B_(2^k)`.  Its product index is
kept nested; for the source range `1 ≤ k ≤ t` it has cardinality `2^t`. -/
noncomputable def higham24StageMatrix (t k : ℕ) :
    Matrix (Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1))))
      (Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1)))) ℂ :=
  Matrix.kronecker
    (1 : Matrix (Fin (2 ^ (t - k))) (Fin (2 ^ (t - k))) ℂ)
    (higham24ButterflyMatrix (k - 1))

/-- Exact scaled-isometry identity for a full radix-2 stage. -/
theorem higham24_stage_gram (t k : ℕ) :
    Matrix.conjTranspose (higham24StageMatrix t k) *
        higham24StageMatrix t k = (2 : ℂ) • 1 := by
  simp only [higham24StageMatrix, Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, Matrix.one_mul,
    higham24_butterfly_gram]
  ext i j
  rcases i with ⟨ia, ib⟩
  rcases j with ⟨ja, jb⟩
  by_cases ha : ia = ja <;> by_cases hb : ib = jb
  · subst ja; subst jb; simp [Matrix.kroneckerMap, Matrix.smul_apply]
  · simp [Matrix.kroneckerMap, Matrix.smul_apply, ha, hb]
  · simp [Matrix.kroneckerMap, Matrix.smul_apply, ha, hb]
  · simp [Matrix.kroneckerMap, Matrix.smul_apply, ha, hb]

/-- The stage half of (24.3): every exact `A_k` has `2`-norm `√2`. -/
theorem higham24_stage_norm (t k : ℕ) :
    ‖higham24StageMatrix t k‖ = Real.sqrt 2 := by
  have hgram := congrArg norm (higham24_stage_gram t k)
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hgram
  have hrhs : ‖(2 : ℂ) • (1 : Matrix
      (Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1))))
      (Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1)))) ℂ)‖ = 2 := by
    have hone : ‖(1 : Matrix
        (Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1))))
        (Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1)))) ℂ)‖ = 1 := by
      rw [show (1 : Matrix
          (Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1))))
          (Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1)))) ℂ) =
            Matrix.diagonal (fun _ => (1 : ℂ)) from Matrix.diagonal_one.symm,
        Matrix.l2_opNorm_diagonal, Pi.norm_def,
        Finset.sup_const Finset.univ_nonempty]
      simp
    rw [norm_smul, hone]
    norm_num
  rw [hrhs] at hgram
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  nlinarith [norm_nonneg (higham24StageMatrix t k)]

/-- Entrywise absolute value of the source stage `A_k`. -/
noncomputable def higham24AbsStageMatrix (t k : ℕ) :
    Matrix (Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1))))
      (Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1)))) ℂ :=
  Matrix.kronecker
    (1 : Matrix (Fin (2 ^ (t - k))) (Fin (2 ^ (t - k))) ℂ)
    (higham24AbsButterflyMatrix (k - 1))

/-- The absolute stage definition is literally entrywise modulus of `A_k`. -/
theorem higham24_absStage_eq_entrywise_norm (t k : ℕ) :
    (fun p q => (‖higham24StageMatrix t k p q‖ : ℂ)) =
      higham24AbsStageMatrix t k := by
  ext p q
  rcases p with ⟨pa, pb⟩
  rcases q with ⟨qa, qb⟩
  simp only [higham24StageMatrix, higham24AbsStageMatrix, Matrix.kronecker]
  by_cases h : pa = qa
  · subst qa
    simp only [Matrix.kroneckerMap, Matrix.of_apply, Matrix.one_apply,
      if_pos, one_mul]
    exact congrFun (congrFun
      (higham24_absButterfly_eq_entrywise_norm (k - 1)) pb) qb
  · simp [Matrix.kroneckerMap, h]

/-- The absolute source stage satisfies `|A_k|ᴴ |A_k| = 2 |A_k|`. -/
theorem higham24_abs_stage_gram (t k : ℕ) :
    Matrix.conjTranspose (higham24AbsStageMatrix t k) *
        higham24AbsStageMatrix t k =
      (2 : ℂ) • higham24AbsStageMatrix t k := by
  simp only [higham24AbsStageMatrix, Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, Matrix.one_mul,
    higham24_abs_butterfly_gram]
  ext i j
  rcases i with ⟨ia, ib⟩
  rcases j with ⟨ja, jb⟩
  simp only [Matrix.smul_apply]
  by_cases ha : ia = ja
  · subst ja; simp
  · simp [ha]

/-- The stage half of the absolute-value identity in (24.3). -/
theorem higham24_abs_stage_norm (t k : ℕ) :
    ‖higham24AbsStageMatrix t k‖ = 2 := by
  have hgram := congrArg norm (higham24_abs_stage_gram t k)
  rw [Matrix.l2_opNorm_conjTranspose_mul_self, norm_smul] at hgram
  norm_num at hgram
  have hne : higham24AbsStageMatrix t k ≠ 0 := by
    intro hzero
    have hentry := congrFun (congrFun hzero (0, (0, 0))) (0, (0, 0))
    simp [higham24AbsStageMatrix, Matrix.kronecker, Matrix.kroneckerMap,
      higham24AbsButterflyMatrix] at hentry
  exact hgram.resolve_right hne

/-- The additive butterfly perturbation induced by weight errors `e_j`.
Only the diagonal-weight block changes, with opposite signs in the two rows. -/
noncomputable def higham24ButterflyPerturbation (k : ℕ)
    (e : Fin (2 ^ k) → ℂ) :
    Matrix (Fin 2 × Fin (2 ^ k)) (Fin 2 × Fin (2 ^ k)) ℂ :=
  fun p q => if p.2 = q.2 then
    if q.1 = 0 then 0
    else if p.1 = 0 then e q.2 else -(e q.2)
  else 0

noncomputable def higham24ButterflyPerturbationGramDiagonal (k : ℕ)
    (e : Fin (2 ^ k) → ℂ) : (Fin 2 × Fin (2 ^ k)) → ℂ :=
  fun q => if q.1 = 0 then 0 else 2 * (conj (e q.2) * e q.2)

theorem higham24_butterflyPerturbation_gram (k : ℕ)
    (e : Fin (2 ^ k) → ℂ) :
    Matrix.conjTranspose (higham24ButterflyPerturbation k e) *
        higham24ButterflyPerturbation k e =
      Matrix.diagonal (higham24ButterflyPerturbationGramDiagonal k e) := by
  ext q s
  rw [Matrix.mul_apply]
  change (∑ p : Fin 2 × Fin (2 ^ k),
    conj (higham24ButterflyPerturbation k e p q) *
      higham24ButterflyPerturbation k e p s) = _
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  rcases q with ⟨qb, qj⟩
  rcases s with ⟨sb, sj⟩
  by_cases hj : qj = sj
  · subst sj
    fin_cases qb <;> fin_cases sb
    all_goals simp [higham24ButterflyPerturbation,
      higham24ButterflyPerturbationGramDiagonal] <;> ring
  · simp [higham24ButterflyPerturbation, hj, Ne.symm hj]

theorem higham24_butterflyPerturbation_norm_le (k : ℕ)
    (e : Fin (2 ^ k) → ℂ) (mu : ℝ) (hmu : 0 ≤ mu)
    (he : ∀ j, ‖e j‖ ≤ mu) :
    ‖higham24ButterflyPerturbation k e‖ ≤ mu * Real.sqrt 2 := by
  have hsq : ‖higham24ButterflyPerturbation k e‖ *
      ‖higham24ButterflyPerturbation k e‖ ≤ 2 * mu ^ 2 := by
    calc
      ‖higham24ButterflyPerturbation k e‖ *
          ‖higham24ButterflyPerturbation k e‖ =
          ‖Matrix.conjTranspose (higham24ButterflyPerturbation k e) *
            higham24ButterflyPerturbation k e‖ := by
              rw [Matrix.l2_opNorm_conjTranspose_mul_self]
      _ = ‖Matrix.diagonal
          (higham24ButterflyPerturbationGramDiagonal k e)‖ := by
            rw [higham24_butterflyPerturbation_gram]
      _ = ‖higham24ButterflyPerturbationGramDiagonal k e‖ :=
            Matrix.l2_opNorm_diagonal _
      _ ≤ 2 * mu ^ 2 := by
        apply (pi_norm_le_iff_of_nonneg (by positivity)).2
        intro q
        rcases q with ⟨qb, qj⟩
        fin_cases qb
        · simp [higham24ButterflyPerturbationGramDiagonal]
          positivity
        · simp [higham24ButterflyPerturbationGramDiagonal]
          nlinarith [norm_nonneg (e qj), he qj]
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hrhs_sq : (mu * Real.sqrt 2) ^ 2 = 2 * mu ^ 2 := by
    rw [mul_pow, hsqrt_sq]
    ring
  have hrhs_nonneg : 0 ≤ mu * Real.sqrt 2 := mul_nonneg hmu hsqrt
  nlinarith [norm_nonneg (higham24ButterflyPerturbation k e)]

/-- The full stage perturbation `ΔA_k = I ⊗ ΔB_k`. -/
noncomputable def higham24StagePerturbation (t k : ℕ)
    (e : Fin (2 ^ (k - 1)) → ℂ) :
    Matrix (Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1))))
      (Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1)))) ℂ :=
  Matrix.kronecker
    (1 : Matrix (Fin (2 ^ (t - k))) (Fin (2 ^ (t - k))) ℂ)
    (higham24ButterflyPerturbation (k - 1) e)

theorem higham24_stagePerturbation_gram (t k : ℕ)
    (e : Fin (2 ^ (k - 1)) → ℂ) :
    Matrix.conjTranspose (higham24StagePerturbation t k e) *
        higham24StagePerturbation t k e =
      Matrix.diagonal (fun q =>
        higham24ButterflyPerturbationGramDiagonal (k - 1) e q.2) := by
  simp only [higham24StagePerturbation, Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, Matrix.one_mul,
    higham24_butterflyPerturbation_gram]
  ext i j
  rcases i with ⟨ia, ib⟩
  rcases j with ⟨ja, jb⟩
  by_cases ha : ia = ja
  · subst ja
    by_cases hb : ib = jb
    · subst jb; simp [Matrix.kroneckerMap]
    · simp [Matrix.kroneckerMap, hb]
  · simp [Matrix.kroneckerMap, ha]

theorem higham24_stagePerturbation_norm_le (t k : ℕ)
    (e : Fin (2 ^ (k - 1)) → ℂ) (mu : ℝ) (hmu : 0 ≤ mu)
    (he : ∀ j, ‖e j‖ ≤ mu) :
    ‖higham24StagePerturbation t k e‖ ≤ mu * Real.sqrt 2 := by
  have hsq : ‖higham24StagePerturbation t k e‖ *
      ‖higham24StagePerturbation t k e‖ ≤ 2 * mu ^ 2 := by
    calc
      ‖higham24StagePerturbation t k e‖ *
          ‖higham24StagePerturbation t k e‖ =
          ‖Matrix.conjTranspose (higham24StagePerturbation t k e) *
            higham24StagePerturbation t k e‖ := by
              rw [Matrix.l2_opNorm_conjTranspose_mul_self]
      _ = ‖Matrix.diagonal
          (fun q : Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1))) =>
            higham24ButterflyPerturbationGramDiagonal (k - 1) e q.2)‖ := by
            rw [higham24_stagePerturbation_gram]
      _ = ‖fun q : Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1))) =>
          higham24ButterflyPerturbationGramDiagonal (k - 1) e q.2‖ :=
            Matrix.l2_opNorm_diagonal _
      _ ≤ 2 * mu ^ 2 := by
        apply (pi_norm_le_iff_of_nonneg (by positivity)).2
        intro q
        rcases q with ⟨qa, qb, qj⟩
        fin_cases qb
        · simp [higham24ButterflyPerturbationGramDiagonal]
          positivity
        · simp [higham24ButterflyPerturbationGramDiagonal]
          nlinarith [norm_nonneg (e qj), he qj]
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hrhs_sq : (mu * Real.sqrt 2) ^ 2 = 2 * mu ^ 2 := by
    rw [mul_pow, hsqrt_sq]
    ring
  have hrhs_nonneg : 0 ≤ mu * Real.sqrt 2 := mul_nonneg hmu hsqrt
  nlinarith [norm_nonneg (higham24StagePerturbation t k e)]

/-- A butterfly using the actually computed diagonal weights. -/
noncomputable def higham24ComputedButterflyMatrix (k : ℕ)
    (weight : Fin (2 ^ k) → ℂ) :
    Matrix (Fin 2 × Fin (2 ^ k)) (Fin 2 × Fin (2 ^ k)) ℂ :=
  fun p q => if p.2 = q.2 then
    if q.1 = 0 then 1
    else if p.1 = 0 then weight q.2 else -(weight q.2)
  else 0

theorem higham24_computedButterfly_sub (k : ℕ)
    (weight : Fin (2 ^ k) → ℂ) :
    higham24ComputedButterflyMatrix k weight - higham24ButterflyMatrix k =
      higham24ButterflyPerturbation k (fun j =>
        weight j - higham24FourierRoot (2 ^ (k + 1)) ^ j.val) := by
  ext p q
  rcases p with ⟨pb, pj⟩
  rcases q with ⟨qb, qj⟩
  by_cases hj : pj = qj
  · subst qj
    fin_cases pb <;> fin_cases qb
    all_goals simp [higham24ComputedButterflyMatrix, higham24ButterflyMatrix,
      higham24ButterflyPerturbation] <;> ring
  · simp [higham24ComputedButterflyMatrix, higham24ButterflyMatrix,
      higham24ButterflyPerturbation, hj]

/-- The source computed stage `Ã_k = I ⊗ B̃_k`. -/
noncomputable def higham24ComputedStageMatrix (t k : ℕ)
    (weight : Fin (2 ^ (k - 1)) → ℂ) :
    Matrix (Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1))))
      (Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1)))) ℂ :=
  Matrix.kronecker
    (1 : Matrix (Fin (2 ^ (t - k))) (Fin (2 ^ (t - k))) ℂ)
    (higham24ComputedButterflyMatrix (k - 1) weight)

theorem higham24_computedStage_sub (t k : ℕ)
    (weight : Fin (2 ^ (k - 1)) → ℂ) (hk : 1 ≤ k) :
    higham24ComputedStageMatrix t k weight - higham24StageMatrix t k =
      higham24StagePerturbation t k (fun j =>
        weight j - higham24FourierRoot (2 ^ k) ^ j.val) := by
  ext p q
  rcases p with ⟨pa, pb⟩
  rcases q with ⟨qa, qb⟩
  simp only [higham24ComputedStageMatrix, higham24StageMatrix,
    higham24StagePerturbation, Matrix.kronecker, Matrix.sub_apply]
  by_cases h : pa = qa
  · subst qa
    simp only [Matrix.kroneckerMap, Matrix.of_apply, Matrix.one_apply, if_pos,
      one_mul]
    simpa [Nat.sub_add_cancel hk] using
      congrFun (congrFun
        (higham24_computedButterfly_sub (k - 1) weight) pb) qb
  · simp [Matrix.kroneckerMap, h]

/-- Equation (24.4), including the printed representation
`Ã_k = A_k + ΔA_k` and the relative stage-norm bound. -/
theorem higham24_eq24_4 (t k : ℕ)
    (weight : Fin (2 ^ (k - 1)) → ℂ) (mu : ℝ)
    (hk : 1 ≤ k) (_hkt : k ≤ t) (hmu : 0 ≤ mu)
    (hw : ∀ j, Higham24WeightApproximation
      (higham24FourierRoot (2 ^ k) ^ j.val) (weight j) mu) :
    higham24ComputedStageMatrix t k weight = higham24StageMatrix t k +
        higham24StagePerturbation t k (fun j =>
          weight j - higham24FourierRoot (2 ^ k) ^ j.val) ∧
      ‖higham24StagePerturbation t k (fun j =>
          weight j - higham24FourierRoot (2 ^ k) ^ j.val)‖ ≤
        mu * ‖higham24StageMatrix t k‖ := by
  constructor
  · have hsub := higham24_computedStage_sub t k weight hk
    rw [sub_eq_iff_eq_add] at hsub
    simpa [add_comm] using hsub
  · rw [higham24_stage_norm]
    exact higham24_stagePerturbation_norm_le t k _ mu hmu fun j =>
      higham24_eq24_2_error_bound (hw j)

/-- A DFT written on recursive binary indices.  Input indices use their
little-endian value; output indices use their big-endian value. -/
noncomputable def higham24BinaryDFT (t : ℕ)
    (x : Higham24BitIndex t → ℂ) (k : Higham24BitIndex t) : ℂ :=
  ∑ j, higham24FourierRoot (2 ^ t) ^
      (higham24BitIndexBEValue t k * higham24BitIndexLEValue t j) * x j

/-- Literal recursive decimation-in-time radix-2 FFT. -/
noncomputable def higham24Radix2FFT : ∀ t,
    (Higham24BitIndex t → ℂ) → Higham24BitIndex t → ℂ
  | 0, x, _ => x ()
  | t + 1, x, p =>
      let even := higham24Radix2FFT t (fun j => x (0, j)) p.2
      let odd := higham24Radix2FFT t (fun j => x (1, j)) p.2
      even + higham24FourierRoot (2 ^ (t + 1)) ^
        (higham24BitIndexBEValue (t + 1) p) * odd

theorem higham24FourierRoot_pow_reduce_two_blocks
    (m : ℕ) (hm : 0 < m) (b : Fin 2) (r j : ℕ) :
    higham24FourierRoot m ^ ((b.val * m + r) * j) =
      higham24FourierRoot m ^ (r * j) := by
  rw [Nat.add_mul, pow_add]
  have hblock :
      higham24FourierRoot m ^ (b.val * m * j) = 1 := by
    calc
      higham24FourierRoot m ^ (b.val * m * j) =
          higham24FourierRoot m ^ (m * (b.val * j)) := by
            congr 1
            ring
      _ = (higham24FourierRoot m ^ m) ^ (b.val * j) := by rw [pow_mul]
      _ = 1 := by rw [higham24FourierRoot_pow_card m hm]; simp
  rw [hblock, one_mul]

theorem higham24FourierRoot_even_exponent
    (m : ℕ) (hm : 0 < m) (b : Fin 2) (r j : ℕ) :
    higham24FourierRoot (2 * m) ^ ((b.val * m + r) * (2 * j)) =
      higham24FourierRoot m ^ (r * j) := by
  calc
    higham24FourierRoot (2 * m) ^ ((b.val * m + r) * (2 * j)) =
        higham24FourierRoot (2 * m) ^ (2 * ((b.val * m + r) * j)) := by
          congr 1
          ring
    _ = (higham24FourierRoot (2 * m) ^ 2) ^ ((b.val * m + r) * j) := by
          rw [pow_mul]
    _ = higham24FourierRoot m ^ ((b.val * m + r) * j) := by
          rw [higham24FourierRoot_double m hm]
    _ = higham24FourierRoot m ^ (r * j) :=
          higham24FourierRoot_pow_reduce_two_blocks m hm b r j

theorem higham24FourierRoot_odd_exponent
    (m : ℕ) (hm : 0 < m) (b : Fin 2) (r j : ℕ) :
    higham24FourierRoot (2 * m) ^ ((b.val * m + r) * (1 + 2 * j)) =
      higham24FourierRoot (2 * m) ^ (b.val * m + r) *
        higham24FourierRoot m ^ (r * j) := by
  calc
    higham24FourierRoot (2 * m) ^ ((b.val * m + r) * (1 + 2 * j)) =
        higham24FourierRoot (2 * m) ^
          ((b.val * m + r) + (b.val * m + r) * (2 * j)) := by
            congr 1
            ring
    _ = higham24FourierRoot (2 * m) ^ (b.val * m + r) *
          higham24FourierRoot (2 * m) ^ ((b.val * m + r) * (2 * j)) := by
            rw [pow_add]
    _ = higham24FourierRoot (2 * m) ^ (b.val * m + r) *
          higham24FourierRoot m ^ (r * j) := by
            rw [higham24FourierRoot_even_exponent m hm b r j]

/-- The literal recursion computes the binary-index DFT exactly. -/
theorem higham24Radix2FFT_eq_binaryDFT :
    ∀ t (x : Higham24BitIndex t → ℂ) (k : Higham24BitIndex t),
      higham24Radix2FFT t x k = higham24BinaryDFT t x k := by
  intro t
  induction t with
  | zero =>
      intro x k
      change Unit at k
      rcases k with ⟨⟩
      simp [higham24Radix2FFT, higham24BinaryDFT,
        Higham24BitIndex, higham24BitIndexBEValue,
        higham24BitIndexLEValue]
  | succ t ih =>
      intro x k
      rcases k with ⟨b, k⟩
      rw [higham24Radix2FFT]
      rw [ih (fun j => x (0, j)) k, ih (fun j => x (1, j)) k]
      unfold higham24BinaryDFT
      conv_rhs =>
        change ∑ j : Fin 2 × Higham24BitIndex t, _
        rw [Fintype.sum_prod_type, Fin.sum_univ_two]
      simp only [higham24BitIndexBEValue_succ, higham24BitIndexLEValue_succ,
        Fin.val_zero, Fin.val_one, zero_add]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro j _hj
        rw [show 2 ^ (t + 1) = 2 * 2 ^ t by rw [pow_succ']]
        rw [higham24FourierRoot_even_exponent (2 ^ t) (by positivity) b
          (higham24BitIndexBEValue t k) (higham24BitIndexLEValue t j)]
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        rw [show 2 ^ (t + 1) = 2 * 2 ^ t by rw [pow_succ']]
        rw [higham24FourierRoot_odd_exponent (2 ^ t) (by positivity) b
          (higham24BitIndexBEValue t k) (higham24BitIndexLEValue t j)]
        ring

/-- Little-endian binary words enumerate `Fin (2^t)`. -/
def higham24BitIndexLEEquiv : ∀ t, Higham24BitIndex t ≃ Fin (2 ^ t)
  | 0 => finOneEquiv.symm
  | t + 1 =>
      (Equiv.prodCongr (Equiv.refl (Fin 2)) (higham24BitIndexLEEquiv t)).trans
        ((Equiv.prodComm (Fin 2) (Fin (2 ^ t))).trans
          (finProdFinEquiv.trans (finCongr (by rw [pow_succ]))))

/-- Big-endian binary words enumerate `Fin (2^t)`. -/
def higham24BitIndexBEEquiv : ∀ t, Higham24BitIndex t ≃ Fin (2 ^ t)
  | 0 => finOneEquiv.symm
  | t + 1 =>
      (Equiv.prodCongr (Equiv.refl (Fin 2)) (higham24BitIndexBEEquiv t)).trans
        (finProdFinEquiv.trans (finCongr (by rw [pow_succ'])))

theorem higham24BitIndexLEEquiv_val :
    ∀ t (i : Higham24BitIndex t),
      (higham24BitIndexLEEquiv t i).val = higham24BitIndexLEValue t i := by
  intro t
  induction t with
  | zero => intro i; cases i; rfl
  | succ t ih =>
      intro i
      rcases i with ⟨b, i⟩
      change b.val + 2 * (higham24BitIndexLEEquiv t i).val =
        b.val + 2 * higham24BitIndexLEValue t i
      rw [ih]

theorem higham24BitIndexBEEquiv_val :
    ∀ t (i : Higham24BitIndex t),
      (higham24BitIndexBEEquiv t i).val = higham24BitIndexBEValue t i := by
  intro t
  induction t with
  | zero => intro i; cases i; rfl
  | succ t ih =>
      intro i
      rcases i with ⟨b, i⟩
      change (higham24BitIndexBEEquiv t i).val + 2 ^ t * b.val =
        b.val * 2 ^ t + higham24BitIndexBEValue t i
      rw [ih]
      ring

theorem higham24FourierRoot_pow (n q : ℕ) (hn : 0 < n) :
    higham24FourierRoot n ^ q =
      Complex.exp (((((-2 : ℝ) * Real.pi * (q : ℝ) / (n : ℝ) : ℝ) : ℂ) *
        Complex.I)) := by
  unfold higham24FourierRoot
  rw [← Complex.exp_nat_mul]
  congr 1
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  simp only [Complex.ext_iff, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  constructor
  · norm_num
  · norm_num
    field_simp [hnR]

/-- The binary-index DFT is the canonical Chapter 24 DFT after the explicit
input/output reindexings. -/
theorem higham24BinaryDFT_eq_dftApply (t : ℕ)
    (x : Higham24BitIndex t → ℂ) (k : Higham24BitIndex t) :
    higham24BinaryDFT t x k =
      higham24DFTApply
        (fun i => x ((higham24BitIndexLEEquiv t).symm i))
        (higham24BitIndexBEEquiv t k) := by
  unfold higham24BinaryDFT higham24DFTApply higham24DFT
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  apply Fintype.sum_equiv (higham24BitIndexLEEquiv t)
  intro j
  rw [(higham24BitIndexLEEquiv t).symm_apply_apply]
  rw [higham24FourierRoot_pow (2 ^ t)
    (higham24BitIndexBEValue t k * higham24BitIndexLEValue t j) (by positivity)]
  unfold higham9_13_fourierVandermonde
  rw [higham24BitIndexBEEquiv_val, higham24BitIndexLEEquiv_val]
  apply congrArg (fun z : ℂ => z * x j)
  congr 1
  norm_num [Nat.cast_mul]
  ring

/-- Source-facing radix-2 correctness theorem.  The input permutation is the
bit-reversal map from little-endian recursive words to ordinary `Fin` indices;
the output is in ordinary DFT order. -/
theorem higham24Radix2FFT_eq_dftApply (t : ℕ)
    (x : Higham24BitIndex t → ℂ) (k : Higham24BitIndex t) :
    higham24Radix2FFT t x k =
      higham24DFTApply
        (fun i => x ((higham24BitIndexLEEquiv t).symm i))
        (higham24BitIndexBEEquiv t k) := by
  rw [higham24Radix2FFT_eq_binaryDFT, higham24BinaryDFT_eq_dftApply]

/-- The final radix-2 stage on binary indices.  The first input column is `I`;
the second is the diagonal Fourier-weight block, including its lower sign. -/
noncomputable def higham24BinaryTopStageMatrix (t : ℕ) :
    Matrix (Higham24BitIndex (t + 1)) (Higham24BitIndex (t + 1)) ℂ :=
  fun p q => if p.2 = q.2 then
    if q.1 = 0 then 1
    else higham24FourierRoot (2 ^ (t + 1)) ^
      higham24BitIndexBEValue (t + 1) p
  else 0

/-- Block-diagonal lift `I₂ ⊗ M` to one more binary index. -/
noncomputable def higham24BinaryLiftMatrix {t : ℕ}
    (M : Matrix (Higham24BitIndex t) (Higham24BitIndex t) ℂ) :
    Matrix (Higham24BitIndex (t + 1)) (Higham24BitIndex (t + 1)) ℂ :=
  fun p q => if p.1 = q.1 then M p.2 q.2 else 0

theorem higham24_binaryTopStage_mulVec (t : ℕ)
    (x : Higham24BitIndex (t + 1) → ℂ)
    (p : Higham24BitIndex (t + 1)) :
    (higham24BinaryTopStageMatrix t).mulVec x p =
      x (0, p.2) + higham24FourierRoot (2 ^ (t + 1)) ^
        higham24BitIndexBEValue (t + 1) p * x (1, p.2) := by
  simp only [Matrix.mulVec, dotProduct, higham24BinaryTopStageMatrix]
  change (∑ q : Fin 2 × Higham24BitIndex t, _) = _
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp

theorem higham24_binaryLift_mulVec {t : ℕ}
    (M : Matrix (Higham24BitIndex t) (Higham24BitIndex t) ℂ)
    (x : Higham24BitIndex (t + 1) → ℂ)
    (p : Higham24BitIndex (t + 1)) :
    (higham24BinaryLiftMatrix M).mulVec x p =
      M.mulVec (fun j => x (p.1, j)) p.2 := by
  simp only [Matrix.mulVec, dotProduct, higham24BinaryLiftMatrix]
  change (∑ q : Fin 2 × Higham24BitIndex t, _) = _
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  rcases p with ⟨b, i⟩
  fin_cases b <;> simp

/-- The literal ordered product `A_t ⋯ A₁` on binary indices.  Recursively,
the earlier stages lift block-diagonally and the new `B_(2^(t+1))` stage is
multiplied on the left. -/
noncomputable def higham24BinaryStageProduct : ∀ t,
    Matrix (Higham24BitIndex t) (Higham24BitIndex t) ℂ
  | 0 => 1
  | t + 1 => higham24BinaryTopStageMatrix t *
      higham24BinaryLiftMatrix (higham24BinaryStageProduct t)

theorem higham24_binaryStageProduct_mulVec :
    ∀ t (x : Higham24BitIndex t → ℂ) (p : Higham24BitIndex t),
    (higham24BinaryStageProduct t).mulVec x p =
      higham24Radix2FFT t x p := by
  intro t
  induction t with
  | zero =>
      intro x p
      change Unit at p
      rcases p with ⟨⟩
      rw [higham24BinaryStageProduct, Matrix.one_mulVec]
      rfl
  | succ t ih =>
      intro x p
      rw [higham24BinaryStageProduct, ← Matrix.mulVec_mulVec,
        higham24_binaryTopStage_mulVec]
      rw [higham24_binaryLift_mulVec, higham24_binaryLift_mulVec, ih, ih]
      rfl

noncomputable def higham24BinaryDFTMatrix (t : ℕ) :
    Matrix (Higham24BitIndex t) (Higham24BitIndex t) ℂ :=
  fun k j => higham24FourierRoot (2 ^ t) ^
    (higham24BitIndexBEValue t k * higham24BitIndexLEValue t j)

theorem higham24_binaryDFTMatrix_mulVec (t : ℕ)
    (x : Higham24BitIndex t → ℂ) (p : Higham24BitIndex t) :
    (higham24BinaryDFTMatrix t).mulVec x p = higham24BinaryDFT t x p := by
  rfl

theorem higham24_binaryDFTMatrix_eq_stageProduct (t : ℕ) :
    higham24BinaryDFTMatrix t = higham24BinaryStageProduct t := by
  ext p q
  let x : Higham24BitIndex t → ℂ := Pi.single q 1
  have hp := higham24_binaryStageProduct_mulVec t x p
  rw [higham24Radix2FFT_eq_binaryDFT] at hp
  have hd := higham24_binaryDFTMatrix_mulVec t x p
  simpa [x, Matrix.col_apply, Matrix.mulVec_single] using hd.trans hp.symm

/-- The source bit-reversal permutation `P_n`, expressed on binary words.
It sends a big-endian input coordinate to the little-endian coordinate consumed
by the decimation-in-time stage product. -/
noncomputable def higham24BitReversalMatrix (t : ℕ) :
    Matrix (Higham24BitIndex t) (Higham24BitIndex t) ℂ :=
  fun p q => if higham24BitIndexLEEquiv t p =
      higham24BitIndexBEEquiv t q then 1 else 0

/-- The canonical DFT matrix with both coordinates read in big-endian order. -/
noncomputable def higham24BigEndianDFTMatrix (t : ℕ) :
    Matrix (Higham24BitIndex t) (Higham24BitIndex t) ℂ :=
  fun p q => higham24FourierRoot (2 ^ t) ^
    (higham24BitIndexBEValue t p * higham24BitIndexBEValue t q)

/-- Theorem 24.1 / equation (24.1), with all reindexing explicit:
`F_n = A_t ⋯ A₁ P_n` for `n = 2^t`. -/
theorem higham24_theorem24_1_stage_factorization (t : ℕ) :
    higham24BigEndianDFTMatrix t =
      higham24BinaryStageProduct t * higham24BitReversalMatrix t := by
  rw [← higham24_binaryDFTMatrix_eq_stageProduct]
  ext p q
  rw [Matrix.mul_apply]
  let j0 : Higham24BitIndex t :=
    (higham24BitIndexLEEquiv t).symm (higham24BitIndexBEEquiv t q)
  rw [Finset.sum_eq_single j0]
  · have hj0 : higham24BitIndexLEValue t j0 =
        higham24BitIndexBEValue t q := by
      rw [← higham24BitIndexLEEquiv_val,
        ← higham24BitIndexBEEquiv_val]
      simp [j0]
    simp [higham24BigEndianDFTMatrix, higham24BinaryDFTMatrix,
      higham24BitReversalMatrix, j0, hj0]
  · intro j _hj hne
    have hdiff : higham24BitIndexLEEquiv t j ≠
        higham24BitIndexBEEquiv t q := by
      intro heq
      apply hne
      exact (higham24BitIndexLEEquiv t).injective
        (by simpa [j0] using heq)
    simp [higham24BitReversalMatrix, hdiff]
  · intro hnot
    exact (hnot (Finset.mem_univ j0)).elim

/-- Literal rounded recursion.  Each butterfly uses the repository's rounded
complex multiplication and addition; the supplied weight table permits the
computed weights of (24.2). -/
noncomputable def higham24RoundedRadix2FFT (fp : FPModel)
    (weight : ∀ t, Higham24BitIndex t → ℂ) : ∀ t,
    (Higham24BitIndex t → ℂ) → Higham24BitIndex t → ℂ
  | 0, x, _ => x ()
  | t + 1, x, p =>
      let even := higham24RoundedRadix2FFT fp weight t (fun j => x (0, j)) p.2
      let odd := higham24RoundedRadix2FFT fp weight t (fun j => x (1, j)) p.2
      fl_complexAdd fp even (fl_complexMul fp (weight (t + 1) p) odd)

/-- One literal rounded butterfly output satisfies the primitive complex
addition/multiplication error decomposition used to build a stage contract. -/
theorem higham24_roundedButterfly_pointwise_error_bound
    (fp : FPModel) (hgamma2 : gammaValid fp 2) (a w b : ℂ) :
    ‖fl_complexAdd fp a (fl_complexMul fp w b) - (a + w * b)‖ ≤
      fp.u * ‖a + fl_complexMul fp w b‖ +
        Real.sqrt 2 * gamma fp 2 * ‖w * b‖ := by
  calc
    ‖fl_complexAdd fp a (fl_complexMul fp w b) - (a + w * b)‖ =
        ‖(fl_complexAdd fp a (fl_complexMul fp w b) -
            (a + fl_complexMul fp w b)) +
          (fl_complexMul fp w b - w * b)‖ := by
            congr 1
            ring
    _ ≤ ‖fl_complexAdd fp a (fl_complexMul fp w b) -
          (a + fl_complexMul fp w b)‖ +
        ‖fl_complexMul fp w b - w * b‖ := norm_add_le _ _
    _ ≤ fp.u * ‖a + fl_complexMul fp w b‖ +
        Real.sqrt 2 * gamma fp 2 * ‖w * b‖ :=
      add_le_add (fl_complexAdd_error_bound fp a (fl_complexMul fp w b))
        (fl_complexMul_error_bound fp hgamma2 w b)

/-- Canonical Euclidean norm on binary-index vectors, transported to the
repository's `Fin`-indexed complex `L²` norm. -/
noncomputable def higham24BinaryVecNorm2 (t : ℕ)
    (x : Higham24BitIndex t → ℂ) : ℝ :=
  complexVecLpNorm (ENNReal.ofReal (2 : ℝ))
    (fun i => x ((higham24BitIndexBEEquiv t).symm i))

/-- An honest explicit execution domain for the product argument in (24.5).
It records exact and computed intermediate states and only a stage-local
normalized error inequality; the final theorem is not a field of the
contract. -/
structure Higham24ExplicitStageExecution
    {V : Type*} [NormedAddCommGroup V]
    (t : ℕ) (eta : ℝ) where
  exactState : ℕ → V
  computedState : ℕ → V
  referenceNorm : ℝ
  referenceNorm_pos : 0 < referenceNorm
  initial : computedState 0 = exactState 0
  step_bound : ∀ k, k < t →
    ‖computedState (k + 1) - exactState (k + 1)‖ / referenceNorm ≤
      (1 + eta) *
        (‖computedState k - exactState k‖ / referenceNorm) + eta

/-- The explicit execution domain is nonvacuous: an exact sequence is a
computed sequence with zero stage error for every nonnegative `eta`. -/
def higham24ExactStageExecution
    {V : Type*} [NormedAddCommGroup V]
    (t : ℕ) (eta : ℝ) (heta : 0 ≤ eta) (state : ℕ → V)
    (referenceNorm : ℝ) (href : 0 < referenceNorm) :
    Higham24ExplicitStageExecution (V := V) t eta where
  exactState := state
  computedState := state
  referenceNorm := referenceNorm
  referenceNorm_pos := href
  initial := rfl
  step_bound := by
    intro k hk
    simp [heta]

/-- Theorem 24.2/(24.5) on the strongest honest explicit stage domain: local
rounded-stage estimates accumulate to the printed relative product bound. -/
theorem higham24_theorem24_2_explicitDomain
    {V : Type*} [NormedAddCommGroup V]
    {t : ℕ} {eta : ℝ} (heta : 0 ≤ eta)
    (hvalid : (t : ℝ) * eta < 1)
    (execution : Higham24ExplicitStageExecution (V := V) t eta) :
    ‖execution.computedState t - execution.exactState t‖ /
        execution.referenceNorm ≤ higham24RelativeFFTBound t eta := by
  let relativeError : ℕ → ℝ := fun k =>
    ‖execution.computedState k - execution.exactState k‖ /
      execution.referenceNorm
  have hzero : relativeError 0 = 0 := by
    simp [relativeError, execution.initial]
  have hbound : ∀ k, k ≤ t → relativeError k ≤ (1 + eta) ^ k - 1 := by
    intro k hk
    induction k with
    | zero => simp [hzero]
    | succ k ih =>
        have hkt : k < t := Nat.lt_of_succ_le hk
        have hrec : relativeError (k + 1) ≤
            (1 + eta) * relativeError k + eta := by
          simpa [relativeError] using execution.step_bound k hkt
        have hone : 0 ≤ 1 + eta := add_nonneg zero_le_one heta
        have hmul := mul_le_mul_of_nonneg_left (ih (Nat.le_of_lt hkt)) hone
        calc
          relativeError (k + 1) ≤ (1 + eta) * relativeError k + eta := hrec
          _ ≤ (1 + eta) * ((1 + eta) ^ k - 1) + eta :=
            add_le_add hmul le_rfl
          _ = (1 + eta) ^ (k + 1) - 1 := by rw [pow_succ']; ring
  exact le_trans (hbound t le_rfl)
    (higham24_eq24_5_product_bound t eta heta hvalid)

/-- Runtime error trace for the literal rounded recursion.  The `step` field is
the precise stage-local obligation produced by the weight and complex
arithmetic analysis in the printed proof.  It is deliberately local, rather
than assuming the final theorem conclusion. -/
structure Higham24Radix2ForwardErrorTrace (fp : FPModel)
    (weight : ∀ t, Higham24BitIndex t → ℂ) (t : ℕ)
    (x : Higham24BitIndex t → ℂ) (eta : ℝ) where
  relativeError : ℕ → ℝ
  initial : relativeError 0 = 0
  step : ∀ k, k < t →
    relativeError (k + 1) ≤ (1 + eta) * relativeError k + eta
  final : relativeError t =
    higham24BinaryVecNorm2 t
        (higham24RoundedRadix2FFT fp weight t x - higham24Radix2FFT t x) /
      higham24BinaryVecNorm2 t (higham24Radix2FFT t x)

/-- Source-shaped certificate for Theorem 24.2.  Besides the local error
trace, it records the computed-weight model (24.2), nonnegativity of `μ`, and
the validity condition needed for `γ₄`.  Thus the source-facing theorem below
does not hide these assumptions behind the final error conclusion. -/
structure Higham24SourceRadix2ForwardErrorTrace (fp : FPModel)
    (weight : ∀ t, Higham24BitIndex t → ℂ) (t : ℕ)
    (x : Higham24BitIndex t → ℂ) (mu : ℝ) extends
    Higham24Radix2ForwardErrorTrace fp weight t x
      (higham24Eta mu (gamma fp 4)) where
  mu_nonneg : 0 ≤ mu
  gamma4_valid : gammaValid fp 4
  weight_error : ∀ s (p : Higham24BitIndex s), s ≤ t →
    Higham24WeightApproximation
      (higham24FourierRoot (2 ^ s) ^ higham24BitIndexBEValue s p)
      (weight s p) mu

theorem higham24_errorTrace_le_one_add_pow_sub_one
    {fp : FPModel} {weight : ∀ t, Higham24BitIndex t → ℂ}
    {t : ℕ} {x : Higham24BitIndex t → ℂ} {eta : ℝ}
    (heta : 0 ≤ eta)
    (trace : Higham24Radix2ForwardErrorTrace fp weight t x eta) :
    trace.relativeError t ≤ (1 + eta) ^ t - 1 := by
  have hbound : ∀ k, k ≤ t →
      trace.relativeError k ≤ (1 + eta) ^ k - 1 := by
    intro k hk
    induction k with
    | zero => simp [trace.initial]
    | succ k ih =>
        have hkt : k < t := Nat.lt_of_succ_le hk
        have hrec := trace.step k hkt
        have hone : 0 ≤ 1 + eta := add_nonneg zero_le_one heta
        have hmul := mul_le_mul_of_nonneg_left (ih (Nat.le_of_lt hkt)) hone
        calc
          trace.relativeError (k + 1) ≤
              (1 + eta) * trace.relativeError k + eta := hrec
          _ ≤ (1 + eta) * ((1 + eta) ^ k - 1) + eta :=
            add_le_add hmul le_rfl
          _ = (1 + eta) ^ (k + 1) - 1 := by rw [pow_succ']; ring
  exact hbound t le_rfl

/-- Conditional error-bound assembly for the literal rounded radix-2 executor,
under a visible stage-local trace certificate.  This lemma does not produce
that certificate from the floating operations. -/
theorem higham24_theorem24_2_of_errorTrace
    {fp : FPModel} {weight : ∀ t, Higham24BitIndex t → ℂ}
    {t : ℕ} {x : Higham24BitIndex t → ℂ} {eta : ℝ}
    (heta : 0 ≤ eta) (hvalid : (t : ℝ) * eta < 1)
    (trace : Higham24Radix2ForwardErrorTrace fp weight t x eta) :
    higham24BinaryVecNorm2 t
        (higham24RoundedRadix2FFT fp weight t x - higham24Radix2FFT t x) /
      higham24BinaryVecNorm2 t (higham24Radix2FFT t x) ≤
        higham24RelativeFFTBound t eta := by
  rw [← trace.final]
  exact le_trans (higham24_errorTrace_le_one_add_pow_sub_one heta trace)
    (higham24_eq24_5_product_bound t eta heta hvalid)

/-- Conditional assembly specialized to the Theorem 24.2 coefficient
`η = μ + γ₄(√2 + μ)` printed in the chapter.  Its explicit source trace remains
an implementation-specific input rather than a derived result. -/
theorem higham24_theorem24_2_of_sourceTrace
    {fp : FPModel} {weight : ∀ t, Higham24BitIndex t → ℂ}
    {t : ℕ} {x : Higham24BitIndex t → ℂ} {mu : ℝ}
    (hvalid : (t : ℝ) * higham24Eta mu (gamma fp 4) < 1)
    (trace : Higham24SourceRadix2ForwardErrorTrace fp weight t x mu) :
    higham24BinaryVecNorm2 t
        (higham24RoundedRadix2FFT fp weight t x - higham24Radix2FFT t x) /
      higham24BinaryVecNorm2 t (higham24Radix2FFT t x) ≤
        higham24RelativeFFTBound t (higham24Eta mu (gamma fp 4)) := by
  have heta : 0 ≤ higham24Eta mu (gamma fp 4) := by
    unfold higham24Eta
    exact add_nonneg trace.mu_nonneg
      (mul_nonneg (gamma_nonneg fp trace.gamma4_valid)
        (add_nonneg (Real.sqrt_nonneg _) trace.mu_nonneg))
  exact higham24_theorem24_2_of_errorTrace heta hvalid
    trace.toHigham24Radix2ForwardErrorTrace

end LeanFpAnalysis.FP
