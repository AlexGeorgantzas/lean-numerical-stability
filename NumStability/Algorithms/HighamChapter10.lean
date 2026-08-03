import Mathlib.Data.Complex.Basic
import NumStability.Algorithms.Cholesky.CholeskyDemmel
import NumStability.Algorithms.Cholesky.CholeskyFl
import NumStability.Algorithms.Cholesky.CholeskyIndefinite
import NumStability.Algorithms.Cholesky.CholeskyNonsym
import NumStability.Algorithms.Cholesky.CholeskyPSD
import NumStability.Algorithms.Cholesky.CholeskyPerturbation
import NumStability.Algorithms.Cholesky.CholeskySolve
import NumStability.Algorithms.Cholesky.CholeskySpec
import NumStability.Algorithms.LinearSystems.Cholesky.ErrorAnalysis.Certificates
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.KahanMatrix
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.ScaledStage
import NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic
import NumStability.Analysis.MatrixNorms.SpectralExtrema.Basic
import NumStability.Analysis.MatrixSpectral
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
import NumStability.Source.Higham.Chapter10.Equation07.AbsoluteFactorNorm.Endpoints
import NumStability.Source.Higham.Chapter10.Equation29.Mathias.Endpoints
import NumStability.Source.Higham.Chapter10.Equation30.ComplexPositiveDefinite.Endpoints
import NumStability.Source.Higham.Chapter10.Lemma11.PivotSequenceStability.Endpoints
import NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.Endpoints
import NumStability.Source.Higham.Chapter10.Problem01.PositiveSemidefiniteEntries.Basic
import NumStability.Source.Higham.Chapter10.Problem04.UnpivotedGrowth.Basic
import NumStability.Source.Higham.Chapter10.Problem08.LeadingMinorsCounterexample.Basic
import NumStability.Source.Higham.Chapter10.Section01.Factorization.Basic
import NumStability.Source.Higham.Chapter10.Section02.ErrorAnalysis.Basic
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Endpoints
import NumStability.Source.Higham.Chapter10.Section04.PositiveDefiniteSymmetricPart.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem06.RoundedCholesky.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem07.FailureVacuity.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem08.ComponentwisePerturbation.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem08.NormwiseDiscrepancy.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.Endpoints

/-!
# HighamChapter10 (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.HighamChapter10`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

open scoped BigOperators

namespace NumStability

/-- **Theorem 10.1**, existence of the Cholesky factorization for real SPD
matrices. -/
theorem higham10_1_cholesky_existence (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hSPD : IsSymPosDef n A) :
    ∃ R : Fin n → Fin n → ℝ, higham10_1_CholeskyFactSpec n A R :=
  cholesky_existence n A hSPD

/-- **Theorem 10.1**, uniqueness of the Cholesky factorization with positive
diagonal. -/
theorem higham10_1_cholesky_uniqueness (n : ℕ)
    (A R₁ R₂ : Fin n → Fin n → ℝ)
    (h₁ : higham10_1_CholeskyFactSpec n A R₁)
    (h₂ : higham10_1_CholeskyFactSpec n A R₂) :
    ∀ i j : Fin n, R₁ i j = R₂ i j :=
  cholesky_uniqueness n A R₁ R₂ h₁ h₂

/-- **Problem 10.4**, first-stage exact GE fact: the Schur-complement reduced
submatrix of an SPD matrix is again SPD. -/
theorem higham10_problem_10_4_first_ge_reduced_submatrix_spd {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hSPD : IsSymPosDef (m + 1) A) :
    IsSymPosDef m
      (fun i j => A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0) :=
  spd_schur_complement_isSymPosDef A hSPD

/-- **Problem 10.4**, one exact GE step: every entry of the first
Schur-complement reduced matrix is bounded by the initial max-entry norm. -/
theorem higham10_problem_10_4_first_ge_entry_abs_le_initial_max {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hSPD : IsSymPosDef (m + 1) A) :
    ∀ i j : Fin m,
      |A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0| ≤
        maxEntryNorm (Nat.succ_pos m) A := by
  let S : Fin m → Fin m → ℝ :=
    fun i j => A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0
  have hS : IsSymPosDef m S := spd_schur_complement_isSymPosDef A hSPD
  have hA00_pos : 0 < A 0 0 := higham10_spd_diag_pos A hSPD 0
  let M : ℝ := maxEntryNorm (Nat.succ_pos m) A
  have hM_pos : 0 < M := by
    have hentry := entry_le_maxEntryNorm (Nat.succ_pos m) A 0 0
    rw [abs_of_pos hA00_pos] at hentry
    exact lt_of_lt_of_le hA00_pos hentry
  have hdiag_le : ∀ i : Fin m, S i i ≤ M := by
    intro i
    have hAii_le : A i.succ i.succ ≤ M := by
      have hentry := entry_le_maxEntryNorm (Nat.succ_pos m) A i.succ i.succ
      rw [abs_of_pos (higham10_spd_diag_pos A hSPD i.succ)] at hentry
      exact hentry
    have hsub_nonneg : 0 ≤ A 0 i.succ * A 0 i.succ / A 0 0 := by
      have hnum : 0 ≤ A 0 i.succ * A 0 i.succ := by
        nlinarith [sq_nonneg (A 0 i.succ)]
      exact div_nonneg hnum (le_of_lt hA00_pos)
    dsimp [S]
    nlinarith
  intro i j
  by_cases hij : i = j
  · subst i
    rw [abs_of_pos (higham10_spd_diag_pos S hS j)]
    exact hdiag_le j
  · have hlt := higham10_problem_10_1_abs_offdiag_lt_sqrt_diag_mul S hS hij
    have hi_pos := higham10_spd_diag_pos S hS i
    have hj_pos := higham10_spd_diag_pos S hS j
    have hprod_le : S i i * S j j ≤ M ^ 2 := by
      nlinarith [hdiag_le i, hdiag_le j, le_of_lt hi_pos, le_of_lt hj_pos,
        le_of_lt hM_pos]
    have hsqrt_le : Real.sqrt (S i i * S j j) ≤ M := by
      have hs := Real.sqrt_le_sqrt hprod_le
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (le_of_lt hM_pos)] at hs
      exact hs
    exact le_trans (le_of_lt hlt) hsqrt_le

/-- **Problem 10.4**, one exact GE step: the max-entry norm of the first
Schur-complement reduced matrix is no larger than the initial max-entry norm. -/
theorem higham10_problem_10_4_first_ge_maxEntryNorm_le {m : ℕ} (hm : 0 < m)
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hSPD : IsSymPosDef (m + 1) A) :
    maxEntryNorm hm
      (fun i j : Fin m =>
        A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0) ≤
      maxEntryNorm (Nat.succ_pos m) A := by
  unfold maxEntryNorm
  apply Finset.sup'_le
  intro i _
  apply Finset.sup'_le
  intro j _
  exact higham10_problem_10_4_first_ge_entry_abs_le_initial_max A hSPD i j

/-- **Problem 10.4**, exact SPD GE induction: unpivoted Gaussian elimination
has positive pivots at every stage and max-entry growth factor at most `1`. -/
theorem higham10_problem_10_4_unpivoted_ge_positive_pivots_and_growth :
    ∀ (n : ℕ) (hn : 0 < n) (A : Fin n → Fin n → ℝ),
      IsSymPosDef n A →
      higham10_problem_10_4_unpivotedGEGrowthBounded n hn A := by
  intro n
  induction n with
  | zero =>
      intro hn _A _hSPD
      exact (Nat.not_lt_zero 0 hn).elim
  | succ n ih =>
      intro hn A hSPD
      cases n with
      | zero =>
          exact higham10_spd_diag_pos A hSPD 0
      | succ m =>
          let S : Fin (m + 1) → Fin (m + 1) → ℝ :=
            fun i j => A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0
          dsimp [higham10_problem_10_4_unpivotedGEGrowthBounded]
          refine ⟨higham10_spd_diag_pos A hSPD 0, ?_, ?_⟩
          · exact higham10_problem_10_4_first_ge_maxEntryNorm_le (Nat.succ_pos m) A hSPD
          · exact ih (Nat.succ_pos m) S
              (higham10_problem_10_4_first_ge_reduced_submatrix_spd A hSPD)

/-- **Algorithm 10.2 + Theorem 10.3, concrete closure**: the concrete
floating-point Cholesky factorization `fl_cholesky` (Algorithm 10.2), when
it runs to completion on a symmetric input (every rounded pivot
nonnegative, every computed diagonal entry nonzero), generates the
Theorem 10.3 backward-error certificate with the sharp `γ_{n+1}` constant:
the certificate hypothesis `higham10_2_CholeskyBackwardError` is discharged
by the algorithm itself rather than assumed. -/
theorem higham10_3_fl_cholesky_certificate (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i)
    (hn1 : gammaValid fp (n + 1))
    (hpiv : ∀ j : Fin n, 0 ≤ fl_cholPivot fp n A j)
    (hdz : ∀ j : Fin n, fl_cholesky fp n A j j ≠ 0) :
    higham10_2_CholeskyBackwardError n A (fl_cholesky fp n A)
      (gamma fp (n + 1)) :=
  fl_cholesky_backward_error fp n A hsym hn1 hpiv hdz

/-- **Theorem 10.3 / equation (10.5) for the concrete Algorithm 10.2
factor**: `R̂ᵀR̂ = A + ΔA` with `|ΔA| ≤ γ_{n+1}|R̂ᵀ||R̂|`, where `R̂` is the
actual computed `fl_cholesky` factor. -/
theorem higham10_3_fl_cholesky_backward_error (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i)
    (hn1 : gammaValid fp (n + 1))
    (hpiv : ∀ j : Fin n, 0 ≤ fl_cholPivot fp n A j)
    (hdz : ∀ j : Fin n, fl_cholesky fp n A j j ≠ 0) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp (n + 1) *
        ∑ k : Fin n, |fl_cholesky fp n A k i| * |fl_cholesky fp n A k j|) ∧
      (∀ i j, ∑ k : Fin n, fl_cholesky fp n A k i * fl_cholesky fp n A k j =
        A i j + ΔA i j) :=
  higham10_3_cholesky_backward_error fp n A (fl_cholesky fp n A) hn1
    (higham10_3_fl_cholesky_certificate fp n A hsym hn1 hpiv hdz)

/-- **Theorem 10.5 for the concrete Algorithm 10.2 factor**: Demmel's `dd^T`
bound with `d_i` the computed factor's column 2-norms, chained end-to-end
from the concrete `fl_cholesky` certificate — no assumed certificate or
Cauchy-Schwarz hypothesis remains. -/
theorem higham10_5_fl_cholesky_demmel_bound (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i)
    (hn1 : gammaValid fp (n + 1))
    (hγlt : gamma fp (n + 1) < 1)
    (hpiv : ∀ j : Fin n, 0 ≤ fl_cholPivot fp n A j)
    (hdz : ∀ j : Fin n, fl_cholesky fp n A j j ≠ 0) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp (n + 1) / (1 - gamma fp (n + 1)) *
        (colNorm n (fl_cholesky fp n A) i *
         colNorm n (fl_cholesky fp n A) j)) ∧
      (∀ i j, ∑ k : Fin n, fl_cholesky fp n A k i * fl_cholesky fp n A k j =
        A i j + ΔA i j) :=
  cholesky_demmel_bound_colNorm n A (fl_cholesky fp n A) (gamma fp (n + 1))
    (gamma_nonneg fp hn1) hγlt
    (fl_cholesky_backward_error fp n A hsym hn1 hpiv hdz)

/-- **Theorem 10.4 / equation (10.6) for the concrete Algorithm 10.2
factor**: factorization plus the two triangular solves on the computed
factor gives `(A + ΔA)x̂ = b` with the absorbed `γ_{3n+1}` componentwise
bound, chained end-to-end from the concrete `fl_cholesky` certificate. -/
theorem higham10_4_fl_cholesky_solve_backward_error (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i)
    (hn1 : gammaValid fp (n + 1))
    (hn3 : gammaValid fp (3 * n + 1))
    (hpiv : ∀ j : Fin n, 0 ≤ fl_cholPivot fp n A j)
    (hdz : ∀ j : Fin n, fl_cholesky fp n A j j ≠ 0) :
    let R_hat := fl_cholesky fp n A
    let R_hatT := fun i j : Fin n => R_hat j i
    let y_hat := fl_forwardSub fp n R_hatT b
    let x_hat := fl_backSub fp n R_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp (3 * n + 1) *
        ∑ k : Fin n, |R_hat k i| * |R_hat k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham10_4_cholesky_solve_backward_error fp n A (fl_cholesky fp n A) b hdz
    (fl_cholesky_backward_error fp n A hsym hn1 hpiv hdz) hn1 hn3

/-- **Theorem 10.7**, success as genuine factorization existence.

    Strengthens `higham10_7_success_condition` from the sign consequence
    `0 < lam_min` to the actual conclusion of Theorem 10.7: when the scaled
    matrix `H` has Rayleigh lower bound `lam` exceeding the scaled backward-error
    quadratic-form bound `t`, the perturbed scaled matrix `D (H + E) D` is SPD
    and has a genuine Cholesky factorization — Cholesky succeeds. The
    "min-eigenvalue → PD" step is now proved (`quadForm_add_pos_of_perturbation`,
    `isSymPosDef_diagCongr`), not assumed. -/
theorem higham10_7_success_factorization (n : ℕ)
    (D : Fin n → ℝ) (H E : Fin n → Fin n → ℝ) (lam t : ℝ)
    (hD_pos : ∀ i, 0 < D i)
    (hH_sym : ∀ i j, H i j = H j i)
    (hE_sym : ∀ i j, E i j = E j i)
    (hlam : ∀ x : Fin n → ℝ, (∃ i, x i ≠ 0) →
        lam * ∑ i : Fin n, x i ^ 2 ≤ ∑ i : Fin n, ∑ j : Fin n, x i * H i j * x j)
    (hE : ∀ x : Fin n → ℝ,
        |∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j| ≤ t * ∑ i : Fin n, x i ^ 2)
    (hlt : t < lam) :
    ∃ R : Fin n → Fin n → ℝ,
      CholeskyFactSpec n (fun i j => D i * (H i j + E i j) * D j) R :=
  cholesky_succeeds_of_scaled_perturbation n D H E lam t hD_pos hH_sym hE_sym
    hlam hE hlt

/-- **Theorem 10.7, spectral success form** (Higham §10.1): if the minimum
eigenvalue of the symmetric scaled matrix `H` — stated through the
repository's `finiteHermitianEigenvalues` — exceeds the scaled
backward-error quadratic-form bound `t`, then the perturbed scaled matrix
`D (H + E) D` has a genuine Cholesky factorization: the algorithm
succeeds.  This replaces the Rayleigh-quotient hypothesis of
`higham10_7_success_factorization` with the source's spectral `λ_min`
framing. -/
theorem higham10_7_success_factorization_spectral (n : ℕ)
    (D : Fin n → ℝ) (H E : Fin n → Fin n → ℝ) (lam t : ℝ)
    (hD_pos : ∀ i, 0 < D i)
    (hH_sym : IsSymmetricFiniteMatrix H)
    (hE_sym : ∀ i j, E i j = E j i)
    (hlam_le : ∀ a : Fin n, lam ≤ finiteHermitianEigenvalues H hH_sym a)
    (hE : ∀ x : Fin n → ℝ,
        |∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j| ≤
          t * ∑ i : Fin n, x i ^ 2)
    (hlt : t < lam) :
    ∃ R : Fin n → Fin n → ℝ,
      CholeskyFactSpec n (fun i j => D i * (H i j + E i j) * D j) R := by
  refine higham10_7_success_factorization n D H E lam t hD_pos
    (fun i j => hH_sym i j) hE_sym ?_ hE hlt
  intro x _hx
  have h := finiteLoewnerLe_smul_id_of_le_finiteHermitianEigenvalues
    H hH_sym hlam_le x
  rw [finiteQuadraticForm_smul_finiteIdMatrix,
    finiteQuadraticForm_eq_sum_sum] at h
  simpa [finiteVecNorm2Sq] using h

/-- **Theorem 10.7 success threshold, `λ_min` form** (Higham §10.1): if
`λ_min(H) > t`, the perturbed scaled matrix `D (H + E) D` has a genuine
Cholesky factorization. -/
theorem higham10_7_success_factorization_min_eig (n : ℕ) (hn : 0 < n)
    (D : Fin n → ℝ) (H E : Fin n → Fin n → ℝ) (t : ℝ)
    (hD_pos : ∀ i, 0 < D i)
    (hH_sym : IsSymmetricFiniteMatrix H)
    (hE_sym : ∀ i j, E i j = E j i)
    (hE : ∀ x : Fin n → ℝ,
        |∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j| ≤
          t * ∑ i : Fin n, x i ^ 2)
    (hlt : t < finiteMinEigenvalue hn H hH_sym) :
    ∃ R : Fin n → Fin n → ℝ,
      CholeskyFactSpec n (fun i j => D i * (H i j + E i j) * D j) R :=
  higham10_7_success_factorization_spectral n D H E
    (finiteMinEigenvalue hn H hH_sym) t hD_pos hH_sym hE_sym
    (finiteMinEigenvalue_le hn H hH_sym) hE hlt

/-- **Eigenvalue interlacing, lower direction** (Golub–Van Loan
Thm 8.1.7 as used in the Theorem 10.7 induction, Higham p. 200): the
minimum eigenvalue of a leading principal submatrix of a symmetric matrix
is at least the minimum eigenvalue of the full matrix.  Proof: evaluate
the full Rayleigh bound at the zero-padded minimizing eigenvector of the
submatrix. -/
theorem finiteMinEigenvalue_leading_principal_ge (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ) (hH : IsSymmetricFiniteMatrix H)
    (k : ℕ) (hk0 : 0 < k) (hk : k ≤ n)
    (hHk_sym : IsSymmetricFiniteMatrix
      (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)) :
    finiteMinEigenvalue hn H hH ≤
      finiteMinEigenvalue hk0
        (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
        hHk_sym := by
  obtain ⟨a, ha⟩ := exists_finiteMinEigenvalue_eq hk0
    (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) hHk_sym
  have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
    (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) hHk_sym a
  have hq :=
    finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
      (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) hHk_sym a
  rw [hnorm, mul_one] at hq
  set v : Fin k → ℝ :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian
      (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
      hHk_sym).eigenvectorBasis a) with hv
  have hvsq : ∑ i : Fin k, v i ^ 2 = 1 := by
    have := hnorm
    unfold finiteVecNorm2Sq at this
    exact this
  have hpadsq : ∑ i : Fin n,
      (if h : i.val < k then v ⟨i.val, h⟩ else 0) ^ 2 = 1 := by
    rw [sum_sq_zero_pad_eq k hk v, hvsq]
  have hray := finiteMinEigenvalue_rayleigh hn H hH
    (fun i => if h : i.val < k then v ⟨i.val, h⟩ else 0)
  rw [hpadsq, mul_one] at hray
  have hpadquad : ∑ i : Fin n, ∑ j : Fin n,
      (if h : i.val < k then v ⟨i.val, h⟩ else 0) * H i j *
        (if h : j.val < k then v ⟨j.val, h⟩ else 0) =
      finiteMinEigenvalue hk0
        (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
        hHk_sym := by
    rw [quadForm_zero_pad_eq H k hk v, ← ha, ← hq,
      finiteQuadraticForm_eq_sum_sum]
  rw [hpadquad] at hray
  exact hray

/-- **Theorem 10.7 (Demmel), success direction for the concrete
Algorithm 10.2** (Higham p. 200): if the minimum eigenvalue of the scaled
matrix `H = D⁻¹AD⁻¹` (`D = diag(√a_ii)`) exceeds
`(2n+3)·γ_{n+1}/(1−γ_{n+1})`, the concrete floating-point Cholesky
algorithm runs to completion: every rounded pivot is positive.  Per-stage
Rayleigh floors come from `λ_min(H)` by interlacing on the bordered
leading blocks and the substitution `z = (√a_i·y_i, √a_jj)`.  The
threshold constant is coarser than the source `n·γ_{n+1}/(1−γ_{n+1})`;
sharpening is open. -/
theorem higham10_7_fl_cholesky_success (fp : FPModel) (n : ℕ)
    (hn0 : 0 < n) (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1)
    (hH_sym : IsSymmetricFiniteMatrix (fun i l : Fin n =>
      A i l / (Real.sqrt (A i i) * Real.sqrt (A l l))))
    (hthresh : (2 * (n : ℝ) + 3) *
      (gamma fp (n + 1) / (1 - gamma fp (n + 1))) <
      finiteMinEigenvalue hn0 (fun i l : Fin n =>
        A i l / (Real.sqrt (A i i) * Real.sqrt (A l l))) hH_sym) :
    ∀ j : Fin n, 0 < fl_cholPivot fp n A j := by
  apply fl_cholesky_pivots_pos fp A hsym hAdiag hn1 hγ1
    (finiteMinEigenvalue hn0 _ hH_sym) _ hthresh
  intro j y
  have hm1n : j.val + 1 ≤ n := j.isLt
  have hHb_sym : IsSymmetricFiniteMatrix (fun i l : Fin (j.val + 1) =>
      (fun i l : Fin n => A i l / (Real.sqrt (A i i) * Real.sqrt (A l l)))
        ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) :=
    fun i l => hH_sym _ _
  have hinterlace := finiteMinEigenvalue_leading_principal_ge n hn0 _
    hH_sym (j.val + 1) (Nat.succ_pos j.val) hm1n hHb_sym
  set z : Fin (j.val + 1) → ℝ := Fin.snoc
    (fun i : Fin j.val =>
      Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) * y i)
    (Real.sqrt (A j j)) with hz
  have hray := finiteMinEigenvalue_rayleigh (Nat.succ_pos j.val)
    (fun i l : Fin (j.val + 1) =>
      (fun i l : Fin n => A i l / (Real.sqrt (A i i) * Real.sqrt (A l l)))
        ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) hHb_sym z
  have hlast_eq : (⟨(Fin.last j.val).val, by omega⟩ : Fin n) = j :=
    Fin.ext (by simp)
  have hcancel : ∀ (i l : Fin n) (u v : ℝ),
      (Real.sqrt (A i i) * u) *
        (A i l / (Real.sqrt (A i i) * Real.sqrt (A l l))) *
        (Real.sqrt (A l l) * v) = u * A i l * v := by
    intro i l u v
    have hi := (Real.sqrt_pos.mpr (hAdiag i)).ne'
    have hl := (Real.sqrt_pos.mpr (hAdiag l)).ne'
    field_simp
  have hnorm : ∑ i : Fin (j.val + 1), z i ^ 2 =
      (∑ i : Fin j.val,
        A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) + A j j := by
    rw [Fin.sum_univ_castSucc]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      rw [hz, Fin.snoc_castSucc, mul_pow, Real.sq_sqrt (hAdiag _).le]
    · rw [hz, Fin.snoc_last, Real.sq_sqrt (hAdiag j).le]
  have hz_nonneg_sq : 0 ≤ ∑ i : Fin (j.val + 1), z i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hquad : ∑ i : Fin (j.val + 1), ∑ l : Fin (j.val + 1),
      z i * ((fun i l : Fin n =>
        A i l / (Real.sqrt (A i i) * Real.sqrt (A l l)))
        ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) * z l =
      (∑ i : Fin j.val, ∑ l : Fin j.val,
        y i * A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l) +
      2 * (∑ i : Fin j.val, y i * A ⟨i.val, by omega⟩ j) + A j j := by
    rw [sum_sum_castSucc_split j.val]
    have hp1 : ∑ i : Fin j.val, ∑ l : Fin j.val,
        z i.castSucc * ((fun i l : Fin n =>
          A i l / (Real.sqrt (A i i) * Real.sqrt (A l l)))
          ⟨(i.castSucc).val, by omega⟩ ⟨(l.castSucc).val, by omega⟩) *
          z l.castSucc =
        ∑ i : Fin j.val, ∑ l : Fin j.val,
          y i * A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro l _
      rw [hz, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact hcancel _ _ (y i) (y l)
    have hp2 : ∑ i : Fin j.val,
        z i.castSucc * ((fun i l : Fin n =>
          A i l / (Real.sqrt (A i i) * Real.sqrt (A l l)))
          ⟨(i.castSucc).val, by omega⟩
          ⟨(Fin.last j.val).val, by omega⟩) * z (Fin.last j.val) =
        ∑ i : Fin j.val, y i * A ⟨i.val, by omega⟩ j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hz, Fin.snoc_castSucc, Fin.snoc_last, hlast_eq]
      have hthis := hcancel ⟨i.val, by omega⟩ j (y i) 1
      simp only [mul_one] at hthis
      exact hthis
    have hp3 : ∑ l : Fin j.val,
        z (Fin.last j.val) * ((fun i l : Fin n =>
          A i l / (Real.sqrt (A i i) * Real.sqrt (A l l)))
          ⟨(Fin.last j.val).val, by omega⟩
          ⟨(l.castSucc).val, by omega⟩) * z l.castSucc =
        ∑ l : Fin j.val, y l * A ⟨l.val, by omega⟩ j := by
      apply Finset.sum_congr rfl
      intro l _
      rw [hz, Fin.snoc_castSucc, Fin.snoc_last, hlast_eq]
      have hthis := hcancel j ⟨l.val, by omega⟩ 1 (y l)
      simp only [one_mul, mul_one] at hthis
      have hfin : Real.sqrt (A j j) *
          (A j ⟨l.val, by omega⟩ /
            (Real.sqrt (A j j) *
             Real.sqrt (A ⟨l.val, by omega⟩ ⟨l.val, by omega⟩))) *
          (Real.sqrt (A ⟨l.val, by omega⟩ ⟨l.val, by omega⟩) * y l) =
          y l * A ⟨l.val, by omega⟩ j := by
        rw [hthis, hsym j ⟨l.val, by omega⟩]
        ring
      exact hfin
    have hp4 : z (Fin.last j.val) * ((fun i l : Fin n =>
        A i l / (Real.sqrt (A i i) * Real.sqrt (A l l)))
        ⟨(Fin.last j.val).val, by omega⟩
        ⟨(Fin.last j.val).val, by omega⟩) * z (Fin.last j.val) =
        A j j := by
      rw [hz, Fin.snoc_last, hlast_eq]
      have hthis := hcancel j j 1 1
      simp only [one_mul, mul_one] at hthis
      exact hthis
    rw [hp1, hp2, hp3, hp4]
    ring
  have hmono : finiteMinEigenvalue hn0 _ hH_sym *
      ∑ i : Fin (j.val + 1), z i ^ 2 ≤
      finiteMinEigenvalue (Nat.succ_pos j.val) _ hHb_sym *
      ∑ i : Fin (j.val + 1), z i ^ 2 :=
    mul_le_mul_of_nonneg_right hinterlace hz_nonneg_sq
  calc finiteMinEigenvalue hn0 _ hH_sym *
      ((∑ i : Fin j.val,
        A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) + A j j)
      = finiteMinEigenvalue hn0 _ hH_sym *
        ∑ i : Fin (j.val + 1), z i ^ 2 := by rw [hnorm]
    _ ≤ finiteMinEigenvalue (Nat.succ_pos j.val) _ hHb_sym *
        ∑ i : Fin (j.val + 1), z i ^ 2 := hmono
    _ ≤ ∑ i : Fin (j.val + 1), ∑ l : Fin (j.val + 1),
        z i * ((fun i l : Fin n =>
          A i l / (Real.sqrt (A i i) * Real.sqrt (A l l)))
          ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) * z l := hray
    _ = (∑ i : Fin j.val, ∑ l : Fin j.val,
          y i * A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l) +
        2 * (∑ i : Fin j.val, y i * A ⟨i.val, by omega⟩ j) + A j j := hquad

/-- **Theorem 10.9(a)**: every real PSD matrix has an upper-triangular
`R` with nonnegative diagonal and `A = R^T R`. -/
theorem higham10_9_psd_cholesky_existence (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n A) :
    ∃ R : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, j.val < i.val → R i j = 0) ∧
      (∀ i : Fin n, 0 ≤ R i i) ∧
      (∀ i j : Fin n, ∑ k : Fin n, R k i * R k j = A i j) :=
  psd_cholesky_existence n A hPSD

/-- **Theorem 10.9(b)**, full-rank/SPD specialization of the pivoted form
with identity permutation. -/
theorem higham10_9_spd_pivoted_cholesky_full_rank (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hSPD : IsSymPosDef n A) :
    ∃ R : Fin n → Fin n → ℝ,
      higham10_9_PivotedCholeskySpec n A R id n :=
  spd_pivoted_cholesky n A hSPD

/-- **Theorem 10.9(b), pivoted PSD existence with the rank identified**:
    every real positive-semidefinite matrix admits a permutation and a
    rank-truncated upper-triangular factor of the displayed form (10.11), and
    the truncation index is exactly the matrix rank.  The greedy constructive
    proof and the two rank inequalities live in `CholeskyPSD`; this theorem is
    the missing chapter-facing assembly. -/
theorem higham10_9_psd_pivoted_cholesky_rank (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n A) :
    ∃ (r : ℕ) (σ : Fin n → Fin n) (R : Fin n → Fin n → ℝ),
      r ≤ n ∧
      higham10_9_PivotedCholeskySpec n A R σ r ∧
      (Matrix.of A).rank = r := by
  obtain ⟨r₀, σ, R, hspec₀⟩ := psd_pivoted_cholesky_exists n A hPSD
  let r := min r₀ n
  have hr : r ≤ n := by
    exact Nat.min_le_right r₀ n
  have hspec : higham10_9_PivotedCholeskySpec n A R σ r :=
    higham10_9_pivotedCholeskySpec_min_rank hspec₀
  exact ⟨r, σ, R, hr, hspec, pivoted_spec_rank_eq_r hspec hr⟩

/-- Split an upper-triangular Gram-product sum at its diagonal row. -/
private lemma higham10_9_upper_product_sum_split {n : ℕ}
    (R : Fin n → Fin n → ℝ)
    (hupper : ∀ i j : Fin n, j.val < i.val → R i j = 0)
    (i j : Fin n) :
    (∑ p : Fin n, R p i * R p j) =
      (∑ p ∈ Finset.univ.filter (fun p : Fin n => p.val < i.val),
        R p i * R p j) + R i i * R i j := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun p : Fin n => p.val < i.val) (fun p => R p i * R p j)]
  congr 1
  apply Finset.sum_eq_single i
  · intro p hp hpi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hp
    have hip : i.val < p.val := by
      have hne : i.val ≠ p.val := fun h => hpi (Fin.ext h.symm)
      omega
    rw [hupper p i hip, zero_mul]
  · simp

/-- **Theorem 10.9(b), uniqueness for the selected permutation.**  Two
    rank-truncated pivoted Cholesky factors with the same permutation and rank
    are equal.  Induction over the positive leading rows first identifies the
    diagonal from the Gram product and positivity, then cancels that pivot to
    identify the rest of the row; all rows at or beyond `r` vanish by the
    displayed block structure. -/
theorem higham10_9_pivoted_cholesky_unique {n : ℕ}
    {A R₁ R₂ : Fin n → Fin n → ℝ} {σ : Fin n → Fin n} {r : ℕ}
    (h₁ : higham10_9_PivotedCholeskySpec n A R₁ σ r)
    (h₂ : higham10_9_PivotedCholeskySpec n A R₂ σ r) :
    R₁ = R₂ := by
  have hrows : ∀ k : ℕ, k < r → ∀ i : Fin n, i.val = k →
      ∀ j : Fin n, R₁ i j = R₂ i j := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hkr i hik
      have hprior : ∀ p : Fin n, p.val < i.val →
          ∀ j : Fin n, R₁ p j = R₂ p j := by
        intro p hpi j
        exact ih p.val (by omega) (by omega) p rfl j
      have hdiag : R₁ i i = R₂ i i := by
        have hp : (∑ p : Fin n, R₁ p i * R₁ p i) =
            ∑ p : Fin n, R₂ p i * R₂ p i := by
          rw [h₁.product_eq i i, h₂.product_eq i i]
        rw [higham10_9_upper_product_sum_split R₁ h₁.R_upper i i,
          higham10_9_upper_product_sum_split R₂ h₂.R_upper i i] at hp
        have hhead :
            (∑ p ∈ Finset.univ.filter (fun p : Fin n => p.val < i.val),
                R₁ p i * R₁ p i) =
              ∑ p ∈ Finset.univ.filter (fun p : Fin n => p.val < i.val),
                R₂ p i * R₂ p i := by
          apply Finset.sum_congr rfl
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
          rw [hprior p hp i]
        rw [hhead] at hp
        have hpos₁ := h₁.R_diag_pos i (by omega)
        have hpos₂ := h₂.R_diag_pos i (by omega)
        nlinarith
      intro j
      have hp : (∑ p : Fin n, R₁ p i * R₁ p j) =
          ∑ p : Fin n, R₂ p i * R₂ p j := by
        rw [h₁.product_eq i j, h₂.product_eq i j]
      rw [higham10_9_upper_product_sum_split R₁ h₁.R_upper i j,
        higham10_9_upper_product_sum_split R₂ h₂.R_upper i j] at hp
      have hhead :
          (∑ p ∈ Finset.univ.filter (fun p : Fin n => p.val < i.val),
              R₁ p i * R₁ p j) =
            ∑ p ∈ Finset.univ.filter (fun p : Fin n => p.val < i.val),
              R₂ p i * R₂ p j := by
        apply Finset.sum_congr rfl
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        rw [hprior p hp i, hprior p hp j]
      rw [hhead, hdiag] at hp
      have hmul : R₂ i i * R₁ i j = R₂ i i * R₂ i j := by
        linarith
      exact mul_left_cancel₀ (h₂.R_diag_pos i (by omega)).ne' hmul
  funext i j
  by_cases hi : i.val < r
  · exact hrows i.val hi i rfl j
  · rw [h₁.R_rank_zero i j (by omega), h₂.R_rank_zero i j (by omega)]

/-- **Theorem 10.9(b), full source-facing assembly**: a PSD matrix admits a
    permutation and a unique rank-truncated Cholesky factor of the form
    `(10.11)`, and the truncation index is the matrix rank. -/
theorem higham10_9_psd_pivoted_cholesky_rank_unique (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n A) :
    ∃ (r : ℕ) (σ : Fin n → Fin n) (R : Fin n → Fin n → ℝ),
      r ≤ n ∧
      higham10_9_PivotedCholeskySpec n A R σ r ∧
      (Matrix.of A).rank = r ∧
      ∀ R' : Fin n → Fin n → ℝ,
        higham10_9_PivotedCholeskySpec n A R' σ r → R' = R := by
  obtain ⟨r, σ, R, hr, hspec, hrank⟩ :=
    higham10_9_psd_pivoted_cholesky_rank n A hPSD
  exact ⟨r, σ, R, hr, hspec, hrank,
    fun R' hspec' => higham10_9_pivoted_cholesky_unique hspec' hspec⟩

/-- **Lemma 10.12, trace form** (fully computable certificate): the
    solve action `Wv = M A₁₂ v` of a PSD block matrix satisfies
    `‖Wv‖₂² ≤ (tr A₂₂ / λ_min(A₁₁)) ‖v‖₂²` — the `c₂₂` certificate of
    `higham10_12_w_action_norm_bound` discharged by
    `psd_quadForm_le_trace` on the trailing block. -/
theorem higham10_12_w_action_trace_bound {k m : ℕ} (hk : 0 < k)
    (A : Fin (k + m) → Fin (k + m) → ℝ)
    (hPSD : IsPosSemiDef (k + m) A)
    (M : Fin k → Fin k → ℝ)
    (hSym : IsSymmetricFiniteMatrix
      (fun i j : Fin k => A (Fin.castAdd m i) (Fin.castAdd m j)))
    (hMinv : ∀ (w : Fin k → ℝ) (i : Fin k),
      ∑ j : Fin k, A (Fin.castAdd m i) (Fin.castAdd m j) *
        (∑ t : Fin k, M j t * w t) = w i)
    (hlampos : 0 < finiteMinEigenvalue hk
      (fun i j : Fin k => A (Fin.castAdd m i) (Fin.castAdd m j)) hSym)
    (v : Fin m → ℝ) :
    vecNorm2Sq (fun i : Fin k => ∑ t : Fin k, M i t *
      (∑ j : Fin m, A (Fin.castAdd m t) (Fin.natAdd k j) * v j)) ≤
    ((∑ j : Fin m, A (Fin.natAdd k j) (Fin.natAdd k j)) /
        finiteMinEigenvalue hk
          (fun i j : Fin k => A (Fin.castAdd m i) (Fin.castAdd m j))
          hSym)
      * vecNorm2Sq v := by
  refine higham10_12_w_action_norm_bound hk A hPSD M hSym hMinv
    hlampos _ (fun w => ?_) v
  have h := psd_quadForm_le_trace
    (fun i j : Fin m => A (Fin.natAdd k i) (Fin.natAdd k j))
    (isPosSemiDef_trailing_block A hPSD) w
  simpa [vecNorm2Sq] using h

/-- **Spectral bounds for unit-diagonal PSD matrices** (the van der
    Sluis (10.9) route ingredient): the scaled matrix `H = D⁻¹AD⁻¹`
    with `D = diag(√a_ii)` has unit diagonal, and any unit-diagonal PSD
    matrix has `1 ≤ λ_max ≤ n` — the upper bound from the trace, the
    lower from the Rayleigh quotient at a coordinate vector. -/
theorem unit_diag_psd_maxEigenvalue_bounds {n : ℕ} (hn : 0 < n)
    (H : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n H)
    (hdiag : ∀ i : Fin n, H i i = 1)
    (hSym : IsSymmetricFiniteMatrix H) :
    1 ≤ finiteMaxEigenvalue hn H hSym ∧
      finiteMaxEigenvalue hn H hSym ≤ (n : ℝ) := by
  constructor
  · -- Rayleigh at a coordinate vector
    set e : Fin n → ℝ := fun k => if k = ⟨0, hn⟩ then 1 else 0 with he
    have hray := finiteMaxEigenvalue_rayleigh hn H hSym e
    have hquad : ∑ i : Fin n, ∑ j : Fin n, e i * H i j * e j =
        H ⟨0, hn⟩ ⟨0, hn⟩ := by
      simp [he, Finset.sum_ite_eq', Finset.mul_sum]
    have hnorm : ∑ i : Fin n, e i ^ 2 = 1 := by
      simp [he, Finset.sum_ite_eq']
    rw [hquad, hnorm, mul_one, hdiag] at hray
    exact hray
  · -- trace bound at the top eigenvector
    obtain ⟨a, ha⟩ := exists_finiteMaxEigenvalue_eq hn H hSym
    have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
      H hSym a
    have hq :=
      finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
        H hSym a
    rw [hnorm, mul_one] at hq
    set v : Fin n → ℝ :=
      ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian H
        hSym).eigenvectorBasis a) with hv
    have hvsq : ∑ i : Fin n, v i ^ 2 = 1 := by
      have := hnorm
      unfold finiteVecNorm2Sq at this
      exact this
    have hqv : ∑ i : Fin n, ∑ j : Fin n, v i * H i j * v j =
        finiteMaxEigenvalue hn H hSym := by
      rw [← ha, ← hq, finiteQuadraticForm_eq_sum_sum]
    have htr := psd_quadForm_le_trace H hPSD v
    have htrace : ∑ i : Fin n, H i i = (n : ℝ) := by
      simp [hdiag]
    rw [hqv, htrace, hvsq, mul_one] at htr
    exact htr

/-- **Condition-number certificate for the scaled matrix** (van der
    Sluis route, display (10.9) fragment): a unit-diagonal PSD matrix
    with positive smallest eigenvalue has
    `κ₂(H) = λ_max/λ_min ≤ n/λ_min`. -/
theorem higham10_9_unit_diag_cond_bound {n : ℕ} (hn : 0 < n)
    (H : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n H)
    (hdiag : ∀ i : Fin n, H i i = 1)
    (hSym : IsSymmetricFiniteMatrix H)
    (hmin : 0 < finiteMinEigenvalue hn H hSym) :
    finiteMaxEigenvalue hn H hSym / finiteMinEigenvalue hn H hSym ≤
      (n : ℝ) / finiteMinEigenvalue hn H hSym := by
  have h := (unit_diag_psd_maxEigenvalue_bounds hn H hPSD hdiag
    hSym).2
  gcongr

/-- **Display (10.9) fragment for the concrete scaled matrix**: for SPD
    data (`A` PSD with positive diagonal), the van der Sluis scaling
    `H = D⁻¹AD⁻¹` satisfies `κ₂(H) ≤ n/λ_min(H)`. -/
theorem higham10_9_scaled_cond_bound {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n A)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hSym : IsSymmetricFiniteMatrix
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))))
    (hmin : 0 < finiteMinEigenvalue hn
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))) hSym) :
    finiteMaxEigenvalue hn
        (fun i l : Fin n => A i l /
          (Real.sqrt (A i i) * Real.sqrt (A l l))) hSym /
      finiteMinEigenvalue hn
        (fun i l : Fin n => A i l /
          (Real.sqrt (A i i) * Real.sqrt (A l l))) hSym ≤
    (n : ℝ) / finiteMinEigenvalue hn
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))) hSym :=
  higham10_9_unit_diag_cond_bound hn _
    (scaled_matrix_isPosSemiDef A hPSD hAdiag)
    (fun i => scaled_matrix_unit_diag A hAdiag i) hSym hmin

/-- **van der Sluis / display (10.9)**: the √-scaling is within a
    factor `n` of every diagonal scaling —
    `κ₂(H) ≤ n·κ₂(DAD)` for every positive diagonal `D`, hence
    `κ₂(H) ≤ n·min_D κ₂(DAD)`. `B` names the largest `d_i²a_ii`
    (supplied with its attainment witness). Chain:
    `λ_max(H) ≤ n` (unit diagonal), `λ_min(H) ≥ λ_min(DAD)/B`
    (diagonal congruence `H = E(DAD)E`, `e_i = 1/(d_i√a_ii)`), and
    `B ≤ λ_max(DAD)` (a diagonal Rayleigh value). -/
theorem higham10_9_van_der_sluis {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n A)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (d : Fin n → ℝ) (hd : ∀ i : Fin n, 0 < d i)
    (hSymH : IsSymmetricFiniteMatrix
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))))
    (hSymM : IsSymmetricFiniteMatrix
      (fun i j : Fin n => d i * A i j * d j))
    (hminM : 0 < finiteMinEigenvalue hn
      (fun i j : Fin n => d i * A i j * d j) hSymM)
    (B : ℝ) (hB : ∀ i : Fin n, d i ^ 2 * A i i ≤ B)
    (hattain : ∃ k : Fin n, d k ^ 2 * A k k = B) :
    finiteMaxEigenvalue hn
        (fun i l : Fin n => A i l /
          (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH /
      finiteMinEigenvalue hn
        (fun i l : Fin n => A i l /
          (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH ≤
    (n : ℝ) * finiteMaxEigenvalue hn
        (fun i j : Fin n => d i * A i j * d j) hSymM /
      finiteMinEigenvalue hn
        (fun i j : Fin n => d i * A i j * d j) hSymM := by
  obtain ⟨k, hk⟩ := hattain
  have hB0 : (0:ℝ) < B := by
    rw [← hk]
    have hdk := hd k
    have hak := hAdiag k
    positivity
  -- B is a Rayleigh value of M
  have hBmax : B ≤ finiteMaxEigenvalue hn
      (fun i j : Fin n => d i * A i j * d j) hSymM := by
    have h := finiteMaxEigenvalue_ge_diag hn
      (fun i j : Fin n => d i * A i j * d j) hSymM k
    have h2 : d k * A k k * d k = B := by rw [← hk]; ring
    calc B = d k * A k k * d k := h2.symm
      _ ≤ _ := h
  -- H is the diagonal congruence of M by e = 1/(d√a)
  have hHM : (fun i j : Fin n =>
      (1 / (d i * Real.sqrt (A i i))) *
        (d i * A i j * d j) *
        (1 / (d j * Real.sqrt (A j j)))) =
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))) := by
    funext i j
    have hi := Real.sqrt_pos.mpr (hAdiag i)
    have hj := Real.sqrt_pos.mpr (hAdiag j)
    have hdi := hd i
    have hdj := hd j
    field_simp
  -- the congruence floor for λ_min(H)
  have hmfloor : ∀ i : Fin n,
      1 / B ≤ (1 / (d i * Real.sqrt (A i i))) ^ 2 := by
    intro i
    have hi := Real.sqrt_pos.mpr (hAdiag i)
    have hdi := hd i
    rw [div_pow, one_pow]
    have hsq : (d i * Real.sqrt (A i i)) ^ 2 = d i ^ 2 * A i i := by
      rw [mul_pow, Real.sq_sqrt (hAdiag i).le]
    rw [hsq]
    have hai := hAdiag i
    have h1 : (0:ℝ) < d i ^ 2 * A i i := by positivity
    exact one_div_le_one_div_of_le h1 (hB i)
  have hSymH' : IsSymmetricFiniteMatrix
      (fun i j : Fin n =>
        (1 / (d i * Real.sqrt (A i i))) *
          (d i * A i j * d j) *
          (1 / (d j * Real.sqrt (A j j)))) := by
    rw [hHM]; exact hSymH
  have hcong := diag_congruence_minEigenvalue_ge hn
    (fun i j : Fin n => d i * A i j * d j) hSymM
    (fun i => 1 / (d i * Real.sqrt (A i i))) (1 / B)
    (one_div_pos.mpr hB0).le hmfloor hSymH' hminM.le
  -- transport across the congruence identity
  have hminH_ge : (1 / B) * finiteMinEigenvalue hn
      (fun i j : Fin n => d i * A i j * d j) hSymM ≤
      finiteMinEigenvalue hn
        (fun i l : Fin n => A i l /
          (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH := by
    refine hcong.trans_eq ?_
    congr 1
  have hminH0 : 0 < finiteMinEigenvalue hn
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH := by
    have : (0:ℝ) < (1 / B) * finiteMinEigenvalue hn
        (fun i j : Fin n => d i * A i j * d j) hSymM :=
      mul_pos (one_div_pos.mpr hB0) hminM
    linarith [hminH_ge]
  -- assemble the condition-number comparison
  have hmaxH : finiteMaxEigenvalue hn
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH ≤ (n : ℝ) :=
    (unit_diag_psd_maxEigenvalue_bounds hn _
      (scaled_matrix_isPosSemiDef A hPSD hAdiag)
      (fun i => scaled_matrix_unit_diag A hAdiag i) hSymH).2
  rw [div_le_div_iff₀ hminH0 hminM]
  have h1 : finiteMaxEigenvalue hn
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH *
      finiteMinEigenvalue hn
        (fun i j : Fin n => d i * A i j * d j) hSymM ≤
      (n : ℝ) * finiteMinEigenvalue hn
        (fun i j : Fin n => d i * A i j * d j) hSymM :=
    mul_le_mul_of_nonneg_right hmaxH hminM.le
  have h2 : finiteMinEigenvalue hn
      (fun i j : Fin n => d i * A i j * d j) hSymM ≤
      B * finiteMinEigenvalue hn
        (fun i l : Fin n => A i l /
          (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH := by
    have := mul_le_mul_of_nonneg_left hminH_ge hB0.le
    calc finiteMinEigenvalue hn
          (fun i j : Fin n => d i * A i j * d j) hSymM
        = B * ((1 / B) * finiteMinEigenvalue hn
            (fun i j : Fin n => d i * A i j * d j) hSymM) := by
          field_simp
      _ ≤ B * finiteMinEigenvalue hn
            (fun i l : Fin n => A i l /
              (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH := this
  have h3 : (n : ℝ) * B ≤ (n : ℝ) *
      finiteMaxEigenvalue hn
        (fun i j : Fin n => d i * A i j * d j) hSymM :=
    mul_le_mul_of_nonneg_left hBmax (Nat.cast_nonneg n)
  have h4 : (n : ℝ) * finiteMinEigenvalue hn
      (fun i j : Fin n => d i * A i j * d j) hSymM ≤
      (n : ℝ) * (B * finiteMinEigenvalue hn
        (fun i l : Fin n => A i l /
          (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH) :=
    mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg n)
  have h5 : ((n : ℝ) * B) * finiteMinEigenvalue hn
      (fun i l : Fin n => A i l /
        (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH ≤
      ((n : ℝ) * finiteMaxEigenvalue hn
        (fun i j : Fin n => d i * A i j * d j) hSymM) *
      finiteMinEigenvalue hn
        (fun i l : Fin n => A i l /
          (Real.sqrt (A i i) * Real.sqrt (A l l))) hSymH :=
    mul_le_mul_of_nonneg_right h3 hminH0.le
  nlinarith [h1, h4, h5]

/-- **Eigenvalue interlacing, upper direction** (the dual of
    `finiteMinEigenvalue_leading_principal_ge`, completing the
    two-sided leading-block spectral envelope): the maximum eigenvalue
    of a leading principal submatrix is at most the maximum eigenvalue
    of the full matrix — evaluate the full max-Rayleigh bound at the
    zero-padded maximizing eigenvector of the submatrix. -/
theorem finiteMaxEigenvalue_leading_principal_le (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ) (hH : IsSymmetricFiniteMatrix H)
    (k : ℕ) (hk0 : 0 < k) (hk : k ≤ n)
    (hHk_sym : IsSymmetricFiniteMatrix
      (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)) :
    finiteMaxEigenvalue hk0
        (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
        hHk_sym ≤
      finiteMaxEigenvalue hn H hH := by
  obtain ⟨a, ha⟩ := exists_finiteMaxEigenvalue_eq hk0
    (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) hHk_sym
  have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
    (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
    hHk_sym a
  have hq :=
    finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
      (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
      hHk_sym a
  rw [hnorm, mul_one] at hq
  set v : Fin k → ℝ :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian
      (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
      hHk_sym).eigenvectorBasis a) with hv
  have hvsq : ∑ i : Fin k, v i ^ 2 = 1 := by
    have := hnorm
    unfold finiteVecNorm2Sq at this
    exact this
  have hpadsq : ∑ i : Fin n,
      (if h : i.val < k then v ⟨i.val, h⟩ else 0) ^ 2 = 1 := by
    rw [sum_sq_zero_pad_eq k hk v, hvsq]
  have hray := finiteMaxEigenvalue_rayleigh hn H hH
    (fun i => if h : i.val < k then v ⟨i.val, h⟩ else 0)
  rw [hpadsq, mul_one] at hray
  have hpadquad : ∑ i : Fin n, ∑ j : Fin n,
      (if h : i.val < k then v ⟨i.val, h⟩ else 0) * H i j *
        (if h : j.val < k then v ⟨j.val, h⟩ else 0) =
      finiteMaxEigenvalue hk0
        (fun i j : Fin k => H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
        hHk_sym := by
    rw [quadForm_zero_pad_eq H k hk v, ← ha, ← hq,
      finiteQuadraticForm_eq_sum_sum]
  rw [hpadquad] at hray
  exact hray

/-- **Per-stage interior mass from the full scaled certificate**
    (Theorem 10.7 sharp route, certificate restriction): a single
    quadratic-form certificate `ε` on the full scaled defect restricts
    to every leading block by zero-padding — the stage-`k` interior
    mass hypothesis of `fl_cholesky_pivot_pos_step_sharp` follows for
    all stages at once. -/
theorem stage_interior_mass_from_full {n : ℕ}
    (Δ : Fin n → Fin n → ℝ) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (ε : ℝ)
    (hcert : ∀ z : Fin n → ℝ,
      |∑ i : Fin n, ∑ j : Fin n, z i *
        (Δ i j / (Real.sqrt (a i) * Real.sqrt (a j))) * z j| ≤
      ε * ∑ i : Fin n, z i ^ 2)
    (hnz : ∀ i j : Fin n, a i = 0 ∨ a j = 0 → Δ i j = 0)
    (k : ℕ) (hk : k ≤ n) (y : Fin k → ℝ) :
    |∑ i : Fin k, ∑ j : Fin k, y i *
      Δ ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ * y j| ≤
      ε * ∑ i : Fin k, a ⟨i.val, by omega⟩ * y i ^ 2 := by
  refine scaled_interior_mass_normwise_quad
    (fun i j : Fin k => Δ ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
    (fun i : Fin k => a ⟨i.val, by omega⟩) (fun i => ha _) ε
    ?_ y (fun i j h => hnz _ _ h)
  intro z
  have hpad := hcert
    (fun i : Fin n => if h : i.val < k then z ⟨i.val, h⟩ else 0)
  have hq := quadForm_zero_pad_eq
    (fun i j : Fin n => Δ i j /
      (Real.sqrt (a i) * Real.sqrt (a j))) k hk z
  have hs := sum_sq_zero_pad_eq k hk z
  rw [hq, hs] at hpad
  exact hpad

/-- **Theorem 10.7 at the source-shaped threshold, certified form**: all
    rounded pivots are positive at `λ > ε + 2γ_{n+1}` given ONLY
    run-level normwise certificates — one quadratic-form certificate on
    the scaled full Gram defect and one scaled column-norm certificate
    per column — the per-stage mass hypotheses being discharged by
    zero-pad restriction. -/
theorem fl_cholesky_pivots_pos_sharp_certified (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1)
    (lam ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hfloor : ∀ j : Fin n, ∀ y : Fin j.val → ℝ,
      lam * ((∑ i : Fin j.val,
          A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) + A j j) ≤
        (∑ i : Fin j.val, ∑ l : Fin j.val,
          y i * A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l) +
        2 * (∑ i : Fin j.val, y i * A ⟨i.val, by omega⟩ j) + A j j)
    (hcertI : ∀ z : Fin n → ℝ,
      |∑ i : Fin n, ∑ l : Fin n, z i *
        (((∑ p : Fin n, fl_cholesky fp n A p i *
            fl_cholesky fp n A p l) - A i l) /
          (Real.sqrt (A i i) * Real.sqrt (A l l))) * z l| ≤
      ε * ∑ i : Fin n, z i ^ 2)
    (hcertB : ∀ j : Fin n, ∑ i : Fin n,
      (if A i i = 0 then 0 else
        ((∑ p : Fin n, fl_cholesky fp n A p i *
            fl_cholesky fp n A p j) - A i j) ^ 2 / A i i) ≤
      ε ^ 2 * ∑ p ∈ Finset.univ.filter
        (fun p : Fin n => p.val < j.val),
        fl_cholesky fp n A p j ^ 2)
    (hlam2ε : 2 * ε ≤ lam)
    (hthresh : ε + 2 * gamma fp (n + 1) < lam) :
    ∀ j : Fin n, 0 < fl_cholPivot fp n A j := by
  set Δ : Fin n → Fin n → ℝ := fun i l =>
    (∑ p : Fin n, fl_cholesky fp n A p i * fl_cholesky fp n A p l) -
      A i l with hΔ
  have hnzI : ∀ i l : Fin n, A i i = 0 ∨ A l l = 0 → Δ i l = 0 :=
    fun i l h => h.elim
      (fun h0 => absurd h0 (hAdiag i).ne')
      (fun h0 => absurd h0 (hAdiag l).ne')
  have hnzB : ∀ i l : Fin n, A i i = 0 → Δ i l = 0 :=
    fun i l h0 => absurd h0 (hAdiag i).ne'
  refine fl_cholesky_pivots_pos_sharp fp A hAdiag hn1 hγ1 lam ε
    hε0 hε1 hfloor ?_ ?_ hlam2ε hthresh
  · -- interior masses from the single full certificate
    intro j y
    have h := stage_interior_mass_from_full Δ (fun i => A i i)
      (fun i => (hAdiag i).le) ε hcertI hnzI j.val j.isLt.le y
    have hrw : ∀ i l : Fin j.val,
        Δ ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ =
        (∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨l.val, by omega⟩) -
          A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ := by
      intro i l
      show (∑ p : Fin n, _ * _) - _ = _
      rw [gram_sum_stage_trunc fp A j ⟨i.val, by omega⟩
        ⟨l.val, by omega⟩ i.isLt]
    calc |∑ i : Fin j.val, ∑ l : Fin j.val, y i *
          ((∑ p : Fin j.val,
            fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
            fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨l.val, by omega⟩) -
            A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) * y l|
        = |∑ i : Fin j.val, ∑ l : Fin j.val, y i *
            Δ ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l| := by
          congr 1
          exact Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun l _ => by rw [hrw i l]
      _ ≤ ε * ∑ i : Fin j.val,
            A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2 := h
  · -- border masses from the column certificates
    intro j y
    have h := stage_border_mass_from_full Δ (fun i => A i i)
      (fun i => (hAdiag i).le) ε hε0
      (fun w => ∑ p ∈ Finset.univ.filter
        (fun p : Fin n => p.val < w.val),
        fl_cholesky fp n A p w ^ 2)
      (fun w => Finset.sum_nonneg fun p _ => sq_nonneg _)
      hnzB hcertB j y
    have hrwB : ∀ i : Fin j.val,
        Δ ⟨i.val, by omega⟩ j =
        (∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
          fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
          A ⟨i.val, by omega⟩ j := by
      intro i
      show (∑ p : Fin n, _ * _) - _ = _
      rw [gram_sum_stage_trunc fp A j ⟨i.val, by omega⟩ j i.isLt]
    have hrwT : (∑ p ∈ Finset.univ.filter
        (fun p : Fin n => p.val < j.val),
        fl_cholesky fp n A p j ^ 2) =
        ∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2 :=
      (sum_fin_eq_sum_filter_lt' j.isLt.le
        (fun p => fl_cholesky fp n A p j ^ 2)).symm
    calc |2 * ∑ i : Fin j.val, y i *
          ((∑ p : Fin j.val,
            fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
            fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
            A ⟨i.val, by omega⟩ j)|
        = |2 * ∑ i : Fin j.val, y i * Δ ⟨i.val, by omega⟩ j| := by
          congr 2
          exact Finset.sum_congr rfl fun i _ => by rw [hrwB i]
      _ ≤ ε * ((∑ p ∈ Finset.univ.filter
            (fun p : Fin n => p.val < j.val),
            fl_cholesky fp n A p j ^ 2) +
          ∑ i : Fin j.val,
            A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) := h
      _ = ε * ((∑ p : Fin j.val,
            fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2) +
          ∑ i : Fin j.val,
            A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) := by
          rw [hrwT]

/-- Row action of the (10.18) matrix on the leading block. -/
private lemma higham10_18_row_cast (k : ℕ) (α : ℝ) (hk : 0 < k)
    (x : Fin (k + k) → ℝ) (i : Fin k) :
    ∑ j : Fin (k + k), higham10_18_matrix k α (Fin.castAdd k i) j *
      x j =
    α * x (Fin.castAdd k i) + x (Fin.natAdd k i) := by
  rw [Fin.sum_univ_add]
  have h1 : ∑ j : Fin k,
      higham10_18_matrix k α (Fin.castAdd k i) (Fin.castAdd k j) *
        x (Fin.castAdd k j) = α * x (Fin.castAdd k i) := by
    rw [Finset.sum_eq_single i]
    · unfold higham10_18_matrix
      simp [Fin.castAdd, i.isLt]
    · intro b _ hb
      unfold higham10_18_matrix
      have hne : (Fin.castAdd k i).val ≠ (Fin.castAdd k b).val := by
        simp only [Fin.coe_castAdd]
        exact fun h => hb (Fin.ext h.symm)
      have h2 : ¬((Fin.castAdd k i).val + k = (Fin.castAdd k b).val ∨
          (Fin.castAdd k b).val + k = (Fin.castAdd k i).val) := by
        simp only [Fin.coe_castAdd]
        push_neg
        omega
      rw [if_neg hne, if_neg h2, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have h2 : ∑ j : Fin k,
      higham10_18_matrix k α (Fin.castAdd k i) (Fin.natAdd k j) *
        x (Fin.natAdd k j) = x (Fin.natAdd k i) := by
    rw [Finset.sum_eq_single i]
    · unfold higham10_18_matrix
      have hne : (Fin.castAdd k i).val ≠ (Fin.natAdd k i).val := by
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        omega
      have hor : (Fin.castAdd k i).val + k = (Fin.natAdd k i).val ∨
          (Fin.natAdd k i).val + k = (Fin.castAdd k i).val := by
        left
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        omega
      rw [if_neg hne, if_pos hor, one_mul]
    · intro b _ hb
      unfold higham10_18_matrix
      have hne : (Fin.castAdd k i).val ≠ (Fin.natAdd k b).val := by
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        omega
      have h3 : ¬((Fin.castAdd k i).val + k = (Fin.natAdd k b).val ∨
          (Fin.natAdd k b).val + k = (Fin.castAdd k i).val) := by
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        push_neg
        constructor
        · intro h
          exact absurd (Fin.ext (show b.val = i.val by omega)) hb
        · omega
      rw [if_neg hne, if_neg h3, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [h1, h2]

/-- Row action of the (10.18) matrix on the trailing block. -/
private lemma higham10_18_row_nat (k : ℕ) (α : ℝ) (hk : 0 < k)
    (x : Fin (k + k) → ℝ) (i : Fin k) :
    ∑ j : Fin (k + k), higham10_18_matrix k α (Fin.natAdd k i) j *
      x j =
    x (Fin.castAdd k i) + α⁻¹ * x (Fin.natAdd k i) := by
  rw [Fin.sum_univ_add]
  have h1 : ∑ j : Fin k,
      higham10_18_matrix k α (Fin.natAdd k i) (Fin.castAdd k j) *
        x (Fin.castAdd k j) = x (Fin.castAdd k i) := by
    rw [Finset.sum_eq_single i]
    · unfold higham10_18_matrix
      have hne : (Fin.natAdd k i).val ≠ (Fin.castAdd k i).val := by
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        omega
      have hor : (Fin.natAdd k i).val + k = (Fin.castAdd k i).val ∨
          (Fin.castAdd k i).val + k = (Fin.natAdd k i).val := by
        right
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        omega
      rw [if_neg hne, if_pos hor, one_mul]
    · intro b _ hb
      unfold higham10_18_matrix
      have hne : (Fin.natAdd k i).val ≠ (Fin.castAdd k b).val := by
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        omega
      have h3 : ¬((Fin.natAdd k i).val + k = (Fin.castAdd k b).val ∨
          (Fin.castAdd k b).val + k = (Fin.natAdd k i).val) := by
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        push_neg
        constructor
        · omega
        · intro h
          exact absurd (Fin.ext (show b.val = i.val by omega)) hb
      rw [if_neg hne, if_neg h3, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have h2 : ∑ j : Fin k,
      higham10_18_matrix k α (Fin.natAdd k i) (Fin.natAdd k j) *
        x (Fin.natAdd k j) = α⁻¹ * x (Fin.natAdd k i) := by
    rw [Finset.sum_eq_single i]
    · unfold higham10_18_matrix
      have heq : (Fin.natAdd k i).val = (Fin.natAdd k i).val := rfl
      have hge : ¬(Fin.natAdd k i).val < k := by
        simp only [Fin.coe_natAdd]
        omega
      rw [if_pos heq, if_neg hge]
    · intro b _ hb
      unfold higham10_18_matrix
      have hne : (Fin.natAdd k i).val ≠ (Fin.natAdd k b).val := by
        simp only [Fin.coe_natAdd]
        intro h
        exact hb (Fin.ext (by omega)).symm
      have h3 : ¬((Fin.natAdd k i).val + k = (Fin.natAdd k b).val ∨
          (Fin.natAdd k b).val + k = (Fin.natAdd k i).val) := by
        simp only [Fin.coe_natAdd]
        push_neg
        omega
      rw [if_neg hne, if_neg h3, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [h1, h2]

/-- **The (10.18) matrix is positive semidefinite** — completion of
    squares pairwise across the two blocks:
    `xᵀAx = ∑ᵢ (√α·xᵢ + x_{k+i}/√α)²`. -/
theorem higham10_18_isPosSemiDef (k : ℕ) (hk : 0 < k) (α : ℝ)
    (hα : 0 < α) :
    IsPosSemiDef (k + k) (higham10_18_matrix k α) := by
  constructor
  · intro i j
    unfold higham10_18_matrix
    by_cases hij : i.val = j.val
    · rw [if_pos hij, if_pos hij.symm, hij]
    · rw [if_neg hij, if_neg (Ne.symm hij)]
      by_cases hd : i.val + k = j.val ∨ j.val + k = i.val
      · rw [if_pos hd, if_pos (Or.symm hd)]
      · rw [if_neg hd, if_neg (fun h => hd (Or.symm h))]
  · intro x
    have hquad : ∑ i : Fin (k + k), ∑ j : Fin (k + k),
        x i * higham10_18_matrix k α i j * x j =
        ∑ i : Fin k, (α * x (Fin.castAdd k i) ^ 2 +
          2 * x (Fin.castAdd k i) * x (Fin.natAdd k i) +
          α⁻¹ * x (Fin.natAdd k i) ^ 2) := by
      rw [Fin.sum_univ_add]
      have hc : ∀ i : Fin k, ∑ j : Fin (k + k),
          x (Fin.castAdd k i) *
            higham10_18_matrix k α (Fin.castAdd k i) j * x j =
          x (Fin.castAdd k i) * (α * x (Fin.castAdd k i) +
            x (Fin.natAdd k i)) := by
        intro i
        rw [← higham10_18_row_cast k α hk x i, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      have hn : ∀ i : Fin k, ∑ j : Fin (k + k),
          x (Fin.natAdd k i) *
            higham10_18_matrix k α (Fin.natAdd k i) j * x j =
          x (Fin.natAdd k i) * (x (Fin.castAdd k i) +
            α⁻¹ * x (Fin.natAdd k i)) := by
        intro i
        rw [← higham10_18_row_nat k α hk x i, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [Finset.sum_congr rfl fun i _ => hc i,
        Finset.sum_congr rfl fun i _ => hn i,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hquad]
    refine Finset.sum_nonneg fun i _ => ?_
    have hsq := sq_nonneg (Real.sqrt α * x (Fin.castAdd k i) +
      (Real.sqrt α)⁻¹ * x (Fin.natAdd k i))
    have hs : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα.le
    have hs0 : (0:ℝ) < Real.sqrt α := Real.sqrt_pos.mpr hα
    have hsinv : ((Real.sqrt α)⁻¹) ^ 2 = α⁻¹ := by
      rw [inv_pow, hs]
    have hmul : Real.sqrt α * (Real.sqrt α)⁻¹ = 1 :=
      mul_inv_cancel₀ hs0.ne'
    have hexp : (Real.sqrt α * x (Fin.castAdd k i) +
        (Real.sqrt α)⁻¹ * x (Fin.natAdd k i)) ^ 2 =
        α * x (Fin.castAdd k i) ^ 2 +
        2 * x (Fin.castAdd k i) * x (Fin.natAdd k i) +
        α⁻¹ * x (Fin.natAdd k i) ^ 2 := by
      have h0 : (Real.sqrt α * x (Fin.castAdd k i) +
          (Real.sqrt α)⁻¹ * x (Fin.natAdd k i)) ^ 2 =
          Real.sqrt α ^ 2 * x (Fin.castAdd k i) ^ 2 +
          2 * (Real.sqrt α * (Real.sqrt α)⁻¹) *
            (x (Fin.castAdd k i) * x (Fin.natAdd k i)) +
          ((Real.sqrt α)⁻¹) ^ 2 * x (Fin.natAdd k i) ^ 2 := by
        ring
      rw [h0, hs, hsinv, hmul]
      ring
    linarith [hexp ▸ hsq]

/-- **Display (10.18): `‖W‖` is arbitrarily large** (Higham p. 204):
    for the PSD matrix `[[αI, I], [I, α⁻¹I]]` the solve `A₁₁W = A₁₂`
    is `W = α⁻¹I` — verified by the row action — and its action norm
    `α⁻¹` exceeds any bound as `α → 0`: no bound on `‖A₁₁⁻¹A₁₂‖`
    independent of the matrix is possible without pivoting
    structure. -/
theorem higham10_18_w_arbitrarily_large (k : ℕ) (hk : 0 < k)
    (C : ℝ) :
    ∃ α : ℝ, 0 < α ∧
      IsPosSemiDef (k + k) (higham10_18_matrix k α) ∧
      (∀ v : Fin k → ℝ, ∀ i : Fin k,
        ∑ j : Fin k, higham10_18_matrix k α (Fin.castAdd k i)
          (Fin.castAdd k j) * (α⁻¹ * v j) =
        higham10_18_matrix k α (Fin.castAdd k i) (Fin.natAdd k i) *
          v i) ∧
      ∀ v : Fin k → ℝ,
        vecNorm2Sq (fun i => α⁻¹ * v i) =
          (α⁻¹) ^ 2 * vecNorm2Sq v ∧
        C ≤ α⁻¹ := by
  set α : ℝ := min 1 (1 / (|C| + 1)) with hα
  have hα0 : 0 < α := by
    rw [hα]
    have : (0:ℝ) < 1 / (|C| + 1) := by positivity
    exact lt_min one_pos this
  refine ⟨α, hα0, higham10_18_isPosSemiDef k hk α hα0, ?_, ?_⟩
  · intro v i
    -- A₁₁ = αI acting on α⁻¹v recovers v = A₁₂-column action
    have hL : ∑ j : Fin k, higham10_18_matrix k α (Fin.castAdd k i)
        (Fin.castAdd k j) * (α⁻¹ * v j) = v i := by
      rw [Finset.sum_eq_single i]
      · unfold higham10_18_matrix
        simp only [Fin.coe_castAdd, if_true]
        rw [if_pos i.isLt]
        field_simp
      · intro b _ hb
        unfold higham10_18_matrix
        have hne : (Fin.castAdd k i).val ≠ (Fin.castAdd k b).val := by
          simp only [Fin.coe_castAdd]
          exact fun h => hb (Fin.ext h.symm)
        have h3 : ¬((Fin.castAdd k i).val + k =
            (Fin.castAdd k b).val ∨
            (Fin.castAdd k b).val + k = (Fin.castAdd k i).val) := by
          simp only [Fin.coe_castAdd]
          push_neg
          omega
        rw [if_neg hne, if_neg h3, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ i) h
    have hR : higham10_18_matrix k α (Fin.castAdd k i)
        (Fin.natAdd k i) = 1 := by
      unfold higham10_18_matrix
      have hne : (Fin.castAdd k i).val ≠ (Fin.natAdd k i).val := by
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        omega
      have hor : (Fin.castAdd k i).val + k = (Fin.natAdd k i).val ∨
          (Fin.natAdd k i).val + k = (Fin.castAdd k i).val := by
        left
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        omega
      rw [if_neg hne, if_pos hor]
    rw [hL, hR, one_mul]
  · intro v
    constructor
    · unfold vecNorm2Sq
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    · have h1 : α ≤ 1 / (|C| + 1) := by
        rw [hα]
        exact min_le_right _ _
      have h2 : (0:ℝ) < |C| + 1 := by positivity
      have h3 : |C| + 1 ≤ α⁻¹ := by
        rw [← one_div]
        rw [le_div_iff₀ hα0]
        calc (|C| + 1) * α ≤ (|C| + 1) * (1 / (|C| + 1)) :=
              mul_le_mul_of_nonneg_left h1 h2.le
          _ = 1 := by field_simp
      calc C ≤ |C| := le_abs_self C
        _ ≤ α⁻¹ := by linarith

/-- **Display (10.21) stage interior mass** (Higham p. 206): under the
    running induction hypothesis, the stage-`j` interior Gram defect
    carries the quadratic-form mass `r·γ_{r+1}/(1−γ_{r+1})` against the
    `A`-diagonal weights, for every stage `j < r` — the Theorem 10.3
    block certificate, the Demmel scaled entrywise bound, and the
    ones-vector Cauchy–Schwarz engine, composed. -/
theorem higham10_21_stage_interior_mass (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1)
    (r : ℕ) (hrn : r ≤ n)
    (j : Fin n) (hjr : j.val < r)
    (IH : ∀ l : Fin n, l.val < j.val → 0 < fl_cholPivot fp n A l)
    (y : Fin j.val → ℝ) :
    |∑ i : Fin j.val, ∑ l : Fin j.val, y i *
      ((∑ p : Fin j.val,
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨l.val, by omega⟩) -
        A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) * y l| ≤
      (r : ℝ) * (gamma fp (r + 1) / (1 - gamma fp (r + 1))) *
      ∑ i : Fin j.val,
        A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2 := by
  -- gamma bookkeeping
  have hrvalid : gammaValid fp (r + 1) :=
    gammaValid_mono fp (by omega) hn1
  have hG0 : 0 ≤ gamma fp (r + 1) := gamma_nonneg fp hrvalid
  have hG1 : gamma fp (r + 1) < 1 :=
    lt_of_le_of_lt (gamma_mono fp (by omega) hn1) hγ1
  have hD : (0:ℝ) < 1 - gamma fp (r + 1) := by linarith
  have hm1valid : gammaValid fp (j.val + 1) :=
    gammaValid_mono fp (by omega) hn1
  have hγm0 : 0 ≤ gamma fp (j.val + 1) := gamma_nonneg fp hm1valid
  have hγmG : gamma fp (j.val + 1) ≤ gamma fp (r + 1) :=
    gamma_mono fp (by omega) hrvalid
  have hγm1 : gamma fp (j.val + 1) < 1 := lt_of_le_of_lt hγmG hG1
  have h1γm : (0:ℝ) < 1 - gamma fp (j.val + 1) := by linarith
  have hu : fp.u < 1 := by
    have h := hn1
    unfold gammaValid at h
    push_cast at h
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ)) fp.u_nonneg]
  -- the stage-j Theorem 10.3 block certificate from the running IH
  set Am : Fin j.val → Fin j.val → ℝ :=
    fun i' l' => A ⟨i'.val, by omega⟩ ⟨l'.val, by omega⟩ with hAm
  have hcert : CholeskyBackwardError j.val Am
      (fl_cholesky fp j.val Am) (gamma fp (j.val + 1)) :=
    fl_cholesky_block_certificate fp j.isLt.le A hsym hu hm1valid IH
  have hloc : ∀ p q : Fin j.val,
      fl_cholesky fp j.val Am p q =
      fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨q.val, by omega⟩ :=
    fun p q => fl_cholesky_leading_principal fp j.isLt.le A p q
  -- Demmel scaled entrywise bound for the stage block, full-run form
  have hentry : ∀ i l : Fin j.val,
      |(∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨l.val, by omega⟩) -
        A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩| ≤
      gamma fp (j.val + 1) / (1 - gamma fp (j.val + 1)) *
        (Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) *
         Real.sqrt (A ⟨l.val, by omega⟩ ⟨l.val, by omega⟩)) := by
    intro i l
    have h := chol_cert_scaled_entrywise_le j.val Am
      (fl_cholesky fp j.val Am) (gamma fp (j.val + 1)) hγm0 hγm1 hcert
      (fun l' => (hAdiag _).le) i l
    simp only [hloc] at h
    exact h
  -- entrywise bound on the scaled defect, then the quadratic-form engine
  have hc0 : 0 ≤ gamma fp (j.val + 1) / (1 - gamma fp (j.val + 1)) :=
    div_nonneg hγm0 h1γm.le
  have hE : ∀ i l : Fin j.val,
      |((∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨l.val, by omega⟩) -
          A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) /
        (Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) *
         Real.sqrt (A ⟨l.val, by omega⟩ ⟨l.val, by omega⟩))| ≤
      gamma fp (j.val + 1) / (1 - gamma fp (j.val + 1)) := by
    intro i l
    have hsi := Real.sqrt_pos.mpr (hAdiag (⟨i.val, by omega⟩ : Fin n))
    have hsl := Real.sqrt_pos.mpr (hAdiag (⟨l.val, by omega⟩ : Fin n))
    rw [abs_div, abs_of_pos (mul_pos hsi hsl),
      div_le_iff₀ (mul_pos hsi hsl)]
    exact hentry i l
  have hquad := quadForm_cert_of_entrywise
    (fun i l : Fin j.val =>
      ((∑ p : Fin j.val,
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨l.val, by omega⟩) -
        A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) /
      (Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) *
       Real.sqrt (A ⟨l.val, by omega⟩ ⟨l.val, by omega⟩)))
    (gamma fp (j.val + 1) / (1 - gamma fp (j.val + 1))) hc0 hE
  have hmass := scaled_interior_mass_normwise_quad
    (fun i l : Fin j.val =>
      (∑ p : Fin j.val,
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨l.val, by omega⟩) -
        A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩)
    (fun i : Fin j.val => A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩)
    (fun i => (hAdiag _).le)
    (gamma fp (j.val + 1) / (1 - gamma fp (j.val + 1)) * (j.val : ℝ))
    hquad y
    (fun i l h => h.elim
      (fun h0 => absurd h0 (hAdiag _).ne')
      (fun h0 => absurd h0 (hAdiag _).ne'))
  -- lift the stage constant to the display's r-shaped constant
  have hle : gamma fp (j.val + 1) / (1 - gamma fp (j.val + 1)) *
      (j.val : ℝ) ≤
      (r : ℝ) * (gamma fp (r + 1) / (1 - gamma fp (r + 1))) := by
    have hcG : gamma fp (j.val + 1) / (1 - gamma fp (j.val + 1)) ≤
        gamma fp (r + 1) / (1 - gamma fp (r + 1)) :=
      div_le_div₀ hG0 hγmG hD (by linarith)
    have hmr : (j.val : ℝ) ≤ (r : ℝ) := by exact_mod_cast hjr.le
    exact (mul_le_mul hcG hmr (Nat.cast_nonneg _)
      (div_nonneg hG0 hD.le)).trans_eq (mul_comm _ _)
  have hW0 : 0 ≤ ∑ i : Fin j.val,
      A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2 :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (hAdiag _).le (sq_nonneg _)
  exact hmass.trans (mul_le_mul_of_nonneg_right hle hW0)

/-- **Display (10.21) stage border mass** (Higham p. 206): under the
    running induction hypothesis, the stage-`j` border-column Gram
    defect carries the scaled mass `r·γ_{r+1}/(1−γ_{r+1})` against the
    computed-column norm and the `A`-diagonal weights — the truncated
    border bound applied to the `(j+1)`-leading block (constant
    `γ_{j+2} ≤ γ_{r+1}`) plus the certificate column-norm control. -/
theorem higham10_21_stage_border_mass (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1)
    (r : ℕ) (hrn : r ≤ n)
    (j : Fin n) (hjr : j.val < r)
    (IH : ∀ l : Fin n, l.val < j.val → 0 < fl_cholPivot fp n A l)
    (y : Fin j.val → ℝ) :
    |2 * ∑ i : Fin j.val, y i *
      ((∑ p : Fin j.val,
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
        fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
        A ⟨i.val, by omega⟩ j)| ≤
      (r : ℝ) * (gamma fp (r + 1) / (1 - gamma fp (r + 1))) *
      ((∑ p : Fin j.val, fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2) +
       ∑ i : Fin j.val,
         A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) := by
  -- gamma bookkeeping
  have hrvalid : gammaValid fp (r + 1) :=
    gammaValid_mono fp (by omega) hn1
  have hG0 : 0 ≤ gamma fp (r + 1) := gamma_nonneg fp hrvalid
  have hG1 : gamma fp (r + 1) < 1 :=
    lt_of_le_of_lt (gamma_mono fp (by omega) hn1) hγ1
  have hD : (0:ℝ) < 1 - gamma fp (r + 1) := by linarith
  have hm1valid : gammaValid fp (j.val + 1) :=
    gammaValid_mono fp (by omega) hn1
  have hγmG : gamma fp (j.val + 1) ≤ gamma fp (r + 1) :=
    gamma_mono fp (by omega) hrvalid
  have hγm1 : gamma fp (j.val + 1) < 1 := lt_of_le_of_lt hγmG hG1
  have h1γm : (0:ℝ) < 1 - gamma fp (j.val + 1) := by linarith
  have hγ2valid : gammaValid fp (j.val + 2) :=
    gammaValid_mono fp (by omega) hn1
  have hγ20 : 0 ≤ gamma fp (j.val + 2) := gamma_nonneg fp hγ2valid
  have hγ2G : gamma fp (j.val + 2) ≤ gamma fp (r + 1) :=
    gamma_mono fp (by omega) hrvalid
  have hu : fp.u < 1 := by
    have h := hn1
    unfold gammaValid at h
    push_cast at h
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ)) fp.u_nonneg]
  -- stage diagonals are nonzero from the IH
  have hdiag_ne : ∀ i : Fin j.val,
      fl_cholesky fp n A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ ≠ 0 := by
    intro i
    rw [fl_cholesky_diag_eq fp n A ⟨i.val, by omega⟩]
    exact (fl_sqrt_pos fp hu _ (IH ⟨i.val, by omega⟩ i.isLt)).ne'
  -- border entry bound at the (j+1)-leading block: constant γ_{j+2}
  set Am1 : Fin (j.val + 1) → Fin (j.val + 1) → ℝ :=
    fun i' l' => A ⟨i'.val, by omega⟩ ⟨l'.val, by omega⟩ with hAm1
  have hloc1 : ∀ p q : Fin (j.val + 1),
      fl_cholesky fp (j.val + 1) Am1 p q =
      fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨q.val, by omega⟩ :=
    fun p q => fl_cholesky_leading_principal fp
      (by omega : j.val + 1 ≤ n) A p q
  have hbord : ∀ i : Fin j.val,
      |(∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
          fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
        A ⟨i.val, by omega⟩ j| ≤
      gamma fp (j.val + 2) *
        (Real.sqrt (∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ ^ 2) *
         Real.sqrt (∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2)) := by
    intro i
    have hdz : fl_cholesky fp (j.val + 1) Am1
        ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ ≠ 0 := by
      rw [hloc1 ⟨i.val, by omega⟩ ⟨i.val, by omega⟩]
      exact hdiag_ne i
    have hb := fl_cholesky_border_bound fp (n := j.val + 1) Am1
      (gammaValid_mono fp (by omega) hn1) (Fin.last j.val) i hdz
    simp only [hloc1] at hb
    exact hb
  -- certificate column-norm control from the stage-j block certificate
  set Am : Fin j.val → Fin j.val → ℝ :=
    fun i' l' => A ⟨i'.val, by omega⟩ ⟨l'.val, by omega⟩ with hAm
  have hcert : CholeskyBackwardError j.val Am
      (fl_cholesky fp j.val Am) (gamma fp (j.val + 1)) :=
    fl_cholesky_block_certificate fp j.isLt.le A hsym hu hm1valid IH
  have hloc : ∀ p q : Fin j.val,
      fl_cholesky fp j.val Am p q =
      fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨q.val, by omega⟩ :=
    fun p q => fl_cholesky_leading_principal fp j.isLt.le A p q
  have hcol : ∀ i : Fin j.val,
      (1 - gamma fp (j.val + 1)) *
        ∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ ^ 2 ≤
      A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ := by
    intro i
    have h := chol_cert_colNormSq_le j.val Am (fl_cholesky fp j.val Am)
      (gamma fp (j.val + 1)) hcert i
    simp only [hloc] at h
    exact h
  have hT0 : 0 ≤ ∑ p : Fin j.val,
      fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2 :=
    Finset.sum_nonneg fun p _ => sq_nonneg _
  -- per-column scaled certificate at the display's r-shaped constant
  have hcertB : ∑ i : Fin j.val,
      (if A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ = 0 then 0 else
        ((∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
          fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
          A ⟨i.val, by omega⟩ j) ^ 2 /
        A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) ≤
      ((r : ℝ) * (gamma fp (r + 1) / (1 - gamma fp (r + 1)))) ^ 2 *
      ∑ p : Fin j.val, fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2 := by
    have hstep : ∀ i : Fin j.val,
        (if A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ = 0 then 0 else
          ((∑ p : Fin j.val,
            fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
            fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
            A ⟨i.val, by omega⟩ j) ^ 2 /
          A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) ≤
        gamma fp (j.val + 2) ^ 2 *
          (∑ p : Fin j.val, fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2) /
          (1 - gamma fp (j.val + 1)) := by
      intro i
      rw [if_neg (hAdiag _).ne']
      have hDsq0 : (0:ℝ) ≤ ∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ ^ 2 :=
        Finset.sum_nonneg fun p _ => sq_nonneg _
      have hδsq : ((∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
          fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
          A ⟨i.val, by omega⟩ j) ^ 2 ≤
          gamma fp (j.val + 2) ^ 2 *
          (∑ p : Fin j.val,
            fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ ^ 2) *
          ∑ p : Fin j.val,
            fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2 := by
        have h := mul_self_le_mul_self (abs_nonneg _) (hbord i)
        rw [abs_mul_abs_self] at h
        have hexp : (gamma fp (j.val + 2) *
            (Real.sqrt (∑ p : Fin j.val,
              fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ ^ 2) *
             Real.sqrt (∑ p : Fin j.val,
              fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2))) *
            (gamma fp (j.val + 2) *
            (Real.sqrt (∑ p : Fin j.val,
              fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ ^ 2) *
             Real.sqrt (∑ p : Fin j.val,
              fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2))) =
            gamma fp (j.val + 2) ^ 2 *
            (∑ p : Fin j.val,
              fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ ^ 2) *
            ∑ p : Fin j.val,
              fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2 := by
          rw [show ∀ g a b : ℝ, g * (a * b) * (g * (a * b)) =
              g ^ 2 * (a * a) * (b * b) from fun g a b => by ring,
            Real.mul_self_sqrt hDsq0, Real.mul_self_sqrt hT0]
        rw [hexp] at h
        rw [pow_two]
        exact h
      rw [div_le_div_iff₀ (hAdiag _) h1γm]
      have h1 := mul_le_mul_of_nonneg_right hδsq h1γm.le
      have h2 := mul_le_mul_of_nonneg_left (hcol i)
        (mul_nonneg (sq_nonneg (gamma fp (j.val + 2))) hT0)
      nlinarith [h1, h2]
    calc ∑ i : Fin j.val,
        (if A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ = 0 then 0 else
          ((∑ p : Fin j.val,
            fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
            fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
            A ⟨i.val, by omega⟩ j) ^ 2 /
          A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩)
        ≤ ∑ _i : Fin j.val,
            gamma fp (j.val + 2) ^ 2 *
            (∑ p : Fin j.val,
              fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2) /
            (1 - gamma fp (j.val + 1)) :=
          Finset.sum_le_sum fun i _ => hstep i
      _ = (j.val : ℝ) * (gamma fp (j.val + 2) ^ 2 *
            (∑ p : Fin j.val,
              fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2) /
            (1 - gamma fp (j.val + 1))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
      _ ≤ ((r : ℝ) * (gamma fp (r + 1) / (1 - gamma fp (r + 1)))) ^ 2 *
            ∑ p : Fin j.val,
              fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2 := by
          have hγ2sq : gamma fp (j.val + 2) ^ 2 ≤
              gamma fp (r + 1) ^ 2 := by nlinarith [hγ2G, hγ20]
          have hDsqle : (1 - gamma fp (r + 1)) ^ 2 ≤
              1 - gamma fp (j.val + 1) := by
            nlinarith [hD, hγmG, hG0, hG1]
          have hfrac : gamma fp (j.val + 2) ^ 2 /
              (1 - gamma fp (j.val + 1)) ≤
              gamma fp (r + 1) ^ 2 / (1 - gamma fp (r + 1)) ^ 2 :=
            div_le_div₀ (sq_nonneg _) hγ2sq (by positivity) hDsqle
          have hmr2 : (j.val : ℝ) ≤ (r : ℝ) ^ 2 := by
            have h1 : (j.val : ℝ) ≤ (r : ℝ) := by exact_mod_cast hjr.le
            have h2 : (1 : ℝ) ≤ (r : ℝ) := by
              have : 1 ≤ r := by omega
              exact_mod_cast this
            nlinarith
          calc (j.val : ℝ) * (gamma fp (j.val + 2) ^ 2 *
                (∑ p : Fin j.val,
                  fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2) /
                (1 - gamma fp (j.val + 1)))
              = ((j.val : ℝ) * (gamma fp (j.val + 2) ^ 2 /
                  (1 - gamma fp (j.val + 1)))) *
                ∑ p : Fin j.val,
                  fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2 := by
                ring
            _ ≤ ((r : ℝ) ^ 2 * (gamma fp (r + 1) ^ 2 /
                  (1 - gamma fp (r + 1)) ^ 2)) *
                ∑ p : Fin j.val,
                  fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2 := by
                refine mul_le_mul_of_nonneg_right ?_ hT0
                exact mul_le_mul hmr2 hfrac
                  (div_nonneg (sq_nonneg _) h1γm.le) (sq_nonneg _)
            _ = ((r : ℝ) * (gamma fp (r + 1) /
                  (1 - gamma fp (r + 1)))) ^ 2 *
                ∑ p : Fin j.val,
                  fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2 := by
                rw [mul_pow, div_pow]
  -- Cauchy–Schwarz + AM–GM assembly
  exact scaled_border_mass_normwise
    (fun i : Fin j.val =>
      (∑ p : Fin j.val,
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
        fl_cholesky fp n A ⟨p.val, by omega⟩ j) - A ⟨i.val, by omega⟩ j)
    (fun i : Fin j.val => A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩)
    (fun i => (hAdiag _).le)
    ((r : ℝ) * (gamma fp (r + 1) / (1 - gamma fp (r + 1))))
    (∑ p : Fin j.val, fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2)
    (mul_nonneg (Nat.cast_nonneg _) (div_nonneg hG0 hD.le)) hT0
    (fun i h0 => absurd h0 (hAdiag _).ne')
    hcertB y

/-- **Display (10.21), self-feeding leading-pivot positivity** (Higham
    §10.3.2, p. 206): with a bordered Rayleigh floor `lam` on the scaled
    leading blocks, every rounded pivot of stages `j < r` of the
    concrete Algorithm 10.2 run is positive at the source-shaped
    threshold `lam > r·γ_{r+1}/(1−γ_{r+1}) + 2γ_{n+1}` — no assumed
    run-level certificates: the stage masses are derived from the
    running induction hypothesis itself.  The `+2γ_{n+1}` additive is
    the recorded honest delta against the source's bare display. -/
theorem higham10_21_fl_cholesky_leading_pivots_pos (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1)
    (r : ℕ) (hrn : r ≤ n) (lam : ℝ)
    (hfloor : ∀ j : Fin n, j.val < r → ∀ y : Fin j.val → ℝ,
      lam * ((∑ i : Fin j.val,
          A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) + A j j) ≤
        (∑ i : Fin j.val, ∑ l : Fin j.val,
          y i * A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l) +
        2 * (∑ i : Fin j.val, y i * A ⟨i.val, by omega⟩ j) + A j j)
    (hlam2ε : 2 * ((r : ℝ) *
      (gamma fp (r + 1) / (1 - gamma fp (r + 1)))) ≤ lam)
    (hthresh : (r : ℝ) * (gamma fp (r + 1) / (1 - gamma fp (r + 1))) +
      2 * gamma fp (n + 1) < lam) :
    ∀ j : Fin n, j.val < r → 0 < fl_cholPivot fp n A j := by
  have hrvalid : gammaValid fp (r + 1) :=
    gammaValid_mono fp (by omega) hn1
  have hG0 : 0 ≤ gamma fp (r + 1) := gamma_nonneg fp hrvalid
  have hG1 : gamma fp (r + 1) < 1 :=
    lt_of_le_of_lt (gamma_mono fp (by omega) hn1) hγ1
  have hε0 : 0 ≤ (r : ℝ) *
      (gamma fp (r + 1) / (1 - gamma fp (r + 1))) :=
    mul_nonneg (Nat.cast_nonneg _) (div_nonneg hG0 (by linarith))
  have H : ∀ k : ℕ, ∀ j : Fin n, j.val = k → j.val < r →
      0 < fl_cholPivot fp n A j := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k IHk =>
      intro j hj hjr
      have IH : ∀ l : Fin n, l.val < j.val → 0 < fl_cholPivot fp n A l :=
        fun l hl => IHk l.val (hj ▸ hl) l rfl (by omega)
      -- λ ≤ 1 from the floor at y = 0, so ε ≤ 1/2 < 1
      have hlam1 : lam ≤ 1 := by
        have h0 := hfloor j hjr (fun _ => (0 : ℝ))
        norm_num at h0
        exact le_of_mul_le_mul_right
          (by linarith : lam * A j j ≤ 1 * A j j) (hAdiag j)
      have hε1 : (r : ℝ) *
          (gamma fp (r + 1) / (1 - gamma fp (r + 1))) < 1 := by
        linarith
      exact fl_cholesky_pivot_pos_step_sharp fp A hAdiag hn1 hγ1 j IH lam
        ((r : ℝ) * (gamma fp (r + 1) / (1 - gamma fp (r + 1)))) hε0 hε1
        (hfloor j hjr)
        (fun y => higham10_21_stage_interior_mass fp A hsym hAdiag hn1 hγ1
          r hrn j hjr IH y)
        (fun y => higham10_21_stage_border_mass fp A hsym hAdiag hn1 hγ1
          r hrn j hjr IH y)
        hlam2ε hthresh
  exact fun j hjr => H j.val j rfl hjr

/-- **Bordered Rayleigh floor from `λ_min` of the scaled matrix** (the
    per-stage floor derivation of the Theorem 10.7 success proofs,
    factored): interlacing on the bordered leading blocks and the
    substitution `z = (√b_ii·y_i, √b_kk)` convert `λ_min(H)` of the
    scaled matrix `H = D⁻¹BD⁻¹` into the bordered quadratic floor used
    by the pivot-positivity inductions. -/
theorem min_eig_scaled_bordered_floor (N : ℕ) (hN0 : 0 < N)
    (B : Fin N → Fin N → ℝ)
    (hsymB : ∀ i l : Fin N, B i l = B l i)
    (hBdiag : ∀ i : Fin N, 0 < B i i)
    (hH_sym : IsSymmetricFiniteMatrix (fun i l : Fin N =>
      B i l / (Real.sqrt (B i i) * Real.sqrt (B l l))))
    (k : Fin N) (y : Fin k.val → ℝ) :
    finiteMinEigenvalue hN0 (fun i l : Fin N =>
        B i l / (Real.sqrt (B i i) * Real.sqrt (B l l))) hH_sym *
      ((∑ i : Fin k.val,
        B ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) + B k k) ≤
      (∑ i : Fin k.val, ∑ l : Fin k.val,
        y i * B ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l) +
      2 * (∑ i : Fin k.val, y i * B ⟨i.val, by omega⟩ k) + B k k := by
  have hm1n : k.val + 1 ≤ N := k.isLt
  have hHb_sym : IsSymmetricFiniteMatrix (fun i l : Fin (k.val + 1) =>
      (fun i l : Fin N => B i l / (Real.sqrt (B i i) * Real.sqrt (B l l)))
        ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) :=
    fun i l => hH_sym _ _
  have hinterlace := finiteMinEigenvalue_leading_principal_ge N hN0 _
    hH_sym (k.val + 1) (Nat.succ_pos k.val) hm1n hHb_sym
  set z : Fin (k.val + 1) → ℝ := Fin.snoc
    (fun i : Fin k.val =>
      Real.sqrt (B ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) * y i)
    (Real.sqrt (B k k)) with hz
  have hray := finiteMinEigenvalue_rayleigh (Nat.succ_pos k.val)
    (fun i l : Fin (k.val + 1) =>
      (fun i l : Fin N => B i l / (Real.sqrt (B i i) * Real.sqrt (B l l)))
        ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) hHb_sym z
  have hlast_eq : (⟨(Fin.last k.val).val, by omega⟩ : Fin N) = k :=
    Fin.ext (by simp)
  have hcancel : ∀ (i l : Fin N) (u v : ℝ),
      (Real.sqrt (B i i) * u) *
        (B i l / (Real.sqrt (B i i) * Real.sqrt (B l l))) *
        (Real.sqrt (B l l) * v) = u * B i l * v := by
    intro i l u v
    have hi := (Real.sqrt_pos.mpr (hBdiag i)).ne'
    have hl := (Real.sqrt_pos.mpr (hBdiag l)).ne'
    field_simp
  have hnorm : ∑ i : Fin (k.val + 1), z i ^ 2 =
      (∑ i : Fin k.val,
        B ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) + B k k := by
    rw [Fin.sum_univ_castSucc]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      rw [hz, Fin.snoc_castSucc, mul_pow, Real.sq_sqrt (hBdiag _).le]
    · rw [hz, Fin.snoc_last, Real.sq_sqrt (hBdiag k).le]
  have hz_nonneg_sq : 0 ≤ ∑ i : Fin (k.val + 1), z i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hquad : ∑ i : Fin (k.val + 1), ∑ l : Fin (k.val + 1),
      z i * ((fun i l : Fin N =>
        B i l / (Real.sqrt (B i i) * Real.sqrt (B l l)))
        ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) * z l =
      (∑ i : Fin k.val, ∑ l : Fin k.val,
        y i * B ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l) +
      2 * (∑ i : Fin k.val, y i * B ⟨i.val, by omega⟩ k) + B k k := by
    rw [sum_sum_castSucc_split k.val]
    have hp1 : ∑ i : Fin k.val, ∑ l : Fin k.val,
        z i.castSucc * ((fun i l : Fin N =>
          B i l / (Real.sqrt (B i i) * Real.sqrt (B l l)))
          ⟨(i.castSucc).val, by omega⟩ ⟨(l.castSucc).val, by omega⟩) *
          z l.castSucc =
        ∑ i : Fin k.val, ∑ l : Fin k.val,
          y i * B ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro l _
      rw [hz, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact hcancel _ _ (y i) (y l)
    have hp2 : ∑ i : Fin k.val,
        z i.castSucc * ((fun i l : Fin N =>
          B i l / (Real.sqrt (B i i) * Real.sqrt (B l l)))
          ⟨(i.castSucc).val, by omega⟩
          ⟨(Fin.last k.val).val, by omega⟩) * z (Fin.last k.val) =
        ∑ i : Fin k.val, y i * B ⟨i.val, by omega⟩ k := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hz, Fin.snoc_castSucc, Fin.snoc_last, hlast_eq]
      have hthis := hcancel ⟨i.val, by omega⟩ k (y i) 1
      simp only [mul_one] at hthis
      exact hthis
    have hp3 : ∑ l : Fin k.val,
        z (Fin.last k.val) * ((fun i l : Fin N =>
          B i l / (Real.sqrt (B i i) * Real.sqrt (B l l)))
          ⟨(Fin.last k.val).val, by omega⟩
          ⟨(l.castSucc).val, by omega⟩) * z l.castSucc =
        ∑ l : Fin k.val, y l * B ⟨l.val, by omega⟩ k := by
      apply Finset.sum_congr rfl
      intro l _
      rw [hz, Fin.snoc_castSucc, Fin.snoc_last, hlast_eq]
      have hthis := hcancel k ⟨l.val, by omega⟩ 1 (y l)
      simp only [one_mul, mul_one] at hthis
      have hfin : Real.sqrt (B k k) *
          (B k ⟨l.val, by omega⟩ /
            (Real.sqrt (B k k) *
             Real.sqrt (B ⟨l.val, by omega⟩ ⟨l.val, by omega⟩))) *
          (Real.sqrt (B ⟨l.val, by omega⟩ ⟨l.val, by omega⟩) * y l) =
          y l * B ⟨l.val, by omega⟩ k := by
        rw [hthis, hsymB k ⟨l.val, by omega⟩]
        ring
      exact hfin
    have hp4 : z (Fin.last k.val) * ((fun i l : Fin N =>
        B i l / (Real.sqrt (B i i) * Real.sqrt (B l l)))
        ⟨(Fin.last k.val).val, by omega⟩
        ⟨(Fin.last k.val).val, by omega⟩) * z (Fin.last k.val) =
        B k k := by
      rw [hz, Fin.snoc_last, hlast_eq]
      have hthis := hcancel k k 1 1
      simp only [one_mul, mul_one] at hthis
      exact hthis
    rw [hp1, hp2, hp3, hp4]
    ring
  have hmono : finiteMinEigenvalue hN0 _ hH_sym *
      ∑ i : Fin (k.val + 1), z i ^ 2 ≤
      finiteMinEigenvalue (Nat.succ_pos k.val) _ hHb_sym *
      ∑ i : Fin (k.val + 1), z i ^ 2 :=
    mul_le_mul_of_nonneg_right hinterlace hz_nonneg_sq
  calc finiteMinEigenvalue hN0 _ hH_sym *
      ((∑ i : Fin k.val,
        B ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) + B k k)
      = finiteMinEigenvalue hN0 _ hH_sym *
        ∑ i : Fin (k.val + 1), z i ^ 2 := by rw [hnorm]
    _ ≤ finiteMinEigenvalue (Nat.succ_pos k.val) _ hHb_sym *
        ∑ i : Fin (k.val + 1), z i ^ 2 := hmono
    _ ≤ ∑ i : Fin (k.val + 1), ∑ l : Fin (k.val + 1),
        z i * ((fun i l : Fin N =>
          B i l / (Real.sqrt (B i i) * Real.sqrt (B l l)))
          ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) * z l := hray
    _ = (∑ i : Fin k.val, ∑ l : Fin k.val,
          y i * B ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l) +
        2 * (∑ i : Fin k.val, y i * B ⟨i.val, by omega⟩ k) + B k k := hquad

/-- **Display (10.21), source-facing `λ_min(H₁₁)` form** (Higham
    §10.3.2, p. 206, the hypothesis of Theorem 10.14): if the minimum
    eigenvalue of the scaled leading `r × r` block
    `H₁₁ = D₁⁻¹A₁₁D₁⁻¹` exceeds
    `r·γ_{r+1}/(1−γ_{r+1}) + 2γ_{n+1}` (and dominates twice the mass
    constant), the concrete Algorithm 10.2 run completes its first `r`
    stages: every rounded pivot below stage `r` is positive.  No
    run-level certificate is assumed; the `+2γ_{n+1}` additive is the
    recorded honest delta against the source's bare display. -/
theorem higham10_21_fl_cholesky_success (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1)
    (r : ℕ) (hr0 : 0 < r) (hrn : r ≤ n)
    (hH_sym : IsSymmetricFiniteMatrix (fun i l : Fin r =>
      A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ /
        (Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) *
         Real.sqrt (A ⟨l.val, by omega⟩ ⟨l.val, by omega⟩))))
    (hlam2ε : 2 * ((r : ℝ) *
        (gamma fp (r + 1) / (1 - gamma fp (r + 1)))) ≤
      finiteMinEigenvalue hr0 (fun i l : Fin r =>
        A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ /
          (Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) *
           Real.sqrt (A ⟨l.val, by omega⟩ ⟨l.val, by omega⟩))) hH_sym)
    (hthresh : (r : ℝ) * (gamma fp (r + 1) / (1 - gamma fp (r + 1))) +
        2 * gamma fp (n + 1) <
      finiteMinEigenvalue hr0 (fun i l : Fin r =>
        A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ /
          (Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) *
           Real.sqrt (A ⟨l.val, by omega⟩ ⟨l.val, by omega⟩))) hH_sym) :
    ∀ j : Fin n, j.val < r → 0 < fl_cholPivot fp n A j := by
  refine higham10_21_fl_cholesky_leading_pivots_pos fp A hsym hAdiag hn1 hγ1
    r hrn _ ?_ hlam2ε hthresh
  intro j hjr y
  exact min_eig_scaled_bordered_floor r hr0
    (fun p q : Fin r => A ⟨p.val, by omega⟩ ⟨q.val, by omega⟩)
    (fun p q => hsym _ _) (fun p => hAdiag _) hH_sym ⟨j.val, hjr⟩ y

/-- **Theorem 10.7 success direction at the source-shaped threshold,
    hypothesis-light** (Higham §10.1, p. 200): the `r = n` instance of
    the display-(10.21) assembly — if
    `λ_min(H) > n·γ_{n+1}/(1−γ_{n+1}) + 2γ_{n+1}` for the scaled matrix
    `H = D⁻¹AD⁻¹` (and `λ_min(H)` dominates twice the mass constant),
    the concrete Algorithm 10.2 run completes: every rounded pivot is
    positive.  This replaces the coarser `(2n+3)`-constant of
    `higham10_7_fl_cholesky_success` and assumes no run-level
    certificates, unlike `fl_cholesky_pivots_pos_sharp_certified`. -/
theorem higham10_7_fl_cholesky_success_sharp (fp : FPModel) (n : ℕ)
    (hn0 : 0 < n) (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1)
    (hH_sym : IsSymmetricFiniteMatrix (fun i l : Fin n =>
      A i l / (Real.sqrt (A i i) * Real.sqrt (A l l))))
    (hlam2ε : 2 * ((n : ℝ) *
        (gamma fp (n + 1) / (1 - gamma fp (n + 1)))) ≤
      finiteMinEigenvalue hn0 (fun i l : Fin n =>
        A i l / (Real.sqrt (A i i) * Real.sqrt (A l l))) hH_sym)
    (hthresh : (n : ℝ) * (gamma fp (n + 1) / (1 - gamma fp (n + 1))) +
        2 * gamma fp (n + 1) <
      finiteMinEigenvalue hn0 (fun i l : Fin n =>
        A i l / (Real.sqrt (A i i) * Real.sqrt (A l l))) hH_sym) :
    ∀ j : Fin n, 0 < fl_cholPivot fp n A j := by
  intro j
  exact higham10_21_fl_cholesky_success fp A hsym hAdiag hn1 hγ1
    n hn0 le_rfl hH_sym hlam2ε hthresh j j.isLt

/-- Geometric telescope: `∑_{i∈[k,k+m)} c²s^{2i} = s^{2k} − s^{2(k+m)}`
    under `c² + s² = 1`. -/
private lemma kahan_telescope (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    (k m : ℕ) :
    ∑ i ∈ Finset.range m, c ^ 2 * s ^ (2 * (k + i)) =
      s ^ (2 * k) - s ^ (2 * (k + m)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : c ^ 2 = 1 - s ^ 2 := by linarith
    have h2 : s ^ (2 * (k + (m + 1))) =
        s ^ (2 * (k + m)) * s ^ 2 := by
      rw [show 2 * (k + (m + 1)) = 2 * (k + m) + 2 by ring, pow_add]
    rw [h1, h2]
    ring

/-- **The Kahan factor satisfies the (10.13) column-tail relation with
    equality on the square part** (Higham p. 205, "R satisfies the
    inequalities (10.13) (as equalities)"): for `k ≤ j < r`,
    `∑_{i≥k} R(θ)_{ij}² = R(θ)_{kk}²`. -/
theorem kahanR_tail_eq (r n : ℕ) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) (hrn : r ≤ n)
    (k : Fin r) (j : Fin n) (hkj : k.val ≤ j.val) (hjr : j.val < r) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin r => k.val ≤ i.val),
      kahanR r n c s i j ^ 2 =
    kahanR r n c s k ⟨k.val, by omega⟩ ^ 2 := by
  -- diagonal value
  have hdiag : kahanR r n c s k ⟨k.val, by omega⟩ = s ^ k.val := by
    unfold kahanR
    rw [if_pos rfl]
  rw [hdiag]
  -- entries in the tail: [k, j) give c²s^{2i}, i = j gives s^{2j}, rest 0
  have hval : ∀ i : Fin r, k.val ≤ i.val →
      kahanR r n c s i j ^ 2 =
      if i.val < j.val then c ^ 2 * s ^ (2 * i.val)
      else if i.val = j.val then s ^ (2 * j.val) else 0 := by
    intro i hki
    unfold kahanR
    by_cases hij : j.val = i.val
    · rw [if_pos hij, if_neg (by omega), if_pos hij.symm, ← pow_mul]
      congr 1
      omega
    · rw [if_neg hij]
      by_cases hlt : i.val < j.val
      · rw [if_pos hlt, if_pos hlt]
        rw [mul_pow, neg_pow, ← pow_mul]
        ring_nf
      · rw [if_neg hlt, if_neg hlt, if_neg (fun h => hij h.symm)]
        norm_num
  rw [Finset.sum_congr rfl fun i hi => hval i
    (by simpa using (Finset.mem_filter.mp hi).2)]
  -- reindex the filtered sum over the explicit segments
  have hsplit : ∑ i ∈ Finset.univ.filter
      (fun i : Fin r => k.val ≤ i.val),
      (if i.val < j.val then c ^ 2 * s ^ (2 * i.val)
        else if i.val = j.val then s ^ (2 * j.val) else 0) =
      (∑ t ∈ Finset.range (j.val - k.val),
        c ^ 2 * s ^ (2 * (k.val + t))) + s ^ (2 * j.val) := by
    -- direct evaluation: sum over Fin r of the guarded values
    rw [Finset.sum_filter]
    rw [Fin.sum_univ_eq_sum_range (fun v =>
      if k.val ≤ v then
        (if v < j.val then c ^ 2 * s ^ (2 * v)
          else if v = j.val then s ^ (2 * j.val) else 0) else 0) r]
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le k.val) (by omega :
        k.val ≤ r),
      ← Finset.sum_Ico_consecutive _ (hkj : k.val ≤ j.val) (by omega :
        j.val ≤ r)]
    have hzero1 : ∑ v ∈ Finset.Ico 0 k.val,
        (if k.val ≤ v then
          (if v < j.val then c ^ 2 * s ^ (2 * v)
            else if v = j.val then s ^ (2 * j.val) else 0) else 0) =
        0 :=
      Finset.sum_eq_zero fun v hv => by
        rw [if_neg (by
          simp only [Finset.mem_Ico] at hv
          omega)]
    have hmid : ∑ v ∈ Finset.Ico k.val j.val,
        (if k.val ≤ v then
          (if v < j.val then c ^ 2 * s ^ (2 * v)
            else if v = j.val then s ^ (2 * j.val) else 0) else 0) =
        ∑ t ∈ Finset.range (j.val - k.val),
          c ^ 2 * s ^ (2 * (k.val + t)) := by
      rw [Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr rfl fun t ht => ?_
      simp only [Finset.mem_range] at ht
      rw [if_pos (by omega), if_pos (by omega)]
    have htail : ∑ v ∈ Finset.Ico j.val r,
        (if k.val ≤ v then
          (if v < j.val then c ^ 2 * s ^ (2 * v)
            else if v = j.val then s ^ (2 * j.val) else 0) else 0) =
        s ^ (2 * j.val) := by
      have hjmem : j.val ∈ Finset.Ico j.val r := by
        simp only [Finset.mem_Ico]
        omega
      rw [Finset.sum_eq_single_of_mem j.val hjmem]
      · rw [if_pos hkj, if_neg (lt_irrefl _), if_pos rfl]
      · intro v hv hvj
        simp only [Finset.mem_Ico] at hv
        rw [if_pos (by omega), if_neg (by omega), if_neg hvj]
    rw [hzero1, hmid, htail, Finset.range_eq_Ico]
    ring
  rw [hsplit, kahan_telescope c s hcs k.val (j.val - k.val)]
  have hexp : 2 * (k.val + (j.val - k.val)) = 2 * j.val := by omega
  rw [hexp, ← pow_mul]
  ring_nf

/-- **Theorem 10.14 for the concrete algorithm** (display (10.22)
    shape): the three-block backward-error certificate of the truncated
    computed factor `R̃ = fl_choleskyTrunc` after `r` completed stages —
    Demmel-stable computed block, trace-controlled border under the
    computed-pivot domination `c`, terminal Schur residual `η` on the
    trailing block. -/
theorem higham10_14_fl_psd_cholesky_backward_error (fp : FPModel)
    (n : ℕ) (A : Fin n → Fin n → ℝ) (hn1 : gammaValid fp (n + 1))
    (hγlt : gamma fp (n + 1) < 1)
    (hsymm : ∀ i j : Fin n, A i j = A j i) (r : ℕ)
    (hdz : ∀ i : Fin n, i.val < r → fl_cholesky fp n A i i ≠ 0)
    (hpiv : ∀ i : Fin n, i.val < r → 0 ≤ fl_cholPivot fp n A i)
    (c : ℝ) (hc : 0 ≤ c)
    (hdom : ∀ j : Fin n, r ≤ j.val → ∀ k : Fin n, k.val < r →
      |fl_cholesky fp n A k j| ≤ c * |fl_cholesky fp n A k k|)
    (η : ℝ)
    (htrail : ∀ i j : Fin n, r ≤ i.val → r ≤ j.val →
      |∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < r),
        fl_cholesky fp n A k i * fl_cholesky fp n A k j - A i j| ≤ η) :
    (∀ i j : Fin n, i.val < r → j.val < r →
      |∑ k : Fin n, fl_choleskyTrunc fp n A r k i *
        fl_choleskyTrunc fp n A r k j - A i j| ≤
      gamma fp (n + 1) / (1 - gamma fp (n + 1)) *
        (Real.sqrt (A i i) * Real.sqrt (A j j))) ∧
    (∀ i j : Fin n, i.val < r → r ≤ j.val →
      |∑ k : Fin n, fl_choleskyTrunc fp n A r k i *
        fl_choleskyTrunc fp n A r k j - A i j| ≤
      gamma fp (n + 1) * c / (1 - gamma fp (n + 1)) *
        (Real.sqrt (A i i) *
         Real.sqrt (∑ k ∈ Finset.univ.filter
          (fun k : Fin n => k.val < r), A k k))) ∧
    (∀ i j : Fin n, r ≤ i.val → j.val < r →
      |∑ k : Fin n, fl_choleskyTrunc fp n A r k i *
        fl_choleskyTrunc fp n A r k j - A i j| ≤
      gamma fp (n + 1) * c / (1 - gamma fp (n + 1)) *
        (Real.sqrt (A j j) *
         Real.sqrt (∑ k ∈ Finset.univ.filter
          (fun k : Fin n => k.val < r), A k k))) ∧
    (∀ i j : Fin n, r ≤ i.val → r ≤ j.val →
      |∑ k : Fin n, fl_choleskyTrunc fp n A r k i *
        fl_choleskyTrunc fp n A r k j - A i j| ≤ η) :=
  fl_choleskyTrunc_backward_error fp n A hn1 hγlt hsymm r hdz hpiv
    c hc hdom η htrail

/-- **Section 10.4 prose**: leading principal submatrices of a matrix with
positive definite symmetric part are again in that class. -/
theorem higham10_4_nonsym_pd_leading_principal (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hA : higham10_4_IsNonsymPosDef n A)
    (k : ℕ) (hk : k ≤ n) :
    higham10_4_IsNonsymPosDef k
      (fun i j => A ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) :=
  nonsymPosDef_leading_principal hA k hk

/-- **(10.29) per-stage quadratic-form monotonicity** (Higham §10.4): the
    `hstage` hypothesis of `stage_maxEigenvalue_le`, discharged end-to-end for a
    genuine nonsymmetric-positive-definite stage `S`.  With `H = sym(S)` and
    `Ĥ = sym(Ŝ)` (`Ŝ = luFirstSchurComplement S`) and their symmetric inverses,
    the stage Gram form never exceeds the parent trailing-block Gram form:
    `(Ŝy)ᵀĤ⁻¹(Ŝy) ≤ (S·(0,y))ᵀH⁻¹(S·(0,y))`.  Threads `schur_gram_stage_le`
    through the alignment lemmas `higham10_29_luSchur_mulVec`,
    `higham10_29_S_mulVec_cons0`, `higham10_29_symPart_luSchur_eq`, and the
    positive-semidefinite inverse fact `spd_inv_quadForm_nonneg`. -/
theorem higham10_29_stage_quadForm_le {m : ℕ}
    (S : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hS : higham10_4_IsNonsymPosDef (m + 1) S)
    (Hinv : Fin (m + 1) → Fin (m + 1) → ℝ)
    (Hhatinv : Fin m → Fin m → ℝ)
    (hHinvRight : IsRightInverse (m + 1) (symmetricPart (m + 1) S) Hinv)
    (hHhatinvRight :
      IsRightInverse m (symmetricPart m (luFirstSchurComplement S)) Hhatinv)
    (y : Fin m → ℝ) :
    (∑ p : Fin m, matMulVec m (luFirstSchurComplement S) y p *
        matMulVec m Hhatinv
          (matMulVec m (luFirstSchurComplement S) y) p) ≤
      ∑ p : Fin (m + 1),
        matMulVec (m + 1) S (Fin.cons 0 y) p *
        matMulVec (m + 1) Hinv (matMulVec (m + 1) S (Fin.cons 0 y)) p := by
  set H : Fin (m + 1) → Fin (m + 1) → ℝ := symmetricPart (m + 1) S with hHdef
  set Hhat : Fin m → Fin m → ℝ :=
    symmetricPart m (luFirstSchurComplement S) with hHhatdef
  have hα : (0 : ℝ) < S 0 0 := nonsymPosDef_diag_pos hS 0
  have hsqrtα : Real.sqrt (S 0 0) * Real.sqrt (S 0 0) = S 0 0 :=
    Real.mul_self_sqrt hα.le
  have hkk : ∀ a b : ℝ,
      a / Real.sqrt (S 0 0) * (b / Real.sqrt (S 0 0)) = a * b / S 0 0 := by
    intro a b; rw [div_mul_div_comm, hsqrtα]
  have hHspd : IsSymPosDef (m + 1) H :=
    (nonsymPosDef_iff_symPartSPD (m + 1) S).mp hS
  set Z : Fin m → Fin m → ℝ :=
    fun i j => H i.succ j.succ - H 0 i.succ * H 0 j.succ / S 0 0 with hZdef
  have hZspd : IsSymPosDef m Z := by
    have h0 := spd_schur_complement_isSymPosDef H hHspd
    have heq : H 0 0 = S 0 0 := by rw [hHdef]; unfold symmetricPart; ring
    simp only [heq] at h0
    rw [hZdef]; exact h0
  obtain ⟨Zinv, hZinvSym, hZright, hZleft⟩ := spd_inverse_exists Z hZspd
  have hβv := schur_gram_stage_le (S 0 0) hα
      (fun i => H 0 i.succ)
      (fun i => (S 0 i.succ - S i.succ 0) / 2)
      (fun i j => H i.succ j.succ)
      H Hinv Z Zinv Hhat Hhatinv
      (by rw [hHdef]; unfold symmetricPart; ring)
      (fun _ => rfl)
      (fun i => by rw [hHdef]; exact symmetricPart_symmetric (m + 1) S i.succ 0)
      (fun _ _ => rfl)
      (fun _ _ => by rw [hZdef])
      hZinvSym
      (fun vv => matMulVec_of_isRightInverse Zinv Z hZleft vv)
      (spd_inv_quadForm_nonneg Z Zinv hZspd hZright
        (fun j => (S 0 j.succ - S j.succ 0) / 2 / Real.sqrt (S 0 0)))
      (fun i j => by
        rw [hHhatdef, higham10_29_symPart_luSchur_eq, hZdef, hHdef]
        simp only []
        rw [hkk, symmetricPart_symmetric (m + 1) S i.succ 0])
      (∑ j : Fin m, S 0 j.succ * y j)
      (fun i => ∑ j : Fin m, S i.succ j.succ * y j)
      (matMulVec_of_isRightInverse H Hinv hHinvRight _)
      (matMulVec_of_isRightInverse Hhat Hhatinv hHhatinvRight _)
  have hR : matMulVec (m + 1) S (Fin.cons 0 y)
      = Fin.cons (∑ j : Fin m, S 0 j.succ * y j)
          (fun i => ∑ j : Fin m, S i.succ j.succ * y j) :=
    higham10_29_S_mulVec_cons0 S y
  have hL : matMulVec m (luFirstSchurComplement S) y
      = (fun i => (∑ j : Fin m, S i.succ j.succ * y j)
          - (∑ j : Fin m, S 0 j.succ * y j) / S 0 0
            * (H 0 i.succ - (S 0 i.succ - S i.succ 0) / 2)) := by
    funext i
    rw [higham10_29_luSchur_mulVec, hHdef]
    unfold symmetricPart
    ring
  rw [hR, hL]
  exact hβv

/-- **(10.29) operator-norm single-stage decrease** (Higham §10.4): for a
    genuine nonsymmetric-positive-definite stage `S`, the maximum eigenvalue of
    the child stage Gram `Q(Ŝ) = Ŝᵀ Ĥ⁻¹ Ŝ` (`Ŝ = luFirstSchurComplement S`,
    `Ĥ = sym Ŝ`) is at most that of the parent stage Gram `Q(S) = Sᵀ H⁻¹ S`
    (`H = sym S`).  Composes the per-stage quadratic-form monotonicity
    `higham10_29_stage_quadForm_le` (as the `hstage` of `stage_maxEigenvalue_le`,
    giving `λ_max(Q(Ŝ)) ≤ λ_max(Q₂₂)`) with the trailing-block interlacing
    `finiteMaxEigenvalue_trailing_principal_le` (`λ_max(Q₂₂) ≤ λ_max(Q(S))`).
    This is the operator-norm step chained by the GE stage induction. -/
theorem higham10_29_stage_operator_le {m : ℕ} (hm : 0 < m)
    (S : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hS : higham10_4_IsNonsymPosDef (m + 1) S)
    (Hinv : Fin (m + 1) → Fin (m + 1) → ℝ)
    (Hhatinv : Fin m → Fin m → ℝ)
    (hHinvSym : ∀ i j, Hinv i j = Hinv j i)
    (hHhatinvSym : ∀ i j, Hhatinv i j = Hhatinv j i)
    (hHinvRight : IsRightInverse (m + 1) (symmetricPart (m + 1) S) Hinv)
    (hHhatinvRight :
      IsRightInverse m (symmetricPart m (luFirstSchurComplement S)) Hhatinv) :
    finiteMaxEigenvalue hm
        (matMul m (matMul m (fun a b => luFirstSchurComplement S b a) Hhatinv)
          (luFirstSchurComplement S))
        (gram_conj_isSymm Hhatinv (luFirstSchurComplement S) hHhatinvSym) ≤
      finiteMaxEigenvalue (Nat.succ_pos m)
        (matMul (m + 1) (matMul (m + 1) (fun a b => S b a) Hinv) S)
        (gram_conj_isSymm Hinv S hHinvSym) := by
  have hstep := stage_maxEigenvalue_le hm S Hinv (luFirstSchurComplement S)
      Hhatinv hHinvSym hHhatinvSym
      (fun y => higham10_29_stage_quadForm_le S hS Hinv Hhatinv
        hHinvRight hHhatinvRight y)
  have htrail := finiteMaxEigenvalue_trailing_principal_le m hm
      (matMul (m + 1) (matMul (m + 1) (fun a b => S b a) Hinv) S)
      (gram_conj_isSymm Hinv S hHinvSym)
      (fun i j => gram_conj_isSymm Hinv S hHinvSym i.succ j.succ)
  exact le_trans hstep htrail

/-- **(10.29) self-contained operator-norm single-stage decrease** (Higham
    §10.4): the induction-ready form of `higham10_29_stage_operator_le` whose
    only hypothesis is that the stage `S` is nonsymmetric positive definite.
    The symmetric inverses `H⁻¹ = sym(S)⁻¹` and `Ĥ⁻¹ = sym(luSchur S)⁻¹` are
    produced internally by `spd_inverse_exists` (the symmetric parts are SPD via
    `nonsymPosDef_iff_symPartSPD`, and `luFirstSchurComplement S` stays nonsym-PD
    via `higham10_29_luFirstSchurComplement_isNonsymPosDef`), so a GE stage
    induction can chain the decrease `λ_max(Q(Ŝ)) ≤ λ_max(Q(S))` across the
    Schur-complement recursion without threading inverse data by hand. -/
theorem higham10_29_stage_operator_le_exists {m : ℕ} (hm : 0 < m)
    (S : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hS : higham10_4_IsNonsymPosDef (m + 1) S) :
    ∃ (Hinv : Fin (m + 1) → Fin (m + 1) → ℝ)
      (Hhatinv : Fin m → Fin m → ℝ)
      (hHinvSym : ∀ i j, Hinv i j = Hinv j i)
      (hHhatinvSym : ∀ i j, Hhatinv i j = Hhatinv j i),
      finiteMaxEigenvalue hm
          (matMul m
            (matMul m (fun a b => luFirstSchurComplement S b a) Hhatinv)
            (luFirstSchurComplement S))
          (gram_conj_isSymm Hhatinv (luFirstSchurComplement S) hHhatinvSym) ≤
        finiteMaxEigenvalue (Nat.succ_pos m)
          (matMul (m + 1) (matMul (m + 1) (fun a b => S b a) Hinv) S)
          (gram_conj_isSymm Hinv S hHinvSym) := by
  obtain ⟨Hinv, hHinvSym, hHinvRight, _⟩ :=
    spd_inverse_exists (symmetricPart (m + 1) S)
      ((nonsymPosDef_iff_symPartSPD (m + 1) S).mp hS)
  obtain ⟨Hhatinv, hHhatinvSym, hHhatinvRight, _⟩ :=
    spd_inverse_exists (symmetricPart m (luFirstSchurComplement S))
      ((nonsymPosDef_iff_symPartSPD m (luFirstSchurComplement S)).mp
        (higham10_29_luFirstSchurComplement_isNonsymPosDef S hS))
  exact ⟨Hinv, Hhatinv, hHinvSym, hHhatinvSym,
    higham10_29_stage_operator_le hm S hS Hinv Hhatinv hHinvSym hHhatinvSym
      hHinvRight hHhatinvRight⟩

end NumStability
