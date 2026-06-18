-- Algorithms/QR/GivensQR.lean
--
-- Backward error analysis for Givens QR factorization (Higham §18.5).
--
-- Lemma 18.8: A sequence of r Givens rotations with per-step error ≤ c
--   yields Â_{r+1} = Qᵀ(A + ΔA) with ‖ΔA‖_F ≤ r·c·‖A‖_F.
--
-- Theorem 18.9: Givens QR gives A + ΔA = Q·R̂ with ‖ΔA‖_F bounded.
--   For an n×n matrix, r = n(n-1)/2 Givens rotations are used.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra
import LeanFpAnalysis.FP.Algorithms.QR.GivensSpec
import LeanFpAnalysis.FP.Algorithms.QR.HouseholderQR

namespace LeanFpAnalysis.FP

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- §18.5  Lemma 18.8: Sequence of Givens rotations backward error
-- ============================================================

/-- **Backward error from a sequence of perturbed Givens rotations**
    (Lemma 18.8, normwise form).

    Given r Givens rotations G₁,...,Gᵣ, if each computed application
    satisfies ‖ΔGₖ‖_F ≤ c, then the product
    (Gᵣ + ΔGᵣ)···(G₁ + ΔG₁)A = Qᵀ(A + ΔA)
    where Q is orthogonal and ‖ΔA‖_F ≤ r·c·‖A‖_F.

    This is an instance of OrthogonalSequenceBackwardError since
    Givens rotations are orthogonal matrices and the accumulation
    mechanism is identical to Lemma 18.3 for Householder. -/
abbrev GivensSequenceBackwardError (n : ℕ) (A : Fin n → Fin n → ℝ)
    (A_hat : Fin n → Fin n → ℝ) (r : ℕ) (c : ℝ) :=
  OrthogonalSequenceBackwardError n A A_hat r c

-- ============================================================
-- §18.5  Theorem 18.9: Givens QR backward error
-- ============================================================

/-- **Theorem 18.9**: Givens QR factorization backward error (normwise).

    The computed R̂ from Givens QR satisfies A + ΔA = Q·R̂
    where Q is orthogonal and ‖ΔA‖_F ≤ c_bound.

    For an n×n matrix, r = n(n-1)/2 Givens rotations are used,
    each with per-step error ≤ √2·γ₆. The total bound is
    c_bound = r · √2·γ₆ · ‖A‖_F. -/
structure GivensQRBackwardError (n : ℕ) (A R_hat : Fin n → Fin n → ℝ)
    (c_bound : ℝ) : Prop where
  /-- There exists an orthogonal Q such that A + ΔA = Q·R̂ with bounded ΔA. -/
  result : ∃ (Q : Fin n → Fin n → ℝ) (ΔA : Fin n → Fin n → ℝ),
    IsOrthogonal n Q ∧
    (∀ i j, matMul n Q R_hat i j = A i j + ΔA i j) ∧
    frobNorm ΔA ≤ c_bound

/-- Theorem 18.9 instantiation: r Givens rotations with per-step error ≤ c
    yield total backward error ≤ r · c · ‖A‖_F.

    The proof is identical to Theorem 18.4 since both use the same
    orthogonal sequence backward error structure (Lemma 18.3/18.8). -/
theorem givens_qr_backward (n : ℕ) (r : ℕ) (hr : 0 < r)
    (A R_hat : Fin n → Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hSeq : GivensSequenceBackwardError n A R_hat r c) :
    GivensQRBackwardError n A R_hat
      (↑r * c * frobNorm A) := by
  obtain ⟨Q, ΔA, hQ, hAhat, hbound⟩ := hSeq.result
  exact ⟨⟨Q, ΔA, hQ, by
    intro i j
    have hR : R_hat = matMul n (matTranspose Q) (fun a b => A a b + ΔA a b) :=
      funext fun k => funext fun l => hAhat k l
    have hQQT : matMul n Q (matTranspose Q) = idMatrix n :=
      funext fun a => funext fun b => hQ.right_inv a b
    rw [hR, ← matMul_assoc, hQQT, matMul_id_left], hbound⟩⟩

-- ============================================================
-- Rectangular Givens QR backward-error bridge
-- ============================================================

/-- A supplied rectangular sequence of perturbed Givens transformations.

    The transformations act on the `m` rows of an `m x n` matrix.  This is a
    source-facing wrapper around the existing rectangular orthogonal-sequence
    machinery: it records the concrete sequence, per-step orthogonality and
    perturbation bounds, and the final computed rectangular factor. -/
structure RectangularGivensSequenceBackwardError (m n : ℕ)
    (A R_hat : Fin m → Fin n → ℝ) (r : ℕ) (c : ℝ) : Type where
  /-- The rectangular states after each perturbed transformation. -/
  A_hat : ℕ → Fin m → Fin n → ℝ
  /-- The exact orthogonal transformations applied to rows. -/
  P : ℕ → Fin m → Fin m → ℝ
  /-- Per-step perturbation matrices. -/
  ΔP : ℕ → Fin m → Fin m → ℝ
  /-- Initial state. -/
  init : A_hat 0 = A
  /-- Final computed rectangular factor. -/
  final : A_hat r = R_hat
  /-- Each exact row transformation is orthogonal. -/
  orth : ∀ k, k < r → IsOrthogonal m (P k)
  /-- Each transformation perturbation has Frobenius norm at most `c`. -/
  pert : ∀ k, k < r → frobNorm (ΔP k) ≤ c
  /-- State transition by the perturbed transformation. -/
  step : ∀ k, k < r →
    A_hat (k + 1) = matMulRectLeft
      (fun a b => P k a b + ΔP k a b) (A_hat k)

/-- Rectangular Givens QR backward-error certificate.

    For an `m x n` computed rectangular factor `R_hat`, there are an orthogonal
    row factor `Q` and a rectangular perturbation `ΔA` such that
    `Q * R_hat = A + ΔA`, with rectangular Frobenius radius `c_bound`. -/
structure RectangularGivensQRBackwardError (m n : ℕ)
    (A R_hat : Fin m → Fin n → ℝ) (c_bound : ℝ) : Prop where
  /-- There exists an orthogonal row factor and bounded rectangular perturbation. -/
  result : ∃ (Q : Fin m → Fin m → ℝ) (ΔA : Fin m → Fin n → ℝ),
    IsOrthogonal m Q ∧
    (∀ i j, matMulRectLeft Q R_hat i j = A i j + ΔA i j) ∧
    frobNormRect ΔA ≤ c_bound

/-- Rectangular Givens QR backward-error bridge.

    A supplied sequence of `r` perturbed orthogonal row transformations gives a
    rectangular backward-error certificate with the rigorous geometric radius
    `((1+c)^r - 1) * ‖A‖_F`.  This is the rectangular counterpart needed for
    tall Givens QR examples; machine-specific traces and downstream QR
    perturbation bounds are separate assumptions. -/
theorem rectangular_givens_qr_backward (m n r : ℕ)
    (A R_hat : Fin m → Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hSeq : RectangularGivensSequenceBackwardError m n A R_hat r c) :
    RectangularGivensQRBackwardError m n A R_hat
      (((1 + c) ^ r - 1) * frobNormRect A) := by
  obtain ⟨Q, ΔA, hQ, hAhat, hbound⟩ :=
    rect_orthogonal_sequence_geometric m n r A hSeq.A_hat hSeq.P hSeq.ΔP
      c hc hSeq.init hSeq.orth hSeq.pert hSeq.step
  refine ⟨⟨Q, ΔA, hQ, ?_, hbound⟩⟩
  let B : Fin m → Fin n → ℝ := fun a b => A a b + ΔA a b
  have hR : R_hat = matMulRectLeft (matTranspose Q) B := by
    rw [← hSeq.final]
    exact funext fun i => funext fun j => hAhat i j
  have hQQT : matMul m Q (matTranspose Q) = idMatrix m :=
    funext fun a => funext fun b => hQ.right_inv a b
  intro i j
  calc
    matMulRectLeft Q R_hat i j
        = matMulRectLeft Q (matMulRectLeft (matTranspose Q) B) i j := by
            rw [hR]
    _ = matMulRectLeft (matMul m Q (matTranspose Q)) B i j := by
            rw [matMulRectLeft_assoc]
    _ = matMulRectLeft (idMatrix m) B i j := by
            rw [hQQT]
    _ = B i j := by
            rw [matMulRectLeft_id]
    _ = A i j + ΔA i j := rfl

/-- Figure 1.5-shaped rectangular Givens QR backward-error bridge.

    For the Chapter 1 `10 x 6` schedule, the already proved rotation count is
    `39`, so the generic rectangular bridge yields the displayed-shape radius
    `((1+c)^39 - 1) * ‖A‖_F` once the actual perturbed Givens sequence is
    supplied. -/
theorem rectangular_givens_qr_backward_ten_by_six
    (A R_hat : Fin 10 → Fin 6 → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hSeq : RectangularGivensSequenceBackwardError 10 6 A R_hat
      (givensQRRectangularRotationCount 10 6) c) :
    RectangularGivensQRBackwardError 10 6 A R_hat
      (((1 + c) ^ 39 - 1) * frobNormRect A) := by
  simpa [givensQRRectangularRotationCount_ten_by_six] using
    rectangular_givens_qr_backward 10 6
      (givensQRRectangularRotationCount 10 6) A R_hat c hc hSeq

/-- The scalar coefficient `2^r - 1` is nonnegative. -/
lemma two_pow_sub_one_nonneg (r : ℕ) :
    0 ≤ (2 : ℝ) ^ r - 1 := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      rw [pow_succ]
      nlinarith

/-- Finite geometric accumulation is linear in `c` on the unit interval:
    `(1+c)^r - 1 ≤ (2^r - 1)c` for `0 ≤ c ≤ 1`. -/
theorem one_add_pow_sub_one_le_two_pow_sub_one_mul_of_le_one
    (r : ℕ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (1 + c) ^ r - 1 ≤ (((2 : ℝ) ^ r - 1) * c) := by
  have hmain : ∀ r : ℕ,
      0 ≤ (2 : ℝ) ^ r - 1 ∧
      (1 + c) ^ r ≤ 1 + (((2 : ℝ) ^ r - 1) * c) := by
    intro r
    induction r with
    | zero =>
        constructor <;> simp
    | succ r ih =>
        rcases ih with ⟨ha_nonneg, ih_bound⟩
        have hc_nonneg : 0 ≤ 1 + c := by linarith
        have hc_square_le : c * c ≤ c := by
          have hmul := mul_le_mul_of_nonneg_left hc1 hc0
          simpa [one_mul] using hmul
        constructor
        · rw [pow_succ]
          nlinarith
        · calc
            (1 + c) ^ Nat.succ r
                = (1 + c) ^ r * (1 + c) := by
                    rw [pow_succ]
            _ ≤ (1 + (((2 : ℝ) ^ r - 1) * c)) * (1 + c) := by
                    exact mul_le_mul_of_nonneg_right ih_bound hc_nonneg
            _ = 1 + ((((2 : ℝ) ^ r - 1 + 1) * c)) +
                  (((2 : ℝ) ^ r - 1) * (c * c)) := by
                    ring
            _ ≤ 1 + ((((2 : ℝ) ^ r - 1 + 1) * c)) +
                  (((2 : ℝ) ^ r - 1) * c) := by
                    have hx :
                        ((2 : ℝ) ^ r - 1) * (c * c) ≤
                          ((2 : ℝ) ^ r - 1) * c :=
                      mul_le_mul_of_nonneg_left hc_square_le ha_nonneg
                    linarith
            _ = 1 + (((2 : ℝ) ^ Nat.succ r - 1) * c) := by
                    rw [pow_succ]
                    ring
  have h := (hmain r).2
  linarith

/-- If a per-rotation error coefficient `c` is bounded by unit roundoff `u ≤ 1`,
    then the geometric Givens growth factor is bounded by `(2^r-1)u`. -/
theorem one_add_pow_sub_one_le_two_pow_sub_one_mul_unit
    (r : ℕ) {c u : ℝ} (hc0 : 0 ≤ c) (hcu : c ≤ u) (hu1 : u ≤ 1) :
    (1 + c) ^ r - 1 ≤ (((2 : ℝ) ^ r - 1) * u) := by
  have hc1 : c ≤ 1 := le_trans hcu hu1
  have hgeom := one_add_pow_sub_one_le_two_pow_sub_one_mul_of_le_one r hc0 hc1
  have hcoef : 0 ≤ (2 : ℝ) ^ r - 1 := two_pow_sub_one_nonneg r
  have hcu_scaled :
      (((2 : ℝ) ^ r - 1) * c) ≤ (((2 : ℝ) ^ r - 1) * u) :=
    mul_le_mul_of_nonneg_left hcu hcoef
  exact le_trans hgeom hcu_scaled

/-- The `10 x 6` Chapter 1 Givens QR geometric factor is explicitly `O(u)`
    under a visible small-roundoff hypothesis. -/
theorem one_add_pow_39_sub_one_le_two_pow_39_sub_one_mul_unit
    {c u : ℝ} (hc0 : 0 ≤ c) (hcu : c ≤ u) (hu1 : u ≤ 1) :
    (1 + c) ^ 39 - 1 ≤ (((2 : ℝ) ^ 39 - 1) * u) := by
  simpa using
    one_add_pow_sub_one_le_two_pow_sub_one_mul_unit 39 hc0 hcu hu1

/-- Unit-roundoff-shaped corollary of the `10 x 6` rectangular Givens QR
    backward-error bridge.

    This closes the finite-rotation geometric `O(u)` step for the Chapter 1
    example once the supplied sequence has per-step coefficient `c ≤ u`.  It is
    still only the backward-error side of the source discussion; the later QR
    perturbation result corresponding to equation (18.27) is a separate theorem
    family. -/
theorem rectangular_givens_qr_backward_ten_by_six_unit_roundoff
    (A R_hat : Fin 10 → Fin 6 → ℝ) (c u : ℝ)
    (hc0 : 0 ≤ c) (hcu : c ≤ u) (hu1 : u ≤ 1)
    (hSeq : RectangularGivensSequenceBackwardError 10 6 A R_hat
      (givensQRRectangularRotationCount 10 6) c) :
    RectangularGivensQRBackwardError 10 6 A R_hat
      (((2 : ℝ) ^ 39 - 1) * u * frobNormRect A) := by
  obtain ⟨Q, ΔA, hQ, hQR, hbound⟩ :=
    (rectangular_givens_qr_backward_ten_by_six A R_hat c hc0 hSeq).result
  refine ⟨⟨Q, ΔA, hQ, hQR, ?_⟩⟩
  have hgeom :=
    one_add_pow_39_sub_one_le_two_pow_39_sub_one_mul_unit hc0 hcu hu1
  have hscaled :
      ((1 + c) ^ 39 - 1) * frobNormRect A ≤
        (((2 : ℝ) ^ 39 - 1) * u) * frobNormRect A :=
    mul_le_mul_of_nonneg_right hgeom (frobNormRect_nonneg A)
  exact le_trans hbound (by simpa [mul_assoc] using hscaled)

-- ============================================================
-- Economy-size QR source predicates for the Stewart theorem
-- ============================================================

/-- Economy-size `Q` has orthonormal columns. -/
def EconomyQHasOrthonormalColumns {m n : ℕ}
    (Q : Fin m → Fin n → ℝ) : Prop :=
  ∀ j k : Fin n, ∑ i : Fin m, Q i j * Q i k = if j = k then 1 else 0

/-- Full-column-rank predicate for an `m x n` rectangular matrix in the local
    matrix API. -/
def RectangularFullColumnRank (m n : ℕ)
    (A : Fin m → Fin n → ℝ) : Prop :=
  ∀ x : Fin n → ℝ, rectMatMulVec A x = (fun _ : Fin m => 0) →
    x = fun _ : Fin n => 0

/-- Upper-triangular square QR factor. -/
def QRUpperTriangular (n : ℕ) (R : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, j.val < i.val → R i j = 0

/-- Lower-triangular square matrix predicate used in Stewart's induction proof. -/
def QRLowerTriangular (n : ℕ) (L : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, i.val < j.val → L i j = 0

/-- Nonnegative diagonal normalization for a square QR factor. -/
def QRNonnegativeDiagonal (n : ℕ) (R : Fin n → Fin n → ℝ) : Prop :=
  ∀ i : Fin n, 0 ≤ R i i

/-- Visible small-perturbation side condition for Stewart-style QR-factor
    perturbation theorems.

    Higham equation (18.27) only applies when the data perturbation is
    sufficiently small.  The exact source threshold is still an open Chapter 18
    dependency, so this predicate keeps the threshold as explicit data instead
    of hiding it inside the Stewart handoff interface. -/
def QRFactorPerturbationSmallEnough (m n : ℕ)
    (A DeltaA : Fin m → Fin n → ℝ) (smallRadius : ℝ) : Prop :=
  frobNormRect DeltaA ≤ smallRadius * frobNormRect A

/-- Strict version of the visible Stewart small-perturbation side condition.

    Stewart Theorem 3.1 uses strict hypotheses.  The non-strict predicate above
    is still useful for closed `<=` handoffs, while this predicate records the
    source-facing strict threshold needed for the nonlinear theorem proof. -/
def QRFactorPerturbationStrictlySmallEnough (m n : ℕ)
    (A DeltaA : Fin m → Fin n → ℝ) (smallRadius : ℝ) : Prop :=
  frobNormRect DeltaA < smallRadius * frobNormRect A

/-- A relative perturbation bound is small enough whenever its relative radius
    is below the exposed Stewart smallness radius. -/
theorem QRFactorPerturbationSmallEnough.of_relative_le {m n : ℕ}
    {A DeltaA : Fin m → Fin n → ℝ} {relA smallRadius : ℝ}
    (hDelta : frobNormRect DeltaA ≤ relA * frobNormRect A)
    (hrel : relA ≤ smallRadius) :
    QRFactorPerturbationSmallEnough m n A DeltaA smallRadius := by
  exact le_trans hDelta
    (mul_le_mul_of_nonneg_right hrel (frobNormRect_nonneg A))

/-- A relative perturbation bound is strictly small enough whenever its
    relative radius is strictly below the exposed Stewart radius and the source
    matrix has positive Frobenius norm. -/
theorem QRFactorPerturbationStrictlySmallEnough.of_relative_lt {m n : ℕ}
    {A DeltaA : Fin m → Fin n → ℝ} {relA smallRadius : ℝ}
    (hDelta : frobNormRect DeltaA ≤ relA * frobNormRect A)
    (hrel : relA < smallRadius)
    (hApos : 0 < frobNormRect A) :
    QRFactorPerturbationStrictlySmallEnough m n A DeltaA smallRadius := by
  exact lt_of_le_of_lt hDelta (mul_lt_mul_of_pos_right hrel hApos)

/-- Source-shaped economy QR factorization predicate for a full column-rank
    rectangular matrix.  This records the mathematical QR objects used by
    Higham/Stewart; it is not a machine-trace or experiment surrogate. -/
structure EconomyQRFactorization (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (Q : Fin m → Fin n → ℝ)
    (R : Fin n → Fin n → ℝ) : Prop where
  /-- The economy `Q` has orthonormal columns. -/
  orthonormalColumns : EconomyQHasOrthonormalColumns Q
  /-- The economy factors multiply back to `A`. -/
  factorization : ∀ i j, rectMatMul Q R i j = A i j
  /-- The square `R` factor is upper triangular. -/
  upper : QRUpperTriangular n R
  /-- The square `R` factor uses the source nonnegative diagonal convention. -/
  diag_nonneg : QRNonnegativeDiagonal n R

/-- Economy QR factorization together with the source full-column-rank
    hypothesis. -/
structure FullColumnRankEconomyQRFactorization (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (Q : Fin m → Fin n → ℝ)
    (R : Fin n → Fin n → ℝ) : Prop where
  /-- The rectangular source matrix has rank `n`. -/
  fullColumnRank : RectangularFullColumnRank m n A
  /-- The economy-size QR factorization data. -/
  qr : EconomyQRFactorization m n A Q R

/-- The first `n` columns of a full `m x m` orthogonal matrix, viewed as an
    economy-size `m x n` factor. -/
def economyQOfFullOrthogonal {m n : ℕ} (hmn : n ≤ m)
    (Q : Fin m → Fin m → ℝ) : Fin m → Fin n → ℝ :=
  fun i j => Q i ⟨j.val, lt_of_lt_of_le j.isLt hmn⟩

/-- The first `n` columns of an orthogonal `m x m` matrix are orthonormal. -/
theorem economyQOfFullOrthogonal_hasOrthonormalColumns {m n : ℕ}
    (hmn : n ≤ m) {Q : Fin m → Fin m → ℝ}
    (hQ : IsOrthogonal m Q) :
    EconomyQHasOrthonormalColumns (economyQOfFullOrthogonal hmn Q) := by
  intro j k
  let j' : Fin m := ⟨j.val, lt_of_lt_of_le j.isLt hmn⟩
  let k' : Fin m := ⟨k.val, lt_of_lt_of_le k.isLt hmn⟩
  have hcol := hQ.col_orthonormal j' k'
  change (∑ i : Fin m, Q i j' * Q i k') =
    (if j = k then 1 else 0)
  by_cases hjk : j = k
  · subst k
    simpa [j', k'] using hcol
  · have hneq : j' ≠ k' := by
      intro h
      apply hjk
      have hval : j.val = k.val := by
        have := congrArg (fun x : Fin m => x.val) h
        simpa [j', k'] using this
      exact Fin.ext hval
    simpa [hjk, hneq, j', k'] using hcol

/-- An economy `Q` with orthonormal columns preserves the squared Euclidean
    norm of a coefficient vector. -/
theorem EconomyQHasOrthonormalColumns.vecNorm2Sq_rectMatMulVec {m n : ℕ}
    {Q : Fin m → Fin n → ℝ} (hQ : EconomyQHasOrthonormalColumns Q)
    (y : Fin n → ℝ) :
    vecNorm2Sq (rectMatMulVec Q y) = vecNorm2Sq y := by
  classical
  unfold rectMatMulVec vecNorm2Sq
  calc
    (∑ i : Fin m, (∑ a : Fin n, Q i a * y a) ^ 2)
        = ∑ i : Fin m, ∑ a : Fin n, ∑ b : Fin n,
            (Q i a * Q i b) * (y a * y b) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [pow_two]
          have h := Finset.sum_mul_sum
            (s := (Finset.univ : Finset (Fin n)))
            (t := (Finset.univ : Finset (Fin n)))
            (f := fun a => Q i a * y a)
            (g := fun b => Q i b * y b)
          simpa [mul_assoc, mul_left_comm, mul_comm] using h
    _ = ∑ a : Fin n, ∑ b : Fin n,
          (∑ i : Fin m, Q i a * Q i b) * (y a * y b) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro b _
          rw [← Finset.sum_mul]
    _ = ∑ a : Fin n, ∑ b : Fin n,
          (if a = b then 1 else 0) * (y a * y b) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          rw [hQ a b]
    _ = ∑ a : Fin n, y a ^ 2 := by
          apply Finset.sum_congr rfl
          intro a _
          simp [pow_two]

/-- Left multiplication by an economy `Q` with orthonormal columns preserves
    squared Frobenius norm. -/
theorem EconomyQHasOrthonormalColumns.frobNormSqRect_rectMatMul {m n : ℕ}
    {Q : Fin m → Fin n → ℝ} (hQ : EconomyQHasOrthonormalColumns Q)
    (R : Fin n → Fin n → ℝ) :
    frobNormSqRect (rectMatMul Q R) = frobNormSqRect R := by
  rw [frobNormSqRect_eq_sum_vecNorm2Sq_cols,
    frobNormSqRect_eq_sum_vecNorm2Sq_cols]
  apply Finset.sum_congr rfl
  intro j _
  simpa [rectMatMul, rectMatMulVec] using
    hQ.vecNorm2Sq_rectMatMulVec (fun k : Fin n => R k j)

/-- Left multiplication by an economy `Q` with orthonormal columns preserves
    Frobenius norm. -/
theorem EconomyQHasOrthonormalColumns.frobNormRect_rectMatMul {m n : ℕ}
    {Q : Fin m → Fin n → ℝ} (hQ : EconomyQHasOrthonormalColumns Q)
    (R : Fin n → Fin n → ℝ) :
    frobNormRect (rectMatMul Q R) = frobNormRect R := by
  unfold frobNormRect
  rw [hQ.frobNormSqRect_rectMatMul R]

/-- In an economy QR factorization, `A = Q R` has the same squared Frobenius
    norm as the square `R` factor. -/
theorem EconomyQRFactorization.frobNormSqRect_eq_R {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {Q : Fin m → Fin n → ℝ}
    {R : Fin n → Fin n → ℝ} (hQR : EconomyQRFactorization m n A Q R) :
    frobNormSqRect A = frobNormSqRect R := by
  have hprod := hQR.orthonormalColumns.frobNormSqRect_rectMatMul R
  have hA : rectMatMul Q R = A := by
    ext i j
    exact hQR.factorization i j
  rw [← hA]
  exact hprod

/-- In an economy QR factorization, `A = Q R` has the same Frobenius norm as
    the square `R` factor. -/
theorem EconomyQRFactorization.frobNormRect_eq_R {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {Q : Fin m → Fin n → ℝ}
    {R : Fin n → Fin n → ℝ} (hQR : EconomyQRFactorization m n A Q R) :
    frobNormRect A = frobNormRect R := by
  have hprod := hQR.orthonormalColumns.frobNormRect_rectMatMul R
  have hA : rectMatMul Q R = A := by
    ext i j
    exact hQR.factorization i j
  rw [← hA]
  exact hprod

/-- Gram identity for left multiplication by an economy `Q` with orthonormal
    columns: `(QR)ᵀ(QR) = RᵀR`. -/
theorem EconomyQHasOrthonormalColumns.rectGram_rectMatMul {m n : ℕ}
    {Q : Fin m → Fin n → ℝ} (hQ : EconomyQHasOrthonormalColumns Q)
    (R : Fin n → Fin n → ℝ) :
    rectMatMul (finiteTranspose (rectMatMul Q R)) (rectMatMul Q R) =
      matMul n (matTranspose R) R := by
  ext i j
  unfold rectMatMul finiteTranspose matMul matTranspose
  calc
    (∑ a : Fin m,
        (∑ b : Fin n, Q a b * R b i) *
          (∑ c : Fin n, Q a c * R c j))
        = ∑ a : Fin m, ∑ b : Fin n, ∑ c : Fin n,
            (Q a b * Q a c) * (R b i * R c j) := by
          apply Finset.sum_congr rfl
          intro a _
          have h := Finset.sum_mul_sum
            (s := (Finset.univ : Finset (Fin n)))
            (t := (Finset.univ : Finset (Fin n)))
            (f := fun b => Q a b * R b i)
            (g := fun c => Q a c * R c j)
          simpa [mul_assoc, mul_left_comm, mul_comm] using h
    _ = ∑ b : Fin n, ∑ c : Fin n,
          (∑ a : Fin m, Q a b * Q a c) * (R b i * R c j) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro c _
          rw [← Finset.sum_mul]
    _ = ∑ b : Fin n, ∑ c : Fin n,
          (if b = c then 1 else 0) * (R b i * R c j) := by
          apply Finset.sum_congr rfl
          intro b _
          apply Finset.sum_congr rfl
          intro c _
          rw [hQ b c]
    _ = ∑ b : Fin n, R b i * R b j := by
          simp

/-- In an economy QR factorization, `AᵀA = RᵀR`. -/
theorem EconomyQRFactorization.rectGram_eq_R {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {Q : Fin m → Fin n → ℝ}
    {R : Fin n → Fin n → ℝ} (hQR : EconomyQRFactorization m n A Q R) :
    rectMatMul (finiteTranspose A) A =
      matMul n (matTranspose R) R := by
  have hprod :=
    hQR.orthonormalColumns.rectGram_rectMatMul R
  have hA : rectMatMul Q R = A := by
    ext i j
    exact hQR.factorization i j
  rw [← hA]
  exact hprod

-- ============================================================
-- Stewart 1977 linearized QR perturbation operator
-- ============================================================

/-- Stewart's linearized QR operator `T`.

For an upper-triangular perturbation `F` of the `R` factor, Stewart defines
`T F = RᵀF + FᵀR`.  The definition is given on all square matrices; the
upper-triangular restriction is carried by `QRUpperTriangular` in theorem
statements. -/
noncomputable def stewartQRLinearMap {n : ℕ}
    (R F : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => matMul n (matTranspose R) F i j +
    matMul n (matTranspose F) R i j

/-- Stewart's natural extension `T̂` applied to an unrestricted square matrix.

The formula is the same as `T`, but the separate name records the source
distinction in Theorem 2.2: `T` is restricted to upper-triangular unknowns,
while `T̂` may be applied to the full matrix `G = QᵀE`. -/
noncomputable def stewartQRNaturalExtension {n : ℕ}
    (R G : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  stewartQRLinearMap R G

/-- The matrix `G = QᵀE` used by Stewart's Theorem 2.2/3.1 handoff. -/
noncomputable def stewartProjectedPerturbation {m n : ℕ}
    (Q E : Fin m → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  rectMatMul (finiteTranspose Q) E

/-- Stewart's displayed linear right-hand side
`Rᵀ(QᵀE) + (EᵀQ)R`. -/
noncomputable def stewartQRLinearRhs {m n : ℕ}
    (R : Fin n → Fin n → ℝ) (Q E : Fin m → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    matMul n (matTranspose R) (stewartProjectedPerturbation Q E) i j +
      matMul n (rectMatMul (finiteTranspose E) Q) R i j

/-- Transposing `QᵀE` gives `EᵀQ` in the local rectangular matrix API. -/
theorem matTranspose_stewartProjectedPerturbation {m n : ℕ}
    (Q E : Fin m → Fin n → ℝ) :
    matTranspose (stewartProjectedPerturbation Q E) =
      rectMatMul (finiteTranspose E) Q := by
  ext i j
  unfold stewartProjectedPerturbation matTranspose rectMatMul finiteTranspose
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Stewart's displayed right-hand side is `T̂(QᵀE)`.

This closes the source algebra between equation (3.1)'s linear term
`Rᵀ(QᵀE)+(EᵀQ)R` and Theorem 2.2's special right-hand side `T̂G`. -/
theorem stewartQRLinearRhs_eq_naturalExtension {m n : ℕ}
    (R : Fin n → Fin n → ℝ) (Q E : Fin m → Fin n → ℝ) :
    stewartQRLinearRhs R Q E =
      stewartQRNaturalExtension R (stewartProjectedPerturbation Q E) := by
  ext i j
  unfold stewartQRLinearRhs stewartQRNaturalExtension stewartQRLinearMap
  rw [matTranspose_stewartProjectedPerturbation Q E]

/-- The first cross term in `(A+E)ᵀ(A+E)` for an economy QR factorization:
    `AᵀE = Rᵀ(QᵀE)`. -/
theorem EconomyQRFactorization.leftCrossGram_eq_stewartProjected
    {m n : ℕ} {A E : Fin m → Fin n → ℝ}
    {Q : Fin m → Fin n → ℝ} {R : Fin n → Fin n → ℝ}
    (hQR : EconomyQRFactorization m n A Q R) :
    rectMatMul (finiteTranspose A) E =
      matMul n (matTranspose R) (stewartProjectedPerturbation Q E) := by
  ext i j
  unfold rectMatMul finiteTranspose matMul matTranspose
    stewartProjectedPerturbation
  calc
    (∑ a : Fin m, A a i * E a j)
        = ∑ a : Fin m, (∑ b : Fin n, Q a b * R b i) * E a j := by
          apply Finset.sum_congr rfl
          intro a _
          simpa [rectMatMul] using
            congrArg (fun x : ℝ => x * E a j)
              (Eq.symm (hQR.factorization a i))
    _ = ∑ a : Fin m, ∑ b : Fin n, (Q a b * R b i) * E a j := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_mul]
    _ = ∑ b : Fin n, ∑ a : Fin m, (Q a b * R b i) * E a j := by
          rw [Finset.sum_comm]
    _ = ∑ b : Fin n, R b i * (∑ a : Fin m, Q a b * E a j) := by
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          ring

/-- The second cross term in `(A+E)ᵀ(A+E)` for an economy QR factorization:
    `EᵀA = (EᵀQ)R`. -/
theorem EconomyQRFactorization.rightCrossGram_eq_stewartProjected
    {m n : ℕ} {A E : Fin m → Fin n → ℝ}
    {Q : Fin m → Fin n → ℝ} {R : Fin n → Fin n → ℝ}
    (hQR : EconomyQRFactorization m n A Q R) :
    rectMatMul (finiteTranspose E) A =
      matMul n (rectMatMul (finiteTranspose E) Q) R := by
  ext i j
  unfold rectMatMul finiteTranspose matMul
  calc
    (∑ a : Fin m, E a i * A a j)
        = ∑ a : Fin m, E a i * (∑ b : Fin n, Q a b * R b j) := by
          apply Finset.sum_congr rfl
          intro a _
          simpa [rectMatMul] using
            congrArg (fun x : ℝ => E a i * x)
              (Eq.symm (hQR.factorization a j))
    _ = ∑ a : Fin m, ∑ b : Fin n, E a i * (Q a b * R b j) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
    _ = ∑ b : Fin n, ∑ a : Fin m, E a i * (Q a b * R b j) := by
          rw [Finset.sum_comm]
    _ = ∑ b : Fin n, (∑ a : Fin m, E a i * Q a b) * R b j := by
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a _
          ring

/-- Expands the perturbed Gram matrix using economy QR data:
    `(A+E)ᵀ(A+E) = RᵀR + Rᵀ(QᵀE) + (EᵀQ)R + EᵀE`. -/
theorem EconomyQRFactorization.rectGram_add_perturbation
    {m n : ℕ} {A E : Fin m → Fin n → ℝ}
    {Q : Fin m → Fin n → ℝ} {R : Fin n → Fin n → ℝ}
    (hQR : EconomyQRFactorization m n A Q R) :
    rectMatMul (finiteTranspose (fun i j => A i j + E i j))
        (fun i j => A i j + E i j) =
      fun i j => matMul n (matTranspose R) R i j +
        stewartQRLinearRhs R Q E i j +
          rectMatMul (finiteTranspose E) E i j := by
  ext i j
  have hAA := congr_fun (congr_fun
    (hQR.rectGram_eq_R) i) j
  have hAE := congr_fun (congr_fun
    (hQR.leftCrossGram_eq_stewartProjected (E := E)) i) j
  have hEA := congr_fun (congr_fun
    (hQR.rightCrossGram_eq_stewartProjected (E := E)) i) j
  unfold stewartQRLinearRhs stewartProjectedPerturbation at hAE ⊢
  unfold rectMatMul finiteTranspose matMul matTranspose at hAA hAE ⊢
  unfold rectMatMul finiteTranspose matMul at hEA
  have hsplit :
      (∑ k : Fin m, (A k i + E k i) * (A k j + E k j)) =
        (∑ k : Fin m, A k i * A k j) +
          (∑ k : Fin m, A k i * E k j) +
            (∑ k : Fin m, E k i * A k j) +
              (∑ k : Fin m, E k i * E k j) := by
    calc
      (∑ k : Fin m, (A k i + E k i) * (A k j + E k j))
          =
            Finset.univ.sum (fun k : Fin m =>
              (A k i * A k j + A k i * E k j) +
                (E k i * A k j + E k i * E k j)) := by
            apply Finset.sum_congr rfl
            intro k _
            ring
      _ = (∑ k : Fin m, A k i * A k j) +
            (∑ k : Fin m, A k i * E k j) +
              (∑ k : Fin m, E k i * A k j) +
                (∑ k : Fin m, E k i * E k j) := by
            simp [Finset.sum_add_distrib]
            ring_nf
  rw [hsplit, hAA, hAE, hEA]
  ring

/-- Stewart's linearized QR operator has symmetric output.

Stewart states `T` as an operator from upper-triangular matrices to symmetric
matrices.  The formula `RᵀF + FᵀR` is symmetric even before imposing the
upper-triangular restriction on `F`. -/
theorem stewartQRLinearMap_symmetric {n : ℕ}
    (R F : Fin n → Fin n → ℝ) :
    IsSymmetricFiniteMatrix (stewartQRLinearMap R F) := by
  intro i j
  unfold stewartQRLinearMap matMul matTranspose
  have hRF :
      (∑ k : Fin n, R k i * F k j) =
        (∑ k : Fin n, F k j * R k i) := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hFR :
      (∑ k : Fin n, F k i * R k j) =
        (∑ k : Fin n, R k j * F k i) := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hRF, hFR]
  ring

/-- Transpose-fixed form of `stewartQRLinearMap_symmetric`. -/
theorem matTranspose_stewartQRLinearMap {n : ℕ}
    (R F : Fin n → Fin n → ℝ) :
    matTranspose (stewartQRLinearMap R F) = stewartQRLinearMap R F := by
  ext i j
  exact (stewartQRLinearMap_symmetric R F j i)

/-- Stewart's natural extension also has symmetric output. -/
theorem stewartQRNaturalExtension_symmetric {n : ℕ}
    (R G : Fin n → Fin n → ℝ) :
    IsSymmetricFiniteMatrix (stewartQRNaturalExtension R G) := by
  simpa [stewartQRNaturalExtension] using
    (stewartQRLinearMap_symmetric R G)

/-- Transpose-fixed form of `stewartQRNaturalExtension_symmetric`. -/
theorem matTranspose_stewartQRNaturalExtension {n : ℕ}
    (R G : Fin n → Fin n → ℝ) :
    matTranspose (stewartQRNaturalExtension R G) =
      stewartQRNaturalExtension R G := by
  simpa [stewartQRNaturalExtension] using
    (matTranspose_stewartQRLinearMap R G)

/-- The displayed Stewart first-correction right-hand side is symmetric. -/
theorem stewartQRLinearRhs_symmetric {m n : ℕ}
    (R : Fin n → Fin n → ℝ) (Q E : Fin m → Fin n → ℝ) :
    IsSymmetricFiniteMatrix (stewartQRLinearRhs R Q E) := by
  rw [stewartQRLinearRhs_eq_naturalExtension R Q E]
  exact stewartQRNaturalExtension_symmetric R (stewartProjectedPerturbation Q E)

/-- Transpose-fixed form of `stewartQRLinearRhs_symmetric`. -/
theorem matTranspose_stewartQRLinearRhs {m n : ℕ}
    (R : Fin n → Fin n → ℝ) (Q E : Fin m → Fin n → ℝ) :
    matTranspose (stewartQRLinearRhs R Q E) =
      stewartQRLinearRhs R Q E := by
  rw [stewartQRLinearRhs_eq_naturalExtension R Q E]
  exact matTranspose_stewartQRNaturalExtension
    R (stewartProjectedPerturbation Q E)

/-- Stewart Theorem 2.1's triangular Frobenius observation, squared form.

If `L` is lower triangular, then each entry of `L` is controlled entrywise by
the symmetrized matrix `L + Lᵀ`, hence `||L||_F^2 <= ||L + Lᵀ||_F^2`. -/
theorem stewartLowerTriangular_frobNormSqRect_le_add_transpose {n : ℕ}
    {L : Fin n → Fin n → ℝ} (hL : QRLowerTriangular n L) :
    frobNormSqRect L ≤
      frobNormSqRect (fun i j => L i j + matTranspose L i j) := by
  unfold frobNormSqRect
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i = j
  · subst j
    unfold matTranspose
    nlinarith [sq_nonneg (L i i)]
  · by_cases hlt : i.val < j.val
    · have hzero : L i j = 0 := hL i j hlt
      rw [hzero]
      unfold matTranspose
      nlinarith [sq_nonneg (L j i)]
    · have hneval : i.val ≠ j.val := by
        intro hv
        exact hij (Fin.ext hv)
      have hle : j.val ≤ i.val := Nat.le_of_not_gt hlt
      have hgt : j.val < i.val := lt_of_le_of_ne hle (Ne.symm hneval)
      have hzero : L j i = 0 := hL j i hgt
      change L i j ^ 2 ≤ (L i j + L j i) ^ 2
      rw [hzero]
      ring_nf
      exact le_rfl

/-- Stewart Theorem 2.1's triangular Frobenius observation with the source
    `sqrt(2)` constant, squared form.

For lower triangular `L`, the symmetrized matrix `L + Lᵀ` contains every
strictly lower-triangular entry twice across transposed positions and every
diagonal entry doubled, giving `2*||L||_F^2 <= ||L+Lᵀ||_F^2`. -/
theorem stewartLowerTriangular_two_mul_frobNormSqRect_le_add_transpose {n : ℕ}
    {L : Fin n → Fin n → ℝ} (hL : QRLowerTriangular n L) :
    2 * frobNormSqRect L ≤
      frobNormSqRect (fun i j => L i j + matTranspose L i j) := by
  have hsum :
      frobNormSqRect L + frobNormSqRect (matTranspose L) ≤
        frobNormSqRect (fun i j => L i j + matTranspose L i j) := by
    unfold frobNormSqRect matTranspose
    calc
      (∑ i : Fin n, ∑ j : Fin n, L i j ^ 2) +
          (∑ i : Fin n, ∑ j : Fin n, L j i ^ 2)
          = ∑ i : Fin n, ∑ j : Fin n, (L i j ^ 2 + L j i ^ 2) := by
              simp [Finset.sum_add_distrib]
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, (L i j + L j i) ^ 2 := by
              apply Finset.sum_le_sum
              intro i _
              apply Finset.sum_le_sum
              intro j _
              by_cases hij : i = j
              · subst j
                nlinarith [sq_nonneg (L i i)]
              · by_cases hlt : i.val < j.val
                · have hzero : L i j = 0 := hL i j hlt
                  rw [hzero]
                  ring_nf
                  exact le_rfl
                · have hneval : i.val ≠ j.val := by
                    intro hv
                    exact hij (Fin.ext hv)
                  have hle : j.val ≤ i.val := Nat.le_of_not_gt hlt
                  have hgt : j.val < i.val := lt_of_le_of_ne hle (Ne.symm hneval)
                  have hzero : L j i = 0 := hL j i hgt
                  rw [hzero]
                  ring_nf
                  exact le_rfl
  have htranspose : frobNormSqRect (matTranspose L) = frobNormSqRect L := by
    unfold frobNormSqRect matTranspose
    rw [Finset.sum_comm]
  have htwo :
      2 * frobNormSqRect L =
        frobNormSqRect L + frobNormSqRect (matTranspose L) := by
    rw [htranspose]
    ring
  rw [htwo]
  exact hsum

/-- Stewart Theorem 2.1's triangular Frobenius observation.

If `L` is lower triangular, then `||L||_F <= ||L + Lᵀ||_F`.  Stewart uses this
in the induction proof for the linear QR perturbation operator. -/
theorem stewartLowerTriangular_frobNormRect_le_add_transpose {n : ℕ}
    {L : Fin n → Fin n → ℝ} (hL : QRLowerTriangular n L) :
    frobNormRect L ≤
      frobNormRect (fun i j => L i j + matTranspose L i j) := by
  unfold frobNormRect
  exact Real.sqrt_le_sqrt
    (stewartLowerTriangular_frobNormSqRect_le_add_transpose hL)

/-- Stewart Theorem 2.1's triangular Frobenius observation with the source
    `sqrt(2)` constant.

This is the exact observation displayed in Stewart's proof:
`sqrt(2) * ||L||_F <= ||L + Lᵀ||_F` for lower triangular `L`. -/
theorem stewartLowerTriangular_sqrt_two_mul_frobNormRect_le_add_transpose
    {n : ℕ} {L : Fin n → Fin n → ℝ} (hL : QRLowerTriangular n L) :
    Real.sqrt (2 : ℝ) * frobNormRect L ≤
      frobNormRect (fun i j => L i j + matTranspose L i j) := by
  unfold frobNormRect
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  exact Real.sqrt_le_sqrt
    (stewartLowerTriangular_two_mul_frobNormSqRect_le_add_transpose hL)

/-- Equality-shaped form of Stewart's lower-triangular Frobenius observation.

This is the source step used after Stewart equation (2.9): once the
symmetrized lower-triangular matrix is identified with a right-hand side `C`,
the norm of the lower-triangular factor is bounded by `||C||_F`. -/
theorem stewartLowerTriangular_frobNormSqRect_le_of_add_transpose_eq {n : ℕ}
    {L C : Fin n → Fin n → ℝ} (hL : QRLowerTriangular n L)
    (hLC : (fun i j => L i j + matTranspose L i j) = C) :
    frobNormSqRect L ≤ frobNormSqRect C := by
  rw [← hLC]
  exact stewartLowerTriangular_frobNormSqRect_le_add_transpose hL

/-- Norm form of the equality-shaped Stewart lower-triangular observation.

This packages the exact inference Stewart uses from a lower-triangular
solution of `L + Lᵀ = C` to the Frobenius bound `||L||_F <= ||C||_F`. -/
theorem stewartLowerTriangular_frobNormRect_le_of_add_transpose_eq {n : ℕ}
    {L C : Fin n → Fin n → ℝ} (hL : QRLowerTriangular n L)
    (hLC : (fun i j => L i j + matTranspose L i j) = C) :
    frobNormRect L ≤ frobNormRect C := by
  rw [← hLC]
  exact stewartLowerTriangular_frobNormRect_le_add_transpose hL

/-- Source-constant form of Stewart's equality-shaped lower-triangular
observation.

This packages the exact inference Stewart uses from `L + Lᵀ = C` to
`sqrt(2) * ||L||_F <= ||C||_F`. -/
theorem stewartLowerTriangular_sqrt_two_mul_frobNormRect_le_of_add_transpose_eq
    {n : ℕ} {L C : Fin n → Fin n → ℝ} (hL : QRLowerTriangular n L)
    (hLC : (fun i j => L i j + matTranspose L i j) = C) :
    Real.sqrt (2 : ℝ) * frobNormRect L ≤ frobNormRect C := by
  rw [← hLC]
  exact stewartLowerTriangular_sqrt_two_mul_frobNormRect_le_add_transpose hL

/-- Stewart equation (2.10)'s lower-triangular/product-norm bound.

If the symmetrized lower-triangular factor is a two-sided product `U*C*V`,
then Stewart's lower-triangular observation plus Frobenius submultiplicativity
give `||L||_F <= ||U||_F ||C||_F ||V||_F`.  In Stewart's proof this is used
with `L = R^{-T}F^T`, `C = B`, and the two inverse triangular factors. -/
theorem stewartLowerTriangular_frobNormRect_le_two_sided_product_of_add_transpose_eq
    {n : ℕ} {L U C V : Fin n → Fin n → ℝ}
    (hL : QRLowerTriangular n L)
    (hLC : (fun i j => L i j + matTranspose L i j) =
      rectMatMul (rectMatMul U C) V) :
    frobNormRect L ≤
      (frobNormRect U * frobNormRect C) * frobNormRect V := by
  have htri :
      frobNormRect L ≤ frobNormRect (rectMatMul (rectMatMul U C) V) :=
    stewartLowerTriangular_frobNormRect_le_of_add_transpose_eq hL hLC
  have hright :
      frobNormRect (rectMatMul (rectMatMul U C) V) ≤
        frobNormRect (rectMatMul U C) * frobNormRect V :=
    frobNormRect_rectMatMul_le (rectMatMul U C) V
  have hleft :
      frobNormRect (rectMatMul U C) ≤
        frobNormRect U * frobNormRect C :=
    frobNormRect_rectMatMul_le U C
  have hprod :
      frobNormRect (rectMatMul U C) * frobNormRect V ≤
        (frobNormRect U * frobNormRect C) * frobNormRect V :=
    mul_le_mul_of_nonneg_right hleft (frobNormRect_nonneg V)
  exact le_trans htri (le_trans hright hprod)

/-- Stewart equation (2.10)'s lower-triangular/product-norm bound with the
source `sqrt(2)` constant.

If `L+Lᵀ=U*C*V`, then Stewart's displayed triangular observation gives
`sqrt(2)||L||_F <= ||U*C*V||_F`, and Frobenius submultiplicativity gives the
product bound. -/
theorem stewartLowerTriangular_sqrt_two_mul_frobNormRect_le_two_sided_product_of_add_transpose_eq
    {n : ℕ} {L U C V : Fin n → Fin n → ℝ}
    (hL : QRLowerTriangular n L)
    (hLC : (fun i j => L i j + matTranspose L i j) =
      rectMatMul (rectMatMul U C) V) :
    Real.sqrt (2 : ℝ) * frobNormRect L ≤
      (frobNormRect U * frobNormRect C) * frobNormRect V := by
  have htri :
      Real.sqrt (2 : ℝ) * frobNormRect L ≤
        frobNormRect (rectMatMul (rectMatMul U C) V) :=
    stewartLowerTriangular_sqrt_two_mul_frobNormRect_le_of_add_transpose_eq hL hLC
  have hright :
      frobNormRect (rectMatMul (rectMatMul U C) V) ≤
        frobNormRect (rectMatMul U C) * frobNormRect V :=
    frobNormRect_rectMatMul_le (rectMatMul U C) V
  have hleft :
      frobNormRect (rectMatMul U C) ≤
        frobNormRect U * frobNormRect C :=
    frobNormRect_rectMatMul_le U C
  have hprod :
      frobNormRect (rectMatMul U C) * frobNormRect V ≤
        (frobNormRect U * frobNormRect C) * frobNormRect V :=
    mul_le_mul_of_nonneg_right hleft (frobNormRect_nonneg V)
  exact le_trans htri (le_trans hright hprod)

/-- Stewart equation (2.10)'s transpose-product specialization.

When the two-sided product has the form `Wᵀ*C*W`, the preceding product bound
and transpose-invariance of the Frobenius norm give the source-shaped estimate
`||L||_F <= ||W||_F^2 ||C||_F`. -/
theorem stewartLowerTriangular_frobNormRect_le_transpose_product_sq_of_add_transpose_eq
    {n : ℕ} {L C W : Fin n → Fin n → ℝ}
    (hL : QRLowerTriangular n L)
    (hLC : (fun i j => L i j + matTranspose L i j) =
      rectMatMul (rectMatMul (finiteTranspose W) C) W) :
    frobNormRect L ≤ frobNormRect W ^ 2 * frobNormRect C := by
  have hbase :
      frobNormRect L ≤
        (frobNormRect (finiteTranspose W) * frobNormRect C) * frobNormRect W :=
    stewartLowerTriangular_frobNormRect_le_two_sided_product_of_add_transpose_eq
      (L := L) (U := finiteTranspose W) (C := C) (V := W) hL hLC
  have htranspose : frobNormRect (finiteTranspose W) = frobNormRect W := by
    unfold frobNormRect frobNormSqRect finiteTranspose
    rw [Finset.sum_comm]
  rw [htranspose] at hbase
  calc
    frobNormRect L ≤
        (frobNormRect W * frobNormRect C) * frobNormRect W := hbase
    _ = frobNormRect W ^ 2 * frobNormRect C := by ring

/-- Stewart equation (2.10)'s transpose-product specialization with the source
    `sqrt(2)` constant.

For `L+Lᵀ=Wᵀ*C*W`, this is the source-faithful local estimate
`sqrt(2)||L||_F <= ||W||_F^2||C||_F`, equivalently
`||L||_F <= (1/sqrt(2))||W||_F^2||C||_F` when divided by `sqrt(2)`. -/
theorem stewartLowerTriangular_sqrt_two_mul_frobNormRect_le_transpose_product_sq_of_add_transpose_eq
    {n : ℕ} {L C W : Fin n → Fin n → ℝ}
    (hL : QRLowerTriangular n L)
    (hLC : (fun i j => L i j + matTranspose L i j) =
      rectMatMul (rectMatMul (finiteTranspose W) C) W) :
    Real.sqrt (2 : ℝ) * frobNormRect L ≤
      frobNormRect W ^ 2 * frobNormRect C := by
  have hbase :
      Real.sqrt (2 : ℝ) * frobNormRect L ≤
        (frobNormRect (finiteTranspose W) * frobNormRect C) * frobNormRect W :=
    stewartLowerTriangular_sqrt_two_mul_frobNormRect_le_two_sided_product_of_add_transpose_eq
      (L := L) (U := finiteTranspose W) (C := C) (V := W) hL hLC
  have htranspose : frobNormRect (finiteTranspose W) = frobNormRect W := by
    unfold frobNormRect frobNormSqRect finiteTranspose
    rw [Finset.sum_comm]
  rw [htranspose] at hbase
  calc
    Real.sqrt (2 : ℝ) * frobNormRect L ≤
        (frobNormRect W * frobNormRect C) * frobNormRect W := hbase
    _ = frobNormRect W ^ 2 * frobNormRect C := by ring

/-- Stewart equation (3.1)'s quadratic right-hand side
    `EᵀE - FᵀF`. -/
noncomputable def stewartQRQuadraticRhs {m n : ℕ}
    (E : Fin m → Fin n → ℝ) (F : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => rectMatMul (finiteTranspose E) E i j -
    matMul n (matTranspose F) F i j

/-- Stewart equation (3.1)'s full right-hand side
    `Rᵀ(QᵀE) + (EᵀQ)R + EᵀE - FᵀF`. -/
noncomputable def stewartQRNonlinearRhs {m n : ℕ}
    (R F : Fin n → Fin n → ℝ) (Q E : Fin m → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => stewartQRLinearRhs R Q E i j +
    stewartQRQuadraticRhs E F i j

/-- Algebraic cancellation step behind Stewart equation (3.1).

If the Gram identity for the perturbed factor is already expanded as
`(R+F)ᵀ(R+F) = RᵀR + Rᵀ(QᵀE) + (EᵀQ)R + EᵀE`, then cancellation of `RᵀR`
and expansion of the left side give
`T F = Rᵀ(QᵀE) + (EᵀQ)R + EᵀE - FᵀF`. -/
theorem stewartQRLinearMap_eq_nonlinearRhs_of_expanded_gram
    {m n : ℕ} {R F : Fin n → Fin n → ℝ}
    {Q E : Fin m → Fin n → ℝ}
    (hgram : ∀ i j : Fin n,
      matMul n (matTranspose (fun a b => R a b + F a b))
          (fun a b => R a b + F a b) i j =
        matMul n (matTranspose R) R i j +
          stewartQRLinearRhs R Q E i j +
            rectMatMul (finiteTranspose E) E i j) :
    stewartQRLinearMap R F =
      stewartQRNonlinearRhs R F Q E := by
  ext i j
  have hg := hgram i j
  unfold stewartQRNonlinearRhs stewartQRQuadraticRhs
  unfold stewartQRLinearMap matMul matTranspose rectMatMul
    finiteTranspose at hg ⊢
  have hsplit :
      (∑ k : Fin n, (R k i + F k i) * (R k j + F k j)) =
        (∑ k : Fin n, R k i * R k j) +
          (∑ k : Fin n, R k i * F k j) +
            (∑ k : Fin n, F k i * R k j) +
              (∑ k : Fin n, F k i * F k j) := by
    calc
      (∑ k : Fin n, (R k i + F k i) * (R k j + F k j))
          =
            Finset.univ.sum (fun k : Fin n =>
              (R k i * R k j + R k i * F k j) +
                (F k i * R k j + F k i * F k j)) := by
            apply Finset.sum_congr rfl
            intro k _
            ring
      _ = (∑ k : Fin n, R k i * R k j) +
            (∑ k : Fin n, R k i * F k j) +
              (∑ k : Fin n, F k i * R k j) +
                (∑ k : Fin n, F k i * F k j) := by
            simp [Finset.sum_add_distrib]
            ring_nf
  rw [hsplit] at hg
  linarith

/-- Stewart equation (3.1) from two economy QR factorizations.

If `A = QR` and `A+E = Qhat (R+F)` are economy QR factorizations, then the
triangular perturbation `F` satisfies Stewart's nonlinear equation
`T F = Rᵀ(QᵀE) + (EᵀQ)R + EᵀE - FᵀF`. -/
theorem stewartQRNonlinearEquation_of_economy_qr_perturbation
    {m n : ℕ} {A E Q Qhat : Fin m → Fin n → ℝ}
    {R F : Fin n → Fin n → ℝ}
    (hQR : EconomyQRFactorization m n A Q R)
    (hPertQR :
      EconomyQRFactorization m n
        (fun i j => A i j + E i j) Qhat
        (fun i j => R i j + F i j)) :
    stewartQRLinearMap R F =
      stewartQRNonlinearRhs R F Q E := by
  apply stewartQRLinearMap_eq_nonlinearRhs_of_expanded_gram
  intro i j
  have hPert := congr_fun (congr_fun
    (hPertQR.rectGram_eq_R) i) j
  have hExpanded := congr_fun (congr_fun
    (hQR.rectGram_add_perturbation (E := E)) i) j
  exact Eq.trans (Eq.symm hPert) hExpanded

/-- The transpose action of an economy `Q` with orthonormal columns is a
Euclidean contraction. -/
theorem EconomyQHasOrthonormalColumns.vecNorm2Sq_rectMatMulVec_finiteTranspose_le
    {m n : ℕ} {Q : Fin m → Fin n → ℝ}
    (hQ : EconomyQHasOrthonormalColumns Q) (z : Fin m → ℝ) :
    vecNorm2Sq (rectMatMulVec (finiteTranspose Q) z) ≤ vecNorm2Sq z := by
  classical
  let q : Fin n → ℝ := rectMatMulVec (finiteTranspose Q) z
  let u : Fin m → ℝ := rectMatMulVec Q q
  have hu_norm : vecNorm2Sq u = vecNorm2Sq q := by
    simpa [u] using hQ.vecNorm2Sq_rectMatMulVec q
  have hinner : (∑ k : Fin m, z k * u k) = vecNorm2Sq q := by
    calc
      (∑ k : Fin m, z k * u k)
          = ∑ k : Fin m, ∑ j : Fin n, z k * (Q k j * q j) := by
              apply Finset.sum_congr rfl
              intro k _
              simp [u, rectMatMulVec, Finset.mul_sum]
      _ = ∑ j : Fin n, ∑ k : Fin m, z k * (Q k j * q j) := by
              rw [Finset.sum_comm]
      _ = ∑ j : Fin n, (∑ k : Fin m, Q k j * z k) * q j := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro k _
              ring
      _ = ∑ j : Fin n, q j * q j := by
              apply Finset.sum_congr rfl
              intro j _
              simp [q, rectMatMulVec, finiteTranspose]
      _ = vecNorm2Sq q := by
              unfold vecNorm2Sq
              apply Finset.sum_congr rfl
              intro j _
              ring
  have hcs := vecInnerProduct_sq_le z u
  have hsq : vecNorm2Sq q ^ 2 ≤ vecNorm2Sq z * vecNorm2Sq q := by
    simpa [hinner, hu_norm] using hcs
  have hq_nonneg : 0 ≤ vecNorm2Sq q := vecNorm2Sq_nonneg q
  by_cases hq_zero : vecNorm2Sq q = 0
  · simpa [q, hq_zero] using vecNorm2Sq_nonneg z
  · have hq_pos : 0 < vecNorm2Sq q := lt_of_le_of_ne hq_nonneg (Ne.symm hq_zero)
    have hdiv := div_le_div_of_nonneg_right hsq (le_of_lt hq_pos)
    have hcancel_left : vecNorm2Sq q ^ 2 / vecNorm2Sq q = vecNorm2Sq q := by
      field_simp [hq_zero]
    have hcancel_right :
        (vecNorm2Sq z * vecNorm2Sq q) / vecNorm2Sq q = vecNorm2Sq z := by
      field_simp [hq_zero]
    simpa [q, hcancel_left, hcancel_right] using hdiv

/-- Norm form of the transpose-action contraction for an economy `Q`. -/
theorem EconomyQHasOrthonormalColumns.vecNorm2_rectMatMulVec_finiteTranspose_le
    {m n : ℕ} {Q : Fin m → Fin n → ℝ}
    (hQ : EconomyQHasOrthonormalColumns Q) (z : Fin m → ℝ) :
    vecNorm2 (rectMatMulVec (finiteTranspose Q) z) ≤ vecNorm2 z := by
  unfold vecNorm2
  exact Real.sqrt_le_sqrt
    (hQ.vecNorm2Sq_rectMatMulVec_finiteTranspose_le z)

/-- Stewart's projected perturbation `G = QᵀE` is no larger than `E` in
Frobenius norm when `Q` has orthonormal columns. -/
theorem EconomyQHasOrthonormalColumns.frobNormSqRect_stewartProjectedPerturbation_le
    {m n : ℕ} {Q E : Fin m → Fin n → ℝ}
    (hQ : EconomyQHasOrthonormalColumns Q) :
    frobNormSqRect (stewartProjectedPerturbation Q E) ≤ frobNormSqRect E := by
  rw [frobNormSqRect_eq_sum_vecNorm2Sq_cols,
    frobNormSqRect_eq_sum_vecNorm2Sq_cols]
  apply Finset.sum_le_sum
  intro j _
  have hcol :=
    hQ.vecNorm2Sq_rectMatMulVec_finiteTranspose_le
      (fun i : Fin m => E i j)
  simpa [stewartProjectedPerturbation, rectMatMul, rectMatMulVec,
    finiteTranspose] using hcol

/-- Frobenius-norm form of the Stewart projected-perturbation contraction. -/
theorem EconomyQHasOrthonormalColumns.frobNormRect_stewartProjectedPerturbation_le
    {m n : ℕ} {Q E : Fin m → Fin n → ℝ}
    (hQ : EconomyQHasOrthonormalColumns Q) :
    frobNormRect (stewartProjectedPerturbation Q E) ≤ frobNormRect E := by
  unfold frobNormRect
  exact Real.sqrt_le_sqrt
    (hQ.frobNormSqRect_stewartProjectedPerturbation_le)

/-- Source-level statement of Stewart Theorem 2.2's linear inverse bound.

This is not yet the proof of Theorem 2.2.  It isolates the exact local
obligation needed next: whenever an upper-triangular `F` solves
`T F = T̂ G`, its Frobenius norm is bounded by `sigma * ||G||_F`. -/
structure StewartQRLinearInverseBound (n : ℕ)
    (R : Fin n → Fin n → ℝ) (sigma : ℝ) : Prop where
  of_natural_extension :
    ∀ {F G : Fin n → Fin n → ℝ},
      QRUpperTriangular n F →
      stewartQRLinearMap R F = stewartQRNaturalExtension R G →
      frobNormRect F ≤ sigma * frobNormRect G

/-- Stewart Theorem 2.2's linear inverse-bound constant
`n(2+sqrt(2))κ(R)`. -/
noncomputable def stewartQRLinearInverseConstant (n : ℕ) (kappa : ℝ) : ℝ :=
  (n : ℝ) * (2 + Real.sqrt 2) * kappa

theorem stewartQRLinearInverseConstant_nonneg (n : ℕ) {kappa : ℝ}
    (hkappa : 0 ≤ kappa) :
    0 ≤ stewartQRLinearInverseConstant n kappa := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hs : 0 ≤ 2 + Real.sqrt 2 := by
    have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    linarith
  unfold stewartQRLinearInverseConstant
  exact mul_nonneg (mul_nonneg hn hs) hkappa

/-- Stewart's linear inverse constant is monotone in the condition quantity. -/
theorem stewartQRLinearInverseConstant_mono_kappa (n : ℕ)
    {kappa₁ kappa₂ : ℝ} (hkappa : kappa₁ ≤ kappa₂) :
    stewartQRLinearInverseConstant n kappa₁ ≤
      stewartQRLinearInverseConstant n kappa₂ := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hs : 0 ≤ 2 + Real.sqrt 2 := by
    have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    linarith
  have hcoef : 0 ≤ (n : ℝ) * (2 + Real.sqrt 2) :=
    mul_nonneg hn hs
  unfold stewartQRLinearInverseConstant
  exact mul_le_mul_of_nonneg_left hkappa hcoef

/-- Stewart's linear inverse constant is monotone in dimension for
nonnegative condition quantities. -/
theorem stewartQRLinearInverseConstant_mono_nat {n m : ℕ}
    (hnm : n ≤ m) {kappa : ℝ} (hkappa : 0 ≤ kappa) :
    stewartQRLinearInverseConstant n kappa ≤
      stewartQRLinearInverseConstant m kappa := by
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hnm
  have hs : 0 ≤ 2 + Real.sqrt 2 := by
    have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    linarith
  have hcoef :
      (n : ℝ) * (2 + Real.sqrt 2) ≤
        (m : ℝ) * (2 + Real.sqrt 2) :=
    mul_le_mul_of_nonneg_right hnmR hs
  unfold stewartQRLinearInverseConstant
  exact mul_le_mul_of_nonneg_right hcoef hkappa

/-- Induction handoff for Stewart's source constant: if an `n`-block condition
quantity is dominated by the full `(n+1)` condition quantity, the corresponding
linear inverse constants are ordered in the direction needed by the recursive
proof. -/
theorem stewartQRLinearInverseConstant_le_succ_of_kappa_le (n : ℕ)
    {kappaTail kappa : ℝ} (hkappaTail : kappaTail ≤ kappa)
    (hkappa : 0 ≤ kappa) :
    stewartQRLinearInverseConstant n kappaTail ≤
      stewartQRLinearInverseConstant (n + 1) kappa := by
  exact le_trans
    (stewartQRLinearInverseConstant_mono_kappa n hkappaTail)
    (stewartQRLinearInverseConstant_mono_nat (Nat.le_succ n) hkappa)

/-- Top-left scalar equation in Stewart Theorem 2.2's induction split.

For an `(n+1) x (n+1)` upper-triangular solve of
`T F = T_hat G`, the `(0,0)` component cancels to `F00 = G00` when
`R00` is nonzero. -/
theorem stewartQRLinearMap_topLeft_eq_of_naturalExtension
    {n : ℕ} {R F G : Fin (n + 1) → Fin (n + 1) → ℝ}
    (hR_upper : QRUpperTriangular (n + 1) R)
    (hF_upper : QRUpperTriangular (n + 1) F)
    (hR00 : R 0 0 ≠ 0)
    (hT : stewartQRLinearMap R F = stewartQRNaturalExtension R G) :
    F 0 0 = G 0 0 := by
  have hRk0 : ∀ k : Fin n, R k.succ 0 = 0 := by
    intro k
    exact hR_upper k.succ 0 (by simp)
  have hFk0 : ∀ k : Fin n, F k.succ 0 = 0 := by
    intro k
    exact hF_upper k.succ 0 (by simp)
  have h00 := congr_fun (congr_fun hT 0) 0
  simp [stewartQRLinearMap, stewartQRNaturalExtension, matMul, matTranspose,
    Fin.sum_univ_succ, hRk0, hFk0] at h00
  have hcoef : (2 : ℝ) * R 0 0 ≠ 0 := by
    exact mul_ne_zero (by norm_num) hR00
  have hdiff : ((2 : ℝ) * R 0 0) * (F 0 0 - G 0 0) = 0 := by
    nlinarith
  have hzero : F 0 0 - G 0 0 = 0 := by
    rcases mul_eq_zero.mp hdiff with hleft | hright
    · exact False.elim (hcoef hleft)
    · exact hright
  exact sub_eq_zero.mp hzero

/-- First-row block equation in Stewart Theorem 2.2's induction split.

After the `(0,0)` component is solved, each top-row entry of an
upper-triangular solution of `T F = T_hat G` is determined by the corresponding
top-row entry of `G` plus the lower-column/top-row coupling term
`sum_k G_{k0} R_{kj} / R00`. -/
theorem stewartQRLinearMap_topRow_eq_of_naturalExtension
    {n : ℕ} {R F G : Fin (n + 1) → Fin (n + 1) → ℝ}
    (hR_upper : QRUpperTriangular (n + 1) R)
    (hF_upper : QRUpperTriangular (n + 1) F)
    (hR00 : R 0 0 ≠ 0)
    (hT : stewartQRLinearMap R F = stewartQRNaturalExtension R G)
    (j : Fin n) :
    F 0 j.succ =
      G 0 j.succ +
        (∑ k : Fin n, G k.succ 0 * R k.succ j.succ) / R 0 0 := by
  have hRk0 : ∀ k : Fin n, R k.succ 0 = 0 := by
    intro k
    exact hR_upper k.succ 0 (by simp)
  have hFk0 : ∀ k : Fin n, F k.succ 0 = 0 := by
    intro k
    exact hF_upper k.succ 0 (by simp)
  have hF00 : F 0 0 = G 0 0 :=
    stewartQRLinearMap_topLeft_eq_of_naturalExtension
      hR_upper hF_upper hR00 hT
  have h0j := congr_fun (congr_fun hT 0) j.succ
  simp [stewartQRLinearMap, stewartQRNaturalExtension, matMul, matTranspose,
    Fin.sum_univ_succ, hRk0, hFk0, hF00] at h0j
  have hmul :
      R 0 0 *
          (F 0 j.succ - G 0 j.succ -
            (∑ k : Fin n, G k.succ 0 * R k.succ j.succ) / R 0 0) = 0 := by
    field_simp [hR00]
    nlinarith
  have hzero :
      F 0 j.succ - G 0 j.succ -
        (∑ k : Fin n, G k.succ 0 * R k.succ j.succ) / R 0 0 = 0 := by
    exact (mul_eq_zero.mp hmul).elim (fun h => False.elim (hR00 h)) id
  linarith

/-- Lower-right block equation in Stewart Theorem 2.2's induction split.

After the first row is solved, the trailing block `F₂₂` solves the same
linearized Stewart equation for the trailing `R₂₂`, but with the corrected
right-hand side `G₂₂ - (G₂₁ / R₀₀) R₁₂`.  This is the source recursion used
after splitting an `(n+1) x (n+1)` upper-triangular solve of
`T F = T_hat G`. -/
theorem stewartQRLinearMap_lowerRight_eq_of_naturalExtension
    {n : ℕ} {R F G : Fin (n + 1) → Fin (n + 1) → ℝ}
    (hR_upper : QRUpperTriangular (n + 1) R)
    (hF_upper : QRUpperTriangular (n + 1) F)
    (hR00 : R 0 0 ≠ 0)
    (hT : stewartQRLinearMap R F = stewartQRNaturalExtension R G) :
    stewartQRLinearMap
        (fun i j : Fin n => R i.succ j.succ)
        (fun i j : Fin n => F i.succ j.succ) =
      stewartQRNaturalExtension
        (fun i j : Fin n => R i.succ j.succ)
        (fun i j : Fin n =>
          G i.succ j.succ - (G i.succ 0 / R 0 0) * R 0 j.succ) := by
  ext i j
  have hFi :
      F 0 i.succ =
        G 0 i.succ +
          (∑ k : Fin n, G k.succ 0 * R k.succ i.succ) / R 0 0 :=
    stewartQRLinearMap_topRow_eq_of_naturalExtension
      hR_upper hF_upper hR00 hT i
  have hFj :
      F 0 j.succ =
        G 0 j.succ +
          (∑ k : Fin n, G k.succ 0 * R k.succ j.succ) / R 0 0 :=
    stewartQRLinearMap_topRow_eq_of_naturalExtension
      hR_upper hF_upper hR00 hT j
  let a : ℝ := R 0 i.succ
  let b : ℝ := R 0 j.succ
  let r0 : ℝ := R 0 0
  let si : ℝ := ∑ k : Fin n, G k.succ 0 * R k.succ i.succ
  let sj : ℝ := ∑ k : Fin n, G k.succ 0 * R k.succ j.succ
  let A : ℝ := ∑ k : Fin n, R k.succ i.succ * F k.succ j.succ
  let B : ℝ := ∑ k : Fin n, F k.succ i.succ * R k.succ j.succ
  let C : ℝ := ∑ k : Fin n, R k.succ i.succ * G k.succ j.succ
  let D : ℝ := ∑ k : Fin n, G k.succ i.succ * R k.succ j.succ
  have hij := congr_fun (congr_fun hT i.succ) j.succ
  simp [stewartQRLinearMap, stewartQRNaturalExtension, matMul, matTranspose,
    Fin.sum_univ_succ, hFi, hFj] at hij
  have hcore : A + B = C + D - a * (sj / r0) - (si / r0) * b := by
    dsimp [a, b, r0, si, sj, A, B, C, D] at *
    nlinarith
  have hleft :
      stewartQRLinearMap
          (fun i j : Fin n => R i.succ j.succ)
          (fun i j : Fin n => F i.succ j.succ) i j =
        A + B := by
    simp [stewartQRLinearMap, matMul, matTranspose, A, B]
  have hright :
      stewartQRNaturalExtension
          (fun i j : Fin n => R i.succ j.succ)
          (fun i j : Fin n =>
            G i.succ j.succ - (G i.succ 0 / R 0 0) * R 0 j.succ) i j =
        C + D - a * (sj / r0) - (si / r0) * b := by
    have hsum1 :
        (∑ x : Fin n,
            R x.succ i.succ *
              (G x.succ j.succ -
                (G x.succ 0 / R 0 0) * R 0 j.succ)) =
          C - (si / r0) * b := by
      dsimp [C, si, r0, b]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      congr 1
      simp_rw [div_eq_mul_inv]
      rw [mul_assoc, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring
    have hsum2 :
        (∑ x : Fin n,
            (G x.succ i.succ -
                (G x.succ 0 / R 0 0) * R 0 i.succ) *
              R x.succ j.succ) =
          D - (sj / r0) * a := by
      dsimp [D, sj, r0, a]
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
      congr 1
      simp_rw [div_eq_mul_inv]
      rw [mul_assoc, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring
    simp [stewartQRNaturalExtension, stewartQRLinearMap, matMul, matTranspose,
      hsum1, hsum2, a, b, r0, si, sj, C, D]
    ring
  rw [hleft, hright]
  exact hcore

/-- Top-left block equation for Stewart's last-column induction split.

Splitting an `(n+1) x (n+1)` upper-triangular solve of
`T F = T_hat G` into an initial `n x n` block and the last column, the
initial block satisfies the same natural-extension equation.  This is the
source-aligned counterpart of Stewart equation (2.6). -/
theorem stewartQRLinearMap_init_eq_of_naturalExtension
    {n : ℕ} {R F G : Fin (n + 1) → Fin (n + 1) → ℝ}
    (hR_upper : QRUpperTriangular (n + 1) R)
    (hF_upper : QRUpperTriangular (n + 1) F)
    (hT : stewartQRLinearMap R F = stewartQRNaturalExtension R G) :
    stewartQRLinearMap
        (fun i j : Fin n => R i.castSucc j.castSucc)
        (fun i j : Fin n => F i.castSucc j.castSucc) =
      stewartQRNaturalExtension
        (fun i j : Fin n => R i.castSucc j.castSucc)
        (fun i j : Fin n => G i.castSucc j.castSucc) := by
  ext i j
  have hRlast_i : R (Fin.last n) i.castSucc = 0 := by
    exact hR_upper (Fin.last n) i.castSucc (by simp)
  have hRlast_j : R (Fin.last n) j.castSucc = 0 := by
    exact hR_upper (Fin.last n) j.castSucc (by simp)
  have hFlast_i : F (Fin.last n) i.castSucc = 0 := by
    exact hF_upper (Fin.last n) i.castSucc (by simp)
  have hFlast_j : F (Fin.last n) j.castSucc = 0 := by
    exact hF_upper (Fin.last n) j.castSucc (by simp)
  have hij := congr_fun (congr_fun hT i.castSucc) j.castSucc
  simp [stewartQRLinearMap, stewartQRNaturalExtension, matMul, matTranspose,
    Fin.sum_univ_castSucc, hRlast_i, hRlast_j, hFlast_i, hFlast_j] at hij
  simpa [stewartQRLinearMap, stewartQRNaturalExtension, matMul, matTranspose]
    using hij

/-- Initial-block residual bound for Stewart's last-column induction route.

If the already-recursive initial block has inverse-bound constant `sigma`,
then the initial-block difference `G11-F11` is bounded by
`(1+sigma)||G||_F`.  This supplies the `alpha` hypothesis consumed by the
last-column residual solve wrappers. -/
theorem stewartQRInitialBlockResidual_frobNormRect_le_full
    {n : ℕ} {R F G : Fin (n + 1) → Fin (n + 1) → ℝ} {sigma : ℝ}
    (hTail :
      StewartQRLinearInverseBound n
        (fun i j : Fin n => R i.castSucc j.castSucc) sigma)
    (hsigma : 0 ≤ sigma)
    (hR_upper : QRUpperTriangular (n + 1) R)
    (hF_upper : QRUpperTriangular (n + 1) F)
    (hT : stewartQRLinearMap R F = stewartQRNaturalExtension R G) :
    frobNormRect
        (fun i j : Fin n => G i.castSucc j.castSucc - F i.castSucc j.castSucc) ≤
      (1 + sigma) * frobNormRect G := by
  let F11 : Fin n → Fin n → ℝ := fun i j => F i.castSucc j.castSucc
  let G11 : Fin n → Fin n → ℝ := fun i j => G i.castSucc j.castSucc
  have hF_init_upper : QRUpperTriangular n F11 := by
    intro i j hji
    exact hF_upper i.castSucc j.castSucc hji
  have hInitEq :
      stewartQRLinearMap
          (fun i j : Fin n => R i.castSucc j.castSucc) F11 =
        stewartQRNaturalExtension
          (fun i j : Fin n => R i.castSucc j.castSucc) G11 := by
    simpa [F11, G11] using
      stewartQRLinearMap_init_eq_of_naturalExtension
        hR_upper hF_upper hT
  have hsub :
      frobNormRect (fun i j : Fin n => G11 i j - F11 i j) ≤
        frobNormRect G11 + frobNormRect F11 := by
    simpa [sub_eq_add_neg, add_comm] using frobNormRect_sub_le G11 F11
  have hF11 : frobNormRect F11 ≤ sigma * frobNormRect G11 :=
    hTail.of_natural_extension hF_init_upper hInitEq
  have hG11 : frobNormRect G11 ≤ frobNormRect G := by
    simpa [G11] using frobNormRect_init_le G
  have hF11_full : frobNormRect F11 ≤ sigma * frobNormRect G := by
    exact le_trans hF11 (mul_le_mul_of_nonneg_left hG11 hsigma)
  calc
    frobNormRect
        (fun i j : Fin n => G i.castSucc j.castSucc - F i.castSucc j.castSucc)
        = frobNormRect (fun i j : Fin n => G11 i j - F11 i j) := by rfl
    _ ≤ frobNormRect G11 + frobNormRect F11 := hsub
    _ ≤ frobNormRect G + sigma * frobNormRect G :=
        add_le_add hG11 hF11_full
    _ = (1 + sigma) * frobNormRect G := by ring

/-- Last-column vector equation for Stewart's last-column induction split.

This is the source-aligned counterpart of Stewart equation (2.7): after the
initial block is separated, the last-column unknown satisfies a vector equation
with the initial block, the last column of `R`, and the last row of `G`. -/
theorem stewartQRLinearMap_lastColumn_eq_of_naturalExtension
    {n : ℕ} {R F G : Fin (n + 1) → Fin (n + 1) → ℝ}
    (hR_upper : QRUpperTriangular (n + 1) R)
    (hF_upper : QRUpperTriangular (n + 1) F)
    (hT : stewartQRLinearMap R F = stewartQRNaturalExtension R G)
    (i : Fin n) :
    (∑ k : Fin n, R k.castSucc i.castSucc * F k.castSucc (Fin.last n)) +
        (∑ k : Fin n, F k.castSucc i.castSucc * R k.castSucc (Fin.last n)) =
      (∑ k : Fin n, R k.castSucc i.castSucc * G k.castSucc (Fin.last n)) +
        (∑ k : Fin n, G k.castSucc i.castSucc * R k.castSucc (Fin.last n)) +
        G (Fin.last n) i.castSucc * R (Fin.last n) (Fin.last n) := by
  have hRlast_i : R (Fin.last n) i.castSucc = 0 := by
    exact hR_upper (Fin.last n) i.castSucc (by simp)
  have hFlast_i : F (Fin.last n) i.castSucc = 0 := by
    exact hF_upper (Fin.last n) i.castSucc (by simp)
  have hi := congr_fun (congr_fun hT i.castSucc) (Fin.last n)
  simp [stewartQRLinearMap, stewartQRNaturalExtension, matMul, matTranspose,
    Fin.sum_univ_castSucc, hRlast_i, hFlast_i] at hi
  simpa [add_assoc] using hi

/-- Bottom-right scalar equation for Stewart's last-column induction split.

This is the source-aligned counterpart of Stewart equation (2.8): the final
diagonal component is determined by the last column of `R`, the last column of
`F`, and the corresponding natural-extension data. -/
theorem stewartQRLinearMap_lastLast_eq_of_naturalExtension
    {n : ℕ} {R F G : Fin (n + 1) → Fin (n + 1) → ℝ}
    (hT : stewartQRLinearMap R F = stewartQRNaturalExtension R G) :
    (2 : ℝ) *
        ((∑ k : Fin n, R k.castSucc (Fin.last n) * F k.castSucc (Fin.last n)) +
          R (Fin.last n) (Fin.last n) * F (Fin.last n) (Fin.last n)) =
      (2 : ℝ) *
        ((∑ k : Fin n, R k.castSucc (Fin.last n) * G k.castSucc (Fin.last n)) +
          R (Fin.last n) (Fin.last n) * G (Fin.last n) (Fin.last n)) := by
  have hll := congr_fun (congr_fun hT (Fin.last n)) (Fin.last n)
  simp [stewartQRLinearMap, stewartQRNaturalExtension, matMul, matTranspose,
    Fin.sum_univ_castSucc] at hll
  have hsumF :
      (∑ k : Fin n, F k.castSucc (Fin.last n) * R k.castSucc (Fin.last n)) =
        ∑ k : Fin n, R k.castSucc (Fin.last n) * F k.castSucc (Fin.last n) := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hsumG :
      (∑ k : Fin n, G k.castSucc (Fin.last n) * R k.castSucc (Fin.last n)) =
        ∑ k : Fin n, R k.castSucc (Fin.last n) * G k.castSucc (Fin.last n) := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsumF, hsumG] at hll
  ring_nf at hll ⊢
  exact hll

/-- Last-column residual equation for Stewart's last-column induction split.

This rewrites Stewart equation (2.7) into the form needed for the augmentation
norm estimate: the difference between the unknown last column and the
natural-extension last column is driven by the already-solved initial block
difference and the last row of the natural-extension data. -/
theorem stewartQRLinearMap_lastColumn_residual_eq_of_naturalExtension
    {n : ℕ} {R F G : Fin (n + 1) → Fin (n + 1) → ℝ}
    (hR_upper : QRUpperTriangular (n + 1) R)
    (hF_upper : QRUpperTriangular (n + 1) F)
    (hT : stewartQRLinearMap R F = stewartQRNaturalExtension R G)
    (i : Fin n) :
    (∑ k : Fin n, R k.castSucc i.castSucc *
        (F k.castSucc (Fin.last n) - G k.castSucc (Fin.last n))) =
      (∑ k : Fin n, (G k.castSucc i.castSucc - F k.castSucc i.castSucc) *
        R k.castSucc (Fin.last n)) +
        G (Fin.last n) i.castSucc * R (Fin.last n) (Fin.last n) := by
  let A : ℝ := ∑ k : Fin n,
    R k.castSucc i.castSucc * F k.castSucc (Fin.last n)
  let B : ℝ := ∑ k : Fin n,
    F k.castSucc i.castSucc * R k.castSucc (Fin.last n)
  let C : ℝ := ∑ k : Fin n,
    R k.castSucc i.castSucc * G k.castSucc (Fin.last n)
  let D : ℝ := ∑ k : Fin n,
    G k.castSucc i.castSucc * R k.castSucc (Fin.last n)
  let e : ℝ := G (Fin.last n) i.castSucc * R (Fin.last n) (Fin.last n)
  have hcol :
      A + B = C + D + e := by
    dsimp [A, B, C, D, e]
    exact stewartQRLinearMap_lastColumn_eq_of_naturalExtension
      hR_upper hF_upper hT i
  have hleft :
      (∑ k : Fin n, R k.castSucc i.castSucc *
          (F k.castSucc (Fin.last n) - G k.castSucc (Fin.last n))) =
        A - C := by
    dsimp [A, C]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
  have hright :
      (∑ k : Fin n, (G k.castSucc i.castSucc - F k.castSucc i.castSucc) *
          R k.castSucc (Fin.last n)) =
        D - B := by
    dsimp [B, D]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
  rw [hleft, hright]
  nlinarith

/-- Bottom-right residual equation for Stewart's last-column induction split.

This is equation (2.8) after moving the natural-extension contribution to the
left.  It is the scalar companion to
`stewartQRLinearMap_lastColumn_residual_eq_of_naturalExtension` for solving the
augmented last column. -/
theorem stewartQRLinearMap_lastLast_residual_eq_of_naturalExtension
    {n : ℕ} {R F G : Fin (n + 1) → Fin (n + 1) → ℝ}
    (hT : stewartQRLinearMap R F = stewartQRNaturalExtension R G) :
    (∑ k : Fin n, R k.castSucc (Fin.last n) *
        (F k.castSucc (Fin.last n) - G k.castSucc (Fin.last n))) +
      R (Fin.last n) (Fin.last n) *
        (F (Fin.last n) (Fin.last n) - G (Fin.last n) (Fin.last n)) = 0 := by
  let A : ℝ := ∑ k : Fin n,
    R k.castSucc (Fin.last n) * F k.castSucc (Fin.last n)
  let B : ℝ := ∑ k : Fin n,
    R k.castSucc (Fin.last n) * G k.castSucc (Fin.last n)
  let pF : ℝ := R (Fin.last n) (Fin.last n) *
    F (Fin.last n) (Fin.last n)
  let pG : ℝ := R (Fin.last n) (Fin.last n) *
    G (Fin.last n) (Fin.last n)
  have hll :
      (2 : ℝ) * (A + pF) = (2 : ℝ) * (B + pG) := by
    dsimp [A, B, pF, pG]
    exact stewartQRLinearMap_lastLast_eq_of_naturalExtension hT
  have hleft :
      (∑ k : Fin n, R k.castSucc (Fin.last n) *
          (F k.castSucc (Fin.last n) - G k.castSucc (Fin.last n))) =
        A - B := by
    dsimp [A, B]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
  rw [hleft]
  dsimp [pF, pG] at hll
  nlinarith

/-- Recursive lower-right norm handoff for Stewart Theorem 2.2's induction.

Once the trailing `n x n` inverse-bound hypothesis is available, the
lower-right block equation gives the corresponding Frobenius bound for `F₂₂`
with the corrected trailing right-hand side. -/
theorem StewartQRLinearInverseBound.lowerRight_le
    {n : ℕ} {R F G : Fin (n + 1) → Fin (n + 1) → ℝ} {sigma : ℝ}
    (hTail :
      StewartQRLinearInverseBound n
        (fun i j : Fin n => R i.succ j.succ) sigma)
    (hR_upper : QRUpperTriangular (n + 1) R)
    (hF_upper : QRUpperTriangular (n + 1) F)
    (hR00 : R 0 0 ≠ 0)
    (hT : stewartQRLinearMap R F = stewartQRNaturalExtension R G) :
    frobNormRect (fun i j : Fin n => F i.succ j.succ) ≤
      sigma *
        frobNormRect
          (fun i j : Fin n =>
            G i.succ j.succ - (G i.succ 0 / R 0 0) * R 0 j.succ) := by
  have hF_tail_upper :
      QRUpperTriangular n (fun i j : Fin n => F i.succ j.succ) := by
    intro i j hji
    exact hF_upper i.succ j.succ (Nat.succ_lt_succ hji)
  exact hTail.of_natural_extension hF_tail_upper
    (stewartQRLinearMap_lowerRight_eq_of_naturalExtension
      hR_upper hF_upper hR00 hT)

/-- Corrected lower-right right-hand side bound in Stewart Theorem 2.2's
    induction split.

The trailing equation uses `G₂₂ - (G₂₁/R₁₁) R₁₂`.  This lemma packages the
triangle inequality together with the exact Frobenius norm of that outer-product
correction term. -/
theorem stewartQRLowerRightCorrectedRhs_frobNormRect_le
    {n : ℕ} {R G : Fin (n + 1) → Fin (n + 1) → ℝ} :
    frobNormRect
        (fun i j : Fin n =>
          G i.succ j.succ - (G i.succ 0 / R 0 0) * R 0 j.succ) ≤
      frobNormRect (fun i j : Fin n => G i.succ j.succ) +
        vecNorm2 (fun i : Fin n => G i.succ 0 / R 0 0) *
          vecNorm2 (fun j : Fin n => R 0 j.succ) := by
  have hsub :=
    frobNormRect_sub_le
      (fun i j : Fin n => G i.succ j.succ)
      (fun i j : Fin n => (G i.succ 0 / R 0 0) * R 0 j.succ)
  simpa [frobNormRect_outerProduct] using hsub

/-- Corrected lower-right right-hand side bound in terms of the full
    right-hand side `G` and the visible pivot-row multiplier.

This is the next source-constant induction foothold after the exact
outer-product correction bound: both `G₂₂` and `G₂₁` are controlled by the
full Frobenius norm of `G`. -/
theorem stewartQRLowerRightCorrectedRhs_frobNormRect_le_full
    {n : ℕ} {R G : Fin (n + 1) → Fin (n + 1) → ℝ} :
    frobNormRect
        (fun i j : Fin n =>
          G i.succ j.succ - (G i.succ 0 / R 0 0) * R 0 j.succ) ≤
      (1 + |1 / R 0 0| * vecNorm2 (fun j : Fin n => R 0 j.succ)) *
        frobNormRect G := by
  have hbase :=
    stewartQRLowerRightCorrectedRhs_frobNormRect_le (R := R) (G := G)
  have hG22 :
      frobNormRect (fun i j : Fin n => G i.succ j.succ) ≤
        frobNormRect G :=
    frobNormRect_tail_le G
  have hdiv :
      vecNorm2 (fun i : Fin n => G i.succ 0 / R 0 0) =
        |1 / R 0 0| * vecNorm2 (fun i : Fin n => G i.succ 0) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (vecNorm2_smul (1 / R 0 0) (fun i : Fin n => G i.succ 0))
  have hG21 :
      vecNorm2 (fun i : Fin n => G i.succ 0 / R 0 0) ≤
        |1 / R 0 0| * frobNormRect G := by
    rw [hdiv]
    exact mul_le_mul_of_nonneg_left
      (vecNorm2_firstColumnTail_le_frobNormRect G)
      (abs_nonneg (1 / R 0 0))
  have hcorr :
      vecNorm2 (fun i : Fin n => G i.succ 0 / R 0 0) *
          vecNorm2 (fun j : Fin n => R 0 j.succ) ≤
        (|1 / R 0 0| * frobNormRect G) *
          vecNorm2 (fun j : Fin n => R 0 j.succ) :=
    mul_le_mul_of_nonneg_right hG21 (vecNorm2_nonneg _)
  calc
    frobNormRect
        (fun i j : Fin n =>
          G i.succ j.succ - (G i.succ 0 / R 0 0) * R 0 j.succ)
        ≤ frobNormRect (fun i j : Fin n => G i.succ j.succ) +
            vecNorm2 (fun i : Fin n => G i.succ 0 / R 0 0) *
              vecNorm2 (fun j : Fin n => R 0 j.succ) := hbase
    _ ≤ frobNormRect G +
          (|1 / R 0 0| * frobNormRect G) *
            vecNorm2 (fun j : Fin n => R 0 j.succ) :=
        add_le_add hG22 hcorr
    _ = (1 + |1 / R 0 0| * vecNorm2 (fun j : Fin n => R 0 j.succ)) *
          frobNormRect G := by
        ring

/-- Frobenius block budget for the unknown upper-triangular correction `F`
    in Stewart Theorem 2.2's induction.

The full norm of `F` is controlled by its leading scalar, top-row tail, and
lower-right trailing block.  This is the matrix-side split needed before the
source-constant recursive estimate bounds those three pieces. -/
theorem stewartQRUpperTriangular_frobNormRect_le_blocks
    {n : ℕ} {F : Fin (n + 1) → Fin (n + 1) → ℝ}
    (hF_upper : QRUpperTriangular (n + 1) F) :
    frobNormRect F ≤
      |F 0 0| + vecNorm2 (fun j : Fin n => F 0 j.succ) +
        frobNormRect (fun i j : Fin n => F i.succ j.succ) := by
  exact frobNormRect_block_firstColumnTail_zero_le F (fun i =>
    hF_upper i.succ 0 (by simp))

/-- Frobenius block budget for an upper-triangular matrix split by the final
    row and column.

This is the block assembly counterpart to Stewart's last-column induction
route: an upper-triangular matrix has zero final-row initial segment, so its
Frobenius norm is controlled by the initial block, the final-column initial
vector, and the final diagonal entry. -/
theorem stewartQRUpperTriangular_frobNormRect_le_lastColumn_blocks
    {n : ℕ} {F : Fin (n + 1) → Fin (n + 1) → ℝ}
    (hF_upper : QRUpperTriangular (n + 1) F) :
    frobNormRect F ≤
      frobNormRect (fun i j : Fin n => F i.castSucc j.castSucc) +
        vecNorm2 (fun i : Fin n => F i.castSucc (Fin.last n)) +
        |F (Fin.last n) (Fin.last n)| := by
  exact frobNormRect_block_lastRowInit_zero_le F (fun j =>
    hF_upper (Fin.last n) j.castSucc (by simp))

/-- Stewart Theorem 2.2's scalar base case.

For `n = 1`, a nonzero triangular factor makes `T F = T̂ G` reduce to
`2 * R 0 0 * F 0 0 = 2 * R 0 0 * G 0 0`, so `F = G` and the inverse-bound
constant `1` suffices. -/
theorem StewartQRLinearInverseBound.one
    {R : Fin 1 → Fin 1 → ℝ} (hR : R 0 0 ≠ 0) :
    StewartQRLinearInverseBound 1 R 1 := by
  refine ⟨?_⟩
  intro F G _hF_upper hT
  have hFG : F = G := by
    ext i j
    fin_cases i
    fin_cases j
    have h00 := congr_fun (congr_fun hT 0) 0
    unfold stewartQRLinearMap stewartQRNaturalExtension
      matMul matTranspose at h00
    simp [stewartQRLinearMap, matMul, matTranspose] at h00
    have hcoef : (2 : ℝ) * R 0 0 ≠ 0 := by
      exact mul_ne_zero (by norm_num) hR
    have hdiff : ((2 : ℝ) * R 0 0) * (F 0 0 - G 0 0) = 0 := by
      nlinarith
    have hzero : F 0 0 - G 0 0 = 0 := by
      rcases mul_eq_zero.mp hdiff with hleft | hright
      · exact False.elim (hcoef hleft)
      · exact hright
    have hfg : F 0 0 = G 0 0 := sub_eq_zero.mp hzero
    simpa using hfg
  rw [hFG]
  simp

/-- First nontrivial `2 x 2` instance of Stewart Theorem 2.2's inverse bound.

This closes the component-equation algebra for `n = 2`.  The displayed
constant is an explicit entry-ratio bound, not Stewart's sharp general source
constant; the general `n > 1` induction theorem remains the open target. -/
theorem StewartQRLinearInverseBound.two_entry_bound
    {R : Fin 2 → Fin 2 → ℝ}
    (hR_upper : QRUpperTriangular 2 R)
    (hR00 : R 0 0 ≠ 0) (hR11 : R 1 1 ≠ 0) :
    StewartQRLinearInverseBound 2 R
      (Real.sqrt ((2 : ℝ) * (2 : ℝ)) *
        (3 + |R 1 1 / R 0 0| + |R 0 1 / R 0 0|)) := by
  refine ⟨?_⟩
  intro F G hF_upper hT
  have hR10 : R 1 0 = 0 := by
    exact hR_upper 1 0 (by norm_num)
  have hF10 : F 1 0 = 0 := by
    exact hF_upper 1 0 (by norm_num)
  have hG_entry : ∀ i j : Fin 2, |G i j| ≤ frobNormRect G := by
    intro i j
    have hrow :
        G i j ^ 2 ≤ ∑ c : Fin 2, G i c ^ 2 :=
      Finset.single_le_sum (fun c _ => sq_nonneg (G i c)) (Finset.mem_univ j)
    have hsq :
        G i j ^ 2 ≤ frobNormSqRect G := by
      unfold frobNormSqRect
      exact le_trans hrow
        (Finset.single_le_sum
          (fun r _ => Finset.sum_nonneg (fun c _ => sq_nonneg (G r c)))
          (Finset.mem_univ i))
    have hsqrt := Real.sqrt_le_sqrt hsq
    simpa [frobNormRect, Real.sqrt_sq_eq_abs] using hsqrt
  have hF00 : F 0 0 = G 0 0 := by
    have h00 := congr_fun (congr_fun hT 0) 0
    unfold stewartQRLinearMap stewartQRNaturalExtension
      matMul matTranspose at h00
    simp [stewartQRLinearMap, matMul, matTranspose, Fin.sum_univ_two,
      hR10, hF10] at h00
    have hcoef : (2 : ℝ) * R 0 0 ≠ 0 := by
      exact mul_ne_zero (by norm_num) hR00
    have hdiff : ((2 : ℝ) * R 0 0) * (F 0 0 - G 0 0) = 0 := by
      nlinarith
    have hzero : F 0 0 - G 0 0 = 0 := by
      rcases mul_eq_zero.mp hdiff with hleft | hright
      · exact False.elim (hcoef hleft)
      · exact hright
    exact sub_eq_zero.mp hzero
  have hF01 : F 0 1 = G 0 1 + (R 1 1 / R 0 0) * G 1 0 := by
    have h01 := congr_fun (congr_fun hT 0) 1
    unfold stewartQRLinearMap stewartQRNaturalExtension
      matMul matTranspose at h01
    simp [stewartQRLinearMap, matMul, matTranspose, Fin.sum_univ_two,
      hR10, hF10, hF00] at h01
    have hmul :
        R 0 0 *
            (F 0 1 - G 0 1 - (R 1 1 / R 0 0) * G 1 0) = 0 := by
      field_simp [hR00]
      nlinarith
    have hzero :
        F 0 1 - G 0 1 - (R 1 1 / R 0 0) * G 1 0 = 0 := by
      exact (mul_eq_zero.mp hmul).elim (fun h => False.elim (hR00 h)) id
    linarith
  have hF11 : F 1 1 = G 1 1 - (R 0 1 / R 0 0) * G 1 0 := by
    have h11 := congr_fun (congr_fun hT 1) 1
    unfold stewartQRLinearMap stewartQRNaturalExtension
      matMul matTranspose at h11
    simp [stewartQRLinearMap, matMul, matTranspose, Fin.sum_univ_two,
      hF01] at h11
    ring_nf at h11
    have hmul :
        ((2 : ℝ) * R 1 1) *
            (F 1 1 - G 1 1 + (R 0 1 / R 0 0) * G 1 0) = 0 := by
      ring_nf
      nlinarith
    have hcoef : (2 : ℝ) * R 1 1 ≠ 0 := by
      exact mul_ne_zero (by norm_num) hR11
    have hzero :
        F 1 1 - G 1 1 + (R 0 1 / R 0 0) * G 1 0 = 0 := by
      exact (mul_eq_zero.mp hmul).elim (fun h => False.elim (hcoef h)) id
    linarith
  let K : ℝ := 3 + |R 1 1 / R 0 0| + |R 0 1 / R 0 0|
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hK_ge_one : 1 ≤ K := by
    dsimp [K]
    have h₁ : (0 : ℝ) ≤ |R 1 1 / R 0 0| := abs_nonneg _
    have h₂ : (0 : ℝ) ≤ |R 0 1 / R 0 0| := abs_nonneg _
    linarith
  have hB_nonneg : 0 ≤ K * frobNormRect G :=
    mul_nonneg hK_nonneg (frobNormRect_nonneg G)
  have hentry : ∀ i j : Fin 2, |F i j| ≤ K * frobNormRect G := by
    intro i j
    fin_cases i <;> fin_cases j
    · change |F 0 0| ≤ K * frobNormRect G
      rw [hF00]
      exact le_trans (hG_entry 0 0)
        (by
          have hnorm := frobNormRect_nonneg G
          nlinarith)
    · change |F 0 1| ≤ K * frobNormRect G
      rw [hF01]
      calc
        |G 0 1 + (R 1 1 / R 0 0) * G 1 0|
            ≤ |G 0 1| + |(R 1 1 / R 0 0) * G 1 0| :=
              abs_add_le _ _
        _ = |G 0 1| + |R 1 1 / R 0 0| * |G 1 0| := by
            rw [abs_mul]
        _ ≤ frobNormRect G + |R 1 1 / R 0 0| * frobNormRect G := by
            exact add_le_add (hG_entry 0 1)
              (mul_le_mul_of_nonneg_left (hG_entry 1 0) (abs_nonneg _))
        _ ≤ K * frobNormRect G := by
            have hnorm := frobNormRect_nonneg G
            have hβ : 0 ≤ |R 0 1 / R 0 0| := abs_nonneg _
            dsimp [K]
            nlinarith
    · change |F 1 0| ≤ K * frobNormRect G
      rw [hF10]
      simpa using hB_nonneg
    · change |F 1 1| ≤ K * frobNormRect G
      rw [hF11]
      calc
        |G 1 1 - (R 0 1 / R 0 0) * G 1 0|
            ≤ |G 1 1| + |(R 0 1 / R 0 0) * G 1 0| := by
              simpa [sub_eq_add_neg, abs_neg] using
                abs_add_le (G 1 1) (-(R 0 1 / R 0 0) * G 1 0)
        _ = |G 1 1| + |R 0 1 / R 0 0| * |G 1 0| := by
            rw [abs_mul]
        _ ≤ frobNormRect G + |R 0 1 / R 0 0| * frobNormRect G := by
            exact add_le_add (hG_entry 1 1)
              (mul_le_mul_of_nonneg_left (hG_entry 1 0) (abs_nonneg _))
        _ ≤ K * frobNormRect G := by
            have hnorm := frobNormRect_nonneg G
            have hα : 0 ≤ |R 1 1 / R 0 0| := abs_nonneg _
            dsimp [K]
            nlinarith
  have hbound :=
    frobNormRect_le_sqrt_mul_nat_of_entry_abs_le F hB_nonneg hentry
  simpa [K, mul_assoc] using hbound

/-- Stewart Theorem 2.2 gives the first-correction bound used in Theorem 3.1.

If `F1` solves the linearized equation
`T F1 = Rᵀ(QᵀE)+(EᵀQ)R`, then Theorem 2.2 and
`||QᵀE||_F <= ||E||_F` imply `||F1||_F <= sigma ||E||_F`. -/
theorem StewartQRLinearInverseBound.firstCorrection_le
    {m n : ℕ} {R F1 : Fin n → Fin n → ℝ}
    {Q E : Fin m → Fin n → ℝ} {sigma : ℝ}
    (hT : StewartQRLinearInverseBound n R sigma)
    (hsigma : 0 ≤ sigma)
    (hF1_upper : QRUpperTriangular n F1)
    (hF1 :
      stewartQRLinearMap R F1 = stewartQRLinearRhs R Q E)
    (hQ : EconomyQHasOrthonormalColumns Q) :
    frobNormRect F1 ≤ sigma * frobNormRect E := by
  have hF1_nat :
      stewartQRLinearMap R F1 =
        stewartQRNaturalExtension R (stewartProjectedPerturbation Q E) := by
    rw [hF1, stewartQRLinearRhs_eq_naturalExtension]
  have hlin :
      frobNormRect F1 ≤
        sigma * frobNormRect (stewartProjectedPerturbation Q E) :=
    hT.of_natural_extension hF1_upper hF1_nat
  have hproj :
      frobNormRect (stewartProjectedPerturbation Q E) ≤ frobNormRect E :=
    hQ.frobNormRect_stewartProjectedPerturbation_le
  exact le_trans hlin (mul_le_mul_of_nonneg_left hproj hsigma)

/-- Relative Frobenius error surface for a rectangular `R` factor.

    The denominator is kept on the right-hand side as
    `eta * ||R||_F`, so downstream theorems can add the exact positivity or
    nonzero assumptions appropriate to their chosen QR convention. -/
def RectangularQRFactorRelativeErrorLe (m n : ℕ)
    (R R_hat : Fin m → Fin n → ℝ) (eta : ℝ) : Prop :=
  frobNormRect (fun i j => R_hat i j - R i j) ≤ eta * frobNormRect R

/-- Relative Frobenius error surface for the economy-size square `R` factor.

    Higham equation (18.27) is a statement about the `n x n` `R` factor in
    an economy-size QR factorization of an `m x n`, full-column-rank matrix.
    This square surface is therefore the source-faithful endpoint for the
    Chapter 1 QR perturbation handoff; the older rectangular surface above is
    retained for compatibility with full stored `m x n` QR arrays. -/
def EconomyQRFactorRelativeErrorLe (n : ℕ)
    (R R_hat : Fin n → Fin n → ℝ) (eta : ℝ) : Prop :=
  frobNormRect (fun i j => R_hat i j - R i j) ≤ eta * frobNormRect R

/-- Monotonicity of the economy-size `R` relative-error surface in its radius.

    This small adapter is useful when a perturbation theorem is first stated in
    Stewart's `κ_F(A)` notation and then converted to the Chapter 1
    `κ_2(A)`-phrasing by a separate condition-number comparison. -/
theorem EconomyQRFactorRelativeErrorLe.mono {n : ℕ}
    {R R_hat : Fin n → Fin n → ℝ} {eta eta' : ℝ}
    (h : EconomyQRFactorRelativeErrorLe n R R_hat eta)
    (heta : eta ≤ eta') :
    EconomyQRFactorRelativeErrorLe n R R_hat eta' := by
  exact le_trans h
    (mul_le_mul_of_nonneg_right heta (frobNormRect_nonneg R))

/-- The Euclidean norm of a coordinate basis vector is one. -/
lemma vecNorm2_finiteBasisVec {n : ℕ} (j : Fin n) :
    vecNorm2 (finiteBasisVec j : Fin n → ℝ) = 1 := by
  unfold vecNorm2 vecNorm2Sq finiteBasisVec
  have hsum :
      (∑ i : Fin n, (if i = j then (1 : ℝ) else 0) ^ 2) = 1 := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ j))
  rw [hsum, Real.sqrt_one]

/-- A rectangular operator-2 bound controls the rectangular Frobenius norm by
    the square root of the number of columns.

    This is the finite-dimensional norm comparison used by the Chapter 1 QR
    bottleneck once a source-faithful interpretation of Stewart's
    `kappa_F(A)` is supplied. -/
theorem frobNormRect_le_sqrt_cols_mul_of_rectOpNorm2Le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) {A2 : ℝ}
    (hA2_nonneg : 0 ≤ A2) (hA2 : rectOpNorm2Le A A2) :
    frobNormRect A ≤ Real.sqrt (n : ℝ) * A2 := by
  classical
  have hcol : ∀ j : Fin n, vecNorm2 (fun i : Fin m => A i j) ≤ A2 := by
    intro j
    have hselect :
        rectMatMulVec A (finiteBasisVec j : Fin n → ℝ) =
          fun i : Fin m => A i j := by
      ext i
      unfold rectMatMulVec finiteBasisVec
      simp [Finset.mem_univ]
    have h := hA2 (finiteBasisVec j : Fin n → ℝ)
    simpa [hselect, vecNorm2_finiteBasisVec j] using h
  have hsqs : frobNormSqRect A ≤ (n : ℝ) * A2 ^ 2 := by
    rw [frobNormSqRect_eq_sum_vecNorm2Sq_cols A]
    calc
      (∑ j : Fin n, vecNorm2Sq (fun i : Fin m => A i j))
          = ∑ j : Fin n, (vecNorm2 (fun i : Fin m => A i j)) ^ 2 := by
              apply Finset.sum_congr rfl
              intro j _
              rw [vecNorm2_sq]
      _ ≤ ∑ _j : Fin n, A2 ^ 2 := by
              apply Finset.sum_le_sum
              intro j _
              have hleft_nonneg :
                  0 ≤ vecNorm2 (fun i : Fin m => A i j) :=
                vecNorm2_nonneg _
              have habs :
                  |vecNorm2 (fun i : Fin m => A i j)| ≤ |A2| := by
                rw [abs_of_nonneg hleft_nonneg, abs_of_nonneg hA2_nonneg]
                exact hcol j
              exact (sq_le_sq).mpr habs
      _ = (n : ℝ) * A2 ^ 2 := by
              simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
  unfold frobNormRect
  calc
    Real.sqrt (frobNormSqRect A)
        ≤ Real.sqrt ((n : ℝ) * A2 ^ 2) :=
          Real.sqrt_le_sqrt hsqs
    _ = Real.sqrt (n : ℝ) * A2 := by
          rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq_eq_abs,
            abs_of_nonneg hA2_nonneg]

/-- Rectangular Frobenius norm squared is invariant under the generic finite
    transpose. -/
theorem frobNormSqRect_finiteTranspose {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    frobNormSqRect (finiteTranspose A) = frobNormSqRect A := by
  unfold frobNormSqRect finiteTranspose
  rw [Finset.sum_comm]

/-- Rectangular Frobenius norm is invariant under the generic finite
    transpose. -/
theorem frobNormRect_finiteTranspose {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    frobNormRect (finiteTranspose A) = frobNormRect A := by
  unfold frobNormRect
  rw [frobNormSqRect_finiteTranspose]

/-- Last-column residual right-hand-side norm foothold.

After Stewart equations (2.7)--(2.8) are rewritten in residual form, the
last-column vector solve is driven by `(G₁₁-F₁₁)ᵀ r + p g`.  This lemma bounds
that vector by the Frobenius norm of the initial-block difference, the
Euclidean norm of the appended `R` column, and the last-row data of `G`. -/
theorem stewartQRLastColumnResidual_rhs_vecNorm2_le
    {n : ℕ} {R F G : Fin (n + 1) → Fin (n + 1) → ℝ} :
    vecNorm2
        (fun i : Fin n =>
          (∑ k : Fin n,
            (G k.castSucc i.castSucc - F k.castSucc i.castSucc) *
              R k.castSucc (Fin.last n)) +
            G (Fin.last n) i.castSucc * R (Fin.last n) (Fin.last n)) ≤
      frobNormRect
          (fun k i : Fin n =>
            G k.castSucc i.castSucc - F k.castSucc i.castSucc) *
        vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) +
        |R (Fin.last n) (Fin.last n)| *
          vecNorm2 (fun i : Fin n => G (Fin.last n) i.castSucc) := by
  let D : Fin n → Fin n → ℝ :=
    fun k i => G k.castSucc i.castSucc - F k.castSucc i.castSucc
  let rcol : Fin n → ℝ := fun k => R k.castSucc (Fin.last n)
  let grow : Fin n → ℝ := fun i => G (Fin.last n) i.castSucc
  let p : ℝ := R (Fin.last n) (Fin.last n)
  have hrepr :
      (fun i : Fin n =>
          (∑ k : Fin n,
            (G k.castSucc i.castSucc - F k.castSucc i.castSucc) *
              R k.castSucc (Fin.last n)) +
            G (Fin.last n) i.castSucc * R (Fin.last n) (Fin.last n)) =
        fun i : Fin n =>
          rectMatMulVec (finiteTranspose D) rcol i + p * grow i := by
    ext i
    dsimp [D, rcol, grow, p, rectMatMulVec, finiteTranspose]
    ring
  have htri :
      vecNorm2 (fun i : Fin n =>
          rectMatMulVec (finiteTranspose D) rcol i + p * grow i) ≤
        vecNorm2 (rectMatMulVec (finiteTranspose D) rcol) +
          vecNorm2 (fun i : Fin n => p * grow i) :=
    vecNorm2_add_le (rectMatMulVec (finiteTranspose D) rcol)
      (fun i : Fin n => p * grow i)
  have hmat :
      vecNorm2 (rectMatMulVec (finiteTranspose D) rcol) ≤
        frobNormRect D * vecNorm2 rcol := by
    have h :=
      vecNorm2_rectMatMulVec_le_frobNormRect_mul
        (finiteTranspose D) rcol
    simpa [frobNormRect_finiteTranspose] using h
  have hscale :
      vecNorm2 (fun i : Fin n => p * grow i) =
        |p| * vecNorm2 grow :=
    vecNorm2_smul p grow
  calc
    vecNorm2
        (fun i : Fin n =>
          (∑ k : Fin n,
            (G k.castSucc i.castSucc - F k.castSucc i.castSucc) *
              R k.castSucc (Fin.last n)) +
            G (Fin.last n) i.castSucc * R (Fin.last n) (Fin.last n))
        = vecNorm2 (fun i : Fin n =>
            rectMatMulVec (finiteTranspose D) rcol i + p * grow i) := by
          rw [hrepr]
    _ ≤ vecNorm2 (rectMatMulVec (finiteTranspose D) rcol) +
          vecNorm2 (fun i : Fin n => p * grow i) := htri
    _ ≤ frobNormRect D * vecNorm2 rcol + |p| * vecNorm2 grow := by
          exact add_le_add hmat (le_of_eq hscale)
    _ = frobNormRect
          (fun k i : Fin n =>
            G k.castSucc i.castSucc - F k.castSucc i.castSucc) *
        vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) +
        |R (Fin.last n) (Fin.last n)| *
          vecNorm2 (fun i : Fin n => G (Fin.last n) i.castSucc) := by
          rfl

/-- Last-column residual solve under an explicit bounded inverse action.

This is the next Stewart Theorem 2.2 augmentation foothold after the residual
equations: if `W` is a left inverse for the initial-block transpose action and
has Euclidean operator bound `rho`, then the unknown last-column correction is
controlled by the source residual right-hand side.  The theorem deliberately
keeps the inverse action as a hypothesis; proving Stewart's global source
constant amounts to constructing such bounds recursively for the triangular
initial blocks. -/
theorem stewartQRLastColumnResidual_vecNorm2_le_of_left_inverse_bound
    {n : ℕ} {R F G : Fin (n + 1) → Fin (n + 1) → ℝ}
    {W : Fin n → Fin n → ℝ} {rho : ℝ}
    (hR_upper : QRUpperTriangular (n + 1) R)
    (hF_upper : QRUpperTriangular (n + 1) F)
    (hT : stewartQRLinearMap R F = stewartQRNaturalExtension R G)
    (hsolve :
      ∀ x : Fin n → ℝ,
        rectMatMulVec W
            (rectMatMulVec
              (finiteTranspose
                (fun k i : Fin n => R k.castSucc i.castSucc)) x) =
          x)
    (hW : rectOpNorm2Le W rho)
    (hrho : 0 ≤ rho) :
    vecNorm2
        (fun k : Fin n =>
          F k.castSucc (Fin.last n) - G k.castSucc (Fin.last n)) ≤
      rho *
        (frobNormRect
            (fun k i : Fin n =>
              G k.castSucc i.castSucc - F k.castSucc i.castSucc) *
          vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) +
          |R (Fin.last n) (Fin.last n)| *
            vecNorm2 (fun i : Fin n => G (Fin.last n) i.castSucc)) := by
  let Rinit : Fin n → Fin n → ℝ :=
    fun k i => R k.castSucc i.castSucc
  let x : Fin n → ℝ :=
    fun k => F k.castSucc (Fin.last n) - G k.castSucc (Fin.last n)
  let b : Fin n → ℝ :=
    fun i =>
      (∑ k : Fin n,
        (G k.castSucc i.castSucc - F k.castSucc i.castSucc) *
          R k.castSucc (Fin.last n)) +
        G (Fin.last n) i.castSucc * R (Fin.last n) (Fin.last n)
  have hb : rectMatMulVec (finiteTranspose Rinit) x = b := by
    ext i
    dsimp [Rinit, x, b, rectMatMulVec, finiteTranspose]
    exact stewartQRLinearMap_lastColumn_residual_eq_of_naturalExtension
      hR_upper hF_upper hT i
  have hx : x = rectMatMulVec W b := by
    calc
      x = rectMatMulVec W (rectMatMulVec (finiteTranspose Rinit) x) := by
          exact (hsolve x).symm
      _ = rectMatMulVec W b := by
          rw [hb]
  have hb_bound :
      vecNorm2 b ≤
        frobNormRect
            (fun k i : Fin n =>
              G k.castSucc i.castSucc - F k.castSucc i.castSucc) *
          vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) +
          |R (Fin.last n) (Fin.last n)| *
            vecNorm2 (fun i : Fin n => G (Fin.last n) i.castSucc) := by
    dsimp [b]
    exact stewartQRLastColumnResidual_rhs_vecNorm2_le
      (R := R) (F := F) (G := G)
  calc
    vecNorm2
        (fun k : Fin n =>
          F k.castSucc (Fin.last n) - G k.castSucc (Fin.last n))
        = vecNorm2 x := by rfl
    _ = vecNorm2 (rectMatMulVec W b) := by rw [hx]
    _ ≤ rho * vecNorm2 b := hW b
    _ ≤ rho *
        (frobNormRect
            (fun k i : Fin n =>
              G k.castSucc i.castSucc - F k.castSucc i.castSucc) *
          vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) +
          |R (Fin.last n) (Fin.last n)| *
            vecNorm2 (fun i : Fin n => G (Fin.last n) i.castSucc)) := by
        exact mul_le_mul_of_nonneg_left hb_bound hrho

/-- Last-column residual solve from the repository matrix-left-inverse API.

This is the public adapter for the previous theorem: an `IsLeftInverse`
certificate for the initial-block transpose action supplies the raw
`W(Tx)=x` hypothesis, while `rectOpNorm2Le` supplies the Euclidean operator
bound used in the residual estimate. -/
theorem stewartQRLastColumnResidual_vecNorm2_le_of_matrix_left_inverse_bound
    {n : ℕ} {R F G : Fin (n + 1) → Fin (n + 1) → ℝ}
    {W : Fin n → Fin n → ℝ} {rho : ℝ}
    (hR_upper : QRUpperTriangular (n + 1) R)
    (hF_upper : QRUpperTriangular (n + 1) F)
    (hT : stewartQRLinearMap R F = stewartQRNaturalExtension R G)
    (hInv :
      IsLeftInverse n
        (finiteTranspose (fun k i : Fin n => R k.castSucc i.castSucc)) W)
    (hW : rectOpNorm2Le W rho)
    (hrho : 0 ≤ rho) :
    vecNorm2
        (fun k : Fin n =>
          F k.castSucc (Fin.last n) - G k.castSucc (Fin.last n)) ≤
      rho *
        (frobNormRect
            (fun k i : Fin n =>
              G k.castSucc i.castSucc - F k.castSucc i.castSucc) *
          vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) +
          |R (Fin.last n) (Fin.last n)| *
            vecNorm2 (fun i : Fin n => G (Fin.last n) i.castSucc)) := by
  exact
    stewartQRLastColumnResidual_vecNorm2_le_of_left_inverse_bound
      hR_upper hF_upper hT
      (rectMatMulVec_left_inverse_of_IsLeftInverse hInv) hW hrho

/-- Full-right-hand-side version of the Stewart last-column residual solve.

After the initial block has already been bounded by `alpha * ||G||_F`, the
last-column residual estimate is controlled by the full right-hand side and the
visible appended-column data of `R`.  This is the source-constant absorption
foothold for Stewart's last-column induction route. -/
theorem stewartQRLastColumnResidual_vecNorm2_le_full_of_matrix_left_inverse_bound
    {n : ℕ} {R F G : Fin (n + 1) → Fin (n + 1) → ℝ}
    {W : Fin n → Fin n → ℝ} {rho alpha : ℝ}
    (hR_upper : QRUpperTriangular (n + 1) R)
    (hF_upper : QRUpperTriangular (n + 1) F)
    (hT : stewartQRLinearMap R F = stewartQRNaturalExtension R G)
    (hInv :
      IsLeftInverse n
        (finiteTranspose (fun k i : Fin n => R k.castSucc i.castSucc)) W)
    (hW : rectOpNorm2Le W rho)
    (hrho : 0 ≤ rho)
    (hInit :
      frobNormRect
          (fun k i : Fin n =>
            G k.castSucc i.castSucc - F k.castSucc i.castSucc) ≤
        alpha * frobNormRect G) :
    vecNorm2
        (fun k : Fin n =>
          F k.castSucc (Fin.last n) - G k.castSucc (Fin.last n)) ≤
      rho *
        ((alpha * vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) +
            |R (Fin.last n) (Fin.last n)|) *
          frobNormRect G) := by
  let D : Fin n → Fin n → ℝ :=
    fun k i => G k.castSucc i.castSucc - F k.castSucc i.castSucc
  let rcol : Fin n → ℝ := fun k => R k.castSucc (Fin.last n)
  let grow : Fin n → ℝ := fun i => G (Fin.last n) i.castSucc
  let p : ℝ := R (Fin.last n) (Fin.last n)
  have hbase :
      vecNorm2
          (fun k : Fin n =>
            F k.castSucc (Fin.last n) - G k.castSucc (Fin.last n)) ≤
        rho * (frobNormRect D * vecNorm2 rcol + |p| * vecNorm2 grow) := by
    exact
      stewartQRLastColumnResidual_vecNorm2_le_of_matrix_left_inverse_bound
        hR_upper hF_upper hT hInv hW hrho
  have hDterm :
      frobNormRect D * vecNorm2 rcol ≤
        (alpha * frobNormRect G) * vecNorm2 rcol :=
    mul_le_mul_of_nonneg_right hInit (vecNorm2_nonneg rcol)
  have hGrow : vecNorm2 grow ≤ frobNormRect G := by
    simpa [grow] using vecNorm2_lastRowInit_le_frobNormRect G
  have hGrowTerm :
      |p| * vecNorm2 grow ≤ |p| * frobNormRect G :=
    mul_le_mul_of_nonneg_left hGrow (abs_nonneg p)
  have hinner :
      frobNormRect D * vecNorm2 rcol + |p| * vecNorm2 grow ≤
        (alpha * vecNorm2 rcol + |p|) * frobNormRect G := by
    calc
      frobNormRect D * vecNorm2 rcol + |p| * vecNorm2 grow
          ≤ (alpha * frobNormRect G) * vecNorm2 rcol +
              |p| * frobNormRect G := add_le_add hDterm hGrowTerm
      _ = (alpha * vecNorm2 rcol + |p|) * frobNormRect G := by ring
  exact le_trans hbase (mul_le_mul_of_nonneg_left hinner hrho)

/-- Bottom-right residual scalar estimate for Stewart's last-column split.

Equation (2.8) says that the final diagonal residual is driven by the inner
product of the appended `R` column with the already controlled last-column
residual.  This lemma isolates the resulting Cauchy--Schwarz bound. -/
theorem stewartQRLastLastResidual_abs_le
    {n : ℕ} {R F G : Fin (n + 1) → Fin (n + 1) → ℝ}
    (hT : stewartQRLinearMap R F = stewartQRNaturalExtension R G)
    (hp : R (Fin.last n) (Fin.last n) ≠ 0) :
    |F (Fin.last n) (Fin.last n) - G (Fin.last n) (Fin.last n)| ≤
      |1 / R (Fin.last n) (Fin.last n)| *
        vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) *
        vecNorm2
          (fun k : Fin n =>
            F k.castSucc (Fin.last n) - G k.castSucc (Fin.last n)) := by
  let rcol : Fin n → ℝ := fun k => R k.castSucc (Fin.last n)
  let x : Fin n → ℝ :=
    fun k => F k.castSucc (Fin.last n) - G k.castSucc (Fin.last n)
  let p : ℝ := R (Fin.last n) (Fin.last n)
  let delta : ℝ := F (Fin.last n) (Fin.last n) - G (Fin.last n) (Fin.last n)
  let S : ℝ := ∑ k : Fin n, rcol k * x k
  have hp' : p ≠ 0 := by
    dsimp [p]
    exact hp
  have hres : S + p * delta = 0 := by
    dsimp [S, rcol, x, p, delta]
    exact stewartQRLinearMap_lastLast_residual_eq_of_naturalExtension hT
  have hpdelta : p * delta = -S := by
    linarith
  have hdelta_eq : delta = -(1 / p) * S := by
    calc
      delta = (1 / p) * (p * delta) := by
        field_simp [hp']
      _ = (1 / p) * (-S) := by rw [hpdelta]
      _ = -(1 / p) * S := by ring
  have hinner : |S| ≤ vecNorm2 rcol * vecNorm2 x := by
    dsimp [S]
    exact abs_vecInnerProduct_le_vecNorm2_mul rcol x
  calc
    |F (Fin.last n) (Fin.last n) - G (Fin.last n) (Fin.last n)|
        = |delta| := by rfl
    _ = |-(1 / p) * S| := by rw [hdelta_eq]
    _ = |1 / p| * |S| := by rw [abs_mul, abs_neg]
    _ ≤ |1 / p| * (vecNorm2 rcol * vecNorm2 x) :=
        mul_le_mul_of_nonneg_left hinner (abs_nonneg (1 / p))
    _ =
      |1 / R (Fin.last n) (Fin.last n)| *
        vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) *
        vecNorm2
          (fun k : Fin n =>
            F k.castSucc (Fin.last n) - G k.castSucc (Fin.last n)) := by
        dsimp [rcol, x, p]
        ring

/-- Full-right-hand-side version of the bottom-right residual estimate.

This composes the scalar residual equation (2.8) with the full-`G`
last-column residual solve.  It is the scalar companion to
`stewartQRLastColumnResidual_vecNorm2_le_full_of_matrix_left_inverse_bound`
for the last-row/last-column augmentation route. -/
theorem stewartQRLastLastResidual_abs_le_full_of_matrix_left_inverse_bound
    {n : ℕ} {R F G : Fin (n + 1) → Fin (n + 1) → ℝ}
    {W : Fin n → Fin n → ℝ} {rho alpha : ℝ}
    (hR_upper : QRUpperTriangular (n + 1) R)
    (hF_upper : QRUpperTriangular (n + 1) F)
    (hT : stewartQRLinearMap R F = stewartQRNaturalExtension R G)
    (hInv :
      IsLeftInverse n
        (finiteTranspose (fun k i : Fin n => R k.castSucc i.castSucc)) W)
    (hW : rectOpNorm2Le W rho)
    (hrho : 0 ≤ rho)
    (hInit :
      frobNormRect
          (fun k i : Fin n =>
            G k.castSucc i.castSucc - F k.castSucc i.castSucc) ≤
        alpha * frobNormRect G)
    (hp : R (Fin.last n) (Fin.last n) ≠ 0) :
    |F (Fin.last n) (Fin.last n) - G (Fin.last n) (Fin.last n)| ≤
      |1 / R (Fin.last n) (Fin.last n)| *
        vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) *
        (rho *
          ((alpha * vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) +
              |R (Fin.last n) (Fin.last n)|) *
            frobNormRect G)) := by
  let rcol : Fin n → ℝ := fun k => R k.castSucc (Fin.last n)
  let x : Fin n → ℝ :=
    fun k => F k.castSucc (Fin.last n) - G k.castSucc (Fin.last n)
  let p : ℝ := R (Fin.last n) (Fin.last n)
  have hscalar :
      |F (Fin.last n) (Fin.last n) - G (Fin.last n) (Fin.last n)| ≤
        |1 / p| * vecNorm2 rcol * vecNorm2 x := by
    simpa [rcol, x, p] using
      stewartQRLastLastResidual_abs_le (R := R) (F := F) (G := G) hT hp
  have hx :
      vecNorm2 x ≤
        rho *
          ((alpha * vecNorm2 rcol + |p|) * frobNormRect G) := by
    simpa [x, rcol, p] using
      stewartQRLastColumnResidual_vecNorm2_le_full_of_matrix_left_inverse_bound
        hR_upper hF_upper hT hInv hW hrho hInit
  have hcoef : 0 ≤ |1 / p| * vecNorm2 rcol :=
    mul_nonneg (abs_nonneg _) (vecNorm2_nonneg _)
  calc
    |F (Fin.last n) (Fin.last n) - G (Fin.last n) (Fin.last n)|
        ≤ |1 / p| * vecNorm2 rcol * vecNorm2 x := hscalar
    _ ≤ |1 / p| * vecNorm2 rcol *
          (rho *
            ((alpha * vecNorm2 rcol + |p|) * frobNormRect G)) :=
        mul_le_mul_of_nonneg_left hx hcoef
    _ =
      |1 / R (Fin.last n) (Fin.last n)| *
        vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) *
        (rho *
          ((alpha * vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) +
              |R (Fin.last n) (Fin.last n)|) *
            frobNormRect G)) := by
        dsimp [rcol, p]

/-- Visible recursive norm estimate for Stewart's last-column induction route.

Assuming the initial `n x n` inverse-bound theorem and a bounded left inverse
for the initial-block transpose action, the full correction is controlled by
the initial block, the final-column residual, and the final scalar residual.
All pivot-column factors are exposed; the remaining source-constant step is to
absorb this coefficient into Stewart's recursive
`(n+1)(2+sqrt(2))κ(R)` budget. -/
theorem StewartQRLinearInverseBound.lastColumn_step_visible_factors
    {n : ℕ} {R F G : Fin (n + 1) → Fin (n + 1) → ℝ}
    {W : Fin n → Fin n → ℝ} {sigma rho : ℝ}
    (hTail :
      StewartQRLinearInverseBound n
        (fun i j : Fin n => R i.castSucc j.castSucc) sigma)
    (hsigma : 0 ≤ sigma)
    (hR_upper : QRUpperTriangular (n + 1) R)
    (hF_upper : QRUpperTriangular (n + 1) F)
    (hT : stewartQRLinearMap R F = stewartQRNaturalExtension R G)
    (hInv :
      IsLeftInverse n
        (finiteTranspose (fun k i : Fin n => R k.castSucc i.castSucc)) W)
    (hW : rectOpNorm2Le W rho)
    (hrho : 0 ≤ rho)
    (hp : R (Fin.last n) (Fin.last n) ≠ 0) :
    frobNormRect F ≤
      (sigma +
          (1 + rho *
            ((1 + sigma) *
              vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) +
              |R (Fin.last n) (Fin.last n)|)) +
          (1 + |1 / R (Fin.last n) (Fin.last n)| *
            vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) *
              (rho *
                ((1 + sigma) *
                  vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) +
                  |R (Fin.last n) (Fin.last n)|)))) *
        frobNormRect G := by
  let R11 : Fin n → Fin n → ℝ :=
    fun i j => R i.castSucc j.castSucc
  let F11 : Fin n → Fin n → ℝ :=
    fun i j => F i.castSucc j.castSucc
  let G11 : Fin n → Fin n → ℝ :=
    fun i j => G i.castSucc j.castSucc
  let rcol : Fin n → ℝ :=
    fun k => R k.castSucc (Fin.last n)
  let fcol : Fin n → ℝ :=
    fun k => F k.castSucc (Fin.last n)
  let gcol : Fin n → ℝ :=
    fun k => G k.castSucc (Fin.last n)
  let xcol : Fin n → ℝ :=
    fun k => F k.castSucc (Fin.last n) - G k.castSucc (Fin.last n)
  let p : ℝ := R (Fin.last n) (Fin.last n)
  have hsplit :=
    stewartQRUpperTriangular_frobNormRect_le_lastColumn_blocks
      (n := n) (F := F) hF_upper
  have hF11_upper : QRUpperTriangular n F11 := by
    intro i j hji
    exact hF_upper i.castSucc j.castSucc hji
  have hInitEq :
      stewartQRLinearMap R11 F11 = stewartQRNaturalExtension R11 G11 := by
    simpa [R11, F11, G11] using
      stewartQRLinearMap_init_eq_of_naturalExtension
        hR_upper hF_upper hT
  have hF11_raw : frobNormRect F11 ≤ sigma * frobNormRect G11 :=
    hTail.of_natural_extension hF11_upper hInitEq
  have hG11 : frobNormRect G11 ≤ frobNormRect G := by
    simpa [G11] using frobNormRect_init_le G
  have hF11 :
      frobNormRect F11 ≤ sigma * frobNormRect G := by
    exact le_trans hF11_raw (mul_le_mul_of_nonneg_left hG11 hsigma)
  have hInit :
      frobNormRect
          (fun k i : Fin n =>
            G k.castSucc i.castSucc - F k.castSucc i.castSucc) ≤
        (1 + sigma) * frobNormRect G :=
    stewartQRInitialBlockResidual_frobNormRect_le_full
      hTail hsigma hR_upper hF_upper hT
  have hx_raw :
      vecNorm2 xcol ≤
        rho * (((1 + sigma) * vecNorm2 rcol + |p|) * frobNormRect G) := by
    simpa [xcol, rcol, p] using
      stewartQRLastColumnResidual_vecNorm2_le_full_of_matrix_left_inverse_bound
        hR_upper hF_upper hT hInv hW hrho hInit
  have hx :
      vecNorm2 xcol ≤
        (rho * ((1 + sigma) * vecNorm2 rcol + |p|)) * frobNormRect G := by
    calc
      vecNorm2 xcol
          ≤ rho * (((1 + sigma) * vecNorm2 rcol + |p|) *
              frobNormRect G) := hx_raw
      _ = (rho * ((1 + sigma) * vecNorm2 rcol + |p|)) *
            frobNormRect G := by ring
  have hfcol_decomp : fcol = fun k : Fin n => gcol k + xcol k := by
    ext k
    dsimp [fcol, gcol, xcol]
    ring
  have hfcol_tri : vecNorm2 fcol ≤ vecNorm2 gcol + vecNorm2 xcol := by
    rw [hfcol_decomp]
    exact vecNorm2_add_le gcol xcol
  have hgcol : vecNorm2 gcol ≤ frobNormRect G := by
    simpa [gcol] using vecNorm2_lastColumnInit_le_frobNormRect G
  have hfcol :
      vecNorm2 fcol ≤
        (1 + rho * ((1 + sigma) * vecNorm2 rcol + |p|)) *
          frobNormRect G := by
    calc
      vecNorm2 fcol ≤ vecNorm2 gcol + vecNorm2 xcol := hfcol_tri
      _ ≤ frobNormRect G +
            (rho * ((1 + sigma) * vecNorm2 rcol + |p|)) *
              frobNormRect G := add_le_add hgcol hx
      _ = (1 + rho * ((1 + sigma) * vecNorm2 rcol + |p|)) *
            frobNormRect G := by ring
  have hdelta_raw :
      |F (Fin.last n) (Fin.last n) - G (Fin.last n) (Fin.last n)| ≤
        |1 / p| * vecNorm2 rcol *
          (rho * (((1 + sigma) * vecNorm2 rcol + |p|) *
            frobNormRect G)) := by
    simpa [rcol, p] using
      stewartQRLastLastResidual_abs_le_full_of_matrix_left_inverse_bound
        hR_upper hF_upper hT hInv hW hrho hInit hp
  have hdelta :
      |F (Fin.last n) (Fin.last n) - G (Fin.last n) (Fin.last n)| ≤
        (|1 / p| * vecNorm2 rcol *
          (rho * ((1 + sigma) * vecNorm2 rcol + |p|))) *
          frobNormRect G := by
    calc
      |F (Fin.last n) (Fin.last n) - G (Fin.last n) (Fin.last n)|
          ≤ |1 / p| * vecNorm2 rcol *
            (rho * (((1 + sigma) * vecNorm2 rcol + |p|) *
              frobNormRect G)) := hdelta_raw
      _ = (|1 / p| * vecNorm2 rcol *
            (rho * ((1 + sigma) * vecNorm2 rcol + |p|))) *
            frobNormRect G := by ring
  have hGll :
      |G (Fin.last n) (Fin.last n)| ≤ frobNormRect G :=
    abs_entry_le_frobNormRect G (Fin.last n) (Fin.last n)
  have hFll_tri :
      |F (Fin.last n) (Fin.last n)| ≤
        |G (Fin.last n) (Fin.last n)| +
          |F (Fin.last n) (Fin.last n) -
            G (Fin.last n) (Fin.last n)| := by
    have hdecomp :
        F (Fin.last n) (Fin.last n) =
          G (Fin.last n) (Fin.last n) +
            (F (Fin.last n) (Fin.last n) -
              G (Fin.last n) (Fin.last n)) := by
      ring
    calc
      |F (Fin.last n) (Fin.last n)|
          = |G (Fin.last n) (Fin.last n) +
              (F (Fin.last n) (Fin.last n) -
                G (Fin.last n) (Fin.last n))| := by
            exact congrArg abs hdecomp
      _ ≤ |G (Fin.last n) (Fin.last n)| +
            |F (Fin.last n) (Fin.last n) - G (Fin.last n) (Fin.last n)| :=
          abs_add_le (G (Fin.last n) (Fin.last n))
            (F (Fin.last n) (Fin.last n) - G (Fin.last n) (Fin.last n))
  have hFll :
      |F (Fin.last n) (Fin.last n)| ≤
        (1 + |1 / p| * vecNorm2 rcol *
          (rho * ((1 + sigma) * vecNorm2 rcol + |p|))) *
          frobNormRect G := by
    calc
      |F (Fin.last n) (Fin.last n)|
          ≤ |G (Fin.last n) (Fin.last n)| +
              |F (Fin.last n) (Fin.last n) -
                G (Fin.last n) (Fin.last n)| := hFll_tri
      _ ≤ frobNormRect G +
            (|1 / p| * vecNorm2 rcol *
              (rho * ((1 + sigma) * vecNorm2 rcol + |p|))) *
              frobNormRect G := add_le_add hGll hdelta
      _ = (1 + |1 / p| * vecNorm2 rcol *
            (rho * ((1 + sigma) * vecNorm2 rcol + |p|))) *
            frobNormRect G := by ring
  calc
    frobNormRect F
        ≤ frobNormRect F11 + vecNorm2 fcol +
            |F (Fin.last n) (Fin.last n)| := by
          simpa [F11, fcol] using hsplit
    _ ≤ sigma * frobNormRect G +
          (1 + rho * ((1 + sigma) * vecNorm2 rcol + |p|)) *
            frobNormRect G +
          (1 + |1 / p| * vecNorm2 rcol *
            (rho * ((1 + sigma) * vecNorm2 rcol + |p|))) *
            frobNormRect G := by
          exact add_le_add (add_le_add hF11 hfcol) hFll
    _ =
      (sigma +
          (1 + rho * ((1 + sigma) * vecNorm2 rcol + |p|)) +
          (1 + |1 / p| * vecNorm2 rcol *
            (rho * ((1 + sigma) * vecNorm2 rcol + |p|)))) *
        frobNormRect G := by ring
    _ =
      (sigma +
          (1 + rho *
            ((1 + sigma) *
              vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) +
              |R (Fin.last n) (Fin.last n)|)) +
          (1 + |1 / R (Fin.last n) (Fin.last n)| *
            vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) *
              (rho *
                ((1 + sigma) *
                  vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) +
                  |R (Fin.last n) (Fin.last n)|)))) *
        frobNormRect G := by
        dsimp [rcol, p]

/-- Last-column recursive adapter for Stewart Theorem 2.2.

The previous theorem exposes the full last-column coefficient.  This adapter
turns any proof that the visible coefficient is absorbed by a target budget
`sigmaNext` into the recursive inverse-bound statement itself. -/
theorem StewartQRLinearInverseBound.lastColumn_step_of_visible_factor_le
    {n : ℕ} {R : Fin (n + 1) → Fin (n + 1) → ℝ}
    {W : Fin n → Fin n → ℝ} {sigma rho sigmaNext : ℝ}
    (hTail :
      StewartQRLinearInverseBound n
        (fun i j : Fin n => R i.castSucc j.castSucc) sigma)
    (hsigma : 0 ≤ sigma)
    (hR_upper : QRUpperTriangular (n + 1) R)
    (hInv :
      IsLeftInverse n
        (finiteTranspose (fun k i : Fin n => R k.castSucc i.castSucc)) W)
    (hW : rectOpNorm2Le W rho)
    (hrho : 0 ≤ rho)
    (hp : R (Fin.last n) (Fin.last n) ≠ 0)
    (hfactor :
      sigma +
          (1 + rho *
            ((1 + sigma) *
              vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) +
              |R (Fin.last n) (Fin.last n)|)) +
          (1 + |1 / R (Fin.last n) (Fin.last n)| *
            vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) *
              (rho *
                ((1 + sigma) *
                  vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) +
                  |R (Fin.last n) (Fin.last n)|))) ≤ sigmaNext) :
    StewartQRLinearInverseBound (n + 1) R sigmaNext := by
  refine ⟨?_⟩
  intro F G hF_upper hT
  have hvisible :
      frobNormRect F ≤
        (sigma +
            (1 + rho *
              ((1 + sigma) *
                vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) +
                |R (Fin.last n) (Fin.last n)|)) +
            (1 + |1 / R (Fin.last n) (Fin.last n)| *
              vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) *
                (rho *
                  ((1 + sigma) *
                    vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) +
                    |R (Fin.last n) (Fin.last n)|)))) *
          frobNormRect G :=
    StewartQRLinearInverseBound.lastColumn_step_visible_factors
      (n := n) (R := R) (F := F) (G := G) (W := W)
      (sigma := sigma) (rho := rho)
      hTail hsigma hR_upper hF_upper hT hInv hW hrho hp
  exact le_trans hvisible
    (mul_le_mul_of_nonneg_right hfactor (frobNormRect_nonneg G))

/-- Source-constant-facing form of the last-column recursive adapter. -/
theorem StewartQRLinearInverseBound.lastColumn_step_of_source_constant_factor_le
    {n : ℕ} {R : Fin (n + 1) → Fin (n + 1) → ℝ}
    {W : Fin n → Fin n → ℝ} {sigma rho kappa : ℝ}
    (hTail :
      StewartQRLinearInverseBound n
        (fun i j : Fin n => R i.castSucc j.castSucc) sigma)
    (hsigma : 0 ≤ sigma)
    (hR_upper : QRUpperTriangular (n + 1) R)
    (hInv :
      IsLeftInverse n
        (finiteTranspose (fun k i : Fin n => R k.castSucc i.castSucc)) W)
    (hW : rectOpNorm2Le W rho)
    (hrho : 0 ≤ rho)
    (hp : R (Fin.last n) (Fin.last n) ≠ 0)
    (hfactor :
      sigma +
          (1 + rho *
            ((1 + sigma) *
              vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) +
              |R (Fin.last n) (Fin.last n)|)) +
          (1 + |1 / R (Fin.last n) (Fin.last n)| *
            vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) *
              (rho *
                ((1 + sigma) *
                  vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) +
                  |R (Fin.last n) (Fin.last n)|))) ≤
        stewartQRLinearInverseConstant (n + 1) kappa) :
    StewartQRLinearInverseBound (n + 1) R
      (stewartQRLinearInverseConstant (n + 1) kappa) :=
  StewartQRLinearInverseBound.lastColumn_step_of_visible_factor_le
    (n := n) (R := R) (W := W) (sigma := sigma) (rho := rho)
    (sigmaNext := stewartQRLinearInverseConstant (n + 1) kappa)
    hTail hsigma hR_upper hInv hW hrho hp hfactor

/-- Last-column recursive adapter using the source inverse of the leading block.

Stewart's last-column proof applies the inverse action of the leading block
transpose.  This wrapper lets the caller provide a right inverse for the
leading block itself, plus an operator-2 bound for that inverse; the shared
transpose-inverse lemmas supply the required left inverse of the transposed
action. -/
theorem StewartQRLinearInverseBound.lastColumn_step_of_right_inverse_visible_factor_le
    {n : ℕ} {R : Fin (n + 1) → Fin (n + 1) → ℝ}
    {Rinv : Fin n → Fin n → ℝ} {sigma rho sigmaNext : ℝ}
    (hTail :
      StewartQRLinearInverseBound n
        (fun i j : Fin n => R i.castSucc j.castSucc) sigma)
    (hsigma : 0 ≤ sigma)
    (hR_upper : QRUpperTriangular (n + 1) R)
    (hInvR :
      IsRightInverse n
        (fun i j : Fin n => R i.castSucc j.castSucc) Rinv)
    (hRinv : rectOpNorm2Le Rinv rho)
    (hrho : 0 ≤ rho)
    (hp : R (Fin.last n) (Fin.last n) ≠ 0)
    (hfactor :
      sigma +
          (1 + rho *
            ((1 + sigma) *
              vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) +
              |R (Fin.last n) (Fin.last n)|)) +
          (1 + |1 / R (Fin.last n) (Fin.last n)| *
            vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) *
              (rho *
                ((1 + sigma) *
                  vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) +
                  |R (Fin.last n) (Fin.last n)|))) ≤ sigmaNext) :
    StewartQRLinearInverseBound (n + 1) R sigmaNext := by
  have hInvT :
      IsLeftInverse n
        (finiteTranspose (fun k i : Fin n => R k.castSucc i.castSucc))
        (finiteTranspose Rinv) :=
    isLeftInverse_finiteTranspose_of_isRightInverse
      (T := fun i j : Fin n => R i.castSucc j.castSucc)
      (T_inv := Rinv) hInvR
  have hRinvT : rectOpNorm2Le (finiteTranspose Rinv) rho :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le Rinv hrho hRinv
  exact
    StewartQRLinearInverseBound.lastColumn_step_of_visible_factor_le
      (n := n) (R := R) (W := finiteTranspose Rinv)
      (sigma := sigma) (rho := rho) (sigmaNext := sigmaNext)
      hTail hsigma hR_upper hInvT hRinvT hrho hp hfactor

/-- Source-constant-facing last-column adapter using a right inverse for the
leading block rather than an arbitrary inverse witness for its transpose. -/
theorem StewartQRLinearInverseBound.lastColumn_step_of_right_inverse_source_constant_factor_le
    {n : ℕ} {R : Fin (n + 1) → Fin (n + 1) → ℝ}
    {Rinv : Fin n → Fin n → ℝ} {sigma rho kappa : ℝ}
    (hTail :
      StewartQRLinearInverseBound n
        (fun i j : Fin n => R i.castSucc j.castSucc) sigma)
    (hsigma : 0 ≤ sigma)
    (hR_upper : QRUpperTriangular (n + 1) R)
    (hInvR :
      IsRightInverse n
        (fun i j : Fin n => R i.castSucc j.castSucc) Rinv)
    (hRinv : rectOpNorm2Le Rinv rho)
    (hrho : 0 ≤ rho)
    (hp : R (Fin.last n) (Fin.last n) ≠ 0)
    (hfactor :
      sigma +
          (1 + rho *
            ((1 + sigma) *
              vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) +
              |R (Fin.last n) (Fin.last n)|)) +
          (1 + |1 / R (Fin.last n) (Fin.last n)| *
            vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) *
              (rho *
                ((1 + sigma) *
                  vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) +
                  |R (Fin.last n) (Fin.last n)|))) ≤
        stewartQRLinearInverseConstant (n + 1) kappa) :
    StewartQRLinearInverseBound (n + 1) R
      (stewartQRLinearInverseConstant (n + 1) kappa) :=
  StewartQRLinearInverseBound.lastColumn_step_of_right_inverse_visible_factor_le
    (n := n) (R := R) (Rinv := Rinv) (sigma := sigma)
    (rho := rho)
    (sigmaNext := stewartQRLinearInverseConstant (n + 1) kappa)
    hTail hsigma hR_upper hInvR hRinv hrho hp hfactor

/-- Last-column recursive adapter using a Frobenius bound on the leading
block's source right inverse.

Stewart's Frobenius condition surface naturally controls the Frobenius norm of
the inverse factor.  The shared matrix-norm bridge converts that into the
rectangular operator certificate required by the residual solve. -/
theorem StewartQRLinearInverseBound.lastColumn_step_of_right_inverse_frob_visible_factor_le
    {n : ℕ} {R : Fin (n + 1) → Fin (n + 1) → ℝ}
    {Rinv : Fin n → Fin n → ℝ} {sigma rho sigmaNext : ℝ}
    (hTail :
      StewartQRLinearInverseBound n
        (fun i j : Fin n => R i.castSucc j.castSucc) sigma)
    (hsigma : 0 ≤ sigma)
    (hR_upper : QRUpperTriangular (n + 1) R)
    (hInvR :
      IsRightInverse n
        (fun i j : Fin n => R i.castSucc j.castSucc) Rinv)
    (hRinvFrob : frobNormRect Rinv ≤ rho)
    (hrho : 0 ≤ rho)
    (hp : R (Fin.last n) (Fin.last n) ≠ 0)
    (hfactor :
      sigma +
          (1 + rho *
            ((1 + sigma) *
              vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) +
              |R (Fin.last n) (Fin.last n)|)) +
          (1 + |1 / R (Fin.last n) (Fin.last n)| *
            vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) *
              (rho *
                ((1 + sigma) *
                  vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) +
                  |R (Fin.last n) (Fin.last n)|))) ≤ sigmaNext) :
    StewartQRLinearInverseBound (n + 1) R sigmaNext :=
  StewartQRLinearInverseBound.lastColumn_step_of_right_inverse_visible_factor_le
    (n := n) (R := R) (Rinv := Rinv) (sigma := sigma)
    (rho := rho) (sigmaNext := sigmaNext)
    hTail hsigma hR_upper hInvR
    (rectOpNorm2Le_of_frobNormRect_le Rinv hRinvFrob) hrho hp hfactor

/-- Source-constant-facing last-column adapter using a Frobenius bound on the
leading block's source right inverse. -/
theorem StewartQRLinearInverseBound.lastColumn_step_of_right_inverse_frob_source_constant_factor_le
    {n : ℕ} {R : Fin (n + 1) → Fin (n + 1) → ℝ}
    {Rinv : Fin n → Fin n → ℝ} {sigma rho kappa : ℝ}
    (hTail :
      StewartQRLinearInverseBound n
        (fun i j : Fin n => R i.castSucc j.castSucc) sigma)
    (hsigma : 0 ≤ sigma)
    (hR_upper : QRUpperTriangular (n + 1) R)
    (hInvR :
      IsRightInverse n
        (fun i j : Fin n => R i.castSucc j.castSucc) Rinv)
    (hRinvFrob : frobNormRect Rinv ≤ rho)
    (hrho : 0 ≤ rho)
    (hp : R (Fin.last n) (Fin.last n) ≠ 0)
    (hfactor :
      sigma +
          (1 + rho *
            ((1 + sigma) *
              vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) +
              |R (Fin.last n) (Fin.last n)|)) +
          (1 + |1 / R (Fin.last n) (Fin.last n)| *
            vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) *
              (rho *
                ((1 + sigma) *
                  vecNorm2 (fun k : Fin n => R k.castSucc (Fin.last n)) +
                  |R (Fin.last n) (Fin.last n)|))) ≤
        stewartQRLinearInverseConstant (n + 1) kappa) :
    StewartQRLinearInverseBound (n + 1) R
      (stewartQRLinearInverseConstant (n + 1) kappa) :=
  StewartQRLinearInverseBound.lastColumn_step_of_right_inverse_frob_visible_factor_le
    (n := n) (R := R) (Rinv := Rinv) (sigma := sigma)
    (rho := rho)
    (sigmaNext := stewartQRLinearInverseConstant (n + 1) kappa)
    hTail hsigma hR_upper hInvR hRinvFrob hrho hp hfactor

/-- Top-row tail norm foothold for Stewart Theorem 2.2's induction.

The top-row equation expresses `F12` as the source top-row data `G12` plus
`R22ᵀ G21 / R00`.  This bounds that vector by the full right-hand-side norm
and a visible trailing-factor multiplier. -/
theorem stewartQRTopRowTail_vecNorm2_le_full
    {n : ℕ} {R F G : Fin (n + 1) → Fin (n + 1) → ℝ}
    (hR_upper : QRUpperTriangular (n + 1) R)
    (hF_upper : QRUpperTriangular (n + 1) F)
    (hR00 : R 0 0 ≠ 0)
    (hT : stewartQRLinearMap R F = stewartQRNaturalExtension R G) :
    vecNorm2 (fun j : Fin n => F 0 j.succ) ≤
      (1 + |1 / R 0 0| *
          frobNormRect (fun i j : Fin n => R i.succ j.succ)) *
        frobNormRect G := by
  let R22 : Fin n → Fin n → ℝ := fun i j => R i.succ j.succ
  let g21 : Fin n → ℝ := fun i => G i.succ 0
  let topG : Fin n → ℝ := fun j => G 0 j.succ
  let coupling : Fin n → ℝ :=
    fun j => (1 / R 0 0) * rectMatMulVec (finiteTranspose R22) g21 j
  have hrow :
      (fun j : Fin n => F 0 j.succ) =
        fun j : Fin n => topG j + coupling j := by
    ext j
    have htop :=
      stewartQRLinearMap_topRow_eq_of_naturalExtension
        hR_upper hF_upper hR00 hT j
    dsimp [topG, coupling, R22, g21, rectMatMulVec, finiteTranspose]
    rw [htop]
    congr 1
    simp_rw [div_eq_mul_inv]
    rw [Finset.sum_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have htri :
      vecNorm2 (fun j : Fin n => F 0 j.succ) ≤
        vecNorm2 topG + vecNorm2 coupling := by
    rw [hrow]
    exact vecNorm2_add_le topG coupling
  have htopG : vecNorm2 topG ≤ frobNormRect G := by
    simpa [topG] using vecNorm2_firstRowTail_le_frobNormRect G
  have hcoupling_eq :
      vecNorm2 coupling =
        |1 / R 0 0| * vecNorm2 (rectMatMulVec (finiteTranspose R22) g21) := by
    dsimp [coupling]
    simpa using
      (vecNorm2_smul (1 / R 0 0)
        (rectMatMulVec (finiteTranspose R22) g21))
  have hmat :
      vecNorm2 (rectMatMulVec (finiteTranspose R22) g21) ≤
        frobNormRect R22 * vecNorm2 g21 := by
    have h :=
      vecNorm2_rectMatMulVec_le_frobNormRect_mul
        (finiteTranspose R22) g21
    simpa [frobNormRect_finiteTranspose] using h
  have hg21 : vecNorm2 g21 ≤ frobNormRect G := by
    simpa [g21] using vecNorm2_firstColumnTail_le_frobNormRect G
  have hmat_full :
      vecNorm2 (rectMatMulVec (finiteTranspose R22) g21) ≤
        frobNormRect R22 * frobNormRect G := by
    exact le_trans hmat
      (mul_le_mul_of_nonneg_left hg21 (frobNormRect_nonneg R22))
  have hcoupling :
      vecNorm2 coupling ≤
        |1 / R 0 0| * (frobNormRect R22 * frobNormRect G) := by
    rw [hcoupling_eq]
    exact mul_le_mul_of_nonneg_left hmat_full (abs_nonneg _)
  calc
    vecNorm2 (fun j : Fin n => F 0 j.succ)
        ≤ vecNorm2 topG + vecNorm2 coupling := htri
    _ ≤ frobNormRect G +
          |1 / R 0 0| * (frobNormRect R22 * frobNormRect G) :=
        add_le_add htopG hcoupling
    _ = (1 + |1 / R 0 0| * frobNormRect R22) * frobNormRect G := by
        ring

/-- Visible recursive norm estimate for Stewart Theorem 2.2's induction.

Assuming the trailing `n x n` inverse-bound theorem, the full correction norm
is bounded by the leading scalar, top-row-tail, and lower-right recursive
pieces with all current pivot-row factors exposed.  The remaining source step
is to absorb this visible coefficient into Stewart's
`(n+1)(2+sqrt(2))κ(R)` constant. -/
theorem StewartQRLinearInverseBound.step_visible_factors
    {n : ℕ} {R F G : Fin (n + 1) → Fin (n + 1) → ℝ} {sigmaTail : ℝ}
    (hTail :
      StewartQRLinearInverseBound n
        (fun i j : Fin n => R i.succ j.succ) sigmaTail)
    (hsigmaTail : 0 ≤ sigmaTail)
    (hR_upper : QRUpperTriangular (n + 1) R)
    (hF_upper : QRUpperTriangular (n + 1) F)
    (hR00 : R 0 0 ≠ 0)
    (hT : stewartQRLinearMap R F = stewartQRNaturalExtension R G) :
    frobNormRect F ≤
      (1 + (1 + |1 / R 0 0| *
            frobNormRect (fun i j : Fin n => R i.succ j.succ)) +
          sigmaTail *
            (1 + |1 / R 0 0| *
              vecNorm2 (fun j : Fin n => R 0 j.succ))) *
        frobNormRect G := by
  have hsplit :=
    stewartQRUpperTriangular_frobNormRect_le_blocks
      (n := n) (F := F) hF_upper
  have hF00eq :
      F 0 0 = G 0 0 :=
    stewartQRLinearMap_topLeft_eq_of_naturalExtension
      hR_upper hF_upper hR00 hT
  have hG00 : |G 0 0| ≤ frobNormRect G := by
    have hrow :
        G 0 0 ^ 2 ≤ ∑ c : Fin (n + 1), G 0 c ^ 2 :=
      Finset.single_le_sum (fun c _ => sq_nonneg (G 0 c)) (Finset.mem_univ 0)
    have hsq :
        G 0 0 ^ 2 ≤ frobNormSqRect G := by
      unfold frobNormSqRect
      exact le_trans hrow
        (Finset.single_le_sum
          (fun r _ => Finset.sum_nonneg (fun c _ => sq_nonneg (G r c)))
          (Finset.mem_univ 0))
    have hsqrt := Real.sqrt_le_sqrt hsq
    simpa [frobNormRect, Real.sqrt_sq_eq_abs] using hsqrt
  have hF00 : |F 0 0| ≤ frobNormRect G := by
    rw [hF00eq]
    exact hG00
  have hF12 :
      vecNorm2 (fun j : Fin n => F 0 j.succ) ≤
        (1 + |1 / R 0 0| *
            frobNormRect (fun i j : Fin n => R i.succ j.succ)) *
          frobNormRect G :=
    stewartQRTopRowTail_vecNorm2_le_full
      hR_upper hF_upper hR00 hT
  have hF22_raw :
      frobNormRect (fun i j : Fin n => F i.succ j.succ) ≤
        sigmaTail *
          frobNormRect
            (fun i j : Fin n =>
              G i.succ j.succ - (G i.succ 0 / R 0 0) * R 0 j.succ) :=
    StewartQRLinearInverseBound.lowerRight_le
      hTail hR_upper hF_upper hR00 hT
  have hcorr :
      frobNormRect
          (fun i j : Fin n =>
            G i.succ j.succ - (G i.succ 0 / R 0 0) * R 0 j.succ) ≤
        (1 + |1 / R 0 0| *
            vecNorm2 (fun j : Fin n => R 0 j.succ)) *
          frobNormRect G :=
    stewartQRLowerRightCorrectedRhs_frobNormRect_le_full (R := R) (G := G)
  have hF22 :
      frobNormRect (fun i j : Fin n => F i.succ j.succ) ≤
        sigmaTail *
          ((1 + |1 / R 0 0| *
              vecNorm2 (fun j : Fin n => R 0 j.succ)) *
            frobNormRect G) :=
    le_trans hF22_raw (mul_le_mul_of_nonneg_left hcorr hsigmaTail)
  calc
    frobNormRect F
        ≤ |F 0 0| + vecNorm2 (fun j : Fin n => F 0 j.succ) +
            frobNormRect (fun i j : Fin n => F i.succ j.succ) := hsplit
    _ ≤ frobNormRect G +
          ((1 + |1 / R 0 0| *
              frobNormRect (fun i j : Fin n => R i.succ j.succ)) *
            frobNormRect G) +
          sigmaTail *
            ((1 + |1 / R 0 0| *
                vecNorm2 (fun j : Fin n => R 0 j.succ)) *
              frobNormRect G) := by
        exact add_le_add (add_le_add hF00 hF12) hF22
    _ =
      (1 + (1 + |1 / R 0 0| *
            frobNormRect (fun i j : Fin n => R i.succ j.succ)) +
          sigmaTail *
            (1 + |1 / R 0 0| *
              vecNorm2 (fun j : Fin n => R 0 j.succ))) *
        frobNormRect G := by
        ring

/-- Recursive adapter for the top-row/trailing-block induction route.

It packages the visible coefficient from `step_visible_factors` as a reusable
`StewartQRLinearInverseBound` whenever that coefficient is absorbed by a target
budget `sigmaNext`. -/
theorem StewartQRLinearInverseBound.step_of_visible_factor_le
    {n : ℕ} {R : Fin (n + 1) → Fin (n + 1) → ℝ}
    {sigmaTail sigmaNext : ℝ}
    (hTail :
      StewartQRLinearInverseBound n
        (fun i j : Fin n => R i.succ j.succ) sigmaTail)
    (hsigmaTail : 0 ≤ sigmaTail)
    (hR_upper : QRUpperTriangular (n + 1) R)
    (hR00 : R 0 0 ≠ 0)
    (hfactor :
      1 + (1 + |1 / R 0 0| *
            frobNormRect (fun i j : Fin n => R i.succ j.succ)) +
          sigmaTail *
            (1 + |1 / R 0 0| *
              vecNorm2 (fun j : Fin n => R 0 j.succ)) ≤ sigmaNext) :
    StewartQRLinearInverseBound (n + 1) R sigmaNext := by
  refine ⟨?_⟩
  intro F G hF_upper hT
  have hvisible :
      frobNormRect F ≤
        (1 + (1 + |1 / R 0 0| *
              frobNormRect (fun i j : Fin n => R i.succ j.succ)) +
            sigmaTail *
              (1 + |1 / R 0 0| *
                vecNorm2 (fun j : Fin n => R 0 j.succ))) *
          frobNormRect G :=
    StewartQRLinearInverseBound.step_visible_factors
      (n := n) (R := R) (F := F) (G := G) (sigmaTail := sigmaTail)
      hTail hsigmaTail hR_upper hF_upper hR00 hT
  exact le_trans hvisible
    (mul_le_mul_of_nonneg_right hfactor (frobNormRect_nonneg G))

/-- Source-constant-facing form of the top-row/trailing-block recursive
adapter. -/
theorem StewartQRLinearInverseBound.step_of_source_constant_factor_le
    {n : ℕ} {R : Fin (n + 1) → Fin (n + 1) → ℝ}
    {sigmaTail kappa : ℝ}
    (hTail :
      StewartQRLinearInverseBound n
        (fun i j : Fin n => R i.succ j.succ) sigmaTail)
    (hsigmaTail : 0 ≤ sigmaTail)
    (hR_upper : QRUpperTriangular (n + 1) R)
    (hR00 : R 0 0 ≠ 0)
    (hfactor :
      1 + (1 + |1 / R 0 0| *
            frobNormRect (fun i j : Fin n => R i.succ j.succ)) +
          sigmaTail *
            (1 + |1 / R 0 0| *
              vecNorm2 (fun j : Fin n => R 0 j.succ)) ≤
        stewartQRLinearInverseConstant (n + 1) kappa) :
    StewartQRLinearInverseBound (n + 1) R
      (stewartQRLinearInverseConstant (n + 1) kappa) :=
  StewartQRLinearInverseBound.step_of_visible_factor_le
    (n := n) (R := R) (sigmaTail := sigmaTail)
    (sigmaNext := stewartQRLinearInverseConstant (n + 1) kappa)
    hTail hsigmaTail hR_upper hR00 hfactor

/-- A rectangular operator-2 bound controls the Frobenius norm by the square
    root of the number of rows. -/
theorem frobNormRect_le_sqrt_rows_mul_of_rectOpNorm2Le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) {A2 : ℝ}
    (hA2_nonneg : 0 ≤ A2) (hA2 : rectOpNorm2Le A A2) :
    frobNormRect A ≤ Real.sqrt (m : ℝ) * A2 := by
  have hAt : rectOpNorm2Le (finiteTranspose A) A2 :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le A hA2_nonneg hA2
  have h :=
    frobNormRect_le_sqrt_cols_mul_of_rectOpNorm2Le
      (finiteTranspose A) hA2_nonneg hAt
  simpa [frobNormRect_finiteTranspose] using h

/-- Conditional `kappa_F`-to-`kappa_2` bridge for rectangular QR data.

    If the source's Frobenius condition quantity is bounded by
    `||A||_F * Aplus2`, and the spectral condition quantity `kappa2` dominates
    `A2 * Aplus2`, then a rectangular operator-2 certificate for `A` gives
    `kappa_F <= sqrt(n) * kappa2`.  This theorem does not define Stewart's
    condition number; it closes only the visible finite-dimensional comparison
    under explicit interpretation hypotheses. -/
theorem rectangularKappaF_le_sqrt_cols_mul_kappa2_of_rectOpNorm2Le {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    {A2 Aplus2 kappaF kappa2 : ℝ}
    (hA2_nonneg : 0 ≤ A2)
    (hAplus2_nonneg : 0 ≤ Aplus2)
    (hA2 : rectOpNorm2Le A A2)
    (hkappaF : kappaF ≤ frobNormRect A * Aplus2)
    (hkappa2 : A2 * Aplus2 ≤ kappa2) :
    kappaF ≤ Real.sqrt (n : ℝ) * kappa2 := by
  have hFrob :
      frobNormRect A ≤ Real.sqrt (n : ℝ) * A2 :=
    frobNormRect_le_sqrt_cols_mul_of_rectOpNorm2Le
      A hA2_nonneg hA2
  calc
    kappaF ≤ frobNormRect A * Aplus2 := hkappaF
    _ ≤ (Real.sqrt (n : ℝ) * A2) * Aplus2 :=
        mul_le_mul_of_nonneg_right hFrob hAplus2_nonneg
    _ = Real.sqrt (n : ℝ) * (A2 * Aplus2) := by ring
    _ ≤ Real.sqrt (n : ℝ) * kappa2 :=
        mul_le_mul_of_nonneg_left hkappa2 (Real.sqrt_nonneg _)

/-- Source-facing ordinary Frobenius/pseudoinverse condition surface for a
    rectangular full-column-rank matrix.

    This definition records the condition-number interpretation suggested by
    Higham's ordinary `κ_F` notation: a Frobenius norm of `A` multiplied by an
    exposed operator-2 bound for the pseudoinverse.  It is not by itself
    Stewart's perturbation theorem; the source theorem must still identify that
    its `κ_F(A)` is bounded by, or equal to, this surface. -/
noncomputable def rectangularFrobeniusPseudoinverseCondition {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (Aplus2 : ℝ) : ℝ :=
  frobNormRect A * Aplus2

/-- Stewart 1977's Frobenius QR condition quantity.

    In Stewart, "Perturbation Bounds for the QR Factorization of a Matrix",
    SIAM J. Numer. Anal. 14(3), 509--518, Theorem 3.1 uses the Frobenius norm
    throughout and defines `κ(A)=||A||||A†||`.  Thus the source-faithful
    Frobenius condition number uses the Frobenius norm of the pseudoinverse
    matrix, not only an operator-2 certificate for it. -/
noncomputable def stewartFrobeniusPseudoinverseCondition {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (Aplus : Fin n → Fin m → ℝ) : ℝ :=
  frobNormRect A * frobNormRect Aplus

/-- Source-facing ordinary spectral/pseudoinverse condition surface for a
    rectangular full-column-rank matrix, written from exposed operator-2
    budgets for `A` and its pseudoinverse. -/
noncomputable def rectangularSpectralPseudoinverseCondition
    (A2 Aplus2 : ℝ) : ℝ :=
  A2 * Aplus2

/-- Stewart 1977 source constant for the relative `R`-factor part of the
    Frobenius QR perturbation theorem.

    Theorem 3.1 gives `||F|| <= 2σ||E||`, with
    `σ = n(2 + sqrt(2))κ(R)` and `κ(R)=κ(A)`.  Dividing by
    `||R||_F=||A||_F` gives the Higham-style relative factor
    `2*n*(2+sqrt(2))*κ(A)*||E||_F/||A||_F`. -/
noncomputable def stewartQRFactorRelativeConstant (n : ℕ) : ℝ :=
  2 * (n : ℝ) * (2 + Real.sqrt 2)

/-- The Stewart 1977 source constant is nonnegative. -/
theorem stewartQRFactorRelativeConstant_nonneg (n : ℕ) :
    0 ≤ stewartQRFactorRelativeConstant n := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hs : 0 ≤ 2 + Real.sqrt 2 := by
    have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    linarith
  unfold stewartQRFactorRelativeConstant
  exact mul_nonneg (mul_nonneg (by norm_num) hn) hs

/-- A source-readable relative smallness radius sufficient for Stewart
    Theorem 3.1 after bounding `F₁` by Theorem 2.2.

    Stewart states the hypotheses as `||A†||||E|| < 1/2` and
    `τ||F₁|| < 1/4`, with
    `τ = n||R⁻¹||(1 + κ(R)/sqrt(2))` and
    `||F₁|| <= n(2+sqrt(2))κ(R)||E||`.  Using `||A||_F=||R||_F` and
    `κ(A)=κ(R)`, this relative radius is a sufficient displayed
    `||E||_F/||A||_F` cap.  The strict inequalities of the source theorem
    must still be supplied when instantiating the perturbation theorem. -/
noncomputable def stewartQRFactorRelativeSmallRadius (n : ℕ)
    (kappaF : ℝ) : ℝ :=
  min ((2 * kappaF)⁻¹)
    ((4 * (n : ℝ) ^ 2 * (2 + Real.sqrt 2) * kappaF ^ 2 *
        (1 + kappaF / Real.sqrt 2))⁻¹)

/-- The Stewart smallness radius is bounded by the source
    `||A†||||E|| <= 1/2` cap, written in relative `kappa_F` form. -/
theorem stewartQRFactorRelativeSmallRadius_le_half_radius
    (n : ℕ) (kappaF : ℝ) :
    stewartQRFactorRelativeSmallRadius n kappaF ≤ (2 * kappaF)⁻¹ := by
  unfold stewartQRFactorRelativeSmallRadius
  exact min_le_left _ _

/-- The Stewart smallness radius is bounded by the source
    `τ||F₁|| <= 1/4` cap after substituting the Theorem 2.2 first-correction
    estimate. -/
theorem stewartQRFactorRelativeSmallRadius_le_quarter_radius
    (n : ℕ) (kappaF : ℝ) :
    stewartQRFactorRelativeSmallRadius n kappaF ≤
      (4 * (n : ℝ) ^ 2 * (2 + Real.sqrt 2) * kappaF ^ 2 *
        (1 + kappaF / Real.sqrt 2))⁻¹ := by
  unfold stewartQRFactorRelativeSmallRadius
  exact min_le_right _ _

/-- The displayed sufficient Stewart smallness radius is nonnegative for
    nonnegative condition quantity. -/
theorem stewartQRFactorRelativeSmallRadius_nonneg
    (n : ℕ) {kappaF : ℝ} (hkappaF : 0 ≤ kappaF) :
    0 ≤ stewartQRFactorRelativeSmallRadius n kappaF := by
  unfold stewartQRFactorRelativeSmallRadius
  refine le_min ?_ ?_
  · exact inv_nonneg.mpr (mul_nonneg (by norm_num) hkappaF)
  · have hn2 : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg (n : ℝ)
    have hs : 0 ≤ 2 + Real.sqrt 2 := by
      have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      linarith
    have hk2 : 0 ≤ kappaF ^ 2 := sq_nonneg kappaF
    have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hdiv : 0 ≤ kappaF / Real.sqrt 2 :=
      div_nonneg hkappaF (le_of_lt hsqrt2_pos)
    have hlast : 0 ≤ 1 + kappaF / Real.sqrt 2 := by linarith
    exact inv_nonneg.mpr
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) hn2)
            hs)
          hk2)
        hlast)

/-- The displayed sufficient Stewart smallness radius is positive for a
    positive dimension and positive Frobenius condition quantity. -/
theorem stewartQRFactorRelativeSmallRadius_pos
    {n : ℕ} {kappaF : ℝ} (hn : 0 < n) (hkappaF : 0 < kappaF) :
    0 < stewartQRFactorRelativeSmallRadius n kappaF := by
  unfold stewartQRFactorRelativeSmallRadius
  refine lt_min ?_ ?_
  · exact inv_pos.mpr (mul_pos (by norm_num) hkappaF)
  · have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hn2 : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hn_pos
    have hs : 0 < 2 + Real.sqrt 2 := by
      have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      linarith
    have hk2 : 0 < kappaF ^ 2 := sq_pos_of_pos hkappaF
    have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hdiv : 0 < kappaF / Real.sqrt 2 :=
      div_pos hkappaF hsqrt2_pos
    have hlast : 0 < 1 + kappaF / Real.sqrt 2 := by linarith
    exact inv_pos.mpr
      (mul_pos
        (mul_pos
          (mul_pos
            (mul_pos (by norm_num) hn2)
            hs)
          hk2)
        hlast)

/-- If the relative data perturbation is below Stewart's displayed smallness
    radius, then the first source smallness condition is met in non-strict
    form: `kappa_F * relA <= 1/2`. -/
theorem stewartQRFactorRelativeSmallness_first_le_half
    (n : ℕ) {kappaF relA : ℝ}
    (hkappaF : 0 ≤ kappaF)
    (hsmall : relA ≤ stewartQRFactorRelativeSmallRadius n kappaF) :
    kappaF * relA ≤ 1 / 2 := by
  have hle_inv :
      relA ≤ (2 * kappaF)⁻¹ :=
    le_trans hsmall
      (stewartQRFactorRelativeSmallRadius_le_half_radius n kappaF)
  by_cases hkzero : kappaF = 0
  · simp [hkzero]
  · have hkpos : 0 < kappaF := lt_of_le_of_ne hkappaF (Ne.symm hkzero)
    have hmul := mul_le_mul_of_nonneg_left hle_inv hkappaF
    have hcalc : kappaF * (2 * kappaF)⁻¹ = 1 / 2 := by
      field_simp [ne_of_gt hkpos]
    nlinarith

/-- Strict source-smallness form of
    `stewartQRFactorRelativeSmallness_first_le_half`. -/
theorem stewartQRFactorRelativeSmallness_first_lt_half
    (n : ℕ) {kappaF relA : ℝ}
    (hkappaF : 0 ≤ kappaF)
    (hsmall : relA < stewartQRFactorRelativeSmallRadius n kappaF) :
    kappaF * relA < 1 / 2 := by
  have hlt_inv :
      relA < (2 * kappaF)⁻¹ :=
    lt_of_lt_of_le hsmall
      (stewartQRFactorRelativeSmallRadius_le_half_radius n kappaF)
  by_cases hkzero : kappaF = 0
  · simp [hkzero]
  · have hkpos : 0 < kappaF := lt_of_le_of_ne hkappaF (Ne.symm hkzero)
    have hmul := mul_lt_mul_of_pos_left hlt_inv hkpos
    have hcalc : kappaF * (2 * kappaF)⁻¹ = 1 / 2 := by
      field_simp [ne_of_gt hkpos]
    nlinarith

/-- If the relative data perturbation is below Stewart's displayed smallness
    radius, then the substituted `τ||F₁|| <= 1/4` source condition is met in
    non-strict form. -/
theorem stewartQRFactorRelativeSmallness_second_le_quarter
    (n : ℕ) {kappaF relA : ℝ}
    (hkappaF : 0 ≤ kappaF)
    (hsmall : relA ≤ stewartQRFactorRelativeSmallRadius n kappaF) :
    (n : ℝ) ^ 2 * (2 + Real.sqrt 2) * kappaF ^ 2 *
        (1 + kappaF / Real.sqrt 2) * relA ≤ 1 / 4 := by
  let denom : ℝ :=
    4 * (n : ℝ) ^ 2 * (2 + Real.sqrt 2) * kappaF ^ 2 *
      (1 + kappaF / Real.sqrt 2)
  have hle_inv : relA ≤ denom⁻¹ := by
    exact le_trans hsmall
      (by
        unfold stewartQRFactorRelativeSmallRadius
        exact min_le_right _ _)
  have hn2 : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg (n : ℝ)
  have hs : 0 ≤ 2 + Real.sqrt 2 := by
    have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    linarith
  have hk2 : 0 ≤ kappaF ^ 2 := sq_nonneg kappaF
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hdiv : 0 ≤ kappaF / Real.sqrt 2 :=
    div_nonneg hkappaF (le_of_lt hsqrt2_pos)
  have hlast : 0 ≤ 1 + kappaF / Real.sqrt 2 := by linarith
  let base : ℝ :=
    (n : ℝ) ^ 2 * (2 + Real.sqrt 2) * kappaF ^ 2 *
      (1 + kappaF / Real.sqrt 2)
  have hbase_nonneg : 0 ≤ base := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hn2 hs) hk2)
      hlast
  have hden_eq : denom = 4 * base := by
    simp [denom, base, mul_assoc]
  by_cases hbase_zero : base = 0
  · simp [base, hbase_zero]
  · have hbase_pos : 0 < base :=
      lt_of_le_of_ne hbase_nonneg (Ne.symm hbase_zero)
    have hmul := mul_le_mul_of_nonneg_left hle_inv hbase_nonneg
    have hcalc : base * denom⁻¹ = 1 / 4 := by
      rw [hden_eq]
      field_simp [ne_of_gt hbase_pos]
    have htarget : base * relA ≤ 1 / 4 := by
      nlinarith
    simpa [base, mul_assoc] using htarget

/-- Strict source-smallness form of
    `stewartQRFactorRelativeSmallness_second_le_quarter`. -/
theorem stewartQRFactorRelativeSmallness_second_lt_quarter
    (n : ℕ) {kappaF relA : ℝ}
    (hkappaF : 0 ≤ kappaF)
    (hsmall : relA < stewartQRFactorRelativeSmallRadius n kappaF) :
    (n : ℝ) ^ 2 * (2 + Real.sqrt 2) * kappaF ^ 2 *
        (1 + kappaF / Real.sqrt 2) * relA < 1 / 4 := by
  let denom : ℝ :=
    4 * (n : ℝ) ^ 2 * (2 + Real.sqrt 2) * kappaF ^ 2 *
      (1 + kappaF / Real.sqrt 2)
  have hlt_inv : relA < denom⁻¹ := by
    exact lt_of_lt_of_le hsmall
      (by
        unfold stewartQRFactorRelativeSmallRadius
        exact min_le_right _ _)
  have hn2 : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg (n : ℝ)
  have hs : 0 ≤ 2 + Real.sqrt 2 := by
    have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    linarith
  have hk2 : 0 ≤ kappaF ^ 2 := sq_nonneg kappaF
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hdiv : 0 ≤ kappaF / Real.sqrt 2 :=
    div_nonneg hkappaF (le_of_lt hsqrt2_pos)
  have hlast : 0 ≤ 1 + kappaF / Real.sqrt 2 := by linarith
  let base : ℝ :=
    (n : ℝ) ^ 2 * (2 + Real.sqrt 2) * kappaF ^ 2 *
      (1 + kappaF / Real.sqrt 2)
  have hbase_nonneg : 0 ≤ base := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hn2 hs) hk2)
      hlast
  have hden_eq : denom = 4 * base := by
    simp [denom, base, mul_assoc]
  by_cases hbase_zero : base = 0
  · simp [base, hbase_zero]
  · have hbase_pos : 0 < base :=
      lt_of_le_of_ne hbase_nonneg (Ne.symm hbase_zero)
    have hmul := mul_lt_mul_of_pos_left hlt_inv hbase_pos
    have hcalc : base * denom⁻¹ = 1 / 4 := by
      rw [hden_eq]
      field_simp [ne_of_gt hbase_pos]
    have htarget : base * relA < 1 / 4 := by
      nlinarith
    simpa [base, mul_assoc] using htarget

/-- The source-faithful Stewart Frobenius condition surface is controlled by
    `n * κ₂` under operator-2 certificates for `A` and its pseudoinverse.

    This is the finite-dimensional bridge appropriate to Stewart's definition
    `κ(A)=||A||_F||A†||_F`: both Frobenius factors cost `sqrt(n)` for an
    `m x n` full-column-rank matrix and its `n x m` pseudoinverse, so the
    comparison factor is `n`, not `sqrt(n)`. -/
theorem stewartFrobeniusPseudoinverseCondition_le_cols_mul_spectral
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (Aplus : Fin n → Fin m → ℝ)
    {A2 Aplus2 : ℝ}
    (hA2_nonneg : 0 ≤ A2)
    (hAplus2_nonneg : 0 ≤ Aplus2)
    (hA2 : rectOpNorm2Le A A2)
    (hAplus2 : rectOpNorm2Le Aplus Aplus2) :
    stewartFrobeniusPseudoinverseCondition A Aplus ≤
      (n : ℝ) * rectangularSpectralPseudoinverseCondition A2 Aplus2 := by
  have hA :
      frobNormRect A ≤ Real.sqrt (n : ℝ) * A2 :=
    frobNormRect_le_sqrt_cols_mul_of_rectOpNorm2Le
      A hA2_nonneg hA2
  have hAplus :
      frobNormRect Aplus ≤ Real.sqrt (n : ℝ) * Aplus2 :=
    frobNormRect_le_sqrt_rows_mul_of_rectOpNorm2Le
      Aplus hAplus2_nonneg hAplus2
  calc
    stewartFrobeniusPseudoinverseCondition A Aplus
        = frobNormRect A * frobNormRect Aplus := rfl
    _ ≤ (Real.sqrt (n : ℝ) * A2) * frobNormRect Aplus :=
        mul_le_mul_of_nonneg_right hA (frobNormRect_nonneg Aplus)
    _ ≤ (Real.sqrt (n : ℝ) * A2) *
          (Real.sqrt (n : ℝ) * Aplus2) :=
        mul_le_mul_of_nonneg_left hAplus
          (mul_nonneg (Real.sqrt_nonneg _) hA2_nonneg)
    _ = (Real.sqrt (n : ℝ) ^ 2) * (A2 * Aplus2) := by ring
    _ = (n : ℝ) * (A2 * Aplus2) := by
        rw [Real.sq_sqrt (Nat.cast_nonneg n)]
    _ = (n : ℝ) *
          rectangularSpectralPseudoinverseCondition A2 Aplus2 := rfl

/-- `10 x 6` specialization of the Stewart 1977 source-faithful
    Frobenius-to-spectral condition bridge. -/
theorem stewartFrobeniusPseudoinverseCondition_le_six_mul_spectral
    (A : Fin 10 → Fin 6 → ℝ) (Aplus : Fin 6 → Fin 10 → ℝ)
    {A2 Aplus2 : ℝ}
    (hA2_nonneg : 0 ≤ A2)
    (hAplus2_nonneg : 0 ≤ Aplus2)
    (hA2 : rectOpNorm2Le A A2)
    (hAplus2 : rectOpNorm2Le Aplus Aplus2) :
    stewartFrobeniusPseudoinverseCondition A Aplus ≤
      (6 : ℝ) * rectangularSpectralPseudoinverseCondition A2 Aplus2 := by
  simpa using
    (stewartFrobeniusPseudoinverseCondition_le_cols_mul_spectral
      (m := 10) (n := 6) A Aplus hA2_nonneg hAplus2_nonneg hA2 hAplus2)

/-- The ordinary Frobenius/pseudoinverse condition surface is at most
    `sqrt(n)` times the spectral/pseudoinverse surface when `A2` is an
    operator-2 bound for an `m x n` matrix `A`.

    This closes the condition-quantity bridge under the explicit ordinary
    Frobenius/spectral interpretation, without adding any Stewart perturbation
    theorem or hidden assumption. -/
theorem rectangularFrobeniusPseudoinverseCondition_le_sqrt_cols_mul_spectral
    {m n : ℕ} (A : Fin m → Fin n → ℝ) {A2 Aplus2 : ℝ}
    (hA2_nonneg : 0 ≤ A2)
    (hAplus2_nonneg : 0 ≤ Aplus2)
    (hA2 : rectOpNorm2Le A A2) :
    rectangularFrobeniusPseudoinverseCondition A Aplus2 ≤
      Real.sqrt (n : ℝ) *
        rectangularSpectralPseudoinverseCondition A2 Aplus2 := by
  exact
    rectangularKappaF_le_sqrt_cols_mul_kappa2_of_rectOpNorm2Le
      A hA2_nonneg hAplus2_nonneg hA2 le_rfl le_rfl

/-- `10 x 6` specialization of the ordinary Frobenius/spectral
    condition-surface bridge used by the Chapter 1 QR example. -/
theorem rectangularFrobeniusPseudoinverseCondition_le_sqrt_six_mul_spectral
    (A : Fin 10 → Fin 6 → ℝ) {A2 Aplus2 : ℝ}
    (hA2_nonneg : 0 ≤ A2)
    (hAplus2_nonneg : 0 ≤ Aplus2)
    (hA2 : rectOpNorm2Le A A2) :
    rectangularFrobeniusPseudoinverseCondition A Aplus2 ≤
      Real.sqrt (6 : ℝ) *
        rectangularSpectralPseudoinverseCondition A2 Aplus2 := by
  simpa using
    (rectangularFrobeniusPseudoinverseCondition_le_sqrt_cols_mul_spectral
      (m := 10) (n := 6) A hA2_nonneg hAplus2_nonneg hA2)

/-- Source-facing `10 x 6` specialization of the conditional
    `kappa_F`-to-`kappa_2` bridge.

    This removes the abstract bridge constant for the Chapter 1 example once
    the source supplies the usual interpretation hypotheses
    `kappaF <= ||A||_F * Aplus2` and `A2 * Aplus2 <= kappa2`.  It still does
    not define Stewart's `kappa_F(A)` or prove equation (18.27). -/
theorem rectangularKappaF_le_sqrt_six_mul_kappa2_of_ten_by_six_rectOpNorm2Le
    (A : Fin 10 → Fin 6 → ℝ)
    {A2 Aplus2 kappaF kappa2 : ℝ}
    (hA2_nonneg : 0 ≤ A2)
    (hAplus2_nonneg : 0 ≤ Aplus2)
    (hA2 : rectOpNorm2Le A A2)
    (hkappaF : kappaF ≤ frobNormRect A * Aplus2)
    (hkappa2 : A2 * Aplus2 ≤ kappa2) :
    kappaF ≤ Real.sqrt (6 : ℝ) * kappa2 := by
  simpa using
    (rectangularKappaF_le_sqrt_cols_mul_kappa2_of_rectOpNorm2Le
      (m := 10) (n := 6) A hA2_nonneg hAplus2_nonneg hA2
      hkappaF hkappa2)

/-- Algebraic `κ_F`-to-`κ_2` bridge for the economy-size QR-factor error
    surface.

    The theorem does not define or prove Stewart's QR condition number.  It
    records only the exact algebra needed once a source theorem supplies
    `κ_F(A)` and a separate comparison supplies
    `κ_F(A) ≤ kappaBridge * κ_2(A)`. -/
theorem EconomyQRFactorRelativeErrorLe.of_kappaF_le_bridge_kappa2 {n : ℕ}
    {R R_hat : Fin n → Fin n → ℝ}
    {cStewart kappaF kappa2 kappaBridge relA : ℝ}
    (h : EconomyQRFactorRelativeErrorLe n R R_hat
      (cStewart * kappaF * relA))
    (hcStewart : 0 ≤ cStewart)
    (hrelA : 0 ≤ relA)
    (hkappa : kappaF ≤ kappaBridge * kappa2) :
    EconomyQRFactorRelativeErrorLe n R R_hat
      (cStewart * (kappaBridge * kappa2) * relA) := by
  refine h.mono ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hkappa hcStewart) hrelA

/-- Abstract Stewart-style rectangular QR-factor perturbation certificate.

    This is the explicit missing theorem interface for Higham equation (18.27):
    whenever a computed rectangular factor `R_hat` is the exact QR `R` factor
    of a nearby matrix `A + DeltaA` through an orthogonal row factor `Q`, and
    `||DeltaA||_F` is bounded by `rho`, the corresponding rectangular `R`
    factor is within relative Frobenius radius `eta` of the reference `R`.

    The structure deliberately records a theorem obligation, not an experiment
    or hidden hypothesis.  Instantiating it requires the Stewart perturbation
    theorem, including rank, sign/diagonal, conditioning, and smallness
    assumptions. -/
structure RectangularQRFactorPerturbationBound (m n : ℕ)
    (A R R_hat : Fin m → Fin n → ℝ) (rho eta : ℝ) : Prop where
  of_backward_error :
    ∀ {Q : Fin m → Fin m → ℝ} {DeltaA : Fin m → Fin n → ℝ},
      IsOrthogonal m Q →
      (∀ i j, matMulRectLeft Q R_hat i j = A i j + DeltaA i j) →
      frobNormRect DeltaA ≤ rho →
      RectangularQRFactorRelativeErrorLe m n R R_hat eta

/-- Source-shaped Stewart QR-factor perturbation interface for Higham (18.27).

    Equation (18.27) is stated with a relative perturbation radius
    `||DeltaA||_F <= relA * ||A||_F` and returns the relative `R`-factor radius
    `cStewart * kappaF * relA`.  This structure keeps that relative form
    explicit instead of hiding it inside the absolute-radius interface
    `RectangularQRFactorPerturbationBound`.  Instantiating it still requires the
    actual Stewart theorem, including full-column-rank, economy-QR
    normalization, conditioning, and sufficiently-small perturbation
    assumptions, including the exposed smallness radius below. -/
structure RectangularQRFactorStewartRelativeBound (m n : ℕ)
    (A R R_hat : Fin m → Fin n → ℝ)
    (cStewart kappaF smallRadius : ℝ) : Prop where
  of_relative_backward_error :
    ∀ {Q : Fin m → Fin m → ℝ} {DeltaA : Fin m → Fin n → ℝ} {relA : ℝ},
      0 ≤ relA →
      IsOrthogonal m Q →
      (∀ i j, matMulRectLeft Q R_hat i j = A i j + DeltaA i j) →
      frobNormRect DeltaA ≤ relA * frobNormRect A →
      QRFactorPerturbationSmallEnough m n A DeltaA smallRadius →
      RectangularQRFactorRelativeErrorLe m n R R_hat
        (cStewart * kappaF * relA)

/-- Source-faithful Stewart QR-factor perturbation interface for the
    economy-size square `R` factor in Higham equation (18.27).

    The source assumes an `m x n` matrix of rank `n`, economy-size QR
    factorizations, and square `R` factors normalized with nonnegative
    diagonal.  The local statement keeps the proof obligation explicit:
    a full rectangular computed factor `R_hat_rect` must satisfy the same
    backward-error identity used by the Givens proof, have an exact zero bottom
    block, and expose its square top block `R_hat`.  Instantiating this
    structure still requires Stewart's perturbation theorem, including the
    full-rank, condition-number, and exposed sufficiently-small perturbation
    assumptions. -/
structure EconomyQRFactorStewartRelativeBound (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (R R_hat : Fin n → Fin n → ℝ)
    (cStewart kappaF smallRadius : ℝ) : Prop where
  of_relative_backward_error :
    ∀ {Q : Fin m → Fin m → ℝ}
      {R_hat_rect : Fin m → Fin n → ℝ}
      {DeltaA : Fin m → Fin n → ℝ} {relA : ℝ},
      (hmn : n ≤ m) →
      0 ≤ relA →
      IsOrthogonal m Q →
      (∀ i j, matMulRectLeft Q R_hat_rect i j = A i j + DeltaA i j) →
      (∀ i j, n ≤ i.val → R_hat_rect i j = 0) →
      (∀ i j, R_hat i j =
        R_hat_rect ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j) →
      (∀ i j, j.val < i.val → R i j = 0) →
      (∀ i, 0 ≤ R i i) →
      (∀ i j, j.val < i.val → R_hat i j = 0) →
      (∀ i, 0 ≤ R_hat i i) →
      frobNormRect DeltaA ≤ relA * frobNormRect A →
      QRFactorPerturbationSmallEnough m n A DeltaA smallRadius →
      EconomyQRFactorRelativeErrorLe n R R_hat
        (cStewart * kappaF * relA)

/-- Convert the source relative Stewart statement (18.27) to the absolute
    backward-error-radius interface used by the Givens QR handoff. -/
theorem RectangularQRFactorPerturbationBound.of_stewart_relative_bound
    {m n : ℕ} {A R R_hat : Fin m → Fin n → ℝ}
    {rho relA cStewart kappaF smallRadius : ℝ}
    (hStewart :
      RectangularQRFactorStewartRelativeBound m n A R R_hat
        cStewart kappaF smallRadius)
    (hrelA : 0 ≤ relA)
    (hrelSmall : relA ≤ smallRadius)
    (hrho : rho ≤ relA * frobNormRect A) :
    RectangularQRFactorPerturbationBound m n A R R_hat rho
      (cStewart * kappaF * relA) where
  of_backward_error := by
    intro Q DeltaA hQ hQR hDelta
    have hDeltaRelA : frobNormRect DeltaA ≤ relA * frobNormRect A :=
      le_trans hDelta hrho
    have hSmall : QRFactorPerturbationSmallEnough m n A DeltaA smallRadius :=
      QRFactorPerturbationSmallEnough.of_relative_le hDeltaRelA hrelSmall
    exact hStewart.of_relative_backward_error hrelA hQ hQR
      hDeltaRelA hSmall

/-- Compose a rectangular Givens backward-error certificate with an explicit
    QR-factor perturbation certificate. -/
theorem RectangularQRFactorPerturbationBound.of_givens_backward_error
    {m n : ℕ} {A R R_hat : Fin m → Fin n → ℝ} {rho eta : ℝ}
    (hBack : RectangularGivensQRBackwardError m n A R_hat rho)
    (hPert : RectangularQRFactorPerturbationBound m n A R R_hat rho eta) :
    RectangularQRFactorRelativeErrorLe m n R R_hat eta := by
  rcases hBack.result with ⟨Q, DeltaA, hQ, hQR, hDelta⟩
  exact hPert.of_backward_error hQ hQR hDelta

/-- Chapter 1 `10 x 6` composition of the closed Givens backward-error bound
    with a Stewart-style QR-factor perturbation certificate.

    The result is the theorem-level handoff for §1.14.2: once the missing
    equation-(18.27) perturbation theorem supplies
    `RectangularQRFactorPerturbationBound` at radius
    `(2^39 - 1) * u * ||A||_F` and relative factor
    `cStewart * kappaF * ((2^39 - 1) * u)`, the final rectangular `R` factor
    has the corresponding relative Frobenius error.  The hidden Figure 1.5
    machine trace is not used here. -/
theorem rectangular_givens_qr_backward_ten_by_six_unit_roundoff_qr_factor_relative_error
    (A R R_hat : Fin 10 → Fin 6 → ℝ) (c u cStewart kappaF : ℝ)
    (hc0 : 0 ≤ c) (hcu : c ≤ u) (hu1 : u ≤ 1)
    (hSeq : RectangularGivensSequenceBackwardError 10 6 A R_hat
      (givensQRRectangularRotationCount 10 6) c)
    (hPert :
      RectangularQRFactorPerturbationBound 10 6 A R R_hat
        (((2 : ℝ) ^ 39 - 1) * u * frobNormRect A)
        (cStewart * kappaF * (((2 : ℝ) ^ 39 - 1) * u))) :
    RectangularQRFactorRelativeErrorLe 10 6 R R_hat
      (cStewart * kappaF * (((2 : ℝ) ^ 39 - 1) * u)) := by
  have hBack :
      RectangularGivensQRBackwardError 10 6 A R_hat
        (((2 : ℝ) ^ 39 - 1) * u * frobNormRect A) :=
    rectangular_givens_qr_backward_ten_by_six_unit_roundoff
      A R_hat c u hc0 hcu hu1 hSeq
  exact RectangularQRFactorPerturbationBound.of_givens_backward_error
    hBack hPert

/-- Chapter 1 `10 x 6` QR handoff directly from the source-shaped Stewart
    relative perturbation theorem.

    This is the equation-(18.27) bridge in the same relative form as the book:
    the closed Givens backward-error radius is
    `((2^39 - 1) * u) * ||A||_F`, so a Stewart theorem for relative data
    perturbations gives the final relative `R`-factor radius
    `cStewart * kappaF * ((2^39 - 1) * u)`. -/
theorem rectangular_givens_qr_backward_ten_by_six_unit_roundoff_qr_factor_relative_error_of_stewart
    (A R R_hat : Fin 10 → Fin 6 → ℝ)
    (c u cStewart kappaF smallRadius : ℝ)
    (hc0 : 0 ≤ c) (hcu : c ≤ u) (hu1 : u ≤ 1)
    (hrelSmall : (((2 : ℝ) ^ 39 - 1) * u) ≤ smallRadius)
    (hSeq : RectangularGivensSequenceBackwardError 10 6 A R_hat
      (givensQRRectangularRotationCount 10 6) c)
    (hStewart :
      RectangularQRFactorStewartRelativeBound 10 6 A R R_hat
        cStewart kappaF smallRadius) :
    RectangularQRFactorRelativeErrorLe 10 6 R R_hat
      (cStewart * kappaF * (((2 : ℝ) ^ 39 - 1) * u)) := by
  have hu0 : 0 ≤ u := le_trans hc0 hcu
  have hrelA_nonneg : 0 ≤ (((2 : ℝ) ^ 39 - 1) * u) :=
    mul_nonneg (two_pow_sub_one_nonneg 39) hu0
  have hPert :
      RectangularQRFactorPerturbationBound 10 6 A R R_hat
        (((2 : ℝ) ^ 39 - 1) * u * frobNormRect A)
        (cStewart * kappaF * (((2 : ℝ) ^ 39 - 1) * u)) :=
    RectangularQRFactorPerturbationBound.of_stewart_relative_bound
      (A := A) (R := R) (R_hat := R_hat)
      (rho := (((2 : ℝ) ^ 39 - 1) * u * frobNormRect A))
      (relA := (((2 : ℝ) ^ 39 - 1) * u))
      hStewart hrelA_nonneg hrelSmall (by rfl)
  exact
    rectangular_givens_qr_backward_ten_by_six_unit_roundoff_qr_factor_relative_error
      A R R_hat c u cStewart kappaF hc0 hcu hu1 hSeq hPert

/-- Chapter 1 `10 x 6` QR handoff in the economy-size square-`R` shape of
    Higham equation (18.27).

    This theorem corrects the source surface from a full rectangular
    `10 x 6` `R` comparison to the square top-block comparison used in
    Stewart's perturbation result.  The hidden Figure 1.5 data remain
    empirical; the theorem consumes only the closed Givens backward-error
    certificate, explicit rectangular-to-top-block shape facts for the computed
    factor, and the still-missing source theorem packaged as
    `EconomyQRFactorStewartRelativeBound`. -/
theorem rectangular_givens_qr_backward_ten_by_six_unit_roundoff_economy_qr_factor_relative_error_of_stewart
    (A R_hat_rect : Fin 10 → Fin 6 → ℝ)
    (R R_hat : Fin 6 → Fin 6 → ℝ)
    (c u cStewart kappaF smallRadius : ℝ)
    (hc0 : 0 ≤ c) (hcu : c ≤ u) (hu1 : u ≤ 1)
    (hrelSmall : (((2 : ℝ) ^ 39 - 1) * u) ≤ smallRadius)
    (hSeq : RectangularGivensSequenceBackwardError 10 6 A R_hat_rect
      (givensQRRectangularRotationCount 10 6) c)
    (hbottom : ∀ i j, (6 : ℕ) ≤ i.val → R_hat_rect i j = 0)
    (htop : ∀ i j, R_hat i j =
      R_hat_rect ⟨i.val, lt_of_lt_of_le i.isLt (by norm_num : 6 ≤ 10)⟩ j)
    (hR_upper : ∀ i j, j.val < i.val → R i j = 0)
    (hR_diag_nonneg : ∀ i, 0 ≤ R i i)
    (hRhat_upper : ∀ i j, j.val < i.val → R_hat i j = 0)
    (hRhat_diag_nonneg : ∀ i, 0 ≤ R_hat i i)
    (hStewart :
      EconomyQRFactorStewartRelativeBound 10 6 A R R_hat
        cStewart kappaF smallRadius) :
    EconomyQRFactorRelativeErrorLe 6 R R_hat
      (cStewart * kappaF * (((2 : ℝ) ^ 39 - 1) * u)) := by
  have hu0 : 0 ≤ u := le_trans hc0 hcu
  have hrelA_nonneg : 0 ≤ (((2 : ℝ) ^ 39 - 1) * u) :=
    mul_nonneg (two_pow_sub_one_nonneg 39) hu0
  obtain ⟨Q, DeltaA, hQ, hQR, hDelta⟩ :=
    (rectangular_givens_qr_backward_ten_by_six_unit_roundoff
      A R_hat_rect c u hc0 hcu hu1 hSeq).result
  have hDeltaRelA : frobNormRect DeltaA ≤
      (((2 : ℝ) ^ 39 - 1) * u) * frobNormRect A := by
    simpa [mul_assoc] using hDelta
  have hSmall :
      QRFactorPerturbationSmallEnough 10 6 A DeltaA smallRadius :=
    QRFactorPerturbationSmallEnough.of_relative_le hDeltaRelA hrelSmall
  exact hStewart.of_relative_backward_error
    (by norm_num : 6 ≤ 10)
    hrelA_nonneg hQ hQR hbottom htop hR_upper hR_diag_nonneg
    hRhat_upper hRhat_diag_nonneg
    hDeltaRelA hSmall

/-- Chapter 1 `10 x 6` economy-QR handoff with an explicit `κ_F`-to-`κ_2`
    comparison hypothesis.

    Higham's Chapter 18 source equation (18.27) is Stewart's Frobenius
    condition-number statement, while the Chapter 1 prose phrases the final
    explanation with `κ_2(A)u`/`O(u)`.  This theorem closes the algebraic
    conversion layer: once the source-shaped Stewart theorem is available and a
    separate QR condition-number comparison proves
    `kappaF ≤ kappaBridge * kappa2`, the closed `10 x 6` Givens backward-error
    bridge yields the corresponding economy-size `R` relative-error bound in
    the Chapter 1 `κ_2` form. -/
theorem rectangular_givens_qr_backward_ten_by_six_unit_roundoff_economy_qr_factor_relative_error_of_stewart_kappa2_bridge
    (A R_hat_rect : Fin 10 → Fin 6 → ℝ)
    (R R_hat : Fin 6 → Fin 6 → ℝ)
    (c u cStewart kappaF kappa2 kappaBridge smallRadius : ℝ)
    (hc0 : 0 ≤ c) (hcu : c ≤ u) (hu1 : u ≤ 1)
    (hcStewart : 0 ≤ cStewart)
    (hkappa : kappaF ≤ kappaBridge * kappa2)
    (hrelSmall : (((2 : ℝ) ^ 39 - 1) * u) ≤ smallRadius)
    (hSeq : RectangularGivensSequenceBackwardError 10 6 A R_hat_rect
      (givensQRRectangularRotationCount 10 6) c)
    (hbottom : ∀ i j, (6 : ℕ) ≤ i.val → R_hat_rect i j = 0)
    (htop : ∀ i j, R_hat i j =
      R_hat_rect ⟨i.val, lt_of_lt_of_le i.isLt (by norm_num : 6 ≤ 10)⟩ j)
    (hR_upper : ∀ i j, j.val < i.val → R i j = 0)
    (hR_diag_nonneg : ∀ i, 0 ≤ R i i)
    (hRhat_upper : ∀ i j, j.val < i.val → R_hat i j = 0)
    (hRhat_diag_nonneg : ∀ i, 0 ≤ R_hat i i)
    (hStewart :
      EconomyQRFactorStewartRelativeBound 10 6 A R R_hat
        cStewart kappaF smallRadius) :
    EconomyQRFactorRelativeErrorLe 6 R R_hat
      (cStewart * (kappaBridge * kappa2) *
        (((2 : ℝ) ^ 39 - 1) * u)) := by
  have hF :
      EconomyQRFactorRelativeErrorLe 6 R R_hat
        (cStewart * kappaF * (((2 : ℝ) ^ 39 - 1) * u)) :=
    rectangular_givens_qr_backward_ten_by_six_unit_roundoff_economy_qr_factor_relative_error_of_stewart
      A R_hat_rect R R_hat c u cStewart kappaF smallRadius
      hc0 hcu hu1 hrelSmall hSeq hbottom htop hR_upper hR_diag_nonneg hRhat_upper
      hRhat_diag_nonneg hStewart
  have hu0 : 0 ≤ u := le_trans hc0 hcu
  have hrelA_nonneg : 0 ≤ (((2 : ℝ) ^ 39 - 1) * u) :=
    mul_nonneg (two_pow_sub_one_nonneg 39) hu0
  exact EconomyQRFactorRelativeErrorLe.of_kappaF_le_bridge_kappa2
    hF hcStewart hrelA_nonneg hkappa

/-- Algebraic cleanup for the Chapter 1 `10 x 6` Stewart/`κ_2` QR radius.

    It exposes the already-proved conditional radius as a fixed source
    constant times the unit roundoff `u`, matching the §1.14.2 `κ_2(A)u`/
    `O(u)` prose without hiding the still-required Stewart theorem or the
    `κ_F`-to-`κ_2` comparison. -/
theorem qrTenBySixStewartKappa2LinearUnitRoundoffRadius_eq
    (cStewart kappaBridge kappa2 u : ℝ) :
    cStewart * (kappaBridge * kappa2) *
        (((2 : ℝ) ^ 39 - 1) * u) =
      (cStewart * ((2 : ℝ) ^ 39 - 1) * kappaBridge * kappa2) * u := by
  ring

/-- Unit-roundoff cap that discharges the exposed Stewart smallness premise in
    the Chapter 1 `10 x 6` QR handoff.

    Once the source theorem supplies a Stewart smallness radius `smallRadius`,
    it is enough to assume
    `u <= smallRadius / (2^39 - 1)` for the closed Givens relative data radius
    `(2^39 - 1)u` to be small enough. -/
theorem qrTenBySixStewartRelativeRadius_le_of_unitRoundoff_le_smallRadius_div
    {u smallRadius : ℝ}
    (huSmall : u ≤ smallRadius / (((2 : ℝ) ^ 39 - 1))) :
    (((2 : ℝ) ^ 39 - 1) * u) ≤ smallRadius := by
  have hpos : 0 < ((2 : ℝ) ^ 39 - 1) := by norm_num
  calc
    ((2 : ℝ) ^ 39 - 1) * u
        ≤ ((2 : ℝ) ^ 39 - 1) *
            (smallRadius / (((2 : ℝ) ^ 39 - 1))) :=
          mul_le_mul_of_nonneg_left huSmall (le_of_lt hpos)
    _ = smallRadius := by field_simp [ne_of_gt hpos]

/-- Strict unit-roundoff cap for Stewart Theorem 3.1's strict smallness
    hypotheses in the Chapter 1 `10 x 6` QR handoff. -/
theorem qrTenBySixStewartRelativeRadius_lt_of_unitRoundoff_lt_smallRadius_div
    {u smallRadius : ℝ}
    (huSmall : u < smallRadius / (((2 : ℝ) ^ 39 - 1))) :
    (((2 : ℝ) ^ 39 - 1) * u) < smallRadius := by
  have hpos : 0 < ((2 : ℝ) ^ 39 - 1) := by norm_num
  calc
    ((2 : ℝ) ^ 39 - 1) * u
        < ((2 : ℝ) ^ 39 - 1) *
            (smallRadius / (((2 : ℝ) ^ 39 - 1))) :=
          mul_lt_mul_of_pos_left huSmall hpos
    _ = smallRadius := by field_simp [ne_of_gt hpos]

/-- Chapter 1 `10 x 6` economy-QR handoff in explicit linear-in-unit-roundoff
    form.

    The theorem is still conditional on a supplied Stewart perturbation
    certificate and a supplied `κ_F <= kappaBridge * κ_2` comparison.  Its
    contribution is only the source-readable final radius
    `(cStewart * (2^39 - 1) * kappaBridge * kappa2) * u`. -/
theorem rectangular_givens_qr_backward_ten_by_six_unit_roundoff_economy_qr_factor_relative_error_of_stewart_kappa2_bridge_linear_u
    (A R_hat_rect : Fin 10 → Fin 6 → ℝ)
    (R R_hat : Fin 6 → Fin 6 → ℝ)
    (c u cStewart kappaF kappa2 kappaBridge smallRadius : ℝ)
    (hc0 : 0 ≤ c) (hcu : c ≤ u) (hu1 : u ≤ 1)
    (hcStewart : 0 ≤ cStewart)
    (hkappa : kappaF ≤ kappaBridge * kappa2)
    (hrelSmall : (((2 : ℝ) ^ 39 - 1) * u) ≤ smallRadius)
    (hSeq : RectangularGivensSequenceBackwardError 10 6 A R_hat_rect
      (givensQRRectangularRotationCount 10 6) c)
    (hbottom : ∀ i j, (6 : ℕ) ≤ i.val → R_hat_rect i j = 0)
    (htop : ∀ i j, R_hat i j =
      R_hat_rect ⟨i.val, lt_of_lt_of_le i.isLt (by norm_num : 6 ≤ 10)⟩ j)
    (hR_upper : ∀ i j, j.val < i.val → R i j = 0)
    (hR_diag_nonneg : ∀ i, 0 ≤ R i i)
    (hRhat_upper : ∀ i j, j.val < i.val → R_hat i j = 0)
    (hRhat_diag_nonneg : ∀ i, 0 ≤ R_hat i i)
    (hStewart :
      EconomyQRFactorStewartRelativeBound 10 6 A R R_hat
        cStewart kappaF smallRadius) :
    EconomyQRFactorRelativeErrorLe 6 R R_hat
      ((cStewart * ((2 : ℝ) ^ 39 - 1) * kappaBridge * kappa2) * u) := by
  have h :=
    rectangular_givens_qr_backward_ten_by_six_unit_roundoff_economy_qr_factor_relative_error_of_stewart_kappa2_bridge
      A R_hat_rect R R_hat c u cStewart kappaF kappa2 kappaBridge smallRadius
      hc0 hcu hu1 hcStewart hkappa hrelSmall hSeq hbottom htop hR_upper
      hR_diag_nonneg hRhat_upper hRhat_diag_nonneg hStewart
  simpa [qrTenBySixStewartKappa2LinearUnitRoundoffRadius_eq] using h

/-- Chapter 1 `10 x 6` economy-QR handoff with the finite-dimensional
    `sqrt(6)` comparison instantiated.

    This theorem removes the abstract `kappaBridge` parameter from the local
    Chapter 1 handoff.  It remains conditional on the actual Stewart
    perturbation theorem, the source smallness premise, and source-faithful
    interpretations of `kappaF` and `kappa2`. -/
theorem rectangular_givens_qr_backward_ten_by_six_unit_roundoff_economy_qr_factor_relative_error_of_stewart_kappa2_sqrt6_linear_u
    (A R_hat_rect : Fin 10 → Fin 6 → ℝ)
    (R R_hat : Fin 6 → Fin 6 → ℝ)
    (c u cStewart kappaF kappa2 smallRadius A2 Aplus2 : ℝ)
    (hc0 : 0 ≤ c) (hcu : c ≤ u) (hu1 : u ≤ 1)
    (hcStewart : 0 ≤ cStewart)
    (hA2_nonneg : 0 ≤ A2)
    (hAplus2_nonneg : 0 ≤ Aplus2)
    (hA2 : rectOpNorm2Le A A2)
    (hkappaF : kappaF ≤ frobNormRect A * Aplus2)
    (hkappa2 : A2 * Aplus2 ≤ kappa2)
    (hrelSmall : (((2 : ℝ) ^ 39 - 1) * u) ≤ smallRadius)
    (hSeq : RectangularGivensSequenceBackwardError 10 6 A R_hat_rect
      (givensQRRectangularRotationCount 10 6) c)
    (hbottom : ∀ i j, (6 : ℕ) ≤ i.val → R_hat_rect i j = 0)
    (htop : ∀ i j, R_hat i j =
      R_hat_rect ⟨i.val, lt_of_lt_of_le i.isLt (by norm_num : 6 ≤ 10)⟩ j)
    (hR_upper : ∀ i j, j.val < i.val → R i j = 0)
    (hR_diag_nonneg : ∀ i, 0 ≤ R i i)
    (hRhat_upper : ∀ i j, j.val < i.val → R_hat i j = 0)
    (hRhat_diag_nonneg : ∀ i, 0 ≤ R_hat i i)
    (hStewart :
      EconomyQRFactorStewartRelativeBound 10 6 A R R_hat
        cStewart kappaF smallRadius) :
    EconomyQRFactorRelativeErrorLe 6 R R_hat
      ((cStewart * ((2 : ℝ) ^ 39 - 1) * Real.sqrt (6 : ℝ) * kappa2) * u) := by
  have hkappa :
      kappaF ≤ Real.sqrt (6 : ℝ) * kappa2 :=
    rectangularKappaF_le_sqrt_six_mul_kappa2_of_ten_by_six_rectOpNorm2Le
      A hA2_nonneg hAplus2_nonneg hA2 hkappaF hkappa2
  exact
    rectangular_givens_qr_backward_ten_by_six_unit_roundoff_economy_qr_factor_relative_error_of_stewart_kappa2_bridge_linear_u
      A R_hat_rect R R_hat c u cStewart kappaF kappa2
      (Real.sqrt (6 : ℝ)) smallRadius hc0 hcu hu1 hcStewart hkappa
      hrelSmall hSeq hbottom htop hR_upper hR_diag_nonneg hRhat_upper
      hRhat_diag_nonneg hStewart

/-- Chapter 1 `10 x 6` economy-QR handoff under the ordinary
    Frobenius/spectral condition-number interpretation.

    This removes the abstract `kappaF` and `kappa2` parameters from the local
    `sqrt(6)` comparison layer by using the explicit surfaces
    `||A||_F * Aplus2` and `A2 * Aplus2`.  The theorem is still conditional on
    the actual Stewart equation-(18.27) perturbation theorem instantiated with
    that Frobenius surface, on a source smallness radius, and on the ordinary
    operator-2/pseudoinverse norm certificates. -/
theorem rectangular_givens_qr_backward_ten_by_six_unit_roundoff_economy_qr_factor_relative_error_of_stewart_condition_surfaces_linear_u
    (A R_hat_rect : Fin 10 → Fin 6 → ℝ)
    (R R_hat : Fin 6 → Fin 6 → ℝ)
    (c u cStewart smallRadius A2 Aplus2 : ℝ)
    (hc0 : 0 ≤ c) (hcu : c ≤ u) (hu1 : u ≤ 1)
    (hcStewart : 0 ≤ cStewart)
    (hA2_nonneg : 0 ≤ A2)
    (hAplus2_nonneg : 0 ≤ Aplus2)
    (hA2 : rectOpNorm2Le A A2)
    (hrelSmall : (((2 : ℝ) ^ 39 - 1) * u) ≤ smallRadius)
    (hSeq : RectangularGivensSequenceBackwardError 10 6 A R_hat_rect
      (givensQRRectangularRotationCount 10 6) c)
    (hbottom : ∀ i j, (6 : ℕ) ≤ i.val → R_hat_rect i j = 0)
    (htop : ∀ i j, R_hat i j =
      R_hat_rect ⟨i.val, lt_of_lt_of_le i.isLt (by norm_num : 6 ≤ 10)⟩ j)
    (hR_upper : ∀ i j, j.val < i.val → R i j = 0)
    (hR_diag_nonneg : ∀ i, 0 ≤ R i i)
    (hRhat_upper : ∀ i j, j.val < i.val → R_hat i j = 0)
    (hRhat_diag_nonneg : ∀ i, 0 ≤ R_hat i i)
    (hStewart :
      EconomyQRFactorStewartRelativeBound 10 6 A R R_hat
        cStewart
        (rectangularFrobeniusPseudoinverseCondition A Aplus2)
        smallRadius) :
    EconomyQRFactorRelativeErrorLe 6 R R_hat
      ((cStewart * ((2 : ℝ) ^ 39 - 1) * Real.sqrt (6 : ℝ) *
          rectangularSpectralPseudoinverseCondition A2 Aplus2) * u) := by
  exact
    rectangular_givens_qr_backward_ten_by_six_unit_roundoff_economy_qr_factor_relative_error_of_stewart_kappa2_sqrt6_linear_u
      A R_hat_rect R R_hat c u cStewart
      (rectangularFrobeniusPseudoinverseCondition A Aplus2)
      (rectangularSpectralPseudoinverseCondition A2 Aplus2)
      smallRadius A2 Aplus2 hc0 hcu hu1 hcStewart hA2_nonneg
      hAplus2_nonneg hA2 le_rfl le_rfl hrelSmall hSeq hbottom htop
      hR_upper hR_diag_nonneg hRhat_upper hRhat_diag_nonneg hStewart

/-- Chapter 1 `10 x 6` economy-QR handoff under the ordinary
    Frobenius/spectral condition-number interpretation, with the Stewart
    smallness premise stated as a direct unit-roundoff cap.

    The theorem still depends on the source theorem packaged as
    `EconomyQRFactorStewartRelativeBound`; it only removes the less readable
    premise `(2^39 - 1)u <= smallRadius` by deriving it from
    `u <= smallRadius/(2^39 - 1)`. -/
theorem rectangular_givens_qr_backward_ten_by_six_unit_roundoff_economy_qr_factor_relative_error_of_stewart_condition_surfaces_linear_u_of_unitRoundoff_le_smallRadius_div
    (A R_hat_rect : Fin 10 → Fin 6 → ℝ)
    (R R_hat : Fin 6 → Fin 6 → ℝ)
    (c u cStewart smallRadius A2 Aplus2 : ℝ)
    (hc0 : 0 ≤ c) (hcu : c ≤ u) (hu1 : u ≤ 1)
    (hcStewart : 0 ≤ cStewart)
    (hA2_nonneg : 0 ≤ A2)
    (hAplus2_nonneg : 0 ≤ Aplus2)
    (hA2 : rectOpNorm2Le A A2)
    (huSmall : u ≤ smallRadius / (((2 : ℝ) ^ 39 - 1)))
    (hSeq : RectangularGivensSequenceBackwardError 10 6 A R_hat_rect
      (givensQRRectangularRotationCount 10 6) c)
    (hbottom : ∀ i j, (6 : ℕ) ≤ i.val → R_hat_rect i j = 0)
    (htop : ∀ i j, R_hat i j =
      R_hat_rect ⟨i.val, lt_of_lt_of_le i.isLt (by norm_num : 6 ≤ 10)⟩ j)
    (hR_upper : ∀ i j, j.val < i.val → R i j = 0)
    (hR_diag_nonneg : ∀ i, 0 ≤ R i i)
    (hRhat_upper : ∀ i j, j.val < i.val → R_hat i j = 0)
    (hRhat_diag_nonneg : ∀ i, 0 ≤ R_hat i i)
    (hStewart :
      EconomyQRFactorStewartRelativeBound 10 6 A R R_hat
        cStewart
        (rectangularFrobeniusPseudoinverseCondition A Aplus2)
        smallRadius) :
    EconomyQRFactorRelativeErrorLe 6 R R_hat
      ((cStewart * ((2 : ℝ) ^ 39 - 1) * Real.sqrt (6 : ℝ) *
          rectangularSpectralPseudoinverseCondition A2 Aplus2) * u) := by
  exact
    rectangular_givens_qr_backward_ten_by_six_unit_roundoff_economy_qr_factor_relative_error_of_stewart_condition_surfaces_linear_u
      A R_hat_rect R R_hat c u cStewart smallRadius A2 Aplus2
      hc0 hcu hu1 hcStewart hA2_nonneg hAplus2_nonneg hA2
      (qrTenBySixStewartRelativeRadius_le_of_unitRoundoff_le_smallRadius_div
        huSmall)
      hSeq hbottom htop hR_upper hR_diag_nonneg hRhat_upper
      hRhat_diag_nonneg hStewart

/-- Chapter 1 `10 x 6` economy-QR handoff under Stewart 1977's actual
    Frobenius pseudoinverse condition surface.

    Stewart defines the Frobenius condition quantity as
    `||A||_F * ||A†||_F`.  Therefore the finite-dimensional comparison to the
    Chapter 1 spectral phrase costs a factor `6` for this `10 x 6` matrix,
    rather than the older mixed `||A||_F * ||A†||_2` surface's `sqrt(6)`.
    The theorem is still conditional on the source perturbation theorem
    packaged as `EconomyQRFactorStewartRelativeBound`. -/
theorem rectangular_givens_qr_backward_ten_by_six_unit_roundoff_economy_qr_factor_relative_error_of_stewart1977_frobenius_condition_surfaces_linear_u
    (A R_hat_rect : Fin 10 → Fin 6 → ℝ)
    (R R_hat : Fin 6 → Fin 6 → ℝ)
    (Aplus : Fin 6 → Fin 10 → ℝ)
    (c u cStewart smallRadius A2 Aplus2 : ℝ)
    (hc0 : 0 ≤ c) (hcu : c ≤ u) (hu1 : u ≤ 1)
    (hcStewart : 0 ≤ cStewart)
    (hA2_nonneg : 0 ≤ A2)
    (hAplus2_nonneg : 0 ≤ Aplus2)
    (hA2 : rectOpNorm2Le A A2)
    (hAplus2 : rectOpNorm2Le Aplus Aplus2)
    (hrelSmall : (((2 : ℝ) ^ 39 - 1) * u) ≤ smallRadius)
    (hSeq : RectangularGivensSequenceBackwardError 10 6 A R_hat_rect
      (givensQRRectangularRotationCount 10 6) c)
    (hbottom : ∀ i j, (6 : ℕ) ≤ i.val → R_hat_rect i j = 0)
    (htop : ∀ i j, R_hat i j =
      R_hat_rect ⟨i.val, lt_of_lt_of_le i.isLt (by norm_num : 6 ≤ 10)⟩ j)
    (hR_upper : ∀ i j, j.val < i.val → R i j = 0)
    (hR_diag_nonneg : ∀ i, 0 ≤ R i i)
    (hRhat_upper : ∀ i j, j.val < i.val → R_hat i j = 0)
    (hRhat_diag_nonneg : ∀ i, 0 ≤ R_hat i i)
    (hStewart :
      EconomyQRFactorStewartRelativeBound 10 6 A R R_hat
        cStewart
        (stewartFrobeniusPseudoinverseCondition A Aplus)
        smallRadius) :
    EconomyQRFactorRelativeErrorLe 6 R R_hat
      ((cStewart * ((2 : ℝ) ^ 39 - 1) * (6 : ℝ) *
          rectangularSpectralPseudoinverseCondition A2 Aplus2) * u) := by
  have hkappa :
      stewartFrobeniusPseudoinverseCondition A Aplus ≤
        (6 : ℝ) * rectangularSpectralPseudoinverseCondition A2 Aplus2 :=
    stewartFrobeniusPseudoinverseCondition_le_six_mul_spectral
      A Aplus hA2_nonneg hAplus2_nonneg hA2 hAplus2
  exact
    rectangular_givens_qr_backward_ten_by_six_unit_roundoff_economy_qr_factor_relative_error_of_stewart_kappa2_bridge_linear_u
      A R_hat_rect R R_hat c u cStewart
      (stewartFrobeniusPseudoinverseCondition A Aplus)
      (rectangularSpectralPseudoinverseCondition A2 Aplus2)
      (6 : ℝ) smallRadius hc0 hcu hu1 hcStewart hkappa hrelSmall
      hSeq hbottom htop hR_upper hR_diag_nonneg hRhat_upper
      hRhat_diag_nonneg hStewart

/-- Same as
    `rectangular_givens_qr_backward_ten_by_six_unit_roundoff_economy_qr_factor_relative_error_of_stewart1977_frobenius_condition_surfaces_linear_u`,
    with the Stewart smallness premise discharged from a direct unit-roundoff
    cap. -/
theorem rectangular_givens_qr_backward_ten_by_six_unit_roundoff_economy_qr_factor_relative_error_of_stewart1977_frobenius_condition_surfaces_linear_u_of_unitRoundoff_le_smallRadius_div
    (A R_hat_rect : Fin 10 → Fin 6 → ℝ)
    (R R_hat : Fin 6 → Fin 6 → ℝ)
    (Aplus : Fin 6 → Fin 10 → ℝ)
    (c u cStewart smallRadius A2 Aplus2 : ℝ)
    (hc0 : 0 ≤ c) (hcu : c ≤ u) (hu1 : u ≤ 1)
    (hcStewart : 0 ≤ cStewart)
    (hA2_nonneg : 0 ≤ A2)
    (hAplus2_nonneg : 0 ≤ Aplus2)
    (hA2 : rectOpNorm2Le A A2)
    (hAplus2 : rectOpNorm2Le Aplus Aplus2)
    (huSmall : u ≤ smallRadius / (((2 : ℝ) ^ 39 - 1)))
    (hSeq : RectangularGivensSequenceBackwardError 10 6 A R_hat_rect
      (givensQRRectangularRotationCount 10 6) c)
    (hbottom : ∀ i j, (6 : ℕ) ≤ i.val → R_hat_rect i j = 0)
    (htop : ∀ i j, R_hat i j =
      R_hat_rect ⟨i.val, lt_of_lt_of_le i.isLt (by norm_num : 6 ≤ 10)⟩ j)
    (hR_upper : ∀ i j, j.val < i.val → R i j = 0)
    (hR_diag_nonneg : ∀ i, 0 ≤ R i i)
    (hRhat_upper : ∀ i j, j.val < i.val → R_hat i j = 0)
    (hRhat_diag_nonneg : ∀ i, 0 ≤ R_hat i i)
    (hStewart :
      EconomyQRFactorStewartRelativeBound 10 6 A R R_hat
        cStewart
        (stewartFrobeniusPseudoinverseCondition A Aplus)
        smallRadius) :
    EconomyQRFactorRelativeErrorLe 6 R R_hat
      ((cStewart * ((2 : ℝ) ^ 39 - 1) * (6 : ℝ) *
          rectangularSpectralPseudoinverseCondition A2 Aplus2) * u) := by
  exact
    rectangular_givens_qr_backward_ten_by_six_unit_roundoff_economy_qr_factor_relative_error_of_stewart1977_frobenius_condition_surfaces_linear_u
      A R_hat_rect R R_hat Aplus c u cStewart smallRadius A2 Aplus2
      hc0 hcu hu1 hcStewart hA2_nonneg hAplus2_nonneg hA2 hAplus2
      (qrTenBySixStewartRelativeRadius_le_of_unitRoundoff_le_smallRadius_div
        huSmall)
      hSeq hbottom htop hR_upper hR_diag_nonneg hRhat_upper
      hRhat_diag_nonneg hStewart

/-- Stewart-1977-constant specialization of the source-faithful Frobenius
    condition handoff. -/
theorem rectangular_givens_qr_backward_ten_by_six_unit_roundoff_economy_qr_factor_relative_error_of_stewart1977_source_constant_frobenius_condition_surfaces_linear_u_of_unitRoundoff_le_smallRadius_div
    (A R_hat_rect : Fin 10 → Fin 6 → ℝ)
    (R R_hat : Fin 6 → Fin 6 → ℝ)
    (Aplus : Fin 6 → Fin 10 → ℝ)
    (c u smallRadius A2 Aplus2 : ℝ)
    (hc0 : 0 ≤ c) (hcu : c ≤ u) (hu1 : u ≤ 1)
    (hA2_nonneg : 0 ≤ A2)
    (hAplus2_nonneg : 0 ≤ Aplus2)
    (hA2 : rectOpNorm2Le A A2)
    (hAplus2 : rectOpNorm2Le Aplus Aplus2)
    (huSmall : u ≤ smallRadius / (((2 : ℝ) ^ 39 - 1)))
    (hSeq : RectangularGivensSequenceBackwardError 10 6 A R_hat_rect
      (givensQRRectangularRotationCount 10 6) c)
    (hbottom : ∀ i j, (6 : ℕ) ≤ i.val → R_hat_rect i j = 0)
    (htop : ∀ i j, R_hat i j =
      R_hat_rect ⟨i.val, lt_of_lt_of_le i.isLt (by norm_num : 6 ≤ 10)⟩ j)
    (hR_upper : ∀ i j, j.val < i.val → R i j = 0)
    (hR_diag_nonneg : ∀ i, 0 ≤ R i i)
    (hRhat_upper : ∀ i j, j.val < i.val → R_hat i j = 0)
    (hRhat_diag_nonneg : ∀ i, 0 ≤ R_hat i i)
    (hStewart :
      EconomyQRFactorStewartRelativeBound 10 6 A R R_hat
        (stewartQRFactorRelativeConstant 6)
        (stewartFrobeniusPseudoinverseCondition A Aplus)
        smallRadius) :
    EconomyQRFactorRelativeErrorLe 6 R R_hat
      ((stewartQRFactorRelativeConstant 6 * ((2 : ℝ) ^ 39 - 1) *
          (6 : ℝ) * rectangularSpectralPseudoinverseCondition A2 Aplus2) *
        u) := by
  exact
    rectangular_givens_qr_backward_ten_by_six_unit_roundoff_economy_qr_factor_relative_error_of_stewart1977_frobenius_condition_surfaces_linear_u_of_unitRoundoff_le_smallRadius_div
      A R_hat_rect R R_hat Aplus c u (stewartQRFactorRelativeConstant 6)
      smallRadius A2 Aplus2 hc0 hcu hu1
      (stewartQRFactorRelativeConstant_nonneg 6)
      hA2_nonneg hAplus2_nonneg hA2 hAplus2 huSmall
      hSeq hbottom htop hR_upper hR_diag_nonneg hRhat_upper
      hRhat_diag_nonneg hStewart

/-- Chapter 1 `O(u)` envelope for the conditional `10 x 6` economy-QR handoff.

    If a fixed constant `K` dominates the exposed Stewart/condition-number
    factor, then the final relative `R`-factor error is bounded by `K * u`.
    This is the precise conditional content behind the prose order statement;
    it does not reproduce the hidden Figure 1.5 machine trace. -/
theorem rectangular_givens_qr_backward_ten_by_six_unit_roundoff_economy_qr_factor_relative_error_of_stewart_kappa2_bridge_le_K_mul_u
    (A R_hat_rect : Fin 10 → Fin 6 → ℝ)
    (R R_hat : Fin 6 → Fin 6 → ℝ)
    (c u cStewart kappaF kappa2 kappaBridge smallRadius K : ℝ)
    (hc0 : 0 ≤ c) (hcu : c ≤ u) (hu1 : u ≤ 1)
    (hcStewart : 0 ≤ cStewart)
    (hkappa : kappaF ≤ kappaBridge * kappa2)
    (hrelSmall : (((2 : ℝ) ^ 39 - 1) * u) ≤ smallRadius)
    (hK : cStewart * ((2 : ℝ) ^ 39 - 1) * kappaBridge * kappa2 ≤ K)
    (hSeq : RectangularGivensSequenceBackwardError 10 6 A R_hat_rect
      (givensQRRectangularRotationCount 10 6) c)
    (hbottom : ∀ i j, (6 : ℕ) ≤ i.val → R_hat_rect i j = 0)
    (htop : ∀ i j, R_hat i j =
      R_hat_rect ⟨i.val, lt_of_lt_of_le i.isLt (by norm_num : 6 ≤ 10)⟩ j)
    (hR_upper : ∀ i j, j.val < i.val → R i j = 0)
    (hR_diag_nonneg : ∀ i, 0 ≤ R i i)
    (hRhat_upper : ∀ i j, j.val < i.val → R_hat i j = 0)
    (hRhat_diag_nonneg : ∀ i, 0 ≤ R_hat i i)
    (hStewart :
      EconomyQRFactorStewartRelativeBound 10 6 A R R_hat
        cStewart kappaF smallRadius) :
    EconomyQRFactorRelativeErrorLe 6 R R_hat (K * u) := by
  have hu0 : 0 ≤ u := le_trans hc0 hcu
  have hLinear :
      EconomyQRFactorRelativeErrorLe 6 R R_hat
        ((cStewart * ((2 : ℝ) ^ 39 - 1) * kappaBridge * kappa2) * u) :=
    rectangular_givens_qr_backward_ten_by_six_unit_roundoff_economy_qr_factor_relative_error_of_stewart_kappa2_bridge_linear_u
      A R_hat_rect R R_hat c u cStewart kappaF kappa2 kappaBridge smallRadius
      hc0 hcu hu1 hcStewart hkappa hrelSmall hSeq hbottom htop hR_upper
      hR_diag_nonneg hRhat_upper hRhat_diag_nonneg hStewart
  exact hLinear.mono (mul_le_mul_of_nonneg_right hK hu0)

end LeanFpAnalysis.FP
