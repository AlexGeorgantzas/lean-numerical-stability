-- Analysis/Norms.lean
--
-- Source-facing norm infrastructure for Higham, Chapter 6.

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact

namespace LeanFpAnalysis.FP

open scoped BigOperators

/-- Complex vector indexed by `Fin n`, the source domain for Higham Chapter 6
    vector norms. -/
abbrev CVec (n : ℕ) := Fin n → ℂ

/-- Pointwise vector addition, kept explicit so Chapter 6 abstract norm
    predicates do not depend on notation choices. -/
noncomputable def complexVecAdd {n : ℕ} (x y : CVec n) : CVec n :=
  fun i => x i + y i

/-- Scalar multiplication for source-facing complex vectors. -/
noncomputable def complexVecSMul {n : ℕ} (a : ℂ) (x : CVec n) : CVec n :=
  fun i => a * x i

/-- Componentwise absolute-value vector, embedded back into `C^n`. -/
noncomputable def complexAbsVec {n : ℕ} (x : CVec n) : CVec n :=
  fun i => (‖x i‖ : ℂ)

@[simp]
lemma complexAbsVec_norm_apply {n : ℕ} (x : CVec n) (i : Fin n) :
    ‖complexAbsVec x i‖ = ‖x i‖ := by
  simp [complexAbsVec]

/-- Componentwise absolute-value order used in Higham, Definition 6.1. -/
def componentwiseAbsLe {n : ℕ} (x y : CVec n) : Prop :=
  ∀ i : Fin n, ‖x i‖ ≤ ‖y i‖

/-- Abstract vector norm axioms for functions `C^n -> R`, matching the three
    axioms listed at the start of Higham, Chapter 6, Section 6.1. -/
structure IsComplexVectorNorm {n : ℕ} (ν : CVec n → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ ν x
  eq_zero_iff : ∀ x, ν x = 0 ↔ x = 0
  smul : ∀ (a : ℂ) (x : CVec n), ν (complexVecSMul a x) = ‖a‖ * ν x
  add_le : ∀ x y : CVec n, ν (complexVecAdd x y) ≤ ν x + ν y

/-- Higham, 2nd ed., Chapter 6, Definition 6.1:
    a vector norm is absolute if `‖ |x| ‖ = ‖x‖`. -/
def IsAbsoluteComplexVectorNorm {n : ℕ} (ν : CVec n → ℝ) : Prop :=
  ∀ x : CVec n, ν (complexAbsVec x) = ν x

/-- Higham, 2nd ed., Chapter 6, Definition 6.1:
    a vector norm is monotone if `|x| <= |y|` componentwise implies
    `‖x‖ <= ‖y‖`. -/
def IsMonotoneComplexVectorNorm {n : ℕ} (ν : CVec n → ℝ) : Prop :=
  ∀ x y : CVec n, componentwiseAbsLe x y → ν x ≤ ν y

/-- Change the sign of one coordinate. -/
noncomputable def flipCoord {n : ℕ} (j : Fin n) (x : CVec n) : CVec n :=
  fun i => if i = j then -x i else x i

/-- Scale one coordinate by a real scalar. -/
noncomputable def scaleCoord {n : ℕ} (j : Fin n) (t : ℝ) (x : CVec n) : CVec n :=
  fun i => if i = j then (t : ℂ) * x i else x i

lemma complexAbsVec_flipCoord {n : ℕ} (j : Fin n) (x : CVec n) :
    complexAbsVec (flipCoord j x) = complexAbsVec x := by
  ext i
  by_cases h : i = j
  · simp [complexAbsVec, flipCoord, h]
  · simp [complexAbsVec, flipCoord, h]

lemma absolute_norm_flipCoord_eq {n : ℕ} {ν : CVec n → ℝ}
    (habs : IsAbsoluteComplexVectorNorm ν) (j : Fin n) (x : CVec n) :
    ν (flipCoord j x) = ν x := by
  calc
    ν (flipCoord j x) = ν (complexAbsVec (flipCoord j x)) := (habs (flipCoord j x)).symm
    _ = ν (complexAbsVec x) := by rw [complexAbsVec_flipCoord]
    _ = ν x := habs x

/-- A one-coordinate contraction does not increase an absolute norm. -/
lemma absolute_norm_scaleCoord_le {n : ℕ} {ν : CVec n → ℝ}
    (hν : IsComplexVectorNorm ν) (habs : IsAbsoluteComplexVectorNorm ν)
    (j : Fin n) (t : ℝ) (x : CVec n) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ν (scaleCoord j t x) ≤ ν x := by
  let a : ℝ := (1 + t) / 2
  let b : ℝ := (1 - t) / 2
  have ha0 : 0 ≤ a := by
    dsimp [a]
    nlinarith
  have hb0 : 0 ≤ b := by
    dsimp [b]
    nlinarith
  have hab_sum : a + b = 1 := by
    dsimp [a, b]
    ring
  have hflip : ν (flipCoord j x) = ν x := absolute_norm_flipCoord_eq habs j x
  have hrepr :
      scaleCoord j t x =
        complexVecAdd (complexVecSMul (a : ℂ) x)
          (complexVecSMul (b : ℂ) (flipCoord j x)) := by
    ext i
    by_cases h : i = j
    · simp [scaleCoord, complexVecAdd, complexVecSMul, flipCoord, h, a, b]
      ring
    · simp [scaleCoord, complexVecAdd, complexVecSMul, flipCoord, h, a, b]
      ring
  calc
    ν (scaleCoord j t x)
        = ν (complexVecAdd (complexVecSMul (a : ℂ) x)
            (complexVecSMul (b : ℂ) (flipCoord j x))) := by rw [hrepr]
    _ ≤ ν (complexVecSMul (a : ℂ) x) +
          ν (complexVecSMul (b : ℂ) (flipCoord j x)) :=
        hν.add_le _ _
    _ = a * ν x + b * ν (flipCoord j x) := by
        rw [hν.smul, hν.smul, Complex.norm_of_nonneg ha0, Complex.norm_of_nonneg hb0]
    _ = (a + b) * ν x := by
        rw [hflip]
        ring
    _ = ν x := by
        rw [hab_sum]
        ring

/-- Scale the coordinates in a finite set by prescribed real factors. -/
noncomputable def scaleOn {n : ℕ} (s : Finset (Fin n)) (θ : Fin n → ℝ)
    (x : CVec n) : CVec n :=
  fun i => if i ∈ s then (θ i : ℂ) * x i else x i

lemma scaleOn_insert_eq_scaleCoord {n : ℕ} (s : Finset (Fin n)) (a : Fin n)
    (ha : a ∉ s) (θ : Fin n → ℝ) (x : CVec n) :
    scaleOn (insert a s) θ x = scaleCoord a (θ a) (scaleOn s θ x) := by
  ext i
  by_cases hi : i = a
  · subst hi
    simp [scaleOn, scaleCoord, ha]
  · by_cases his : i ∈ s
    · have hins : i ∈ insert a s := by exact Finset.mem_insert.mpr (Or.inr his)
      simp [scaleOn, scaleCoord, hi, his, hins]
    · have hins : i ∉ insert a s := by
        intro hmem
        rcases Finset.mem_insert.mp hmem with hia | hs
        · exact hi hia
        · exact his hs
      simp [scaleOn, scaleCoord, hi, his, hins]

/-- Iterating one-coordinate contractions over a finite set cannot increase an
    absolute norm. -/
lemma absolute_norm_scaleOn_le {n : ℕ} {ν : CVec n → ℝ}
    (hν : IsComplexVectorNorm ν) (habs : IsAbsoluteComplexVectorNorm ν)
    (s : Finset (Fin n)) (θ : Fin n → ℝ) (x : CVec n)
    (hθ0 : ∀ i, 0 ≤ θ i) (hθ1 : ∀ i, θ i ≤ 1) :
    ν (scaleOn s θ x) ≤ ν x := by
  induction s using Finset.induction_on with
  | empty =>
      have hscale : scaleOn (∅ : Finset (Fin n)) θ x = x := by
        ext i
        simp [scaleOn]
      rw [hscale]
  | insert a s ha ih =>
      rw [scaleOn_insert_eq_scaleCoord s a ha θ x]
      exact (absolute_norm_scaleCoord_le hν habs a (θ a) (scaleOn s θ x)
        (hθ0 a) (hθ1 a)).trans (ih)

lemma exists_unit_interval_scale_of_abs_le {n : ℕ} (x y : CVec n)
    (hxy : componentwiseAbsLe x y) :
    ∃ θ : Fin n → ℝ,
      (∀ i, 0 ≤ θ i) ∧ (∀ i, θ i ≤ 1) ∧
        complexAbsVec x = scaleOn Finset.univ θ (complexAbsVec y) := by
  let θ : Fin n → ℝ := fun i => if ‖y i‖ = 0 then 0 else ‖x i‖ / ‖y i‖
  refine ⟨θ, ?_, ?_, ?_⟩
  · intro i
    by_cases hy : ‖y i‖ = 0
    · simp [θ, hy]
    · dsimp [θ]
      rw [if_neg hy]
      exact div_nonneg (norm_nonneg (x i)) (norm_nonneg (y i))
  · intro i
    by_cases hy : ‖y i‖ = 0
    · simp [θ, hy]
    · have hypos : 0 < ‖y i‖ := lt_of_le_of_ne (norm_nonneg (y i)) (Ne.symm hy)
      dsimp [θ]
      rw [if_neg hy]
      exact (div_le_one hypos).mpr (hxy i)
  · ext i
    have hreal : ‖x i‖ = θ i * ‖y i‖ := by
      by_cases hy : ‖y i‖ = 0
      · have hx0 : ‖x i‖ = 0 := by
          exact le_antisymm ((hxy i).trans (le_of_eq hy)) (norm_nonneg _)
        simp [θ, hy, hx0]
      · have hyne : ‖y i‖ ≠ 0 := hy
        dsimp [θ]
        rw [if_neg hy]
        field_simp [hyne]
    have hc := congrArg (fun r : ℝ => (r : ℂ)) hreal
    simpa [complexAbsVec, scaleOn, Complex.ofReal_mul] using hc

/-- The easy direction of Higham, Theorem 6.2: monotone vector norms are
    absolute. -/
theorem absolute_of_monotone_complexVectorNorm {n : ℕ} {ν : CVec n → ℝ}
    (hmono : IsMonotoneComplexVectorNorm ν) :
    IsAbsoluteComplexVectorNorm ν := by
  intro x
  apply le_antisymm
  · exact hmono (complexAbsVec x) x (by intro i; simp)
  · exact hmono x (complexAbsVec x) (by intro i; simp)

/-- Higham, 2nd ed., Chapter 6, Definition 6.1 / Theorem 6.2
    (Bauer-Stoer-Witzgall): an abstract norm on `C^n` is monotone iff it is
    absolute.  The proof formalizes the coordinate-contraction argument rather
    than importing the cited theorem as a hypothesis. -/
theorem monotone_iff_absolute_complexVectorNorm {n : ℕ} {ν : CVec n → ℝ}
    (hν : IsComplexVectorNorm ν) :
    IsMonotoneComplexVectorNorm ν ↔ IsAbsoluteComplexVectorNorm ν := by
  constructor
  · exact absolute_of_monotone_complexVectorNorm
  · intro habs x y hxy
    obtain ⟨θ, hθ0, hθ1, hscale⟩ := exists_unit_interval_scale_of_abs_le x y hxy
    calc
      ν x = ν (complexAbsVec x) := (habs x).symm
      _ = ν (scaleOn Finset.univ θ (complexAbsVec y)) := by rw [hscale]
      _ ≤ ν (complexAbsVec y) := absolute_norm_scaleOn_le hν habs Finset.univ θ
        (complexAbsVec y) hθ0 hθ1
      _ = ν y := habs y

/-- Source-facing theorem name for Higham, 2nd ed., Chapter 6, Theorem 6.2. -/
theorem absolute_norm_iff_monotone_norm {n : ℕ} {ν : CVec n → ℝ}
    (hν : IsComplexVectorNorm ν) :
    IsAbsoluteComplexVectorNorm ν ↔ IsMonotoneComplexVectorNorm ν := by
  exact (monotone_iff_absolute_complexVectorNorm hν).symm

-- ============================================================
-- Mixed subordinate norm foundation
-- ============================================================

/-- Abstract complex linear functional on `C^n`, in the explicit vector
    operations used by this source-facing file. -/
structure IsComplexLinearForm {n : ℕ} (φ : CVec n → ℂ) : Prop where
  map_add : ∀ x y : CVec n, φ (complexVecAdd x y) = φ x + φ y
  map_smul : ∀ (a : ℂ) (x : CVec n), φ (complexVecSMul a x) = a * φ x

lemma IsComplexLinearForm.map_zero {n : ℕ} {φ : CVec n → ℂ}
    (hφ : IsComplexLinearForm φ) : φ 0 = 0 := by
  have h := hφ.map_smul (0 : ℂ) (0 : CVec n)
  have hleft : complexVecSMul (0 : ℂ) (0 : CVec n) = 0 := by
    ext i
    simp [complexVecSMul]
  rw [hleft] at h
  simpa using h

/-- Standard coordinate vector in `C^n`. -/
def standardBasisCVec {n : ℕ} (j : Fin n) : CVec n :=
  fun i => if i = j then 1 else 0

lemma sum_smul_standardBasisCVec {n : ℕ} (x : CVec n) :
    (fun i : Fin n => ∑ j : Fin n, x j * standardBasisCVec j i) = x := by
  ext i
  calc
    (∑ j : Fin n, x j * standardBasisCVec j i) = x i * standardBasisCVec i i := by
      refine Finset.sum_eq_single i ?_ ?_
      · intro j _hj hji
        simp [standardBasisCVec, hji.symm]
      · intro hnot
        simp at hnot
    _ = x i := by
      simp [standardBasisCVec]

lemma IsComplexLinearForm.apply_sum {n : ℕ} {φ : CVec n → ℂ}
    (hφ : IsComplexLinearForm φ) (s : Finset (Fin n)) (a : Fin n → ℂ)
    (v : Fin n → CVec n) :
    φ (fun i : Fin n => Finset.sum s fun j => a j * v j i) =
      Finset.sum s fun j => a j * φ (v j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change φ (0 : CVec n) = 0
      exact hφ.map_zero
  | insert j s hjs ih =>
      have hsplit :
          (fun i : Fin n => Finset.sum (insert j s) fun k => a k * v k i) =
            complexVecAdd (complexVecSMul (a j) (v j))
              (fun i : Fin n => Finset.sum s fun k => a k * v k i) := by
        ext i
        simp [Finset.sum_insert hjs, complexVecAdd, complexVecSMul]
      rw [hsplit, hφ.map_add, hφ.map_smul, ih, Finset.sum_insert hjs]

lemma IsComplexLinearForm.apply_eq_sum_basis {n : ℕ} {φ : CVec n → ℂ}
    (hφ : IsComplexLinearForm φ) (x : CVec n) :
    φ x = ∑ j : Fin n, x j * φ (standardBasisCVec j) := by
  have hdecomp :
      (fun i : Fin n => ∑ j : Fin n, x j * standardBasisCVec j i) = x :=
    sum_smul_standardBasisCVec x
  calc
    φ x = φ (fun i : Fin n => ∑ j : Fin n, x j * standardBasisCVec j i) := by
      rw [hdecomp]
    _ = ∑ j : Fin n, x j * φ (standardBasisCVec j) := by
      simpa using hφ.apply_sum Finset.univ x standardBasisCVec

/-- Concrete complex vector 1-norm. -/
noncomputable def complexVecOneNorm {n : ℕ} (x : CVec n) : ℝ :=
  ∑ i : Fin n, ‖x i‖

theorem complexVecOneNorm_isComplexVectorNorm {n : ℕ} :
    IsComplexVectorNorm (complexVecOneNorm (n := n)) := by
  constructor
  · intro x
    exact Finset.sum_nonneg (fun i _ => norm_nonneg (x i))
  · intro x
    constructor
    · intro hx
      have hterms :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => norm_nonneg (x i))).mp hx
      ext i
      exact norm_eq_zero.mp (hterms i (Finset.mem_univ i))
    · intro hx
      subst hx
      simp [complexVecOneNorm]
  · intro a x
    unfold complexVecOneNorm complexVecSMul
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [norm_mul]
  · intro x y
    unfold complexVecOneNorm complexVecAdd
    calc
      (∑ i : Fin n, ‖x i + y i‖)
          ≤ ∑ i : Fin n, (‖x i‖ + ‖y i‖) := by
            apply Finset.sum_le_sum
            intro i _
            exact norm_add_le (x i) (y i)
      _ = (∑ i : Fin n, ‖x i‖) + ∑ i : Fin n, ‖y i‖ := by
            rw [Finset.sum_add_distrib]

lemma complexVecOneNorm_standardBasisCVec {n : ℕ} (j : Fin n) :
    complexVecOneNorm (standardBasisCVec j) = 1 := by
  unfold complexVecOneNorm standardBasisCVec
  calc
    (∑ i : Fin n, ‖(if i = j then 1 else 0 : ℂ)‖) =
        ∑ i : Fin n, (if i = j then 1 else 0 : ℝ) := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hij : i = j
          · simp [hij]
          · simp [hij]
    _ = 1 := by
          simp [Finset.sum_ite_eq', Finset.mem_univ]

/-- Concrete complex vector infinity norm, using Mathlib's sup norm on finite
    functions. -/
noncomputable def complexVecInfNorm {n : ℕ} (x : CVec n) : ℝ :=
  ‖x‖

lemma complexVecInfNorm_nonneg {n : ℕ} (x : CVec n) :
    0 ≤ complexVecInfNorm x := by
  unfold complexVecInfNorm
  exact norm_nonneg x

lemma complexVecInfNorm_coord_le {n : ℕ} (x : CVec n) (i : Fin n) :
    ‖x i‖ ≤ complexVecInfNorm x := by
  unfold complexVecInfNorm
  exact norm_le_pi_norm x i

lemma complexVecInfNorm_le_of_coord_le {n : ℕ} (x : CVec n) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ i : Fin n, ‖x i‖ ≤ c) :
    complexVecInfNorm x ≤ c := by
  unfold complexVecInfNorm
  rw [pi_norm_le_iff_of_nonneg hc]
  exact h

theorem complexVecInfNorm_isComplexVectorNorm {n : ℕ} :
    IsComplexVectorNorm (complexVecInfNorm (n := n)) := by
  constructor
  · exact complexVecInfNorm_nonneg
  · intro x
    constructor
    · intro hx
      exact norm_eq_zero.mp hx
    · intro hx
      subst hx
      simp [complexVecInfNorm]
  · intro a x
    have hvec : complexVecSMul a x = a • x := by
      ext i
      simp [complexVecSMul]
    simp [complexVecInfNorm, hvec, norm_smul]
  · intro x y
    have hvec : complexVecAdd x y = x + y := by
      ext i
      simp [complexVecAdd]
    simpa [complexVecInfNorm, hvec] using norm_add_le x y

lemma complexVecInfNorm_standardBasisCVec {n : ℕ} (j : Fin n) :
    complexVecInfNorm (standardBasisCVec j) = 1 := by
  apply le_antisymm
  · apply complexVecInfNorm_le_of_coord_le _ zero_le_one
    intro i
    by_cases hij : i = j
    · simp [standardBasisCVec, hij]
    · simp [standardBasisCVec, hij]
  · have h := complexVecInfNorm_coord_le (standardBasisCVec j) j
    simpa [standardBasisCVec] using h

/-- A phase with norm at most one that turns `z` into its absolute value. -/
noncomputable def complexUnitPhase (z : ℂ) : ℂ :=
  if z = 0 then 0 else z⁻¹ * (‖z‖ : ℂ)

lemma complexUnitPhase_norm_le_one (z : ℂ) :
    ‖complexUnitPhase z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [complexUnitPhase, hz]
  · have hznorm_ne : ‖z‖ ≠ 0 := by
      exact norm_ne_zero_iff.mpr hz
    calc
      ‖complexUnitPhase z‖ = ‖z⁻¹ * (‖z‖ : ℂ)‖ := by
        simp [complexUnitPhase, hz]
      _ = ‖z⁻¹‖ * ‖(‖z‖ : ℂ)‖ := norm_mul _ _
      _ = ‖z‖⁻¹ * ‖z‖ := by
        rw [norm_inv, Complex.norm_of_nonneg (norm_nonneg z)]
      _ = 1 := by
        field_simp [hznorm_ne]
      _ ≤ 1 := le_rfl

lemma mul_complexUnitPhase_eq_norm (z : ℂ) :
    z * complexUnitPhase z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [complexUnitPhase, hz]
  · simp [complexUnitPhase, hz]

/-- A nontrivial source-facing normed `C^n` has at least one unit vector. -/
lemma exists_unit_complexVectorNorm {n : ℕ} {ν : CVec n → ℝ}
    (hν : IsComplexVectorNorm ν) (hn : 0 < n) :
    ∃ u : CVec n, ν u = 1 := by
  let j0 : Fin n := ⟨0, hn⟩
  let e : CVec n := standardBasisCVec j0
  have he_ne : e ≠ 0 := by
    intro he
    have hcoord := congr_fun he j0
    simp [e, standardBasisCVec] at hcoord
  have hνe_ne : ν e ≠ 0 := by
    intro hνe
    exact he_ne ((hν.eq_zero_iff e).mp hνe)
  have hνe_pos : 0 < ν e :=
    lt_of_le_of_ne (hν.nonneg e) (Ne.symm hνe_ne)
  let u : CVec n := complexVecSMul (((ν e)⁻¹ : ℝ) : ℂ) e
  refine ⟨u, ?_⟩
  have hinv_nonneg : 0 ≤ (ν e)⁻¹ := inv_nonneg.mpr (hν.nonneg e)
  dsimp [u]
  rw [hν.smul, Complex.norm_of_nonneg hinv_nonneg]
  field_simp [ne_of_gt hνe_pos]

/-- A norming functional for `x`: it is complex-linear, bounded by the norm,
    and attains the value `1` at `x`.  This is the local hypothesis supplied by
    the dual-norm-attainment step in Higham, equation (6.3). -/
structure IsNormingFunctionalAt {n : ℕ} (ν : CVec n → ℝ) (x : CVec n)
    (φ : CVec n → ℂ) : Prop where
  linear : IsComplexLinearForm φ
  bound : ∀ v : CVec n, ‖φ v‖ ≤ ν v
  value : φ x = 1

/-- A functional has dual-norm upper bound `d` with respect to the source
    vector norm `ν`. -/
def DualFunctionalBound {n : ℕ} (ν : CVec n → ℝ) (φ : CVec n → ℂ)
    (d : ℝ) : Prop :=
  ∀ v : CVec n, ‖φ v‖ ≤ d * ν v

/-- Least-bound predicate for the dual norm of a complex linear functional.
    This is the functional analogue of `IsMixedSubordinateNormValue` and is
    used for the rank-one subordinate norm identity in Problem 6.2. -/
structure IsDualFunctionalNormValue {n : ℕ} (ν : CVec n → ℝ)
    (φ : CVec n → ℂ) (d : ℝ) : Prop where
  linear : IsComplexLinearForm φ
  bound : DualFunctionalBound ν φ d
  least : ∀ e : ℝ, DualFunctionalBound ν φ e → d ≤ e

/-- Values `|φ x|` attained by a linear functional on the unit sphere. -/
def DualUnitFunctionalNormSet {n : ℕ} (ν : CVec n → ℝ)
    (φ : CVec n → ℂ) : Set ℝ :=
  {r | ∃ x : CVec n, ν x = 1 ∧ r = ‖φ x‖}

/-- Maximum form of the dual functional norm over unit vectors. -/
def IsMaxDualUnitFunctionalNormValue {n : ℕ} (ν : CVec n → ℝ)
    (φ : CVec n → ℂ) (d : ℝ) : Prop :=
  d ∈ DualUnitFunctionalNormSet ν φ ∧
    ∀ r : ℝ, r ∈ DualUnitFunctionalNormSet ν φ → r ≤ d

/-- Values `|φ x| / ||x||` attained by a linear functional on nonzero vectors. -/
def DualNonzeroFunctionalRatioSet {n : ℕ} (ν : CVec n → ℝ)
    (φ : CVec n → ℂ) : Set ℝ :=
  {r | ∃ x : CVec n, x ≠ 0 ∧ r = ‖φ x‖ / ν x}

/-- Maximum form of the dual functional norm over nonzero-vector ratios. -/
def IsMaxDualNonzeroFunctionalRatioValue {n : ℕ} (ν : CVec n → ℝ)
    (φ : CVec n → ℂ) (d : ℝ) : Prop :=
  d ∈ DualNonzeroFunctionalRatioSet ν φ ∧
    ∀ r : ℝ, r ∈ DualNonzeroFunctionalRatioSet ν φ → r ≤ d

theorem isDualFunctionalNormValue_of_isMaxDualUnitFunctionalNormValue
    {n : ℕ} {ν : CVec n → ℝ} {φ : CVec n → ℂ} {d : ℝ}
    (hν : IsComplexVectorNorm ν) (hφ : IsComplexLinearForm φ)
    (hmax : IsMaxDualUnitFunctionalNormValue ν φ d) :
    IsDualFunctionalNormValue ν φ d := by
  refine ⟨hφ, ?_, ?_⟩
  · intro x
    by_cases hxzero : x = 0
    · have hleft : ‖φ x‖ = 0 := by
        rw [hxzero, hφ.map_zero, norm_zero]
      have hright : d * ν x = 0 := by
        have hxnorm : ν x = 0 := (hν.eq_zero_iff x).mpr hxzero
        rw [hxnorm, mul_zero]
      rw [hleft, hright]
    · have hxnorm_ne : ν x ≠ 0 := by
        intro hxnorm
        exact hxzero ((hν.eq_zero_iff x).mp hxnorm)
      have hxnorm_pos : 0 < ν x :=
        lt_of_le_of_ne (hν.nonneg x) (Ne.symm hxnorm_ne)
      let u : CVec n := complexVecSMul (((ν x)⁻¹ : ℝ) : ℂ) x
      have hinv_nonneg : 0 ≤ (ν x)⁻¹ := inv_nonneg.mpr (hν.nonneg x)
      have hu_unit : ν u = 1 := by
        dsimp [u]
        rw [hν.smul, Complex.norm_of_nonneg hinv_nonneg]
        field_simp [ne_of_gt hxnorm_pos]
      have humem : ‖φ u‖ ∈ DualUnitFunctionalNormSet ν φ :=
        ⟨u, hu_unit, rfl⟩
      have hmax_le : ‖φ u‖ ≤ d := hmax.2 ‖φ u‖ humem
      have hscaled_abs : |ν x|⁻¹ * ‖φ x‖ ≤ d := by
        simpa [u, hφ.map_smul] using hmax_le
      have hscaled : (ν x)⁻¹ * ‖φ x‖ ≤ d := by
        simpa [abs_of_nonneg (hν.nonneg x)] using hscaled_abs
      have hmul := mul_le_mul_of_nonneg_left hscaled (le_of_lt hxnorm_pos)
      calc
        ‖φ x‖ = ν x * ((ν x)⁻¹ * ‖φ x‖) := by
          field_simp [ne_of_gt hxnorm_pos]
        _ ≤ ν x * d := hmul
        _ = d * ν x := by ring
  · intro e he
    obtain ⟨x, hxunit, hd⟩ := hmax.1
    have hex := he x
    rw [hxunit, mul_one] at hex
    rw [hd]
    exact hex

theorem isMaxDualNonzeroFunctionalRatioValue_of_isMaxDualUnitFunctionalNormValue
    {n : ℕ} {ν : CVec n → ℝ} {φ : CVec n → ℂ} {d : ℝ}
    (hν : IsComplexVectorNorm ν) (hφ : IsComplexLinearForm φ)
    (hmax : IsMaxDualUnitFunctionalNormValue ν φ d) :
    IsMaxDualNonzeroFunctionalRatioValue ν φ d := by
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hxunit, hd⟩ := hmax.1
    have hxne : x ≠ 0 := by
      intro hxzero
      have hxnorm : ν x = 0 := (hν.eq_zero_iff x).mpr hxzero
      rw [hxunit] at hxnorm
      norm_num at hxnorm
    refine ⟨x, hxne, ?_⟩
    rw [hd, hxunit]
    ring
  · intro r hr
    obtain ⟨x, hxne, hr⟩ := hr
    have hxnorm_ne : ν x ≠ 0 := by
      intro hxnorm
      exact hxne ((hν.eq_zero_iff x).mp hxnorm)
    have hxnorm_pos : 0 < ν x :=
      lt_of_le_of_ne (hν.nonneg x) (Ne.symm hxnorm_ne)
    let u : CVec n := complexVecSMul (((ν x)⁻¹ : ℝ) : ℂ) x
    have hinv_nonneg : 0 ≤ (ν x)⁻¹ := inv_nonneg.mpr (hν.nonneg x)
    have hu_unit : ν u = 1 := by
      dsimp [u]
      rw [hν.smul, Complex.norm_of_nonneg hinv_nonneg]
      field_simp [ne_of_gt hxnorm_pos]
    have humem : ‖φ u‖ ∈ DualUnitFunctionalNormSet ν φ :=
      ⟨u, hu_unit, rfl⟩
    have hmax_le : ‖φ u‖ ≤ d := hmax.2 ‖φ u‖ humem
    have hscaled_abs : |ν x|⁻¹ * ‖φ x‖ ≤ d := by
      simpa [u, hφ.map_smul] using hmax_le
    have hscaled : (ν x)⁻¹ * ‖φ x‖ ≤ d := by
      simpa [abs_of_nonneg (hν.nonneg x)] using hscaled_abs
    rw [hr]
    calc
      ‖φ x‖ / ν x = (ν x)⁻¹ * ‖φ x‖ := by ring
      _ ≤ d := hscaled

theorem isMaxDualUnitFunctionalNormValue_of_isMaxDualNonzeroFunctionalRatioValue
    {n : ℕ} {ν : CVec n → ℝ} {φ : CVec n → ℂ} {d : ℝ}
    (hν : IsComplexVectorNorm ν) (hφ : IsComplexLinearForm φ)
    (hmax : IsMaxDualNonzeroFunctionalRatioValue ν φ d) :
    IsMaxDualUnitFunctionalNormValue ν φ d := by
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hxne, hd⟩ := hmax.1
    have hxnorm_ne : ν x ≠ 0 := by
      intro hxnorm
      exact hxne ((hν.eq_zero_iff x).mp hxnorm)
    have hxnorm_pos : 0 < ν x :=
      lt_of_le_of_ne (hν.nonneg x) (Ne.symm hxnorm_ne)
    let u : CVec n := complexVecSMul (((ν x)⁻¹ : ℝ) : ℂ) x
    have hinv_nonneg : 0 ≤ (ν x)⁻¹ := inv_nonneg.mpr (hν.nonneg x)
    have hu_unit : ν u = 1 := by
      dsimp [u]
      rw [hν.smul, Complex.norm_of_nonneg hinv_nonneg]
      field_simp [ne_of_gt hxnorm_pos]
    refine ⟨u, hu_unit, ?_⟩
    have hu_norm_abs : ‖φ u‖ = |ν x|⁻¹ * ‖φ x‖ := by
      simp [u, hφ.map_smul]
    have hu_norm : ‖φ u‖ = (ν x)⁻¹ * ‖φ x‖ := by
      simpa [abs_of_nonneg (hν.nonneg x)] using hu_norm_abs
    rw [hu_norm, hd]
    ring
  · intro r hr
    obtain ⟨x, hxunit, hr⟩ := hr
    have hxne : x ≠ 0 := by
      intro hxzero
      have hxnorm : ν x = 0 := (hν.eq_zero_iff x).mpr hxzero
      rw [hxunit] at hxnorm
      norm_num at hxnorm
    have hratio_mem : ‖φ x‖ / ν x ∈ DualNonzeroFunctionalRatioSet ν φ :=
      ⟨x, hxne, rfl⟩
    have hratio_le := hmax.2 (‖φ x‖ / ν x) hratio_mem
    rw [hr]
    rw [hxunit, div_one] at hratio_le
    exact hratio_le

theorem isMaxDualNonzeroFunctionalRatioValue_iff_unitValue
    {n : ℕ} {ν : CVec n → ℝ} {φ : CVec n → ℂ} {d : ℝ}
    (hν : IsComplexVectorNorm ν) (hφ : IsComplexLinearForm φ) :
    IsMaxDualNonzeroFunctionalRatioValue ν φ d ↔
      IsMaxDualUnitFunctionalNormValue ν φ d := by
  constructor
  · exact isMaxDualUnitFunctionalNormValue_of_isMaxDualNonzeroFunctionalRatioValue
      hν hφ
  · exact isMaxDualNonzeroFunctionalRatioValue_of_isMaxDualUnitFunctionalNormValue
      hν hφ

lemma dualFunctionalNormValue_nonneg_of_nonempty
    {n : ℕ} {ν : CVec n → ℝ} (hν : IsComplexVectorNorm ν) (hn : 0 < n)
    {φ : CVec n → ℂ} {d : ℝ}
    (hφd : IsDualFunctionalNormValue ν φ d) :
    0 ≤ d := by
  obtain ⟨u, hu_unit⟩ := exists_unit_complexVectorNorm hν hn
  have hbound := hφd.bound u
  rw [hu_unit, mul_one] at hbound
  exact le_trans (norm_nonneg (φ u)) hbound

-- ============================================================
-- Hahn-Banach bridge for abstract Chapter 6 vector norms
-- ============================================================

/-- Wrapper around `C^n` whose built-in norm is a source-facing abstract
    Higham vector norm `ν`.  This lets Mathlib's Hahn-Banach theorem apply
    without replacing the canonical normed-space structure on `Fin n -> C`. -/
structure NormedCVec (n : ℕ) (ν : CVec n → ℝ) where
  val : CVec n

namespace NormedCVec

variable {n : ℕ} {ν : CVec n → ℝ}

/-- The wrapper is linearly equivalent to the underlying vector type. -/
protected def equiv (n : ℕ) (ν : CVec n → ℝ) : NormedCVec n ν ≃ CVec n where
  toFun := NormedCVec.val
  invFun := fun x => ⟨x⟩
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; rfl

instance : CoeFun (NormedCVec n ν) (fun _ => Fin n → ℂ) :=
  ⟨NormedCVec.val⟩

@[ext]
lemma ext {x y : NormedCVec n ν} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

instance : AddCommGroup (NormedCVec n ν) :=
  (NormedCVec.equiv n ν).addCommGroup

noncomputable instance : Module ℂ (NormedCVec n ν) :=
  (NormedCVec.equiv n ν).module ℂ

@[simp] lemma val_zero : (0 : NormedCVec n ν).val = 0 := rfl
@[simp] lemma val_add (x y : NormedCVec n ν) : (x + y).val = x.val + y.val := rfl
@[simp] lemma val_neg (x : NormedCVec n ν) : (-x).val = -x.val := rfl
@[simp] lemma val_sub (x y : NormedCVec n ν) : (x - y).val = x.val - y.val := rfl
@[simp] lemma val_smul (a : ℂ) (x : NormedCVec n ν) : (a • x).val = a • x.val := rfl

instance : Norm (NormedCVec n ν) where
  norm x := ν x.val

lemma norm_eq (x : NormedCVec n ν) : ‖x‖ = ν x.val := rfl

lemma add_val_eq_complexVecAdd (x y : NormedCVec n ν) :
    (x + y).val = complexVecAdd x.val y.val := by
  ext i
  rfl

lemma smul_val_eq_complexVecSMul (a : ℂ) (x : NormedCVec n ν) :
    (a • x).val = complexVecSMul a x.val := by
  ext i
  simp [complexVecSMul]

/-- Core normed-space data generated by an abstract source-facing vector norm. -/
def normedSpaceCore (hν : IsComplexVectorNorm ν) :
    NormedSpace.Core ℂ (NormedCVec n ν) where
  norm_nonneg x := hν.nonneg x.val
  norm_smul a x := by
    change ν (a • x.val) = ‖a‖ * ν x.val
    rw [show (a • x.val) = complexVecSMul a x.val by ext i; rfl]
    exact hν.smul a x.val
  norm_triangle x y := by
    change ν (x.val + y.val) ≤ ν x.val + ν y.val
    rw [show (x.val + y.val) = complexVecAdd x.val y.val by ext i; rfl]
    exact hν.add_le x.val y.val
  norm_eq_zero_iff x := by
    change ν x.val = 0 ↔ x = 0
    constructor
    · intro h
      apply ext
      exact (hν.eq_zero_iff x.val).mp h
    · intro h
      subst h
      exact (hν.eq_zero_iff 0).mpr rfl

noncomputable def normedAddCommGroup (hν : IsComplexVectorNorm ν) :
    NormedAddCommGroup (NormedCVec n ν) :=
  NormedAddCommGroup.ofCore (𝕜 := ℂ) (normedSpaceCore hν)

/-- Hahn-Banach norming functional for a unit vector in the abstract norm `ν`. -/
theorem exists_normingFunctionalAt_of_unit_vector (hν : IsComplexVectorNorm ν)
    {x : CVec n} (hx : ν x = 1) :
    ∃ φ : CVec n → ℂ, IsNormingFunctionalAt ν x φ := by
  letI : NormedAddCommGroup (NormedCVec n ν) := normedAddCommGroup hν
  letI : Module ℂ (NormedCVec n ν) :=
    (NormedCVec.equiv n ν).module ℂ
  letI : NormedSpace ℂ (NormedCVec n ν) :=
    NormedSpace.ofCore (𝕜 := ℂ) (normedSpaceCore hν)
  let x' : NormedCVec n ν := ⟨x⟩
  have hxnorm : ‖x'‖ ≠ 0 := by
    change ν x ≠ 0
    rw [hx]
    norm_num
  obtain ⟨g, hg_norm, hgx⟩ := exists_dual_vector ℂ x' hxnorm
  refine ⟨fun v => g ⟨v⟩, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro u v
      change g ⟨complexVecAdd u v⟩ = g ⟨u⟩ + g ⟨v⟩
      have hwrap : (⟨complexVecAdd u v⟩ : NormedCVec n ν) =
          (⟨u⟩ : NormedCVec n ν) + (⟨v⟩ : NormedCVec n ν) := by
        ext i
        rfl
      rw [hwrap]
      exact map_add g ⟨u⟩ ⟨v⟩
    · intro a v
      change g ⟨complexVecSMul a v⟩ = a * g ⟨v⟩
      have hwrap : (⟨complexVecSMul a v⟩ : NormedCVec n ν) =
          a • (⟨v⟩ : NormedCVec n ν) := by
        ext i
        simp [complexVecSMul]
      rw [hwrap]
      exact map_smul g a ⟨v⟩
  · intro v
    have hle := g.le_opNorm (⟨v⟩ : NormedCVec n ν)
    rw [hg_norm] at hle
    change ‖g ⟨v⟩‖ ≤ 1 * ν v at hle
    simpa using hle
  · change g ⟨x⟩ = 1
    change g x' = ((ν x : ℝ) : ℂ) at hgx
    dsimp [x'] at hgx
    rw [hx] at hgx
    simpa using hgx

end NormedCVec

/-- A norming functional at a unit vector has dual functional norm value `1`.
    This records the least-bound form of Higham's equation (6.3). -/
theorem isDualFunctionalNormValue_one_of_normingFunctionalAt
    {n : ℕ} {ν : CVec n → ℝ} {x : CVec n} {φ : CVec n → ℂ}
    (hx : ν x = 1) (hφ : IsNormingFunctionalAt ν x φ) :
    IsDualFunctionalNormValue ν φ 1 := by
  refine ⟨hφ.linear, ?_, ?_⟩
  · intro v
    simpa using hφ.bound v
  · intro e he
    have h := he x
    rw [hφ.value, norm_one, hx] at h
    simpa using h

/-- Hahn-Banach produces a unit dual functional norm value for every unit vector
    in an abstract source-facing complex vector norm. -/
theorem exists_dualFunctionalNormValue_one_of_unit_vector
    {n : ℕ} {ν : CVec n → ℝ} (hν : IsComplexVectorNorm ν)
    {x : CVec n} (hx : ν x = 1) :
    ∃ φ : CVec n → ℂ, IsDualFunctionalNormValue ν φ 1 ∧ φ x = 1 := by
  obtain ⟨φ, hφ⟩ := NormedCVec.exists_normingFunctionalAt_of_unit_vector hν hx
  exact ⟨φ, isDualFunctionalNormValue_one_of_normingFunctionalAt hx hφ, hφ.value⟩

/-- A continuous linear map on a finite-dimensional complex normed space
    attains its operator norm on the unit sphere whenever its norm is positive. -/
theorem exists_unit_vector_norm_apply_eq_opNorm_finiteDimensional
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : E →L[ℂ] F) (hfpos : 0 < ‖f‖) :
    ∃ x : E, ‖x‖ = 1 ∧ ‖f x‖ = ‖f‖ := by
  haveI : ProperSpace E := FiniteDimensional.proper ℂ E
  cases subsingleton_or_nontrivial E with
  | inl hsub =>
      letI : Subsingleton E := hsub
      have hfzero : f = 0 := by
        ext x
        have hx : x = 0 := Subsingleton.elim x 0
        simp [hx]
      rw [hfzero, norm_zero] at hfpos
      exact False.elim (lt_irrefl _ hfpos)
  | inr hnon =>
      letI : Nontrivial E := hnon
      haveI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
      let s : Set E := Metric.sphere (0 : E) 1
      have hscompact : IsCompact s := by
        dsimp [s]
        exact isCompact_sphere (0 : E) 1
      have hsne : s.Nonempty := by
        dsimp [s]
        exact (NormedSpace.sphere_nonempty (E := E) (x := (0 : E)) (r := 1)).mpr
          zero_le_one
      have hcont : ContinuousOn (fun x : E => ‖f x‖) s :=
        (continuous_norm.comp f.continuous).continuousOn
      obtain ⟨x, hxs, hsSup, _hxmax⟩ :=
        hscompact.exists_sSup_image_eq_and_ge hsne hcont
      refine ⟨x, ?_, ?_⟩
      · simpa [s, Metric.mem_sphere, dist_eq_norm] using hxs
      · have hxnorm : ‖x‖ = 1 := by
          simpa [s, Metric.mem_sphere, dist_eq_norm] using hxs
        have hle : ‖f x‖ ≤ ‖f‖ := by
          simpa [hxnorm] using f.le_opNorm x
        apply le_antisymm hle
        have hsSupNorm := f.sSup_sphere_eq_norm
        exact le_of_eq <| by
          calc
            ‖f‖ = sSup ((fun x : E => ‖f x‖) '' s) := by
              simpa [s] using hsSupNorm.symm
            _ = ‖f x‖ := hsSup

/-- A linear-map-shaped object from `C^n` to `C^m`.  This keeps Chapter 6's
    mixed subordinate norm infrastructure independent of a concrete matrix
    representation until the matrix API is fixed. -/
abbrev ComplexVectorMap (n m : ℕ) := CVec n → CVec m

/-- Concrete finite complex matrix, represented in the same lightweight style
    as the repository's real matrix code. -/
abbrev CMatrix (m n : ℕ) := Fin m → Fin n → ℂ

/-- Matrix-vector product as a source-facing vector map. -/
noncomputable def complexMatrixVecMul {m n : ℕ} (A : CMatrix m n) :
    ComplexVectorMap n m :=
  fun x i => ∑ j : Fin n, A i j * x j

/-- Concrete complex matrix 1-norm, the maximum absolute column sum. -/
noncomputable def complexMatrixOneNorm {m n : ℕ} (A : CMatrix m n) : ℝ :=
  let f : Fin n → NNReal := fun j => ∑ i : Fin m, ‖A i j‖₊
  ((Finset.univ.sup f : NNReal) : ℝ)

/-- The concrete matrix 1-norm is exactly the maximum of the column 1-norms. -/
theorem complexMatrixOneNorm_eq_max_column_oneNorm {m n : ℕ}
    (A : CMatrix m n) :
    complexMatrixOneNorm A =
      ((Finset.univ.sup (fun j : Fin n => ∑ i : Fin m, ‖A i j‖₊) : NNReal) : ℝ) := by
  rfl

lemma complexMatrixOneNorm_nonneg {m n : ℕ} (A : CMatrix m n) :
    0 ≤ complexMatrixOneNorm A := by
  unfold complexMatrixOneNorm
  exact NNReal.coe_nonneg _

lemma complexMatrixOneNorm_col_sum_le {m n : ℕ} (A : CMatrix m n) (j : Fin n) :
    (∑ i : Fin m, ‖A i j‖) ≤ complexMatrixOneNorm A := by
  unfold complexMatrixOneNorm
  let f : Fin n → NNReal := fun j => ∑ i : Fin m, ‖A i j‖₊
  have hnn : f j ≤ Finset.univ.sup f :=
    Finset.le_sup (s := (Finset.univ : Finset (Fin n))) (f := f) (Finset.mem_univ j)
  have hreal : ((f j : NNReal) : ℝ) ≤ ((Finset.univ.sup f : NNReal) : ℝ) := by
    exact_mod_cast hnn
  simpa [f, NNReal.coe_sum] using hreal

/-- Equation (6.12), p = 1 lower-bound form: each column 1-norm is bounded
    by the induced matrix 1-norm. -/
theorem complexMatrixOneNorm_column_oneNorm_le {m n : ℕ}
    (A : CMatrix m n) (j : Fin n) :
    complexVecOneNorm (fun i : Fin m => A i j) ≤ complexMatrixOneNorm A := by
  simpa [complexVecOneNorm] using complexMatrixOneNorm_col_sum_le A j

lemma complexMatrixOneNorm_le_of_col_sum_le {m n : ℕ} {A : CMatrix m n}
    {d : ℝ} (hd : 0 ≤ d)
    (hcols : ∀ j : Fin n, (∑ i : Fin m, ‖A i j‖) ≤ d) :
    complexMatrixOneNorm A ≤ d := by
  unfold complexMatrixOneNorm
  let f : Fin n → NNReal := fun j => ∑ i : Fin m, ‖A i j‖₊
  have hcols_nn : ∀ j, f j ≤ Real.toNNReal d := by
    intro j
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal d hd]
    simpa [f, NNReal.coe_sum] using hcols j
  have hsup : Finset.univ.sup f ≤ Real.toNNReal d :=
    Finset.sup_le (fun j _ => hcols_nn j)
  have hreal : ((Finset.univ.sup f : NNReal) : ℝ) ≤ d := by
    rw [← Real.coe_toNNReal d hd]
    exact_mod_cast hsup
  simpa [f] using hreal

/-- Concrete complex matrix infinity norm, the maximum absolute row sum. -/
noncomputable def complexMatrixInfNorm {m n : ℕ} (A : CMatrix m n) : ℝ :=
  let f : Fin m → NNReal := fun i => ∑ j : Fin n, ‖A i j‖₊
  ((Finset.univ.sup f : NNReal) : ℝ)

/-- The concrete matrix infinity norm is exactly the maximum of the row
    1-norms. -/
theorem complexMatrixInfNorm_eq_max_row_oneNorm {m n : ℕ}
    (A : CMatrix m n) :
    complexMatrixInfNorm A =
      ((Finset.univ.sup (fun i : Fin m => ∑ j : Fin n, ‖A i j‖₊) : NNReal) : ℝ) := by
  rfl

lemma complexMatrixInfNorm_nonneg {m n : ℕ} (A : CMatrix m n) :
    0 ≤ complexMatrixInfNorm A := by
  unfold complexMatrixInfNorm
  exact NNReal.coe_nonneg _

lemma complexMatrixInfNorm_row_sum_le {m n : ℕ} (A : CMatrix m n) (i : Fin m) :
    (∑ j : Fin n, ‖A i j‖) ≤ complexMatrixInfNorm A := by
  unfold complexMatrixInfNorm
  let f : Fin m → NNReal := fun i => ∑ j : Fin n, ‖A i j‖₊
  have hnn : f i ≤ Finset.univ.sup f :=
    Finset.le_sup (s := (Finset.univ : Finset (Fin m))) (f := f) (Finset.mem_univ i)
  have hreal : ((f i : NNReal) : ℝ) ≤ ((Finset.univ.sup f : NNReal) : ℝ) := by
    exact_mod_cast hnn
  simpa [f, NNReal.coe_sum] using hreal

/-- Equation (6.13), p = infinity lower-bound form: each row 1-norm is
    bounded by the induced matrix infinity norm. -/
theorem complexMatrixInfNorm_row_oneNorm_le {m n : ℕ}
    (A : CMatrix m n) (i : Fin m) :
    complexVecOneNorm (fun j : Fin n => A i j) ≤ complexMatrixInfNorm A := by
  simpa [complexVecOneNorm] using complexMatrixInfNorm_row_sum_le A i

lemma complexMatrixInfNorm_le_of_row_sum_le {m n : ℕ} {A : CMatrix m n}
    {d : ℝ} (hd : 0 ≤ d)
    (hrows : ∀ i : Fin m, (∑ j : Fin n, ‖A i j‖) ≤ d) :
    complexMatrixInfNorm A ≤ d := by
  unfold complexMatrixInfNorm
  let f : Fin m → NNReal := fun i => ∑ j : Fin n, ‖A i j‖₊
  have hrows_nn : ∀ i, f i ≤ Real.toNNReal d := by
    intro i
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal d hd]
    simpa [f, NNReal.coe_sum] using hrows i
  have hsup : Finset.univ.sup f ≤ Real.toNNReal d :=
    Finset.sup_le (fun i _ => hrows_nn i)
  have hreal : ((Finset.univ.sup f : NNReal) : ℝ) ≤ d := by
    rw [← Real.coe_toNNReal d hd]
    exact_mod_cast hsup
  simpa [f] using hreal

lemma complexMatrixVecMul_standardBasisCVec {m n : ℕ}
    (A : CMatrix m n) (j : Fin n) :
    complexMatrixVecMul A (standardBasisCVec j) = fun i : Fin m => A i j := by
  ext i
  unfold complexMatrixVecMul standardBasisCVec
  simp [Finset.sum_ite_eq', Finset.mem_univ]

/-- Explicit linearity predicate for source-facing maps `C^n -> C^m`. -/
structure IsComplexVectorMapLinear {n m : ℕ} (T : ComplexVectorMap n m) : Prop where
  map_add : ∀ x y : CVec n,
    T (complexVecAdd x y) = complexVecAdd (T x) (T y)
  map_smul : ∀ (a : ℂ) (x : CVec n),
    T (complexVecSMul a x) = complexVecSMul a (T x)

/-- Composition of source-facing vector maps. -/
def complexVectorMapComp {n m k : ℕ} (A : ComplexVectorMap m k)
    (B : ComplexVectorMap n m) : ComplexVectorMap n k :=
  fun x => A (B x)

/-- Pointwise addition of source-facing vector maps. -/
noncomputable def complexVectorMapAdd {n m : ℕ} (A B : ComplexVectorMap n m) :
    ComplexVectorMap n m :=
  fun x => complexVecAdd (A x) (B x)

/-- Scalar multiplication of a source-facing vector map. -/
noncomputable def complexVectorMapSMul {n m : ℕ} (a : ℂ)
    (A : ComplexVectorMap n m) : ComplexVectorMap n m :=
  fun x => complexVecSMul a (A x)

/-- A source-facing square map is singular if it has a nonzero kernel vector. -/
def IsSingularComplexVectorMap {n : ℕ} (A : ComplexVectorMap n n) : Prop :=
  ∃ x : CVec n, x ≠ 0 ∧ A x = 0

lemma complexVectorMapComp_linear {n m k : ℕ} {A : ComplexVectorMap m k}
    {B : ComplexVectorMap n m} (hA : IsComplexVectorMapLinear A)
    (hB : IsComplexVectorMapLinear B) :
    IsComplexVectorMapLinear (complexVectorMapComp A B) := by
  constructor
  · intro x y
    simp [complexVectorMapComp, hB.map_add x y, hA.map_add]
  · intro a x
    simp [complexVectorMapComp, hB.map_smul a x, hA.map_smul]

lemma complexVectorMapAdd_linear {n m : ℕ} {A B : ComplexVectorMap n m}
    (hA : IsComplexVectorMapLinear A) (hB : IsComplexVectorMapLinear B) :
    IsComplexVectorMapLinear (complexVectorMapAdd A B) := by
  constructor
  · intro x y
    ext i
    simp [complexVectorMapAdd, complexVecAdd, hA.map_add, hB.map_add]
    ring
  · intro a x
    ext i
    simp [complexVectorMapAdd, complexVecAdd, complexVecSMul, hA.map_smul,
      hB.map_smul]
    ring

lemma complexVectorMapSMul_linear {n m : ℕ} {A : ComplexVectorMap n m}
    (a : ℂ) (hA : IsComplexVectorMapLinear A) :
    IsComplexVectorMapLinear (complexVectorMapSMul a A) := by
  constructor
  · intro x y
    ext i
    simp [complexVectorMapSMul, complexVecAdd, complexVecSMul, hA.map_add]
    ring
  · intro b x
    ext i
    simp [complexVectorMapSMul, complexVecSMul, hA.map_smul]
    ring

lemma complexMatrixVecMul_linear {m n : ℕ} (A : CMatrix m n) :
    IsComplexVectorMapLinear (complexMatrixVecMul A) := by
  constructor
  · intro x y
    ext i
    simp only [complexMatrixVecMul, complexVecAdd]
    calc
      (∑ j : Fin n, A i j * (x j + y j)) =
          ∑ j : Fin n, (A i j * x j + A i j * y j) := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            ring
      _ = (∑ j : Fin n, A i j * x j) + ∑ j : Fin n, A i j * y j := by
            rw [Finset.sum_add_distrib]
  · intro a x
    ext i
    simp only [complexMatrixVecMul, complexVecSMul]
    calc
      (∑ j : Fin n, A i j * (a * x j)) =
          ∑ j : Fin n, a * (A i j * x j) := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            ring
      _ = a * ∑ j : Fin n, A i j * x j := by
            rw [Finset.mul_sum]

lemma IsComplexVectorMapLinear.map_zero {n m : ℕ} {T : ComplexVectorMap n m}
    (hT : IsComplexVectorMapLinear T) : T 0 = 0 := by
  have h := hT.map_smul (0 : ℂ) (0 : CVec n)
  have hleft : complexVecSMul (0 : ℂ) (0 : CVec n) = 0 := by
    ext i
    simp [complexVecSMul]
  have hright : complexVecSMul (0 : ℂ) (T 0) = 0 := by
    ext i
    simp [complexVecSMul]
  rw [hleft, hright] at h
  exact h

/-- Predicate form of a mixed subordinate norm upper bound:
    `νβ (T x) <= c * να x` for all source vectors. -/
def MixedSubordinateBound {n m : ℕ} (να : CVec n → ℝ) (νβ : CVec m → ℝ)
    (T : ComplexVectorMap n m) (c : ℝ) : Prop :=
  ∀ x : CVec n, νβ (T x) ≤ c * να x

/-- A value of the mixed subordinate norm, represented as the least admissible
    bound.  This avoids committing to the Chapter 6 `max`/`sup` matrix-norm
    machinery before that source-facing API is fixed. -/
def IsMixedSubordinateNormValue {n m : ℕ} (να : CVec n → ℝ)
    (νβ : CVec m → ℝ) (T : ComplexVectorMap n m) (c : ℝ) : Prop :=
  MixedSubordinateBound να νβ T c ∧
    ∀ d : ℝ, MixedSubordinateBound να νβ T d → c ≤ d

/-- Matrix form of a mixed subordinate upper bound, using the concrete
    matrix-vector bridge. -/
def MixedSubordinateMatrixBound {n m : ℕ} (να : CVec n → ℝ) (νβ : CVec m → ℝ)
    (A : CMatrix m n) (c : ℝ) : Prop :=
  MixedSubordinateBound να νβ (complexMatrixVecMul A) c

/-- Matrix form of a mixed subordinate norm value, represented as the least
    admissible mixed bound for the concrete matrix-vector map. -/
def IsMixedSubordinateMatrixNormValue {n m : ℕ} (να : CVec n → ℝ)
    (νβ : CVec m → ℝ) (A : CMatrix m n) (c : ℝ) : Prop :=
  IsMixedSubordinateNormValue να νβ (complexMatrixVecMul A) c

theorem mixedSubordinateMatrixBound_iff_map_bound
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    {A : CMatrix m n} {c : ℝ} :
    MixedSubordinateMatrixBound να νβ A c ↔
      MixedSubordinateBound να νβ (complexMatrixVecMul A) c := by
  rfl

theorem mixedSubordinateMatrixNormValue_iff_map_value
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    {A : CMatrix m n} {c : ℝ} :
    IsMixedSubordinateMatrixNormValue να νβ A c ↔
      IsMixedSubordinateNormValue να νβ (complexMatrixVecMul A) c := by
  rfl

/-- Equation (6.11), p = 1 upper-bound form:
    the maximum absolute column sum bounds the matrix action induced by the
    complex vector 1-norm. -/
theorem complexMatrixOneNorm_mixedSubordinateMatrixBound
    {m n : ℕ} (A : CMatrix m n) :
    MixedSubordinateMatrixBound complexVecOneNorm complexVecOneNorm A
      (complexMatrixOneNorm A) := by
  intro x
  unfold complexVecOneNorm complexMatrixVecMul
  calc
    (∑ i : Fin m, ‖∑ j : Fin n, A i j * x j‖)
        ≤ ∑ i : Fin m, ∑ j : Fin n, ‖A i j * x j‖ := by
          apply Finset.sum_le_sum
          intro i _
          exact norm_sum_le _ _
    _ = ∑ i : Fin m, ∑ j : Fin n, ‖A i j‖ * ‖x j‖ := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          exact norm_mul (A i j) (x j)
    _ = ∑ j : Fin n, ∑ i : Fin m, ‖A i j‖ * ‖x j‖ := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin n, (∑ i : Fin m, ‖A i j‖) * ‖x j‖ := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
    _ ≤ ∑ j : Fin n, complexMatrixOneNorm A * ‖x j‖ := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_right
            (complexMatrixOneNorm_col_sum_le A j) (norm_nonneg (x j))
    _ = complexMatrixOneNorm A * ∑ j : Fin n, ‖x j‖ := by
          rw [Finset.mul_sum]

/-- Equation (6.11), p = 1: for nonempty source dimension, the maximum
    absolute column sum is the least mixed subordinate bound induced by the
    complex vector 1-norm. -/
theorem complexMatrixOneNorm_isMixedSubordinateMatrixNormValue
    {m n : ℕ} (hn : 0 < n) (A : CMatrix m n) :
    IsMixedSubordinateMatrixNormValue complexVecOneNorm complexVecOneNorm A
      (complexMatrixOneNorm A) := by
  refine ⟨complexMatrixOneNorm_mixedSubordinateMatrixBound A, ?_⟩
  intro d hd
  have hd_nonneg : 0 ≤ d := by
    let j0 : Fin n := ⟨0, hn⟩
    have h := hd (standardBasisCVec j0)
    rw [complexMatrixVecMul_standardBasisCVec A j0,
      complexVecOneNorm_standardBasisCVec j0, mul_one] at h
    exact (Finset.sum_nonneg (fun i _ => norm_nonneg (A i j0))).trans h
  apply complexMatrixOneNorm_le_of_col_sum_le hd_nonneg
  intro j
  have h := hd (standardBasisCVec j)
  rw [complexMatrixVecMul_standardBasisCVec A j,
    complexVecOneNorm_standardBasisCVec j, mul_one] at h
  exact h

/-- Equation (6.11), p = infinity upper-bound form:
    the maximum absolute row sum bounds the matrix action induced by the
    complex vector infinity norm. -/
theorem complexMatrixInfNorm_mixedSubordinateMatrixBound
    {m n : ℕ} (A : CMatrix m n) :
    MixedSubordinateMatrixBound complexVecInfNorm complexVecInfNorm A
      (complexMatrixInfNorm A) := by
  intro x
  apply complexVecInfNorm_le_of_coord_le
  · exact mul_nonneg (complexMatrixInfNorm_nonneg A) (complexVecInfNorm_nonneg x)
  · intro i
    calc
      ‖complexMatrixVecMul A x i‖
          = ‖∑ j : Fin n, A i j * x j‖ := rfl
      _ ≤ ∑ j : Fin n, ‖A i j * x j‖ := norm_sum_le _ _
      _ = ∑ j : Fin n, ‖A i j‖ * ‖x j‖ := by
            apply Finset.sum_congr rfl
            intro j _
            exact norm_mul (A i j) (x j)
      _ ≤ ∑ j : Fin n, ‖A i j‖ * complexVecInfNorm x := by
            apply Finset.sum_le_sum
            intro j _
            exact mul_le_mul_of_nonneg_left
              (complexVecInfNorm_coord_le x j) (norm_nonneg (A i j))
      _ = (∑ j : Fin n, ‖A i j‖) * complexVecInfNorm x := by
            rw [Finset.sum_mul]
      _ ≤ complexMatrixInfNorm A * complexVecInfNorm x :=
            mul_le_mul_of_nonneg_right
              (complexMatrixInfNorm_row_sum_le A i) (complexVecInfNorm_nonneg x)

/-- Equation (6.11), p = infinity: for nonempty source dimension, the maximum
    absolute row sum is the least mixed subordinate bound induced by the
    complex vector infinity norm. -/
theorem complexMatrixInfNorm_isMixedSubordinateMatrixNormValue
    {m n : ℕ} (hn : 0 < n) (A : CMatrix m n) :
    IsMixedSubordinateMatrixNormValue complexVecInfNorm complexVecInfNorm A
      (complexMatrixInfNorm A) := by
  refine ⟨complexMatrixInfNorm_mixedSubordinateMatrixBound A, ?_⟩
  intro d hd
  have hd_nonneg : 0 ≤ d := by
    obtain ⟨u, hu_unit⟩ :=
      exists_unit_complexVectorNorm complexVecInfNorm_isComplexVectorNorm hn
    have h := hd u
    rw [hu_unit, mul_one] at h
    exact (complexVecInfNorm_nonneg (complexMatrixVecMul A u)).trans h
  apply complexMatrixInfNorm_le_of_row_sum_le hd_nonneg
  intro i
  let x : CVec n := fun j => complexUnitPhase (A i j)
  have hx_le_one : complexVecInfNorm x ≤ 1 := by
    apply complexVecInfNorm_le_of_coord_le _ zero_le_one
    intro j
    exact complexUnitPhase_norm_le_one (A i j)
  have hrow :
      complexMatrixVecMul A x i = (∑ j : Fin n, (‖A i j‖ : ℂ)) := by
    unfold complexMatrixVecMul
    apply Finset.sum_congr rfl
    intro j _
    exact mul_complexUnitPhase_eq_norm (A i j)
  have hsum_cast :
      (∑ j : Fin n, (‖A i j‖ : ℂ)) =
        ((∑ j : Fin n, ‖A i j‖ : ℝ) : ℂ) := by
    norm_num
  have hrow_norm :
      ‖complexMatrixVecMul A x i‖ = ∑ j : Fin n, ‖A i j‖ := by
    have hsum_nonneg : 0 ≤ ∑ j : Fin n, ‖A i j‖ :=
      Finset.sum_nonneg (fun j _ => norm_nonneg (A i j))
    rw [hrow, hsum_cast, Complex.norm_of_nonneg hsum_nonneg]
  calc
    (∑ j : Fin n, ‖A i j‖)
        = ‖complexMatrixVecMul A x i‖ := hrow_norm.symm
    _ ≤ complexVecInfNorm (complexMatrixVecMul A x) :=
        complexVecInfNorm_coord_le (complexMatrixVecMul A x) i
    _ ≤ d * complexVecInfNorm x := hd x
    _ ≤ d * 1 := mul_le_mul_of_nonneg_left hx_le_one hd_nonneg
    _ = d := by ring

/-- Values attained by a linear map on the `α`-unit sphere, measured in the
    `β`-norm.  This is the source-facing `max_{||x||_α = 1} ||T x||_β`
    carrier for equations (6.5)-(6.6). -/
def MixedUnitImageNormSet {n m : ℕ} (να : CVec n → ℝ) (νβ : CVec m → ℝ)
    (T : ComplexVectorMap n m) : Set ℝ :=
  {r | ∃ x : CVec n, να x = 1 ∧ r = νβ (T x)}

/-- Predicate form of the maximum of `||T x||_β` on the `α`-unit sphere. -/
def IsMaxMixedUnitImageNormValue {n m : ℕ} (να : CVec n → ℝ)
    (νβ : CVec m → ℝ) (T : ComplexVectorMap n m) (c : ℝ) : Prop :=
  c ∈ MixedUnitImageNormSet να νβ T ∧
    ∀ r : ℝ, r ∈ MixedUnitImageNormSet να νβ T → r ≤ c

/-- Values `||T x||_β / ||x||_α` attained by nonzero source vectors. -/
def MixedNonzeroImageRatioSet {n m : ℕ} (να : CVec n → ℝ) (νβ : CVec m → ℝ)
    (T : ComplexVectorMap n m) : Set ℝ :=
  {r | ∃ x : CVec n, x ≠ 0 ∧ r = νβ (T x) / να x}

/-- Predicate form of the maximum of `||T x||_β / ||x||_α` over nonzero
    source vectors, the first max form in Higham equation (6.5). -/
def IsMaxMixedNonzeroImageRatioValue {n m : ℕ} (να : CVec n → ℝ)
    (νβ : CVec m → ℝ) (T : ComplexVectorMap n m) (c : ℝ) : Prop :=
  c ∈ MixedNonzeroImageRatioSet να νβ T ∧
    ∀ r : ℝ, r ∈ MixedNonzeroImageRatioSet να νβ T → r ≤ c

/-- Matrix version of the unit-sphere image norm set in equations (6.5)-(6.6). -/
def MixedSubordinateMatrixUnitNormSet {n m : ℕ} (να : CVec n → ℝ)
    (νβ : CVec m → ℝ) (A : CMatrix m n) : Set ℝ :=
  MixedUnitImageNormSet να νβ (complexMatrixVecMul A)

/-- Matrix version of the nonzero-vector ratio set in equation (6.5). -/
def MixedSubordinateMatrixNonzeroRatioSet {n m : ℕ} (να : CVec n → ℝ)
    (νβ : CVec m → ℝ) (A : CMatrix m n) : Set ℝ :=
  MixedNonzeroImageRatioSet να νβ (complexMatrixVecMul A)

/-- Matrix version of the source-facing unit-sphere maximum. -/
def IsMaxMixedSubordinateMatrixNormValue {n m : ℕ} (να : CVec n → ℝ)
    (νβ : CVec m → ℝ) (A : CMatrix m n) (c : ℝ) : Prop :=
  IsMaxMixedUnitImageNormValue να νβ (complexMatrixVecMul A) c

/-- Matrix version of the source-facing nonzero-vector ratio maximum. -/
def IsMaxMixedSubordinateMatrixRatioValue {n m : ℕ} (να : CVec n → ℝ)
    (νβ : CVec m → ℝ) (A : CMatrix m n) (c : ℝ) : Prop :=
  IsMaxMixedNonzeroImageRatioValue να νβ (complexMatrixVecMul A) c

theorem isMixedSubordinateNormValue_of_isMaxMixedUnitImageNormValue
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    {T : ComplexVectorMap n m} {c : ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hTlin : IsComplexVectorMapLinear T)
    (hmax : IsMaxMixedUnitImageNormValue να νβ T c) :
    IsMixedSubordinateNormValue να νβ T c := by
  refine ⟨?_, ?_⟩
  · intro x
    by_cases hxzero : x = 0
    · have hTxzero : T x = 0 := by
        rw [hxzero]
        exact hTlin.map_zero
      have hleft : νβ (T x) = 0 := (hβ.eq_zero_iff (T x)).mpr hTxzero
      have hright : c * να x = 0 := by
        have hxnorm : να x = 0 := (hα.eq_zero_iff x).mpr hxzero
        rw [hxnorm, mul_zero]
      rw [hleft, hright]
    · have hxnorm_ne : να x ≠ 0 := by
        intro hxnorm
        exact hxzero ((hα.eq_zero_iff x).mp hxnorm)
      have hxnorm_pos : 0 < να x :=
        lt_of_le_of_ne (hα.nonneg x) (Ne.symm hxnorm_ne)
      let u : CVec n := complexVecSMul (((να x)⁻¹ : ℝ) : ℂ) x
      have hinv_nonneg : 0 ≤ (να x)⁻¹ := inv_nonneg.mpr (hα.nonneg x)
      have hu_unit : να u = 1 := by
        dsimp [u]
        rw [hα.smul, Complex.norm_of_nonneg hinv_nonneg]
        field_simp [ne_of_gt hxnorm_pos]
      have humem : νβ (T u) ∈ MixedUnitImageNormSet να νβ T :=
        ⟨u, hu_unit, rfl⟩
      have hmax_le : νβ (T u) ≤ c := hmax.2 (νβ (T u)) humem
      have hscaled_abs : |να x|⁻¹ * νβ (T x) ≤ c := by
        simpa [u, hTlin.map_smul, hβ.smul] using hmax_le
      have hscaled : (να x)⁻¹ * νβ (T x) ≤ c := by
        simpa [abs_of_nonneg (hα.nonneg x)] using hscaled_abs
      have hmul := mul_le_mul_of_nonneg_left hscaled (le_of_lt hxnorm_pos)
      calc
        νβ (T x) = να x * ((να x)⁻¹ * νβ (T x)) := by
          field_simp [ne_of_gt hxnorm_pos]
        _ ≤ να x * c := hmul
        _ = c * να x := by ring
  · intro d hd
    obtain ⟨x, hxunit, hc⟩ := hmax.1
    have hdx := hd x
    rw [hxunit, mul_one] at hdx
    rw [hc]
    exact hdx

theorem isMaxMixedNonzeroImageRatioValue_of_isMaxMixedUnitImageNormValue
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    {T : ComplexVectorMap n m} {c : ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hTlin : IsComplexVectorMapLinear T)
    (hmax : IsMaxMixedUnitImageNormValue να νβ T c) :
    IsMaxMixedNonzeroImageRatioValue να νβ T c := by
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hxunit, hc⟩ := hmax.1
    have hxne : x ≠ 0 := by
      intro hxzero
      have hxnorm : να x = 0 := (hα.eq_zero_iff x).mpr hxzero
      rw [hxunit] at hxnorm
      norm_num at hxnorm
    refine ⟨x, hxne, ?_⟩
    rw [hc, hxunit]
    ring
  · intro r hr
    obtain ⟨x, hxne, hr⟩ := hr
    have hxnorm_ne : να x ≠ 0 := by
      intro hxnorm
      exact hxne ((hα.eq_zero_iff x).mp hxnorm)
    have hxnorm_pos : 0 < να x :=
      lt_of_le_of_ne (hα.nonneg x) (Ne.symm hxnorm_ne)
    let u : CVec n := complexVecSMul (((να x)⁻¹ : ℝ) : ℂ) x
    have hinv_nonneg : 0 ≤ (να x)⁻¹ := inv_nonneg.mpr (hα.nonneg x)
    have hu_unit : να u = 1 := by
      dsimp [u]
      rw [hα.smul, Complex.norm_of_nonneg hinv_nonneg]
      field_simp [ne_of_gt hxnorm_pos]
    have humem : νβ (T u) ∈ MixedUnitImageNormSet να νβ T :=
      ⟨u, hu_unit, rfl⟩
    have hmax_le : νβ (T u) ≤ c := hmax.2 (νβ (T u)) humem
    have hscaled_abs : |να x|⁻¹ * νβ (T x) ≤ c := by
      simpa [u, hTlin.map_smul, hβ.smul] using hmax_le
    have hscaled : (να x)⁻¹ * νβ (T x) ≤ c := by
      simpa [abs_of_nonneg (hα.nonneg x)] using hscaled_abs
    rw [hr]
    calc
      νβ (T x) / να x = (να x)⁻¹ * νβ (T x) := by ring
      _ ≤ c := hscaled

theorem isMaxMixedUnitImageNormValue_of_isMaxMixedNonzeroImageRatioValue
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    {T : ComplexVectorMap n m} {c : ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hTlin : IsComplexVectorMapLinear T)
    (hmax : IsMaxMixedNonzeroImageRatioValue να νβ T c) :
    IsMaxMixedUnitImageNormValue να νβ T c := by
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hxne, hc⟩ := hmax.1
    have hxnorm_ne : να x ≠ 0 := by
      intro hxnorm
      exact hxne ((hα.eq_zero_iff x).mp hxnorm)
    have hxnorm_pos : 0 < να x :=
      lt_of_le_of_ne (hα.nonneg x) (Ne.symm hxnorm_ne)
    let u : CVec n := complexVecSMul (((να x)⁻¹ : ℝ) : ℂ) x
    have hinv_nonneg : 0 ≤ (να x)⁻¹ := inv_nonneg.mpr (hα.nonneg x)
    have hu_unit : να u = 1 := by
      dsimp [u]
      rw [hα.smul, Complex.norm_of_nonneg hinv_nonneg]
      field_simp [ne_of_gt hxnorm_pos]
    refine ⟨u, hu_unit, ?_⟩
    have hu_norm_abs :
        νβ (T u) = |να x|⁻¹ * νβ (T x) := by
      simp [u, hTlin.map_smul, hβ.smul]
    have hu_norm : νβ (T u) = (να x)⁻¹ * νβ (T x) := by
      simpa [abs_of_nonneg (hα.nonneg x)] using hu_norm_abs
    rw [hu_norm, hc]
    ring
  · intro r hr
    obtain ⟨x, hxunit, hr⟩ := hr
    have hxne : x ≠ 0 := by
      intro hxzero
      have hxnorm : να x = 0 := (hα.eq_zero_iff x).mpr hxzero
      rw [hxunit] at hxnorm
      norm_num at hxnorm
    have hratio_mem : νβ (T x) / να x ∈ MixedNonzeroImageRatioSet να νβ T :=
      ⟨x, hxne, rfl⟩
    have hratio_le := hmax.2 (νβ (T x) / να x) hratio_mem
    rw [hr]
    rw [hxunit, div_one] at hratio_le
    exact hratio_le

theorem isMaxMixedNonzeroImageRatioValue_iff_unitImageNormValue
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    {T : ComplexVectorMap n m} {c : ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hTlin : IsComplexVectorMapLinear T) :
    IsMaxMixedNonzeroImageRatioValue να νβ T c ↔
      IsMaxMixedUnitImageNormValue να νβ T c := by
  constructor
  · exact isMaxMixedUnitImageNormValue_of_isMaxMixedNonzeroImageRatioValue
      hα hβ hTlin
  · exact isMaxMixedNonzeroImageRatioValue_of_isMaxMixedUnitImageNormValue
      hα hβ hTlin

/-- Higham equation (6.7), bound form: composing an `α -> γ` map with a
    `γ -> β` map gives the product bound. -/
theorem mixedSubordinateBound_comp {n m k : ℕ}
    {να : CVec n → ℝ} {νγ : CVec m → ℝ} {νβ : CVec k → ℝ}
    {A : ComplexVectorMap m k} {B : ComplexVectorMap n m} {a b : ℝ}
    (ha0 : 0 ≤ a) (hA : MixedSubordinateBound νγ νβ A a)
    (hB : MixedSubordinateBound να νγ B b) :
    MixedSubordinateBound να νβ (complexVectorMapComp A B) (a * b) := by
  intro x
  calc
    νβ (complexVectorMapComp A B x) ≤ a * νγ (B x) := hA (B x)
    _ ≤ a * (b * να x) := mul_le_mul_of_nonneg_left (hB x) ha0
    _ = (a * b) * να x := by ring

/-- Higham equation (6.7), value form for the local least-bound predicate. -/
theorem mixedSubordinateNormValue_comp_le {n m k : ℕ}
    {να : CVec n → ℝ} {νγ : CVec m → ℝ} {νβ : CVec k → ℝ}
    {A : ComplexVectorMap m k} {B : ComplexVectorMap n m} {a b c : ℝ}
    (ha0 : 0 ≤ a)
    (hcomp : IsMixedSubordinateNormValue να νβ (complexVectorMapComp A B) c)
    (hA : IsMixedSubordinateNormValue νγ νβ A a)
    (hB : IsMixedSubordinateNormValue να νγ B b) :
    c ≤ a * b :=
  hcomp.2 (a * b) (mixedSubordinateBound_comp ha0 hA.1 hB.1)

/-- In finite dimensions, a positive least mixed subordinate bound is attained
    by some unit source vector.  This closes the compactness/norm-attainment
    step needed in Higham's proof of equation (6.10) for the local
    source-facing least-bound predicate. -/
theorem exists_unit_vector_attaining_mixedSubordinateNormValue
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    {T : ComplexVectorMap n m} (hTlin : IsComplexVectorMapLinear T)
    {c : ℝ} (hTval : IsMixedSubordinateNormValue να νβ T c)
    (hcpos : 0 < c) :
    ∃ x : CVec n, να x = 1 ∧ νβ (T x) = c := by
  let instSrcNAG : NormedAddCommGroup (NormedCVec n να) :=
    NormedCVec.normedAddCommGroup hα
  letI : NormedAddCommGroup (NormedCVec n να) := instSrcNAG
  let instSrcModule : Module ℂ (NormedCVec n να) :=
    (NormedCVec.equiv n να).module ℂ
  letI : Module ℂ (NormedCVec n να) := instSrcModule
  let instSrcNS : NormedSpace ℂ (NormedCVec n να) :=
    NormedSpace.ofCore (𝕜 := ℂ) (NormedCVec.normedSpaceCore hα)
  letI : NormedSpace ℂ (NormedCVec n να) := instSrcNS
  let instTgtNAG : NormedAddCommGroup (NormedCVec m νβ) :=
    NormedCVec.normedAddCommGroup hβ
  letI : NormedAddCommGroup (NormedCVec m νβ) := instTgtNAG
  let instTgtModule : Module ℂ (NormedCVec m νβ) :=
    (NormedCVec.equiv m νβ).module ℂ
  letI : Module ℂ (NormedCVec m νβ) := instTgtModule
  let instTgtNS : NormedSpace ℂ (NormedCVec m νβ) :=
    NormedSpace.ofCore (𝕜 := ℂ) (NormedCVec.normedSpaceCore hβ)
  letI : NormedSpace ℂ (NormedCVec m νβ) := instTgtNS
  let instSrcFin : FiniteDimensional ℂ (NormedCVec n να) := by
    let e : CVec n ≃ₗ[ℂ] NormedCVec n να :=
      { toFun := fun x => ⟨x⟩
        invFun := NormedCVec.val
        left_inv := by intro x; rfl
        right_inv := by intro x; cases x; rfl
        map_add' := by intro x y; rfl
        map_smul' := by intro a x; rfl }
    exact LinearEquiv.finiteDimensional e
  letI : FiniteDimensional ℂ (NormedCVec n να) := instSrcFin
  let L : NormedCVec n να →ₗ[ℂ] NormedCVec m νβ :=
    { toFun := fun x => ⟨T x.val⟩
      map_add' := by
        intro x y
        apply NormedCVec.ext
        have h := hTlin.map_add x.val y.val
        simpa [complexVecAdd] using h
      map_smul' := by
        intro a x
        apply NormedCVec.ext
        have h := hTlin.map_smul a x.val
        simpa [complexVecSMul] using h }
  have hLbound : ∀ x : NormedCVec n να, ‖L x‖ ≤ c * ‖x‖ := by
    intro x
    exact hTval.1 x.val
  let f : NormedCVec n να →L[ℂ] NormedCVec m νβ :=
    L.mkContinuous c hLbound
  have hf_norm_le : ‖f‖ ≤ c :=
    LinearMap.mkContinuous_norm_le L (le_of_lt hcpos) hLbound
  have hbound_op : MixedSubordinateBound να νβ T ‖f‖ := by
    intro x
    have h := f.le_opNorm (⟨x⟩ : NormedCVec n να)
    simpa [f, L, NormedCVec.norm_eq] using h
  have hc_le_norm : c ≤ ‖f‖ := hTval.2 ‖f‖ hbound_op
  have hfnorm : ‖f‖ = c := le_antisymm hf_norm_le hc_le_norm
  have hfpos : 0 < ‖f‖ := by
    rw [hfnorm]
    exact hcpos
  obtain ⟨x, hxnorm, hfxnorm⟩ :=
    @exists_unit_vector_norm_apply_eq_opNorm_finiteDimensional
      (NormedCVec n να) (NormedCVec m νβ)
      instSrcNAG instSrcNS instSrcFin instTgtNAG instTgtNS f hfpos
  refine ⟨x.val, ?_, ?_⟩
  · simpa [NormedCVec.norm_eq] using hxnorm
  · have hfx : ‖f x‖ = c := hfxnorm.trans hfnorm
    simpa [f, L, NormedCVec.norm_eq] using hfx

/-- View a complex linear functional as a source-facing map into `C^1`. -/
noncomputable def dualFunctionalAsVectorMap {n : ℕ} (φ : CVec n → ℂ) :
    ComplexVectorMap n 1 :=
  fun v _ => φ v

lemma dualFunctionalAsVectorMap_linear {n : ℕ} {φ : CVec n → ℂ}
    (hφ : IsComplexLinearForm φ) :
    IsComplexVectorMapLinear (dualFunctionalAsVectorMap φ) := by
  constructor
  · intro x y
    ext i
    simp [dualFunctionalAsVectorMap, complexVecAdd, hφ.map_add]
  · intro a x
    ext i
    simp [dualFunctionalAsVectorMap, complexVecSMul, hφ.map_smul]

lemma complexVecOneNorm_dualFunctionalAsVectorMap_apply
    {n : ℕ} (φ : CVec n → ℂ) (x : CVec n) :
    complexVecOneNorm (dualFunctionalAsVectorMap φ x) = ‖φ x‖ := by
  unfold complexVecOneNorm dualFunctionalAsVectorMap
  simp

/-- A dual functional least-bound value is the same as a mixed subordinate
    least-bound value for the associated map into `C^1`. -/
theorem dualFunctional_as_mixedSubordinateNormValue
    {n : ℕ} {ν : CVec n → ℝ} {φ : CVec n → ℂ} {d : ℝ}
    (hφd : IsDualFunctionalNormValue ν φ d) :
    IsComplexVectorMapLinear (dualFunctionalAsVectorMap φ) ∧
      IsMixedSubordinateNormValue ν complexVecOneNorm
        (dualFunctionalAsVectorMap φ) d := by
  refine ⟨dualFunctionalAsVectorMap_linear hφd.linear, ?_⟩
  refine ⟨?_, ?_⟩
  · intro x
    simpa [complexVecOneNorm_dualFunctionalAsVectorMap_apply] using hφd.bound x
  · intro e he
    apply hφd.least e
    intro x
    simpa [complexVecOneNorm_dualFunctionalAsVectorMap_apply] using he x

/-- Positive dual least-bound values attain the source-facing unit-vector
    maximum in equation (6.2). -/
theorem isMaxDualUnitFunctionalNormValue_of_dualFunctionalNormValue_pos
    {n : ℕ} {ν : CVec n → ℝ} (hν : IsComplexVectorNorm ν)
    {φ : CVec n → ℂ} {d : ℝ}
    (hφd : IsDualFunctionalNormValue ν φ d) (hdpos : 0 < d) :
    IsMaxDualUnitFunctionalNormValue ν φ d := by
  have hβ : IsComplexVectorNorm (complexVecOneNorm (n := 1)) :=
    complexVecOneNorm_isComplexVectorNorm
  obtain ⟨hTlin, hTval⟩ := dualFunctional_as_mixedSubordinateNormValue hφd
  obtain ⟨x, hxunit, hTx⟩ :=
    exists_unit_vector_attaining_mixedSubordinateNormValue
      hν hβ hTlin hTval hdpos
  refine ⟨?_, ?_⟩
  · refine ⟨x, hxunit, ?_⟩
    exact hTx.symm.trans (complexVecOneNorm_dualFunctionalAsVectorMap_apply φ x)
  · intro r hr
    obtain ⟨x, hxunit, hr⟩ := hr
    rw [hr]
    have h := hφd.bound x
    rwa [hxunit, mul_one] at h

/-- The zero dual least-bound case still attains the unit-vector maximum when
    the source dimension is nonempty: every unit value is zero. -/
theorem isMaxDualUnitFunctionalNormValue_of_dualFunctionalNormValue_zero
    {n : ℕ} {ν : CVec n → ℝ} (hν : IsComplexVectorNorm ν) (hn : 0 < n)
    {φ : CVec n → ℂ}
    (hφd : IsDualFunctionalNormValue ν φ 0) :
    IsMaxDualUnitFunctionalNormValue ν φ 0 := by
  obtain ⟨u, hu_unit⟩ := exists_unit_complexVectorNorm hν hn
  have hφu_le_zero : ‖φ u‖ ≤ 0 := by
    have h := hφd.bound u
    simpa [hu_unit] using h
  have hφu_zero : ‖φ u‖ = 0 :=
    le_antisymm hφu_le_zero (norm_nonneg (φ u))
  refine ⟨?_, ?_⟩
  · exact ⟨u, hu_unit, hφu_zero.symm⟩
  · intro r hr
    obtain ⟨x, hxunit, hr⟩ := hr
    rw [hr]
    have h := hφd.bound x
    rwa [hxunit, mul_one] at h

/-- Nonempty-dimensional form of equation (6.2): every local dual least-bound
    value is the maximum over unit vectors. -/
theorem isMaxDualUnitFunctionalNormValue_of_dualFunctionalNormValue
    {n : ℕ} {ν : CVec n → ℝ} (hν : IsComplexVectorNorm ν) (hn : 0 < n)
    {φ : CVec n → ℂ} {d : ℝ}
    (hφd : IsDualFunctionalNormValue ν φ d) :
    IsMaxDualUnitFunctionalNormValue ν φ d := by
  have hdnonneg := dualFunctionalNormValue_nonneg_of_nonempty hν hn hφd
  rcases lt_or_eq_of_le hdnonneg with hdpos | hdzero
  · exact isMaxDualUnitFunctionalNormValue_of_dualFunctionalNormValue_pos hν hφd hdpos
  · subst hdzero
    exact isMaxDualUnitFunctionalNormValue_of_dualFunctionalNormValue_zero hν hn hφd

/-- Nonempty-dimensional form of equation (6.2): every local dual least-bound
    value is also the maximum of the nonzero-vector ratio. -/
theorem isMaxDualNonzeroFunctionalRatioValue_of_dualFunctionalNormValue
    {n : ℕ} {ν : CVec n → ℝ} (hν : IsComplexVectorNorm ν) (hn : 0 < n)
    {φ : CVec n → ℂ} {d : ℝ}
    (hφd : IsDualFunctionalNormValue ν φ d) :
    IsMaxDualNonzeroFunctionalRatioValue ν φ d := by
  exact isMaxDualNonzeroFunctionalRatioValue_of_isMaxDualUnitFunctionalNormValue
    hν hφd.linear
    (isMaxDualUnitFunctionalNormValue_of_dualFunctionalNormValue hν hn hφd)

/-- Source-facing maximum form of equations (6.5)-(6.6): a positive least
    mixed subordinate value is attained as the maximum of `||T x||_β` over
    `||x||_α = 1`. -/
theorem isMaxMixedUnitImageNormValue_of_mixedSubordinateNormValue
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    {T : ComplexVectorMap n m} (hTlin : IsComplexVectorMapLinear T)
    {c : ℝ} (hTval : IsMixedSubordinateNormValue να νβ T c)
    (hcpos : 0 < c) :
    IsMaxMixedUnitImageNormValue να νβ T c := by
  obtain ⟨x, hxunit, hTx⟩ :=
    exists_unit_vector_attaining_mixedSubordinateNormValue hα hβ hTlin hTval hcpos
  refine ⟨?_, ?_⟩
  · exact ⟨x, hxunit, hTx.symm⟩
  · intro r hr
    obtain ⟨y, hyunit, hr⟩ := hr
    rw [hr]
    have hbound := hTval.1 y
    rwa [hyunit, mul_one] at hbound

theorem isMixedSubordinateMatrixNormValue_of_isMaxMatrixNormValue
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    {A : CMatrix m n} {c : ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hmax : IsMaxMixedSubordinateMatrixNormValue να νβ A c) :
    IsMixedSubordinateMatrixNormValue να νβ A c :=
  isMixedSubordinateNormValue_of_isMaxMixedUnitImageNormValue hα hβ
    (complexMatrixVecMul_linear A) hmax

/-- Concrete matrix form of equations (6.5)-(6.6): a positive least mixed
    subordinate matrix norm value is the maximum of the target norm on the
    source unit sphere. -/
theorem isMaxMixedSubordinateMatrixNormValue_of_matrixNormValue
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    {A : CMatrix m n} {c : ℝ}
    (hAval : IsMixedSubordinateMatrixNormValue να νβ A c)
    (hcpos : 0 < c) :
    IsMaxMixedSubordinateMatrixNormValue να νβ A c :=
  isMaxMixedUnitImageNormValue_of_mixedSubordinateNormValue hα hβ
    (complexMatrixVecMul_linear A) hAval hcpos

theorem isMaxMixedSubordinateMatrixRatioValue_iff_unitNormValue
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    {A : CMatrix m n} {c : ℝ} :
    IsMaxMixedSubordinateMatrixRatioValue να νβ A c ↔
      IsMaxMixedSubordinateMatrixNormValue να νβ A c :=
  isMaxMixedNonzeroImageRatioValue_iff_unitImageNormValue hα hβ
    (complexMatrixVecMul_linear A)

/-- Concrete matrix form of Higham equation (6.5): for a positive local mixed
    subordinate matrix norm value, the nonzero-vector ratio maximum and the
    unit-sphere maximum agree at the same value. -/
theorem isMaxMixedSubordinateMatrixRatioValue_of_matrixNormValue
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    {A : CMatrix m n} {c : ℝ}
    (hAval : IsMixedSubordinateMatrixNormValue να νβ A c)
    (hcpos : 0 < c) :
    IsMaxMixedSubordinateMatrixRatioValue να νβ A c :=
  (isMaxMixedSubordinateMatrixRatioValue_iff_unitNormValue hα hβ).2
    (isMaxMixedSubordinateMatrixNormValue_of_matrixNormValue hα hβ hAval hcpos)

/-- Rank-one operator `v ↦ φ(v) y`. -/
noncomputable def rankOneOperator {n m : ℕ} (φ : CVec n → ℂ) (y : CVec m) :
    ComplexVectorMap n m :=
  fun v j => φ v * y j

lemma rankOneOperator_linear {n m : ℕ} {φ : CVec n → ℂ} {y : CVec m}
    (hφ : IsComplexLinearForm φ) :
    IsComplexVectorMapLinear (rankOneOperator φ y) := by
  constructor
  · intro u v
    ext j
    simp [rankOneOperator, complexVecAdd, hφ.map_add]
    ring
  · intro a v
    ext j
    simp [rankOneOperator, complexVecSMul, hφ.map_smul, mul_assoc]

lemma rankOneOperator_apply_norm {n m : ℕ} {νβ : CVec m → ℝ}
    (hβ : IsComplexVectorNorm νβ) (φ : CVec n → ℂ) (y : CVec m)
    (v : CVec n) :
    νβ (rankOneOperator φ y v) = ‖φ v‖ * νβ y := by
  exact hβ.smul (φ v) y

/-- Concrete matrix representing the rank-one map `v ↦ φ(v)y`, using the
    standard basis expansion of the linear functional `φ`. -/
noncomputable def rankOneCMatrixFromFunctional {n m : ℕ}
    (φ : CVec n → ℂ) (y : CVec m) : CMatrix m n :=
  fun i j => y i * φ (standardBasisCVec j)

lemma complexMatrixVecMul_rankOneCMatrixFromFunctional {n m : ℕ}
    {φ : CVec n → ℂ} {y : CVec m} (hφ : IsComplexLinearForm φ) :
    complexMatrixVecMul (rankOneCMatrixFromFunctional φ y) =
      rankOneOperator φ y := by
  ext v i
  calc
    (complexMatrixVecMul (rankOneCMatrixFromFunctional φ y) v) i =
        ∑ j : Fin n, (y i * φ (standardBasisCVec j)) * v j := by
          rfl
    _ = y i * ∑ j : Fin n, v j * φ (standardBasisCVec j) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro j _hj
          ring
    _ = y i * φ v := by
          rw [← hφ.apply_eq_sum_basis v]
    _ = (rankOneOperator φ y v) i := by
          simp [rankOneOperator]
          ring

/-- Scaling a map by a positive real scalar scales its local mixed subordinate
    norm value by the same scalar. -/
theorem mixedSubordinateNormValue_smul_real_pos
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hβ : IsComplexVectorNorm νβ) {T : ComplexVectorMap n m} {c r : ℝ}
    (hrpos : 0 < r) (hT : IsMixedSubordinateNormValue να νβ T c) :
    IsMixedSubordinateNormValue να νβ (complexVectorMapSMul (r : ℂ) T) (r * c) := by
  refine ⟨?_, ?_⟩
  · intro v
    calc
      νβ (complexVectorMapSMul (r : ℂ) T v)
          = r * νβ (T v) := by
            rw [complexVectorMapSMul, hβ.smul, Complex.norm_of_nonneg (le_of_lt hrpos)]
      _ ≤ r * (c * να v) := mul_le_mul_of_nonneg_left (hT.1 v) (le_of_lt hrpos)
      _ = (r * c) * να v := by ring
  · intro d hd
    have hbound : MixedSubordinateBound να νβ T (d / r) := by
      intro v
      have h := hd v
      rw [complexVectorMapSMul, hβ.smul, Complex.norm_of_nonneg (le_of_lt hrpos)] at h
      have hdiv : νβ (T v) ≤ (d * να v) / r := by
        exact (le_div_iff₀ hrpos).mpr (by simpa [mul_comm] using h)
      calc
        νβ (T v) ≤ (d * να v) / r := hdiv
        _ = (d / r) * να v := by ring
    have hc_le : c ≤ d / r := hT.2 (d / r) hbound
    calc
      r * c ≤ r * (d / r) := mul_le_mul_of_nonneg_left hc_le (le_of_lt hrpos)
      _ = d := by field_simp [ne_of_gt hrpos]

/-- Rank-one mixed subordinate norm formula, in the local least-bound model:
    if `φ` has dual functional norm value `d`, then `v ↦ φ(v)y` has mixed
    subordinate norm value `νβ y * d`, provided the target vector has positive
    `β`-norm.  This is the source-facing functional version of Problem 6.2. -/
theorem rankOneOperator_isMixedSubordinateNormValue_of_dualFunctionalNormValue
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hβ : IsComplexVectorNorm νβ) {φ : CVec n → ℂ} {y : CVec m} {d : ℝ}
    (hφ : IsDualFunctionalNormValue να φ d) (hypos : 0 < νβ y) :
    IsComplexVectorMapLinear (rankOneOperator φ y) ∧
      IsMixedSubordinateNormValue να νβ (rankOneOperator φ y) (νβ y * d) := by
  refine ⟨rankOneOperator_linear hφ.linear, ?_⟩
  refine ⟨?_, ?_⟩
  · intro v
    have hy_nonneg : 0 ≤ νβ y := le_of_lt hypos
    calc
      νβ (rankOneOperator φ y v) = ‖φ v‖ * νβ y :=
        rankOneOperator_apply_norm hβ φ y v
      _ ≤ (d * να v) * νβ y :=
        mul_le_mul_of_nonneg_right (hφ.bound v) hy_nonneg
      _ = (νβ y * d) * να v := by ring
  · intro c hc
    have hdual_bound : DualFunctionalBound να φ (c / νβ y) := by
      intro v
      have h := hc v
      rw [rankOneOperator_apply_norm hβ φ y v] at h
      have hdiv : ‖φ v‖ ≤ (c * να v) / νβ y :=
        (le_div_iff₀ hypos).mpr h
      calc
        ‖φ v‖ ≤ (c * να v) / νβ y := hdiv
        _ = (c / νβ y) * να v := by ring
    have hd_le : d ≤ c / νβ y := hφ.least (c / νβ y) hdual_bound
    calc
      νβ y * d ≤ νβ y * (c / νβ y) :=
        mul_le_mul_of_nonneg_left hd_le (le_of_lt hypos)
      _ = c := by field_simp [ne_of_gt hypos]

/-- Concrete matrix form of Problem 6.2 for a rank-one map represented through
    a dual functional. -/
theorem rankOneCMatrix_isMixedSubordinateMatrixNormValue_of_dualFunctionalNormValue
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hβ : IsComplexVectorNorm νβ) {φ : CVec n → ℂ} {y : CVec m} {d : ℝ}
    (hφ : IsDualFunctionalNormValue να φ d) (hypos : 0 < νβ y) :
    IsMixedSubordinateMatrixNormValue να νβ (rankOneCMatrixFromFunctional φ y)
      (νβ y * d) := by
  have hmap := complexMatrixVecMul_rankOneCMatrixFromFunctional
    (n := n) (m := m) (φ := φ) (y := y) hφ.linear
  have hval :=
    (rankOneOperator_isMixedSubordinateNormValue_of_dualFunctionalNormValue
      hβ hφ hypos).2
  dsimp [IsMixedSubordinateMatrixNormValue]
  rw [hmap]
  exact hval

lemma rankOneOperator_apply_of_norming_value {n m : ℕ} (φ : CVec n → ℂ)
    (x : CVec n) (y : CVec m) (hφx : φ x = 1) :
    rankOneOperator φ y x = y := by
  ext j
  simp [rankOneOperator, hφx]

lemma mixedSubordinateNormValue_one_of_bound_attained {n m : ℕ}
    {να : CVec n → ℝ} {νβ : CVec m → ℝ} {T : ComplexVectorMap n m}
    {x : CVec n} (hx : να x = 1) (hTx : νβ (T x) = 1)
    (hbound : MixedSubordinateBound να νβ T 1) :
    IsMixedSubordinateNormValue να νβ T 1 := by
  refine ⟨hbound, ?_⟩
  intro d hd
  have h := hd x
  rw [hTx, hx] at h
  simpa using h

/-- Higham, 2nd ed., Chapter 6, Lemma 6.3 foundation:
    given a unit source vector with a norming functional and a unit target
    vector, the rank-one operator `v ↦ φ(v)y` maps the source vector to the
    target vector and has mixed subordinate norm value `1`.

    The following existence theorem discharges the norming-functional hypothesis
    for unit vectors using the Hahn-Banach bridge above. -/
theorem rankOne_isMixedSubordinateNormValue_one_of_normingFunctional
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hβ : IsComplexVectorNorm νβ) {x : CVec n} {y : CVec m}
    {φ : CVec n → ℂ} (hx : να x = 1) (hy : νβ y = 1)
    (hφ : IsNormingFunctionalAt να x φ) :
    IsMixedSubordinateNormValue να νβ (rankOneOperator φ y) 1 ∧
      rankOneOperator φ y x = y := by
  have hmap : rankOneOperator φ y x = y :=
    rankOneOperator_apply_of_norming_value φ x y hφ.value
  have hbound : MixedSubordinateBound να νβ (rankOneOperator φ y) 1 := by
    intro v
    calc
      νβ (rankOneOperator φ y v) = ‖φ v‖ * νβ y :=
        rankOneOperator_apply_norm hβ φ y v
      _ = ‖φ v‖ := by rw [hy, mul_one]
      _ ≤ να v := hφ.bound v
      _ = 1 * να v := by ring
  exact ⟨mixedSubordinateNormValue_one_of_bound_attained hx (by rw [hmap, hy]) hbound,
    hmap⟩

/-- Concrete matrix form of the rank-one construction in Lemma 6.3. -/
theorem rankOneCMatrix_isMixedSubordinateMatrixNormValue_one_of_normingFunctional
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hβ : IsComplexVectorNorm νβ) {x : CVec n} {y : CVec m}
    {φ : CVec n → ℂ} (hx : να x = 1) (hy : νβ y = 1)
    (hφ : IsNormingFunctionalAt να x φ) :
    IsMixedSubordinateMatrixNormValue να νβ (rankOneCMatrixFromFunctional φ y) 1 ∧
      complexMatrixVecMul (rankOneCMatrixFromFunctional φ y) x = y := by
  have hmap := complexMatrixVecMul_rankOneCMatrixFromFunctional
    (n := n) (m := m) (φ := φ) (y := y) hφ.linear
  have hmain :=
    rankOne_isMixedSubordinateNormValue_one_of_normingFunctional hβ hx hy hφ
  constructor
  · dsimp [IsMixedSubordinateMatrixNormValue]
    rw [hmap]
    exact hmain.1
  · rw [hmap]
    exact hmain.2

/-- Higham, 2nd ed., Chapter 6, Lemma 6.3 foundation:
    for any unit source vector `x` and unit target vector `y`, there is a
    rank-one map with mixed subordinate norm value `1` that maps `x` to `y`. -/
theorem exists_rankOne_isMixedSubordinateNormValue_one
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    {x : CVec n} {y : CVec m} (hx : να x = 1) (hy : νβ y = 1) :
    ∃ T : ComplexVectorMap n m,
      IsComplexVectorMapLinear T ∧
        IsMixedSubordinateNormValue να νβ T 1 ∧ T x = y := by
  obtain ⟨φ, hφ⟩ := NormedCVec.exists_normingFunctionalAt_of_unit_vector hα hx
  have hmain :=
    rankOne_isMixedSubordinateNormValue_one_of_normingFunctional hβ hx hy hφ
  exact ⟨rankOneOperator φ y, rankOneOperator_linear hφ.linear, hmain⟩

/-- Higham, 2nd ed., Chapter 6, Lemma 6.3 foundation, concrete matrix form:
    for unit source and target vectors there is a rank-one matrix with local
    mixed subordinate matrix norm value `1` mapping the source vector to the
    target vector. -/
theorem exists_rankOneCMatrix_isMixedSubordinateMatrixNormValue_one
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    {x : CVec n} {y : CVec m} (hx : να x = 1) (hy : νβ y = 1) :
    ∃ A : CMatrix m n,
      IsMixedSubordinateMatrixNormValue να νβ A 1 ∧
        complexMatrixVecMul A x = y := by
  obtain ⟨φ, hφ⟩ := NormedCVec.exists_normingFunctionalAt_of_unit_vector hα hx
  have hmain :=
    rankOneCMatrix_isMixedSubordinateMatrixNormValue_one_of_normingFunctional
      hβ hx hy hφ
  exact ⟨rankOneCMatrixFromFunctional φ y, hmain⟩

/-- Theorem 6.5 lower-bound foundation: if `A + Δ` is singular and `Ainv`
    is a left inverse of `A`, then any mixed subordinate bound `d` for `Δ`
    satisfies the reciprocal condition-number lower bound
    `(a * s)⁻¹ <= d / a`, where `a` is the norm value of `A` and `s` is an
    upper bound for `Ainv`. -/
theorem singular_perturbation_inv_condition_le_relative_bound
    {n : ℕ} {να νβ : CVec n → ℝ} {A Ainv Δ : ComplexVectorMap n n}
    {a s d : ℝ} (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (ha : 0 < a) (hs : 0 < s)
    (hAinv_left : ∀ x : CVec n, Ainv (A x) = x)
    (hAinv_bound : MixedSubordinateBound νβ να Ainv s)
    (hΔ_bound : MixedSubordinateBound να νβ Δ d)
    (hsing : IsSingularComplexVectorMap (complexVectorMapAdd A Δ)) :
    (a * s)⁻¹ ≤ d / a := by
  obtain ⟨x, hxne, hxsing⟩ := hsing
  have hxnorm_ne : να x ≠ 0 := by
    intro hxzero
    exact hxne ((hα.eq_zero_iff x).mp hxzero)
  have hxnorm_pos : 0 < να x := lt_of_le_of_ne (hα.nonneg x) (Ne.symm hxnorm_ne)
  have hA_eq_neg : A x = complexVecSMul (-1 : ℂ) (Δ x) := by
    ext i
    have hcoord := congrFun hxsing i
    simp [complexVectorMapAdd, complexVecAdd, complexVecSMul] at hcoord ⊢
    exact eq_neg_of_add_eq_zero_left hcoord
  have hx_eq : x = Ainv (complexVecSMul (-1 : ℂ) (Δ x)) := by
    calc
      x = Ainv (A x) := (hAinv_left x).symm
      _ = Ainv (complexVecSMul (-1 : ℂ) (Δ x)) := by rw [hA_eq_neg]
  have hnorm_le : να x ≤ (s * d) * να x := by
    calc
      να x = να (Ainv (complexVecSMul (-1 : ℂ) (Δ x))) := congrArg να hx_eq
      _ ≤ s * νβ (complexVecSMul (-1 : ℂ) (Δ x)) :=
        hAinv_bound (complexVecSMul (-1 : ℂ) (Δ x))
      _ = s * νβ (Δ x) := by
        rw [hβ.smul (-1 : ℂ) (Δ x)]
        norm_num
      _ ≤ s * (d * να x) :=
        mul_le_mul_of_nonneg_left (hΔ_bound x) (le_of_lt hs)
      _ = (s * d) * να x := by ring
  have hone_le : 1 ≤ s * d := by
    exact le_of_mul_le_mul_right (by simpa [one_mul] using hnorm_le) hxnorm_pos
  have haspos : 0 < a * s := mul_pos ha hs
  rw [inv_le_iff_one_le_mul₀ haspos]
  calc
    1 ≤ s * d := hone_le
    _ = (d / a) * (a * s) := by field_simp [ne_of_gt ha]

/-- Theorem 6.5 upper-bound foundation: from a positive mixed subordinate value
    `s` for a right inverse `Ainv`, construct a perturbation `Δ` with mixed
    subordinate value `s⁻¹` such that `A + Δ` is singular. -/
theorem exists_singular_perturbation_attaining_inverse_bound
    {n : ℕ} {να νβ : CVec n → ℝ} {A Ainv : ComplexVectorMap n n}
    {s : ℝ} (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hA_right : ∀ y : CVec n, A (Ainv y) = y)
    (hAinv_lin : IsComplexVectorMapLinear Ainv)
    (hAinv : IsMixedSubordinateNormValue νβ να Ainv s) (hspos : 0 < s) :
    ∃ Δ : ComplexVectorMap n n,
      IsComplexVectorMapLinear Δ ∧
        IsMixedSubordinateNormValue να νβ Δ s⁻¹ ∧
          IsSingularComplexVectorMap (complexVectorMapAdd A Δ) := by
  obtain ⟨y, hy, hAinvy⟩ :=
    exists_unit_vector_attaining_mixedSubordinateNormValue hβ hα hAinv_lin hAinv hspos
  let x : CVec n := Ainv y
  let xunit : CVec n := complexVecSMul (((s⁻¹ : ℝ) : ℂ)) x
  have hsinv_pos : 0 < s⁻¹ := inv_pos.mpr hspos
  have hxunit : να xunit = 1 := by
    dsimp [xunit, x]
    rw [hα.smul, Complex.norm_of_nonneg (le_of_lt hsinv_pos), hAinvy]
    field_simp [ne_of_gt hspos]
  let negy : CVec n := complexVecSMul (-1 : ℂ) y
  have hnegy : νβ negy = 1 := by
    dsimp [negy]
    rw [hβ.smul, hy]
    norm_num
  obtain ⟨B, hBlin, hBval, hBxunit⟩ :=
    exists_rankOne_isMixedSubordinateNormValue_one hα hβ hxunit hnegy
  let Δ : ComplexVectorMap n n := complexVectorMapSMul (((s⁻¹ : ℝ) : ℂ)) B
  refine ⟨Δ, ?_, ?_, ?_⟩
  · exact complexVectorMapSMul_linear (((s⁻¹ : ℝ) : ℂ)) hBlin
  · have hscaled :=
      mixedSubordinateNormValue_smul_real_pos hβ hsinv_pos hBval
    simpa [Δ] using hscaled
  · refine ⟨x, ?_, ?_⟩
    · intro hxzero
      have hxnorm_zero : να x = 0 := (hα.eq_zero_iff x).mpr hxzero
      change να (Ainv y) = 0 at hxnorm_zero
      rw [hAinvy] at hxnorm_zero
      exact (ne_of_gt hspos) hxnorm_zero
    · have hΔx : Δ x = negy := by
        have hmap := hBlin.map_smul (((s⁻¹ : ℝ) : ℂ)) x
        change B (complexVecSMul (((s⁻¹ : ℝ) : ℂ)) x) =
          complexVecSMul (((s⁻¹ : ℝ) : ℂ)) (B x) at hmap
        change complexVecSMul (((s⁻¹ : ℝ) : ℂ)) (B x) = negy
        rw [← hmap]
        simpa [xunit] using hBxunit
      ext i
      simp [complexVectorMapAdd, complexVecAdd, hA_right y, x, hΔx, negy,
        complexVecSMul]

/-- Relative form of the attaining perturbation in the local Theorem 6.5 model:
    if `a > 0` is the mixed subordinate value of `A`, the constructed singular
    perturbation has relative size `(a * s)⁻¹`. -/
theorem exists_singular_perturbation_attaining_relative_inverse_bound
    {n : ℕ} {να νβ : CVec n → ℝ} {A Ainv : ComplexVectorMap n n}
    {a s : ℝ} (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (ha : 0 < a)
    (hA_right : ∀ y : CVec n, A (Ainv y) = y)
    (hAinv_lin : IsComplexVectorMapLinear Ainv)
    (hAinv : IsMixedSubordinateNormValue νβ να Ainv s) (hspos : 0 < s) :
    ∃ Δ : ComplexVectorMap n n,
      IsComplexVectorMapLinear Δ ∧
        IsMixedSubordinateNormValue να νβ Δ s⁻¹ ∧
          IsSingularComplexVectorMap (complexVectorMapAdd A Δ) ∧
            s⁻¹ / a = (a * s)⁻¹ := by
  obtain ⟨Δ, hΔlin, hΔval, hsing⟩ :=
    exists_singular_perturbation_attaining_inverse_bound hα hβ hA_right
      hAinv_lin hAinv hspos
  refine ⟨Δ, hΔlin, hΔval, hsing, ?_⟩
  field_simp [ne_of_gt ha, ne_of_gt hspos]

/-- Local predicate for the relative mixed distance from `A` to singularity.
    The value `a` records the mixed subordinate value of `A`; `ρ` is a least
    relative perturbation size, and the infimum is represented by an explicit
    attaining linear perturbation. -/
def IsMixedRelativeSingularDistanceValue
    {n : ℕ} (να νβ : CVec n → ℝ) (A : ComplexVectorMap n n)
    (a ρ : ℝ) : Prop :=
  IsMixedSubordinateNormValue να νβ A a ∧
    (∀ (Δ : ComplexVectorMap n n) (d : ℝ),
      IsComplexVectorMapLinear Δ →
        IsMixedSubordinateNormValue να νβ Δ d →
          IsSingularComplexVectorMap (complexVectorMapAdd A Δ) →
            ρ ≤ d / a) ∧
    ∃ Δ : ComplexVectorMap n n, ∃ d : ℝ,
      IsComplexVectorMapLinear Δ ∧
        IsMixedSubordinateNormValue να νβ Δ d ∧
          IsSingularComplexVectorMap (complexVectorMapAdd A Δ) ∧ d / a = ρ

/-- Candidate relative distances `||ΔA||_{α,β} / ||A||_{α,β}` for singular
    perturbations in the local mixed least-bound model. -/
def MixedRelativeSingularDistanceSet
    {n : ℕ} (να νβ : CVec n → ℝ) (A : ComplexVectorMap n n)
    (a : ℝ) : Set ℝ :=
  {ρ | ∃ Δ : ComplexVectorMap n n, ∃ d : ℝ,
    IsComplexVectorMapLinear Δ ∧
      IsMixedSubordinateNormValue να νβ Δ d ∧
        IsSingularComplexVectorMap (complexVectorMapAdd A Δ) ∧ ρ = d / a}

/-- Source-facing local `min` form of the relative distance to singularity. -/
def IsMinimumMixedRelativeSingularDistance
    {n : ℕ} (να νβ : CVec n → ℝ) (A : ComplexVectorMap n n)
    (a ρ : ℝ) : Prop :=
  ρ ∈ MixedRelativeSingularDistanceSet να νβ A a ∧
    ∀ r : ℝ, r ∈ MixedRelativeSingularDistanceSet να νβ A a → ρ ≤ r

/-- Product-form mixed condition number value in the local least-bound model.
    This records the right-hand side of Higham equation (6.8); it is not yet
    the perturbation-limit definition from the first half of Theorem 6.4. -/
def IsMixedConditionNumberProductValue
    {n : ℕ} (να νβ : CVec n → ℝ) (A Ainv : ComplexVectorMap n n)
    (κ : ℝ) : Prop :=
  ∃ a s : ℝ,
    IsMixedSubordinateNormValue να νβ A a ∧
      IsMixedSubordinateNormValue νβ να Ainv s ∧ κ = a * s

theorem mixedConditionNumberProductValue_norm_mul_inverse_norm
    {n : ℕ} {να νβ : CVec n → ℝ} {A Ainv : ComplexVectorMap n n}
    {a s : ℝ} (hA : IsMixedSubordinateNormValue να νβ A a)
    (hAinv : IsMixedSubordinateNormValue νβ να Ainv s) :
    IsMixedConditionNumberProductValue να νβ A Ainv (a * s) := by
  exact ⟨a, s, hA, hAinv, rfl⟩

theorem isMinimumMixedRelativeSingularDistance_of_value
    {n : ℕ} {να νβ : CVec n → ℝ} {A : ComplexVectorMap n n}
    {a ρ : ℝ} (hρ : IsMixedRelativeSingularDistanceValue να νβ A a ρ) :
    IsMinimumMixedRelativeSingularDistance να νβ A a ρ := by
  refine ⟨?_, ?_⟩
  · obtain ⟨Δ, d, hΔlin, hΔval, hsing, hrel⟩ := hρ.2.2
    exact ⟨Δ, d, hΔlin, hΔval, hsing, hrel.symm⟩
  · intro r hr
    obtain ⟨Δ, d, hΔlin, hΔval, hsing, hr⟩ := hr
    rw [hr]
    exact hρ.2.1 Δ d hΔlin hΔval hsing

/-- Local Theorem 6.5 model: for an invertible source-facing map `A`, if
    `a = ||A||_{α,β}` and `s = ||A⁻¹||_{β,α}` in the local least-bound model,
    then the attained relative distance to singularity is `(a*s)⁻¹`. -/
theorem mixedRelativeSingularDistanceValue_eq_inv_norm_mul_inverse_norm
    {n : ℕ} {να νβ : CVec n → ℝ} {A Ainv : ComplexVectorMap n n}
    {a s : ℝ} (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (ha : 0 < a) (hs : 0 < s)
    (hA : IsMixedSubordinateNormValue να νβ A a)
    (hAinv_left : ∀ x : CVec n, Ainv (A x) = x)
    (hAinv_right : ∀ y : CVec n, A (Ainv y) = y)
    (hAinv_lin : IsComplexVectorMapLinear Ainv)
    (hAinv : IsMixedSubordinateNormValue νβ να Ainv s) :
    IsMixedRelativeSingularDistanceValue να νβ A a ((a * s)⁻¹) := by
  refine ⟨hA, ?_, ?_⟩
  · intro Δ d _hΔlin hΔval hsing
    exact singular_perturbation_inv_condition_le_relative_bound hα hβ ha hs
      hAinv_left hAinv.1 hΔval.1 hsing
  · obtain ⟨Δ, hΔlin, hΔval, hsing, hrel⟩ :=
      exists_singular_perturbation_attaining_relative_inverse_bound hα hβ ha
        hAinv_right hAinv_lin hAinv hs
    exact ⟨Δ, s⁻¹, hΔlin, hΔval, hsing, hrel⟩

/-- Local source-facing `min` version of Theorem 6.5: the minimum relative
    singular perturbation size is `(||A||_{α,β} ||A⁻¹||_{β,α})⁻¹` in the
    local least-bound model. -/
theorem mixedRelativeSingularDistance_min_eq_inv_norm_mul_inverse_norm
    {n : ℕ} {να νβ : CVec n → ℝ} {A Ainv : ComplexVectorMap n n}
    {a s : ℝ} (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (ha : 0 < a) (hs : 0 < s)
    (hA : IsMixedSubordinateNormValue να νβ A a)
    (hAinv_left : ∀ x : CVec n, Ainv (A x) = x)
    (hAinv_right : ∀ y : CVec n, A (Ainv y) = y)
    (hAinv_lin : IsComplexVectorMapLinear Ainv)
    (hAinv : IsMixedSubordinateNormValue νβ να Ainv s) :
    IsMinimumMixedRelativeSingularDistance να νβ A a ((a * s)⁻¹) := by
  exact isMinimumMixedRelativeSingularDistance_of_value
    (mixedRelativeSingularDistanceValue_eq_inv_norm_mul_inverse_norm hα hβ
      ha hs hA hAinv_left hAinv_right hAinv_lin hAinv)

/-- Local source-facing reciprocal condition-number form of Theorem 6.5:
    for the product-form condition-number value `κ = ||A||_{α,β} ||A⁻¹||_{β,α}`,
    the relative distance-to-singularity minimum is `κ⁻¹`. -/
theorem mixedRelativeSingularDistance_min_eq_inv_conditionNumberProduct
    {n : ℕ} {να νβ : CVec n → ℝ} {A Ainv : ComplexVectorMap n n}
    {a s : ℝ} (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (ha : 0 < a) (hs : 0 < s)
    (hA : IsMixedSubordinateNormValue να νβ A a)
    (hAinv_left : ∀ x : CVec n, Ainv (A x) = x)
    (hAinv_right : ∀ y : CVec n, A (Ainv y) = y)
    (hAinv_lin : IsComplexVectorMapLinear Ainv)
    (hAinv : IsMixedSubordinateNormValue νβ να Ainv s) :
    ∃ κ : ℝ,
      IsMixedConditionNumberProductValue να νβ A Ainv κ ∧
        IsMinimumMixedRelativeSingularDistance να νβ A a κ⁻¹ := by
  refine ⟨a * s, mixedConditionNumberProductValue_norm_mul_inverse_norm hA hAinv, ?_⟩
  exact mixedRelativeSingularDistance_min_eq_inv_norm_mul_inverse_norm hα hβ
    ha hs hA hAinv_left hAinv_right hAinv_lin hAinv

/-- Equation (6.9), upper-bound skeleton: if `S` has mixed subordinate value
    `s` as a `β -> α` map and `Δ` has `α -> β` bound `1`, then
    `S ∘ Δ ∘ S` has `β -> α` bound `s^2`. -/
theorem mixedSubordinate_inverseSandwich_bound
    {n : ℕ} {να νβ : CVec n → ℝ} {S Δ : ComplexVectorMap n n} {s : ℝ}
    (hs0 : 0 ≤ s)
    (hS : IsMixedSubordinateNormValue νβ να S s)
    (hΔ : MixedSubordinateBound να νβ Δ 1) :
    MixedSubordinateBound νβ να
      (complexVectorMapComp S (complexVectorMapComp Δ S)) (s ^ 2) := by
  have hDS : MixedSubordinateBound νβ νβ (complexVectorMapComp Δ S) (1 * s) :=
    mixedSubordinateBound_comp (by norm_num) hΔ hS.1
  have hSDS : MixedSubordinateBound νβ να
      (complexVectorMapComp S (complexVectorMapComp Δ S)) (s * (1 * s)) :=
    mixedSubordinateBound_comp hs0 hS.1 hDS
  simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hSDS

/-- Equation (6.9), upper-bound value form for the local least-bound predicate. -/
theorem mixedSubordinate_inverseSandwich_value_le
    {n : ℕ} {να νβ : CVec n → ℝ} {S Δ : ComplexVectorMap n n} {s c : ℝ}
    (hs0 : 0 ≤ s)
    (hS : IsMixedSubordinateNormValue νβ να S s)
    (hΔ : MixedSubordinateBound να νβ Δ 1)
    (hcomp : IsMixedSubordinateNormValue νβ να
      (complexVectorMapComp S (complexVectorMapComp Δ S)) c) :
    c ≤ s ^ 2 :=
  hcomp.2 (s ^ 2) (mixedSubordinate_inverseSandwich_bound hs0 hS hΔ)

/-- Equation (6.9), lower-bound construction under an explicit norm-attainment
    witness for `S`: if `νβ y = 1` and `να (S y) = s`, then some unit mixed
    perturbation `Δ` makes the sandwich attain `s^2` at `y`. -/
theorem exists_inverseSandwich_attains_square
    {n : ℕ} {να νβ : CVec n → ℝ} {S : ComplexVectorMap n n} {s : ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hSlin : IsComplexVectorMapLinear S) (hspos : 0 < s)
    {y : CVec n} (hy : νβ y = 1) (hSy : να (S y) = s) :
    ∃ Δ : ComplexVectorMap n n,
      IsComplexVectorMapLinear Δ ∧
        IsMixedSubordinateNormValue να νβ Δ 1 ∧
          να (complexVectorMapComp S (complexVectorMapComp Δ S) y) = s ^ 2 := by
  let x : CVec n := complexVecSMul (((s⁻¹ : ℝ) : ℂ)) (S y)
  have hs_nonneg : 0 ≤ s := le_of_lt hspos
  have hsinv_nonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hs_nonneg
  have hx : να x = 1 := by
    dsimp [x]
    rw [hα.smul, Complex.norm_of_nonneg hsinv_nonneg, hSy]
    field_simp [ne_of_gt hspos]
  have hsinv_mul : (s : ℂ) * (((s⁻¹ : ℝ) : ℂ)) = 1 := by
    rw [← Complex.ofReal_mul]
    norm_num [mul_inv_cancel₀ (ne_of_gt hspos)]
  have hSy_eq : S y = complexVecSMul (s : ℂ) x := by
    ext i
    dsimp [x, complexVecSMul]
    rw [← mul_assoc, hsinv_mul, one_mul]
  obtain ⟨Δ, hΔlin, hΔval, hΔx⟩ :=
    exists_rankOne_isMixedSubordinateNormValue_one hα hβ hx hy
  refine ⟨Δ, hΔlin, hΔval, ?_⟩
  have hΔSy : Δ (S y) = complexVecSMul (s : ℂ) y := by
    rw [hSy_eq, hΔlin.map_smul, hΔx]
  have hSand :
      complexVectorMapComp S (complexVectorMapComp Δ S) y =
        complexVecSMul (s : ℂ) (S y) := by
    simp [complexVectorMapComp, hΔSy, hSlin.map_smul]
  calc
    να (complexVectorMapComp S (complexVectorMapComp Δ S) y)
        = να (complexVecSMul (s : ℂ) (S y)) := by rw [hSand]
    _ = ‖(s : ℂ)‖ * να (S y) := hα.smul (s : ℂ) (S y)
    _ = s * s := by rw [Complex.norm_of_nonneg hs_nonneg, hSy]
    _ = s ^ 2 := by ring

/-- Equation (6.9), lower-bound value form under explicit norm attainment. -/
theorem exists_inverseSandwich_value_ge_square
    {n : ℕ} {να νβ : CVec n → ℝ} {S : ComplexVectorMap n n} {s : ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hSlin : IsComplexVectorMapLinear S) (hspos : 0 < s)
    {y : CVec n} (hy : νβ y = 1) (hSy : να (S y) = s) :
    ∃ Δ : ComplexVectorMap n n,
      IsComplexVectorMapLinear Δ ∧
        IsMixedSubordinateNormValue να νβ Δ 1 ∧
          ∀ c : ℝ,
            IsMixedSubordinateNormValue νβ να
              (complexVectorMapComp S (complexVectorMapComp Δ S)) c →
              s ^ 2 ≤ c := by
  obtain ⟨Δ, hΔlin, hΔval, hattain⟩ :=
    exists_inverseSandwich_attains_square hα hβ hSlin hspos hy hSy
  refine ⟨Δ, hΔlin, hΔval, ?_⟩
  intro c hcomp
  have h := hcomp.1 y
  rw [hattain, hy] at h
  simpa using h

/-- Equation (6.9), packaged equality route under explicit norm attainment:
    some unit mixed perturbation `Δ` makes the sandwich norm value exactly
    `s^2`, and all unit mixed perturbations are bounded above by `s^2`. -/
theorem exists_inverseSandwich_value_eq_square_of_attained
    {n : ℕ} {να νβ : CVec n → ℝ} {S : ComplexVectorMap n n} {s : ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hSlin : IsComplexVectorMapLinear S)
    (hS : IsMixedSubordinateNormValue νβ να S s) (hspos : 0 < s)
    {y : CVec n} (hy : νβ y = 1) (hSy : να (S y) = s) :
    ∃ Δ : ComplexVectorMap n n,
      IsComplexVectorMapLinear Δ ∧
        IsMixedSubordinateNormValue να νβ Δ 1 ∧
          ∀ c : ℝ,
            IsMixedSubordinateNormValue νβ να
              (complexVectorMapComp S (complexVectorMapComp Δ S)) c →
              c = s ^ 2 := by
  obtain ⟨Δ, hΔlin, hΔval, hlower⟩ :=
    exists_inverseSandwich_value_ge_square hα hβ hSlin hspos hy hSy
  refine ⟨Δ, hΔlin, hΔval, ?_⟩
  intro c hcomp
  apply le_antisymm
  · exact mixedSubordinate_inverseSandwich_value_le (le_of_lt hspos) hS hΔval.1 hcomp
  · exact hlower c hcomp

/-- Equation (6.9), packaged equality route with the finite-dimensional
    norm-attainment step discharged from the positive mixed subordinate value
    of `S`. -/
theorem exists_inverseSandwich_value_eq_square
    {n : ℕ} {να νβ : CVec n → ℝ} {S : ComplexVectorMap n n} {s : ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hSlin : IsComplexVectorMapLinear S)
    (hS : IsMixedSubordinateNormValue νβ να S s) (hspos : 0 < s) :
    ∃ Δ : ComplexVectorMap n n,
      IsComplexVectorMapLinear Δ ∧
        IsMixedSubordinateNormValue να νβ Δ 1 ∧
          ∀ c : ℝ,
            IsMixedSubordinateNormValue νβ να
              (complexVectorMapComp S (complexVectorMapComp Δ S)) c →
              c = s ^ 2 := by
  obtain ⟨y, hy, hSy⟩ :=
    exists_unit_vector_attaining_mixedSubordinateNormValue hβ hα hSlin hS hspos
  exact exists_inverseSandwich_value_eq_square_of_attained
    hα hβ hSlin hS hspos hy hSy

end LeanFpAnalysis.FP
