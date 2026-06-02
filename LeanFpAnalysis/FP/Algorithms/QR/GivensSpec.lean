-- Algorithms/QR/GivensSpec.lean
--
-- Givens rotation definition and algebraic properties (Higham §18.5),
-- plus backward error model for Givens application (Lemma 18.7).
--
-- A Givens rotation G(p,q,c,s) ∈ ℝⁿˣⁿ differs from the identity only
-- at entries (p,p)=c, (q,q)=c, (p,q)=s, (q,p)=-s.
-- When c² + s² = 1, G is orthogonal. Applying G in floating-point
-- yields ŷ = (G + ΔG)x with ‖ΔG‖_F ≤ c (Lemma 18.7).

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra

namespace LeanFpAnalysis.FP

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- §18.5  Givens rotation definition
-- ============================================================

/-- **Givens rotation** G(p,q,c,s) ∈ ℝⁿˣⁿ (§18.5).

    Differs from the identity only at entries
    (p,p)=c, (q,q)=c, (p,q)=s, (q,p)=−s.
    When c² + s² = 1, G is orthogonal. -/
noncomputable def givensRotation (n : ℕ) (p q : Fin n) (c s : ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    if i = p ∧ j = p then c
    else if i = q ∧ j = q then c
    else if i = p ∧ j = q then s
    else if i = q ∧ j = p then -s
    else if i = j then 1
    else 0

/-- Concrete floating-point application of a Givens rotation with supplied
    exact parameters `c` and `s`.

    Only the two affected components are rounded:

    * `y_p = fl_add (fl_mul c x_p) (fl_mul s x_q)`;
    * `y_q = fl_sub (fl_mul c x_q) (fl_mul s x_p)`;
    * all other entries are copied exactly.

    This is the low-level algorithmic object needed before rebuilding
    Givens QR end-to-end.  It assumes `c` and `s` have already been supplied;
    a separate rotation-construction kernel is still needed for full Givens QR. -/
noncomputable def fl_givensApply (fp : FPModel) (n : ℕ)
    (p q : Fin n) (c s : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i =>
    if i = p then
      fp.fl_add (fp.fl_mul c (x p)) (fp.fl_mul s (x q))
    else if i = q then
      fp.fl_sub (fp.fl_mul c (x q)) (fp.fl_mul s (x p))
    else
      x i

-- ============================================================
-- Point-value lemmas for givensRotation
-- ============================================================

-- Row p: G(p, j) = if j=p then c else if j=q then s else 0
private lemma giv_row_p (n : ℕ) (p q : Fin n) (c s : ℝ) (hpq : p ≠ q) (j : Fin n) :
    givensRotation n p q c s p j =
    if j = p then c else if j = q then s else 0 := by
  unfold givensRotation
  by_cases h1 : j = p
  · simp [h1]
  · by_cases h2 : j = q
    · simp [h1, h2, hpq]
    · simp [h1, h2, hpq, Ne.symm h1]

-- Row q: G(q, j) = if j=p then -s else if j=q then c else 0
private lemma giv_row_q (n : ℕ) (p q : Fin n) (c s : ℝ) (hpq : p ≠ q) (j : Fin n) :
    givensRotation n p q c s q j =
    if j = p then -s else if j = q then c else 0 := by
  have hqp := hpq.symm
  unfold givensRotation
  by_cases h1 : j = p
  · simp [h1, hqp, hpq]
  · by_cases h2 : j = q
    · simp [h1, h2, hqp, hpq]
    · simp [h1, h2, hqp, Ne.symm h2]

-- Column k (k ∉ {p,q}): G(i, k) = if i=k then 1 else 0 for any i
-- (The column index k≠p,q means all ∧-branches checking j=p or j=q are false)
private lemma giv_col_other (n : ℕ) (p q : Fin n) (c s : ℝ)
    (i k : Fin n) (hkp : k ≠ p) (hkq : k ≠ q) :
    givensRotation n p q c s i k = if i = k then 1 else 0 := by
  unfold givensRotation
  simp [hkp, hkq, Ne.symm hkp, Ne.symm hkq]

-- Row k (k ∉ {p,q}): G(k, j) = if k=j then 1 else 0 for any j
private lemma giv_row_other (n : ℕ) (p q : Fin n) (c s : ℝ)
    (k j : Fin n) (hkp : k ≠ p) (hkq : k ≠ q) :
    givensRotation n p q c s k j = if k = j then 1 else 0 := by
  unfold givensRotation; simp [hkp, hkq]

-- Column p: G(i, p) = if i=p then c else if i=q then -s else 0
private lemma giv_col_p (n : ℕ) (p q : Fin n) (c s : ℝ) (hpq : p ≠ q) (i : Fin n) :
    givensRotation n p q c s i p =
    if i = p then c else if i = q then -s else 0 := by
  have hqp := hpq.symm
  unfold givensRotation
  by_cases h1 : i = p
  · simp [h1, hqp]
  · by_cases h2 : i = q
    · simp [h1, h2, hqp, hpq]
    · simp [h1, h2, Ne.symm h1]

-- Column q: G(i, q) = if i=p then s else if i=q then c else 0
private lemma giv_col_q (n : ℕ) (p q : Fin n) (c s : ℝ) (hpq : p ≠ q) (i : Fin n) :
    givensRotation n p q c s i q =
    if i = p then s else if i = q then c else 0 := by
  have hqp := hpq.symm
  unfold givensRotation
  by_cases h1 : i = p
  · simp [h1, hpq, hqp]
  · by_cases h2 : i = q
    · simp [h1, h2, hqp]
    · simp [h1, h2, Ne.symm h2]

@[simp] theorem fl_givensApply_p (fp : FPModel) (n : ℕ)
    (p q : Fin n) (c s : ℝ) (x : Fin n → ℝ) :
    fl_givensApply fp n p q c s x p =
      fp.fl_add (fp.fl_mul c (x p)) (fp.fl_mul s (x q)) := by
  simp [fl_givensApply]

@[simp] theorem fl_givensApply_q (fp : FPModel) (n : ℕ)
    (p q : Fin n) (c s : ℝ) (x : Fin n → ℝ) (hpq : p ≠ q) :
    fl_givensApply fp n p q c s x q =
      fp.fl_sub (fp.fl_mul c (x q)) (fp.fl_mul s (x p)) := by
  simp [fl_givensApply, hpq.symm]

@[simp] theorem fl_givensApply_other (fp : FPModel) (n : ℕ)
    (p q i : Fin n) (c s : ℝ) (x : Fin n → ℝ)
    (hip : i ≠ p) (hiq : i ≠ q) :
    fl_givensApply fp n p q c s x i = x i := by
  simp [fl_givensApply, hip, hiq]

/-- Exact `p`-component of applying a Givens rotation to a vector. -/
theorem givensRotation_matMulVec_p (n : ℕ) (p q : Fin n)
    (c s : ℝ) (x : Fin n → ℝ) (hpq : p ≠ q) :
    matMulVec n (givensRotation n p q c s) x p =
      c * x p + s * x q := by
  let f : Fin n → ℝ := fun j =>
    (if j = p then c else if j = q then s else 0) * x j
  have hp : p ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ p
  have hq : q ∈ (Finset.univ : Finset (Fin n)).erase p :=
    Finset.mem_erase.mpr ⟨hpq.symm, Finset.mem_univ q⟩
  have hrest : ∑ j ∈ (Finset.univ.erase p).erase q, f j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj
    have hjq : j ≠ q := hj.1
    have hjp : j ≠ p := hj.2
    simp [f, hjp, hjq]
  unfold matMulVec
  calc
    (∑ j : Fin n, givensRotation n p q c s p j * x j)
        = ∑ j : Fin n, f j := by
        apply Finset.sum_congr rfl
        intro j _
        simp [f, giv_row_p n p q c s hpq j]
    _ = f p + f q + ∑ j ∈ (Finset.univ.erase p).erase q, f j := by
        rw [← Finset.add_sum_erase _ f hp, ← Finset.add_sum_erase _ f hq]
        ring
    _ = c * x p + s * x q := by
        rw [hrest]
        simp [f, hpq.symm]

/-- Exact `q`-component of applying a Givens rotation to a vector. -/
theorem givensRotation_matMulVec_q (n : ℕ) (p q : Fin n)
    (c s : ℝ) (x : Fin n → ℝ) (hpq : p ≠ q) :
    matMulVec n (givensRotation n p q c s) x q =
      c * x q - s * x p := by
  let f : Fin n → ℝ := fun j =>
    (if j = p then -s else if j = q then c else 0) * x j
  have hp : p ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ p
  have hq : q ∈ (Finset.univ : Finset (Fin n)).erase p :=
    Finset.mem_erase.mpr ⟨hpq.symm, Finset.mem_univ q⟩
  have hrest : ∑ j ∈ (Finset.univ.erase p).erase q, f j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj
    have hjq : j ≠ q := hj.1
    have hjp : j ≠ p := hj.2
    simp [f, hjp, hjq]
  unfold matMulVec
  calc
    (∑ j : Fin n, givensRotation n p q c s q j * x j)
        = ∑ j : Fin n, f j := by
        apply Finset.sum_congr rfl
        intro j _
        simp [f, giv_row_q n p q c s hpq j]
    _ = f p + f q + ∑ j ∈ (Finset.univ.erase p).erase q, f j := by
        rw [← Finset.add_sum_erase _ f hp, ← Finset.add_sum_erase _ f hq]
        ring
    _ = c * x q - s * x p := by
        rw [hrest]
        simp [f, hpq.symm]
        ring

/-- Unaffected components of an exact Givens application are copied. -/
theorem givensRotation_matMulVec_other (n : ℕ) (p q i : Fin n)
    (c s : ℝ) (x : Fin n → ℝ) (hip : i ≠ p) (hiq : i ≠ q) :
    matMulVec n (givensRotation n p q c s) x i = x i := by
  unfold matMulVec
  rw [show (∑ j : Fin n, givensRotation n p q c s i j * x j) =
      ∑ j : Fin n, (if i = j then 1 else 0) * x j from by
        apply Finset.sum_congr rfl
        intro j _
        rw [giv_row_other n p q c s i j hip hiq]]
  simp [Finset.sum_ite_eq, Finset.mem_univ]

/-- G(p,q,c,s) is orthogonal when c² + s² = 1 and p ≠ q.

    Proof: GᵀG and GGᵀ both equal I. For each (i,j), the sum ∑_k G_{ki}G_{kj}
    has at most 3 nonzero terms (k=p, k=q, k=i or k=j), which collapse
    using c²+s²=1. -/
theorem givensRotation_orthogonal (n : ℕ) (p q : Fin n) (c s : ℝ)
    (hpq : p ≠ q) (hcs : c ^ 2 + s ^ 2 = 1) :
    IsOrthogonal n (givensRotation n p q c s) := by
  have hqp : q ≠ p := hpq.symm
  have hcs' : c * c + s * s = 1 := by nlinarith [hcs]
  -- Sum splitting: extract k=p and k=q terms
  have sum_split : ∀ f : Fin n → ℝ,
      ∑ k, f k = f p + f q + ∑ k ∈ (Finset.univ.erase p).erase q, f k := by
    intro f
    have hp := Finset.mem_univ p
    have hq : q ∈ (Finset.univ : Finset (Fin n)).erase p :=
      Finset.mem_erase.mpr ⟨hqp, Finset.mem_univ q⟩
    rw [← Finset.add_sum_erase _ f hp, ← Finset.add_sum_erase _ f hq]; ring
  -- Membership in the erased set
  have mem_rest : ∀ k : Fin n, k ∈ (Finset.univ.erase p).erase q ↔ k ≠ q ∧ k ≠ p := by
    intro k; simp [Finset.mem_erase]
  -- p and q are not in the rest set
  have hpnr : p ∉ (Finset.univ.erase p).erase q := by simp [Finset.mem_erase]
  have hqnr : q ∉ (Finset.univ.erase p).erase q := by simp [Finset.mem_erase]
  -- ∑ k ∈ rest, (if k=a then 1 else 0) * (if k=b then 1 else 0)
  --   = if a ∈ rest then (if a=b then 1 else 0) else 0
  have delta_sum : ∀ (a b : Fin n),
      ∑ k ∈ (Finset.univ.erase p).erase q,
        (if k = a then (1:ℝ) else 0) * (if k = b then 1 else 0) =
      if a ∈ (Finset.univ.erase p).erase q then (if a = b then 1 else 0) else 0 := by
    intro a b
    by_cases ha : a ∈ (Finset.univ.erase p).erase q
    · rw [if_pos ha]
      trans ∑ k ∈ (Finset.univ.erase p).erase q,
          if k = a then (if a = b then (1:ℝ) else 0) else 0
      · apply Finset.sum_congr rfl; intro k _
        by_cases hka : k = a
        · subst hka; simp
        · simp [hka]
      · simp [ha]
    · rw [if_neg ha]
      apply Finset.sum_eq_zero; intro k hk
      have hka : k ≠ a := fun heq => ha (heq ▸ hk)
      simp [hka]
  constructor <;> intro i j
  · -- GᵀG = I: ∑_k G_{ki}·G_{kj} = δ_{ij}
    show ∑ k, givensRotation n p q c s k i * givensRotation n p q c s k j = _
    rw [sum_split,
        giv_row_p n p q c s hpq i, giv_row_p n p q c s hpq j,
        giv_row_q n p q c s hpq i, giv_row_q n p q c s hpq j]
    conv_lhs =>
      rw [show ∑ k ∈ (Finset.univ.erase p).erase q,
          givensRotation n p q c s k i * givensRotation n p q c s k j =
          ∑ k ∈ (Finset.univ.erase p).erase q,
            (if k = i then (1:ℝ) else 0) * (if k = j then 1 else 0) from by
        apply Finset.sum_congr rfl; intro k hk
        rw [mem_rest] at hk
        rw [giv_row_other n p q c s k i hk.2 hk.1,
            giv_row_other n p q c s k j hk.2 hk.1]]
    rw [delta_sum i j]
    by_cases hip : i = p
    · by_cases hjp : j = p
      · -- (p,p): c*c + (-s)*(-s) + 0 = 1
        subst hip; subst hjp
        simp only [if_true, if_neg hpq, if_neg hpnr]
        nlinarith
      · by_cases hjq : j = q
        · -- (p,q): c*s + (-s)*c + 0 = 0 ≠ 1
          subst hip; subst hjq
          simp only [if_true, if_neg hpq, if_neg hqp, if_neg hpnr]
          ring
        · -- (p, other j): 0 + 0 + 0 = 0 ≠ 1
          subst hip
          simp only [if_true, if_neg hjp, if_neg hjq, if_neg hpnr]
          simp [Ne.symm hjp, Ne.symm hjq]
    · by_cases hiq : i = q
      · by_cases hjp : j = p
        · -- (q,p): s*c + c*(-s) + 0 = 0 ≠ 1
          subst hiq; subst hjp
          simp only [if_neg hqp, if_true, if_neg hpq, if_neg hqnr]
          ring
        · by_cases hjq : j = q
          · -- (q,q): s*s + c*c + 0 = 1
            subst hiq; subst hjq
            simp only [if_neg hqp, if_true, if_neg hqnr]
            nlinarith
          · -- (q, other j): 0
            subst hiq
            simp only [if_neg hqp, if_true, if_neg hjp, if_neg hjq, if_neg hqnr]
            simp [Ne.symm hjp, Ne.symm hjq]
      · -- i ∉ {p,q}
        have hir : i ∈ (Finset.univ.erase p).erase q := by
          rw [mem_rest]; exact ⟨hiq, hip⟩
        simp only [if_neg hip, if_neg hiq, if_pos hir]
        by_cases hjp : j = p
        · subst hjp; simp [Ne.symm hip]
        · by_cases hjq : j = q
          · subst hjq; simp [Ne.symm hiq]
          · simp [Ne.symm hip, Ne.symm hiq]
  · -- GGᵀ = I: ∑_k G_{ik}·G_{jk} = δ_{ij}
    show ∑ k, givensRotation n p q c s i k * givensRotation n p q c s j k = _
    rw [sum_split,
        giv_col_p n p q c s hpq i, giv_col_p n p q c s hpq j,
        giv_col_q n p q c s hpq i, giv_col_q n p q c s hpq j]
    conv_lhs =>
      rw [show ∑ k ∈ (Finset.univ.erase p).erase q,
          givensRotation n p q c s i k * givensRotation n p q c s j k =
          ∑ k ∈ (Finset.univ.erase p).erase q,
            (if k = i then (1:ℝ) else 0) * (if k = j then 1 else 0) from by
        apply Finset.sum_congr rfl; intro k hk
        rw [mem_rest] at hk
        rw [giv_col_other n p q c s i k hk.2 hk.1,
            giv_col_other n p q c s j k hk.2 hk.1]
        simp only [eq_comm]]
    rw [delta_sum i j]
    by_cases hip : i = p
    · by_cases hjp : j = p
      · -- (p,p): c*c + s*s + 0 = 1
        subst hip; subst hjp
        simp only [if_true, if_neg hpq, if_neg hpnr]
        nlinarith
      · by_cases hjq : j = q
        · -- (p,q): c*(-s) + s*c + 0 = 0 ≠ 1
          subst hip; subst hjq
          simp only [if_true, if_neg hpq, if_neg hqp, if_neg hpnr]
          ring
        · -- (p, other j): 0
          subst hip
          simp only [if_true, if_neg hjp, if_neg hjq, if_neg hpnr]
          simp [Ne.symm hjp, Ne.symm hjq]
    · by_cases hiq : i = q
      · by_cases hjp : j = p
        · -- (q,p): (-s)*c + c*s + 0 = 0 ≠ 1
          subst hiq; subst hjp
          simp only [if_neg hqp, if_true, if_neg hpq, if_neg hqnr]
          ring
        · by_cases hjq : j = q
          · -- (q,q): (-s)*(-s) + c*c + 0 = 1
            subst hiq; subst hjq
            simp only [if_neg hqp, if_true, if_neg hqnr]
            nlinarith
          · -- (q, other j): 0
            subst hiq
            simp only [if_neg hqp, if_true, if_neg hjp, if_neg hjq, if_neg hqnr]
            simp [Ne.symm hjp, Ne.symm hjq]
      · -- i ∉ {p,q}
        have hir : i ∈ (Finset.univ.erase p).erase q := by
          rw [mem_rest]; exact ⟨hiq, hip⟩
        simp only [if_neg hip, if_neg hiq, if_pos hir]
        by_cases hjp : j = p
        · subst hjp; simp [Ne.symm hip]
        · by_cases hjq : j = q
          · subst hjq; simp [Ne.symm hiq]
          · simp [Ne.symm hip, Ne.symm hiq]

-- ============================================================
-- §18.5  Lemma 18.7: Givens application backward error
-- ============================================================

/-- **Backward error model for Givens application** (Lemma 18.7).

    When a Givens rotation G is applied to a vector x in
    floating-point arithmetic, the computed result ŷ satisfies
    ŷ = (G + ΔG)x where ‖ΔG‖_F ≤ c.

    This records the result of Lemma 18.7 as a reusable contract. The bound c
    is typically √2·γ₆ (6 flops per affected component). -/
structure GivensAppError (n : ℕ) (G : Fin n → Fin n → ℝ)
    (x y_hat : Fin n → ℝ) (c : ℝ) : Prop where
  /-- G is orthogonal. -/
  orth : IsOrthogonal n G
  /-- The computed result satisfies ŷ = (G + ΔG)x with ‖ΔG‖_F ≤ c. -/
  pert : ∃ ΔG : Fin n → Fin n → ℝ,
    frobNorm ΔG ≤ c ∧
    ∀ i, y_hat i = matMulVec n (fun a b => G a b + ΔG a b) x i

end LeanFpAnalysis.FP
