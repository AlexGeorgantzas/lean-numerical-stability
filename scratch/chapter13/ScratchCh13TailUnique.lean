import LeanFpAnalysis.FP.Algorithms.LU.BlockLU

namespace LeanFpAnalysis.FP

open scoped BigOperators
open scoped Matrix

noncomputable def blockLUOneStepL_test {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ))
    (A11_inv : Fin r → Fin r → ℝ)
    (L_S : Fin m → Fin m → (Fin r → Fin r → ℝ)) :
    Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ) := fun i j =>
  if hi : i = 0 then
    if j = 0 then idBlock r else zeroBlock r
  else if hj : j = 0 then
    fun s t => ∑ l : Fin r, A i 0 s l * A11_inv l t
  else L_S (i.pred hi) (j.pred hj)

noncomputable def blockLUOneStepU_test {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ))
    (U_S : Fin m → Fin m → (Fin r → Fin r → ℝ)) :
    Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ) := fun i j =>
  if hi : i = 0 then A 0 j
  else if hj : j = 0 then zeroBlock r
  else U_S (i.pred hi) (j.pred hj)

private lemma sum_ite_eq_val_test {r : ℕ} (f : Fin r → ℝ) (s : Fin r) :
    ∑ l : Fin r, (if s = l then (1 : ℝ) else 0) * f l = f s := by
  simp [Finset.sum_ite_eq', Finset.mem_univ]

private lemma sum_ite_eq_val_right_test {r : ℕ} (f : Fin r → ℝ) (t : Fin r) :
    ∑ l : Fin r, f l * (if l = t then (1 : ℝ) else 0) = f t := by
  simp_rw [mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq', Finset.mem_univ]

theorem block_lu_one_step_explicit_test {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ))
    (A11_inv : Fin r → Fin r → ℝ)
    (hInv : ∀ s t : Fin r,
      ∑ l : Fin r, A11_inv s l * A (0 : Fin (m + 1)) (0 : Fin (m + 1)) l t =
        if s = t then 1 else 0)
    (L_S U_S : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (hS : BlockLUFactSpec m r (blockSchur A A11_inv) L_S U_S) :
    BlockLUFactSpec (m + 1) r A
      (blockLUOneStepL_test A A11_inv L_S)
      (blockLUOneStepU_test A U_S) := by
  let L := blockLUOneStepL_test A A11_inv L_S
  let U := blockLUOneStepU_test A U_S
  change BlockLUFactSpec (m + 1) r A L U
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = 0
    · subst hi; simp [L, blockLUOneStepL_test]
    · simp only [L, blockLUOneStepL_test, dif_neg hi]; exact hS.L_diag (i.pred hi)
  · intro i j hij
    by_cases hi : i = 0
    · subst hi
      have hj : j ≠ 0 := by intro h; subst h; exact lt_irrefl _ hij
      simp [L, blockLUOneStepL_test, hj]
    · have hj : j ≠ 0 := by intro h; subst h; exact absurd hij (Nat.not_lt_zero _)
      simp only [L, blockLUOneStepL_test, dif_neg hi, dif_neg hj]
      exact hS.L_upper_zero _ _ (by
        have := Fin.val_pred j hj; have := Fin.val_pred i hi
        have : i.val ≠ 0 := fun h => hi (Fin.ext h)
        have : j.val ≠ 0 := fun h => hj (Fin.ext h)
        omega)
  · intro i j hij
    by_cases hi : i = 0
    · subst hi; exact absurd hij (Nat.not_lt_zero _)
    · by_cases hj : j = 0
      · subst hj; simp [U, blockLUOneStepU_test, hi]
      · simp only [U, blockLUOneStepU_test, dif_neg hi, dif_neg hj]
        exact hS.U_lower_zero _ _ (by
          have := Fin.val_pred j hj; have := Fin.val_pred i hi
          have : i.val ≠ 0 := fun h => hi (Fin.ext h)
          have : j.val ≠ 0 := fun h => hj (Fin.ext h)
          omega)
  · intro i j s t
    rw [Fin.sum_univ_succ]
    have hL0 : ∀ p, L 0 p = if p = 0 then idBlock r else zeroBlock r :=
      fun p => by simp [L, blockLUOneStepL_test]
    have hU0 : ∀ p, U 0 p = A 0 p :=
      fun p => by simp [U, blockLUOneStepU_test]
    have hL0s : ∀ k : Fin m, L 0 (Fin.succ k) = zeroBlock r :=
      fun k => by rw [hL0]; simp [Fin.succ_ne_zero]
    have hLs0 : ∀ k : Fin m, L (Fin.succ k) 0 =
        fun s t => ∑ l, A (Fin.succ k) 0 s l * A11_inv l t :=
      fun k => by simp [L, blockLUOneStepL_test, Fin.succ_ne_zero]
    have hLss : ∀ (p q : Fin m), L (Fin.succ p) (Fin.succ q) = L_S p q :=
      fun p q => by simp [L, blockLUOneStepL_test, Fin.succ_ne_zero, Fin.pred_succ]
    have hUs0 : ∀ k : Fin m, U (Fin.succ k) 0 = zeroBlock r :=
      fun k => by simp [U, blockLUOneStepU_test, Fin.succ_ne_zero]
    have hUss : ∀ (p q : Fin m), U (Fin.succ p) (Fin.succ q) = U_S p q :=
      fun p q => by simp [U, blockLUOneStepU_test, Fin.succ_ne_zero, Fin.pred_succ]
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · subst hi; subst hj
      rw [hL0 0, if_pos rfl, hU0 0]
      have hzero : ∀ k : Fin m,
          ∑ l : Fin r, L 0 (Fin.succ k) s l * U (Fin.succ k) 0 l t = 0 :=
        fun k => by simp [hL0s k, zeroBlock]
      rw [Finset.sum_eq_zero (fun k _ => hzero k), add_zero]
      exact sum_ite_eq_val_test _ s
    · subst hi
      rw [hL0 0, if_pos rfl, hU0 j]
      have hzero : ∀ k : Fin m,
          ∑ l : Fin r, L 0 (Fin.succ k) s l * U (Fin.succ k) j l t = 0 :=
        fun k => by simp [hL0s k, zeroBlock]
      rw [Finset.sum_eq_zero (fun k _ => hzero k), add_zero]
      exact sum_ite_eq_val_test _ s
    · subst hj; rw [hU0 0]
      have hzero : ∀ k : Fin m,
          ∑ l : Fin r, L i (Fin.succ k) s l * U (Fin.succ k) 0 l t = 0 :=
        fun k => by simp [hUs0 k, zeroBlock]
      rw [Finset.sum_eq_zero (fun k _ => hzero k), add_zero]
      have hLi0 : L i 0 = fun s t => ∑ l, A i 0 s l * A11_inv l t := by
        have := hLs0 (i.pred hi); rwa [Fin.succ_pred i hi] at this
      simp_rw [hLi0, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp_rw [mul_assoc, ← Finset.mul_sum, hInv]
      exact sum_ite_eq_val_right_test _ t
    · rw [hU0 j]
      have hLi0 : L i 0 = fun s t => ∑ l, A i 0 s l * A11_inv l t := by
        have := hLs0 (i.pred hi); rwa [Fin.succ_pred i hi] at this
      simp_rw [hLi0]
      have hsec : ∀ (k : Fin m) (l : Fin r),
          L i (Fin.succ k) s l * U (Fin.succ k) j l t =
          L_S (i.pred hi) k s l * U_S k (j.pred hj) l t := by
        intro k l
        have hLeq : L i (Fin.succ k) = L_S (i.pred hi) k := by
          have := hLss (i.pred hi) k; rwa [Fin.succ_pred i hi] at this
        have hUeq : U (Fin.succ k) j = U_S k (j.pred hj) := by
          have := hUss k (j.pred hj); rwa [Fin.succ_pred j hj] at this
        rw [hLeq, hUeq]
      simp_rw [hsec]
      have hprod := hS.product_eq (i.pred hi) (j.pred hj) s t
      simp only [blockSchur, Fin.succ_pred] at hprod
      rw [hprod]
      have hfirst : ∑ l : Fin r,
          (∑ l' : Fin r, A i 0 s l' * A11_inv l' l) * A 0 j l t =
          ∑ l₁ : Fin r, ∑ l₂ : Fin r,
            A i 0 s l₁ * A11_inv l₁ l₂ * A 0 j l₂ t := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
      linarith

theorem schur_tail_existsUnique_test {m r : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ)}
    {A11_inv : Fin r → Fin r → ℝ}
    (hInvLeft : ∀ s t : Fin r,
      ∑ l : Fin r, A11_inv s l * A 0 0 l t = if s = t then 1 else 0)
    (hInvRight : ∀ s t : Fin r,
      ∑ l : Fin r, A 0 0 s l * A11_inv l t = if s = t then 1 else 0)
    (hExistsUnique :
      ∃ L U : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ),
        BlockLUFactSpec (m + 1) r A L U ∧
          ∀ L' U' : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ),
            BlockLUFactSpec (m + 1) r A L' U' → L' = L ∧ U' = U) :
    ∃ Ls Us : Fin m → Fin m → (Fin r → Fin r → ℝ),
      BlockLUFactSpec m r (blockSchur A A11_inv) Ls Us ∧
        ∀ Ls' Us' : Fin m → Fin m → (Fin r → Fin r → ℝ),
          BlockLUFactSpec m r (blockSchur A A11_inv) Ls' Us' →
            Ls' = Ls ∧ Us' = Us := by
  rcases hExistsUnique with ⟨L, U, hLU, hUnique⟩
  let Ls : Fin m → Fin m → (Fin r → Fin r → ℝ) :=
    fun i j => L (Fin.succ i) (Fin.succ j)
  let Us : Fin m → Fin m → (Fin r → Fin r → ℝ) :=
    fun i j => U (Fin.succ i) (Fin.succ j)
  have hTail : BlockLUFactSpec m r (blockSchur A A11_inv) Ls Us :=
    hLU.schurTailFactSpec_of_right_inverse A11_inv hInvRight
  refine ⟨Ls, Us, hTail, ?_⟩
  intro Ls' Us' hTail'
  let L' := blockLUOneStepL_test A A11_inv Ls'
  let U' := blockLUOneStepU_test A Us'
  have hFull' : BlockLUFactSpec (m + 1) r A L' U' := by
    simpa [L', U'] using
      block_lu_one_step_explicit_test A A11_inv hInvLeft Ls' Us' hTail'
  have hEq := hUnique L' U' hFull'
  constructor
  · ext i j s t
    have hblock := congr_fun (congr_fun hEq.1 (Fin.succ i)) (Fin.succ j)
    have hscalar := congr_fun (congr_fun hblock s) t
    simpa [L', blockLUOneStepL_test, Ls, Fin.succ_ne_zero, Fin.pred_succ] using hscalar
  · ext i j s t
    have hblock := congr_fun (congr_fun hEq.2 (Fin.succ i)) (Fin.succ j)
    have hscalar := congr_fun (congr_fun hblock s) t
    simpa [U', blockLUOneStepU_test, Us, Fin.succ_ne_zero, Fin.pred_succ] using hscalar

end LeanFpAnalysis.FP
