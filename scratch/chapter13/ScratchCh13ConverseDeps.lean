import LeanFpAnalysis.FP.Algorithms.LU.BlockLU

namespace LeanFpAnalysis.FP

open scoped BigOperators
open scoped Matrix

theorem test_leadingBlockPrefix_zero_nonsingular_of_first_block_inverse {m r : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ)}
    {A11_inv : Fin r → Fin r → ℝ}
    (hInvLeft : ∀ s t : Fin r,
      ∑ l : Fin r, A11_inv s l * A 0 0 l t = if s = t then 1 else 0)
    (hInvRight : ∀ s t : Fin r,
      ∑ l : Fin r, A 0 0 s l * A11_inv l t = if s = t then 1 else 0) :
    BlockMatrixNonsingular (leadingBlockPrefix13_2 A 0 (Nat.succ_pos m)) := by
  refine ⟨fun _ _ => A11_inv, ?_, ?_⟩
  · intro i j s t
    fin_cases i
    fin_cases j
    rw [Fin.sum_univ_one]
    simpa [leadingBlockPrefix13_2, blockMatrixIdentity, idBlock] using hInvLeft s t
  · intro i j s t
    fin_cases i
    fin_cases j
    rw [Fin.sum_univ_one]
    simpa [leadingBlockPrefix13_2, blockMatrixIdentity, idBlock] using hInvRight s t

theorem test_LeadingPrincipalBlockNonsingular13_2_of_first_block_inverse_of_schur {m r : ℕ}
    {A : Fin (m + 2) → Fin (m + 2) → (Fin r → Fin r → ℝ)}
    {A11_inv : Fin r → Fin r → ℝ}
    (hInvLeft : ∀ s t : Fin r,
      ∑ l : Fin r, A11_inv s l * A 0 0 l t = if s = t then 1 else 0)
    (hInvRight : ∀ s t : Fin r,
      ∑ l : Fin r, A 0 0 s l * A11_inv l t = if s = t then 1 else 0)
    (hSchurLead : LeadingPrincipalBlockNonsingular13_2 (blockSchur A A11_inv)) :
    LeadingPrincipalBlockNonsingular13_2 A := by
  intro p hp
  cases p with
  | zero =>
      have h0 :
          BlockMatrixNonsingular
            (leadingBlockPrefix13_2 A 0 (Nat.succ_pos (m + 1))) :=
        test_leadingBlockPrefix_zero_nonsingular_of_first_block_inverse
          (A := A) (A11_inv := A11_inv) hInvLeft hInvRight
      simpa [leadingBlockPrefix13_2] using h0
  | succ p =>
      have hpTail : p + 1 < m + 1 := by omega
      have hpSchur : p < m + 1 := Nat.lt_trans (Nat.lt_succ_self p) hpTail
      have hTailPrefix :
          BlockMatrixNonsingular
            (leadingBlockPrefix13_2 (blockSchur A A11_inv) p hpSchur) :=
        hSchurLead p hpTail
      have hSchurPrefix :
          BlockMatrixNonsingular
            (blockSchur
              (leadingBlockPrefix13_2 A (p + 1) (Nat.succ_lt_succ hpSchur))
              A11_inv) := by
        rw [← leadingBlockPrefix13_2_blockSchur A A11_inv p hpSchur]
        exact hTailPrefix
      have hInvLeftPrefix :
          ∀ s t : Fin r,
            ∑ l : Fin r,
              A11_inv s l *
                leadingBlockPrefix13_2 A (p + 1) (Nat.succ_lt_succ hpSchur) 0 0 l t =
              if s = t then 1 else 0 := by
        intro s t
        simpa [leadingBlockPrefix13_2] using hInvLeft s t
      have hInvRightPrefix :
          ∀ s t : Fin r,
            ∑ l : Fin r,
              leadingBlockPrefix13_2 A (p + 1) (Nat.succ_lt_succ hpSchur) 0 0 s l *
                A11_inv l t =
              if s = t then 1 else 0 := by
        intro s t
        simpa [leadingBlockPrefix13_2] using hInvRight s t
      have hAssembled :
          BlockMatrixNonsingular
            (leadingBlockPrefix13_2 A (p + 1) (Nat.succ_lt_succ hpSchur)) :=
        blockMatrixNonsingular_of_first_block_inverse_of_blockSchur_nonsingular
          (A := leadingBlockPrefix13_2 A (p + 1) (Nat.succ_lt_succ hpSchur))
          (A11_inv := A11_inv)
          hInvLeftPrefix hInvRightPrefix hSchurPrefix
      simpa [leadingBlockPrefix13_2] using hAssembled

theorem test_BlockLUFactSpec.schurTail_existsUnique_of_existsUnique_of_first_block_inverse
    {m r : ℕ}
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
  rcases block_lu_one_step A A11_inv hInvLeft Ls' Us' hTail' with
    ⟨L', U', hLU'⟩
  have hEq := hUnique L' U' hLU'
  constructor
  · ext i j s t
    have hBlock := congr_fun (congr_fun hEq.1 (Fin.succ i)) (Fin.succ j)
    exact congr_fun (congr_fun hBlock s) t
  · ext i j s t
    have hBlock := congr_fun (congr_fun hEq.2 (Fin.succ i)) (Fin.succ j)
    exact congr_fun (congr_fun hBlock s) t

end LeanFpAnalysis.FP
