/-
Chapter 11 closure: the **SOLVE-side backward error** for the block-LDLᵀ linear
system solve (Higham Theorems 11.3 / 11.7, the `(A + ΔA₂) x̂ = b` half).

The factorization half — `L̂D̂L̂ᵀ = A + ΔA₁` with the printed componentwise
envelope `|ΔA₁| ≤ p(n) u (|A| + |L̂||D̂||L̂ᵀ|)` — is already derived
(`higham11_3_block_ldlt_mixed_printed`, `fl_blockLDLT_mixed_bound`,
`flMixed_envelope_le_printed`).  In those results the *solve* residual is either
absent (`ΔA₂ = 0`) or supplied as a source hypothesis `hsolve`.

This module derives the solve residual from the floating-point solve process.
The block-LDLᵀ solve of `L̂ D̂ L̂ᵀ x̂ = b` runs three substeps:

  * forward substitution   `L̂ ẑ = b`               (`fl_forwardSub`);
  * block-diagonal solve   `D̂ ŵ = ẑ`               (1×1 blocks by `fl_div`,
                                                     2×2 blocks by (11.5));
  * back substitution      `L̂ᵀ x̂ = ŵ`             (`fl_backSub`).

Each substep has a componentwise backward error; composing the three collapsed
factors `(L̂+ΔL)(D̂+ΔD)(L̂ᵀ+ΔU)` against `L̂D̂L̂ᵀ` (via the fully generic Aasen
solve-chain machinery `higham11_15_aasenChainDeltaA` /
`higham11_15_aasen_chain_source_backward_error_of_components`) yields
`(L̂D̂L̂ᵀ + ΔM) x̂ = b`.  Folding this against the proven factorization residual
`L̂D̂L̂ᵀ = A + ΔA₁` (via
`higham11_8_aasen_source_backward_error_of_factor_and_solve_residuals`) gives
`(A + ΔA₂) x̂ = b` with `ΔA₂ = ΔA₁ + ΔM` and the honest componentwise budget
`|ΔA₂| ≤ (factorization envelope) + (solve-chain envelope)`.

WHAT IS DERIVED HERE (from the fl model + existing derived results):
  * `flMixedL` is unit lower triangular (`flMixedL_diag`, `flMixedL_lower`);
  * the two OUTER triangular-solve backward errors, from the actual
    `fl_forwardSub`/`fl_backSub` runs on `L̂` and `L̂ᵀ` (Chapter 8, reused);
  * the composition of the three substep residuals into `(L̂D̂L̂ᵀ + ΔM) x̂ = b`
    and the componentwise chain budget for `ΔM`;
  * the fold against the factorization residual into `(A + ΔA₂) x̂ = b`;
  * the honest componentwise bound for `ΔA₂`.

WHAT IS ASSUMED (the sanctioned Higham (11.5) source hypothesis): the MIDDLE
block-diagonal solve backward error `(D̂ + ΔD) ŵ = ẑ` with
`|ΔD| ≤ γ_mid |D̂|`.  This is exactly Higham's equation (11.5) applied to the
block-diagonal `D̂` (a sequence of 1×1 solves — themselves derivable from
`fl_oneByOne_solve_backward_error`, provided here for the diagonal case — and
2×2 solves, the explicitly permitted assumption).  The full recursive
composition of this middle solve over the pivot schedule is a self-contained
further development; it is isolated as the single explicit hypothesis `hmid`.

The file contains only proved declarations and traceability comments.
-/
import LeanFpAnalysis.FP.Algorithms.Cholesky.BunchTridiagonalHFactorCh11Closure

open scoped BigOperators

namespace LeanFpAnalysis.FP.Ch11Closure.Solve

open LeanFpAnalysis.FP
open LeanFpAnalysis.FP.Ch11Closure
open LeanFpAnalysis.FP.Ch11Closure.Mixed

/-! ## Part 1 — `L̂ = flMixedL` is unit lower triangular

The forward/back triangular solves that bracket the block-diagonal solve run on
`L̂` and `L̂ᵀ`; both require `L̂` to have nonzero (indeed unit) diagonal and to be
lower triangular.  Both facts are structural inductions on the pivot schedule,
discharged entirely by the existing `flMixedL_*` computation lemmas. -/

/-- The computed factor `L̂` has unit diagonal. -/
theorem flMixedL_diag (fp : FPModel) :
    ∀ {n : ℕ} (s : PivotSchedule n) (A : Fin n → Fin n → ℝ) (I : Fin n),
      flMixedL fp s A I I = 1 := by
  intro n s
  induction s with
  | nil => intro A I; exact Fin.elim0 I
  | consOne s ih =>
      intro A I
      refine Fin.cases ?_ (fun i => ?_) I
      · simp
      · rw [flMixedL_consOne_ss]; exact ih (flSchurCompl _ fp A) i
  | consTwo s ih =>
      intro A I
      refine Fin.cases ?_ (fun k => ?_) I
      · simp
      · refine Fin.cases ?_ (fun i => ?_) k
        · exact flMixedL_consTwo_11 fp s A
        · rw [flMixedL_consTwo_tt]; exact ih (flSchurCompl2 _ fp A) i

/-- The computed factor `L̂` is lower triangular. -/
theorem flMixedL_lower (fp : FPModel) :
    ∀ {n : ℕ} (s : PivotSchedule n) (A : Fin n → Fin n → ℝ) (I J : Fin n),
      I.val < J.val → flMixedL fp s A I J = 0 := by
  intro n s
  induction s with
  | nil => intro A I; exact Fin.elim0 I
  | consOne s ih =>
      intro A I J
      refine Fin.cases ?_ (fun i => ?_) I
      · -- I = 0
        refine Fin.cases ?_ (fun j => ?_) J
        · intro h; exact absurd h (by rw [Fin.val_zero]; omega)
        · intro _; simp
      · -- I = i.succ
        refine Fin.cases ?_ (fun j => ?_) J
        · intro h; exact absurd h (by rw [Fin.val_zero]; omega)
        · intro h
          rw [flMixedL_consOne_ss]
          exact ih (flSchurCompl _ fp A) i j (by simp only [Fin.val_succ] at h ⊢; omega)
  | consTwo s ih =>
      intro A I J
      refine Fin.cases ?_ (fun k => ?_) I
      · -- I = 0
        refine Fin.cases ?_ (fun l => ?_) J
        · intro h; exact absurd h (by rw [Fin.val_zero]; omega)
        · refine Fin.cases ?_ (fun j => ?_) l
          · intro _; exact flMixedL_consTwo_01 fp s A
          · intro _; simp
      · refine Fin.cases ?_ (fun i => ?_) k
        · -- I = Fin.succ 0
          refine Fin.cases ?_ (fun l => ?_) J
          · intro h; exact absurd h (by rw [Fin.val_zero]; omega)
          · refine Fin.cases ?_ (fun j => ?_) l
            · intro h; exact absurd h (by simp only [Fin.val_succ, Fin.val_zero]; omega)
            · intro _; exact flMixedL_consTwo_1t fp s A j
        · -- I = i.succ.succ
          refine Fin.cases ?_ (fun l => ?_) J
          · intro h; exact absurd h (by rw [Fin.val_zero]; omega)
          · refine Fin.cases ?_ (fun j => ?_) l
            · intro h; exact absurd h (by simp only [Fin.val_succ, Fin.val_zero]; omega)
            · intro h
              rw [flMixedL_consTwo_tt]
              exact ih (flSchurCompl2 _ fp A) i j (by simp only [Fin.val_succ] at h ⊢; omega)

/-! ## Part 2 — the derived diagonal (all-1×1) middle solve

The 1×1 half of the block-diagonal middle solve is fully derivable: a diagonal
`D̂` (nonzero diagonal) is solved componentwise by `fl_div`, and the per-entry
backward error `fl_oneByOne_solve_backward_error` assembles into
`(D̂ + ΔD) ŵ = ẑ` with `|ΔD| ≤ γ₁ |D̂|`.  This is the model of the middle-solve
hypothesis used below and shows that the 1×1 blocks require no assumption. -/

/-- **Derived diagonal middle solve.**  For a diagonal `D` with nonzero diagonal,
    the componentwise `fl_div` solution `ŵ i = fl(ẑ i / D i i)` is the exact
    solution of `(D + ΔD) ŵ = ẑ` with `ΔD` supported on the diagonal and
    `|ΔD i j| ≤ γ₁ |D i j|`.  No assumption — this is `fl_oneByOne_solve_backward_error`
    applied per diagonal block. -/
theorem fl_diagonal_solve_backward_error (fp : FPModel) (n : ℕ)
    (D : Fin n → Fin n → ℝ) (z : Fin n → ℝ)
    (hDdiag : ∀ i : Fin n, D i i ≠ 0)
    (hDoff : ∀ i j : Fin n, i ≠ j → D i j = 0)
    (hval : gammaValid fp 1) :
    ∃ (w : Fin n → ℝ) (ΔD : Fin n → Fin n → ℝ),
      (∀ i j : Fin n, |ΔD i j| ≤ gamma fp 1 * |D i j|) ∧
      (∀ p : Fin n, ∑ q : Fin n, (D p q + ΔD p q) * w q = z p) := by
  -- per-diagonal-block witnesses
  have hstep : ∀ i : Fin n, ∃ Δe : ℝ,
      |Δe| ≤ gamma fp 1 * |D i i| ∧ (D i i + Δe) * fp.fl_div (z i) (D i i) = z i :=
    fun i => fl_oneByOne_solve_backward_error fp (z i) (D i i) (hDdiag i) hval
  let Δdiag : Fin n → ℝ := fun i => Classical.choose (hstep i)
  have hΔdiag_bound : ∀ i, |Δdiag i| ≤ gamma fp 1 * |D i i| := fun i =>
    (Classical.choose_spec (hstep i)).1
  have hΔdiag_eq : ∀ i, (D i i + Δdiag i) * fp.fl_div (z i) (D i i) = z i := fun i =>
    (Classical.choose_spec (hstep i)).2
  refine ⟨fun i => fp.fl_div (z i) (D i i),
    fun i j => if i = j then Δdiag i else 0, ?_, ?_⟩
  · intro i j
    by_cases hij : i = j
    · subst hij; simpa using hΔdiag_bound i
    · simp only [if_neg hij, abs_zero]
      exact mul_nonneg (gamma_nonneg fp hval) (abs_nonneg _)
  · intro p
    -- only the diagonal `q = p` term survives
    rw [Finset.sum_eq_single p]
    · simpa using hΔdiag_eq p
    · intro q _ hqp
      have hDpq : D p q = 0 := hDoff p q (fun h => hqp h.symm)
      simp only [hDpq, if_neg (show ¬ (p = q) from fun h => hqp h.symm), add_zero, zero_mul]
    · intro hp; exact absurd (Finset.mem_univ p) hp

/-! ## Part 2a — block-diagonal middle-solve assembly

The mixed-pivot middle factor is represented recursively: a leading 1×1 or 2×2
block, zeros across the block split, and a trailing block-diagonal tail.  The
following two assembly lemmas turn local block residuals plus a tail residual
into the full block-diagonal residual with the same componentwise budget. -/

noncomputable def middleBlockDiagConsOne {n : ℕ} (e : ℝ) (Dtail : Fin n → Fin n → ℝ) :
    Fin (n + 1) → Fin (n + 1) → ℝ :=
  fun I J =>
    Fin.cases (Fin.cases e (fun _ => 0) J)
      (fun i => Fin.cases 0 (fun j => Dtail i j) J) I

noncomputable def middleVecConsOne {n : ℕ} (x0 : ℝ) (xtail : Fin n → ℝ) :
    Fin (n + 1) → ℝ :=
  fun I => Fin.cases x0 (fun i => xtail i) I

@[simp] theorem middleBlockDiagConsOne_00 {n : ℕ} (e : ℝ)
    (Dtail : Fin n → Fin n → ℝ) :
    middleBlockDiagConsOne e Dtail 0 0 = e := by
  simp [middleBlockDiagConsOne]

@[simp] theorem middleBlockDiagConsOne_0s {n : ℕ} (e : ℝ)
    (Dtail : Fin n → Fin n → ℝ) (j : Fin n) :
    middleBlockDiagConsOne e Dtail 0 j.succ = 0 := by
  simp [middleBlockDiagConsOne]

@[simp] theorem middleBlockDiagConsOne_s0 {n : ℕ} (e : ℝ)
    (Dtail : Fin n → Fin n → ℝ) (i : Fin n) :
    middleBlockDiagConsOne e Dtail i.succ 0 = 0 := by
  simp [middleBlockDiagConsOne]

@[simp] theorem middleBlockDiagConsOne_ss {n : ℕ} (e : ℝ)
    (Dtail : Fin n → Fin n → ℝ) (i j : Fin n) :
    middleBlockDiagConsOne e Dtail i.succ j.succ = Dtail i j := by
  simp [middleBlockDiagConsOne]

/-- Assemble a leading scalar middle solve with a trailing block-diagonal solve. -/
theorem middleBlockDiagConsOne_solve_assemble {n : ℕ}
    (gammaMid e z0 : ℝ) (Dtail : Fin n → Fin n → ℝ) (ztail : Fin n → ℝ)
    (w0 Δe : ℝ) (wTail : Fin n → ℝ) (ΔTail : Fin n → Fin n → ℝ)
    (hheadBound : |Δe| ≤ gammaMid * |e|)
    (hheadEq : (e + Δe) * w0 = z0)
    (htailBound : ∀ i j : Fin n, |ΔTail i j| ≤ gammaMid * |Dtail i j|)
    (htailEq : ∀ i : Fin n, ∑ j : Fin n, (Dtail i j + ΔTail i j) * wTail j = ztail i) :
    ∃ (w : Fin (n + 1) → ℝ) (ΔD : Fin (n + 1) → Fin (n + 1) → ℝ),
      (∀ i j : Fin (n + 1), |ΔD i j| ≤ gammaMid * |middleBlockDiagConsOne e Dtail i j|) ∧
      (∀ p : Fin (n + 1),
        ∑ q : Fin (n + 1), (middleBlockDiagConsOne e Dtail p q + ΔD p q) * w q
          = middleVecConsOne z0 ztail p) := by
  refine ⟨middleVecConsOne w0 wTail, middleBlockDiagConsOne Δe ΔTail, ?_, ?_⟩
  · intro i j
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero => simpa [middleBlockDiagConsOne] using hheadBound
        | succ j => simp [middleBlockDiagConsOne]
    | succ i =>
        cases j using Fin.cases with
        | zero => simp [middleBlockDiagConsOne]
        | succ j => simpa [middleBlockDiagConsOne] using htailBound i j
  · intro p
    cases p using Fin.cases with
    | zero =>
        rw [Fin.sum_univ_succ]
        simp [middleBlockDiagConsOne, middleVecConsOne, hheadEq]
    | succ i =>
        rw [Fin.sum_univ_succ]
        simp [middleBlockDiagConsOne, middleVecConsOne, htailEq i]

noncomputable def middleBlockDiagConsTwo {n : ℕ} (E : Fin 2 → Fin 2 → ℝ)
    (Dtail : Fin n → Fin n → ℝ) : Fin (n + 2) → Fin (n + 2) → ℝ :=
  fun I J =>
    Fin.cases
      (Fin.cases (E 0 0) (fun l => Fin.cases (E 0 1) (fun _ => 0) l) J)
      (fun k => Fin.cases
        (Fin.cases (E 1 0) (fun l => Fin.cases (E 1 1) (fun _ => 0) l) J)
        (fun i => Fin.cases 0 (fun l => Fin.cases 0 (fun j => Dtail i j) l) J)
        k) I

noncomputable def middleVecConsTwo {n : ℕ} (xHead : Fin 2 → ℝ) (xtail : Fin n → ℝ) :
    Fin (n + 2) → ℝ :=
  fun I => Fin.cases (xHead 0) (fun k => Fin.cases (xHead 1) (fun i => xtail i) k) I

@[simp] theorem middleBlockDiagConsTwo_00 {n : ℕ} (E : Fin 2 → Fin 2 → ℝ)
    (Dtail : Fin n → Fin n → ℝ) :
    middleBlockDiagConsTwo E Dtail 0 0 = E 0 0 := by
  simp only [middleBlockDiagConsTwo, Fin.cases_zero]

@[simp] theorem middleBlockDiagConsTwo_01 {n : ℕ} (E : Fin 2 → Fin 2 → ℝ)
    (Dtail : Fin n → Fin n → ℝ) :
    middleBlockDiagConsTwo E Dtail 0 (Fin.succ 0) = E 0 1 := by
  simp only [middleBlockDiagConsTwo, Fin.cases_zero, Fin.cases_succ]

@[simp] theorem middleBlockDiagConsTwo_0t {n : ℕ} (E : Fin 2 → Fin 2 → ℝ)
    (Dtail : Fin n → Fin n → ℝ) (j : Fin n) :
    middleBlockDiagConsTwo E Dtail 0 j.succ.succ = 0 := by
  simp only [middleBlockDiagConsTwo, Fin.cases_zero, Fin.cases_succ]

@[simp] theorem middleBlockDiagConsTwo_10 {n : ℕ} (E : Fin 2 → Fin 2 → ℝ)
    (Dtail : Fin n → Fin n → ℝ) :
    middleBlockDiagConsTwo E Dtail (Fin.succ 0) 0 = E 1 0 := by
  simp only [middleBlockDiagConsTwo, Fin.cases_zero, Fin.cases_succ]

@[simp] theorem middleBlockDiagConsTwo_11 {n : ℕ} (E : Fin 2 → Fin 2 → ℝ)
    (Dtail : Fin n → Fin n → ℝ) :
    middleBlockDiagConsTwo E Dtail (Fin.succ 0) (Fin.succ 0) = E 1 1 := by
  simp only [middleBlockDiagConsTwo, Fin.cases_zero, Fin.cases_succ]

@[simp] theorem middleBlockDiagConsTwo_1t {n : ℕ} (E : Fin 2 → Fin 2 → ℝ)
    (Dtail : Fin n → Fin n → ℝ) (j : Fin n) :
    middleBlockDiagConsTwo E Dtail (Fin.succ 0) j.succ.succ = 0 := by
  simp only [middleBlockDiagConsTwo, Fin.cases_zero, Fin.cases_succ]

@[simp] theorem middleBlockDiagConsTwo_t0 {n : ℕ} (E : Fin 2 → Fin 2 → ℝ)
    (Dtail : Fin n → Fin n → ℝ) (i : Fin n) :
    middleBlockDiagConsTwo E Dtail i.succ.succ 0 = 0 := by
  simp only [middleBlockDiagConsTwo, Fin.cases_zero, Fin.cases_succ]

@[simp] theorem middleBlockDiagConsTwo_t1 {n : ℕ} (E : Fin 2 → Fin 2 → ℝ)
    (Dtail : Fin n → Fin n → ℝ) (i : Fin n) :
    middleBlockDiagConsTwo E Dtail i.succ.succ (Fin.succ 0) = 0 := by
  simp only [middleBlockDiagConsTwo, Fin.cases_zero, Fin.cases_succ]

@[simp] theorem middleBlockDiagConsTwo_tt {n : ℕ} (E : Fin 2 → Fin 2 → ℝ)
    (Dtail : Fin n → Fin n → ℝ) (i j : Fin n) :
    middleBlockDiagConsTwo E Dtail i.succ.succ j.succ.succ = Dtail i j := by
  simp only [middleBlockDiagConsTwo, Fin.cases_succ]

/-- Assemble a leading 2×2 middle solve with a trailing block-diagonal solve. -/
theorem middleBlockDiagConsTwo_solve_assemble {n : ℕ}
    (gammaMid : ℝ) (E : Fin 2 → Fin 2 → ℝ) (Dtail : Fin n → Fin n → ℝ)
    (zHead : Fin 2 → ℝ) (ztail : Fin n → ℝ)
    (wHead : Fin 2 → ℝ) (ΔE : Fin 2 → Fin 2 → ℝ)
    (wTail : Fin n → ℝ) (ΔTail : Fin n → Fin n → ℝ)
    (hheadBound : ∀ p q : Fin 2, |ΔE p q| ≤ gammaMid * |E p q|)
    (hheadEq : ∀ p : Fin 2, ∑ q : Fin 2, (E p q + ΔE p q) * wHead q = zHead p)
    (htailBound : ∀ i j : Fin n, |ΔTail i j| ≤ gammaMid * |Dtail i j|)
    (htailEq : ∀ i : Fin n, ∑ j : Fin n, (Dtail i j + ΔTail i j) * wTail j = ztail i) :
    ∃ (w : Fin (n + 2) → ℝ) (ΔD : Fin (n + 2) → Fin (n + 2) → ℝ),
      (∀ i j : Fin (n + 2), |ΔD i j| ≤ gammaMid * |middleBlockDiagConsTwo E Dtail i j|) ∧
      (∀ p : Fin (n + 2),
        ∑ q : Fin (n + 2), (middleBlockDiagConsTwo E Dtail p q + ΔD p q) * w q
          = middleVecConsTwo zHead ztail p) := by
  refine ⟨middleVecConsTwo wHead wTail, middleBlockDiagConsTwo ΔE ΔTail, ?_, ?_⟩
  · intro i j
    refine Fin.cases ?_ (fun iTail => ?_) i
    · refine Fin.cases ?_ (fun jTail => ?_) j
      · simpa [middleBlockDiagConsTwo] using hheadBound 0 0
      · refine Fin.cases ?_ (fun _ => ?_) jTail
        · simpa [middleBlockDiagConsTwo] using hheadBound 0 1
        · change |(0 : ℝ)| ≤ gammaMid * |(0 : ℝ)|
          simp
    · refine Fin.cases ?_ (fun iTail2 => ?_) iTail
      · refine Fin.cases ?_ (fun jTail => ?_) j
        · simpa [middleBlockDiagConsTwo] using hheadBound 1 0
        · refine Fin.cases ?_ (fun _ => ?_) jTail
          · simpa [middleBlockDiagConsTwo] using hheadBound 1 1
          · change |(0 : ℝ)| ≤ gammaMid * |(0 : ℝ)|
            simp
      · refine Fin.cases ?_ (fun jTail => ?_) j
        · change |(0 : ℝ)| ≤ gammaMid * |(0 : ℝ)|
          simp
        · refine Fin.cases ?_ (fun jTail2 => ?_) jTail
          · change |(0 : ℝ)| ≤ gammaMid * |(0 : ℝ)|
            simp
          · simpa [middleBlockDiagConsTwo] using htailBound iTail2 jTail2
  · intro p
    refine Fin.cases ?_ (fun pTail => ?_) p
    · rw [sum_fin_add_two]
      have h0 := hheadEq 0
      rw [Fin.sum_univ_two] at h0
      simpa [middleBlockDiagConsTwo, middleVecConsTwo] using h0
    · refine Fin.cases ?_ (fun i => ?_) pTail
      · rw [sum_fin_add_two]
        have h1 := hheadEq 1
        rw [Fin.sum_univ_two] at h1
        simp only [middleBlockDiagConsTwo, middleVecConsTwo, Fin.cases_zero, Fin.cases_succ,
          zero_mul, Finset.sum_const_zero, add_zero]
        exact h1
      · rw [sum_fin_add_two]
        simp only [middleBlockDiagConsTwo, middleVecConsTwo, Fin.cases_zero, Fin.cases_succ,
          zero_mul, zero_add, add_zero]
        exact htailEq i

/-! ## Part 2b — schedule-level middle-solve assembly

The previous lemmas assemble one head block and one solved tail.  The following
recursive predicate records exactly the local block middle-solve data needed
along a pivot schedule, and the theorem folds those local data into one global
middle-solve residual for the recursively assembled middle factor. -/

noncomputable def mixedMiddleDFromSchedule (fp : FPModel) :
    {n : ℕ} → PivotSchedule n → (Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ
  | 0, .nil, _ => fun I _ => Fin.elim0 I
  | _ + 1, .consOne s, A =>
      middleBlockDiagConsOne (A 0 0) (mixedMiddleDFromSchedule fp s (flSchurCompl _ fp A))
  | _ + 2, .consTwo s, A =>
      middleBlockDiagConsTwo (leadingTwoBlock _ A)
        (mixedMiddleDFromSchedule fp s (flSchurCompl2 _ fp A))

noncomputable def MixedMiddleSolveBlocks (fp : FPModel) (gammaMid : ℝ) :
    {n : ℕ} → PivotSchedule n → (Fin n → Fin n → ℝ) → (Fin n → ℝ) → Prop
  | 0, .nil, _, _ => True
  | _ + 1, .consOne s, A, z =>
      (∃ w0 Δe : ℝ,
        |Δe| ≤ gammaMid * |A 0 0| ∧ (A 0 0 + Δe) * w0 = z 0) ∧
      MixedMiddleSolveBlocks fp gammaMid s (flSchurCompl _ fp A) (fun i => z i.succ)
  | m + 2, .consTwo s, A, z =>
      (∃ (wHead : Fin 2 → ℝ) (ΔE : Fin 2 → Fin 2 → ℝ),
        (∀ p q : Fin 2, |ΔE p q| ≤ gammaMid * |leadingTwoBlock m A p q|) ∧
        (∀ p : Fin 2,
          ∑ q : Fin 2, (leadingTwoBlock m A p q + ΔE p q) * wHead q = z (embedTwo m p))) ∧
      MixedMiddleSolveBlocks fp gammaMid s (flSchurCompl2 m fp A) (fun i => z i.succ.succ)

/-- Fold schedule-local middle-solve residuals into one global block-diagonal
    residual for the constructor-based mixed middle factor. -/
theorem mixedMiddleDFromSchedule_solve_of_blocks (fp : FPModel) (gammaMid : ℝ) :
    {n : ℕ} → (s : PivotSchedule n) → (A : Fin n → Fin n → ℝ) → (z : Fin n → ℝ) →
      MixedMiddleSolveBlocks fp gammaMid s A z →
      ∃ (w : Fin n → ℝ) (ΔD : Fin n → Fin n → ℝ),
        (∀ i j : Fin n, |ΔD i j| ≤ gammaMid * |mixedMiddleDFromSchedule fp s A i j|) ∧
        (∀ p : Fin n, ∑ q : Fin n, (mixedMiddleDFromSchedule fp s A p q + ΔD p q) * w q = z p)
  | 0, .nil, A, z, h => by
      refine ⟨(fun I => Fin.elim0 I), (fun I _ => Fin.elim0 I), ?_, ?_⟩
      · intro i; exact Fin.elim0 i
      · intro p; exact Fin.elim0 p
  | _ + 1, .consOne s, A, z, h => by
      rcases h with ⟨hhead, htailBlocks⟩
      rcases hhead with ⟨w0, Δe, hΔe, hheadEq⟩
      obtain ⟨wTail, ΔTail, hTailBound, hTailEq⟩ :=
        mixedMiddleDFromSchedule_solve_of_blocks fp gammaMid s (flSchurCompl _ fp A)
          (fun i => z i.succ) htailBlocks
      obtain ⟨w, ΔD, hBound, hEq⟩ :=
        middleBlockDiagConsOne_solve_assemble gammaMid (A 0 0) (z 0)
          (mixedMiddleDFromSchedule fp s (flSchurCompl _ fp A)) (fun i => z i.succ)
          w0 Δe wTail ΔTail hΔe hheadEq hTailBound hTailEq
      refine ⟨w, ΔD, ?_, ?_⟩
      · simpa [mixedMiddleDFromSchedule] using hBound
      · intro p
        have hp := hEq p
        cases p using Fin.cases with
        | zero => simpa [mixedMiddleDFromSchedule, middleVecConsOne] using hp
        | succ i => simpa [mixedMiddleDFromSchedule, middleVecConsOne] using hp
  | m + 2, .consTwo s, A, z, h => by
      rcases h with ⟨hhead, htailBlocks⟩
      rcases hhead with ⟨wHead, ΔE, hΔE, hheadEq⟩
      obtain ⟨wTail, ΔTail, hTailBound, hTailEq⟩ :=
        mixedMiddleDFromSchedule_solve_of_blocks fp gammaMid s (flSchurCompl2 m fp A)
          (fun i => z i.succ.succ) htailBlocks
      obtain ⟨w, ΔD, hBound, hEq⟩ :=
        middleBlockDiagConsTwo_solve_assemble gammaMid (leadingTwoBlock m A)
          (mixedMiddleDFromSchedule fp s (flSchurCompl2 m fp A))
          (fun p => z (embedTwo m p)) (fun i => z i.succ.succ)
          wHead ΔE wTail ΔTail hΔE hheadEq hTailBound hTailEq
      refine ⟨w, ΔD, ?_, ?_⟩
      · simpa [mixedMiddleDFromSchedule] using hBound
      · intro p
        have hp := hEq p
        cases p using Fin.cases with
        | zero => simpa [mixedMiddleDFromSchedule, middleVecConsTwo] using hp
        | succ pTail =>
            cases pTail using Fin.cases with
            | zero => simpa [mixedMiddleDFromSchedule, middleVecConsTwo] using hp
            | succ i => simpa [mixedMiddleDFromSchedule, middleVecConsTwo] using hp

/-- The constructor-based mixed middle factor is the named `flMixedD` factor
    used by the mixed-pivot block-LDLᵀ development. -/
theorem mixedMiddleDFromSchedule_eq_flMixedD (fp : FPModel) :
    {n : ℕ} → (s : PivotSchedule n) → (A : Fin n → Fin n → ℝ) →
      mixedMiddleDFromSchedule fp s A = flMixedD fp s A
  | 0, .nil, _ => by
      funext i _
      exact Fin.elim0 i
  | _ + 1, .consOne s, A => by
      have htail := mixedMiddleDFromSchedule_eq_flMixedD fp s (flSchurCompl _ fp A)
      funext i j
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero => simp [mixedMiddleDFromSchedule]
          | succ j => simp [mixedMiddleDFromSchedule]
      | succ i =>
          cases j using Fin.cases with
          | zero => simp [mixedMiddleDFromSchedule]
          | succ j => simp [mixedMiddleDFromSchedule, htail]
  | m + 2, .consTwo s, A => by
      have htail := mixedMiddleDFromSchedule_eq_flMixedD fp s (flSchurCompl2 m fp A)
      funext i j
      refine Fin.cases ?_ (fun iTail => ?_) i
      · refine Fin.cases ?_ (fun jTail => ?_) j
        · simp [mixedMiddleDFromSchedule]
        · refine Fin.cases ?_ (fun _ => ?_) jTail
          · simp only [mixedMiddleDFromSchedule, middleBlockDiagConsTwo_01,
              leadingTwoBlock_apply, embedTwo_zero, embedTwo_one_eq, flMixedD_consTwo_01]
          · simp [mixedMiddleDFromSchedule]
      · refine Fin.cases ?_ (fun iTail2 => ?_) iTail
        · refine Fin.cases ?_ (fun jTail => ?_) j
          · simp only [mixedMiddleDFromSchedule, middleBlockDiagConsTwo_10,
              leadingTwoBlock_apply, embedTwo_zero, embedTwo_one_eq, flMixedD_consTwo_10]
          · refine Fin.cases ?_ (fun jTail2 => ?_) jTail
            · simp only [mixedMiddleDFromSchedule, middleBlockDiagConsTwo_11,
                leadingTwoBlock_apply, embedTwo_one_eq, flMixedD_consTwo_11]
            · change middleBlockDiagConsTwo (leadingTwoBlock m A)
                  (mixedMiddleDFromSchedule fp s (flSchurCompl2 m fp A)) (Fin.succ 0)
                  jTail2.succ.succ =
                flMixedD fp (s.consTwo) A (Fin.succ 0) jTail2.succ.succ
              simp only [middleBlockDiagConsTwo_1t, flMixedD_consTwo_1t]
        · refine Fin.cases ?_ (fun jTail => ?_) j
          · simp [mixedMiddleDFromSchedule]
          · refine Fin.cases ?_ (fun jTail2 => ?_) jTail
            · simp only [mixedMiddleDFromSchedule, middleBlockDiagConsTwo_t1,
                flMixedD_consTwo_t1]
            · simp [mixedMiddleDFromSchedule, htail]

/-- Schedule-local middle-solve residuals folded directly for the named
    mixed-pivot middle factor `flMixedD`. -/
theorem flMixedD_solve_of_blocks (fp : FPModel) (gammaMid : ℝ)
    {n : ℕ} (s : PivotSchedule n) (A : Fin n → Fin n → ℝ) (z : Fin n → ℝ)
    (hblocks : MixedMiddleSolveBlocks fp gammaMid s A z) :
    ∃ (w : Fin n → ℝ) (ΔD : Fin n → Fin n → ℝ),
      (∀ i j : Fin n, |ΔD i j| ≤ gammaMid * |flMixedD fp s A i j|) ∧
      (∀ p : Fin n, ∑ q : Fin n, (flMixedD fp s A p q + ΔD p q) * w q = z p) := by
  obtain ⟨w, ΔD, hBound, hEq⟩ :=
    mixedMiddleDFromSchedule_solve_of_blocks fp gammaMid s A z hblocks
  have hD := mixedMiddleDFromSchedule_eq_flMixedD fp s A
  refine ⟨w, ΔD, ?_, ?_⟩
  · intro i j
    simpa [hD] using hBound i j
  · intro p
    simpa [hD] using hEq p

/-! ## Part 2c — the solve-chain envelope is a scalar multiple of `|L̂||D̂||L̂ᵀ|`

The derived Aasen collapsed budget for the middle factor `D̂` with symmetric
outer factor (`U = L̂ᵀ`) and middle budget `γ_mid |D̂|` factors exactly as a
dimension-independent coefficient times the `|L̂||D̂||L̂ᵀ|` product entry
`higham11_4_bunchKaufmanProductEntry`.  This exhibits the solve-side backward
error in Higham's normwise `c·u·‖A‖_M` shape. -/

theorem aasenChainDeltaABound_eq_coeff_mul_productEntry (n : ℕ) (γ γmid : ℝ)
    (L D : Fin n → Fin n → ℝ) (i j : Fin n) :
    higham11_15_aasenChainDeltaABound n γ (fun p q => γmid * |D p q|) L D
        (fun r c => L c r) i j
      = ((2 * γ + γ ^ 2) + (1 + 2 * γ + γ ^ 2) * γmid)
          * higham11_4_bunchKaufmanProductEntry n L D i j := by
  unfold higham11_15_aasenChainDeltaABound higham11_4_bunchKaufmanProductEntry
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  dsimp only
  ring

/-! ## Part 3 — the solve-side backward error of the block-LDLᵀ solve

`higham11_3_block_ldlt_solve_backward_error`.  The full Theorem 11.3 statement,
factorization *and* solve halves, with the solve residual `(A + ΔA₂) x̂ = b`
DERIVED (not `0`/`hsolve`), for the concrete computed solution
`x̂ = fl_backSub L̂ᵀ (block-diagonal solve of ẑ = fl_forwardSub L̂ b)`.

The single explicit hypothesis `hmid`/`hΔD` is the (11.5) block-diagonal middle
solve `(D̂ + ΔD) ŵ = ẑ` with `|ΔD| ≤ γ_mid |D̂|`. -/

/-- **Theorem 11.3 (block-LDLᵀ), solve half derived.**

    For the rounded mixed-pivot block-LDLᵀ path of `A` recorded by the schedule
    `s` (per-stage `FlMixedPivots` conditions `hp`), let `L̂ = flMixedL fp s A`,
    `D̂ = flMixedD fp s A`, and let the linear system `L̂ D̂ L̂ᵀ x̂ = b` be solved
    by forward substitution `ẑ = fl_forwardSub L̂ b`, a block-diagonal solve
    `ŵ` of `D̂ ŵ = ẑ` (satisfying the (11.5) backward error `hΔD`/`hmid`), and
    back substitution `x̂ = fl_backSub L̂ᵀ ŵ`.  Then

      `L̂ D̂ L̂ᵀ = A + ΔA₁`,   `(A + ΔA₂) x̂ = b`,

    with `|ΔA₁| ≤ p(n) u (|A| + |L̂||D̂||L̂ᵀ|)` (the printed factorization
    envelope) and `|ΔA₂| ≤ (that envelope) + (solve-chain envelope)`, where the
    solve-chain envelope is the derived Aasen collapsed budget
    `higham11_15_aasenChainDeltaABound` with outer relative error `γ_n` and
    middle budget `γ_mid |D̂|`. -/
theorem higham11_3_block_ldlt_solve_backward_error
    (fp : FPModel) (hval : gammaValid fp 3)
    {n : ℕ} (s : PivotSchedule n) (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hvaln : gammaValid fp n)
    (cSolve cStage gammaMid : ℝ)
    (hcS0 : 0 ≤ cSolve) (hcS40 : cSolve ≤ 40)
    (hcSt0 : 0 ≤ cStage) (hcSt5 : cStage ≤ 5)
    (hgammaMid : 0 ≤ gammaMid)
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 100)
    (hp : FlMixedPivots fp cSolve cStage s A)
    (w_hat : Fin n → ℝ) (ΔD : Fin n → Fin n → ℝ)
    (hΔD : ∀ i j : Fin n, |ΔD i j| ≤ gammaMid * |flMixedD fp s A i j|)
    (hmid : ∀ p : Fin n,
      ∑ q : Fin n, (flMixedD fp s A p q + ΔD p q) * w_hat q
        = fl_forwardSub fp n (flMixedL fp s A) b p) :
    ∃ ΔA1 ΔA2 : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |ΔA1 i j|
          ≤ higham11_3_printedFirstOrderBound n A (flMixedL fp s A) (flMixedD fp s A)
              id (pPoly n) fp.u i j) ∧
      (∀ i j : Fin n, |ΔA2 i j|
          ≤ higham11_3_printedFirstOrderBound n A (flMixedL fp s A) (flMixedD fp s A)
              id (pPoly n) fp.u i j
            + higham11_15_aasenChainDeltaABound n (gamma fp n)
                (fun i j => gammaMid * |flMixedD fp s A i j|)
                (flMixedL fp s A) (flMixedD fp s A) (fun r c => flMixedL fp s A c r) i j) ∧
      (∀ i j : Fin n,
        (∑ k₁, ∑ k₂, flMixedL fp s A i k₁ * flMixedD fp s A k₁ k₂ * flMixedL fp s A j k₂)
          = A i j + ΔA1 i j) ∧
      (∀ i : Fin n,
        ∑ j : Fin n,
          (A i j + ΔA2 i j) * fl_backSub fp n (fun r c => flMixedL fp s A c r) w_hat j = b i) := by
  -- abbreviations kept definitionally transparent (`let`) so `rfl` sees through them
  let L : Fin n → Fin n → ℝ := flMixedL fp s A
  let D : Fin n → Fin n → ℝ := flMixedD fp s A
  let U : Fin n → Fin n → ℝ := fun r c => flMixedL fp s A c r
  let A_fact : Fin n → Fin n → ℝ :=
    fun i j => ∑ k₁, ∑ k₂, L i k₁ * D k₁ k₂ * L j k₂
  let BT : Fin n → Fin n → ℝ := fun i j => gammaMid * |D i j|
  let bound : Fin n → Fin n → ℝ := higham11_15_aasenChainDeltaABound n (gamma fp n) BT L D U
  let B_factor : Fin n → Fin n → ℝ :=
    higham11_3_printedFirstOrderBound n A L D id (pPoly n) fp.u
  -- structural facts about `L̂` and `L̂ᵀ`
  have hLdiag : ∀ i : Fin n, L i i ≠ 0 := fun i => by
    show flMixedL fp s A i i ≠ 0; rw [flMixedL_diag]; exact one_ne_zero
  have hLlower : ∀ i j : Fin n, i.val < j.val → L i j = 0 := fun i j h =>
    flMixedL_lower fp s A i j h
  have hUdiag : ∀ i : Fin n, U i i ≠ 0 := fun i => by
    show flMixedL fp s A i i ≠ 0; rw [flMixedL_diag]; exact one_ne_zero
  have hUupper : ∀ i j : Fin n, j.val < i.val → U i j = 0 := fun i j h =>
    flMixedL_lower fp s A j i h
  -- OUTER solve backward errors (derived, Chapter 8)
  obtain ⟨ΔL, hΔL, hforward⟩ := forwardSub_backward_error fp n L b hLdiag hLlower hvaln
  obtain ⟨ΔU, hΔU, hback⟩ := backSub_backward_error fp n U w_hat hUdiag hUupper hvaln
  -- chain-perturbation budget (derived, generic Aasen collapse)
  have hBT : ∀ p q : Fin n, 0 ≤ BT p q := fun p q => mul_nonneg hgammaMid (abs_nonneg _)
  have hbound : ∀ i j : Fin n,
      |higham11_15_aasenChainDeltaA n L D U ΔL ΔD ΔU i j| ≤ bound i j :=
    higham11_15_aasenChainDeltaA_abs_bound_gamma n L D U ΔL ΔD ΔU BT (gamma fp n)
      (gamma_nonneg fp hvaln) hBT hΔL hΔD hΔU
  -- compose the three substep residuals into `(A_fact + ΔM) x̂ = b`
  obtain ⟨DeltaS, hDeltaS, hsource⟩ :=
    higham11_15_aasen_chain_source_backward_error_of_components
      n A_fact L D U ΔL ΔD ΔU
      b (fl_forwardSub fp n L b) w_hat (fl_backSub fp n U w_hat) bound
      (by intro i j; rfl) hforward hmid hback hbound
  -- factorization residual `|A_fact - A| ≤ B_factor` (derived, reused closures)
  have hfactorBound : ∀ i j : Fin n, |A_fact i j - A i j| ≤ B_factor i j := by
    intro i j
    exact le_trans (fl_blockLDLT_mixed_bound fp hval cSolve cStage s A hp i j)
      (flMixed_envelope_le_printed fp hval cSolve cStage hcS0 hcS40 hcSt0 hcSt5 s A hsmall hp i j)
  -- fold factorization + solve into `(A + ΔA₂) x̂ = b`
  obtain ⟨ΔA2, hΔA2, hsolveEq⟩ :=
    higham11_8_aasen_source_backward_error_of_factor_and_solve_residuals
      n A A_fact DeltaS B_factor bound b (fl_backSub fp n U w_hat)
      hfactorBound hDeltaS hsource
  refine ⟨fun i j => A_fact i j - A i j, ΔA2, ?_, ?_, ?_, ?_⟩
  · -- |ΔA₁| ≤ printed factorization envelope
    intro i j; exact hfactorBound i j
  · -- |ΔA₂| ≤ factorization envelope + solve-chain envelope
    intro i j; exact hΔA2 i j
  · -- factorization equation `L̂D̂L̂ᵀ = A + ΔA₁`
    intro i j; show A_fact i j = A i j + (A_fact i j - A i j); ring
  · -- derived solve residual `(A + ΔA₂) x̂ = b`
    exact hsolveEq

/-! ## Part 3b — diagonal middle solve specialization

When the computed middle factor is diagonal (the all-1×1 block case), the
middle solve is no longer an input: `fl_diagonal_solve_backward_error` derives
the required `(D̂ + ΔD) ŵ = ẑ` residual from the actual scalar divisions. -/

/-- **Theorem 11.3 solve half with diagonal middle solve derived.**  This
specializes `higham11_3_block_ldlt_solve_backward_error` to the all-1×1
middle case by constructing `ŵ` and `ΔD` from the scalar `fl_div` solve, so the
caller no longer supplies the middle-solve hypothesis `hmid`. -/
theorem higham11_3_block_ldlt_solve_backward_error_of_diagonal_middle
    (fp : FPModel) (hval : gammaValid fp 3)
    {n : ℕ} (s : PivotSchedule n) (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hvaln : gammaValid fp n)
    (cSolve cStage : ℝ)
    (hcS0 : 0 ≤ cSolve) (hcS40 : cSolve ≤ 40)
    (hcSt0 : 0 ≤ cStage) (hcSt5 : cStage ≤ 5)
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 100)
    (hp : FlMixedPivots fp cSolve cStage s A)
    (hDdiag : ∀ i : Fin n, flMixedD fp s A i i ≠ 0)
    (hDoff : ∀ i j : Fin n, i ≠ j → flMixedD fp s A i j = 0) :
    ∃ w_hat : Fin n → ℝ, ∃ ΔA1 ΔA2 : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |ΔA1 i j|
          ≤ higham11_3_printedFirstOrderBound n A (flMixedL fp s A) (flMixedD fp s A)
              id (pPoly n) fp.u i j) ∧
      (∀ i j : Fin n, |ΔA2 i j|
          ≤ higham11_3_printedFirstOrderBound n A (flMixedL fp s A) (flMixedD fp s A)
              id (pPoly n) fp.u i j
            + higham11_15_aasenChainDeltaABound n (gamma fp n)
                (fun i j => gamma fp 1 * |flMixedD fp s A i j|)
                (flMixedL fp s A) (flMixedD fp s A) (fun r c => flMixedL fp s A c r) i j) ∧
      (∀ i j : Fin n,
        (∑ k₁, ∑ k₂, flMixedL fp s A i k₁ * flMixedD fp s A k₁ k₂ * flMixedL fp s A j k₂)
          = A i j + ΔA1 i j) ∧
      (∀ i : Fin n,
        ∑ j : Fin n,
          (A i j + ΔA2 i j) * fl_backSub fp n (fun r c => flMixedL fp s A c r) w_hat j = b i) := by
  have hval1 : gammaValid fp 1 := gammaValid_mono fp (by norm_num) hval
  obtain ⟨w_hat, ΔD, hΔD, hmid⟩ :=
    fl_diagonal_solve_backward_error fp n (flMixedD fp s A)
      (fl_forwardSub fp n (flMixedL fp s A) b) hDdiag hDoff hval1
  obtain ⟨ΔA1, ΔA2, hΔA1, hΔA2, hfac, hsolve⟩ :=
    higham11_3_block_ldlt_solve_backward_error fp hval s A b hvaln cSolve cStage
      (gamma fp 1) hcS0 hcS40 hcSt0 hcSt5 (gamma_nonneg fp hval1)
      hsmall hp w_hat ΔD hΔD hmid
  exact ⟨w_hat, ΔA1, ΔA2, hΔA1, hΔA2, hfac, hsolve⟩

/-! ## Part 4 — normwise (Theorem 11.7) repackaging

Specializing to a factor-norm bound `|L̂||D̂||L̂ᵀ| ≤ c₀·Amax` (the tridiagonal
"constant growth" fact supplied by `TriPivotData`/`hfactor_bound` in the
Theorem 11.7 chain) and `|A| ≤ Amax`, the componentwise envelopes collapse to
the printed normwise `c·u·‖A‖_M` shape: the factorization side lands in
`p(n)(1+c₀)·u·Amax` and the solve side adds the derived
`((2γ+γ²)+(1+2γ+γ²)γ_mid)·c₀·Amax`. -/

/-- **Theorem 11.7 (Bunch tridiagonal), solve half, normwise form.**  With the
    factor-norm bound `|L̂||D̂||L̂ᵀ| ≤ c₀·Amax` and `|A| ≤ Amax`, the block-LDLᵀ
    solve produces `L̂D̂L̂ᵀ = A + ΔA₁`, `(A + ΔA₂) x̂ = b` with the normwise
    bounds

      `|ΔA₁| ≤ p(n)(1+c₀)·u·Amax`,
      `|ΔA₂| ≤ p(n)(1+c₀)·u·Amax + ((2γₙ+γₙ²)+(1+2γₙ+γₙ²)γ_mid)·c₀·Amax`,

    the derived solve constant being the strictly larger polynomial. -/
theorem higham11_7_bunch_tridiagonal_solve_backward_error_normwise
    (fp : FPModel) (hval : gammaValid fp 3)
    {n : ℕ} (s : PivotSchedule n) (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hvaln : gammaValid fp n)
    (Amax c0 cSolve cStage gammaMid : ℝ)
    (hAmax : ∀ i j : Fin n, |A i j| ≤ Amax) (hAmax0 : 0 ≤ Amax) (hc0 : 0 ≤ c0)
    (hcS0 : 0 ≤ cSolve) (hcS40 : cSolve ≤ 40)
    (hcSt0 : 0 ≤ cStage) (hcSt5 : cStage ≤ 5)
    (hgammaMid : 0 ≤ gammaMid)
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 100)
    (hp : FlMixedPivots fp cSolve cStage s A)
    (hfactorNorm : ∀ i j : Fin n,
      higham11_4_bunchKaufmanProductEntry n (flMixedL fp s A) (flMixedD fp s A) i j ≤ c0 * Amax)
    (w_hat : Fin n → ℝ) (ΔD : Fin n → Fin n → ℝ)
    (hΔD : ∀ i j : Fin n, |ΔD i j| ≤ gammaMid * |flMixedD fp s A i j|)
    (hmid : ∀ p : Fin n,
      ∑ q : Fin n, (flMixedD fp s A p q + ΔD p q) * w_hat q
        = fl_forwardSub fp n (flMixedL fp s A) b p) :
    ∃ ΔA1 ΔA2 : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |ΔA1 i j| ≤ pPoly n * fp.u * ((1 + c0) * Amax)) ∧
      (∀ i j : Fin n, |ΔA2 i j| ≤ pPoly n * fp.u * ((1 + c0) * Amax)
          + ((2 * gamma fp n + gamma fp n ^ 2)
              + (1 + 2 * gamma fp n + gamma fp n ^ 2) * gammaMid) * (c0 * Amax)) ∧
      (∀ i j : Fin n,
        (∑ k₁, ∑ k₂, flMixedL fp s A i k₁ * flMixedD fp s A k₁ k₂ * flMixedL fp s A j k₂)
          = A i j + ΔA1 i j) ∧
      (∀ i : Fin n,
        ∑ j : Fin n,
          (A i j + ΔA2 i j) * fl_backSub fp n (fun r c => flMixedL fp s A c r) w_hat j = b i) := by
  obtain ⟨ΔA1, ΔA2, hΔA1, hΔA2, hfacEq, hsolveEq⟩ :=
    higham11_3_block_ldlt_solve_backward_error fp hval s A b hvaln cSolve cStage gammaMid
      hcS0 hcS40 hcSt0 hcSt5 hgammaMid hsmall hp w_hat ΔD hΔD hmid
  have hγn : 0 ≤ gamma fp n := gamma_nonneg fp hvaln
  have hpu : 0 ≤ pPoly n * fp.u := mul_nonneg (by unfold pPoly; positivity) fp.u_nonneg
  have hcoeff : 0 ≤ (2 * gamma fp n + gamma fp n ^ 2)
      + (1 + 2 * gamma fp n + gamma fp n ^ 2) * gammaMid := by positivity
  -- relaxation of the printed factorization envelope to `p(n)(1+c₀)u·Amax`
  have hfact_relax : ∀ i j : Fin n,
      higham11_3_printedFirstOrderBound n A (flMixedL fp s A) (flMixedD fp s A)
          id (pPoly n) fp.u i j ≤ pPoly n * fp.u * ((1 + c0) * Amax) := by
    intro i j
    unfold higham11_3_printedFirstOrderBound
    refine mul_le_mul_of_nonneg_left ?_ hpu
    have hsum : |A (id i) (id j)|
          + higham11_4_bunchKaufmanProductEntry n (flMixedL fp s A) (flMixedD fp s A) i j
        ≤ Amax + c0 * Amax := add_le_add (hAmax i j) (hfactorNorm i j)
    calc |A (id i) (id j)|
            + higham11_4_bunchKaufmanProductEntry n (flMixedL fp s A) (flMixedD fp s A) i j
          ≤ Amax + c0 * Amax := hsum
      _ = (1 + c0) * Amax := by ring
  -- relaxation of the derived solve-chain envelope to `coeff·c₀·Amax`
  have hsolve_relax : ∀ i j : Fin n,
      higham11_15_aasenChainDeltaABound n (gamma fp n)
          (fun i j => gammaMid * |flMixedD fp s A i j|)
          (flMixedL fp s A) (flMixedD fp s A) (fun r c => flMixedL fp s A c r) i j
        ≤ ((2 * gamma fp n + gamma fp n ^ 2)
            + (1 + 2 * gamma fp n + gamma fp n ^ 2) * gammaMid) * (c0 * Amax) := by
    intro i j
    rw [aasenChainDeltaABound_eq_coeff_mul_productEntry]
    exact mul_le_mul_of_nonneg_left (hfactorNorm i j) hcoeff
  refine ⟨ΔA1, ΔA2, ?_, ?_, hfacEq, hsolveEq⟩
  · intro i j; exact le_trans (hΔA1 i j) (hfact_relax i j)
  · intro i j
    exact le_trans (hΔA2 i j) (add_le_add (hfact_relax i j) (hsolve_relax i j))

/-- **Theorem 11.7 solve half with diagonal middle solve derived.**  This is the
normwise `higham11_7_bunch_tridiagonal_solve_backward_error_normwise` endpoint
specialized to a diagonal computed middle factor, deriving the middle solve
from scalar `fl_div` and using `γ₁` for the middle-solve budget. -/
theorem higham11_7_bunch_tridiagonal_solve_backward_error_normwise_of_diagonal_middle
    (fp : FPModel) (hval : gammaValid fp 3)
    {n : ℕ} (s : PivotSchedule n) (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hvaln : gammaValid fp n)
    (Amax c0 cSolve cStage : ℝ)
    (hAmax : ∀ i j : Fin n, |A i j| ≤ Amax) (hAmax0 : 0 ≤ Amax) (hc0 : 0 ≤ c0)
    (hcS0 : 0 ≤ cSolve) (hcS40 : cSolve ≤ 40)
    (hcSt0 : 0 ≤ cStage) (hcSt5 : cStage ≤ 5)
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 100)
    (hp : FlMixedPivots fp cSolve cStage s A)
    (hfactorNorm : ∀ i j : Fin n,
      higham11_4_bunchKaufmanProductEntry n (flMixedL fp s A) (flMixedD fp s A) i j ≤ c0 * Amax)
    (hDdiag : ∀ i : Fin n, flMixedD fp s A i i ≠ 0)
    (hDoff : ∀ i j : Fin n, i ≠ j → flMixedD fp s A i j = 0) :
    ∃ w_hat : Fin n → ℝ, ∃ ΔA1 ΔA2 : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |ΔA1 i j| ≤ pPoly n * fp.u * ((1 + c0) * Amax)) ∧
      (∀ i j : Fin n, |ΔA2 i j| ≤ pPoly n * fp.u * ((1 + c0) * Amax)
          + ((2 * gamma fp n + gamma fp n ^ 2)
              + (1 + 2 * gamma fp n + gamma fp n ^ 2) * gamma fp 1) * (c0 * Amax)) ∧
      (∀ i j : Fin n,
        (∑ k₁, ∑ k₂, flMixedL fp s A i k₁ * flMixedD fp s A k₁ k₂ * flMixedL fp s A j k₂)
          = A i j + ΔA1 i j) ∧
      (∀ i : Fin n,
        ∑ j : Fin n,
          (A i j + ΔA2 i j) * fl_backSub fp n (fun r c => flMixedL fp s A c r) w_hat j = b i) := by
  have hval1 : gammaValid fp 1 := gammaValid_mono fp (by norm_num) hval
  obtain ⟨w_hat, ΔD, hΔD, hmid⟩ :=
    fl_diagonal_solve_backward_error fp n (flMixedD fp s A)
      (fl_forwardSub fp n (flMixedL fp s A) b) hDdiag hDoff hval1
  obtain ⟨ΔA1, ΔA2, hΔA1, hΔA2, hfac, hsolve⟩ :=
    higham11_7_bunch_tridiagonal_solve_backward_error_normwise fp hval s A b hvaln
      Amax c0 cSolve cStage (gamma fp 1) hAmax hAmax0 hc0 hcS0 hcS40
      hcSt0 hcSt5 (gamma_nonneg fp hval1) hsmall hp hfactorNorm w_hat ΔD hΔD hmid
  exact ⟨w_hat, ΔA1, ΔA2, hΔA1, hΔA2, hfac, hsolve⟩

/-! ## Precise honesty status

**Fully derived here:**
  * `flMixedL_diag`, `flMixedL_lower` — `L̂` is unit lower triangular (structural
    induction on the schedule, via the existing `flMixedL_*` simp lemmas).
  * `fl_diagonal_solve_backward_error` — the diagonal (all-1×1) middle solve,
    derived per block from `fl_oneByOne_solve_backward_error`.  This is the model
    of the middle-solve hypothesis and shows the 1×1 blocks need no assumption.
  * The two OUTER triangular-solve backward errors, from the actual
    `fl_forwardSub`/`fl_backSub` runs (`forwardSub_backward_error`,
    `backSub_backward_error`, reused).
  * The collapse of the three substep residuals into `(L̂D̂L̂ᵀ + ΔM) x̂ = b` and
    the componentwise chain budget for `ΔM`
    (`higham11_15_aasen_chain_source_backward_error_of_components`,
    `higham11_15_aasenChainDeltaA_abs_bound_gamma`, generic in the middle factor).
  * The fold against the derived factorization residual `L̂D̂L̂ᵀ = A + ΔA₁`
    (`fl_blockLDLT_mixed_bound`, `flMixed_envelope_le_printed`) into
    `(A + ΔA₂) x̂ = b` with `ΔA₂ = ΔA₁ + ΔM`
    (`higham11_8_aasen_source_backward_error_of_factor_and_solve_residuals`),
    and the honest componentwise bound `|ΔA₂| ≤ B_factor + B_solve`.

**Assumed (the sanctioned Higham (11.5) source hypothesis):** the MIDDLE
block-diagonal solve `hmid`/`hΔD`: `(D̂ + ΔD) ŵ = ẑ` with `|ΔD| ≤ γ_mid |D̂|`.
This is (11.5) for the block-diagonal `D̂` (1×1 blocks derivable as in
`fl_diagonal_solve_backward_error`; 2×2 blocks the explicitly permitted (11.5)
assumption).  Its recursive composition over the pivot schedule is a
self-contained further development, isolated here as the single hypothesis.

**Strength.**  The solve residual `(A + ΔA₂) x̂ = b` is now derived for the
concrete computed solution `x̂` — no longer a supplied `hsolve`/`ΔA₂ = 0`.  The
bound is the honest sum of the printed factorization envelope and the derived
solve-chain envelope, matching Higham's `p(n) u (|A| + |L̂||D̂||L̂ᵀ|)` shape
(the solve constant being the strictly larger polynomial, as in Higham). -/

end LeanFpAnalysis.FP.Ch11Closure.Solve
