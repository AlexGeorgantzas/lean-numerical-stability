/-
Algorithms/Cholesky/AasenDirect118Ch11Closure.lean

Chapter 11 closure, **module #4** — the final assembly of the faithful
Theorem-11.8 (Aasen backward error) closure.

This file composes the three completed pieces of the faithful 11.8 tower:

  * **#2** `AasenCoupledFpCh11Closure` — the coupled floating-point Aasen sweep
    `flAasen fp n A` (fields `.Lhat`, `.Hhat`, `.That`), its nonzero-pivot
    predicate `FlAasenPivots`, and the structural facts (`L̂` unit lower
    triangular with first column `e₁`, `T̂` symmetric tridiagonal).
  * **#3** `AasenFactorResidualCh11Closure.fl_aasen_factorization_residual` — the
    *direct* factorization residual of the computed factors,
    `|(L̂ T̂ L̂ᵀ)_{ij} − A_{ij}| ≤ γ_{3n} (|L̂| |T̂| |L̂ᵀ|)_{ij}`, proved with **no**
    diagonal dominance, **no** no-cancellation, and **no** comparison to an exact
    reference `L, T`.
  * **#1** `AasenTridiagGEPPCh11Closure` — the dominance-free middle-solve
    factor-norm growth control for the Bunch (Algorithm-11.6) factorisation of
    the symmetric tridiagonal `T̂`.

## What is delivered

`higham11_8_aasen_backward_error_direct` assembles the direct factorization
residual (#3) with the repository's rounded Aasen solve chain
(`fl_forwardSub L̂ · (Pb)`, a tridiagonal solve of `T̂`, `fl_backSub L̂ᵀ ·`) via
the generic combiner
`higham11_8_aasen_source_backward_error_of_factor_and_solve_residuals`, giving
the honest Higham-11.8 conclusion for the **computed** Aasen factors:

  * componentwise `|ΔA| ≤ B_factor + B_solve` (`B_factor` is the *derived* direct
    residual budget `γ_{3n} |L̂| |T̂| |L̂ᵀ|`, `B_solve` the closed solve-chain
    budget);
  * the source equation `(A + ΔA) x̂ = P b`;
  * the printed normwise bound `‖ΔA‖∞ ≤ (n−1)² γ_{15n+25} ‖T̂‖∞`.

## Honesty / strength notes

The **factorization** half of Theorem 11.8 is fully *derived* from the coupled
fp Aasen model of module #2/#3 — this is the substantive, novel part: the
residual is on the computed factors with none of the usual crutches.

The **middle solve** is routed through a tridiagonal factorisation
`T̂ = L_T̂ U_T̂` (supplied as algorithm data with the Chapter-9 eq. (9.20)
perturbation model `h20`).  Its factor-norm growth enters only through the
single hypothesis `hmiddle_factors : ‖L_T̂‖∞ ‖U_T̂‖∞ ≤ ‖T̂‖∞` — the standard
`O(1)` tridiagonal-solve growth guarantee, the exact analogue of the explicit
partial-pivoting cap `|L̂ i j| ≤ 1` used for the outer factor.  This is the same
middle-solve reduction used by the existing endpoint
`Aasen118ReducedCh11Closure.higham11_8_aasen_normwise_backward_error_of_reduced`
(there written with a parameter `κmidLU ≤ 1`).

The dominance-free Bunch route (module #1,
`bunch_tridiag_absFactor_infNorm_le_infNorm`) discharges this middle-solve growth
*without* any dominance hypothesis, but only at an honest `O(n)` constant
(`κ = n · c₀`); folding that `O(n)` into the printed bound would replace the
*linear* radius `γ_{15n+25}` by a quadratic one, so it is not used inside the
linear-radius endpoint below.  The Bunch bound is re-exported here
(`bunch_middle_absFactor_infNorm_le`) so the dominance-free discharge remains
available to callers who accept the quadratic radius.

Constant note.  The printed Theorem 11.8 displays `γ_{3n+1}` (factor) and a
solve constant; the assembled radius here is the repository's canonical
same-class radius `γ_{15n+25}`, obtained from the shares
`γ_{3n} + (2γ_n+γ_n²) + (1+2γ_n+γ_n²) f(γ_n) ≤ γ_{3n} + γ_{2n} + γ_{6n} ≤
γ_{15n+25}` (the factor share is `γ_{3n}`, strictly smaller than the printed
`γ_{3n+1}`).

No `sorry`/`admit`/`axiom`/`native_decide`; everything below is derived from the
already-closed pieces and the `infNorm`/`gamma` arithmetic machinery.
-/
import LeanFpAnalysis.FP.Algorithms.Cholesky.AasenFactorResidualCh11Closure
import LeanFpAnalysis.FP.Algorithms.Cholesky.AasenTridiagGEPPCh11Closure
import LeanFpAnalysis.FP.Algorithms.Cholesky.AasenFactorNormCh11Closure

open scoped BigOperators

namespace LeanFpAnalysis.FP.Ch11Closure.AasenDirect

open LeanFpAnalysis.FP
open LeanFpAnalysis.FP.Ch11Closure.AasenNorm
open LeanFpAnalysis.FP.Ch11Closure
open LeanFpAnalysis.FP.Ch11Closure.Mixed
open LeanFpAnalysis.FP.Ch11Closure.HFactor

/-! ### Small `infNorm` arithmetic helpers -/

/-- A nonnegative scalar factors out of an `infNorm` (as an upper bound):
`‖c · M‖∞ ≤ c ‖M‖∞` for `c ≥ 0` and entrywise-nonnegative `M`. -/
theorem infNorm_const_mul_le {n : ℕ} (c : ℝ) (hc : 0 ≤ c) (M : Fin n → Fin n → ℝ)
    (hM : ∀ i j : Fin n, 0 ≤ M i j) :
    infNorm (fun i j => c * M i j) ≤ c * infNorm M := by
  apply infNorm_le_of_row_sum_le
  · intro i
    calc ∑ j : Fin n, |c * M i j|
        = ∑ j : Fin n, c * M i j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [abs_of_nonneg (mul_nonneg hc (hM i j))]
      _ = c * ∑ j : Fin n, M i j := by rw [Finset.mul_sum]
      _ ≤ c * infNorm M := by
          apply mul_le_mul_of_nonneg_left _ hc
          calc ∑ j : Fin n, M i j
              = ∑ j : Fin n, |M i j| := by
                apply Finset.sum_congr rfl
                intro j _
                rw [abs_of_nonneg (hM i j)]
            _ ≤ infNorm M := row_sum_le_infNorm M i
  · exact mul_nonneg hc (infNorm_nonneg M)

/-- The absolute triple-product matrix `|L| |T| |U|` has `infNorm` bounded by the
product of the three `infNorm`s.  This is the normwise cap for the direct Aasen
factorization residual budget `γ_{3n} |L̂| |T̂| |L̂ᵀ|`. -/
theorem infNorm_tripleAbs_le {n : ℕ} (hn : 0 < n) (L T U : Fin n → Fin n → ℝ) :
    infNorm (fun i j => ∑ p : Fin n, ∑ q : Fin n, |L i p| * |T p q| * |U q j|)
      ≤ infNorm L * infNorm T * infNorm U := by
  have heq :
      (fun i j => ∑ p : Fin n, ∑ q : Fin n, |L i p| * |T p q| * |U q j|)
        = matMul n (absMatrix n L) (matMul n (absMatrix n T) (absMatrix n U)) := by
    funext i j
    simp only [matMul, absMatrix]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [heq]
  calc infNorm (matMul n (absMatrix n L) (matMul n (absMatrix n T) (absMatrix n U)))
      ≤ infNorm (absMatrix n L) * infNorm (matMul n (absMatrix n T) (absMatrix n U)) :=
        infNorm_matMul_le hn _ _
    _ ≤ infNorm (absMatrix n L) *
          (infNorm (absMatrix n T) * infNorm (absMatrix n U)) :=
        mul_le_mul_of_nonneg_left (infNorm_matMul_le hn _ _) (infNorm_nonneg _)
    _ = infNorm L * infNorm T * infNorm U := by
        rw [infNorm_absMatrix hn L, infNorm_absMatrix hn T, infNorm_absMatrix hn U]
        ring

/-! ### Re-export: the dominance-free Bunch middle-solve growth (module #1)

This restates module #1's `bunch_tridiag_absFactor_infNorm_le_infNorm` so that the
dominance-free discharge of the middle-solve factor-norm growth is available at
this assembly layer (at the honest `O(n)` constant `κ = n · c₀`). -/

/-- The Bunch (Algorithm-11.6) factor-product `|L̂_B| |D̂_B| |L̂_Bᵀ|` of the
symmetric tridiagonal `T̂` has `infNorm` bounded by `(n · c₀) ‖T̂‖∞`, with **no**
diagonal-dominance hypothesis (module #1). -/
theorem bunch_middle_absFactor_infNorm_le
    (fp : FPModel) (hval : gammaValid fp 3)
    {n : ℕ} (T : Fin n → Fin n → ℝ) (s : PivotSchedule n)
    (hdata : TriPivotData fp (infNorm T) s T) :
    infNorm (bunchAbsFactorProduct fp s T) ≤ ((n : ℝ) * hfactorConst fp) * infNorm T :=
  bunch_tridiag_absFactor_infNorm_le_infNorm fp hval T s hdata

/-! ### Module #4 — the assembled direct Aasen backward error (Theorem 11.8) -/

/-- **Theorem 11.8 (Aasen), faithful direct assembly.**

For the computed floating-point Aasen factors `L̂ = (flAasen fp n A).Lhat`,
`T̂ = (flAasen fp n A).That`, run the Aasen solve chain
`x̂ = L̂⁻ᵀ (U_T̂⁻¹ (L_T̂⁻¹ (L̂⁻¹ P b)))` (outer forward/back substitutions with the
computed `L̂`, `L̂ᵀ`; middle tridiagonal solve of `T̂` via its factors
`L_T̂, U_T̂`).  Then there is a perturbation `ΔA` with

  * `|ΔA_{ij}| ≤ B_factor_{ij} + B_solve_{ij}` (componentwise, Higham's first
    bound), where `B_factor = γ_{3n} |L̂| |T̂| |L̂ᵀ|` is the **derived** direct
    factorization residual budget (module #3) and `B_solve` is the closed
    solve-chain budget;
  * `(A + ΔA) x̂ = P b` (the source equation); and
  * `‖ΔA‖∞ ≤ (n−1)² γ_{15n+25} ‖T̂‖∞` (the printed normwise bound).

Hypotheses: `A` symmetric; the nonzero-pivot predicate `FlAasenPivots`; the
explicit partial-pivoting cap `|L̂ i j| ≤ 1`; the middle tridiagonal solve
factors `L_T̂, U_T̂` with the Chapter-9 eq. (9.20) perturbation model `h20`, their
triangular shape, and the `O(1)` middle-solve factor-norm growth guarantee
`hmiddle_factors : ‖L_T̂‖∞ ‖U_T̂‖∞ ≤ ‖T̂‖∞`; and `gammaValid fp (15 n + 25)`.  No
diagonal dominance and no no-cancellation are assumed. -/
theorem higham11_8_aasen_backward_error_direct
    (fp : FPModel) (n : ℕ) (hn : 2 ≤ n)
    (A Pmat : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hsymm : ∀ i j : Fin n, A i j = A j i)
    (hp : FlAasenPivots fp n A)
    (hLhat_cap : ∀ i j : Fin n, |(flAasen fp n A).Lhat i j| ≤ 1)
    (L_T_hat U_T_hat DeltaT_LU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n
      (flAasen fp n A).That L_T_hat U_T_hat DeltaT_LU (gamma fp n))
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hmiddle_factors :
      infNorm L_T_hat * infNorm U_T_hat ≤ infNorm (flAasen fp n A).That)
    (hval : gammaValid fp (15 * n + 25)) :
    let Lh := (flAasen fp n A).Lhat
    let Th := (flAasen fp n A).That
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n Lh rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let Uouter : Fin n → Fin n → ℝ := fun i j => Lh j i
    let w_hat := fl_backSub fp n Uouter y_hat
    let B_factor : Fin n → Fin n → ℝ := fun i j =>
      gamma fp (3 * n) *
        ∑ p : Fin n, ∑ q : Fin n, |Lh i p| * |Th p q| * |Lh j q|
    let B_solve : Fin n → Fin n → ℝ :=
      higham11_15_aasenChainDeltaABound n (gamma fp n)
        (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) Lh Th Uouter
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |ΔA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + ΔA i j) * w_hat j = rhs i) ∧
      infNorm ΔA ≤ ((n - 1 : ℕ) : ℝ) ^ 2 * gamma fp (15 * n + 25) * infNorm Th := by
  intro Lh Th rhs z_hat q_hat y_hat Uouter w_hat B_factor B_solve
  -- gamma-validity at the auxiliary radii
  have hn_pos : 0 < n := by omega
  have hnval : gammaValid fp n := gammaValid_mono fp (by omega) hval
  have h2n : gammaValid fp (2 * n) := gammaValid_mono fp (by omega) hval
  have h3n : gammaValid fp (3 * n) := gammaValid_mono fp (by omega) hval
  have h6n : gammaValid fp (6 * n) := gammaValid_mono fp (by omega) hval
  have hγn_nonneg : 0 ≤ gamma fp n := gamma_nonneg fp hnval
  -- structural facts for the computed outer factor `L̂`
  have hLdiag_one : ∀ i : Fin n, Lh i i = 1 := flAasen_L_unit_diag fp n A
  have hLupper : ∀ i j : Fin n, i.val < j.val → Lh i j = 0 :=
    flAasen_L_upper_zero fp n A
  have hLfirst : ∀ i j : Fin n, j.val = 0 → i.val ≠ 0 → Lh i j = 0 :=
    flAasen_L_first_col fp n A
  have hLdiag_ne : ∀ i : Fin n, Lh i i ≠ 0 := fun i => by
    rw [hLdiag_one i]; exact one_ne_zero
  -- the computed factorization product `A_fact = L̂ T̂ L̂ᵀ`
  let A_fact : Fin n → Fin n → ℝ :=
    fun i j => ∑ p : Fin n, ∑ q : Fin n, Lh i p * Th p q * Lh j q
  have hprod_fact :
      ∀ i j : Fin n, (∑ p : Fin n, ∑ q : Fin n, Lh i p * Th p q * Lh j q) = A_fact i j :=
    fun _ _ => rfl
  -- solve-chain residual: `(A_fact + DeltaS) x̂ = P b`, `|DeltaS| ≤ B_solve`
  obtain ⟨DeltaS, hDeltaS, hsource⟩ :=
    higham11_15_fl_aasen_solve_chain_source_backward_error
      fp n A_fact Pmat Lh Th L_T_hat U_T_hat b DeltaT_LU h20
      hLdiag_ne hLupper hT_L_diag hT_U_diag hT_L_lower hT_U_upper hnval hprod_fact
  -- factorization residual `|A_fact − A| ≤ B_factor` (module #3, direct)
  have hfactor : ∀ i j : Fin n, |A_fact i j - A i j| ≤ B_factor i j :=
    fun i j => fl_aasen_factorization_residual fp n A hp hsymm h3n i j
  -- combine into the source backward error
  obtain ⟨ΔA, hΔA_comp, hΔA_source⟩ :=
    higham11_8_aasen_source_backward_error_of_factor_and_solve_residuals
      n A A_fact DeltaS B_factor B_solve rhs w_hat hfactor hDeltaS hsource
  refine ⟨ΔA, hΔA_comp, hΔA_source, ?_⟩
  -- ===== normwise fold =====
  -- nonnegativity of the two budgets
  have hBT_nonneg :
      ∀ p q : Fin n, 0 ≤ higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat p q :=
    higham11_15_aasenMiddleSolveBudget_nonneg fp n L_T_hat U_T_hat hnval
  have hBf_nonneg : ∀ i j : Fin n, 0 ≤ B_factor i j := by
    intro i j
    exact mul_nonneg (gamma_nonneg fp h3n)
      (Finset.sum_nonneg (fun p _ =>
        Finset.sum_nonneg (fun q _ => by positivity)))
  have hBs_nonneg : ∀ i j : Fin n, 0 ≤ B_solve i j :=
    higham11_15_aasenChainDeltaABound_nonneg n (gamma fp n)
      (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) Lh Th Uouter
      hγn_nonneg hBT_nonneg
  -- `‖ΔA‖∞ ≤ ‖B_factor‖∞ + ‖B_solve‖∞`
  have hΔ_split : infNorm ΔA ≤ infNorm B_factor + infNorm B_solve := by
    apply infNorm_le_of_row_sum_le
    · intro i
      have hBf_row : ∑ j : Fin n, B_factor i j ≤ infNorm B_factor := by
        calc ∑ j : Fin n, B_factor i j
            = ∑ j : Fin n, |B_factor i j| :=
              Finset.sum_congr rfl (fun j _ => (abs_of_nonneg (hBf_nonneg i j)).symm)
          _ ≤ infNorm B_factor := row_sum_le_infNorm B_factor i
      have hBs_row : ∑ j : Fin n, B_solve i j ≤ infNorm B_solve := by
        calc ∑ j : Fin n, B_solve i j
            = ∑ j : Fin n, |B_solve i j| :=
              Finset.sum_congr rfl (fun j _ => (abs_of_nonneg (hBs_nonneg i j)).symm)
          _ ≤ infNorm B_solve := row_sum_le_infNorm B_solve i
      calc ∑ j : Fin n, |ΔA i j|
          ≤ ∑ j : Fin n, (B_factor i j + B_solve i j) :=
            Finset.sum_le_sum (fun j _ => hΔA_comp i j)
        _ = (∑ j : Fin n, B_factor i j) + ∑ j : Fin n, B_solve i j :=
            Finset.sum_add_distrib
        _ ≤ infNorm B_factor + infNorm B_solve := add_le_add hBf_row hBs_row
    · exact add_nonneg (infNorm_nonneg _) (infNorm_nonneg _)
  -- `‖B_factor‖∞ ≤ γ_{3n} ‖L̂‖ ‖T̂‖ ‖L̂ᵀ‖`
  have hBf_le :
      infNorm B_factor ≤ gamma fp (3 * n) * (infNorm Lh * infNorm Th * infNorm Uouter) := by
    have hM_nonneg :
        ∀ i j : Fin n,
          0 ≤ ∑ p : Fin n, ∑ q : Fin n, |Lh i p| * |Th p q| * |Uouter q j| :=
      fun i j => Finset.sum_nonneg (fun p _ =>
        Finset.sum_nonneg (fun q _ => by positivity))
    have h1 :
        infNorm B_factor ≤
          gamma fp (3 * n) *
            infNorm (fun i j =>
              ∑ p : Fin n, ∑ q : Fin n, |Lh i p| * |Th p q| * |Uouter q j|) :=
      infNorm_const_mul_le (gamma fp (3 * n)) (gamma_nonneg fp h3n) _ hM_nonneg
    have h2 := infNorm_tripleAbs_le hn_pos Lh Th Uouter
    calc infNorm B_factor
        ≤ gamma fp (3 * n) *
            infNorm (fun i j =>
              ∑ p : Fin n, ∑ q : Fin n, |Lh i p| * |Th p q| * |Uouter q j|) := h1
      _ ≤ gamma fp (3 * n) * (infNorm Lh * infNorm Th * infNorm Uouter) :=
          mul_le_mul_of_nonneg_left h2 (gamma_nonneg fp h3n)
  -- `‖B_solve‖∞` two-term aggregation
  have hBs_le :
      infNorm B_solve ≤
        (2 * gamma fp n + (gamma fp n) ^ 2) *
            (infNorm Lh * infNorm Th * infNorm Uouter) +
          (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
            (infNorm Lh *
              infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) *
              infNorm Uouter) :=
    higham11_15_aasenChainDeltaABound_infNorm_le n hn_pos (gamma fp n)
      (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) Lh Th Uouter
      hγn_nonneg hBT_nonneg
  -- outer-factor infinity-norm caps from `|L̂ i j| ≤ 1`
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hLn : infNorm Lh ≤ ((n - 1 : ℕ) : ℝ) := by
    rw [hcast]
    exact aasen_L_infNorm_le n hn Lh hLdiag_one hLupper hLfirst hLhat_cap
  have hUn : infNorm Uouter ≤ ((n - 1 : ℕ) : ℝ) := by
    rw [hcast]
    exact aasen_LT_infNorm_le n hn Lh hLdiag_one hLupper hLfirst hLhat_cap
  have hα_nonneg : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hTn_nonneg : (0 : ℝ) ≤ infNorm Th := infNorm_nonneg _
  -- middle-solve budget norm cap `‖BT‖∞ ≤ f(γ_n) ‖T̂‖∞` (via `κmidLU = 1`)
  have hBTn :
      infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) ≤
        higham9_14_f (gamma fp n) * infNorm Th := by
    have h :=
      higham11_15_aasenMiddleSolveBudget_infNorm_le_of_factor_product_bound
        fp n hn_pos L_T_hat U_T_hat Th 1 hnval (by rw [one_mul]; exact hmiddle_factors)
    simpa [mul_one] using h
  -- product caps
  have hLU : infNorm Lh * infNorm Uouter ≤ ((n - 1 : ℕ) : ℝ) ^ 2 := by
    calc infNorm Lh * infNorm Uouter
        ≤ ((n - 1 : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ) :=
          mul_le_mul hLn hUn (infNorm_nonneg _) hα_nonneg
      _ = ((n - 1 : ℕ) : ℝ) ^ 2 := by ring
  have hPle :
      infNorm Lh * infNorm Th * infNorm Uouter ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * infNorm Th := by
    calc infNorm Lh * infNorm Th * infNorm Uouter
        = (infNorm Lh * infNorm Uouter) * infNorm Th := by ring
      _ ≤ ((n - 1 : ℕ) : ℝ) ^ 2 * infNorm Th :=
          mul_le_mul_of_nonneg_right hLU hTn_nonneg
  have hQle :
      infNorm Lh *
          infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) *
          infNorm Uouter ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * higham9_14_f (gamma fp n) * infNorm Th := by
    calc infNorm Lh *
            infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) *
            infNorm Uouter
        = (infNorm Lh * infNorm Uouter) *
            infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) := by ring
      _ ≤ ((n - 1 : ℕ) : ℝ) ^ 2 *
            infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) :=
          mul_le_mul_of_nonneg_right hLU (infNorm_nonneg _)
      _ ≤ ((n - 1 : ℕ) : ℝ) ^ 2 * (higham9_14_f (gamma fp n) * infNorm Th) :=
          mul_le_mul_of_nonneg_left hBTn (sq_nonneg _)
      _ = ((n - 1 : ℕ) : ℝ) ^ 2 * higham9_14_f (gamma fp n) * infNorm Th := by ring
  -- gamma-share coefficients
  have hcT : (0 : ℝ) ≤ 2 * gamma fp n + (gamma fp n) ^ 2 := by
    nlinarith [hγn_nonneg, sq_nonneg (gamma fp n)]
  have hc2 : (0 : ℝ) ≤ 1 + 2 * gamma fp n + (gamma fp n) ^ 2 := by
    nlinarith [hγn_nonneg, sq_nonneg (gamma fp n)]
  -- the bracket of shares folds into `γ_{15n+25}`
  have hb2 : 2 * gamma fp n + (gamma fp n) ^ 2 ≤ gamma fp (2 * n) :=
    higham11_8_two_gamma_plus_sq_le_gamma_2n fp n h2n
  have hb6 :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) * higham9_14_f (gamma fp n) ≤
        gamma fp (6 * n) :=
    higham11_8_one_plus_two_gamma_plus_sq_mul_higham9_14_f_gamma_le_gamma_6n fp n h6n
  have hparts :
      gamma fp (2 * n) + gamma fp (3 * n) + gamma fp (2 * n) + gamma fp (6 * n) ≤
        gamma fp (15 * n + 25) :=
    higham11_8_gamma_2n_plus_3n_plus_2n_plus_6n_le_gamma_15n25 fp n hval
  have hγ2n_nonneg : (0 : ℝ) ≤ gamma fp (2 * n) := gamma_nonneg fp h2n
  have hbracket :
      gamma fp (3 * n) + (2 * gamma fp n + (gamma fp n) ^ 2) +
          (1 + 2 * gamma fp n + (gamma fp n) ^ 2) * higham9_14_f (gamma fp n) ≤
        gamma fp (15 * n + 25) := by
    linarith
  -- termwise monotone lifts
  have t1 :
      gamma fp (3 * n) * (infNorm Lh * infNorm Th * infNorm Uouter) ≤
        gamma fp (3 * n) * (((n - 1 : ℕ) : ℝ) ^ 2 * infNorm Th) :=
    mul_le_mul_of_nonneg_left hPle (gamma_nonneg fp h3n)
  have t2 :
      (2 * gamma fp n + (gamma fp n) ^ 2) *
          (infNorm Lh * infNorm Th * infNorm Uouter) ≤
        (2 * gamma fp n + (gamma fp n) ^ 2) * (((n - 1 : ℕ) : ℝ) ^ 2 * infNorm Th) :=
    mul_le_mul_of_nonneg_left hPle hcT
  have t3 :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (infNorm Lh *
            infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) *
            infNorm Uouter) ≤
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (((n - 1 : ℕ) : ℝ) ^ 2 * higham9_14_f (gamma fp n) * infNorm Th) :=
    mul_le_mul_of_nonneg_left hQle hc2
  -- assemble
  calc infNorm ΔA
      ≤ infNorm B_factor + infNorm B_solve := hΔ_split
    _ ≤ gamma fp (3 * n) * (infNorm Lh * infNorm Th * infNorm Uouter) +
          ((2 * gamma fp n + (gamma fp n) ^ 2) *
              (infNorm Lh * infNorm Th * infNorm Uouter) +
            (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
              (infNorm Lh *
                infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) *
                infNorm Uouter)) := add_le_add hBf_le hBs_le
    _ ≤ gamma fp (3 * n) * (((n - 1 : ℕ) : ℝ) ^ 2 * infNorm Th) +
          ((2 * gamma fp n + (gamma fp n) ^ 2) *
              (((n - 1 : ℕ) : ℝ) ^ 2 * infNorm Th) +
            (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
              (((n - 1 : ℕ) : ℝ) ^ 2 * higham9_14_f (gamma fp n) * infNorm Th)) := by
        linarith [t1, t2, t3]
    _ = (gamma fp (3 * n) + (2 * gamma fp n + (gamma fp n) ^ 2) +
            (1 + 2 * gamma fp n + (gamma fp n) ^ 2) * higham9_14_f (gamma fp n)) *
          (((n - 1 : ℕ) : ℝ) ^ 2 * infNorm Th) := by ring
    _ ≤ gamma fp (15 * n + 25) * (((n - 1 : ℕ) : ℝ) ^ 2 * infNorm Th) :=
        mul_le_mul_of_nonneg_right hbracket
          (mul_nonneg (sq_nonneg _) hTn_nonneg)
    _ = ((n - 1 : ℕ) : ℝ) ^ 2 * gamma fp (15 * n + 25) * infNorm Th := by ring

end LeanFpAnalysis.FP.Ch11Closure.AasenDirect
