/-
Algorithms/Cholesky/AasenTridiagGEPPCh11Closure.lean

Chapter 11 closure, **Piece D** of the faithful Theorem-11.8 (Aasen) closure:
the *middle-factor* backward-error input needed by the Aasen solve chain.

For `P A Pᵀ = L̂ T̂ L̂ᵀ` (Aasen's method), the middle solve `T̂ y = z` for the
symmetric tridiagonal factor `T̂` must be discharged with a factorisation whose
*factor-norm growth* is controlled by `‖T̂‖∞` — **without** a diagonal-dominance
hypothesis (Aasen's `T̂` need not be diagonally dominant).

## Why the naive tridiagonal-GEPP growth route (`≤ 3|(Π·T̂)|`) does not close

The task's primary target #3 asked for the componentwise partial-pivoting growth
bound

    `∀ i j, ∑ k, |M̂ i k| · |Û k j| ≤ 3 · |(Π·T̂) i j|`

for a tridiagonal GEPP factorisation `M̂ Û = Π·T̂`.  This componentwise bound is
**false** for genuine tridiagonal partial pivoting, because a row interchange
creates *fill* at a position where the permuted matrix is zero.  Concretely, for

    T̂ = [[d0, c0, 0 ], [a1, d1, c1], [0, a2, d2]]   with |a1| > |d0|,

step 0 swaps rows 0 and 1, so after elimination `Û` acquires a second
super-diagonal entry `Û_{1,2} = -m1·c1 ≠ 0` (with multiplier `m1 = d0/a1`),
while the permuted matrix has `(Π·T̂)_{1,2} = 0` (row 1 of `Π·T̂` is the original
row 0 = `[d0, c0, 0]`).  Then

    (|M̂||Û|)_{1,2} = |m1|·|c1| + 1·|m1·c1| = 2|m1||c1| > 0 = 3·|(Π·T̂)_{1,2}|,

so the componentwise `≤ 3|(Π·T̂)|` claim is violated.  The correct partial-pivot
statement is *normwise* (`‖ |M̂||Û| ‖∞ ≤ κ ‖T̂‖∞`), and its honest constant is
`κ ≈ 12`, **not** `3` (each `Û` row has ≤ 3 nonzeros of size ≤ `2·maxEntry`, and
`|M̂| ≤ 1` doubles the row).  The repository now has an **exact** recursive
partial-pivoting trace and a proof of the tridiagonal growth factor `ρ ≤ 2`.
The trace-level certificate API does not expose the factor band/fill support,
however, so the unconditional reusable consequence proved below is the weaker
row-sum estimate `‖M̂‖∞‖Û‖∞ ≤ 2n²‖T̂‖∞`.  There is still no rounded
pivoted-GEPP producer (the reusable rounded Doolittle loop
`higham9_2_rectRoundedLoop*` performs **no** pivoting), so this exact result does
not by itself discharge the computed middle solve in Theorem 11.8.

## Delivered routes: exact GEPP bound and the §11.1.4 Bunch factorisation

Per the task's explicit fallback, we instead supply the middle-solve factor-norm
input from Bunch's method (Algorithm 11.6), whose factor-norm growth is
**already discharged without any dominance hypothesis** in
`BunchTridiagonalHFactorCh11Closure.hfactor_bound`:

    `higham11_4_bunchKaufmanProductEntry n L̂ D̂ i j ≤ hfactorConst fp · Amax`

(with the dimension-independent constant `c₀ = hfactorConst fp`).  Here we lift
that per-entry bound to the normwise factor-norm bound the Aasen assembly needs:

    `‖ |L̂||D̂||L̂ᵀ| ‖∞ ≤ (n · c₀) · ‖T̂‖∞`   (no dominance),

so the Aasen middle solve can be routed through the Bunch factorisation of `T̂`
(the assembly's componentwise budget then reads `|L̂||L_B||D_B||L_Bᵀ||L̂ᵀ|`, the
same normwise class as the printed `(n−1)² γ_{15n+25} ‖T̂‖∞`).

No `sorry`/`admit`/`axiom`/`native_decide`; everything below is derived from the
already-closed Bunch factor-norm bound and the `infNorm` row-sum machinery.
-/
import LeanFpAnalysis.FP.Algorithms.Cholesky.AasenGrowthCh11Closure
import LeanFpAnalysis.FP.Algorithms.Cholesky.BunchTridiagonalHFactorCh11Closure

open scoped BigOperators

namespace LeanFpAnalysis.FP.Ch11Closure.AasenDirect

open LeanFpAnalysis.FP
open LeanFpAnalysis.FP.Ch11Closure
open LeanFpAnalysis.FP.Ch11Closure.Mixed
open LeanFpAnalysis.FP.Ch11Closure.HFactor

/-- The nonnegative absolute Bunch factor-product matrix `|L̂||D̂||L̂ᵀ|` of the
Algorithm-11.6 factorisation of `T̂` recorded by the pivot schedule `s`.  This is
the middle-factor "factor norm" whose growth the Aasen solve chain must bound. -/
noncomputable def bunchAbsFactorProduct (fp : FPModel) {n : ℕ}
    (s : PivotSchedule n) (T : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j =>
    higham11_4_bunchKaufmanProductEntry n (flMixedL fp s T) (flMixedD fp s T) i j

/-- Every entry of the Bunch factor-product matrix is nonnegative. -/
theorem bunchAbsFactorProduct_nonneg (fp : FPModel) {n : ℕ}
    (s : PivotSchedule n) (T : Fin n → Fin n → ℝ) (i j : Fin n) :
    0 ≤ bunchAbsFactorProduct fp s T i j :=
  higham11_4_bunchKaufmanProductEntry_nonneg n
    (flMixedL fp s T) (flMixedD fp s T) i j

/-- **Piece D — Bunch middle-solve factor-norm bound (no dominance).**

For a symmetric tridiagonal `T̂` whose Algorithm-11.6 (Bunch) mixed-pivot run is
recorded by the schedule `s` with per-stage pivot data `TriPivotData` and local
scales bounded by `Amax`, the factor norm of the computed Bunch factorisation
obeys

    `‖ |L̂||D̂||L̂ᵀ| ‖∞ ≤ (n · c₀) · Amax`,   `c₀ = hfactorConst fp`,

with **no** diagonal-dominance hypothesis.  This is the middle-factor growth
input the Aasen solve chain needs; the dominance-free constant comes from the
already-closed per-entry bound `hfactor_bound`, lifted here to the normwise
`infNorm` via the row-sum count `n`. -/
theorem bunch_tridiag_absFactor_infNorm_le
    (fp : FPModel) (hval : gammaValid fp 3)
    {n : ℕ} (T : Fin n → Fin n → ℝ) (s : PivotSchedule n)
    (Amax : ℝ) (hAmax0 : 0 ≤ Amax)
    (hdata : TriPivotData fp Amax s T) :
    infNorm (bunchAbsFactorProduct fp s T) ≤ (n : ℝ) * hfactorConst fp * Amax := by
  have hentry :
      ∀ i j : Fin n, bunchAbsFactorProduct fp s T i j ≤ hfactorConst fp * Amax :=
    hfactor_bound fp hval Amax hAmax0 s T hdata
  apply infNorm_le_of_row_sum_le
  · intro i
    calc ∑ j : Fin n, |bunchAbsFactorProduct fp s T i j|
        = ∑ j : Fin n, bunchAbsFactorProduct fp s T i j :=
          Finset.sum_congr rfl
            (fun j _ => abs_of_nonneg (bunchAbsFactorProduct_nonneg fp s T i j))
      _ ≤ ∑ _j : Fin n, hfactorConst fp * Amax :=
          Finset.sum_le_sum (fun j _ => hentry i j)
      _ = (n : ℝ) * hfactorConst fp * Amax := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (hfactorConst_nonneg fp hval)) hAmax0

/-- **Piece D — Bunch middle-solve factor-norm bound in terms of `‖T̂‖∞`.**

Specialising the local scale to `Amax = ‖T̂‖∞` (a legitimate global bound, since
`|T̂ i j| ≤ ‖T̂‖∞`), the Bunch factor norm is controlled by `‖T̂‖∞`:

    `‖ |L̂||D̂||L̂ᵀ| ‖∞ ≤ (n · c₀) · ‖T̂‖∞`.

This is the `‖ |factors| ‖∞ ≤ c · ‖T̂‖∞` input requested by the Aasen assembly. -/
theorem bunch_tridiag_absFactor_infNorm_le_infNorm
    (fp : FPModel) (hval : gammaValid fp 3)
    {n : ℕ} (T : Fin n → Fin n → ℝ) (s : PivotSchedule n)
    (hdata : TriPivotData fp (infNorm T) s T) :
    infNorm (bunchAbsFactorProduct fp s T) ≤ ((n : ℝ) * hfactorConst fp) * infNorm T := by
  have h := bunch_tridiag_absFactor_infNorm_le fp hval T s (infNorm T)
    (infNorm_nonneg T) hdata
  -- `(n:ℝ) * c₀ * ‖T̂‖∞` and `((n:ℝ) * c₀) * ‖T̂‖∞` are the same term.
  simpa [mul_assoc] using h

/-- Matrix-product (`matMul`/`absMatrix`) restatement of the Bunch factor-norm
bound, matching the `|L̂||D̂||L̂ᵀ|` product form consumed by the Aasen
middle-solve budget machinery.  The two product matrices agree entrywise
(`higham11_4_bunchKaufmanProductEntry_eq_absLDLTProduct`), hence share an
`infNorm`. -/
theorem bunch_tridiag_absLDLTProduct_infNorm_le
    (fp : FPModel) (hval : gammaValid fp 3)
    {n : ℕ} (T : Fin n → Fin n → ℝ) (s : PivotSchedule n)
    (Amax : ℝ) (hAmax0 : 0 ≤ Amax)
    (hdata : TriPivotData fp Amax s T) :
    infNorm (higham11_4_absLDLTProduct n (flMixedL fp s T) (flMixedD fp s T)) ≤
      (n : ℝ) * hfactorConst fp * Amax := by
  have heq :
      higham11_4_absLDLTProduct n (flMixedL fp s T) (flMixedD fp s T) =
        bunchAbsFactorProduct fp s T := by
    funext i j
    exact
      (higham11_4_bunchKaufmanProductEntry_eq_absLDLTProduct n
        (flMixedL fp s T) (flMixedD fp s T) i j).symm
  rw [heq]
  exact bunch_tridiag_absFactor_infNorm_le fp hval T s Amax hAmax0 hdata

/-! ### Exact tridiagonal-GEPP factor-norm consequence

The Chapter-9 trace now proves the source growth fact `max |U| ≤ 2 max |T|`
and constructs an exact permuted `LU` certificate with `|L i j| ≤ 1`.  The
available certificate API does not yet expose the sharper band support of the
factors, so converting both max-entry estimates to row-sum norms costs two
factors of `n`. -/

/-- **Unconditional exact-GEPP factor-norm bound available from the current
trace API.**  Every exact partial-pivoting trace for a tridiagonal `T` supplies
permuted factors with

    `‖L‖∞ ‖U‖∞ ≤ 2 n² ‖T‖∞`.

This is derived only from the actual GEPP trace, its unit multiplier bound, and
the proved tridiagonal growth factor `rho ≤ 2`; it is not a target-scale
hypothesis.  It records the strongest bound exposed by those reusable APIs.
The coefficient is too large to replace the coefficient-one hypothesis in the
linear-radius Theorem-11.8 wrapper. -/
theorem tridiag_GEPP_exists_factor_infNorm_product_le_two_n_sq
    {n : ℕ} (hn : 0 < n) (T Utrace : Fin n → Fin n → ℝ)
    (hTri : IsTridiagonal n T)
    (htrace : higham9_7_PartialPivotGEPPUTrace n T Utrace) :
    ∃ L U : Fin n → Fin n → ℝ, ∃ sigma : Fin n → Fin n,
      higham9_2_PermutedLUFactSpec n T L U sigma ∧
      (∀ i j : Fin n, |L i j| ≤ 1) ∧
      infNorm L * infNorm U ≤
        (2 * (n : ℝ) ^ 2) * infNorm T := by
  obtain ⟨L, U, sigma, hLU, hLentry, hUtrace⟩ :=
    higham9_7_PartialPivotGEPPUTrace_exists_PermutedLUFactSpec_L_bound_maxEntryNorm_le
      htrace
  refine ⟨L, U, sigma, hLU, hLentry, ?_⟩
  have hcast_nonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hLnorm : infNorm L ≤ (n : ℝ) := by
    apply infNorm_le_of_row_sum_le
    · intro i
      calc
        ∑ j : Fin n, |L i j| ≤ ∑ _j : Fin n, (1 : ℝ) := by
          exact Finset.sum_le_sum (fun j _ => hLentry i j)
        _ = (n : ℝ) := by simp
    · exact hcast_nonneg
  have htraceMax : maxEntryNorm hn Utrace ≤ 2 * maxEntryNorm hn T := by
    apply maxEntryNorm_le_of_entry_le_bound
    intro i j
    exact higham9_11_tridiag_GEPPUTrace_entry_abs_le_two_mul hn T Utrace
      hTri htrace i j
  have hUnorm : infNorm U ≤ (n : ℝ) * (2 * infNorm T) := by
    calc
      infNorm U ≤ (n : ℝ) * maxEntryNorm hn U :=
        infNorm_le_card_mul_maxEntryNorm hn U
      _ ≤ (n : ℝ) * maxEntryNorm hn Utrace :=
        mul_le_mul_of_nonneg_left (hUtrace hn) hcast_nonneg
      _ ≤ (n : ℝ) * (2 * maxEntryNorm hn T) :=
        mul_le_mul_of_nonneg_left htraceMax hcast_nonneg
      _ ≤ (n : ℝ) * (2 * infNorm T) := by
        gcongr
        exact maxEntryNorm_le_infNorm hn T
  calc
    infNorm L * infNorm U
        ≤ (n : ℝ) * ((n : ℝ) * (2 * infNorm T)) :=
          mul_le_mul hLnorm hUnorm (infNorm_nonneg U) hcast_nonneg
    _ = (2 * (n : ℝ) ^ 2) * infNorm T := by ring

end LeanFpAnalysis.FP.Ch11Closure.AasenDirect
