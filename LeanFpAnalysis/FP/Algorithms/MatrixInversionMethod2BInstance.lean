/-
Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
Chapter 14 ("Matrix Inversion"), §14.3, equation (14.14), Method 2B
(pp. 266-267).

  Method 2B computes the off-diagonal block as `X21 = -X22 L21 X11`, so the
  rounded block satisfies (14.14)

      X̂21 = -X̂22 L21 X̂11 + Δ(X̂22, L21, X̂11).

  Postmultiplying by `L11` (with `X̂11 L11 = I`, since X11 is computed by
  Method 2) gives the off-diagonal left residual

      X̂21 L11 + X̂22 L21 = Δ(X̂22, L21, X̂11) L11,

  whose bound carries the extra factor `|X̂11||L11|`.  Higham notes this factor
  is what breaks the desired residual form (14.8): "the left residual is not
  guaranteed to be small ... the method must be regarded as unstable when the
  block size exceeds 1" (p. 266).

  Codex's `MatrixInversion.lean` supplies the algebraic hinge and a *conditional*
  obstruction wrapper
  `higham14_eq14_14_method2B_no_small_offdiag_residual_of_propagated_delta`,
  which still assumes a "large propagated delta" hypothesis.  THIS FILE closes
  the residual row by constructing a concrete, source-shaped INSTANCE (a
  2×2 ill-conditioned `L11`, block size `m = 2 > 1` as the source requires) and
  DERIVING that hypothesis: a genuine `O(u)`-small block-update perturbation is
  amplified by the ill-conditioned `L11` into an off-diagonal residual of size
  `ε·t`, which exceeds the `O(u)` budget `ε` by the conditioning factor `t` and
  grows without bound as `t → ∞`.

  Import-only extension; reuses Codex's `higham14_eq14_14_method2B_*` wrappers
  verbatim.  No new axioms.
-/
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra
import LeanFpAnalysis.FP.Algorithms.MatrixInversion

namespace LeanFpAnalysis.FP.Ch14Ext

open scoped BigOperators

/-!
### The concrete Method 2B witness (block size `m = 2`, `r = 1`)

All data is parametrized by the conditioning parameter `t` and the roundoff
level `ε`.  The diagonal block `L11` is the classic unit lower-triangular
ill-conditioned matrix `[[1,0],[-t,1]]`; its exact inverse `X11 = [[1,0],[t,1]]`
satisfies `X11 L11 = I` but has `|X11||L11|` entries of size `t`.
-/

/-- Method 2B diagonal block `L11 = [[1, 0], [-t, 1]]` (unit lower triangular,
    ill conditioned for large `t`). -/
noncomputable def ch14ext_method2B_L11 (t : ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![1, 0], ![-t, 1]]

/-- Exact inverse of `L11`: `X11 = [[1, 0], [t, 1]]`.  Here `X11 L11 = I`
    holds exactly, modelling "X11 computed by Method 2" at its best case. -/
noncomputable def ch14ext_method2B_X11 (t : ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![1, 0], ![t, 1]]

/-- Trailing diagonal-block inverse `X̂22` (a fixed nonzero `1×1` value). -/
noncomputable def ch14ext_method2B_X22 : Fin 1 → Fin 1 → ℝ :=
  fun _ _ => 2

/-- Rectangular lower-left block `L21` (a fixed nonzero `1×2` block). -/
noncomputable def ch14ext_method2B_L21 : Fin 1 → Fin 2 → ℝ :=
  ![![3, 5]]

/-- The genuine `O(u)`-small block-update perturbation `Δ = [0, ε]`: an
    entrywise product-rounding error of size `≤ ε` in the `(14.14)` triple
    product, placed in the second column so that postmultiplication by the
    large `L11` entry `-t` amplifies it. -/
noncomputable def ch14ext_method2B_delta (ε : ℝ) : Fin 1 → Fin 2 → ℝ :=
  ![![0, ε]]

/-- The rounded off-diagonal block from equation (14.14):
    `X̂21 = -X̂22 L21 X̂11 + Δ`, i.e. the exact Method 2B triple product plus the
    explicit product-rounding perturbation `Δ`. -/
noncomputable def ch14ext_method2B_X21hat (ε t : ℝ) : Fin 1 → Fin 2 → ℝ :=
  fun i j =>
    higham14_method2BBlockUpdateExact
        ch14ext_method2B_X22 ch14ext_method2B_L21 (ch14ext_method2B_X11 t) i j +
      ch14ext_method2B_delta ε i j

/-- `X̂11 L11 = I` exactly: `X11 = [[1,0],[t,1]]` is a left inverse of
    `L11 = [[1,0],[-t,1]]`.  This is the "X11 computed by Method 2" premise of
    the (14.14) residual analysis, in its exact best case. -/
theorem ch14ext_method2B_left_inverse (t : ℝ) :
    IsLeftInverse 2 (ch14ext_method2B_L11 t) (ch14ext_method2B_X11 t) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [ch14ext_method2B_L11, ch14ext_method2B_X11, Fin.sum_univ_two]

/-- The Method 2B block-update perturbation of this instance is exactly the
    explicit `Δ = [0, ε]` (the exact triple product cancels). -/
theorem ch14ext_method2B_delta_eq (ε t : ℝ) :
    higham14_method2BBlockUpdateDelta (ch14ext_method2B_X21hat ε t)
        ch14ext_method2B_X22 ch14ext_method2B_L21 (ch14ext_method2B_X11 t) =
      ch14ext_method2B_delta ε := by
  funext i j
  simp [higham14_method2BBlockUpdateDelta, ch14ext_method2B_X21hat]

/-- The perturbation is a *genuine* `O(u)`-small block-update error: its
    componentwise product-error certificate holds with roundoff level `ε` and
    unit envelope `absBound ≡ 1`.  Hence the concrete `X̂21` satisfies Codex's
    source-facing `Method2BBlockUpdateSpec`. -/
theorem ch14ext_method2B_spec (ε t : ℝ) (hε : 0 ≤ ε) :
    Method2BBlockUpdateSpec (ch14ext_method2B_X21hat ε t)
      ch14ext_method2B_X22 ch14ext_method2B_L21 (ch14ext_method2B_X11 t)
      ε (fun _ _ => 1) := by
  apply higham14_eq14_14_method2B_block_update_spec_of_product_error
  intro i j
  have hΔ :
      ch14ext_method2B_X21hat ε t i j -
        higham14_method2BBlockUpdateExact ch14ext_method2B_X22
          ch14ext_method2B_L21 (ch14ext_method2B_X11 t) i j =
        ch14ext_method2B_delta ε i j := by
    simp [ch14ext_method2B_X21hat]
  rw [hΔ]
  fin_cases j <;>
    simp [ch14ext_method2B_delta, abs_of_nonneg, hε]

/-- **Named residual (quantitative core).**  The propagated block-update
    perturbation `Δ L11`, which by Codex's identity equals the whole
    off-diagonal left residual `X̂21 L11 + X̂22 L21`, has `(0,0)` entry exactly
    `-(ε·t)`.  The roundoff-level error `ε` is thus amplified by the
    conditioning factor `t = |X̂11||L11|`-scale — precisely Higham's obstruction
    to the desired residual form (14.8). -/
theorem ch14ext_method2B_residual_value (ε t : ℝ) :
    rectMatMul (ch14ext_method2B_delta ε) (ch14ext_method2B_L11 t)
        (0 : Fin 1) (0 : Fin 2) = -(ε * t) := by
  simp [rectMatMul, Fin.sum_univ_two, ch14ext_method2B_delta,
    ch14ext_method2B_L11]

/-- **Headline (14.14) Method 2B instability witness.**

    For any positive roundoff level `ε` and any conditioning `t > 1`, the
    concrete instance's off-diagonal left-residual block
    `X̂21 L11 + X̂22 L21` cannot satisfy the `O(u)` budget `ε`: it already
    violates it in the `(0,0)` entry, where the residual has magnitude `ε·t`.

    This DERIVES the "large propagated delta" hypothesis that Codex's
    `higham14_eq14_14_method2B_no_small_offdiag_residual_of_propagated_delta`
    wrapper left assumed, from concrete floating-point-shaped data: an honest
    `O(u)` block-update error amplified by an ill-conditioned `L11`. -/
theorem ch14ext_method2B_offdiag_residual_not_small
    (ε t : ℝ) (hε : 0 < ε) (ht : 1 < t) :
    ¬ (∀ (i : Fin 1) (j : Fin 2),
        |rectMatMul (ch14ext_method2B_X21hat ε t) (ch14ext_method2B_L11 t) i j +
            rectMatMul ch14ext_method2B_X22 ch14ext_method2B_L21 i j| ≤ ε) := by
  have hεt : (0 : ℝ) < ε * t := mul_pos hε (lt_trans one_pos ht)
  refine
    higham14_eq14_14_method2B_no_small_offdiag_residual_of_propagated_delta
      (ch14ext_method2B_L11 t) (ch14ext_method2B_X11 t)
      (ch14ext_method2B_X21hat ε t) ch14ext_method2B_X22 ch14ext_method2B_L21
      ε (fun _ _ => 1) (fun _ _ => ε)
      (ch14ext_method2B_spec ε t (le_of_lt hε))
      (ch14ext_method2B_left_inverse t)
      (i0 := (0 : Fin 1)) (j0 := (0 : Fin 2)) ?_
  -- Derive the largeness: `ε < |Δ L11 (0,0)| = ε·t`.
  rw [ch14ext_method2B_delta_eq ε t, ch14ext_method2B_residual_value ε t,
    abs_neg, abs_of_pos hεt]
  nlinarith [hε, ht]

/-- **Unbounded amplification (non-`O(u)`).**  For a fixed positive roundoff
    level `ε`, the `(0,0)` off-diagonal residual entry exceeds any prescribed
    bound `C` once the conditioning parameter is large enough.  Thus the
    residual is not `O(u)`: its size relative to `ε` is unbounded, confirming
    that Method 2B "must be regarded as unstable when the block size exceeds 1"
    (Higham, §14.3, p. 266). -/
theorem ch14ext_method2B_residual_amplification_unbounded
    (ε : ℝ) (hε : 0 < ε) (C : ℝ) :
    ∃ t : ℝ, C < |rectMatMul (ch14ext_method2B_delta ε)
        (ch14ext_method2B_L11 t) (0 : Fin 1) (0 : Fin 2)| := by
  refine ⟨(|C| + 1) / ε + 1, ?_⟩
  rw [ch14ext_method2B_residual_value]
  have ht : (0 : ℝ) < (|C| + 1) / ε + 1 := by positivity
  have hεt : (0 : ℝ) < ε * ((|C| + 1) / ε + 1) := mul_pos hε ht
  rw [abs_neg, abs_of_pos hεt]
  have hCle : C ≤ |C| := le_abs_self C
  have hexp : ε * ((|C| + 1) / ε + 1) = (|C| + 1) + ε := by
    field_simp
  rw [hexp]
  linarith [hCle, hε]

end LeanFpAnalysis.FP.Ch14Ext
