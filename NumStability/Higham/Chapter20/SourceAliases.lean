import NumStability.Algorithms.LeastSquares.LSQRSolve

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-!
# Higham Chapter 20 source aliases

Source-facing names and compact wrappers for the Chapter 20 least-squares
results proved by the reusable least-squares modules.
-/

/-- Higham, 2nd ed., Chapter 20, equation (20.32):
    `B⁺ r = B⁺ P_B (I - P_A) r`.

Here `P_A = A A⁺` and `P_B = B B⁺`.  The identity only needs the
left-inverse relation for `B⁺` and the source-residual relation `P_A r = 0`;
the symmetry and norm hypotheses used in the following estimate (20.33) are
not needed for this exact algebraic proof line. -/
theorem higham20_eq20_32_Bplus_residual_eq_crossProjection
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (r : Fin m → ℝ)
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0) :
    rectMatMulVec Bplus r =
      rectMatMulVec Bplus
        (rectMatMulVec
          (rectMatMul (rectMatMul B Bplus)
            (fun i j => idMatrix m i j - rectMatMul A Aplus i j)) r) := by
  let PA : Fin m → Fin m → ℝ := rectMatMul A Aplus
  let PB : Fin m → Fin m → ℝ := rectMatMul B Bplus
  let IPA : Fin m → Fin m → ℝ := fun i j => idMatrix m i j - PA i j
  have hBplusPB : rectMatMul Bplus PB = Bplus := by
    calc
      rectMatMul Bplus PB = rectMatMul Bplus (rectMatMul B Bplus) := by
        rfl
      _ = rectMatMul (rectMatMul Bplus B) Bplus := by
        rw [rectMatMul_assoc]
      _ = rectMatMul (idMatrix (k + 1)) Bplus := by
        rw [hleftB]
      _ = Bplus := rectMatMul_id_left Bplus
  have hIPA_r : rectMatMulVec IPA r = r := by
    rw [show IPA =
        (fun i j => idMatrix m i j - rectMatMul A Aplus i j) by
      ext i j
      rfl]
    rw [wedinLemma20_12_rectMatMulVec_projectionComplement]
    rw [hrangeA_residual]
    ext i
    simp
  change rectMatMulVec Bplus r =
    rectMatMulVec Bplus (rectMatMulVec (rectMatMul PB IPA) r)
  symm
  calc
    rectMatMulVec Bplus (rectMatMulVec (rectMatMul PB IPA) r)
        = rectMatMulVec Bplus
            (rectMatMulVec PB (rectMatMulVec IPA r)) := by
            rw [rectMatMulVec_rectMatMul]
    _ = rectMatMulVec Bplus (rectMatMulVec PB r) := by
            rw [hIPA_r]
    _ = rectMatMulVec (rectMatMul Bplus PB) r := by
            rw [← rectMatMulVec_rectMatMul]
    _ = rectMatMulVec Bplus r := by
            rw [hBplusPB]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.6, source-facing existential
    package.

An asymmetric perturbed augmented system with matrix perturbations `DeltaA1`
and `DeltaA2` admits a single symmetric perturbation `DeltaA` for which `y`
is an exact least-squares minimizer.  The witness is `DeltaA1` in the
zero-residual branch and the projector mixture from (20.22) in the nonzero
branch.  The same witness satisfies both printed combined bounds, for
`p = F` and for the repository's operator-2 predicate (`p = 2`). -/
theorem higham20_lemma20_6_exists_symmetric_perturbation_minimizer_and_norm_bounds
    {m n : ℕ} (A DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b s : Fin m → ℝ) (y : Fin n → ℝ)
    (h : LSAsymmetricPerturbedAugmentedSystem A DeltaA1 DeltaA2 b s y)
    {alpha beta : ℝ} (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hDeltaA1 : rectOpNorm2Le DeltaA1 alpha)
    (hDeltaA2 : rectOpNorm2Le DeltaA2 beta) :
    ∃ DeltaA : Fin m → Fin n → ℝ,
      ((s = 0 ∧ DeltaA = DeltaA1) ∨
        (s ≠ 0 ∧ DeltaA = lsLemma20_6Perturbation s DeltaA1 DeltaA2)) ∧
      IsLeastSquaresMinimizer (fun i j => A i j + DeltaA i j) b y ∧
      frobNormRect DeltaA ≤
        Real.sqrt (frobNormRect DeltaA1 ^ 2 + frobNormRect DeltaA2 ^ 2) ∧
      rectOpNorm2Le DeltaA (Real.sqrt (alpha ^ 2 + beta ^ 2)) := by
  by_cases hs : s = 0
  · refine ⟨DeltaA1, Or.inl ⟨hs, rfl⟩, ?_, ?_, ?_⟩
    · exact
        LSAugmentedSystem.isLeastSquaresMinimizer_of_zero_rhs
          (fun i j => A i j + DeltaA1 i j) b (0 : Fin m → ℝ) y
          (LSAsymmetricPerturbedAugmentedSystem.to_augmentedSystem_of_s_eq_zero
            A DeltaA1 DeltaA2 b s y h hs)
    · have hrad_nonneg :
          0 ≤ frobNormRect DeltaA1 ^ 2 + frobNormRect DeltaA2 ^ 2 :=
        add_nonneg (sq_nonneg _) (sq_nonneg _)
      have hroot_sq :
          Real.sqrt
              (frobNormRect DeltaA1 ^ 2 + frobNormRect DeltaA2 ^ 2) ^ 2 =
            frobNormRect DeltaA1 ^ 2 + frobNormRect DeltaA2 ^ 2 :=
        Real.sq_sqrt hrad_nonneg
      nlinarith [frobNormRect_nonneg DeltaA1,
        frobNormRect_nonneg DeltaA2,
        Real.sqrt_nonneg
          (frobNormRect DeltaA1 ^ 2 + frobNormRect DeltaA2 ^ 2)]
    · have hrad_nonneg : 0 ≤ alpha ^ 2 + beta ^ 2 :=
        add_nonneg (sq_nonneg _) (sq_nonneg _)
      have hroot_sq :
          Real.sqrt (alpha ^ 2 + beta ^ 2) ^ 2 = alpha ^ 2 + beta ^ 2 :=
        Real.sq_sqrt hrad_nonneg
      have halpha_root : alpha ≤ Real.sqrt (alpha ^ 2 + beta ^ 2) := by
        nlinarith [Real.sqrt_nonneg (alpha ^ 2 + beta ^ 2), sq_nonneg beta]
      intro x
      exact (hDeltaA1 x).trans
        (mul_le_mul_of_nonneg_right halpha_root (vecNorm2_nonneg x))
  · have hsq : vecNorm2Sq s ≠ 0 :=
      lsLemma20_6Projector_den_ne_zero_of_ne_zero hs
    let DeltaA := lsLemma20_6Perturbation s DeltaA1 DeltaA2
    let sbar : Fin m → ℝ :=
      fun i => lsLemma20_6Beta s DeltaA1 DeltaA2 y * s i
    have haug :
        LSAugmentedSystem (fun i j => A i j + DeltaA i j) b
          (0 : Fin n → ℝ) sbar y := by
      simpa [DeltaA, sbar] using
        LSAsymmetricPerturbedAugmentedSystem.to_augmentedSystem_of_s_ne_zero
          A DeltaA1 DeltaA2 b s y h hs
    refine ⟨DeltaA, Or.inr ⟨hs, rfl⟩, ?_, ?_, ?_⟩
    · exact
        LSAugmentedSystem.isLeastSquaresMinimizer_of_zero_rhs
          (fun i j => A i j + DeltaA i j) b sbar y haug
    · simpa [DeltaA] using
        lsLemma20_6Perturbation_norm_bound_two_frob
          s hsq DeltaA1 DeltaA2
    · simpa [DeltaA] using
        lsLemma20_6Perturbation_norm_bound_two_operator
          s hsq DeltaA1 DeltaA2 halpha hbeta hDeltaA1 hDeltaA2

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equations (20.1)-(20.2):
    one-right-hand-side-budget wrapper for the proved full-column Wedin route.

The single source budget `||Delta b||₂ ≤ eps ||b||₂` supplies the residual
estimate directly.  For the solution estimate, `b = A x + r` and the supplied
operator bound for `A` imply
`||Delta b||₂ ≤ eps (A_norm ||x||₂ + ||r||₂)`.  The matrix-difference radius
is also derived from `B = A + DeltaA`, so neither of those two handoff facts is
duplicated in the public assumptions. -/
theorem higham20_theorem20_1_solution_and_residualRelativeRHS_le_of_one_rhs_budget
    {m k : ℕ} (hm : 0 < m) (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ)
    (b Deltab r s : Fin m → ℝ) (x y : Fin (k + 1) → ℝ)
    {Aplus_norm delta eta DeltaA_norm Deltab_norm kappa eps A_norm : ℝ}
    (hb_norm_pos : 0 < vecNorm2 b)
    (hAplus_pos : 0 < Aplus_norm)
    (hA_norm_pos : 0 < A_norm)
    (heps_nonneg : 0 ≤ eps)
    (hx_norm_pos : 0 < vecNorm2 x)
    (hkappa : kappa = Aplus_norm * A_norm)
    (hdelta : delta = eps * A_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall_eta : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hA : rectOpNorm2Le A A_norm)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hDeltaA_norm_budget : DeltaA_norm ≤ eps * A_norm)
    (hDeltab_norm_budget : Deltab_norm ≤ eps * vecNorm2 b)
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (horth_s : ∀ j : Fin (k + 1), ∑ i : Fin m, B i j * s i = 0) :
    (vecNorm2 (fun j => y j - x j) / vecNorm2 x ≤
        wedinTheorem20_1SolutionRelativeRHS
          kappa eps A_norm (vecNorm2 x) (vecNorm2 r)) ∧
      (vecNorm2 (fun i => r i - s i) / vecNorm2 b ≤
        wedinTheorem20_1ResidualRelativeRHS kappa eps) := by
  have hBA : (fun i j => B i j - A i j) = DeltaA := by
    ext i j
    rw [hB]
    ring
  have hDeltaA_norm_le_delta : DeltaA_norm ≤ delta := by
    rw [hdelta]
    exact hDeltaA_norm_budget
  have hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta := by
    rw [hBA]
    intro z
    exact (hDeltaA z).trans
      (mul_le_mul_of_nonneg_right hDeltaA_norm_le_delta (vecNorm2_nonneg z))
  have hb_decomp : b = fun i => rectMatMulVec A x i + r i := by
    ext i
    have hri := congrFun hr i
    change r i = b i - rectMatMulVec A x i at hri
    linarith
  have hb_norm_le :
      vecNorm2 b ≤ A_norm * vecNorm2 x + vecNorm2 r := by
    calc
      vecNorm2 b =
          vecNorm2 (fun i => rectMatMulVec A x i + r i) := by
            rw [hb_decomp]
      _ ≤ vecNorm2 (rectMatMulVec A x) + vecNorm2 r :=
            vecNorm2_add_le (rectMatMulVec A x) r
      _ ≤ A_norm * vecNorm2 x + vecNorm2 r :=
            add_le_add (hA x) le_rfl
  have hDeltab_norm_budget_solution :
      Deltab_norm ≤ eps * (A_norm * vecNorm2 x + vecNorm2 r) :=
    hDeltab_norm_budget.trans
      (mul_le_mul_of_nonneg_left hb_norm_le heps_nonneg)
  exact
    wedinTheorem20_1_solution_and_residualRelativeRHS_le_of_residual_definitions_min_surface_geometry_column_orthogonal
      hm A B Aplus Bplus DeltaA b Deltab r s x y hb_norm_pos
      hAplus_pos hA_norm_pos heps_nonneg hx_norm_pos hkappa hdelta heta
      hsmall_eta hleftA hleftB hSymA hSymB hDelta hAplus hDeltaA
      hDeltab hDeltaA_norm_budget hDeltab_norm_budget_solution
      hDeltab_norm_budget hrangeA_residual hB hr hs horth_s

end NumStability
