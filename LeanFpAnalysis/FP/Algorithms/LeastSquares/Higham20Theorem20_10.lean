import LeanFpAnalysis.FP.Algorithms.LeastSquares.LSE

namespace LeanFpAnalysis.FP

open scoped BigOperators Matrix.Norms.Frobenius

namespace Theorem20_10

/-!
# Higham, Chapter 20, Theorem 20.10

This module gives a compact end-to-end surface for the rounded Householder GQR
path developed in `LSE.lean`.  In particular, the same named returned vector is
used in both parts of the theorem.  The construction computes Householder
panels for `Bᵀ` and the reversed trailing `A Q₂` block, computes the transformed
right-hand side, and performs the two rounded triangular solves.

The coefficients below are the explicit conservative gamma envelopes proved
for that concrete path.  They play the role of Higham's dimension-dependent
`γ̃_mn` and `γ̃_np` constants without claiming sharper constants than the local
implementation lemmas establish.
-/

/-- The proof-level returned vector of the concrete rounded Householder GQR
path.  Its specification identifies it with the rounded transformed-tail
triangular solve for the constructed GQR record. -/
noncomputable def computedX {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold
          hB hStack) :
    Fin (p + q) → ℝ :=
  theorem20_10_constructed_householder_returned_xhat
    fp A B b d hp hq hB hStack hu

/-- The concrete rounded Householder GQR path supplies the Part (a)
perturbation certificate for its named returned vector.

This is the missing consolidation step between the already proved concrete
factor/RHS construction, rank preservation, rounded triangular solves, and the
generic Part (a) certificate.  No perturbed rank, nonzero triangular diagonal,
or computed-vector identification is assumed: all three are discharged from
the source ranks and the single public unit-roundoff threshold. -/
theorem computedX_partA_certificate
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold
          hB hStack) :
    Nonempty
      (Theorem20_10PartAPerturbationCertificate A B b d
        (computedX fp A B b d hp hq hB hStack hu)
        (theorem20_10_householder_composed_partA_gammaA fp r p q)
        (theorem20_10_householder_composed_partA_gammaB fp r p q)) := by
  let xhat : Fin (p + q) → ℝ :=
    theorem20_10_constructed_householder_returned_xhat
      fp A B b d hp hq hB hStack hu
  let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
    fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
  let beta : Fin q → ℝ :=
    theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
  rcases
      theorem20_10_constructed_householder_returned_xhat_rank_preserved_triangular_solve_and_exact_perturbed_minimizer_of_source_ranks_unit_roundoff_smallnessThreshold_composed_conservative_gamma
        fp A B b d hp hq hB hStack hu with
    ⟨DeltaA0, DeltaB0, Deltab0, _hDeltaBrep, hDeltaA0, hDeltaB0,
      hDeltab0, hpert, _hQeq, _hSeq, htail, hxhat, hrank,
      _htri, _hpartB⟩
  have hdiag :
      (∀ i : Fin p, hpert.S i i ≠ 0) ∧
        (∀ i : Fin q, hpert.L22 i i ≠ 0) :=
    (hpert.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero).1 hrank
  rcases
      theorem20_10_householder_component_unit_roundoff_conditions_of_lt_smallnessThreshold
        fp hB hStack hp hq hu with
    ⟨hsmallA, hsmallB, _hhalf, _hunit⟩
  have hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallA (by norm_num)
  have hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallB (by norm_num)
  have hKA_ge_two : 2 ≤ householderConstructApplyGammaIndex (r + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hKB_ge_two : 2 ≤ householderConstructApplyGammaIndex (p + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hvalid2S : gammaValid fp (2 * p) := by
    apply gammaValid_mono fp _ hvalidB
    calc
      2 * p = p * 2 := by omega
      _ ≤ p * householderConstructApplyGammaIndex (p + q) :=
        Nat.mul_le_mul_left p hKB_ge_two
  have hvalid2L22 : gammaValid fp (2 * q) := by
    apply gammaValid_mono fp _ hvalidA
    calc
      2 * q ≤ 2 * (p + q) := Nat.mul_le_mul_left 2 (by omega)
      _ = (p + q) * 2 := by omega
      _ ≤ (p + q) * householderConstructApplyGammaIndex (r + q) :=
        Nat.mul_le_mul_left (p + q) hKA_ge_two
  have hvalidp : gammaValid fp p :=
    gammaValid_mono fp (by omega) hvalid2S
  have hvalidq : gammaValid fp q :=
    gammaValid_mono fp (by omega) hvalid2L22
  have hgammap_nonneg : 0 ≤ gamma fp p := gamma_nonneg fp hvalidp
  have hgammaq_nonneg : 0 ≤ gamma fp q := gamma_nonneg fp hvalidq
  rcases
      theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_double_gammaValid_source_bounds_transformed_tail
        fp hpert beta (fun i => b i + Deltab0 i) d
        (gamma fp q) (gamma fp p) (0 : Fin (r + q) → ℝ)
        hgammap_nonneg le_rfl le_rfl hdiag.1 hdiag.2 hvalid2S hvalid2L22 with
    ⟨_DeltaS, _DeltaL22, _hDeltaS, _hDeltaL22,
      _hDeltaSfrob, _hDeltaL22frob, hcert⟩
  have hzero :
      vecNorm2 (0 : Fin (r + q) → ℝ) ≤
        gamma fp q * vecNorm2 (fun i => b i + Deltab0 i) := by
    change vecNorm2 (fun _ : Fin (r + q) => 0) ≤
      gamma fp q * vecNorm2 (fun i => b i + Deltab0 i)
    rw [vecNorm2_zero]
    exact mul_nonneg hgammaq_nonneg (vecNorm2_nonneg _)
  have htail0 : ∀ j : Fin q,
      matMulVec (r + q) (matTranspose hpert.U)
          (fun k => (b k + Deltab0 k) + (0 : Fin (r + q) → ℝ) k)
          (Fin.natAdd r j) = beta j := by
    intro j
    simpa using htail j
  have hcert2 := hcert hzero htail0
  have hxhat' :
      xhat = theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d := by
    simpa [xhat, Qb, beta] using hxhat
  rw [← hxhat'] at hcert2
  have hgammaB0_nonneg :
      0 ≤ theorem20_10_householder_gammaB fp r p q := by
    simpa [theorem20_10_householder_gammaB] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidB
  have hgammaB_solution :
      gamma fp p ≤ theorem20_10_householder_composed_partA_gammaB fp r p q := by
    dsimp [theorem20_10_householder_composed_partA_gammaB]
    nlinarith
  have hcomposed :
      Nonempty
        (Theorem20_10PartAPerturbationCertificate A B b d xhat
          (theorem20_10_householder_composed_partA_gammaA fp r p q)
          (theorem20_10_householder_composed_partA_gammaB fp r p q)) :=
    theorem20_10_nonempty_partA_certificate_compose_source_perturbations
      A B b d xhat DeltaA0 DeltaB0 Deltab0
      hgammaq_nonneg hgammap_nonneg hDeltaA0 hDeltaB0 hDeltab0
      (by
        dsimp [theorem20_10_householder_composed_partA_gammaA]
        exact le_max_left _ _)
      (by
        dsimp [theorem20_10_householder_composed_partA_gammaA]
        exact le_max_right _ _)
      (by
        dsimp [theorem20_10_householder_composed_partA_gammaB]
        exact le_rfl)
      hgammaB_solution hcert2
  simpa [computedX, xhat] using hcomposed

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), for the same named
computed Householder GQR vector used by Part (b).

The conclusion is the printed mixed-stability form: the returned vector is an
`O(γ̃_np)` relative perturbation of the exact solution of an LSE problem whose
`A`, `B`, and `b` data have the displayed `O(γ̃_mn)`/`O(γ̃_np)` normwise
perturbations, while `d` is unchanged. -/
theorem computedX_partA_mixed_stability
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold
          hB hStack) :
    let xhat := computedX fp A B b d hp hq hB hStack hu
    let gammaA := theorem20_10_householder_composed_partA_gammaA fp r p q
    let gammaB := theorem20_10_householder_composed_partA_gammaB fp r p q
    ∃ (DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
      (DeltaB : Fin p → Fin (p + q) → ℝ)
      (Deltab : Fin (r + q) → ℝ)
      (DeltaX : Fin (p + q) → ℝ)
      (x : Fin (p + q) → ℝ),
      (∀ j, xhat j = x j + DeltaX j) ∧
      vecNorm2 DeltaX ≤ gammaB * vecNorm2 x ∧
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      vecNorm2 Deltab ≤ gammaA * vecNorm2 b ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      IsLSEMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fun i j => B i j + DeltaB i j) d x := by
  dsimp
  rcases computedX_partA_certificate fp A B b d hp hq hB hStack hu with
    ⟨cert⟩
  have hcore :=
    theorem20_10_partA_mixed_stability_of_perturbation_certificate
      A B b d (computedX fp A B b d hp hq hB hStack hu) cert
  dsimp at hcore
  rcases hcore with
    ⟨DeltaA, DeltaB, Deltab, DeltaX, x,
      hAeq, hBeq, hbeq, hxhat, hDeltaX, hDeltaA,
      hDeltab, hDeltaB, hx, _hmethod⟩
  subst DeltaA
  subst DeltaB
  subst Deltab
  exact
    ⟨cert.DeltaA, cert.DeltaB, cert.Deltab, DeltaX, x, hxhat, hDeltaX,
      hDeltaA, hDeltab, hDeltaB, hx⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), for the same named
computed Householder GQR vector used by Part (a).

The vector is the exact solution of a perturbed LSE problem, including a
constraint-right-hand-side perturbation.  All four perturbations carry the
explicit normwise budgets in the source theorem. -/
theorem computedX_partB_backward_error
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold
          hB hStack) :
    let xhat := computedX fp A B b d hp hq hB hStack hu
    let gammaA := theorem20_10_householder_composed_partA_gammaA fp r p q
    let gammaB := theorem20_10_householder_composed_partA_gammaB fp r p q
    ∃ (DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
      (DeltaB : Fin p → Fin (p + q) → ℝ)
      (Deltab : Fin (r + q) → ℝ)
      (Deltad : Fin p → ℝ),
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      vecNorm2 Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
      IsLSEMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fun i j => B i j + DeltaB i j)
        (fun i => d i + Deltad i) xhat := by
  dsimp
  rcases
      theorem20_10_constructed_householder_returned_xhat_exact_perturbed_minimizer_of_source_ranks_unit_roundoff_smallnessThreshold_composed_conservative_gamma
        fp A B b d hp hq hB hStack hu with
    ⟨DeltaA, DeltaB, Deltab, Deltad, hDeltad,
      hDeltaA, hDeltaB, hDeltab, hDeltadBound, hxhat, _hunique⟩
  exact
    ⟨DeltaA, DeltaB, Deltab, Deltad,
      hDeltaA, hDeltaB, hDeltab, hDeltadBound, hxhat⟩

end Theorem20_10

end LeanFpAnalysis.FP
