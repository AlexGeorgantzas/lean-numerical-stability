import NumStability.Algorithms.RandomizedLinearAlgebra.Concentration.TraceMGF.LeverageScore
import NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.ExactTransforms.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.LeverageScore.ComputedBasis
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.LeverageScore.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.RowNorm.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.RowNorm.Gram
import NumStability.Analysis.FiniteProbability
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm02.RowSampling.Endpoints
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation07.SubspaceEmbedding.Leverage
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation07.SubspaceEmbedding.LeverageTraceMGF

/-!
# NumStability.Source.DrineasMahoney.RandNLA2016.Equation07.SubspaceEmbedding.ComputedBasis

W11 canonical source correspondence destination. Whole commands are copied unchanged from `NumStability.Algorithms.RandNLA.RowSamplingLeverageComputedBasis`; the historical path re-exports this module.
-/

-- Algorithms/RandNLA/RowSamplingLeverageComputedBasis.lean
--
-- Computed-basis floating-point transfers for Algorithm 2 leverage sampling.
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602




namespace NumStability

open scoped BigOperators ComplexOrder

/-!
## Algorithm 2 leverage sampling with a computed/stored basis table

The leverage law remains exact by project convention.  This file charges the
non-probability matrix table that is actually used in the sampled sketch:
an exact orthonormal analysis basis `U` may be represented downstream by a
computed table `Uhat : ComputedMatrix fp U`.
-/

























































-- ============================================================
-- Actual-input leverage sampling via a right factor A = U C
-- ============================================================





















































































































































































































































































































































































/-- Exact Algorithm 2 equation (7) transferred from the orthonormal analysis
basis to the actual input matrix `A = U C`.

The probability law and leverage probabilities remain the exact law generated
by `U`; the sampled matrix whose Gram appears in the event is the actual input
`preconditionColumns U C`. -/
theorem leverageTraceProbability_eventProb_factoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
    {m r n s : ℕ} {ε δ : ℝ} (U : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hr : 0 < r)
    (hrVar : 0 < (r : ℝ) - 1)
    (hs : 0 < (s : ℝ)) (hε : 0 < ε) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 * (r : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((r : ℝ) - 1) + (2 / 3 : ℝ) * (r : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 * (r : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((r : ℝ) - 1) + (2 / 3 : ℝ) * ε))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s) U hU hr).eventProb
        {samples |
          finiteLoewnerLe
            (fun j k : Fin n =>
              leverageFactoredInputSampleGram U C samples j k -
                rowGram (preconditionColumns U C) j k)
            (fun j k : Fin n =>
              ε * rowGram (preconditionColumns U C) j k) ∧
          finiteLoewnerLe
            (fun j k : Fin n =>
              -(leverageFactoredInputSampleGram U C samples j k -
                rowGram (preconditionColumns U C) j k))
            (fun j k : Fin n =>
              ε * rowGram (preconditionColumns U C) j k)} := by
  classical
  let P := leverageTraceProbability (steps := s) U hU hr
  let E : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe
        (fun a b : Fin r => rowSampleGram s U samples a b - finiteIdMatrix a b)
        (fun a b : Fin r => ε * finiteIdMatrix a b) ∧
      finiteLoewnerLe
        (fun a b : Fin r => -(rowSampleGram s U samples a b - finiteIdMatrix a b))
        (fun a b : Fin r => ε * finiteIdMatrix a b)}
  let G : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe
        (fun j k : Fin n =>
          leverageFactoredInputSampleGram U C samples j k -
            rowGram (preconditionColumns U C) j k)
        (fun j k : Fin n => ε * rowGram (preconditionColumns U C) j k) ∧
      finiteLoewnerLe
        (fun j k : Fin n =>
          -(leverageFactoredInputSampleGram U C samples j k -
            rowGram (preconditionColumns U C) j k))
        (fun j k : Fin n => ε * rowGram (preconditionColumns U C) j k)}
  have hE : 1 - δ ≤ P.eventProb E := by
    simpa [P, E] using
      leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
        (s := s) (ε := ε) (δ := δ) U hU hr hrVar hs hε hδ
        hbudgetUpper hbudgetLower
  have hsubset : E ⊆ G := by
    intro samples hsamples
    rcases hsamples with ⟨hUpperU, hLowerU⟩
    let ExactU : Fin r → Fin r → ℝ :=
      fun a b => rowSampleGram s U samples a b - finiteIdMatrix a b
    let EpsU : Fin r → Fin r → ℝ :=
      fun a b => ε * finiteIdMatrix a b
    let ExactA : Fin n → Fin n → ℝ :=
      fun j k =>
        leverageFactoredInputSampleGram U C samples j k -
          rowGram (preconditionColumns U C) j k
    let EpsA : Fin n → Fin n → ℝ :=
      fun j k => ε * rowGram (preconditionColumns U C) j k
    have hExactA :
        ExactA = leverageRightGramCongruence ExactU C := by
      simpa [ExactA, ExactU] using
        leverageFactoredInput_error_eq_rightGramCongruence_error
          U C samples hU
    have hEpsA :
        leverageRightGramCongruence EpsU C = EpsA := by
      simpa [EpsU, EpsA] using
        leverageRightGramCongruence_smul_finiteIdMatrix_eq_smul_factoredInputGram
          U C hU ε
    have hUpperA :
        finiteLoewnerLe ExactA EpsA := by
      rw [hExactA, ← hEpsA]
      exact finiteLoewnerLe_leverageRightGramCongruence C hUpperU
    have hLowerA :
        finiteLoewnerLe (fun j k : Fin n => -ExactA j k) EpsA := by
      have hcong :
          finiteLoewnerLe
            (leverageRightGramCongruence (fun a b : Fin r => -ExactU a b) C)
            EpsA := by
        rw [← hEpsA]
        exact finiteLoewnerLe_leverageRightGramCongruence C hLowerU
      have hneg :
          (fun j k : Fin n => -ExactA j k) =
            leverageRightGramCongruence (fun a b : Fin r => -ExactU a b) C := by
        rw [hExactA, leverageRightGramCongruence_neg]
      rw [hneg]
      exact hcong
    exact ⟨by simpa [ExactA, EpsA] using hUpperA,
      by simpa [ExactA, EpsA] using hLowerA⟩
  exact hE.trans (FiniteProbability.eventProb_mono P hsubset)





































































































































































































































































































































































































































































































/-- Fully floating-point Algorithm 2 equation (7) transfer with a computed
basis table and computed row-scale denominators. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleGramDotWithComputedBasisDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
    (fp : FPModel) {m n s : ℕ} {ε δ : ℝ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n)
    (hnVar : 0 < (n : ℝ) - 1)
    (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (Uhat : ComputedMatrix fp U)
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb U))
    (hε : 0 < ε) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 * (n : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((n : ℝ) - 1) + (2 / 3 : ℝ) * (n : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 * (n : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((n : ℝ) - 1) + (2 / 3 : ℝ) * ε))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s) U hU hn).eventProb
        {samples |
          finiteLoewnerLe
            (fun j k : Fin n =>
              fl_rowSampleGramDotWithComputedDen fp Uhat.matrix dhat.den
                  samples j k -
                finiteIdMatrix j k)
            (fun j k : Fin n =>
              (ε + leverageComputedBasisDenGramBudget fp U Uhat dhat) *
                finiteIdMatrix j k) ∧
          finiteLoewnerLe
            (fun j k : Fin n =>
              -(fl_rowSampleGramDotWithComputedDen fp Uhat.matrix dhat.den
                  samples j k -
                finiteIdMatrix j k))
            (fun j k : Fin n =>
              (ε + leverageComputedBasisDenGramBudget fp U Uhat dhat) *
                finiteIdMatrix j k)} := by
  classical
  let P := leverageTraceProbability (steps := s) U hU hn
  let τ : ℝ := leverageComputedBasisDenGramBudget fp U Uhat dhat
  let Eexact : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe
        (fun j k : Fin n => rowSampleGram s U samples j k - finiteIdMatrix j k)
        (fun j k : Fin n => ε * finiteIdMatrix j k) ∧
      finiteLoewnerLe
        (fun j k : Fin n => -(rowSampleGram s U samples j k - finiteIdMatrix j k))
        (fun j k : Fin n => ε * finiteIdMatrix j k)}
  let Good : Set (RowTrace m s) := {samples | rowTracePositiveProb U samples}
  let F : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k : Fin n =>
          fl_rowSampleGramDotWithComputedDen fp Uhat.matrix dhat.den samples j k -
            rowSampleGram s U samples j k) ≤ τ}
  let G : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe
        (fun j k : Fin n =>
          fl_rowSampleGramDotWithComputedDen fp Uhat.matrix dhat.den
              samples j k -
            finiteIdMatrix j k)
        (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) ∧
      finiteLoewnerLe
        (fun j k : Fin n =>
          -(fl_rowSampleGramDotWithComputedDen fp Uhat.matrix dhat.den
              samples j k -
            finiteIdMatrix j k))
        (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k)}
  have hE :
      1 - δ ≤ P.eventProb Eexact := by
    simpa [P, Eexact] using
      leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
        (s := s) (ε := ε) (δ := δ) U hU hn hnVar hs hε hδ
        hbudgetUpper hbudgetLower
  have hGoodProb : P.eventProb Good = 1 := by
    let hden : 0 < rowSqNormProbDen U :=
      rowSqNormProbDen_pos_of_orthonormal_columns U hU hn
    simpa [P, Good, leverageTraceProbability] using
      rowSqNormTraceProbability_eventProb_rowTracePositiveProb
        (steps := s) U hden
  have hGood_subset_F : Good ⊆ F := by
    intro samples hgood
    have hgood_pos : rowTracePositiveProb U samples := by
      simpa [Good] using hgood
    simpa [F, τ] using
      leverage_fl_rowSampleGramDotWithComputedBasisDen_perturb_bound
        fp U hU hn hs hγ Uhat dhat samples hgood_pos
  have hF : 1 - (0 : ℝ) ≤ P.eventProb F := by
    have hmono : P.eventProb Good ≤ P.eventProb F :=
      FiniteProbability.eventProb_mono P hGood_subset_F
    linarith
  have hEF :
      1 - (δ + 0) ≤ P.eventProb (Eexact ∩ F) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add P Eexact F δ 0 hE hF
  have hsubset : Eexact ∩ F ⊆ G := by
    intro samples hsamples
    rcases hsamples with ⟨hexact, hpert⟩
    rcases hexact with ⟨hExactUpper, hExactLower⟩
    let Exact : Fin n → Fin n → ℝ :=
      fun j k => rowSampleGram s U samples j k - finiteIdMatrix j k
    let Delta : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_rowSampleGramDotWithComputedDen fp Uhat.matrix dhat.den samples j k -
          rowSampleGram s U samples j k
    have htwo :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        Exact Delta hExactUpper (by simpa [Exact] using hExactLower)
        (by simpa [F, Delta, τ] using hpert)
    rcases htwo with ⟨hUpper, hLower⟩
    have hCompEq :
        (fun j k : Fin n =>
          fl_rowSampleGramDotWithComputedDen fp Uhat.matrix dhat.den
              samples j k -
            finiteIdMatrix j k) =
        fun j k : Fin n => Exact j k + Delta j k := by
      ext j k
      dsimp [Exact, Delta]
      ring
    have hNegCompEq :
        (fun j k : Fin n =>
          -(fl_rowSampleGramDotWithComputedDen fp Uhat.matrix dhat.den
              samples j k -
            finiteIdMatrix j k)) =
        fun j k : Fin n => -(Exact j k + Delta j k) := by
      ext j k
      dsimp [Exact, Delta]
      ring
    have hUpperComp :
        finiteLoewnerLe
          (fun j k : Fin n =>
            fl_rowSampleGramDotWithComputedDen fp Uhat.matrix dhat.den
                samples j k -
              finiteIdMatrix j k)
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) := by
      rw [hCompEq]
      exact hUpper
    have hLowerComp :
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(fl_rowSampleGramDotWithComputedDen fp Uhat.matrix dhat.den
                samples j k -
              finiteIdMatrix j k))
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) := by
      rw [hNegCompEq]
      exact hLower
    exact ⟨hUpperComp, hLowerComp⟩
  have hG := hEF.trans (FiniteProbability.eventProb_mono P hsubset)
  simpa [P, Eexact, F, G, τ] using hG

/-- Fully floating-point Algorithm 2 equation (7) transfer for an actual input
matrix factored as `A = U C`, with an arbitrary already-certified leverage
denominator table.

This is infrastructure for denominator routines: the concrete final theorem
below instantiates `dhat_i = fl_sqrt (fl_mul s p_i)`. -/
theorem leverageTraceProbability_eventProb_factoredInput_fl_rowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
    (fp : FPModel) {m r n s : ℕ} {ε δ : ℝ}
    (U : Fin m → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hr : 0 < r)
    (hrVar : 0 < (r : ℝ) - 1)
    (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb U))
    (hε : 0 < ε) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 * (r : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((r : ℝ) - 1) + (2 / 3 : ℝ) * (r : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 * (r : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((r : ℝ) - 1) + (2 / 3 : ℝ) * ε))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s) U hU hr).eventProb
        {samples |
          finiteLoewnerLe
            (fun j k : Fin n =>
              fl_rowSampleGramDotWithComputedDen fp (preconditionColumns U C)
                  dhat.den samples j k -
                rowGram (preconditionColumns U C) j k)
            (fun j k : Fin n =>
              ε * rowGram (preconditionColumns U C) j k +
                leverageFactoredInputDenGramBudget fp U C dhat *
                  finiteIdMatrix j k) ∧
          finiteLoewnerLe
            (fun j k : Fin n =>
              -(fl_rowSampleGramDotWithComputedDen fp (preconditionColumns U C)
                  dhat.den samples j k -
                rowGram (preconditionColumns U C) j k))
            (fun j k : Fin n =>
              ε * rowGram (preconditionColumns U C) j k +
                leverageFactoredInputDenGramBudget fp U C dhat *
                  finiteIdMatrix j k)} := by
  classical
  let P := leverageTraceProbability (steps := s) U hU hr
  let τ : ℝ := leverageFactoredInputDenGramBudget fp U C dhat
  let Eexact : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe
        (fun j k : Fin n =>
          leverageFactoredInputSampleGram U C samples j k -
            rowGram (preconditionColumns U C) j k)
        (fun j k : Fin n => ε * rowGram (preconditionColumns U C) j k) ∧
      finiteLoewnerLe
        (fun j k : Fin n =>
          -(leverageFactoredInputSampleGram U C samples j k -
            rowGram (preconditionColumns U C) j k))
        (fun j k : Fin n => ε * rowGram (preconditionColumns U C) j k)}
  let Good : Set (RowTrace m s) := {samples | rowTracePositiveProb U samples}
  let F : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k : Fin n =>
          fl_rowSampleGramDotWithComputedDen fp (preconditionColumns U C)
              dhat.den samples j k -
            leverageFactoredInputSampleGram U C samples j k) ≤ τ}
  let G : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe
        (fun j k : Fin n =>
          fl_rowSampleGramDotWithComputedDen fp (preconditionColumns U C)
              dhat.den samples j k -
            rowGram (preconditionColumns U C) j k)
        (fun j k : Fin n =>
          ε * rowGram (preconditionColumns U C) j k +
            τ * finiteIdMatrix j k) ∧
      finiteLoewnerLe
        (fun j k : Fin n =>
          -(fl_rowSampleGramDotWithComputedDen fp (preconditionColumns U C)
              dhat.den samples j k -
            rowGram (preconditionColumns U C) j k))
        (fun j k : Fin n =>
          ε * rowGram (preconditionColumns U C) j k +
            τ * finiteIdMatrix j k)}
  have hE :
      1 - δ ≤ P.eventProb Eexact := by
    simpa [P, Eexact] using
      leverageTraceProbability_eventProb_factoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
        (s := s) (ε := ε) (δ := δ) U C hU hr hrVar hs hε hδ
        hbudgetUpper hbudgetLower
  have hGoodProb : P.eventProb Good = 1 := by
    let hden : 0 < rowSqNormProbDen U :=
      rowSqNormProbDen_pos_of_orthonormal_columns U hU hr
    simpa [P, Good, leverageTraceProbability] using
      rowSqNormTraceProbability_eventProb_rowTracePositiveProb
        (steps := s) U hden
  have hGood_subset_F : Good ⊆ F := by
    intro samples hgood
    have hgood_pos : rowTracePositiveProb U samples := by
      simpa [Good] using hgood
    simpa [F, τ] using
      leverage_fl_rowSampleGramDotWithComputedDen_factoredInput_perturb_bound
        fp U C hs hγ dhat samples hgood_pos
  have hF : 1 - (0 : ℝ) ≤ P.eventProb F := by
    have hmono : P.eventProb Good ≤ P.eventProb F :=
      FiniteProbability.eventProb_mono P hGood_subset_F
    linarith
  have hEF :
      1 - (δ + 0) ≤ P.eventProb (Eexact ∩ F) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add P Eexact F δ 0 hE hF
  have hsubset : Eexact ∩ F ⊆ G := by
    intro samples hsamples
    rcases hsamples with ⟨hexact, hpert⟩
    rcases hexact with ⟨hExactUpper, hExactLower⟩
    let Exact : Fin n → Fin n → ℝ :=
      fun j k =>
        leverageFactoredInputSampleGram U C samples j k -
          rowGram (preconditionColumns U C) j k
    let Delta : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_rowSampleGramDotWithComputedDen fp (preconditionColumns U C)
            dhat.den samples j k -
          leverageFactoredInputSampleGram U C samples j k
    let Eps : Fin n → Fin n → ℝ :=
      fun j k => ε * rowGram (preconditionColumns U C) j k
    have htwo :=
      leverage_finiteLoewnerLe_two_sided_add_general_of_frobNorm_le
        Exact Delta Eps hExactUpper (by simpa [Exact] using hExactLower)
        (by simpa [F, Delta, τ] using hpert)
    rcases htwo with ⟨hUpper, hLower⟩
    have hCompEq :
        (fun j k : Fin n =>
          fl_rowSampleGramDotWithComputedDen fp (preconditionColumns U C)
              dhat.den samples j k -
            rowGram (preconditionColumns U C) j k) =
        fun j k : Fin n => Exact j k + Delta j k := by
      ext j k
      dsimp [Exact, Delta]
      ring
    have hNegCompEq :
        (fun j k : Fin n =>
          -(fl_rowSampleGramDotWithComputedDen fp (preconditionColumns U C)
              dhat.den samples j k -
            rowGram (preconditionColumns U C) j k)) =
        fun j k : Fin n => -(Exact j k + Delta j k) := by
      ext j k
      dsimp [Exact, Delta]
      ring
    have hUpperComp :
        finiteLoewnerLe
          (fun j k : Fin n =>
            fl_rowSampleGramDotWithComputedDen fp (preconditionColumns U C)
                dhat.den samples j k -
              rowGram (preconditionColumns U C) j k)
          (fun j k : Fin n =>
            ε * rowGram (preconditionColumns U C) j k +
              τ * finiteIdMatrix j k) := by
      rw [hCompEq]
      simpa [Eps] using hUpper
    have hLowerComp :
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(fl_rowSampleGramDotWithComputedDen fp (preconditionColumns U C)
                dhat.den samples j k -
              rowGram (preconditionColumns U C) j k))
          (fun j k : Fin n =>
            ε * rowGram (preconditionColumns U C) j k +
              τ * finiteIdMatrix j k) := by
      rw [hNegCompEq]
      simpa [Eps] using hLower
    exact ⟨hUpperComp, hLowerComp⟩
  have hG := hEF.trans (FiniteProbability.eventProb_mono P hsubset)
  simpa [P, Eexact, F, G, τ] using hG

/-- Fully concrete floating-point Algorithm 2 equation (7) for an actual input
matrix factored as `A = U C`.

The implementation samples from the exact leverage law defined by `U`, computes
the actual input sketch using rows of `A = U C`, forms the concrete denominator
`dhat_i = fl_sqrt (fl_mul s p_i)`, rounds the sampled-row divisions, and
computes the sampled Gram with floating-point dot products. -/
theorem leverageTraceProbability_eventProb_factoredInput_fl_rowSampleGramDotWithFlMulThenSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
    (fp : FPModel) {m r n s : ℕ} {ε δ : ℝ}
    (U : Fin m → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hr : 0 < r)
    (hrVar : 0 < (r : ℝ) - 1)
    (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 * (r : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((r : ℝ) - 1) + (2 / 3 : ℝ) * (r : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 * (r : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((r : ℝ) - 1) + (2 / 3 : ℝ) * ε))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s) U hU hr).eventProb
        {samples |
          finiteLoewnerLe
            (fun j k : Fin n =>
              fl_rowSampleGramDotWithComputedDen fp (preconditionColumns U C)
                  (leverageFlMulThenSqrtRowScaleDen fp U hU hr hs hγ).den
                  samples j k -
                rowGram (preconditionColumns U C) j k)
            (fun j k : Fin n =>
              ε * rowGram (preconditionColumns U C) j k +
                leverageFactoredInputDenGramBudget fp U C
                  (leverageFlMulThenSqrtRowScaleDen fp U hU hr hs hγ) *
                  finiteIdMatrix j k) ∧
          finiteLoewnerLe
            (fun j k : Fin n =>
              -(fl_rowSampleGramDotWithComputedDen fp (preconditionColumns U C)
                  (leverageFlMulThenSqrtRowScaleDen fp U hU hr hs hγ).den
                  samples j k -
                rowGram (preconditionColumns U C) j k))
            (fun j k : Fin n =>
              ε * rowGram (preconditionColumns U C) j k +
                leverageFactoredInputDenGramBudget fp U C
                  (leverageFlMulThenSqrtRowScaleDen fp U hU hr hs hγ) *
                  finiteIdMatrix j k)} := by
  exact
    leverageTraceProbability_eventProb_factoredInput_fl_rowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
      fp U C hU hr hrVar hs hγ
      (leverageFlMulThenSqrtRowScaleDen fp U hU hr hs hγ)
      hε hδ hbudgetUpper hbudgetLower

/-- Concrete Algorithm 2 computed-basis endpoint for a stored basis table
realized by rounded `fl_mul U_ij 1` copies. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleGramDotWithStoredBasisMulOneAndFlMulThenSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
    (fp : FPModel) {m n s : ℕ} {ε δ : ℝ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n)
    (hnVar : 0 < (n : ℝ) - 1)
    (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 * (n : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((n : ℝ) - 1) + (2 / 3 : ℝ) * (n : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 * (n : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((n : ℝ) - 1) + (2 / 3 : ℝ) * ε))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s) U hU hn).eventProb
        {samples |
          finiteLoewnerLe
            (fun j k : Fin n =>
              fl_rowSampleGramDotWithComputedDen fp
                  (ComputedMatrix.flMulOne fp U).matrix
                  (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ).den
                  samples j k -
                finiteIdMatrix j k)
            (fun j k : Fin n =>
              (ε + leverageComputedBasisDenGramBudget fp U
                (ComputedMatrix.flMulOne fp U)
                (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ)) *
                finiteIdMatrix j k) ∧
          finiteLoewnerLe
            (fun j k : Fin n =>
              -(fl_rowSampleGramDotWithComputedDen fp
                  (ComputedMatrix.flMulOne fp U).matrix
                  (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ).den
                  samples j k -
                finiteIdMatrix j k))
            (fun j k : Fin n =>
              (ε + leverageComputedBasisDenGramBudget fp U
                (ComputedMatrix.flMulOne fp U)
                (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ)) *
                finiteIdMatrix j k)} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleGramDotWithComputedBasisDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
      fp U hU hn hnVar hs hγ (ComputedMatrix.flMulOne fp U)
      (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ)
      hε hδ hbudgetUpper hbudgetLower

/-- Concrete Algorithm 2 computed-basis endpoint for a stored basis table
realized by rounded `fl_add U_ij 0` copies. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleGramDotWithStoredBasisAddZeroRightAndFlMulThenSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
    (fp : FPModel) {m n s : ℕ} {ε δ : ℝ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n)
    (hnVar : 0 < (n : ℝ) - 1)
    (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 * (n : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((n : ℝ) - 1) + (2 / 3 : ℝ) * (n : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 * (n : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((n : ℝ) - 1) + (2 / 3 : ℝ) * ε))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s) U hU hn).eventProb
        {samples |
          finiteLoewnerLe
            (fun j k : Fin n =>
              fl_rowSampleGramDotWithComputedDen fp
                  (ComputedMatrix.flAddZeroRight fp U).matrix
                  (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ).den
                  samples j k -
                finiteIdMatrix j k)
            (fun j k : Fin n =>
              (ε + leverageComputedBasisDenGramBudget fp U
                (ComputedMatrix.flAddZeroRight fp U)
                (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ)) *
                finiteIdMatrix j k) ∧
          finiteLoewnerLe
            (fun j k : Fin n =>
              -(fl_rowSampleGramDotWithComputedDen fp
                  (ComputedMatrix.flAddZeroRight fp U).matrix
                  (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ).den
                  samples j k -
                finiteIdMatrix j k))
            (fun j k : Fin n =>
              (ε + leverageComputedBasisDenGramBudget fp U
                (ComputedMatrix.flAddZeroRight fp U)
                (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ)) *
                finiteIdMatrix j k)} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleGramDotWithComputedBasisDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
      fp U hU hn hnVar hs hγ (ComputedMatrix.flAddZeroRight fp U)
      (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ)
      hε hδ hbudgetUpper hbudgetLower

/-- Concrete Algorithm 2 computed-basis endpoint for a stored basis table
realized by rounded `fl_sub U_ij 0` copies. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleGramDotWithStoredBasisSubZeroRightAndFlMulThenSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
    (fp : FPModel) {m n s : ℕ} {ε δ : ℝ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n)
    (hnVar : 0 < (n : ℝ) - 1)
    (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 * (n : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((n : ℝ) - 1) + (2 / 3 : ℝ) * (n : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 * (n : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((n : ℝ) - 1) + (2 / 3 : ℝ) * ε))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s) U hU hn).eventProb
        {samples |
          finiteLoewnerLe
            (fun j k : Fin n =>
              fl_rowSampleGramDotWithComputedDen fp
                  (ComputedMatrix.flSubZeroRight fp U).matrix
                  (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ).den
                  samples j k -
                finiteIdMatrix j k)
            (fun j k : Fin n =>
              (ε + leverageComputedBasisDenGramBudget fp U
                (ComputedMatrix.flSubZeroRight fp U)
                (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ)) *
                finiteIdMatrix j k) ∧
          finiteLoewnerLe
            (fun j k : Fin n =>
              -(fl_rowSampleGramDotWithComputedDen fp
                  (ComputedMatrix.flSubZeroRight fp U).matrix
                  (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ).den
                  samples j k -
                finiteIdMatrix j k))
            (fun j k : Fin n =>
              (ε + leverageComputedBasisDenGramBudget fp U
                (ComputedMatrix.flSubZeroRight fp U)
                (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ)) *
                finiteIdMatrix j k)} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleGramDotWithComputedBasisDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
      fp U hU hn hnVar hs hγ (ComputedMatrix.flSubZeroRight fp U)
      (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ)
      hε hδ hbudgetUpper hbudgetLower

end NumStability
