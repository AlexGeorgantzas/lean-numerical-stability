import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation05.GramApproximation.SampledGramEndpoints
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation06.LeverageProbability.Normalization
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation07.SubspaceEmbedding.Leverage

/-!
Relocated from the historical wave owners NumStability.Algorithms.RandNLA.RowSamplingLeverage under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

namespace NumStability

open scoped BigOperators

/-!
## Algorithm 2 with leverage-score probabilities

Equation (6) in Drineas--Mahoney defines the row-sampling probabilities by
applying the norm-squared row distribution to an orthonormal-column matrix
`U` spanning the column space of `A`:

`p_i = ||U_i*||_2^2 / ∑_r ||U_r*||_2^2 = ||U_i*||_2^2 / n`.

This file keeps Algorithm 2's sampled sketch and Gram-matrix machinery from
`RowSampling.lean` and `RowSamplingGram.lean`, specializing it to such `U`.
The equation (7) result is stated in vector-action form,
`||Mx||₂ ≤ c ||x||₂` for all `x`, which is the operator-2-norm inequality
without introducing a separate supremum-valued spectral norm.
-/

-- ============================================================
-- Leverage-score probabilities: equation (6)
-- ============================================================





















































































































































































































-- ============================================================
-- One-step rank-one facts for source-sharp equation (7) concentration
-- ============================================================















































































-- ============================================================
-- Equation (7): exact arithmetic
-- ============================================================

/-- Exact equation (7), stated as an operator-2-norm bound in vector-action
    form. The proof reuses the equation (5) Frobenius high-probability theorem
    for norm-squared row sampling, applied to the orthonormal-column matrix
    `U`, and then uses `||M||₂ ≤ ||M||_F`.

The event says that the exact sampled sketch satisfies
`||(ŨᵀŨ - I)x||₂ ≤ ε ||x||₂` for every vector `x`. -/
theorem leverageTraceProbability_eventProb_rowSampleGram_opNorm2_error_le_epsilon
    {m n : ℕ} {s : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n)
    (hs : 0 < (s : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    1 - 1 / ((s : ℝ) * (ε / (n : ℝ)) ^ 2) ≤
      (leverageTraceProbability (steps := s) U hU hn).eventProb
        {samples |
          opNorm2Le
            (fun j k => rowSampleGram s U samples j k - idMatrix n j k)
            ε} := by
  classical
  let hden : 0 < rowSqNormProbDen U :=
    rowSqNormProbDen_pos_of_orthonormal_columns U hU hn
  let η : ℝ := ε / (n : ℝ)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hη : 0 < η := div_pos hε (by exact_mod_cast hn)
  have hden_eq : rowSqNormProbDen U = (n : ℝ) :=
    rowSqNormProbDen_eq_nat_of_orthonormal_columns U hU
  have hgram : rowGram U = idMatrix n :=
    rowGram_eq_id_of_orthonormal_columns U hU
  have hscale : η * rowSqNormProbDen U = ε := by
    simp [η, hden_eq, hnR]
  let P := leverageTraceProbability (steps := s) U hU hn
  let E : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k => rowSampleGram s U samples j k - rowGram U j k) ≤
          η * rowSqNormProbDen U}
  let F : Set (RowTrace m s) :=
    {samples |
      opNorm2Le
        (fun j k => rowSampleGram s U samples j k - idMatrix n j k) ε}
  have hbase :
      1 - 1 / ((s : ℝ) * η ^ 2) ≤
        P.eventProb E := by
    simpa [P, E, leverageTraceProbability] using
      rowSqNormTraceProbability_eventProb_rowSampleGram_frob_error_le_epsilon
        (A := U) hden hs η hη
  have hsubset : E ⊆ F := by
    intro samples hsamples
    have hsamples' :
        frobNorm
          (fun j k => rowSampleGram s U samples j k - rowGram U j k) ≤
            η * rowSqNormProbDen U := by
      simpa [E] using hsamples
    have hFrob :
        frobNorm
          (fun j k => rowSampleGram s U samples j k - idMatrix n j k) ≤
            ε := by
      simpa [hgram, hscale] using hsamples'
    exact opNorm2Le_of_frobNorm_le
      (fun j k => rowSampleGram s U samples j k - idMatrix n j k) hFrob
  exact hbase.trans (FiniteProbability.eventProb_mono P hsubset)

-- ============================================================
-- Floating-point leverage-score stability and equation (7)
-- ============================================================















































/-- Fully floating-point equation (7), in vector-action operator-2 form.

With the same probability as the exact equation (7) Frobenius argument, the
computed Gram matrix formed by rounded row scaling and the library's
floating-point dot product satisfies

`||(fl(ŨᵀŨ) - I)x||₂ ≤ (ε + τ_full) ||x||₂`

for every vector `x`, where
`τ_full = rowSampleGramFullFpPerturbBudget fp s U`. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleGramDot_opNorm2_error_le_epsilon_add_budget
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (hn : 0 < n) (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    {ε : ℝ} (hε : 0 < ε) :
    1 - 1 / ((s : ℝ) * (ε / (n : ℝ)) ^ 2) ≤
      (leverageTraceProbability (steps := s) U hU hn).eventProb
        {samples |
          opNorm2Le
            (fun j k => fl_rowSampleGramDot fp s U samples j k -
              idMatrix n j k)
            (ε + rowSampleGramFullFpPerturbBudget fp s U)} := by
  classical
  let hden : 0 < rowSqNormProbDen U :=
    rowSqNormProbDen_pos_of_orthonormal_columns U hU hn
  let η : ℝ := ε / (n : ℝ)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hη : 0 < η := div_pos hε (by exact_mod_cast hn)
  have hden_eq : rowSqNormProbDen U = (n : ℝ) :=
    rowSqNormProbDen_eq_nat_of_orthonormal_columns U hU
  have hgram : rowGram U = idMatrix n :=
    rowGram_eq_id_of_orthonormal_columns U hU
  have hscale :
      η * rowSqNormProbDen U +
          rowSampleGramFullFpPerturbBudget fp s U =
        ε + rowSampleGramFullFpPerturbBudget fp s U := by
    simp [η, hden_eq, hnR]
  let P := leverageTraceProbability (steps := s) U hU hn
  let E : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k => fl_rowSampleGramDot fp s U samples j k -
          rowGram U j k) ≤
        η * rowSqNormProbDen U +
          rowSampleGramFullFpPerturbBudget fp s U}
  let F : Set (RowTrace m s) :=
    {samples |
      opNorm2Le
        (fun j k => fl_rowSampleGramDot fp s U samples j k -
          idMatrix n j k)
        (ε + rowSampleGramFullFpPerturbBudget fp s U)}
  have hbase :
      1 - 1 / ((s : ℝ) * η ^ 2) ≤
        P.eventProb E := by
    simpa [P, E, leverageTraceProbability] using
      rowSqNormTraceProbability_eventProb_fl_rowSampleGramDot_frob_error_le_epsilon_add_explicit_budget
        fp (A := U) hden hs hγ η hη
  have hsubset : E ⊆ F := by
    intro samples hsamples
    have hsamples' :
        frobNorm
          (fun j k => fl_rowSampleGramDot fp s U samples j k -
            rowGram U j k) ≤
          η * rowSqNormProbDen U +
            rowSampleGramFullFpPerturbBudget fp s U := by
      simpa [E] using hsamples
    have hFrob :
        frobNorm
          (fun j k => fl_rowSampleGramDot fp s U samples j k -
            idMatrix n j k) ≤
          ε + rowSampleGramFullFpPerturbBudget fp s U := by
      simpa [hgram, hscale] using hsamples'
    exact opNorm2Le_of_frobNorm_le
      (fun j k => fl_rowSampleGramDot fp s U samples j k - idMatrix n j k)
      hFrob
  exact hbase.trans (FiniteProbability.eventProb_mono P hsubset)

end NumStability
