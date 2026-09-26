import Mathlib.Analysis.InnerProductSpace.PiL2
import NumStability.Algorithms.LinearSystems.Cholesky.Factorization.Spec
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations
import NumStability.Algorithms.LinearSystems.LeastSquares.StoredQR
import NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication
import NumStability.Algorithms.LinearSystems.QR.Householder.StoredQR
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.DiagonalDominance
import NumStability.Algorithms.LinearSystems.Triangular.InverseBounds
import NumStability.Algorithms.RandomizedLinearAlgebra.LeastSquaresSketching.Objectives.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.LeastSquaresSketching.RowSampling.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.LeverageScore.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.RowNorm.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.RowNorm.Gram
import NumStability.Analysis.FiniteProbability
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.BackwardError
import NumStability.Analysis.Perturbation.LeastSquares.Basic
import NumStability.Analysis.Perturbation.LeastSquares.NormalEquations
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm02.RowSampling.Endpoints
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation07.SubspaceEmbedding.Leverage
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation07.SubspaceEmbedding.LeverageTraceMGF
import NumStability.Source.Higham.Chapter20.Theorem03.QRSolve

/-!
# NumStability.Source.DrineasMahoney.RandNLA2016.Equation08.LeastSquaresSketch.Endpoints

W11 canonical source correspondence destination. Whole commands are copied unchanged from `NumStability.Algorithms.RandNLA.LeastSquaresSketch`; the historical path re-exports this module.
-/

-- Algorithms/RandNLA/LeastSquaresSketch.lean
--
-- Deterministic least-squares consequences of a sketching/subspace-embedding
-- hypothesis, motivated by CACM RandNLA equation (8).
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602














namespace NumStability

open scoped BigOperators

/-!
## Least-squares sketch objective

Equation (8) in the CACM RandNLA survey is the least-squares problem

`x_opt = argmin_x ||A x - b||₂`.

This file formalizes the deterministic implication used by RandNLA
least-squares algorithms: if a sketch preserves the squared residual objective
for every `x`, then an exact minimizer of the sketched problem is a relative
residual-objective approximation for the original problem.

It does not prove that a particular random sampling or random projection
constructs such a sketch with high probability.  That remains a separate
subspace-embedding/concentration obligation.
-/
















































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Source-aligned Bennett sample-budget version of the augmented-span
    row-sampled least-squares objective theorem.

This composes the sharper finite-Loewner equation (7) theorem with the
least-squares objective bridge.  The dimension in the Bennett budget is the
finite rank of `span{columns(A), b}`. -/
theorem leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget
    {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ))
    (xHat : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1)
    (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hfactor : (1 + ε) / (1 - ε) ≤ 1 + η)
    (hhat :
      ∀ samples,
        IsLeastSquaresMinimizer
          (rowSampleLSMatrixWithBasisScale s
            (augmentedSpanBasisMatrix A b) A samples)
          (rowSampleLSVectorWithBasisScale s
            (augmentedSpanBasisMatrix A b) b samples)
          (xHat samples)) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  classical
  let d := Module.finrank ℝ (augmentedDataSpan A b)
  let U := augmentedSpanBasisMatrix A b
  let P := leverageTraceProbability (steps := s) U
    (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
    (Nat.zero_lt_of_lt hd)
  let E : RowTrace m s → Fin d → Fin d → ℝ :=
    fun samples j k => rowSampleGram s U samples j k - idMatrix d j k
  have hdVar : 0 < (d : ℝ) - 1 := by
    have hdReal : (1 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  have hprob :
      1 - δ ≤ P.eventProb
        {samples |
          finiteLoewnerLe (E samples)
            (fun j k : Fin d => ε * finiteIdMatrix j k) ∧
          finiteLoewnerLe (fun j k : Fin d => -E samples j k)
            (fun j k : Fin d => ε * finiteIdMatrix j k)} := by
    simpa [P, E, U, d, idMatrix, finiteIdMatrix] using
      leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
        (s := s) (ε := ε) (δ := δ) U
        (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
        (Nat.zero_lt_of_lt hd) hdVar hs hε_pos hδ
        hbudgetUpper hbudgetLower
  have hmain :=
    eventProb_lsObjective_le_one_add_eta_of_coordinate_finiteLoewner_error
      P A b
      (fun samples => rowSampleLSMatrixWithBasisScale s U A samples)
      (fun samples => rowSampleLSVectorWithBasisScale s U b samples)
      (residualCoordinates A b U) E xHat xOpt
      hprob hε hfactor hhat
      (fun x =>
        lsObjective_eq_vecNorm2Sq_residualCoordinates_of_residualsInColumnSpace
          A b U (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (residualsInColumnSpace_augmentedSpanBasisMatrix A b) x)
      (fun samples x =>
        rowSampleLSObjectiveWithBasisScale_eq_coordinate_quadratic_error
          s A b U samples (residualCoordinates A b U)
          (fun x i => residualsInColumnSpace_augmentedSpanBasisMatrix A b x i)
          x)
  simpa [P, U, d] using hmain




























































































































































/-- Source-aligned Bennett sample-budget version of the floating-point
    augmented-span least-squares objective theorem.

The exact sampling event is the sharper finite-Loewner equation (7) theorem;
the floating-point event adds the rounded row-scaling/dot-product Gram budget
to the preservation radius before applying the least-squares bridge. -/
theorem leverageTraceProbability_eventProb_fl_lsObjective_le_one_add_eta_of_augmentedSpan_sample_budget
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (SA : RowTrace m s → Fin s → Fin n → ℝ)
    (Sb : RowTrace m s → Fin s → ℝ)
    (xHat : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hradius :
      ε + rowSampleGramFullFpPerturbBudget fp s
          (augmentedSpanBasisMatrix A b) < 1)
    (hfactor :
      (1 + (ε + rowSampleGramFullFpPerturbBudget fp s
          (augmentedSpanBasisMatrix A b))) /
          (1 - (ε + rowSampleGramFullFpPerturbBudget fp s
            (augmentedSpanBasisMatrix A b))) ≤
        1 + η)
    (hhat :
      ∀ samples, IsLeastSquaresMinimizer (SA samples) (Sb samples)
        (xHat samples))
    (hsketch : ∀ samples x,
      lsObjective (SA samples) (Sb samples) x =
        vecNorm2Sq
          (residualCoordinates A b (augmentedSpanBasisMatrix A b) x) +
          ∑ j : Fin (Module.finrank ℝ (augmentedDataSpan A b)),
            residualCoordinates A b (augmentedSpanBasisMatrix A b) x j *
              matMulVec (Module.finrank ℝ (augmentedDataSpan A b))
                (fun j k =>
                  fl_rowSampleGramDot fp s
                    (augmentedSpanBasisMatrix A b) samples j k -
                    idMatrix (Module.finrank ℝ (augmentedDataSpan A b)) j k)
                (residualCoordinates A b
                  (augmentedSpanBasisMatrix A b) x) j) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  classical
  let d := Module.finrank ℝ (augmentedDataSpan A b)
  let U := augmentedSpanBasisMatrix A b
  let P := leverageTraceProbability (steps := s) U
    (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
    (Nat.zero_lt_of_lt hd)
  let radius : ℝ := ε + rowSampleGramFullFpPerturbBudget fp s U
  let E : RowTrace m s → Fin d → Fin d → ℝ :=
    fun samples j k =>
      fl_rowSampleGramDot fp s U samples j k - idMatrix d j k
  have hdVar : 0 < (d : ℝ) - 1 := by
    have hdReal : (1 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  have hprob :
      1 - δ ≤ P.eventProb
        {samples |
          finiteLoewnerLe (E samples)
            (fun j k : Fin d => radius * finiteIdMatrix j k) ∧
          finiteLoewnerLe (fun j k : Fin d => -E samples j k)
            (fun j k : Fin d => radius * finiteIdMatrix j k)} := by
    simpa [P, E, U, d, radius, idMatrix, finiteIdMatrix] using
      leverageTraceProbability_eventProb_fl_rowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
        fp (s := s) (ε := ε) (δ := δ) U
        (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
        (Nat.zero_lt_of_lt hd) hdVar hs hγ hε_pos hδ
        hbudgetUpper hbudgetLower
  have hmain :=
    eventProb_lsObjective_le_one_add_eta_of_coordinate_finiteLoewner_error
      P A b SA Sb (residualCoordinates A b U) E xHat xOpt
      hprob (by simpa [radius, U] using hradius)
      (by simpa [radius, U] using hfactor) hhat
      (fun x =>
        lsObjective_eq_vecNorm2Sq_residualCoordinates_of_residualsInColumnSpace
          A b U (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (residualsInColumnSpace_augmentedSpanBasisMatrix A b) x)
      (by simpa [E, U, d] using hsketch)
  simpa [P, U, d] using hmain

/-- Source-aligned Bennett sample-budget theorem for the literal rounded
    sampled/scaled least-squares construction.

This is the high-probability composition for the concrete rounded `A,b` sketch.
It reuses the exact finite-Loewner equation (7) concentration theorem and the
literal rounded objective perturbation theorem.  The remaining floating-point
size requirement is exposed as `hobjectiveBudget`: the sum of the explicit
rounded-objective budgets at the rounded minimizer and at `xOpt` must fit in
the slack between the exact sketch factor and the requested `1 + η` factor. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ))
    (xHat : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hhat :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xHat samples)) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  classical
  let d := Module.finrank ℝ (augmentedDataSpan A b)
  let U := augmentedSpanBasisMatrix A b
  let P := leverageTraceProbability (steps := s) U
    (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
    (Nat.zero_lt_of_lt hd)
  let Good : Set (RowTrace m s) := {samples | rowTracePositiveProb U samples}
  let E : RowTrace m s → Fin d → Fin d → ℝ :=
    fun samples j k => rowSampleGram s U samples j k - idMatrix d j k
  let Exact : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe (E samples)
        (fun j k : Fin d => ε * finiteIdMatrix j k) ∧
      finiteLoewnerLe (fun j k : Fin d => -E samples j k)
        (fun j k : Fin d => ε * finiteIdMatrix j k)}
  let Target : Set (RowTrace m s) :=
    {samples |
      samples ∈ Good ∧
      (finiteLoewnerLe (E samples)
          (fun j k : Fin d => ε * finiteIdMatrix j k) ∧
        finiteLoewnerLe (fun j k : Fin d => -E samples j k)
          (fun j k : Fin d => ε * finiteIdMatrix j k)) ∧
      rowSampleLSObjectiveFpBudget fp s A b U samples (xHat samples) +
        rowSampleLSObjectiveFpBudget fp s A b U samples xOpt ≤
          ((1 + η) * (1 - ε) - (1 + ε)) *
            lsObjective A b xOpt}
  have hdVar : 0 < (d : ℝ) - 1 := by
    have hdReal : (1 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  have hExact :
      1 - δ ≤ P.eventProb Exact := by
    simpa [P, Exact, E, U, d, idMatrix, finiteIdMatrix] using
      leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
        (s := s) (ε := ε) (δ := δ) U
        (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
        (Nat.zero_lt_of_lt hd) hdVar hs hε_pos hδ
        hbudgetUpper hbudgetLower
  have hGoodProb : P.eventProb Good = 1 := by
    let hden : 0 < rowSqNormProbDen U :=
      rowSqNormProbDen_pos_of_orthonormal_columns U
        (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
        (Nat.zero_lt_of_lt hd)
    simpa [P, Good, leverageTraceProbability, U] using
      rowSqNormTraceProbability_eventProb_rowTracePositiveProb
        (steps := s) U hden
  have hGoodLower : 1 - (0 : ℝ) ≤ P.eventProb Good := by
    linarith
  have hinter :
      1 - (δ + 0) ≤ P.eventProb (Exact ∩ Good) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      P Exact Good δ 0 hExact hGoodLower
  have hTargetProb : 1 - δ ≤ P.eventProb Target := by
    have hsubset : Exact ∩ Good ⊆ Target := by
      intro samples hsamples
      rcases hsamples with ⟨hexact, hgood⟩
      have hgood' : rowTracePositiveProb U samples := by
        simpa [Good] using hgood
      exact ⟨hgood, hexact, by
        simpa [Target, U] using hobjectiveBudget samples hgood'⟩
    have hmono := FiniteProbability.eventProb_mono P hsubset
    have hδsum : δ + 0 = δ := by ring
    nlinarith
  have hmain :=
    eventProb_lsObjective_le_one_add_eta_of_coordinate_finiteLoewner_error_with_objective_error_on_event
      P Good A b
      (fun samples => rowSampleLSMatrixWithBasisScale s U A samples)
      (fun samples => fl_rowSampleLSMatrixWithBasisScale fp s U A samples)
      (fun samples => rowSampleLSVectorWithBasisScale s U b samples)
      (fun samples => fl_rowSampleLSVectorWithBasisScale fp s U b samples)
      (residualCoordinates A b U) E xHat xOpt
      (fun samples =>
        rowSampleLSObjectiveFpBudget fp s A b U samples (xHat samples))
      (fun samples =>
        rowSampleLSObjectiveFpBudget fp s A b U samples xOpt)
      (ε := ε) (η := η) (α := 1 - δ)
      (by simpa [Target] using hTargetProb)
      hε hhat
      (fun x =>
        lsObjective_eq_vecNorm2Sq_residualCoordinates_of_residualsInColumnSpace
          A b U (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (residualsInColumnSpace_augmentedSpanBasisMatrix A b) x)
      (fun samples x =>
        rowSampleLSObjectiveWithBasisScale_eq_coordinate_quadratic_error
          s A b U samples (residualCoordinates A b U)
          (fun x i => residualsInColumnSpace_augmentedSpanBasisMatrix A b x i)
          x)
      (fun samples hgood =>
        fl_rowSampleLSObjectiveWithBasisScale_error_bound_of_positiveProb_budget
          fp A b U samples (xHat samples) hs
          (by simpa [Good] using hgood))
      (fun samples hgood =>
        fl_rowSampleLSObjectiveWithBasisScale_error_bound_of_positiveProb_budget
          fp A b U samples xOpt hs
          (by simpa [Good] using hgood))
  simpa [P, U, d] using hmain

/-- Source-aligned Bennett sample-budget theorem for the literal rounded
    sampled/scaled least-squares construction with an explicit solver gap.

This is the solver-facing bridge for equation (8).  The vector `xHat samples`
need only be an additive-gap approximate minimizer of the literal rounded
sampled problem.  The theorem keeps that solver gap explicit: it must fit,
together with the two rounded-objective perturbation budgets, inside the same
objective slack.  It does not prove a concrete QR/preconditioner gap bound. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_solver_gap
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ))
    (xHat : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (solverGap : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            solverGap samples ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hhat :
      ∀ samples,
        IsLeastSquaresApproxMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xHat samples) (solverGap samples)) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  classical
  let d := Module.finrank ℝ (augmentedDataSpan A b)
  let U := augmentedSpanBasisMatrix A b
  let P := leverageTraceProbability (steps := s) U
    (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
    (Nat.zero_lt_of_lt hd)
  let Good : Set (RowTrace m s) := {samples | rowTracePositiveProb U samples}
  let E : RowTrace m s → Fin d → Fin d → ℝ :=
    fun samples j k => rowSampleGram s U samples j k - idMatrix d j k
  let Exact : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe (E samples)
        (fun j k : Fin d => ε * finiteIdMatrix j k) ∧
      finiteLoewnerLe (fun j k : Fin d => -E samples j k)
        (fun j k : Fin d => ε * finiteIdMatrix j k)}
  let Target : Set (RowTrace m s) :=
    {samples |
      samples ∈ Good ∧
      (finiteLoewnerLe (E samples)
          (fun j k : Fin d => ε * finiteIdMatrix j k) ∧
        finiteLoewnerLe (fun j k : Fin d => -E samples j k)
          (fun j k : Fin d => ε * finiteIdMatrix j k)) ∧
      rowSampleLSObjectiveFpBudget fp s A b U samples (xHat samples) +
        rowSampleLSObjectiveFpBudget fp s A b U samples xOpt +
        solverGap samples ≤
          ((1 + η) * (1 - ε) - (1 + ε)) *
            lsObjective A b xOpt}
  have hdVar : 0 < (d : ℝ) - 1 := by
    have hdReal : (1 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  have hExact :
      1 - δ ≤ P.eventProb Exact := by
    simpa [P, Exact, E, U, d, idMatrix, finiteIdMatrix] using
      leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
        (s := s) (ε := ε) (δ := δ) U
        (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
        (Nat.zero_lt_of_lt hd) hdVar hs hε_pos hδ
        hbudgetUpper hbudgetLower
  have hGoodProb : P.eventProb Good = 1 := by
    let hden : 0 < rowSqNormProbDen U :=
      rowSqNormProbDen_pos_of_orthonormal_columns U
        (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
        (Nat.zero_lt_of_lt hd)
    simpa [P, Good, leverageTraceProbability, U] using
      rowSqNormTraceProbability_eventProb_rowTracePositiveProb
        (steps := s) U hden
  have hGoodLower : 1 - (0 : ℝ) ≤ P.eventProb Good := by
    linarith
  have hinter :
      1 - (δ + 0) ≤ P.eventProb (Exact ∩ Good) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      P Exact Good δ 0 hExact hGoodLower
  have hTargetProb : 1 - δ ≤ P.eventProb Target := by
    have hsubset : Exact ∩ Good ⊆ Target := by
      intro samples hsamples
      rcases hsamples with ⟨hexact, hgood⟩
      have hgood' : rowTracePositiveProb U samples := by
        simpa [Good] using hgood
      exact ⟨hgood, hexact, by
        simpa [Target, U] using hobjectiveBudget samples hgood'⟩
    have hmono := FiniteProbability.eventProb_mono P hsubset
    have hδsum : δ + 0 = δ := by ring
    nlinarith
  have hmain :=
    eventProb_lsObjective_le_one_add_eta_of_coordinate_finiteLoewner_error_with_objective_error_and_solver_gap_on_event
      P Good A b
      (fun samples => rowSampleLSMatrixWithBasisScale s U A samples)
      (fun samples => fl_rowSampleLSMatrixWithBasisScale fp s U A samples)
      (fun samples => rowSampleLSVectorWithBasisScale s U b samples)
      (fun samples => fl_rowSampleLSVectorWithBasisScale fp s U b samples)
      (residualCoordinates A b U) E xHat xOpt
      (fun samples =>
        rowSampleLSObjectiveFpBudget fp s A b U samples (xHat samples))
      (fun samples =>
        rowSampleLSObjectiveFpBudget fp s A b U samples xOpt)
      solverGap
      (ε := ε) (η := η) (α := 1 - δ)
      (by simpa [Target] using hTargetProb)
      hε hhat
      (fun x =>
        lsObjective_eq_vecNorm2Sq_residualCoordinates_of_residualsInColumnSpace
          A b U (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (residualsInColumnSpace_augmentedSpanBasisMatrix A b) x)
      (fun samples x =>
        rowSampleLSObjectiveWithBasisScale_eq_coordinate_quadratic_error
          s A b U samples (residualCoordinates A b U)
          (fun x i => residualsInColumnSpace_augmentedSpanBasisMatrix A b x i)
          x)
      (fun samples hgood =>
        fl_rowSampleLSObjectiveWithBasisScale_error_bound_of_positiveProb_budget
          fp A b U samples (xHat samples) hs
          (by simpa [Good] using hgood))
      (fun samples hgood =>
        fl_rowSampleLSObjectiveWithBasisScale_error_bound_of_positiveProb_budget
          fp A b U samples xOpt hs
          (by simpa [Good] using hgood))
  simpa [P, U, d] using hmain

/-- Source-aligned Bennett sample-budget theorem for literal rounded
    sampled/scaled least squares with a componentwise solver forward-error
    certificate.

This specializes the solver-gap theorem to the common situation where a solver
returns `xHat samples` together with a componentwise distance certificate
`solverDx samples` from an exact minimizer `xStar samples` of the rounded
sampled problem.  The induced objective gap is explicit and follows from the
local residual/objective perturbation algebra above. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_forward_error
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ))
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (solverDx : RowTrace m s → Fin n → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples) (solverDx samples) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hdx : ∀ samples j, 0 ≤ solverDx samples j)
    (hclose : ∀ samples j,
      |xHat samples j - xStar samples j| ≤ solverDx samples j) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_solver_gap
      fp A b hd hs xHat xOpt
      (fun samples =>
        lsSolutionForwardObjectiveGap
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples) (solverDx samples))
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget ?_
  intro samples
  exact
    isLeastSquaresApproxMinimizer_of_solution_abs_le
      (fl_rowSampleLSMatrixWithBasisScale fp s
        (augmentedSpanBasisMatrix A b) A samples)
      (fl_rowSampleLSVectorWithBasisScale fp s
        (augmentedSpanBasisMatrix A b) b samples)
      (xHat samples) (xStar samples) (solverDx samples)
      (hstar samples) (hdx samples) (hclose samples)

/-- Source-aligned Bennett sample-budget theorem for literal rounded
    sampled/scaled least squares when the downstream solver is certified by a
    perturbed normal-equation system.

The theorem reuses the local Gram-system forward-error theorem to construct
the componentwise `solverDx` certificate consumed by
`..._and_forward_error`.  It still keeps the perturbed-system certificate
explicit; deriving that certificate from a concrete QR factorization,
preconditioner, or iterative solver is a separate downstream theorem. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_perturbed_gram_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ))
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (ΔG : RowTrace m s → Fin n → Fin n → ℝ)
    (Δg : RowTrace m s → Fin n → ℝ)
    (εG εg : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (gramForwardSolverDx (ATA_inv samples) (εG samples)
                (εg samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hPerturbed : ∀ samples i,
      matMulVec n
        (fun j k =>
          lsNormalMatrix
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples) j k +
            ΔG samples j k)
        (xHat samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i +
          Δg samples i)
    (hΔG_bound : ∀ samples i j, |ΔG samples i j| ≤ εG samples)
    (hΔg_bound : ∀ samples i, |Δg samples i| ≤ εg samples)
    (hεG : ∀ samples, 0 ≤ εG samples)
    (hεg : ∀ samples, 0 ≤ εg samples) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_forward_error
      fp A b hd hs xHat xStar xOpt
      (fun samples =>
        gramForwardSolverDx (ATA_inv samples) (εG samples)
          (εg samples) (xHat samples))
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar ?_ ?_
  · intro samples j
    exact
      gramForwardSolverDx_nonneg
        (ATA_inv samples) (εG samples) (εg samples) (xHat samples)
        (hεG samples) (hεg samples) j
  · intro samples j
    exact
      gram_forward_error_certificate_of_perturbed_gram_system
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples) (hInv samples)
        (lsNormalRhs
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples))
        (xStar samples) (xHat samples)
        (hExact samples) (ΔG samples) (Δg samples)
        (hPerturbed samples) (εG samples) (εg samples)
        (hΔG_bound samples) (hΔg_bound samples)
        (hεG samples) (hεg samples) j

/-- Source-aligned Bennett sample-budget theorem for literal rounded
    sampled/scaled least squares when the downstream solver is represented by
    the local `LSQRSolveBackwardError` specification.

This closes the small adapter from the repository's least-squares QR
backward-error vocabulary to the RandNLA objective transfer.  It still does
not prove the QR/preconditioner implementation theorem that would construct
the `LSQRSolveBackwardError` structure for a concrete solver. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_ls_qr_backward_error_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ))
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hBack : ∀ samples,
      LSQRSolveBackwardError n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (lsNormalRhs
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples))
        (xHat samples) (c_G samples) (c_g samples)) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_forward_error
      fp A b hd hs xHat xStar xOpt
      (fun samples =>
        lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
          (c_g samples) (xHat samples))
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar ?_ ?_
  · intro samples j
    have hBackSamples := hBack samples
    rcases hBackSamples.result with ⟨ΔG, _Δg, _hPerturbed, hΔG_frob, _hΔg_bound⟩
    have hcG : 0 ≤ c_G samples := le_trans (frobNorm_nonneg ΔG) hΔG_frob
    exact
      lsQRSolveBackwardSolverDx_nonneg
        (ATA_inv samples) (c_G samples) (c_g samples) (xHat samples)
        hcG j
  · intro samples j
    exact
      gram_forward_error_certificate_of_ls_qr_solve_backward_error
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples) (hInv samples)
        (lsNormalRhs
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples))
        (xStar samples) (xHat samples) (hExact samples)
        (c_G samples) (c_g samples) (hBack samples) j

/-- Source-aligned Bennett sample-budget theorem for literal rounded
    sampled/scaled least squares when the downstream solver is a stored
    Householder QR handoff satisfying the packaged off-diagonal-control
    invariant.

The theorem composes the repository's concrete stored-QR
`LSQRSolveBackwardError` theorem with the RandNLA objective transfer.  The
remaining QR/preconditioner obligation is intentionally visible as the single
route-1 invariant `StoredQROffDiagonalControlInvariant`: a concrete QR route
must prove it from source-specific pivoting, ordering, or off-diagonal-growth
assumptions before this becomes a fully implementation-backed theorem. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hoff : ∀ samples,
      StoredQROffDiagonalControlInvariant hmn fp
        (A_hat samples) (b_hat samples) (alpha samples))
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_ls_qr_backward_error_solver
      fp A b hd hs xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget
      hstar hInv hExact ?_
  intro samples
  have hBack :=
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_offDiagonalControl
      fp hmn
      (fl_rowSampleLSMatrixWithBasisScale fp s
        (augmentedSpanBasisMatrix A b) A samples)
      (fl_rowSampleLSVectorWithBasisScale fp s
        (augmentedSpanBasisMatrix A b) b samples)
      (A_hat samples) (b_hat samples) (alpha samples)
      hm hγ (hInitA samples) (hInitb samples)
      (hStepA samples) (hStepb samples) (hAlphaDef samples)
      (hoff samples)
  simpa [hxHat samples, hcG samples, hcg samples,
    storedQRBackSubSolution, storedQRFinalR, storedQRFinalTopRhs,
    lsNormalMatrix, lsNormalRhs, rectLSGram, rectLSRhs] using hBack

/-- Source-aligned Bennett sample-budget theorem for the route-1 packaged
    off-diagonal-control QR handoff, with the packaged invariant built from
    local diagonal dominance and the canonical finite-max product-smallness
    inequality.

This is the direct equation (8) wrapper for the two visible route-1 fields.  It
does not prove local diagonal dominance or scalar finite-max smallness from the
stored recurrence; it only prevents the packaged invariant from becoming an
extra hidden hypothesis once those two source/domain facts are supplied
samplewise. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver_of_diagDominant_finiteMaxSmallness
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hsmall : ∀ samples,
      2 * storedQRDiagDominantInvFactorBudget hmn (A_hat samples) *
          ((s : ℝ) *
            (storedQRCompactSequenceRelativeBudget hmn fp
              (A_hat samples) (b_hat samples) (alpha samples) *
              storedQRPivotColumnNormBudget hmn (A_hat samples)) ^ 2) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar hInv
      hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef ?_ hxHat hcG hcg
  intro samples
  exact
    StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSmallness
      hmn fp (A_hat samples) (b_hat samples) (alpha samples) hm
      (fun k hk => hDD samples k hk) (hsmall samples)

/-- Source-aligned Bennett sample-budget theorem for the route-1 packaged
    off-diagonal-control QR handoff, with the packaged invariant built from the
    canonical finite-max rational-gamma source-denominator cap route.

This is the probability-level sibling of the solver theorem
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds`.
It keeps the remaining QR arithmetic obligations samplewise and explicit:
local diagonal dominance, source-shaped Householder denominator nonbreakdown,
the unit-roundoff cap, the rational-cap validity condition, and the canonical
scalar finite-max smallness inequality. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    (Ucap : ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hUcap_nonneg : 0 ≤ Ucap)
    (hden : ∀ samples k (hk : k < n),
      (∑ i : Fin s,
        householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k) i *
          householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k) i) ≠ 0)
    (hu : fp.u ≤ Ucap)
    (huCap : (s : ℝ) * Ucap < 1)
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * Ucap) / (1 - (s : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar hInv
      hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef ?_ hxHat hcG hcg
  intro samples
  exact
    StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds
      hmn fp (A_hat samples) (b_hat samples) (alpha samples) Ucap hm
      (fun k hk => hDD samples k hk)
      hUcap_nonneg (hden samples) hu huCap (hsmall samples)

/-- Source-aligned Bennett sample-budget theorem for the canonical
    rational-gamma QR handoff, with source denominator nonbreakdown derived
    from signed-alpha/trailing-norm data.

    This is the probability-level source-nonbreakdown reduction of
    `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`.
    The raw `v^T v != 0` field is replaced by samplewise positive active
    trailing norms; the existing signed-alpha definition supplies the square
    equation and sign condition used by the local Householder nonbreakdown
    theorem. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_trailingNormPos_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    (Ucap : ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hUcap_nonneg : 0 ≤ Ucap)
    (htrailingPos : ∀ samples k (hk : k < n),
      0 < householderTrailingNorm2Sq s
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat samples k a ⟨k, hk⟩))
    (hu : fp.u ≤ Ucap)
    (huCap : (s : ℝ) * Ucap < 1)
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * Ucap) / (1 - (s : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hden : ∀ samples k (hk : k < n),
      (∑ i : Fin s,
        householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k) i *
          householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k) i) ≠ 0 := by
    intro samples k hk
    have halpha :
        alpha samples k * alpha samples k =
          householderTrailingNorm2Sq s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) := by
      rw [hAlphaDef samples k hk]
      exact
        signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq
          s ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat samples k a ⟨k, hk⟩)
    have hsign :
        alpha samples k *
            A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0 := by
      rw [hAlphaDef samples k hk]
      exact
        signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos
          s ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat samples k a ⟨k, hk⟩)
    exact
      householderTrailingActiveVector_inner_self_ne_zero_of_trailingNorm2Sq_pos_mul_nonpos
        s ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)
        halpha (htrailingPos samples k hk) hsign
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      Ucap hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar
      hInv hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef hDD
      hUcap_nonneg hden hu huCap hsmall hxHat hcG hcg

/-- Source-aligned Bennett sample-budget theorem for the canonical
    rational-gamma QR handoff, with source denominator nonbreakdown derived
    from leading-block determinant data.

    This is the probability-level determinant/rank specialization of
    `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_trailingNormPos_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`.
    The samplewise previous/current leading determinant facts and lower-zero
    shape imply positive active trailing norms, which feed the existing
    signed-alpha source-nonbreakdown route. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_leadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    (Ucap : ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hUcap_nonneg : 0 ≤ Ucap)
    (hdetPrev : ∀ samples k (hk : k < n),
      Matrix.det
        (qrPreviousLeadingBlockTranspose (A_hat samples k)
          (le_of_lt (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin k) (Fin k) ℝ) ≠ 0)
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hlowerPrev : ∀ samples k (hk : k < n) (i : Fin s) (j : Fin k),
      k ≤ i.val → A_hat samples k i (qrPreviousColumn n k hk j) = 0)
    (hu : fp.u ≤ Ucap)
    (huCap : (s : ℝ) * Ucap < 1)
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * Ucap) / (1 - (s : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have htrailingPos : ∀ samples k (hk : k < n),
      0 < householderTrailingNorm2Sq s
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat samples k a ⟨k, hk⟩) := by
    intro samples k hk
    exact
      householderTrailingNorm2Sq_pos_of_leading_block_det_ne_zero
        (A_hat samples k) (lt_of_lt_of_le hk hmn) hk
        (hdetPrev samples k hk) (hdetLead samples k hk)
        (hlowerPrev samples k hk)
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_trailingNormPos_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      Ucap hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar
      hInv hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef hDD
      hUcap_nonneg htrailingPos hu huCap hsmall hxHat hcG hcg

/-- Source-aligned Bennett sample-budget theorem for the canonical
    rational-gamma QR handoff, with current leading-block nonsingularity
    derived from local diagonal dominance.

    Compared with
    `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_leadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`,
    this wrapper removes the samplewise current leading-block determinant
    field.  The previous transposed leading-block determinant remains visible,
    while the current one follows from `IsDiagDominantUpper`. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_previousLeadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    (Ucap : ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hUcap_nonneg : 0 ≤ Ucap)
    (hdetPrev : ∀ samples k (hk : k < n),
      Matrix.det
        (qrPreviousLeadingBlockTranspose (A_hat samples k)
          (le_of_lt (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin k) (Fin k) ℝ) ≠ 0)
    (hlowerPrev : ∀ samples k (hk : k < n) (i : Fin s) (j : Fin k),
      k ≤ i.val → A_hat samples k i (qrPreviousColumn n k hk j) = 0)
    (hu : fp.u ≤ Ucap)
    (huCap : (s : ℝ) * Ucap < 1)
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * Ucap) / (1 - (s : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_leadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      Ucap hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar
      hInv hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef hDD
      hUcap_nonneg hdetPrev
      (fun samples k hk =>
        det_ne_zero_of_diagDominantUpper (k + 1)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (hDD samples k hk))
      hlowerPrev hu huCap hsmall hxHat hcG hcg

/-- Source-aligned Bennett sample-budget theorem for the canonical
    rational-gamma QR handoff, with both previous and current local determinant
    fields derived from local diagonal dominance.

Compared with
`..._stored_qr_diagDominant_previousLeadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`,
this wrapper also removes the samplewise previous transposed leading-block
determinant field.  The previous determinant is obtained from the same
samplewise `IsDiagDominantUpper` leading-block hypothesis via the local
top-left-block determinant adapter; the previous lower-zero field remains
visible because it is still needed by the trailing-norm bridge. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_lowerPrev_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    (Ucap : ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hUcap_nonneg : 0 ≤ Ucap)
    (hlowerPrev : ∀ samples k (hk : k < n) (i : Fin s) (j : Fin k),
      k ≤ i.val → A_hat samples k i (qrPreviousColumn n k hk j) = 0)
    (hu : fp.u ≤ Ucap)
    (huCap : (s : ℝ) * Ucap < 1)
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * Ucap) / (1 - (s : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_previousLeadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      Ucap hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar
      hInv hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef hDD
      hUcap_nonneg
      (fun samples k hk =>
        qrPreviousLeadingBlockTranspose_det_ne_zero_of_diagDominant_leadingBlock
          (A_hat samples k) (le_of_lt (lt_of_lt_of_le hk hmn))
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk
          (hDD samples k hk))
      hlowerPrev hu huCap hsmall hxHat hcG hcg

/-- Source-aligned Bennett sample-budget theorem for the canonical
    rational-gamma diagonal-dominant QR route, with the previous-column
    lower-zero shape derived from the stored panel recurrence.

This removes the explicit samplewise `hlowerPrev` field from
`..._stored_qr_diagDominant_lowerPrev_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`.
The only lower-zero information used is the repository theorem that the stored
Householder panel loop preserves completed columns and writes exact zeros below
each pivot. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    (Ucap : ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hUcap_nonneg : 0 ≤ Ucap)
    (hu : fp.u ≤ Ucap)
    (huCap : (s : ℝ) * Ucap < 1)
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * Ucap) / (1 - (s : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hlowerPrev : ∀ samples k (hk : k < n) (i : Fin s) (j : Fin k),
      k ≤ i.val → A_hat samples k i (qrPreviousColumn n k hk j) = 0 := by
    intro samples
    exact
      storedQRPreviousColumnLowerZero_of_stored_trailing_householder_sequence
        fp hmn (A_hat samples) (alpha samples) (hStepA samples)
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_lowerPrev_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      Ucap hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar
      hInv hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef hDD
      hUcap_nonneg hlowerPrev hu huCap hsmall hxHat hcG hcg

/-- Probability wrapper for the stored-lower canonical rational-gamma QR route
    with `0 ≤ Ucap` derived from the unit-roundoff cap.

This removes one proof-artifact hypothesis from the high-probability Algorithm 2
least-squares objective theorem: the FP model gives `0 ≤ fp.u`, so `fp.u ≤ Ucap`
already implies `0 ≤ Ucap`. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_uCap
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    (Ucap : ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hu : fp.u ≤ Ucap)
    (huCap : (s : ℝ) * Ucap < 1)
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * Ucap) / (1 - (s : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hUcap_nonneg : 0 ≤ Ucap := le_trans fp.u_nonneg hu
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      Ucap hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar
      hInv hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef hDD
      hUcap_nonneg hu huCap hsmall hxHat hcG hcg

/-- Probability wrapper for the stored-lower canonical rational-gamma QR route
    with all gamma-validity guards derived from the displayed unit-roundoff cap.

The assumptions `fp.u ≤ Ucap` and `(s : ℝ) * Ucap < 1` imply
`gammaValid fp s`; since the sampled problem has `n ≤ s`, they also imply
`gammaValid fp n`. This removes the remaining redundant floating-point
validity hypotheses from the cap-based high-probability Algorithm 2 surface. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_uCap_no_gammaValid
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    (Ucap : ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hu : fp.u ≤ Ucap)
    (huCap : (s : ℝ) * Ucap < 1)
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * Ucap) / (1 - (s : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hm : gammaValid fp s :=
    gammaValid_of_u_le_cap fp s Ucap hu huCap
  have hγ : gammaValid fp n :=
    gammaValid_mono fp hmn hm
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_uCap
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      Ucap hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar
      hInv hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef hDD hu huCap
      hsmall hxHat hcG hcg

/-- Probability wrapper for the stored-lower canonical rational-gamma QR route
    specialized to the actual unit roundoff of the FP model.

This removes the displayed-cap field `fp.u ≤ Ucap` from the high-probability
Algorithm 2 surface by choosing `Ucap = fp.u`.  The sampled-dimension validity
guard `gammaValid fp s` and the actual-unit scalar smallness condition remain
visible. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_actualUnitRoundoff
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * fp.u) / (1 - (s : ℝ) * fp.u)
      let Fcap :=
        fp.u * (1 + Gcap) * (1 + fp.u) +
          fp.u * (1 + Gcap) +
          Gcap +
          fp.u * (1 + Gcap) * (1 + fp.u) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (fp.u + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have huCap : (s : ℝ) * fp.u < 1 := by
    simpa [gammaValid] using hm
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_uCap_no_gammaValid
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      fp.u hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar
      hInv hExact hInitA hInitb hStepA hStepb hAlphaDef hDD
      (le_rfl : fp.u ≤ fp.u) huCap hsmall hxHat hcG hcg

/-- Source-aligned Bennett sample-budget theorem for the stored-lower canonical
    rational-gamma QR route, specialized to the actual unit roundoff and with the
    operation-validity guard displayed as `(s : ℝ) * fp.u < 1`.

This keeps the real numerical smallness hypothesis visible and removes the
abstract `gammaValid fp s` assumption from the probability-level statement.  The
canonical scalar smallness inequality remains an explicit QR-domain hypothesis. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_actualUnitRoundoff_no_gammaValid
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (huSmall : (s : ℝ) * fp.u < 1)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * fp.u) / (1 - (s : ℝ) * fp.u)
      let Fcap :=
        fp.u * (1 + Gcap) * (1 + fp.u) +
          fp.u * (1 + Gcap) +
          Gcap +
          fp.u * (1 + Gcap) * (1 + fp.u) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (fp.u + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_uCap_no_gammaValid
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      fp.u hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar
      hInv hExact hInitA hInitb hStepA hStepb hAlphaDef hDD
      (le_rfl : fp.u ≤ fp.u) huSmall hsmall hxHat hcG hcg

/-- Source-aligned Bennett sample-budget theorem for the route-1 packaged
    off-diagonal-control QR handoff, with compact-product smallness supplied by
    the canonical finite maximum of the explicit compact Householder norm
    coefficient.

This is the coefficient-max sibling of
`..._offDiagonalControl_solver_of_diagDominant_finiteMaxSmallness`.  It still
does not prove local diagonal dominance or scalar coefficient-max smallness from
the stored recurrence; it only threads the already formalized coefficient-max
product theorem into the probability-level equation (8) surface. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver_of_diagDominant_finiteMaxNormBudgetCoeffSmallness
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hsmall : ∀ samples,
      2 * storedQRDiagDominantInvFactorBudget hmn (A_hat samples) *
          ((s : ℝ) *
            (((n : ℝ) *
                ((n : ℝ) *
                  storedQRCompactStepNormBudgetCoeffBudget hmn fp
                    (A_hat samples) (alpha samples) +
                  storedQRCompactStepNormBudgetCoeffBudget hmn fp
                    (A_hat samples) (alpha samples))) *
              storedQRPivotColumnNormBudget hmn (A_hat samples)) ^ 2) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar hInv
      hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef ?_ hxHat hcG hcg
  intro samples
  exact
    StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxNormBudgetCoeffSmallness
      hmn fp (A_hat samples) (b_hat samples) (alpha samples) hm
      (fun k hk => hDD samples k hk) (hsmall samples)

/-- Source-aligned Bennett sample-budget theorem for literal rounded
    sampled/scaled least squares when the downstream solver is a stored
    Householder QR handoff satisfying the source-shaped off-diagonal-control
    certificate.

The theorem composes the repository's concrete stored-QR
`LSQRSolveBackwardError` theorem with the RandNLA objective transfer.  The
remaining QR/preconditioner obligations are intentionally visible: the stored
loop must supply signed-alpha steps, source off-diagonal control, and the
budget equations identifying the reported solution and radii with the final
back-substitution handoff. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hoff : ∀ samples,
      StoredQRSourceOffDiagonalControl hmn fp
        (A_hat samples) (b_hat samples) (alpha samples))
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar hInv
      hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef
      (fun samples =>
        StoredQROffDiagonalControlInvariant.of_sourceOffDiagonalControl
          hmn fp (A_hat samples) (b_hat samples) (alpha samples)
          (hoff samples))
      hxHat hcG hcg

/-- Source-aligned Bennett sample-budget theorem for the primitive
    off-diagonal-control route.

This is the probability-level companion to
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_offdiag_product`.
The stored recurrence supplies triangular shape, while the caller supplies the
genuine route-1 fields: leading-block nonsingularity, norm-square
nonbreakdown, row-wise off-diagonal domination, and per-pivot compact-product
smallness.  Thus the theorem closes the objective-transfer assembly edge
without hiding the remaining computed-loop invariant obligations. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_leadingBlock_det_ne_zero_normSqBudget_offdiag_product_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq s
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat samples k a ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hoffdiag : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), i.val < j.val →
        |qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i j| ≤
        |qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hproduct : ∀ samples k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((s : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples) *
            vecNorm2 (fun i : Fin s => A_hat samples k i ⟨k, hk⟩)) ^ 2) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar hInv
      hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef
      (fun samples =>
        StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_offdiag_product
          hmn fp (A_hat samples) (b_hat samples) (alpha samples) hm
          (hStepA samples) (hAlphaDef samples) (hbudgetNormSq samples)
          (hdetLead samples) (hoffdiag samples) (hproduct samples))
      hxHat hcG hcg

/-- Source-aligned Bennett sample-budget theorem whose stored-QR solver uses
    the packaged displayed row-budget control certificate.

This is the equation (8) probability-level companion to
`StoredQRDisplayedRowBudgetControl`.  It keeps the Cox--Higham row-growth and
diagonal lower-bound/nonbreakdown fields visible as a single samplewise domain
certificate, then reuses the source-shaped stored-QR objective theorem. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (rowBudget : RowTrace m s → ∀ k, k < n → Fin (k + 1) → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq s
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat samples k a ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hrowControl : ∀ samples,
      StoredQRDisplayedRowBudgetControl hmn (A_hat samples) (rowBudget samples))
    (hproduct : ∀ samples k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((s : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples) *
            vecNorm2 (fun i : Fin s => A_hat samples k i ⟨k, hk⟩)) ^ 2) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar hInv
      hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef
      (fun samples =>
        StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowBudgetControl_product
          hmn fp (A_hat samples) (b_hat samples) (alpha samples)
          (rowBudget samples) hm (hStepA samples) (hAlphaDef samples)
          (hbudgetNormSq samples) (hdetLead samples) (hrowControl samples)
          (hproduct samples))
      hxHat hcG hcg

/-- Source-aligned Bennett sample-budget theorem whose displayed row-budget
    stored-QR solver certificate derives norm-square nonbreakdown from local
    `κ∞`/dual compact-budget data.

This is the row-budget-control companion to
`..._stored_qr_rowBudgetControl_solver`.  It removes the raw samplewise
norm-square nonbreakdown hypothesis by reusing the local leading-block inverse
budget route, while keeping the displayed row-budget control, determinant, and
compact-product hypotheses explicit. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_kappaInf_dualBudget_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K : RowTrace m s → ℕ → ℝ)
    (rowBudget : RowTrace m s → ∀ k, k < n → Fin (k + 1) → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hrowControl : ∀ samples,
      StoredQRDisplayedRowBudgetControl hmn (A_hat samples) (rowBudget samples))
    (hproduct : ∀ samples k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((s : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples) *
            vecNorm2 (fun i : Fin s => A_hat samples k i ⟨k, hk⟩)) ^ 2) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hbudgetNormSq : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq s
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat samples k a ⟨k, hk⟩) := by
    intro samples
    exact
      storedQRSignedStage_normSqBudget_of_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget
        hmn fp (A_hat samples) (alpha samples) (κ samples) (K samples)
        (hStepA samples) (hdetLead samples) (hK samples) (hκ samples)
        (hκbudget samples) (hbudgetDual samples)
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_solver
      fp A b hd hs hmn A_hat b_hat alpha rowBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hbudgetNormSq hdetLead hrowControl hproduct
      hxHat hcG hcg

/-- Source-aligned Bennett sample-budget theorem whose displayed row-budget
    stored-QR solver certificate uses the finite global compact-product budget.

This is the finite-budget version of
`..._rowBudgetControl_kappaInf_dualBudget_solver`: the scalar condition
`storedQRCompactSequenceProductBudget < 1` is converted locally into the
per-pivot compact-product inequalities consumed by the row-budget-control
handoff.  The theorem still keeps the displayed row-budget certificate and the
local `κ∞`/dual compact-budget data visible. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_globalProduct_kappaInf_dualBudget_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K : RowTrace m s → ℕ → ℝ)
    (rowBudget : RowTrace m s → ∀ k, k < n → Fin (k + 1) → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hrowControl : ∀ samples,
      StoredQRDisplayedRowBudgetControl hmn (A_hat samples) (rowBudget samples))
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hproduct : ∀ samples k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((s : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples) *
            vecNorm2 (fun i : Fin s => A_hat samples k i ⟨k, hk⟩)) ^ 2) <
        1 := by
    intro samples k hk
    let kk : Fin n := ⟨k, hk⟩
    have hle :
        storedQRCompactSequenceProductExpr hmn fp
            (A_hat samples) (b_hat samples) (alpha samples) kk ≤
          storedQRCompactSequenceProductBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples) :=
      storedQRCompactSequenceProductExpr_le_budget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) kk
    exact lt_of_le_of_lt (by
      simpa [storedQRCompactSequenceProductExpr, kk] using hle)
      (hglobalProduct samples)
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_kappaInf_dualBudget_solver
      fp A b hd hs hmn A_hat b_hat alpha κ K rowBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hrowControl
      hproduct hxHat hcG hcg

/-- Source-aligned Bennett sample-budget theorem for the scalar row-max defect
    QR route.

This is the probability-level companion to
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowMaxDiagDefect_globalProduct`.
It keeps the scalar samplewise condition
`storedQRRowMaxDiagDefectBudget <= 0` visible and converts it to the packaged
displayed row-budget certificate locally.  The theorem also keeps the
norm-square nonbreakdown, determinant, and finite global compact-product
conditions explicit. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowMaxDiagDefect_globalProduct_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq s
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat samples k a ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hdefect : ∀ samples,
      storedQRRowMaxDiagDefectBudget hmn (A_hat samples) ≤ 0)
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  let rowBudget :
      RowTrace m s → ∀ k, k < n → Fin (k + 1) → ℝ :=
    fun samples k hk i =>
      qrLeadingStrictUpperRowMaxBudget hmn (A_hat samples) k hk i
  have hrowControl : ∀ samples,
      StoredQRDisplayedRowBudgetControl hmn (A_hat samples)
        (rowBudget samples) := by
    intro samples
    exact
      StoredQRDisplayedRowBudgetControl.of_rowMaxDiagDefectBudget_nonpos
        hmn (A_hat samples) (hdefect samples)
  have hproduct : ∀ samples k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((s : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples) *
            vecNorm2 (fun i : Fin s => A_hat samples k i ⟨k, hk⟩)) ^ 2) <
        1 := by
    intro samples k hk
    let kk : Fin n := ⟨k, hk⟩
    have hle :
        storedQRCompactSequenceProductExpr hmn fp
            (A_hat samples) (b_hat samples) (alpha samples) kk ≤
          storedQRCompactSequenceProductBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples) :=
      storedQRCompactSequenceProductExpr_le_budget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) kk
    exact lt_of_le_of_lt (by
      simpa [storedQRCompactSequenceProductExpr, kk] using hle)
      (hglobalProduct samples)
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_solver
      fp A b hd hs hmn A_hat b_hat alpha rowBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hbudgetNormSq hdetLead hrowControl hproduct
      hxHat hcG hcg

/-- Source-aligned Bennett sample-budget theorem for the scalar row-max defect
    QR route with gamma-validity derived from actual unit roundoff.

This is the actual-unit-roundoff sibling of
`..._rowMaxDiagDefect_globalProduct_solver`: the sampled-dimension scalar guard
`(s : ℝ) * fp.u < 1` supplies both `gammaValid fp s` and, since `n ≤ s`,
`gammaValid fp n`.  The scalar row-defect, determinant, norm-square
nonbreakdown, and global compact-product hypotheses remain visible. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowMaxDiagDefect_globalProduct_solver_of_actualUnitRoundoff_no_gammaValid
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (huSmall : (s : ℝ) * fp.u < 1)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq s
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat samples k a ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hdefect : ∀ samples,
      storedQRRowMaxDiagDefectBudget hmn (A_hat samples) ≤ 0)
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hm : gammaValid fp s :=
    gammaValid_of_u_le_cap fp s fp.u (le_rfl : fp.u ≤ fp.u) huSmall
  have hγ : gammaValid fp n :=
    gammaValid_mono fp hmn hm
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowMaxDiagDefect_globalProduct_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar hInv
      hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef hbudgetNormSq
      hdetLead hdefect hglobalProduct hxHat hcG hcg

/-- Active-max-pivot global compact-step version of the row-budget-control
    equation (8) theorem.

This theorem connects the active-max-pivot packaged row-budget constructor to
the RandNLA probability layer.  It derives the samplewise
`StoredQRDisplayedRowBudgetControl` certificate from the finite active
max-pivot policy, local `κ∞`/dual compact-budget data, and the global
compact-step recurrence, then applies the finite global-product row-budget
objective theorem. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hBudget_diag : ∀ samples k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget samples k ≤
        |qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  let rowBudget : RowTrace m s → ∀ k, k < n → Fin (k + 1) → ℝ :=
    fun samples k _hk _i => stageBudget samples k
  have hrowControl : ∀ samples,
      StoredQRDisplayedRowBudgetControl hmn (A_hat samples)
        (rowBudget samples) := by
    intro samples
    exact
      StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_globalCompactBudget_activeMaxPivot_kappaInf_dualBudget
        hmn fp (A_hat samples) (alpha samples) (κ samples) (K samples)
        (stageBudget samples) hm (hStepA samples) (hAlphaDef samples)
        (hdetLead samples) (hK samples) (hκ samples) (hκbudget samples)
        (hbudgetDual samples) (hinitBlock samples) (hglobalBudget samples)
        (hBudget_nonneg samples) (hBudget_mono samples) (hBudget_diag samples)
        (hpivotChoice samples)
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_globalProduct_kappaInf_dualBudget_solver
      fp A b hd hs hmn A_hat b_hat alpha κ K rowBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hrowControl
      hglobalProduct hxHat hcG hcg

/-- Source-aligned Bennett sample-budget theorem whose stored-QR solver
    certificate is discharged by the active/prefix global compact-step route.

This is the equation (8) assembly theorem for the current Cox--Higham
active/prefix branch: it combines the RandNLA objective transfer with the
stored QR solver certificate that derives completed-column preservation and
per-pivot compact-product conditions internally.  The genuinely source-specific
QR fields remain visible samplewise assumptions: norm-square nonbreakdown,
local leading-block nonsingularity, diagonal lower bounds, pivot maximality,
the global compact-step recurrence, and the global product-smallness scalar. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq s
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat samples k a ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hBudget_diag : ∀ samples k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget samples k ≤
        |qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hpivotMax : ∀ samples t (ht : t < n), ∀ l : Fin n, t ≤ l.val →
        householderTrailingColumnNorm2Sq
            (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat samples t) l ≤
          householderTrailingColumnNorm2Sq
            (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat samples t) ⟨t, ht⟩)
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget
      hstar hInv hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef ?_
      hxHat hcG hcg
  intro samples
  exact
    StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_completedColumns_globalProduct_offdiag_rows
      hmn fp (A_hat samples) (b_hat samples) (alpha samples)
      (stageBudget samples) hm (hStepA samples) (hAlphaDef samples)
      (hbudgetNormSq samples) (hdetLead samples) (hinit samples)
      (hinitBlock samples) (hglobalBudget samples) (hBudget_nonneg samples)
      (hBudget_mono samples) (hBudget_diag samples) (hpivotMax samples)
      (hglobalProduct samples)

/-- Source-aligned Bennett sample-budget theorem for the active/prefix global
    compact-step route without a separate global stage-budget monotonicity
    hypothesis.

This is the same equation (8) assembly as
`..._stored_qr_activePrefix_globalProduct_solver`, but the samplewise
monotonicity field is replaced by the horizon-clamped QR budget wrapper from
the stored-QR source-control library. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_solver_of_horizonBudget
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hbudgetNormSq : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq s
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat samples k a ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_diag : ∀ samples k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget samples k ≤
        |qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hpivotMax : ∀ samples t (ht : t < n), ∀ l : Fin n, t ≤ l.val →
        householderTrailingColumnNorm2Sq
            (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat samples t) l ≤
          householderTrailingColumnNorm2Sq
            (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat samples t) ⟨t, ht⟩)
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget
      hstar hInv hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef ?_
      hxHat hcG hcg
  intro samples
  exact
    StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_globalCompactBudget_completedColumns_globalProduct_offdiag_rows_of_horizonBudget
      hmn fp (A_hat samples) (b_hat samples) (alpha samples)
      (stageBudget samples) hm (hStepA samples) (hAlphaDef samples)
      (hbudgetNormSq samples) (hdetLead samples) (hinit samples)
      (hinitBlock samples) (hglobalBudget samples) (hBudget_nonneg samples)
      (hBudget_diag samples) (hpivotMax samples) (hglobalProduct samples)

/-- Source-aligned Bennett sample-budget theorem whose active/prefix stored-QR
    solver certificate derives norm-square nonbreakdown from local `κ∞`/dual
    compact-budget data.

This is the same equation (8) assembly as
`..._stored_qr_activePrefix_globalProduct_solver`, but it replaces the raw
samplewise `hbudgetNormSq` assumption by the structured leading-block
inverse-budget route already proved in the QR/least-squares library. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_kappaInf_dualBudget_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hBudget_diag : ∀ samples k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget samples k ≤
        |qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hpivotMax : ∀ samples t (ht : t < n), ∀ l : Fin n, t ≤ l.val →
        householderTrailingColumnNorm2Sq
            (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat samples t) l ≤
          householderTrailingColumnNorm2Sq
            (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat samples t) ⟨t, ht⟩)
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hbudgetNormSq : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq s
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat samples k a ⟨k, hk⟩) := by
    intro samples
    exact
      storedQRSignedStage_normSqBudget_of_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget
        hmn fp (A_hat samples) (alpha samples) (κ samples) (K samples)
        (hStepA samples) (hdetLead samples) (hK samples) (hκ samples)
        (hκbudget samples) (hbudgetDual samples)
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_solver
      fp A b hd hs hmn A_hat b_hat alpha stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hbudgetNormSq hdetLead hinit hinitBlock
      hglobalBudget hBudget_nonneg hBudget_mono hBudget_diag hpivotMax
      hglobalProduct hxHat hcG hcg

/-- Horizon-clamped sibling of the `κ∞`/dual-budget active/prefix global-product
    equation (8) theorem.

This removes the samplewise global stage-budget monotonicity field while still
deriving norm-square nonbreakdown from the local leading-block
`κ∞`/self-norm and dual compact-budget route. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_kappaInf_dualBudget_solver_of_horizonBudget
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_diag : ∀ samples k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget samples k ≤
        |qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hpivotMax : ∀ samples t (ht : t < n), ∀ l : Fin n, t ≤ l.val →
        householderTrailingColumnNorm2Sq
            (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat samples t) l ≤
          householderTrailingColumnNorm2Sq
            (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat samples t) ⟨t, ht⟩)
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hbudgetNormSq : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq s
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat samples k a ⟨k, hk⟩) := by
    intro samples
    exact
      storedQRSignedStage_normSqBudget_of_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget
        hmn fp (A_hat samples) (alpha samples) (κ samples) (K samples)
        (hStepA samples) (hdetLead samples) (hK samples) (hκ samples)
        (hκbudget samples) (hbudgetDual samples)
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_solver_of_horizonBudget
      fp A b hd hs hmn A_hat b_hat alpha stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hbudgetNormSq hdetLead hinit hinitBlock
      hglobalBudget hBudget_nonneg hBudget_diag hpivotMax
      hglobalProduct hxHat hcG hcg

/-- Active-max-pivot version of the source-aligned Bennett sample-budget theorem
    for the active/prefix global compact-step route.

This is the same equation (8) assembly as
`..._stored_qr_activePrefix_globalProduct_kappaInf_dualBudget_solver`, but it
replaces the raw samplewise pivot-maximality hypothesis by the algorithmic
policy that the displayed pivot column is `householderActiveMaxPivotColumn` for
the current active block. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hBudget_diag : ∀ samples k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget samples k ≤
        |qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  classical
  have hpivotMax : ∀ samples t (ht : t < n), ∀ l : Fin n, t ≤ l.val →
      householderTrailingColumnNorm2Sq
          (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
          (A_hat samples t) l ≤
        householderTrailingColumnNorm2Sq
          (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
          (A_hat samples t) ⟨t, ht⟩ := by
    intro samples t ht l hl
    have hmax :=
      householderActiveMaxPivotColumn_pivot_max
        ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t) l hl
    have hnormEq :
        householderTrailingColumnNorm2Sq
            (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat samples t)
            (householderActiveMaxPivotColumn
              ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t)) =
          householderTrailingColumnNorm2Sq
            (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat samples t) ⟨t, ht⟩ := by
      rw [← hpivotChoice samples t ht]
    exact hmax.trans_eq hnormEq
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_kappaInf_dualBudget_solver
      fp A b hd hs hmn A_hat b_hat alpha κ K stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hinit hinitBlock
      hglobalBudget hBudget_nonneg hBudget_mono hBudget_diag hpivotMax
      hglobalProduct hxHat hcG hcg

/-- Horizon-clamped active-max-pivot version of the source-aligned Bennett
    sample-budget theorem for the active/prefix global compact-step route.

This is the same equation (8) assembly as
`..._activePrefix_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver`, but
the samplewise global stage-budget monotonicity field is derived internally
from the finite compact-step recurrence through the horizon-clamped
`κ∞`/dual-budget wrapper. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver_of_horizonBudget
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_diag : ∀ samples k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget samples k ≤
        |qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  classical
  have hpivotMax : ∀ samples t (ht : t < n), ∀ l : Fin n, t ≤ l.val →
      householderTrailingColumnNorm2Sq
          (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
          (A_hat samples t) l ≤
        householderTrailingColumnNorm2Sq
          (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
          (A_hat samples t) ⟨t, ht⟩ := by
    intro samples t ht l hl
    have hmax :=
      householderActiveMaxPivotColumn_pivot_max
        ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t) l hl
    have hnormEq :
        householderTrailingColumnNorm2Sq
            (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat samples t)
            (householderActiveMaxPivotColumn
              ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t)) =
          householderTrailingColumnNorm2Sq
            (m := s) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat samples t) ⟨t, ht⟩ := by
      rw [← hpivotChoice samples t ht]
    exact hmax.trans_eq hnormEq
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_kappaInf_dualBudget_solver_of_horizonBudget
      fp A b hd hs hmn A_hat b_hat alpha κ K stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hinit hinitBlock
      hglobalBudget hBudget_nonneg hBudget_diag hpivotMax
      hglobalProduct hxHat hcG hcg

/-- Active-max-pivot equation (8) wrapper with visible row-max assumptions.

This is the same high-probability active/prefix QR assembly as
`..._activeMaxPivot_kappaInf_dualBudget_solver`, but it exposes the two
row-max fields needed by the scalar stage-diagonal route:
`storedQRRowMaxDiagDefectBudget <= 0` and the displayed comparison
`stageBudget <= qrLeadingStrictUpperRowMaxBudget`.  The diagonal lower-bound
family is derived internally by the row-max bridge before applying the existing
active-max-pivot probability theorem. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hrowDefect : ∀ samples,
      storedQRRowMaxDiagDefectBudget hmn (A_hat samples) ≤ 0)
    (hstage_le_rowMax : ∀ samples k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget samples k ≤
          qrLeadingStrictUpperRowMaxBudget hmn (A_hat samples) k hk i)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  classical
  have hBudget_diag : ∀ samples k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget samples k ≤
        |qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i| := by
    intro samples
    exact
      storedQRStageBudget_le_diag_of_stageDiagLowerDefectBudget_nonpos
        hmn (A_hat samples) (stageBudget samples)
        (storedQRStageDiagLowerDefectBudget_nonpos_of_rowMaxDiagDefectBudget_nonpos_stageBudget_le_rowMax
          hmn (A_hat samples) (stageBudget samples) (hrowDefect samples)
          (hstage_le_rowMax samples))
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver
      fp A b hd hs hmn A_hat b_hat alpha κ K stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hinit hinitBlock
      hglobalBudget hBudget_nonneg hBudget_mono hBudget_diag hpivotChoice
      hglobalProduct hxHat hcG hcg

/-- Horizon-clamped visible row-max active-max-pivot equation (8) wrapper.

This is the same theorem surface as
`..._activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver`,
but it removes the samplewise global stage-budget monotonicity field by deriving
the diagonal lower-bound family from the row-max assumptions and then applying
the horizon-clamped active-pivot `κ∞`/dual-budget wrapper. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver_of_horizonBudget
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hrowDefect : ∀ samples,
      storedQRRowMaxDiagDefectBudget hmn (A_hat samples) ≤ 0)
    (hstage_le_rowMax : ∀ samples k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget samples k ≤
          qrLeadingStrictUpperRowMaxBudget hmn (A_hat samples) k hk i)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  classical
  have hBudget_diag : ∀ samples k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget samples k ≤
        |qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i| := by
    intro samples
    exact
      storedQRStageBudget_le_diag_of_stageDiagLowerDefectBudget_nonpos
        hmn (A_hat samples) (stageBudget samples)
        (storedQRStageDiagLowerDefectBudget_nonpos_of_rowMaxDiagDefectBudget_nonpos_stageBudget_le_rowMax
          hmn (A_hat samples) (stageBudget samples) (hrowDefect samples)
          (hstage_le_rowMax samples))
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver_of_horizonBudget
      fp A b hd hs hmn A_hat b_hat alpha κ K stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hinit hinitBlock
      hglobalBudget hBudget_nonneg hBudget_diag hpivotChoice
      hglobalProduct hxHat hcG hcg

/-- Actual-unit-roundoff sibling of the probability-level visible row-max
    active-pivot equation (8) theorem.

The scalar sampled-dimension guard `(s : ℝ) * fp.u < 1` supplies both
`gammaValid fp s` and, because `n ≤ s`, `gammaValid fp n`.  The row-max
defect, stage-budget/row-max comparison, determinant/conditioning,
dual compact-budget, active-pivot policy, and global compact-product
assumptions remain visible. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver_of_actualUnitRoundoff_no_gammaValid
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (huSmall : (s : ℝ) * fp.u < 1)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hrowDefect : ∀ samples,
      storedQRRowMaxDiagDefectBudget hmn (A_hat samples) ≤ 0)
    (hstage_le_rowMax : ∀ samples k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget samples k ≤
          qrLeadingStrictUpperRowMaxBudget hmn (A_hat samples) k hk i)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hm : gammaValid fp s :=
    gammaValid_of_u_le_cap fp s fp.u (le_rfl : fp.u ≤ fp.u) huSmall
  have hγ : gammaValid fp n :=
    gammaValid_mono fp hmn hm
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver
      fp A b hd hs hmn A_hat b_hat alpha κ K stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hinit hinitBlock
      hglobalBudget hBudget_nonneg hBudget_mono hrowDefect hstage_le_rowMax
      hpivotChoice hglobalProduct hxHat hcG hcg

/-- Horizon-clamped actual-unit-roundoff version of the visible row-max
    active-max-pivot equation (8) wrapper.

This composes the actual-unit-roundoff validity reduction with the
horizon-clamped row-max theorem, so the sampled theorem surface exposes
`(s : ℝ) * fp.u < 1` instead of sampled `gammaValid` fields and does not expose
the samplewise global stage-budget monotonicity hypothesis. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (huSmall : (s : ℝ) * fp.u < 1)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hrowDefect : ∀ samples,
      storedQRRowMaxDiagDefectBudget hmn (A_hat samples) ≤ 0)
    (hstage_le_rowMax : ∀ samples k (hk : k < n),
      ∀ i : Fin (k + 1), i.val < k →
        stageBudget samples k ≤
          qrLeadingStrictUpperRowMaxBudget hmn (A_hat samples) k hk i)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hm : gammaValid fp s :=
    gammaValid_of_u_le_cap fp s fp.u (le_rfl : fp.u ≤ fp.u) huSmall
  have hγ : gammaValid fp n :=
    gammaValid_mono fp hmn hm
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver_of_horizonBudget
      fp A b hd hs hmn A_hat b_hat alpha κ K stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hinit hinitBlock
      hglobalBudget hBudget_nonneg hrowDefect hstage_le_rowMax hpivotChoice
      hglobalProduct hxHat hcG hcg

/-- Active-max-pivot equation (8) wrapper with finite row-max scalar defects.

This sampled theorem replaces the displayed samplewise comparison
`stageBudget <= qrLeadingStrictUpperRowMaxBudget` by the scalar finite maximum
condition `storedQRStageRowMaxComparisonDefectBudget <= 0`, then applies the
existing visible row-max probability theorem. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hrowDefect : ∀ samples,
      storedQRRowMaxDiagDefectBudget hmn (A_hat samples) ≤ 0)
    (hcomparison : ∀ samples,
      storedQRStageRowMaxComparisonDefectBudget hmn
        (A_hat samples) (stageBudget samples) ≤ 0)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver
      fp A b hd hs hmn A_hat b_hat alpha κ K stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hinit hinitBlock
      hglobalBudget hBudget_nonneg hBudget_mono hrowDefect
      (fun samples =>
        storedQRStageBudget_le_rowMax_of_stageRowMaxComparisonDefectBudget_nonpos
          hmn (A_hat samples) (stageBudget samples) (hcomparison samples))
      hpivotChoice hglobalProduct hxHat hcG hcg

/-- Horizon-clamped scalar-comparison active-pivot equation (8) wrapper.

This is the explicit-`gammaValid` sibling of the scalar finite comparison
probability theorem.  It extracts the displayed comparison
`stageBudget <= qrLeadingStrictUpperRowMaxBudget` from the scalar comparison
defect and then calls the horizon-clamped visible row-max wrapper, so the
samplewise global stage-budget monotonicity field is not part of this theorem
surface. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver_of_horizonBudget
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hrowDefect : ∀ samples,
      storedQRRowMaxDiagDefectBudget hmn (A_hat samples) ≤ 0)
    (hcomparison : ∀ samples,
      storedQRStageRowMaxComparisonDefectBudget hmn
        (A_hat samples) (stageBudget samples) ≤ 0)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver_of_horizonBudget
      fp A b hd hs hmn A_hat b_hat alpha κ K stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hinit hinitBlock
      hglobalBudget hBudget_nonneg hrowDefect
      (fun samples =>
        storedQRStageBudget_le_rowMax_of_stageRowMaxComparisonDefectBudget_nonpos
          hmn (A_hat samples) (stageBudget samples) (hcomparison samples))
      hpivotChoice hglobalProduct hxHat hcG hcg

/-- Diagonal-dominant scalar-comparison sampled equation (8) wrapper.

This is the probability-level sibling of the local diagonal-dominant
active-pivot scalar-comparison route: samplewise diagonal dominance supplies the
local determinant and row-max scalar-defect fields, while the scalar comparison
defect supplies the remaining stage-budget/row-max comparison through the
already-formalized finite package. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hcomparison : ∀ samples,
      storedQRStageRowMaxComparisonDefectBudget hmn
        (A_hat samples) (stageBudget samples) ≤ 0)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0 := by
    intro samples k hk
    exact
      det_ne_zero_of_diagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        (hDD samples k hk)
  have hrowDefect : ∀ samples,
      storedQRRowMaxDiagDefectBudget hmn (A_hat samples) ≤ 0 := by
    intro samples
    exact
      storedQRRowMaxDiagDefectBudget_nonpos_of_diagDominant
        hmn (A_hat samples) (hDD samples)
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver
      fp A b hd hs hmn A_hat b_hat alpha κ K stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hinit hinitBlock
      hglobalBudget hBudget_nonneg hBudget_mono hrowDefect hcomparison
      hpivotChoice hglobalProduct hxHat hcG hcg

/-- Diagonal-dominant scalar-comparison sampled equation (8) wrapper with
    compact-product smallness supplied by the canonical finite-max scalar.

This is the probability-level finite-max sibling of
`..._activePrefix_globalProduct_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_...`:
for each sampled stored-QR trace, local diagonal dominance and the finite-max
smallness inequality derive the raw global product field before the existing
active-pivot scalar-comparison theorem is applied. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSmallness_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hcomparison : ∀ samples,
      storedQRStageRowMaxComparisonDefectBudget hmn
        (A_hat samples) (stageBudget samples) ≤ 0)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hsmall : ∀ samples,
      2 * storedQRDiagDominantInvFactorBudget hmn (A_hat samples) *
          ((s : ℝ) *
            (storedQRCompactSequenceRelativeBudget hmn fp
                (A_hat samples) (b_hat samples) (alpha samples) *
              storedQRPivotColumnNormBudget hmn (A_hat samples)) ^ 2) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1 := by
    intro samples
    exact
      storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_smallness
        hmn fp (A_hat samples) (b_hat samples) (alpha samples) hm
        (fun k => hDD samples k.val k.isLt) (hsmall samples)
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver
      fp A b hd hs hmn A_hat b_hat alpha κ K stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hDD hK hκ hκbudget hbudgetDual hinit hinitBlock
      hglobalBudget hBudget_nonneg hBudget_mono hcomparison hpivotChoice
      hglobalProduct hxHat hcG hcg

/-- Diagonal-dominant scalar-comparison sampled equation (8) wrapper using the
    concrete dual-budget route.

This is the probability-level active-pivot finite-max theorem after eliminating
the auxiliary `κ`/`K` and dual compact-budget package.  For each sampled stored
QR trace, the concrete-dual source-control theorem derives norm-square
nonbreakdown from local diagonal dominance and the canonical finite-max
smallness scalar. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSmallness_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_concreteDual_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hcomparison : ∀ samples,
      storedQRStageRowMaxComparisonDefectBudget hmn
        (A_hat samples) (stageBudget samples) ≤ 0)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hsmall : ∀ samples,
      2 * storedQRDiagDominantInvFactorBudget hmn (A_hat samples) *
          ((s : ℝ) *
            (storedQRCompactSequenceRelativeBudget hmn fp
                (A_hat samples) (b_hat samples) (alpha samples) *
              storedQRPivotColumnNormBudget hmn (A_hat samples)) ^ 2) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget
      hstar hInv hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef ?_
      hxHat hcG hcg
  intro samples
  exact
    StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSmallness_stageRowMaxComparisonDefect_concreteDual_offdiag_rows
      hmn fp (A_hat samples) (b_hat samples) (alpha samples)
      (stageBudget samples) hm (hStepA samples) (hAlphaDef samples)
      (hDD samples) (hinit samples) (hinitBlock samples)
      (hglobalBudget samples) (hBudget_nonneg samples)
      (hBudget_mono samples) (hcomparison samples) (hpivotChoice samples)
      (hsmall samples)

/-- Actual-unit-roundoff sibling of the sampled active finite-max concrete-dual
    equation (8) theorem.

The sampled `gammaValid fp s` and triangular `gammaValid fp n` hypotheses are
derived from `(s : ℝ) * fp.u < 1`.  The genuinely open QR-domain fields remain
visible samplewise: local diagonal dominance, signed-stage recurrence budgets,
active-pivot choice, scalar comparison defect, and finite-max product
smallness. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSmallness_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_concreteDual_solver_of_actualUnitRoundoff_no_gammaValid
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (huSmall : (s : ℝ) * fp.u < 1)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hcomparison : ∀ samples,
      storedQRStageRowMaxComparisonDefectBudget hmn
        (A_hat samples) (stageBudget samples) ≤ 0)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hsmall : ∀ samples,
      2 * storedQRDiagDominantInvFactorBudget hmn (A_hat samples) *
          ((s : ℝ) *
            (storedQRCompactSequenceRelativeBudget hmn fp
                (A_hat samples) (b_hat samples) (alpha samples) *
              storedQRPivotColumnNormBudget hmn (A_hat samples)) ^ 2) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hm : gammaValid fp s :=
    gammaValid_of_u_le_cap fp s fp.u (le_rfl : fp.u ≤ fp.u) huSmall
  have hγ : gammaValid fp n :=
    gammaValid_mono fp hmn hm
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSmallness_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_concreteDual_solver
      fp A b hd hs hmn A_hat b_hat alpha stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef hDD hinit hinitBlock hglobalBudget hBudget_nonneg
      hBudget_mono hcomparison hpivotChoice hsmall hxHat hcG hcg

/-- Diagonal-dominant scalar-comparison sampled equation (8) wrapper using the
    canonical source-denominator/rational-gamma compact-product cap.

This is the probability-level sibling of the active local source-denominator
handoff: for each sampled stored QR trace, the source-control certificate
derives the raw compact-product field from source-denominator nonbreakdown,
the unit-roundoff cap, and the canonical rational-gamma cap-smallness scalar. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    (Ucap : ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hcomparison : ∀ samples,
      storedQRStageRowMaxComparisonDefectBudget hmn
        (A_hat samples) (stageBudget samples) ≤ 0)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hUcap_nonneg : 0 ≤ Ucap)
    (hden : ∀ samples k (hk : k < n),
      (∑ i : Fin s,
        householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k) i *
          householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k) i) ≠ 0)
    (hu : fp.u ≤ Ucap)
    (huCap : (s : ℝ) * Ucap < 1)
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * Ucap) / (1 - (s : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget
      hstar hInv hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef ?_
      hxHat hcG hcg
  intro samples
  exact
    StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows
      hmn fp (A_hat samples) (b_hat samples) (alpha samples)
      (stageBudget samples) Ucap hm (hStepA samples) (hAlphaDef samples)
      (hDD samples) (hinit samples) (hinitBlock samples)
      (hglobalBudget samples) (hBudget_nonneg samples)
      (hBudget_mono samples) (hcomparison samples) (hpivotChoice samples)
      hUcap_nonneg (hden samples) hu huCap (hsmall samples)

/-- Horizon-clamped sampled equation (8) wrapper using the canonical
    source-denominator/rational-gamma compact-product cap.

For each sampled stored QR trace, the global compact-step recurrence supplies
monotonicity on the QR horizon.  The local source-control certificate clamps
the budget after that horizon internally, so this probability surface no longer
exposes a samplewise global monotonicity assumption. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_horizonBudget
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    (Ucap : ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hcomparison : ∀ samples,
      storedQRStageRowMaxComparisonDefectBudget hmn
        (A_hat samples) (stageBudget samples) ≤ 0)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hUcap_nonneg : 0 ≤ Ucap)
    (hden : ∀ samples k (hk : k < n),
      (∑ i : Fin s,
        householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k) i *
          householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k) i) ≠ 0)
    (hu : fp.u ≤ Ucap)
    (huCap : (s : ℝ) * Ucap < 1)
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * Ucap) / (1 - (s : ℝ) * Ucap)
      let Fcap :=
        Ucap * (1 + Gcap) * (1 + Ucap) +
          Ucap * (1 + Gcap) +
          Gcap +
          Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (Ucap + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget
      hstar hInv hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef ?_
      hxHat hcG hcg
  intro samples
  exact
    StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_horizonBudget
      hmn fp (A_hat samples) (b_hat samples) (alpha samples)
      (stageBudget samples) Ucap hm (hStepA samples) (hAlphaDef samples)
      (hDD samples) (hinit samples) (hinitBlock samples)
      (hglobalBudget samples) (hBudget_nonneg samples)
      (hcomparison samples) (hpivotChoice samples) hUcap_nonneg
      (hden samples) hu huCap (hsmall samples)

/-- Actual-unit-roundoff sibling of the probability-level active
    source-denominator/cap scalar-comparison theorem.

This specializes the cap to `Ucap = fp.u` and derives the sampled
`gammaValid fp s` and triangular `gammaValid fp n` guards internally from
`(s : ℝ) * fp.u < 1`. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_actualUnitRoundoff_no_gammaValid
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (huSmall : (s : ℝ) * fp.u < 1)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hcomparison : ∀ samples,
      storedQRStageRowMaxComparisonDefectBudget hmn
        (A_hat samples) (stageBudget samples) ≤ 0)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hden : ∀ samples k (hk : k < n),
      (∑ i : Fin s,
        householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k) i *
          householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k) i) ≠ 0)
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * fp.u) / (1 - (s : ℝ) * fp.u)
      let Fcap :=
        fp.u * (1 + Gcap) * (1 + fp.u) +
          fp.u * (1 + Gcap) +
          Gcap +
          fp.u * (1 + Gcap) * (1 + fp.u) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (fp.u + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hm : gammaValid fp s :=
    gammaValid_of_u_le_cap fp s fp.u (le_rfl : fp.u ≤ fp.u) huSmall
  have hγ : gammaValid fp n :=
    gammaValid_mono fp hmn hm
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver
      fp A b hd hs hmn A_hat b_hat alpha stageBudget xHat xStar xOpt
      ATA_inv c_G c_g fp.u hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef hDD hinit hinitBlock hglobalBudget hBudget_nonneg
      hBudget_mono hcomparison hpivotChoice fp.u_nonneg hden
      (le_rfl : fp.u ≤ fp.u) huSmall hsmall hxHat hcG hcg

/-- Actual-unit horizon-clamped sibling of the probability-level active
    source-denominator/cap scalar-comparison theorem.

This combines the horizon-clamped source-denominator handoff with the
`Ucap = fp.u` specialization, deriving the sampled `gammaValid` guards from
`(s : ℝ) * fp.u < 1` while leaving global stage-budget monotonicity off the
surface. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (huSmall : (s : ℝ) * fp.u < 1)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hcomparison : ∀ samples,
      storedQRStageRowMaxComparisonDefectBudget hmn
        (A_hat samples) (stageBudget samples) ≤ 0)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hden : ∀ samples k (hk : k < n),
      (∑ i : Fin s,
        householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k) i *
          householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k) i) ≠ 0)
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * fp.u) / (1 - (s : ℝ) * fp.u)
      let Fcap :=
        fp.u * (1 + Gcap) * (1 + fp.u) +
          fp.u * (1 + Gcap) +
          Gcap +
          fp.u * (1 + Gcap) * (1 + fp.u) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (fp.u + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hm : gammaValid fp s :=
    gammaValid_of_u_le_cap fp s fp.u (le_rfl : fp.u ≤ fp.u) huSmall
  have hγ : gammaValid fp n :=
    gammaValid_mono fp hmn hm
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_horizonBudget
      fp A b hd hs hmn A_hat b_hat alpha stageBudget xHat xStar xOpt
      ATA_inv c_G c_g fp.u hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA hStepb
      hAlphaDef hDD hinit hinitBlock hglobalBudget hBudget_nonneg
      hcomparison hpivotChoice fp.u_nonneg hden
      (le_rfl : fp.u ≤ fp.u) huSmall hsmall hxHat hcG hcg

/-- Sampled actual-unit active source-denominator theorem with denominator
    nonbreakdown derived from the stored QR trace.

This stored-lower sibling removes the samplewise raw source-denominator field
from the equation (8) probability surface.  For every sampled trace, denominator
nonbreakdown follows from the stored recurrence, signed-alpha definition, and
local diagonal dominance before the existing actual-unit theorem is applied. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_actualUnitRoundoff_no_gammaValid
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (huSmall : (s : ℝ) * fp.u < 1)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hcomparison : ∀ samples,
      storedQRStageRowMaxComparisonDefectBudget hmn
        (A_hat samples) (stageBudget samples) ≤ 0)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * fp.u) / (1 - (s : ℝ) * fp.u)
      let Fcap :=
        fp.u * (1 + Gcap) * (1 + fp.u) +
          fp.u * (1 + Gcap) +
          Gcap +
          fp.u * (1 + Gcap) * (1 + fp.u) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (fp.u + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_actualUnitRoundoff_no_gammaValid
      fp A b hd hs hmn A_hat b_hat alpha stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact huSmall hInitA hInitb hStepA hStepb
      hAlphaDef hDD hinit hinitBlock hglobalBudget hBudget_nonneg
      hBudget_mono hcomparison hpivotChoice
      (fun samples =>
        storedQRSourceDenominator_ne_zero_of_diagDominant_signedAlphaDef_stored_trailing_sequence
          fp hmn (A_hat samples) (alpha samples)
          (hStepA samples) (hAlphaDef samples) (hDD samples))
      hsmall hxHat hcG hcg

/-- Horizon-clamped sampled actual-unit active source-denominator theorem with
    denominator nonbreakdown derived from the stored QR trace.

This is the stored-lower sibling of the horizon-clamped source-denominator
probability theorem: the trace itself supplies denominator nonbreakdown, and
the compact-step recurrence supplies the only monotonicity needed on the QR
horizon. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (huSmall : (s : ℝ) * fp.u < 1)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hcomparison : ∀ samples,
      storedQRStageRowMaxComparisonDefectBudget hmn
        (A_hat samples) (stageBudget samples) ≤ 0)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hsmall : ∀ samples,
      let Dcap := storedQRDiagDominantInvFactorBudget hmn (A_hat samples)
      let Ncap := storedQRPivotColumnNormBudget hmn (A_hat samples)
      let Gcap := ((s : ℝ) * fp.u) / (1 - (s : ℝ) * fp.u)
      let Fcap :=
        fp.u * (1 + Gcap) * (1 + fp.u) +
          fp.u * (1 + Gcap) +
          Gcap +
          fp.u * (1 + Gcap) * (1 + fp.u) ^ 2
      2 * Dcap *
          ((s : ℝ) *
            ((((n : ℝ) * ((n : ℝ) + 1) * (fp.u + 2 * Fcap)) *
                Ncap) ^ 2)) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget
      fp A b hd hs hmn A_hat b_hat alpha stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact huSmall hInitA hInitb hStepA hStepb
      hAlphaDef hDD hinit hinitBlock hglobalBudget hBudget_nonneg
      hcomparison hpivotChoice
      (fun samples =>
        storedQRSourceDenominator_ne_zero_of_diagDominant_signedAlphaDef_stored_trailing_sequence
          fp hmn (A_hat samples) (alpha samples)
          (hStepA samples) (hAlphaDef samples) (hDD samples))
      hsmall hxHat hcG hcg

/-- Actual-unit-roundoff sibling of the probability-level scalar-comparison
    active-pivot equation (8) theorem. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver_of_actualUnitRoundoff_no_gammaValid
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (huSmall : (s : ℝ) * fp.u < 1)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hBudget_mono : ∀ samples a b, a ≤ b →
      stageBudget samples a ≤ stageBudget samples b)
    (hrowDefect : ∀ samples,
      storedQRRowMaxDiagDefectBudget hmn (A_hat samples) ≤ 0)
    (hcomparison : ∀ samples,
      storedQRStageRowMaxComparisonDefectBudget hmn
        (A_hat samples) (stageBudget samples) ≤ 0)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver_of_actualUnitRoundoff_no_gammaValid
      fp A b hd hs hmn A_hat b_hat alpha κ K stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact huSmall hInitA hInitb hStepA
      hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hinit hinitBlock
      hglobalBudget hBudget_nonneg hBudget_mono hrowDefect
      (fun samples =>
        storedQRStageBudget_le_rowMax_of_stageRowMaxComparisonDefectBudget_nonpos
          hmn (A_hat samples) (stageBudget samples) (hcomparison samples))
      hpivotChoice hglobalProduct hxHat hcG hcg

/-- Horizon-clamped actual-unit-roundoff sibling of the probability-level
    scalar-comparison active-pivot equation (8) theorem.

This removes the samplewise global budget-monotonicity field from the
actual-unit scalar-comparison surface by extracting the displayed row-max
comparison from the scalar defect and calling the horizon row-max wrapper. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K stageBudget : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (huSmall : (s : ℝ) * fp.u < 1)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hinit : ∀ samples k (hk : k < n),
      ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      |A_hat samples 0
          (qrLeadingRow s k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        stageBudget samples 0)
    (hinitBlock : ∀ samples r l,
      |A_hat samples 0 r l| ≤ stageBudget samples 0)
    (hglobalBudget : ∀ samples t (ht : t < n),
      coxHighamActiveRowGrowthFactor s * stageBudget samples t +
          storedQRSignedStageGlobalCompactBudget hmn fp
            (A_hat samples) (alpha samples) t ht ≤
        stageBudget samples (t + 1))
    (hBudget_nonneg : ∀ samples t, 0 ≤ stageBudget samples t)
    (hrowDefect : ∀ samples,
      storedQRRowMaxDiagDefectBudget hmn (A_hat samples) ≤ 0)
    (hcomparison : ∀ samples,
      storedQRStageRowMaxComparisonDefectBudget hmn
        (A_hat samples) (stageBudget samples) ≤ 0)
    (hpivotChoice : ∀ samples t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat samples t))
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  have hm : gammaValid fp s :=
    gammaValid_of_u_le_cap fp s fp.u (le_rfl : fp.u ≤ fp.u) huSmall
  have hγ : gammaValid fp n :=
    gammaValid_mono fp hmn hm
  exact
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver_of_horizonBudget
      fp A b hd hs hmn A_hat b_hat alpha κ K stageBudget xHat xStar xOpt
      ATA_inv c_G c_g hε_pos hε hδ hbudgetUpper hbudgetLower
      hobjectiveBudget hstar hInv hExact hm hγ hInitA hInitb hStepA
      hStepb hAlphaDef hdetLead hK hκ hκbudget hbudgetDual hinit hinitBlock
      hglobalBudget hBudget_nonneg hrowDefect hcomparison hpivotChoice
      hglobalProduct hxHat hcG hcg

/-- Source-aligned Bennett sample-budget theorem whose stored-QR solver
    certificate uses diagonal-dominant local leading blocks.

This is an equation (8) assembly route for the case where the displayed local
leading blocks are already diagonally dominant.  The diagonal-dominance
hypothesis supplies the off-diagonal/diagonal-lower-bound field directly, while
the `κ∞`/dual-budget hypotheses supply the norm-square nonbreakdown margin and
the finite global compact-product scalar supplies product smallness. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_globalProduct_kappaInf_dualBudget_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hglobalProduct : ∀ samples,
      storedQRCompactSequenceProductBudget hmn fp
        (A_hat samples) (b_hat samples) (alpha samples) < 1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget
      hstar hInv hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef ?_
      hxHat hcG hcg
  intro samples
  exact
    StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_globalProduct
      hmn fp (A_hat samples) (b_hat samples) (alpha samples)
      (κ samples) (K samples) hm (hStepA samples) (hAlphaDef samples)
      (hdetLead samples) (hDD samples) (hK samples) (hκ samples)
      (hκbudget samples) (hbudgetDual samples) (hglobalProduct samples)

/-- Source-aligned Bennett sample-budget theorem whose stored-QR solver
    certificate uses diagonal-dominant local leading blocks and the canonical
    finite-max product-smallness scalar condition.

This is the same equation (8) assembly as
`..._diagDominant_globalProduct_kappaInf_dualBudget_solver`, but the raw
global-product hypothesis is replaced by one scalar inequality involving the
canonical finite maxima of the local diagonal-dominant inverse factors and
pivot-column norms for each sampled QR trace. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSmallness_kappaInf_dualBudget_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (κ K : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hK : ∀ samples k (_hk : k < n), 0 < K samples k)
    (hκ : ∀ samples k (hk : k < n),
      kappaInf (k + 1) (Nat.succ_pos k)
          (qrLeadingBlock (A_hat samples k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          (nonsingInv (k + 1)
            (qrLeadingBlock (A_hat samples k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ≤
        κ samples k)
    (hκbudget : ∀ samples k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) *
          (κ samples k /
            infNorm
              (qrLeadingBlock (A_hat samples k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) ^ 2 ≤
        K samples k)
    (hbudgetDual : ∀ samples k (hk : k < n),
      (s : ℝ) *
          (householderCompactComponentBudget fp s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
            (householderBetaSpec s
              (householderTrailingActiveVector s
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
            (fun a => A_hat samples k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K samples k)
    (hsmall : ∀ samples,
      2 * storedQRDiagDominantInvFactorBudget hmn (A_hat samples) *
          ((s : ℝ) *
            (storedQRCompactSequenceRelativeBudget hmn fp
              (A_hat samples) (b_hat samples) (alpha samples) *
              storedQRPivotColumnNormBudget hmn (A_hat samples)) ^ 2) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver
      fp A b hd hs hmn A_hat b_hat alpha xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget
      hstar hInv hExact hm hγ hInitA hInitb hStepA hStepb hAlphaDef ?_
      hxHat hcG hcg
  intro samples
  exact
    StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_finiteMaxSmallness
      hmn fp (A_hat samples) (b_hat samples) (alpha samples)
      (κ samples) (K samples) hm (hStepA samples) (hAlphaDef samples)
      (hdetLead samples) (hDD samples) (hK samples) (hκ samples)
      (hκbudget samples) (hbudgetDual samples) (hsmall samples)

/-- Source-aligned Bennett sample-budget theorem for literal rounded
    sampled/scaled least squares whose stored-QR solver is discharged by the
    concrete diagonal-dominant finite-max route.

Compared with
`..._diagDominant_finiteMaxSmallness_kappaInf_dualBudget_solver`, this theorem
does not expose auxiliary `κ`/`K` sequences or a separate dual compact-budget
hypothesis.  The local least-squares theorem reuses the repository's concrete
diagonal-dominant inverse-budget route and the canonical finite-max scalar
smallness inequality. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSmallness_concreteDual_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hdetLead : ∀ samples k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hsmall : ∀ samples,
      2 * storedQRDiagDominantInvFactorBudget hmn (A_hat samples) *
          ((s : ℝ) *
            (storedQRCompactSequenceRelativeBudget hmn fp
              (A_hat samples) (b_hat samples) (alpha samples) *
              storedQRPivotColumnNormBudget hmn (A_hat samples)) ^ 2) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_ls_qr_backward_error_solver
      fp A b hd hs xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget
      hstar hInv hExact ?_
  intro samples
  have hBack :=
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_diagDominant_finiteMaxSmallness_concreteDual
      fp hmn
      (fl_rowSampleLSMatrixWithBasisScale fp s
        (augmentedSpanBasisMatrix A b) A samples)
      (fl_rowSampleLSVectorWithBasisScale fp s
        (augmentedSpanBasisMatrix A b) b samples)
      (A_hat samples) (b_hat samples) (alpha samples)
      hm hγ (hInitA samples) (hInitb samples)
      (hStepA samples) (hStepb samples) (hAlphaDef samples)
      (hdetLead samples) (hDD samples) (hsmall samples)
  simpa [hxHat samples, hcG samples, hcg samples,
    storedQRBackSubSolution, storedQRFinalR, storedQRFinalTopRhs,
    lsNormalMatrix, lsNormalRhs, rectLSGram, rectLSRhs] using hBack

/-- Source-aligned Bennett sample-budget theorem for literal rounded
    sampled/scaled least squares whose stored-QR solver is discharged by the
    concrete diagonal-dominant finite-max route, with local determinant
    nonzeroness derived from `IsDiagDominantUpper`.

Compared with
`..._diagDominant_finiteMaxSmallness_concreteDual_solver`, this theorem does
not expose a separate samplewise `hdetLead` field: the repository
`IsDiagDominantUpper` predicate already includes upper-triangular shape and
nonzero diagonal entries, hence local nonsingularity. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSmallness_concreteDual_solver_of_diagDominant
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ)) (hmn : n ≤ s)
    (A_hat : RowTrace m s → ℕ → Fin s → Fin n → ℝ)
    (b_hat : RowTrace m s → ℕ → Fin s → ℝ)
    (alpha : RowTrace m s → ℕ → ℝ)
    (xHat xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (c_G c_g : RowTrace m s → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples (xHat samples) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (lsQRSolveBackwardSolverDx (ATA_inv samples) (c_G samples)
                (c_g samples) (xHat samples)) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (hm : gammaValid fp s)
    (hγ : gammaValid fp n)
    (hInitA : ∀ samples,
      A_hat samples 0 =
        fl_rowSampleLSMatrixWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) A samples)
    (hInitb : ∀ samples,
      b_hat samples 0 =
        fl_rowSampleLSVectorWithBasisScale fp s
          (augmentedSpanBasisMatrix A b) b samples)
    (hStepA : ∀ samples k (hk : k < n),
      A_hat samples (k + 1) =
        fl_householderStoredPanelStep fp s n k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (A_hat samples k))
    (hStepb : ∀ samples k (hk : k < n),
      b_hat samples (k + 1) =
        fl_householderStoredRhsStep fp s k
          (householderTrailingActiveVector s
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k))
          (householderBetaSpec s
            (householderTrailingActiveVector s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩) (alpha samples k)))
          (b_hat samples k))
    (hAlphaDef : ∀ samples k (hk : k < n),
      alpha samples k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq s
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat samples k a ⟨k, hk⟩)))
          (A_hat samples k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ samples k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat samples k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk))
    (hsmall : ∀ samples,
      2 * storedQRDiagDominantInvFactorBudget hmn (A_hat samples) *
          ((s : ℝ) *
            (storedQRCompactSequenceRelativeBudget hmn fp
              (A_hat samples) (b_hat samples) (alpha samples) *
              storedQRPivotColumnNormBudget hmn (A_hat samples)) ^ 2) <
        1)
    (hxHat : ∀ samples,
      xHat samples =
        storedQRBackSubSolution fp hmn (A_hat samples) (b_hat samples))
    (hcG : ∀ samples,
      c_G samples =
        qrSolveFinalGramBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples)))
    (hcg : ∀ samples,
      c_g samples =
        qrSolveFinalRhsBudget fp
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (storedQRFinalR hmn (A_hat samples))
          (storedQRCompactSequenceRelativeBudget hmn fp
            (A_hat samples) (b_hat samples) (alpha samples))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_ls_qr_backward_error_solver
      fp A b hd hs xHat xStar xOpt ATA_inv c_G c_g
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget
      hstar hInv hExact ?_
  intro samples
  have hBack :=
    LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_finiteMaxSmallness_concreteDual
      fp hmn
      (fl_rowSampleLSMatrixWithBasisScale fp s
        (augmentedSpanBasisMatrix A b) A samples)
      (fl_rowSampleLSVectorWithBasisScale fp s
        (augmentedSpanBasisMatrix A b) b samples)
      (A_hat samples) (b_hat samples) (alpha samples)
      hm hγ (hInitA samples) (hInitb samples)
      (hStepA samples) (hStepb samples) (hAlphaDef samples)
      (hDD samples) (hsmall samples)
  simpa [hxHat samples, hcG samples, hcg samples,
    storedQRBackSubSolution, storedQRFinalR, storedQRFinalTopRhs,
    lsNormalMatrix, lsNormalRhs, rectLSGram, rectLSRhs] using hBack

/-- Source-aligned Bennett sample-budget theorem for literal rounded
    sampled/scaled least squares when the downstream solver is the concrete
    normal-equations/Cholesky method formalized in
    `LSNormalEquations.lean`.

This closes an implementation-backed solver certificate route: the local
normal-equations backward-error theorem supplies explicit perturbation radii,
and the local forward-error theorem turns them into the componentwise
`solverDx` certificate consumed by the RandNLA objective transfer.  This is
not a QR/preconditioner theorem; it is a concrete normal-equations solver
variant with its conditioning consequences exposed in the certificate. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_normal_eq_cholesky_solver
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 1 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ))
    (xStar : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (ATA_inv : RowTrace m s → Fin n → Fin n → ℝ)
    (absATA : RowTrace m s → Fin n → Fin n → ℝ)
    (absATb : RowTrace m s → Fin n → ℝ)
    (C_hat : RowTrace m s → Fin n → Fin n → ℝ)
    (c_hat : RowTrace m s → Fin n → ℝ)
    (R_hat : RowTrace m s → Fin n → Fin n → ℝ)
    {ε η δ : ℝ} (hε_pos : 0 < ε) (hε : ε < 1) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) *
                (Module.finrank ℝ (augmentedDataSpan A b) : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 *
          (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((Module.finrank ℝ (augmentedDataSpan A b) : ℝ) - 1) +
              (2 / 3 : ℝ) * ε)))
    (hobjectiveBudget :
      ∀ samples,
        rowTracePositiveProb (augmentedSpanBasisMatrix A b) samples →
          rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples
              (normalEqCholeskyXHat fp n (c_hat samples) (R_hat samples)) +
            rowSampleLSObjectiveFpBudget fp s A b
              (augmentedSpanBasisMatrix A b) samples xOpt +
            lsSolutionForwardObjectiveGap
              (fl_rowSampleLSMatrixWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) A samples)
              (fl_rowSampleLSVectorWithBasisScale fp s
                (augmentedSpanBasisMatrix A b) b samples)
              (xStar samples)
              (normalEqCholeskySolverDx (m := s) fp (ATA_inv samples)
                (absATA samples) (absATb samples) (R_hat samples)
                (normalEqCholeskyXHat fp n (c_hat samples) (R_hat samples))) ≤
            ((1 + η) * (1 - ε) - (1 + ε)) *
              lsObjective A b xOpt)
    (hstar :
      ∀ samples,
        IsLeastSquaresMinimizer
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples)
          (xStar samples))
    (hInv : ∀ samples,
      IsInverse n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples))
    (hExact : ∀ samples i,
      matMulVec n
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (xStar samples) i =
          lsNormalRhs
            (fl_rowSampleLSMatrixWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) A samples)
            (fl_rowSampleLSVectorWithBasisScale fp s
              (augmentedSpanBasisMatrix A b) b samples) i)
    (habsATA : ∀ samples i j, 0 ≤ absATA samples i j)
    (habsATb : ∀ samples i, 0 ≤ absATb samples i)
    (hGram : ∀ samples,
      GramProductError n (C_hat samples)
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (absATA samples) (gamma fp s))
    (hGramVec : ∀ samples,
      GramVecError n (c_hat samples)
        (lsNormalRhs
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples))
        (absATb samples) (gamma fp s))
    (hChol : ∀ samples,
      CholeskyBackwardError n (C_hat samples) (R_hat samples)
        (gamma fp (n + 1)))
    (hR_diag : ∀ samples i, R_hat samples i i ≠ 0)
    (hγs : gammaValid fp s) (hγn1 : gammaValid fp (n + 1)) :
    1 - δ ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
          (Nat.zero_lt_of_lt hd)).eventProb
        {samples |
          lsObjective A b
              (normalEqCholeskyXHat fp n (c_hat samples) (R_hat samples)) ≤
            (1 + η) * lsObjective A b xOpt} := by
  refine
    leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_forward_error
      fp A b hd hs
      (fun samples =>
        normalEqCholeskyXHat fp n (c_hat samples) (R_hat samples))
      xStar xOpt
      (fun samples =>
        normalEqCholeskySolverDx (m := s) fp (ATA_inv samples)
          (absATA samples) (absATb samples) (R_hat samples)
          (normalEqCholeskyXHat fp n (c_hat samples) (R_hat samples)))
      hε_pos hε hδ hbudgetUpper hbudgetLower hobjectiveBudget hstar ?_ ?_
  · intro samples j
    exact
      normalEqCholeskySolverDx_nonneg (m := s) fp (ATA_inv samples)
        (absATA samples) (absATb samples) (R_hat samples)
        (normalEqCholeskyXHat fp n (c_hat samples) (R_hat samples))
        (habsATA samples) (habsATb samples) hγs hγn1 j
  · intro samples j
    exact
      normal_equations_cholesky_forward_error_certificate (m := s) fp
        (lsNormalMatrix
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples))
        (ATA_inv samples) (hInv samples)
        (lsNormalRhs
          (fl_rowSampleLSMatrixWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) A samples)
          (fl_rowSampleLSVectorWithBasisScale fp s
            (augmentedSpanBasisMatrix A b) b samples))
        (xStar samples) (hExact samples)
        (absATA samples) (absATb samples)
        (C_hat samples) (c_hat samples) (R_hat samples)
        (hGram samples) (hGramVec samples) (hChol samples)
        (hR_diag samples) hγs hγn1 j




















































end NumStability
