import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.RandomizedLinearAlgebra.Concentration.TraceMGF.LeverageScore
import NumStability.Algorithms.RandomizedLinearAlgebra.Concentration.TraceMGF.RowNorm
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.LeverageScore.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.RowNorm.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.RowNorm.Gram
import NumStability.Analysis.FiniteProbability
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixConcentration
import NumStability.Analysis.MatrixInequalities.LiebTrace.Concavity
import NumStability.FloatingPoint.Model
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm02.RowSampling.Endpoints
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation04.RowSamplingProbability.Normalization
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation05.GramApproximation.Bounds
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation05.GramApproximation.SampledGramEndpoints
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation06.LeverageProbability.Normalization
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation07.SubspaceEmbedding.Leverage
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation07.SubspaceEmbedding.LeverageTraceMGF
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation07.SubspaceEmbedding.RowNormTraceMGF
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation07.SubspaceEmbedding.SampledGramOperatorNorm
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation08.LeastSquaresSketch.Endpoints

/-!
Relocated from the historical wave owners NumStability.Algorithms.RandNLA.LeastSquaresSketch under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

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















































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Leverage-score row sampling supplies the coordinate-space operator event
    needed by the least-squares bridge, provided the original and sketched
    objectives have the stated coordinate representation. -/
theorem leverageTraceProbability_eventProb_lsObjective_le_one_add_eta_of_coordinate_quadratic_error
    {m n d : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (hU : HasOrthonormalColumns U)
    (hd : 0 < d) (hs : 0 < (s : ℝ))
    (SA : RowTrace m s → Fin s → Fin n → ℝ)
    (Sb : RowTrace m s → Fin s → ℝ)
    (coord : (Fin n → ℝ) → Fin d → ℝ)
    (xHat : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    {ε η : ℝ} (hε_pos : 0 < ε) (hε : ε < 1)
    (hfactor : (1 + ε) / (1 - ε) ≤ 1 + η)
    (hhat :
      ∀ samples, IsLeastSquaresMinimizer (SA samples) (Sb samples)
        (xHat samples))
    (horig : ∀ x : Fin n → ℝ,
      lsObjective A b x = vecNorm2Sq (coord x))
    (hsketch : ∀ samples x,
      lsObjective (SA samples) (Sb samples) x =
        vecNorm2Sq (coord x) +
          ∑ j : Fin d, coord x j *
            matMulVec d
              (fun j k => rowSampleGram s U samples j k - idMatrix d j k)
              (coord x) j) :
    1 - 1 / ((s : ℝ) * (ε / (d : ℝ)) ^ 2) ≤
      (leverageTraceProbability (steps := s) U hU hd).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  let P := leverageTraceProbability (steps := s) U hU hd
  let E : RowTrace m s → Fin d → Fin d → ℝ :=
    fun samples j k => rowSampleGram s U samples j k - idMatrix d j k
  have hprob :
      1 - 1 / ((s : ℝ) * (ε / (d : ℝ)) ^ 2) ≤
        P.eventProb {samples | opNorm2Le (E samples) ε} := by
    simpa [P, E] using
      leverageTraceProbability_eventProb_rowSampleGram_opNorm2_error_le_epsilon
        U hU hd hs hε_pos
  exact
    eventProb_lsObjective_le_one_add_eta_of_coordinate_quadratic_error
      P A b SA Sb coord E xHat xOpt (le_of_lt hε_pos) hprob hε hfactor
      hhat horig hsketch

/-- Exact leverage-score row-sampled least-squares objective guarantee with the
    concrete Algorithm 2 sampled rows of `A` and `b`.

The only remaining representation hypothesis is the mathematical statement
that each original residual has coordinates in the rows of the leverage basis
`U`.  The sampled/sketched objective representation itself is proved locally by
`rowSampleLSObjectiveWithBasisScale_eq_coordinate_quadratic_error`. -/
theorem leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_residual_coordinates
    {m n d : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (hU : HasOrthonormalColumns U)
    (hd : 0 < d) (hs : 0 < (s : ℝ))
    (coord : (Fin n → ℝ) → Fin d → ℝ)
    (xHat : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    {ε η : ℝ} (hε_pos : 0 < ε) (hε : ε < 1)
    (hfactor : (1 + ε) / (1 - ε) ≤ 1 + η)
    (hhat :
      ∀ samples,
        IsLeastSquaresMinimizer
          (rowSampleLSMatrixWithBasisScale s U A samples)
          (rowSampleLSVectorWithBasisScale s U b samples)
          (xHat samples))
    (horig : ∀ x : Fin n → ℝ,
      lsObjective A b x = vecNorm2Sq (coord x))
    (hres : ∀ x : Fin n → ℝ, ∀ i : Fin m,
      lsResidual A b x i = ∑ a : Fin d, U i a * coord x a) :
    1 - 1 / ((s : ℝ) * (ε / (d : ℝ)) ^ 2) ≤
      (leverageTraceProbability (steps := s) U hU hd).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_lsObjective_le_one_add_eta_of_coordinate_quadratic_error
      A b U hU hd hs
      (fun samples => rowSampleLSMatrixWithBasisScale s U A samples)
      (fun samples => rowSampleLSVectorWithBasisScale s U b samples)
      coord xHat xOpt hε_pos hε hfactor hhat horig
      (fun samples x =>
        rowSampleLSObjectiveWithBasisScale_eq_coordinate_quadratic_error
          s A b U samples coord hres x)

/-- Exact leverage-score row-sampled least-squares objective guarantee using
    canonical residual coordinates.

This removes the arbitrary coordinate map from
`leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_residual_coordinates`.
The remaining mathematical condition is that every residual `A x - b` lies in
the column span of the orthonormal-column matrix `U`.  Constructing such a `U`
from an augmented residual space is the separate QR/SVD/rank foundation. -/
theorem leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_residualsInColumnSpace
    {m n d : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (hU : HasOrthonormalColumns U)
    (hd : 0 < d) (hs : 0 < (s : ℝ))
    (xHat : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    {ε η : ℝ} (hε_pos : 0 < ε) (hε : ε < 1)
    (hfactor : (1 + ε) / (1 - ε) ≤ 1 + η)
    (hhat :
      ∀ samples,
        IsLeastSquaresMinimizer
          (rowSampleLSMatrixWithBasisScale s U A samples)
          (rowSampleLSVectorWithBasisScale s U b samples)
          (xHat samples))
    (hcol : ResidualsInColumnSpace A b U) :
    1 - 1 / ((s : ℝ) * (ε / (d : ℝ)) ^ 2) ≤
      (leverageTraceProbability (steps := s) U hU hd).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_residual_coordinates
      A b U hU hd hs (residualCoordinates A b U) xHat xOpt hε_pos hε
      hfactor hhat
      (fun x =>
        lsObjective_eq_vecNorm2Sq_residualCoordinates_of_residualsInColumnSpace
          A b U hU hcol x)
      (fun x i => hcol x i)

/-- Exact leverage-score row-sampled least-squares objective guarantee using
    the orthonormal basis of the augmented data span `span{columns(A), b}`.

This closes the low-dimensional basis-construction dependency for equation
(8): the leverage dimension is now the explicit finite dimension of the
augmented data span.  The hypothesis `hd` rules out the degenerate zero-span
case, where the equation (6) leverage denominator would be zero. -/
theorem leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan
    {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hd : 0 < Module.finrank ℝ (augmentedDataSpan A b))
    (hs : 0 < (s : ℝ))
    (xHat : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    {ε η : ℝ} (hε_pos : 0 < ε) (hε : ε < 1)
    (hfactor : (1 + ε) / (1 - ε) ≤ 1 + η)
    (hhat :
      ∀ samples,
        IsLeastSquaresMinimizer
          (rowSampleLSMatrixWithBasisScale s
            (augmentedSpanBasisMatrix A b) A samples)
          (rowSampleLSVectorWithBasisScale s
            (augmentedSpanBasisMatrix A b) b samples)
          (xHat samples)) :
    1 - 1 / ((s : ℝ) *
        (ε / (Module.finrank ℝ (augmentedDataSpan A b) : ℝ)) ^ 2) ≤
      (leverageTraceProbability (steps := s)
          (augmentedSpanBasisMatrix A b)
          (hasOrthonormalColumns_augmentedSpanBasisMatrix A b) hd).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_residualsInColumnSpace
      A b (augmentedSpanBasisMatrix A b)
      (hasOrthonormalColumns_augmentedSpanBasisMatrix A b) hd hs
      xHat xOpt hε_pos hε hfactor hhat
      (residualsInColumnSpace_augmentedSpanBasisMatrix A b)

























































































/-- Concrete identity-basis specialization of the exact leverage-score
    row-sampled least-squares objective guarantee.

With \(U=I_m\), equation (6) gives uniform row probabilities and every residual
is automatically in the span of `U`.  This closes a fully concrete finite-row
instance of the least-squares bridge.  It is intentionally weaker than the
survey's low-dimensional augmented-basis theorem, where \(d\) should be the
rank of the residual subspace rather than \(m\). -/
theorem leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_idBasis
    {m n : ℕ} {s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m) (hs : 0 < (s : ℝ))
    (xHat : RowTrace m s → Fin n → ℝ) (xOpt : Fin n → ℝ)
    {ε η : ℝ} (hε_pos : 0 < ε) (hε : ε < 1)
    (hfactor : (1 + ε) / (1 - ε) ≤ 1 + η)
    (hhat :
      ∀ samples,
        IsLeastSquaresMinimizer
          (rowSampleLSMatrixWithBasisScale s (idMatrix m) A samples)
          (rowSampleLSVectorWithBasisScale s (idMatrix m) b samples)
          (xHat samples)) :
    1 - 1 / ((s : ℝ) * (ε / (m : ℝ)) ^ 2) ≤
      (leverageTraceProbability (steps := s) (idMatrix m)
          (hasOrthonormalColumns_idMatrix m) hm).eventProb
        {samples |
          lsObjective A b (xHat samples) ≤
            (1 + η) * lsObjective A b xOpt} := by
  exact
    leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_residualsInColumnSpace
      A b (idMatrix m) (hasOrthonormalColumns_idMatrix m) hm hs
      xHat xOpt hε_pos hε hfactor hhat
      (residualsInColumnSpace_idMatrix A b)

end NumStability
