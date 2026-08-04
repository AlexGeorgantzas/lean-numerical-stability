import NumStability.Analysis.TestMatrices.Hilbert.Exact
import NumStability.Analysis.TestMatrices.Pascal.Exact
import NumStability.Source.Higham.Chapter28.Equation01.HilbertInverse.Exact
import NumStability.Source.Higham.Chapter28.Equation02.ExactHilbertDeterminant.Exact
import NumStability.Source.Higham.Chapter28.Equation03.HilbertCholeskyFactor.Exact

/-!
# Higham28Exact: the mandated split, all sides at once

B0009 forbids classifying `Higham28Exact` wholesale, so its declarations
were split across 2 reusable and 3 Chapter 28 source
destinations. This test imports both sides and nothing else, so a
declaration routed to the wrong side of the split fails to resolve here.
-/
#check @NumStability.hilbert_gram_sum
#check @NumStability.hilbertRInvAbsCore
#check @NumStability.hilbertRNat_diag_sq
#check @NumStability.hilbert_det_formula
#check @NumStability.hilbertGramTelescoper
#check @NumStability.hilbertDetFormula_succ
