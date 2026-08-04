import NumStability.Analysis.TestMatrices.Cauchy.Basic
import NumStability.Analysis.TestMatrices.Companion.Basic
import NumStability.Analysis.TestMatrices.Hilbert.Basic
import NumStability.Analysis.TestMatrices.Orthogonal.Basic
import NumStability.Source.Higham.Chapter28.Equation01.HilbertInverse.Basic
import NumStability.Source.Higham.Chapter28.Equation02.ExactHilbertDeterminant.Basic
import NumStability.Source.Higham.Chapter28.Equation03.HilbertCholeskyFactor.Basic
import NumStability.Source.Higham.Chapter28.Equation04.HilbertCholeskyInverse.Basic

/-!
# Higham28: the mandated split, all sides at once

B0009 forbids classifying `Higham28` wholesale, so its declarations
were split across 7 reusable and 4 Chapter 28 source
destinations. This test imports both sides and nothing else, so a
declaration routed to the wrong side of the split fails to resolve here.
-/
#check @NumStability.hilbertRNat
#check @NumStability.cauchyMatrix
#check @NumStability.hilbertRCore
#check @NumStability.hilbertMatrix
#check @NumStability.altChooseShift
#check @NumStability.hilbertRInvNat
