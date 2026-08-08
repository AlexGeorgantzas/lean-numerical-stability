import NumStability.Algorithms.TestMatrices.Higham28Companion
import NumStability.Algorithms.TestMatrices.Higham28CompanionSpectral
import NumStability.Algorithms.TestMatrices.Higham28Contracts
import NumStability.Algorithms.TestMatrices.Higham28GaussianQRHaar
import NumStability.Algorithms.TestMatrices.Higham28Ginibre
import NumStability.Algorithms.TestMatrices.Higham28GinibreAbsoluteDetRecurrence
import NumStability.Algorithms.TestMatrices.Higham28GinibreCharacteristicProduct
import NumStability.Algorithms.TestMatrices.Higham28GinibreComplexPairs
import NumStability.Algorithms.TestMatrices.Higham28GinibreCorollary31Factor
import NumStability.Algorithms.TestMatrices.Higham28GinibreDeterminantIntegral
import NumStability.Algorithms.TestMatrices.Higham28GinibreDeterminantMoment
import NumStability.Algorithms.TestMatrices.Higham28GinibreDimensionTwo

/-!
# The retained closure, through the facades that keep it

165 private declarations cannot move: a Lean private name is mangled with its
defining module, so relocating one would rename it. Their command-level
closure -- 562 declarations, including the 28 file-scoped `local instance`
declarations and everything that uses them -- is retained at the historical
owner. This test imports those facades and checks retained *public*
declarations; the private ones are deliberately never referenced, because they
are invisible outside their defining module, which is exactly why they stayed.
-/
#check @NumStability.measurable_gaussianQRQ
#check @NumStability.companionMatrix_charpoly
#check @NumStability.companionOfMatrix_charpoly
#check @NumStability.toeplitzSineVector_ne_zero
#check @NumStability.instMeasurableSpaceRSqMat_2
#check @NumStability.instMeasurableSpaceRSqMat_5
