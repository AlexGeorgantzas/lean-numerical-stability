import NumStability.Analysis.TestMatrices.Pascal.Basic
import NumStability.Analysis.TestMatrices.Pascal.Contracts
import NumStability.Analysis.TestMatrices.Pascal.Exact
import NumStability.Analysis.TestMatrices.Pascal.PascalDualFlag
import NumStability.Analysis.TestMatrices.Pascal.PascalOscillation
import NumStability.Analysis.TestMatrices.Pascal.PascalOscillationCore
import NumStability.Analysis.TestMatrices.Pascal.PascalSpectral
import NumStability.Analysis.TestMatrices.Pascal.PascalTotalPositivity

/-!
# Pascal: reusable test-matrix analysis, standing alone

Imports only the reusable `Pascal` modules. This is the family boundary the
wave brief asks for: reusable test-matrix analysis that a later wave can use
without importing Chapter 28 source correspondence.
-/
#check @NumStability.pascalLower
#check @NumStability.pascalMatrix
#check @NumStability.signedPascal
#check @NumStability.compoundMatrix
