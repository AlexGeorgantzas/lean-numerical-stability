import NumStability.Analysis.TestMatrices.Cauchy.Basic
import NumStability.Analysis.TestMatrices.Cauchy.Cauchy
import NumStability.Analysis.TestMatrices.Cauchy.Contracts

/-!
# Cauchy: reusable test-matrix analysis, standing alone

Imports only the reusable `Cauchy` modules. This is the family boundary the
wave brief asks for: reusable test-matrix analysis that a later wave can use
without importing Chapter 28 source correspondence.
-/
#check @NumStability.cauchyLower
#check @NumStability.cauchyUpper
#check @NumStability.cauchyMatrix
#check @NumStability.cauchyChoTerm
