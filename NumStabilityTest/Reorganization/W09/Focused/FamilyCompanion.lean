import NumStability.Analysis.TestMatrices.Companion.Basic
import NumStability.Analysis.TestMatrices.Companion.Companion
import NumStability.Analysis.TestMatrices.Companion.CompanionSpectral
import NumStability.Analysis.TestMatrices.Companion.Contracts

/-!
# Companion: reusable test-matrix analysis, standing alone

Imports only the reusable `Companion` modules. This is the family boundary the
wave brief asks for: reusable test-matrix analysis that a later wave can use
without importing Chapter 28 source correspondence.
-/
#check @NumStability.companionMatrix
#check @NumStability.companionOfMatrix
#check @NumStability.companionRankMinor
#check @NumStability.companionEigenvector
