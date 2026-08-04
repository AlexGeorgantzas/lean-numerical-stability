import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.FiniteExpectation.GinibreSignedExpectation

/-!
# GinibreSignedExpectation canonical-only test (S_GIN_FINEXP, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28GinibreSignedExpectation`
during wave W09 and must resolve from S_GIN_FINEXP alone.
-/
#check @NumStability.abs_ginibreAlternatingCount_le
#check @NumStability.ginibreAlternatingCount_add_two
#check @NumStability.ginibreAlternatingEigenvalueCount
