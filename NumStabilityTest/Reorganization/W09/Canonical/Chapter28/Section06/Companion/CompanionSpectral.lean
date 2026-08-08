import NumStability.Source.Higham.Chapter28.Section06.Companion.CompanionSpectral

/-!
# CompanionSpectral canonical-only test (S_S06_COMPANION, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28CompanionSpectral`
during wave W09 and must resolve from S_S06_COMPANION alone.
-/
#check @NumStability.companion_orderTwo_isStarNormal_iff
#check @NumStability.companionSquaredSingularValues_nonneg
#check @NumStability.companionExceptionalSquaredSingularValuePlus_isRoot
