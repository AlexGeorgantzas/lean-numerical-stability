import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.Incidence.GinibreIncidence

/-!
# GinibreIncidence canonical-only test (S_GIN_INC, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28GinibreIncidence`
during wave W09 and must resolve from S_GIN_INC alone.
-/
#check @NumStability.unitEquivFinOne
#check @NumStability.LinearMap.lowerBlock
#check @NumStability.ginibreIncidenceChart
