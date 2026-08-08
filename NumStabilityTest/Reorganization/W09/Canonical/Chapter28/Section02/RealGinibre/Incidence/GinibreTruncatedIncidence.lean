import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.Incidence.GinibreTruncatedIncidence

/-!
# GinibreTruncatedIncidence canonical-only test (S_GIN_INC, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28GinibreTruncatedIncidence`
during wave W09 and must resolve from S_GIN_INC alone.
-/
#check @NumStability.iUnion_ginibreIncidenceRankPieceBelow
#check @NumStability.pairwiseDisjoint_ginibreIncidenceRankPieceBelow
