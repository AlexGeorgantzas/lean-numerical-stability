import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.SignedIncidence.GinibreSignedRankTransfer

/-!
# GinibreSignedRankTransfer canonical-only test (S_GIN_SIGNED, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28GinibreSignedRankTransfer`
during wave W09 and must resolve from S_GIN_SIGNED alone.
-/
#check @NumStability.ginibreIncidenceRankPieceBelow
#check @NumStability.sum_fin_ite_lt_eq_ginibreAlternatingCount
#check @NumStability.sum_fin_ite_lt_eq_ginibreAlternatingPairCount
