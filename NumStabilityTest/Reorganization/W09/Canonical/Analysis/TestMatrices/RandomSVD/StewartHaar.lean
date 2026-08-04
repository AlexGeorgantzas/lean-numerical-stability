import NumStability.Analysis.TestMatrices.RandomSVD.StewartHaar

/-!
# StewartHaar canonical-only test (R_RANDOMSVD, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28StewartHaar`
during wave W09 and must resolve from R_RANDOMSVD alone.
-/
#check @NumStability.stewartTailCastEquiv
#check @NumStability.stewartInputSplitEquiv
#check @NumStability.stewartInputSplitEquiv_fst
