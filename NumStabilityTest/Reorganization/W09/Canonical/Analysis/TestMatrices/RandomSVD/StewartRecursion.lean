import NumStability.Analysis.TestMatrices.RandomSVD.StewartRecursion

/-!
# StewartRecursion canonical-only test (R_RANDOMSVD, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28StewartRecursion`
during wave W09 and must resolve from R_RANDOMSVD alone.
-/
#check @NumStability.split_succ
#check @NumStability.finCastEquiv_val
#check @NumStability.tail_input_apply
