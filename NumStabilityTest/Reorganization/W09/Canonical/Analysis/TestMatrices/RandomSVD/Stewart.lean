import NumStability.Analysis.TestMatrices.RandomSVD.Stewart

/-!
# Stewart canonical-only test (R_RANDOMSVD, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28Stewart`
during wave W09 and must resolve from R_RANDOMSVD alone.
-/
#check @NumStability.stewartRDiagonal
#check @NumStability.stewartSignDiagonal
#check @NumStability.StewartGaussianInputs
