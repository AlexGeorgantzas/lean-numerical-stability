import NumStability.Analysis.TestMatrices.Pascal.Contracts

/-!
# Contracts canonical-only test (R_PASCAL, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28Contracts`
during wave W09 and must resolve from R_PASCAL alone.
-/
#check @NumStability.pascalLastBasis
#check @NumStability.pascalLastKernel
#check @NumStability.pascalLastKernel_last
