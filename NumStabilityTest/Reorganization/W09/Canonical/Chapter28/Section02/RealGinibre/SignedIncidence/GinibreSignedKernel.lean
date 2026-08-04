import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.SignedIncidence.GinibreSignedKernel

/-!
# GinibreSignedKernel canonical-only test (S_GIN_SIGNED, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28GinibreSignedKernel`
during wave W09 and must resolve from S_GIN_SIGNED alone.
-/
#check @NumStability.ginibreOrderedGaussianKernelMoment
#check @NumStability.ginibreOrderedGaussianKernelIntegrand
#check @NumStability.ginibreOrderedGaussianKernelMoment_sub_eq
