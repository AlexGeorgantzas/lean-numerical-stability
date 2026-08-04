import NumStability.Source.Higham.Chapter28.Section01.HilbertConditioning.HilbertCondition

/-!
# HilbertCondition canonical-only test (S_S01_HILBERT, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28HilbertCondition`
during wave W09 and must resolve from S_S01_HILBERT alone.
-/
#check @NumStability.hilbertDelannoyTerm
#check @NumStability.hilbertCentralDelannoy
#check @NumStability.hilbertDelannoyTerm_step
