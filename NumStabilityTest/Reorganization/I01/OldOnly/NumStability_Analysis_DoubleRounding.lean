import NumStability.Analysis.DoubleRounding

/-!
# I01 historical-only test: Analysis.DoubleRounding

Imports only the retained historical wrapper and checks both declarations
moved to `Counterexample.Inputs`.
-/

#check @NumStability.FloatingPointFormat.binary64MantissaExtendedLocalFormat
#check @NumStability.FloatingPointFormat.problem2_9Source
