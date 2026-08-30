import NumStability.Analysis.FloatingPointArithmetic.Format
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results

/-!
# Higham Problem 2.9 double-rounding inputs

The local extended format and exact source value used by the Problem 2.9
double-rounding results.
-/

namespace NumStability

noncomputable section

namespace FloatingPointFormat

/-! ## Higham Problem 2.9: `sqrt (1 - 2^-53)` -/

/-- A local binary extended format with a 64-bit mantissa. The exponent range
is restricted to the neighborhood of `1`, which is the only range used by
Problem 2.9's `sqrt (1 - 2^-53)` example. -/
def binary64MantissaExtendedLocalFormat : FloatingPointFormat where
  beta := 2
  t := 64
  emin := 0
  emax := 1
  beta_ge_two := by norm_num
  t_pos := by norm_num
  emin_le_emax := by norm_num

/-- The exact real value in Higham Problem 2.9. -/
noncomputable def problem2_9Source : ℝ :=
  Real.sqrt (1 - (2 : ℝ) ^ (-53 : ℤ))

end FloatingPointFormat

end

end NumStability
