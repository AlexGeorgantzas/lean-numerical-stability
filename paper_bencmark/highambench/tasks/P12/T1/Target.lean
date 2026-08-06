import HighamBench.P12Definitions

namespace HighamBench

/-- P12-T1: equation (10), the nearest-addition error is no larger than the right addend. -/
theorem p12_t1_nearest_add_error_le_right
    (representable : ℝ → Prop) (x y s : ℝ)
    (hx : representable x)
    (hs : p12Nearest representable (x + y) s) :
    |s - (x + y)| ≤ |y| := by
  -- PROOF_START
  sorry

end HighamBench
