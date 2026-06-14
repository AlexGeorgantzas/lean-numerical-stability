-- Analysis/FusedMultiplyAdd.lean
--
-- Finite single-rounding FMA surface for Higham Chapter 2, §2.9.

import LeanFpAnalysis.FP.Analysis.FloatingPointArithmetic

namespace LeanFpAnalysis.FP

noncomputable section

/-!
# Fused Multiply-Add

Higham Chapter 2, §2.9 notes that a fused multiply-add forms `x*y + z` as
though it were a single floating-point operation, with one rounding at the end.
This file records the finite real-valued theorem surface for that statement.
It is not a full IEEE FMA semantics: exception flags, signed zeros, infinities,
NaNs, traps, and payload behavior remain in the IEEE ledger.
-/

/-- Exact real value computed before the single final FMA rounding. -/
def fusedMultiplyAddExact (x y z : ℝ) : ℝ :=
  x * y + z

namespace FloatingPointFormat

/-- Source-facing finite round-to-even FMA: round the exact `x*y+z` once at the
end. -/
def finiteRoundToEvenFMA (fmt : FloatingPointFormat) (x y z : ℝ) : ℝ :=
  fmt.finiteRoundToEven (fusedMultiplyAddExact x y z)

/-- Source-facing finite FMA parameterized by an IEEE rounding mode. -/
def finiteRoundToModeFMA
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (x y z : ℝ) : ℝ :=
  fmt.finiteRoundToMode mode (fusedMultiplyAddExact x y z)

theorem finiteRoundToModeFMA_nearestEven
    (fmt : FloatingPointFormat) (x y z : ℝ) :
    fmt.finiteRoundToModeFMA IeeeRoundingMode.nearestEven x y z =
      fmt.finiteRoundToEvenFMA x y z := rfl

/-- The finite FMA wrapper is a single final rounding of the exact product-plus
addend. -/
theorem finiteRoundToEvenFMA_eq_round_exact
    (fmt : FloatingPointFormat) (x y z : ℝ) :
    fmt.finiteRoundToEvenFMA x y z =
      fmt.finiteRoundToEven (x * y + z) := rfl

/-- If the exact fused result is representable in the finite system, the
finite FMA returns it exactly. -/
theorem finiteRoundToEvenFMA_eq_exact_of_finiteSystem
    {fmt : FloatingPointFormat} {x y z : ℝ}
    (hxyz : fmt.finiteSystem (fusedMultiplyAddExact x y z)) :
    fmt.finiteRoundToEvenFMA x y z = fusedMultiplyAddExact x y z := by
  exact fmt.finiteRoundToEven_eq_self_of_finiteSystem hxyz

/-- In the finite-normal, non-exceptional case, the single-rounded finite FMA
satisfies the strict standard-model relative-error equation. -/
theorem finiteRoundToEvenFMA_standardModel_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x y z : ℝ}
    (hxyz : fmt.finiteNormalRange (fusedMultiplyAddExact x y z)) :
    ∃ δ : ℝ,
      |δ| < fmt.unitRoundoff ∧
        fmt.finiteRoundToEvenFMA x y z =
          fusedMultiplyAddExact x y z * (1 + δ) := by
  rcases
    fmt.finiteRoundToEven_signedRelErrorWitness_lt_of_finiteNormalRange
      hxyz with
    ⟨δ, _hround, hδ, hwit⟩
  exact
    ⟨δ, hδ,
      by simpa [finiteRoundToEvenFMA, fusedMultiplyAddExact,
        signedRelErrorWitness] using hwit⟩

theorem finiteRoundToEvenFMA_inverseRelErrorWitness_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x y z : ℝ}
    (hxyz : fmt.finiteNormalRange (fusedMultiplyAddExact x y z)) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite (fusedMultiplyAddExact x y z)
          (fmt.finiteRoundToEvenFMA x y z) ∧
        |δ| ≤ fmt.unitRoundoff ∧
          inverseRelErrorWitness (fmt.finiteRoundToEvenFMA x y z)
            (fusedMultiplyAddExact x y z) δ := by
  rcases
    fmt.finiteRoundToEven_inverseRelErrorWitness_of_finiteNormalRange
      hxyz with
    ⟨δ, hround, hδ, hwit⟩
  exact
    ⟨δ,
      by simpa [finiteRoundToEvenFMA, fusedMultiplyAddExact] using hround,
      hδ,
      by simpa [finiteRoundToEvenFMA, fusedMultiplyAddExact] using hwit⟩

end FloatingPointFormat

end

end LeanFpAnalysis.FP
