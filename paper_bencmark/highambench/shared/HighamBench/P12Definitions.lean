import Mathlib.Data.Real.Basic

namespace HighamBench

/-- A condition-neutral nearest-rounding relation into a representable set. -/
def p12Nearest (representable : ℝ → Prop) (exact rounded : ℝ) : Prop :=
  representable rounded ∧
    ∀ candidate, representable candidate →
      |exact - rounded| ≤ |exact - candidate|

/-- The three returned/intermediate values of Dekker's FastTwoSum algorithm. -/
structure P12FastTwoSumTrace where
  s : ℝ
  t : ℝ
  e : ℝ

/-- The values needed to state the exact ThreeProduct composition in Lemma 4. -/
structure P12ThreeProductTrace where
  th : ℝ
  tl : ℝ
  s1 : ℝ
  a2 : ℝ
  a3 : ℝ
  a4 : ℝ
  s2 : ℝ
  t : ℝ
  r : ℝ
  s3 : ℝ

end HighamBench
