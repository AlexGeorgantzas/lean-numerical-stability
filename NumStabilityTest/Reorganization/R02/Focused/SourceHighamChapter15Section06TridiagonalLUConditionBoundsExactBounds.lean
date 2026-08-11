import NumStability.Source.Higham.Chapter15.Section06.TridiagonalLUConditionBounds.ExactBounds

/-!
# Frozen route and private-normalized closure: `NumStability.Source.Higham.Chapter15.Section06.TridiagonalLUConditionBounds.ExactBounds`

Exercises the frozen declaration route together with the reviewed private
normalization. The private members re-mangle against this module and are
not addressable from here; the public members of the private reverse
closure that live here are checked instead, which is what pins the
normalization observably.
-/

#check @NumStability.Ch15Closure.H15_Theorem15_7_of_absLU_eq
#check @NumStability.Ch15Closure.H15_Theorem15_8_of_rowDiagDominant
