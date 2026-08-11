import NumStability.Source.Higham.Chapter15.Theorem09.Ikebe.IrreducibleRightInverse.RankOneStructure

/-!
# Frozen route and private-normalized closure: `NumStability.Source.Higham.Chapter15.Theorem09.Ikebe.IrreducibleRightInverse.RankOneStructure`

Exercises the frozen declaration route together with the reviewed private
normalization. The private members re-mangle against this module and are
not addressable from here; the public members of the private reverse
closure that live here are checked instead, which is what pins the
normalization observably.
-/

#check @NumStability.Ch15IkebeClosure.H15_Theorem15_9_of_irreducible_rightInverse
