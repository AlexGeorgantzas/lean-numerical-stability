import NumStability.Source.Higham.Chapter15.Problem06.TridiagonalInverseNorm.Recurrences.EntryFormulas

/-!
# Frozen route and private-normalized closure: `NumStability.Source.Higham.Chapter15.Problem06.TridiagonalInverseNorm.Recurrences.EntryFormulas`

Exercises the frozen declaration route together with the reviewed private
normalization. The private members re-mangle against this module and are
not addressable from here; the public members of the private reverse
closure that live here are checked instead, which is what pins the
normalization observably.
-/

#check @NumStability.Higham15Problem15_6.tridiag_mulVec_entry
#check @NumStability.Higham15Problem15_6.tridiag_vecMul_entry
