import NumStability.Source.Higham.Chapter15.Section02.Boyd.GlobalConvergence.ScalarCase.Iteration

/-!
# Frozen route and private-normalized closure: `NumStability.Source.Higham.Chapter15.Section02.Boyd.GlobalConvergence.ScalarCase.Iteration`

Exercises the frozen declaration route together with the reviewed private
normalization. The private members re-mangle against this module and are
not addressable from here; the public members of the private reverse
closure that live here are checked instead, which is what pins the
normalization observably.
-/

#check @NumStability.Ch15.boydScalar_basis_mem_carrier
#check @NumStability.Ch15.boydScalar_carrier_eq_basis
#check @NumStability.Ch15.boydScalar_xnext_basis_eq
#check @NumStability.Ch15.boydScalar_xnext_basis_nonneg
#check @NumStability.Ch15.boydScalar_xseq_basis_eq
#check @NumStability.Ch15.boydScalar_zof_basis_nonneg
#check @NumStability.Ch15.higham15_boyd_global_of_nonnegative_irreducibleGram_all_dimensions
#check @NumStability.Ch15.higham15_boyd_global_scalar
