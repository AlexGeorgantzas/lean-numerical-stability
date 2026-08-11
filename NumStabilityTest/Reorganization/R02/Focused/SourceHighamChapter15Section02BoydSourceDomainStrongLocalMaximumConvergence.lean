import NumStability.Source.Higham.Chapter15.Section02.Boyd.SourceDomain.StrongLocalMaximum.Convergence

/-!
# Frozen route and private-normalized closure: `NumStability.Source.Higham.Chapter15.Section02.Boyd.SourceDomain.StrongLocalMaximum.Convergence`

Exercises the frozen declaration route together with the reviewed private
normalization. The private members re-mangle against this module and are
not addressable from here; the public members of the private reverse
closure that live here are checked instead, which is what pins the
normalization observably.
-/

#check @NumStability.Ch15.IsBoydConcreteSourceStrongLocalMaximum.hasActualSecondDerivativeGap
#check @NumStability.Ch15.higham15_boyd_source_linear_of_strongLocalMaximum_subsequentialLimit
#check @NumStability.Ch15.rect_general_boyd_concrete_source_local_linear
#check @NumStability.Ch15.rect_general_boyd_concrete_source_local_linear_uniform
