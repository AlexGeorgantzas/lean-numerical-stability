import NumStability.Source.Higham.Chapter15.Section02.Boyd.LocalConvergence.ConstrainedLagrangian.Differentiation

/-!
# Frozen route and private-normalized closure: `NumStability.Source.Higham.Chapter15.Section02.Boyd.LocalConvergence.ConstrainedLagrangian.Differentiation`

Exercises the frozen declaration route together with the reviewed private
normalization. The private members re-mangle against this module and are
not addressable from here; the public members of the private reverse
closure that live here are checked instead, which is what pins the
normalization observably.
-/

#check @NumStability.Ch15.boydConstrainedLagrangianFirst_hasDerivAt
#check @NumStability.Ch15.boydConstrainedLagrangianLine_hasDerivAt
#check @NumStability.Ch15.boydConstrainedSecondVariation_is_second_derivative
