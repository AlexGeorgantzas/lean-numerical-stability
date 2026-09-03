import NumStability.Algorithms.Summation.Accumulator

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Summation.Accumulator`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Algorithms.Summation.Accumulator`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.accumulatorSet_self
