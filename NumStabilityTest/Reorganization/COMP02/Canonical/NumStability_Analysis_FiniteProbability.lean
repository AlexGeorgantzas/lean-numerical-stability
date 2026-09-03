import NumStability.Analysis.FiniteProbability

/-! COMP-02 declaration-bearing isolation check for `NumStability.Analysis.FiniteProbability`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Analysis.FiniteProbability`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.FiniteProbability.ext
