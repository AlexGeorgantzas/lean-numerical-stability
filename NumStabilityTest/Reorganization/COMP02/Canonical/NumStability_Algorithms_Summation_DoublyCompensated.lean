import NumStability.Algorithms.Summation.DoublyCompensated

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Summation.DoublyCompensated`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Algorithms.Summation.DoublyCompensated`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.priestStepTrace_c
