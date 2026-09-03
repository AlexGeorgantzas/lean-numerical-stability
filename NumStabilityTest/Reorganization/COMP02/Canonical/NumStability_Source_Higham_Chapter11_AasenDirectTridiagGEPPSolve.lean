import NumStability.Source.Higham.Chapter11.AasenDirectTridiagGEPPSolve

/-! COMP-02 declaration-bearing isolation check for `NumStability.Source.Higham.Chapter11.AasenDirectTridiagGEPPSolve`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.AasenDirectTridiagGEPPSolve`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.Ch11Closure.AasenDirectGEPP.aasenDirectMiddleBudget_of_envelope
