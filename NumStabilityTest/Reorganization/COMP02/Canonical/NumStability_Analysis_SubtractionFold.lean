import NumStability.Analysis.SubtractionFold

/-! COMP-02 declaration-bearing isolation check for `NumStability.Analysis.SubtractionFold`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Analysis.SubtractionFold`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.fl_sub_fold_unroll
