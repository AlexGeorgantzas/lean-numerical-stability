import NumStability.Analysis.MatrixSpectral

/-! COMP-02 declaration-bearing isolation check for `NumStability.Analysis.MatrixSpectral`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Analysis.MatrixSpectral`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.finiteMatrixExp_symmetric
