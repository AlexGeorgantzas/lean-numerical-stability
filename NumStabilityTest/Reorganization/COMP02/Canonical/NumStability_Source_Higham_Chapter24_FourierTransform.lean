import NumStability.Source.Higham.Chapter24.FourierTransform

/-! COMP-02 declaration-bearing isolation check for `NumStability.Source.Higham.Chapter24.FourierTransform`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter24.FourierTransform`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.higham24_dftInverse_mul_dft
