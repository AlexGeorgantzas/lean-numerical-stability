import NumStability.Source.Higham.Chapter24.InverseFFT

/-! COMP-02 declaration-bearing isolation check for `NumStability.Source.Higham.Chapter24.InverseFFT`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter24.InverseFFT`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.higham24_conjugateEuclidean_norm
