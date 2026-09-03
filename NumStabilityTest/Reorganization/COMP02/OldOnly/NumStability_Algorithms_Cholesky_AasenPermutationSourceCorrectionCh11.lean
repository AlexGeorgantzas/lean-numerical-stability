import NumStability.Algorithms.Cholesky.AasenPermutationSourceCorrectionCh11

/-! COMP-02 declaration-bearing isolation check for `NumStability.Algorithms.Cholesky.AasenPermutationSourceCorrectionCh11`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter11.AasenPermutationSourceCorrection`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.higham11_15_unpermute_corrected_matrix
