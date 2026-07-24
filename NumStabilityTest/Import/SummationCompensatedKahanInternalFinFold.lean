import NumStability.Algorithms.Summation.Compensated.Kahan.Internal.FinFold

/-!
# Kahan internal finite-fold smoke test

Checks that the unsupported owner-local bridge remains directly importable by
the Affine and Coupled implementation modules.
-/

#check NumStability.Compensated.Kahan.Internal.listFoldlOfFn_eq_finFoldl
