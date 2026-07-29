import NumStability.Algorithms.LinearSystems.LeastSquares.GramBasis

/-!
# GramBasis canonical-only import smoke test

Imports exactly one canonical module so no sibling import can supply
the declarations checked below.
-/

#check @NumStability.rectRightGramBasisOrderedEquiv
#check @NumStability.rectRightGramBasisSingularValue_pos_of_rectMatMulVec_injective
#check @NumStability.rectRightGramLeftSingularFromEigenbasis_transpose_action_of_pos
