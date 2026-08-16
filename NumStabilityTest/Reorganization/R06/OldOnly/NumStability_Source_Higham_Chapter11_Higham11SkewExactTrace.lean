import NumStability.Source.Higham.Chapter11.Higham11SkewExactTrace

/-!
# R06 historical-only test — `Higham11SkewExactTrace`

Imports exactly the historical path; checks its preserved public
surface (67 declarations).
-/

#check @NumStability.Higham11ExactSkewTrace
#check @NumStability.Higham11ExactSkewTrace.below
#check @NumStability.Higham11ExactSkewTrace.brecOn
#check @NumStability.Higham11ExactSkewTrace.brecOn.eq
#check @NumStability.Higham11ExactSkewTrace.brecOn.go
#check @NumStability.Higham11ExactSkewTrace.casesOn
#check @NumStability.Higham11ExactSkewTrace.ctorElim
#check @NumStability.Higham11ExactSkewTrace.ctorElimType
#check @NumStability.Higham11ExactSkewTrace.ctorIdx
#check @NumStability.Higham11ExactSkewTrace.firstPerm
#check @NumStability.Higham11ExactSkewTrace.firstPerm_injective
#check @NumStability.Higham11ExactSkewTrace.firstPermuted_isSkew
#check @NumStability.Higham11ExactSkewTrace.growthUpdates
#check @NumStability.Higham11ExactSkewTrace.isSkew
#check @NumStability.Higham11ExactSkewTrace.nil
#check @NumStability.Higham11ExactSkewTrace.nil.elim
#check @NumStability.Higham11ExactSkewTrace.nil.noConfusion
#check @NumStability.Higham11ExactSkewTrace.nil.sizeOf_spec
#check @NumStability.Higham11ExactSkewTrace.noAction
#check @NumStability.Higham11ExactSkewTrace.noAction.elim
#check @NumStability.Higham11ExactSkewTrace.noAction.inj
#check @NumStability.Higham11ExactSkewTrace.noAction.injEq
#check @NumStability.Higham11ExactSkewTrace.noAction.noConfusion
#check @NumStability.Higham11ExactSkewTrace.noAction.sizeOf_spec
#check @NumStability.Higham11ExactSkewTrace.noConfusion
#check @NumStability.Higham11ExactSkewTrace.noConfusionType
#check @NumStability.Higham11ExactSkewTrace.rec
#check @NumStability.Higham11ExactSkewTrace.recOn
#check @NumStability.Higham11ExactSkewTrace.singleton
#check @NumStability.Higham11ExactSkewTrace.singleton.elim
#check @NumStability.Higham11ExactSkewTrace.singleton.noConfusion
#check @NumStability.Higham11ExactSkewTrace.singleton.sizeOf_spec
#check @NumStability.Higham11ExactSkewTrace.singleton_maxEntryNorm_eq_zero
#check @NumStability.Higham11ExactSkewTrace.stageGrowthFactor_printed_bound
#check @NumStability.Higham11ExactSkewTrace.stageMax_le_growth_pow
#check @NumStability.Higham11ExactSkewTrace.stageMax_le_printed_sqrt_growth
#check @NumStability.Higham11ExactSkewTrace.stageMaxes
#check @NumStability.Higham11ExactSkewTrace.stageMaxes_eq_zero_of_dimension_le_one
#check @NumStability.Higham11ExactSkewTrace.two
#check @NumStability.Higham11ExactSkewTrace.two.elim
#check @NumStability.Higham11ExactSkewTrace.two.inj
#check @NumStability.Higham11ExactSkewTrace.two.injEq
#check @NumStability.Higham11ExactSkewTrace.two.noConfusion
#check @NumStability.Higham11ExactSkewTrace.two.sizeOf_spec
#check @NumStability.Higham11ExactSkewTrace.twoPivots
#check @NumStability.Higham11ExactSkewTrace.two_mul_growthUpdates_le_sub_two
#check @NumStability.Higham11ExactSkewTrace.two_mul_twoPivots_le_dimension
#check @NumStability.Higham11ExactSkewTrace.widths
#check @NumStability.Higham11ExactSkewTrace.widths_sum
#check @NumStability.Higham11SkewMatrix
#check @NumStability.higham11_9_exactSkewTrace
#check @NumStability.higham11_9_exactSkewTrace_printed_unit_multiplier_claim_is_false
#check @NumStability.higham11_9_noAction_offDiagonal_zero
#check @NumStability.higham11_9_nonempty_exactSkewTrace
#check @NumStability.higham11_9_skewActualPerm_one_of_pos
#check @NumStability.higham11_9_skewActualPerm_zero_of_pos
#check @NumStability.higham11_9_skewActualPermuted_pivot_eq_selected
#check @NumStability.higham11_9_skewActualPermuted_pivot_ne_zero
#check @NumStability.higham11_9_skewActualPermuted_trailing_column_zero_le_pivot
#check @NumStability.higham11_9_skewActualSchurTwo
#check @NumStability.higham11_9_skewActualSchurTwo_entry_bound
#check @NumStability.higham11_9_skewActualSchurTwo_isSkew
#check @NumStability.higham11_9_skewActualSchurTwo_maxEntryNorm_le
#check @NumStability.higham11_9_skewNoActionTail
#check @NumStability.higham11_9_skewNoActionTail_isSkew
#check @NumStability.higham11_9_skewNoActionTail_maxEntryNorm_le
#check @NumStability.higham11_9_skewPivot_dominates_selected_column
