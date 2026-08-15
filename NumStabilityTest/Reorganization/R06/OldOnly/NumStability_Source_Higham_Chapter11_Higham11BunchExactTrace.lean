import NumStability.Source.Higham.Chapter11.Higham11BunchExactTrace

/-!
# R06 historical-only test — `Higham11BunchExactTrace`

Imports exactly the historical path; checks its preserved public
surface (59 declarations).
-/

#check @NumStability.Higham11BunchMatrix
#check @NumStability.Higham11ExactBunchTrace
#check @NumStability.Higham11ExactBunchTrace.below
#check @NumStability.Higham11ExactBunchTrace.brecOn
#check @NumStability.Higham11ExactBunchTrace.brecOn.eq
#check @NumStability.Higham11ExactBunchTrace.brecOn.go
#check @NumStability.Higham11ExactBunchTrace.casesOn
#check @NumStability.Higham11ExactBunchTrace.ctorElim
#check @NumStability.Higham11ExactBunchTrace.ctorElimType
#check @NumStability.Higham11ExactBunchTrace.ctorIdx
#check @NumStability.Higham11ExactBunchTrace.nil
#check @NumStability.Higham11ExactBunchTrace.nil.elim
#check @NumStability.Higham11ExactBunchTrace.nil.noConfusion
#check @NumStability.Higham11ExactBunchTrace.nil.sizeOf_spec
#check @NumStability.Higham11ExactBunchTrace.noConfusion
#check @NumStability.Higham11ExactBunchTrace.noConfusionType
#check @NumStability.Higham11ExactBunchTrace.one
#check @NumStability.Higham11ExactBunchTrace.one.elim
#check @NumStability.Higham11ExactBunchTrace.one.inj
#check @NumStability.Higham11ExactBunchTrace.one.injEq
#check @NumStability.Higham11ExactBunchTrace.one.noConfusion
#check @NumStability.Higham11ExactBunchTrace.one.sizeOf_spec
#check @NumStability.Higham11ExactBunchTrace.one_active_entry_bound
#check @NumStability.Higham11ExactBunchTrace.one_pivot_lower
#check @NumStability.Higham11ExactBunchTrace.one_schur_entry_bound
#check @NumStability.Higham11ExactBunchTrace.pivotDetAbs
#check @NumStability.Higham11ExactBunchTrace.rec
#check @NumStability.Higham11ExactBunchTrace.recOn
#check @NumStability.Higham11ExactBunchTrace.stageMaxes
#check @NumStability.Higham11ExactBunchTrace.sum_widths
#check @NumStability.Higham11ExactBunchTrace.two
#check @NumStability.Higham11ExactBunchTrace.two.elim
#check @NumStability.Higham11ExactBunchTrace.two.inj
#check @NumStability.Higham11ExactBunchTrace.two.injEq
#check @NumStability.Higham11ExactBunchTrace.two.noConfusion
#check @NumStability.Higham11ExactBunchTrace.two.sizeOf_spec
#check @NumStability.Higham11ExactBunchTrace.two_active_entry_bound
#check @NumStability.Higham11ExactBunchTrace.two_indices_ne
#check @NumStability.Higham11ExactBunchTrace.two_pivot_lower
#check @NumStability.Higham11ExactBunchTrace.two_pivot_lower_alpha_sq
#check @NumStability.Higham11ExactBunchTrace.two_pivot_pos
#check @NumStability.Higham11ExactBunchTrace.two_schur_entry_bound
#check @NumStability.Higham11ExactBunchTrace.widths
#check @NumStability.higham11_1_bunchMultTwo
#check @NumStability.higham11_1_bunchMultTwo_one
#check @NumStability.higham11_1_bunchMultTwo_zero
#check @NumStability.higham11_1_bunchOneActive
#check @NumStability.higham11_1_bunchOnePerm
#check @NumStability.higham11_1_bunchOnePerm_zero
#check @NumStability.higham11_1_bunchSchurOne
#check @NumStability.higham11_1_bunchSchurOne_symmetric
#check @NumStability.higham11_1_bunchSchurTwo
#check @NumStability.higham11_1_bunchSchurTwo_symmetric
#check @NumStability.higham11_1_bunchSymmetricPermute
#check @NumStability.higham11_1_bunchSymmetricPermute_symmetric
#check @NumStability.higham11_1_bunchTwoActive
#check @NumStability.higham11_1_bunchTwoPerm
#check @NumStability.higham11_1_bunchTwoPerm_one
#check @NumStability.higham11_1_bunchTwoPerm_zero
