import NumStability.Algorithms.HighamChapter4KaoWangScope

/-!
# Historical Higham--Kao--Wang scope import test

This old-only smoke test verifies the direct compatibility wrapper without a
canonical sibling import.
-/

#check NumStability.HighamChapter4KaoWang.IntegerAdditionTree
#check NumStability.HighamChapter4KaoWang.higham43_runningBudget_exactArithmetic_eq_kaoWangCost
#check NumStability.HighamChapter4KaoWang.higham43_computedBudget_ne_kaoWangExactCost_witness
#check NumStability.HighamChapter4KaoWang.ReductionCorrect
