import NumStability.Algorithms.Summation.Accumulator
import NumStability.Algorithms.Summation.Compensated
import NumStability.Algorithms.Summation.DoublyCompensated
import NumStability.Algorithms.Summation.Insertion
import NumStability.Algorithms.Summation.Insertion.ActiveList
import NumStability.Algorithms.Summation.Insertion.Executor
import NumStability.Algorithms.Summation.Insertion.RunningError
import NumStability.Algorithms.Summation.Insertion.Schedule
import NumStability.Algorithms.Summation.Insertion.ScheduleExecution
import NumStability.Algorithms.Summation.Pairwise
import NumStability.Algorithms.Summation.Pairwise.Core
import NumStability.Algorithms.Summation.PlusMinus
import NumStability.Algorithms.Summation.Recursive
import NumStability.Algorithms.Summation.Recursive.Core
import NumStability.Algorithms.Summation.Tree
import NumStability.Algorithms.Summation.Tree.Balanced
import NumStability.Algorithms.Summation.Tree.Core
import NumStability.Algorithms.Summation.Tree.Chain
import NumStability.Source.Higham.Chapter04.Problem03
import NumStability.Source.Higham.Chapter04.Section01.InsertionExamples
import NumStability.Source.Higham.Chapter04.Section01.PairwiseSixTerm

/-!
# Canonical summation-path smoke test

Every canonical algorithm target and refined tree layer is imported directly,
independently of the historical forwarding paths.
-/

#check NumStability.fl_recursiveSum
#check NumStability.fl_kahanSum
#check NumStability.fl_insertionSumList
#check NumStability.InsertionScheduleTree.GreedyInsertionTree.exactMergeCost_le
#check NumStability.fl_insertionPowersFour_eq_recursiveSum
#check NumStability.SumTree.backward_error
#check NumStability.SumTree.balancedTree
#check NumStability.SumTree.chainTreeSucc_eval_eq_recursiveSum
#check NumStability.recursiveSum_problem43_abs_error_bound
#check NumStability.fl_pairwiseSumSixDisplayed
