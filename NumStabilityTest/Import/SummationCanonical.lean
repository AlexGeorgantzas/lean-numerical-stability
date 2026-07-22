import NumStability.Algorithms.Summation.Accumulator
import NumStability.Algorithms.Summation.Compensated
import NumStability.Algorithms.Summation.DoublyCompensated
import NumStability.Algorithms.Summation.Insertion
import NumStability.Algorithms.Summation.Pairwise
import NumStability.Algorithms.Summation.PlusMinus
import NumStability.Algorithms.Summation.Recursive
import NumStability.Algorithms.Summation.Tree
import NumStability.Algorithms.Summation.Tree.Balanced
import NumStability.Algorithms.Summation.Tree.Core
import NumStability.Algorithms.Summation.Tree.RecursiveBridge

/-!
# Canonical summation-path smoke test

Every canonical algorithm target and refined tree layer is imported directly,
independently of the historical forwarding paths.
-/

#check NumStability.fl_recursiveSum
#check NumStability.fl_kahanSum
#check NumStability.fl_insertionSumList
#check NumStability.SumTree.backward_error
#check NumStability.SumTree.balancedTree
#check NumStability.SumTree.chainTreeSucc_eval_eq_recursiveSum
