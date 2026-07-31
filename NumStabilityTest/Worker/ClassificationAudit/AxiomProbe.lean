import NumStability.Algorithms.HighamChapter9
import NumStability.Algorithms.HighamChapter11
import NumStability.Algorithms.DotProduct
import NumStability.Source.Higham.Chapter11.Theorem07

/-!
# Axiom probes for representative public declarations

An isolated worker probe, not a root test. It prints the axiom dependencies of
one representative public declaration from each surface this lane reasons about:

* the historical Chapter 9 owner;
* the historical Chapter 11 owner;
* a reusable dot-product API this lane proposes to keep reusable;
* the existing canonical Chapter 11 Theorem 11.7 slice.

The accepted axiom set for this repository is
`[propext, Classical.choice, Quot.sound]`. This lane moves no declaration, so
these probes are a baseline record rather than a comparison: they document what
the frozen base already depends on, so the integrator can compare after the
Chapter 9 and Chapter 11 waves are implemented.
-/

#print axioms NumStability.higham9_1_exists_partialPivotChoice
#print axioms NumStability.higham11_3_oneByOne_step_factorization
#print axioms NumStability.dotProduct_factor_expansion_succ
#print axioms
  NumStability.Ch11Closure.TriGrowthInv.higham11_7_bunch_tridiagonal_actual_schedule_middle_solve
