/-!
# Worker smoke: historical Chapter 9 surface

This isolated worker module checks that the historical Chapter 9 import stays
available while the proposal is reviewed. It is deliberately not in a root
test aggregate.
-/

import NumStability.Algorithms.HighamChapter9
import NumStability.Algorithms.LinearSystems.LU

example : True := by trivial
