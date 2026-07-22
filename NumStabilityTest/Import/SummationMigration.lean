import NumStabilityTest.Import.Compatibility.Summation.Accumulator
import NumStabilityTest.Import.Compatibility.Summation.Compensated
import NumStabilityTest.Import.Compatibility.Summation.DoublyCompensated
import NumStabilityTest.Import.Compatibility.Summation.Insertion
import NumStabilityTest.Import.Compatibility.Summation.Pairwise
import NumStabilityTest.Import.Compatibility.Summation.PlusMinus
import NumStabilityTest.Import.Compatibility.Summation.Recursive
import NumStabilityTest.Import.Compatibility.Summation.Tree

/-!
# Historical summation-path smoke test

Each historical root-level import is compiled and checked in an isolated child
module, so neither canonical imports nor sibling wrappers can mask a broken
forwarding path.
-/
