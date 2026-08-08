import NumStability.Source.Higham.Chapter28.Section01.Cauchy.Cauchy
import NumStability.Source.Higham.Chapter28.Section01.HilbertConditioning.Cauchy
import NumStability.Source.Higham.Chapter28.Section01.HilbertConditioning.HilbertCondition

/-!
# Chapter 28 Section01: exact source correspondence

Imports only the `Section01` source modules. The wave brief asks for exact
Chapter 28 source correspondence, so each printed locus must be resolvable
from its own modules without the historical facade.
-/
#check @NumStability.hilbertDelannoyTerm
#check @NumStability.hilbertCentralDelannoy
#check @NumStability.hilbertDelannoyTerm_step
#check @NumStability.sum_cauchyInverseFormula
