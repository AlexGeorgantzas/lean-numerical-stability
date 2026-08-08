import NumStability.Source.Higham.Chapter28.Section04.Pascal.Pascal
import NumStability.Source.Higham.Chapter28.Section04.Pascal.PascalCondition
import NumStability.Source.Higham.Chapter28.Section04.Pascal.PascalOscillation
import NumStability.Source.Higham.Chapter28.Section04.Pascal.PascalSpectral
import NumStability.Source.Higham.Chapter28.Section04.ReciprocalSpectrumSPD.ReciprocalSPD

/-!
# Chapter 28 Section04: exact source correspondence

Imports only the `Section04` source modules. The wave brief asks for exact
Chapter 28 source correspondence, so each printed locus must be resolvable
from its own modules without the historical facade.
-/
#check @NumStability.pascalInverseMatrix
#check @NumStability.rotatedSignedPascal
#check @NumStability.higham28SignDiagonal
#check @NumStability.opNorm2_transpose_eq
