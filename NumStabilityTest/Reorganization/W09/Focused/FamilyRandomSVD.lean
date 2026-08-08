import NumStability.Analysis.TestMatrices.RandomSVD.Basic
import NumStability.Analysis.TestMatrices.RandomSVD.Stewart
import NumStability.Analysis.TestMatrices.RandomSVD.StewartHaar
import NumStability.Analysis.TestMatrices.RandomSVD.StewartRecursion

/-!
# RandomSVD: reusable test-matrix analysis, standing alone

Imports only the reusable `RandomSVD` modules. This is the family boundary the
wave brief asks for: reusable test-matrix analysis that a later wave can use
without importing Chapter 28 source correspondence.
-/
#check @NumStability.split_succ
#check @NumStability.randsvdMatrix
#check @NumStability.finCastEquiv_val
#check @NumStability.stewartRDiagonal
