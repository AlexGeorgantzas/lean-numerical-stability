import NumStability.Analysis.TestMatrices.Cauchy.Basic
import NumStability.Analysis.TestMatrices.Cauchy.Cauchy
import NumStability.Analysis.TestMatrices.Cauchy.Contracts
import NumStability.Analysis.TestMatrices.Companion.Basic
import NumStability.Analysis.TestMatrices.Companion.Companion
import NumStability.Analysis.TestMatrices.Companion.CompanionSpectral
import NumStability.Analysis.TestMatrices.Companion.Contracts
import NumStability.Analysis.TestMatrices.Gaussian.GaussianDirection
import NumStability.Analysis.TestMatrices.Gaussian.GaussianOrthogonal
import NumStability.Analysis.TestMatrices.Hilbert.Asymptotics
import NumStability.Analysis.TestMatrices.Hilbert.Basic
import NumStability.Analysis.TestMatrices.Hilbert.Exact
import NumStability.Analysis.TestMatrices.Hilbert.HilbertAsymptotic
import NumStability.Analysis.TestMatrices.Hilbert.ShiftedHilbert
import NumStability.Analysis.TestMatrices.Orthogonal.Basic
import NumStability.Analysis.TestMatrices.Orthogonal.OrthogonalCoordinates
import NumStability.Analysis.TestMatrices.Orthogonal.OrthogonalFibers
import NumStability.Analysis.TestMatrices.Orthogonal.OrthogonalHaar
import NumStability.Analysis.TestMatrices.Orthogonal.OrthogonalSphere
import NumStability.Analysis.TestMatrices.Pascal.Basic
import NumStability.Analysis.TestMatrices.Pascal.Contracts
import NumStability.Analysis.TestMatrices.Pascal.Exact
import NumStability.Analysis.TestMatrices.Pascal.PascalDualFlag
import NumStability.Analysis.TestMatrices.Pascal.PascalOscillation
import NumStability.Analysis.TestMatrices.Pascal.PascalOscillationCore
import NumStability.Analysis.TestMatrices.Pascal.PascalSpectral
import NumStability.Analysis.TestMatrices.Pascal.PascalTotalPositivity
import NumStability.Analysis.TestMatrices.RandomSVD.Basic
import NumStability.Analysis.TestMatrices.RandomSVD.Stewart
import NumStability.Analysis.TestMatrices.RandomSVD.StewartHaar
import NumStability.Analysis.TestMatrices.RandomSVD.StewartRecursion
import NumStability.Analysis.TestMatrices.RealGinibre.GinibreRoots
import NumStability.Analysis.TestMatrices.Toeplitz.Basic
import NumStability.Analysis.TestMatrices.Toeplitz.Contracts

/-!
# The reusable test-matrix tier, imported with no Source module present

Imports every reusable W09 destination and nothing else: no
`Source.Higham.Chapter28` module and no historical facade appears in this import
list. B0009 requires the reusable tier to have zero direct *or transitive* Source
reachability, so if any reusable module pulled Chapter 28 back in, this test would
still compile -- but `reach.py` proves the transitive half, and this proves that
the tier stands up with nothing else imported.
-/
#check @NumStability.split_succ
#check @NumStability.cauchyLower
#check @NumStability.cauchyUpper
#check @NumStability.hilbertRNat
#check @NumStability.pascalLower
#check @NumStability.cauchyMatrix
