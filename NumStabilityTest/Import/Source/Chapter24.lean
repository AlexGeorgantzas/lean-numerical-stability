import NumStability.Source.Higham.Chapter24.CirculantForwardError
import NumStability.Source.Higham.Chapter24.CirculantSystems
import NumStability.Source.Higham.Chapter24.FFTBackwardStability
import NumStability.Source.Higham.Chapter24.ForwardFFTPerturbation
import NumStability.Source.Higham.Chapter24.FourierTransform
import NumStability.Source.Higham.Chapter24.InverseFFT
import NumStability.Source.Higham.Chapter24.Radix2FFT
import NumStability.Source.Higham.Chapter24.RoundedCirculantSolver
import NumStability.Source.Higham.Chapter24.RoundedDiagonalSolve
import NumStability.Source.Higham.Chapter24.StructuredMixedStability

/-!
# Canonical Chapter 24 import smoke test

Each implementation module is imported directly so the chapter umbrella cannot
mask an unresolved canonical path.
-/

#check NumStability.higham24DFT
#check NumStability.higham24_theorem24_1_stage_factorization
#check NumStability.higham24Circulant
#check NumStability.higham24LiteralForwardPerturbation
#check NumStability.higham24RoundedDiagonalSolve
#check NumStability.higham24RoundedInverseRadix2FFTFin
#check NumStability.higham24LiteralRoundedCirculantSolve
#check NumStability.higham24_literalFFT_backward_stable
#check NumStability.higham24_theorem24_3_literal_quadraticRemainder
#check NumStability.higham24_theorem24_3_literal_forward_error_multiple_kappa_u
