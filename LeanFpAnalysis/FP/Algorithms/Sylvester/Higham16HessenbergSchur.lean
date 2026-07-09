-- Algorithms/Sylvester/Higham16HessenbergSchur.lean
--
-- Exact Hessenberg-Schur handoff for Higham, 2nd ed., Chapter 16.2.

import LeanFpAnalysis.FP.Algorithms.Sylvester.Higham16Spectrum
import LeanFpAnalysis.FP.Algorithms.HighamChapter9

namespace LeanFpAnalysis.FP

open scoped BigOperators

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), Hessenberg-Schur handoff:
    shifting the singleton Bartels-Stewart column coefficient by `t I`
    preserves the upper-Hessenberg zero pattern. -/
theorem sylvesterTriangularShiftedCoeff_isUpperHessenberg
    (m : Nat) (R : RMatFn m m) (t : Real)
    (hR : IsUpperHessenberg m R) :
    IsUpperHessenberg m (sylvesterTriangularShiftedCoeff m R t) := by
  intro i j hij
  have hne : i ≠ j := by
    intro h
    subst h
    omega
  simp [sylvesterTriangularShiftedCoeff, hR i j hij, hne]

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), Hessenberg-Schur handoff:
    a nonsingular shifted singleton column coefficient with upper-Hessenberg
    structure admits the Chapter 9 exact GEPP Hessenberg `U` trace.  This is a
    structural bridge only; it does not model rounded Bartels-Stewart arithmetic
    or a LAPACK-style estimator. -/
theorem exists_HessenbergGEPPUTrace_sylvesterTriangularShiftedCoeff_of_det_ne_zero
    (m : Nat) (hm : 0 < m) (R : RMatFn m m) (t : Real)
    (hR : IsUpperHessenberg m R)
    (hdet : Matrix.det (sylvesterTriangularShiftedCoeff m R t) ≠ 0) :
    exists U : Fin m -> Fin m -> Real,
      higham9_10_HessenbergGEPPUTrace
        (maxEntryNorm hm (sylvesterTriangularShiftedCoeff m R t))
        1 m (sylvesterTriangularShiftedCoeff m R t) U := by
  exact
    higham9_10_exists_HessenbergGEPPUTrace_of_det_ne_zero
      hm (sylvesterTriangularShiftedCoeff m R t)
      (sylvesterTriangularShiftedCoeff_isUpperHessenberg m R t hR)
      (by simpa [Matrix.of_apply] using hdet)

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), Hessenberg-Schur handoff:
    the Chapter 9 upper-Hessenberg GEPP trace for a nonsingular shifted
    singleton column coefficient also satisfies Wilkinson's exact max-entry
    growth-factor bound.  This packages the structural handoff for later
    solver-analysis use without asserting rounded Schur arithmetic. -/
theorem exists_HessenbergGEPPUTrace_growthFactorEntry_le_card_sylvesterTriangularShiftedCoeff_of_det_ne_zero
    (m : Nat) (hm : 0 < m) (R : RMatFn m m) (t : Real)
    (hR : IsUpperHessenberg m R)
    (hdet : Matrix.det (sylvesterTriangularShiftedCoeff m R t) ≠ 0)
    (hmax : 0 < maxEntryNorm hm (sylvesterTriangularShiftedCoeff m R t)) :
    exists U : Fin m -> Fin m -> Real,
      higham9_10_HessenbergGEPPUTrace
        (maxEntryNorm hm (sylvesterTriangularShiftedCoeff m R t))
        1 m (sylvesterTriangularShiftedCoeff m R t) U /\
      growthFactorEntry hm (sylvesterTriangularShiftedCoeff m R t) U hmax <=
        (m : Real) := by
  exact
    higham9_10_exists_HessenbergGEPPUTrace_growthFactorEntry_le_card_of_det_ne_zero
      hm (sylvesterTriangularShiftedCoeff m R t)
      (sylvesterTriangularShiftedCoeff_isUpperHessenberg m R t hR)
      (by simpa [Matrix.of_apply] using hdet)
      hmax

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), Hessenberg-Schur handoff:
    nonsingularity of the shifted singleton column coefficient also supplies
    the positive max-entry denominator needed for the Chapter 9 upper-Hessenberg
    growth-factor package. -/
theorem exists_HessenbergGEPPUTrace_growthFactorEntry_le_card_sylvesterTriangularShiftedCoeff_of_det_ne_zero_exists_hmax
    (m : Nat) (hm : 0 < m) (R : RMatFn m m) (t : Real)
    (hR : IsUpperHessenberg m R)
    (hdet : Matrix.det (sylvesterTriangularShiftedCoeff m R t) ≠ 0) :
    exists hmax : 0 < maxEntryNorm hm (sylvesterTriangularShiftedCoeff m R t),
    exists U : Fin m -> Fin m -> Real,
      higham9_10_HessenbergGEPPUTrace
        (maxEntryNorm hm (sylvesterTriangularShiftedCoeff m R t))
        1 m (sylvesterTriangularShiftedCoeff m R t) U /\
      growthFactorEntry hm (sylvesterTriangularShiftedCoeff m R t) U hmax <=
        (m : Real) := by
  exact
    higham9_10_exists_HessenbergGEPPUTrace_growthFactorEntry_le_card_of_det_ne_zero_exists_hAmax
      hm (sylvesterTriangularShiftedCoeff m R t)
      (sylvesterTriangularShiftedCoeff_isUpperHessenberg m R t hR)
      (by simpa [Matrix.of_apply] using hdet)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8),
    Hessenberg-Schur handoff for the supplied triangular solve: if the left
    Schur factor is upper Hessenberg, the right factor is upper triangular, and
    every singleton shifted column coefficient is nonsingular, then the exact
    triangular Sylvester equation is uniquely solvable and every shifted column
    system admits the Chapter 9 upper-Hessenberg GEPP trace with growth bound.
    This bundles exact structural certificates only; it does not assert a
    rounded Bartels-Stewart implementation. -/
theorem existsUnique_isSylvesterSolutionRect_and_HessenbergGEPPUTrace_growth_of_upperHessenberg_triangular_shifted_det_ne_zero
    (m n : Nat) (hm : 0 < m)
    (R : RMatFn m m) (S : RMatFn n n) (C : RMatFn m n)
    (hR : IsUpperHessenberg m R)
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) ≠ 0) :
    ExistsUnique (IsSylvesterSolutionRect m n R S C) /\
      (forall k : Fin n,
        exists hmax : 0 < maxEntryNorm hm
            (sylvesterTriangularShiftedCoeff m R (S k k)),
        exists U : Fin m -> Fin m -> Real,
          higham9_10_HessenbergGEPPUTrace
            (maxEntryNorm hm (sylvesterTriangularShiftedCoeff m R (S k k)))
            1 m (sylvesterTriangularShiftedCoeff m R (S k k)) U /\
          growthFactorEntry hm (sylvesterTriangularShiftedCoeff m R (S k k))
              U hmax <= (m : Real)) := by
  constructor
  · exact sylvester_triangular_solve_exists_unique m n R S C hS hshift
  · intro k
    exact
      exists_HessenbergGEPPUTrace_growthFactorEntry_le_card_sylvesterTriangularShiftedCoeff_of_det_ne_zero_exists_hmax
        m hm R (S k k) hR (hshift k)

end LeanFpAnalysis.FP
