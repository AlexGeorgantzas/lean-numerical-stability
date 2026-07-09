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

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for the supplied shifted-determinant
    Hessenberg-Schur solve/trace-growth package. -/
alias H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_and_HessenbergGEPPUTrace_growth_of_upperHessenberg_triangular_shifted_det_ne_zero :=
  existsUnique_isSylvesterSolutionRect_and_HessenbergGEPPUTrace_growth_of_upperHessenberg_triangular_shifted_det_ne_zero

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8),
    Hessenberg-Schur handoff with the shifted singleton determinant
    certificates discharged from one global Schur-coordinate vec/Kronecker
    determinant certificate.  This is an exact structural wrapper around the
    supplied triangular solve and Chapter 9 Hessenberg GEPP trace-growth
    package; it does not assert rounded Bartels-Stewart arithmetic. -/
theorem existsUnique_isSylvesterSolutionRect_and_HessenbergGEPPUTrace_growth_of_upperHessenberg_triangular_vecCoeff_det_ne_zero
    (m n : Nat) (hm : 0 < m)
    (R : RMatFn m m) (S : RMatFn n n) (C : RMatFn m n)
    (hR : IsUpperHessenberg m R)
    (hS : IsUpperTriangularFn n S)
    (hdetGlobal : Not (Matrix.det (sylvesterVecCoeff m n R S) = 0)) :
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
  exact
    existsUnique_isSylvesterSolutionRect_and_HessenbergGEPPUTrace_growth_of_upperHessenberg_triangular_shifted_det_ne_zero
      m n hm R S C hR hS
      (fun k =>
        sylvesterTriangularShiftedCoeff_det_ne_zero_of_singleton_global_vecCoeff_det_ne_zero
          m n R S (fun i : Fin n => i.val) k
          (by
            intro i j hij
            exact hS i j (Fin.lt_def.mpr hij))
          (by
            intro i hi
            exact Fin.ext hi)
          hdetGlobal)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for the Hessenberg-Schur solve/trace-growth package
    from one global Schur-coordinate vec/Kronecker determinant certificate. -/
alias H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_and_HessenbergGEPPUTrace_growth_of_upperHessenberg_triangular_vecCoeff_det_ne_zero :=
  existsUnique_isSylvesterSolutionRect_and_HessenbergGEPPUTrace_growth_of_upperHessenberg_triangular_vecCoeff_det_ne_zero

/-- Higham, 2nd ed., Chapter 16.2, equations (16.3)-(16.8),
    Schur-coordinate Hessenberg-Schur handoff with shifted singleton
    determinant certificates discharged from no-common-complex-spectrum data.
    This remains an exact supplied-factor triangular bridge, not rounded
    Bartels-Stewart arithmetic or estimator production. -/
theorem existsUnique_isSylvesterSolutionRect_and_HessenbergGEPPUTrace_growth_of_upperHessenberg_triangular_no_common_complex_right_eigenvalue
    (m n : Nat) (hm : 0 < m)
    (R : RMatFn m m) (S : RMatFn n n) (C : RMatFn m n)
    (hR : IsUpperHessenberg m R)
    (hS : IsUpperTriangularFn n S)
    (hno :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex R)
        (realMatrixToComplex S)) :
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
  exact
    existsUnique_isSylvesterSolutionRect_and_HessenbergGEPPUTrace_growth_of_upperHessenberg_triangular_vecCoeff_det_ne_zero
      m n hm R S C hR hS
      (sylvesterVecCoeff_det_ne_zero_of_no_common_complex_right_eigenvalue
        m n R S hno)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.3)-(16.8):
    source-numbered alias for the Schur-coordinate Hessenberg-Schur
    solve/trace-growth package from no-common-complex-spectrum data. -/
alias H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_and_HessenbergGEPPUTrace_growth_of_upperHessenberg_triangular_no_common_complex_right_eigenvalue :=
  existsUnique_isSylvesterSolutionRect_and_HessenbergGEPPUTrace_growth_of_upperHessenberg_triangular_no_common_complex_right_eigenvalue

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8),
    original-coordinate Hessenberg-Schur handoff with shifted singleton
    determinant certificates discharged from nonsingularity of the original
    vec/Kronecker Sylvester coefficient.  The conclusion combines exact
    original-coordinate unique solvability with per-column Chapter 9
    upper-Hessenberg GEPP trace-growth certificates for the supplied
    Schur-coordinate column systems. -/
theorem existsUnique_isSylvesterSolutionRect_and_HessenbergGEPPUTrace_growth_of_realSchur_upperHessenberg_triangular_vecCoeff_det_ne_zero
    (m n : Nat) (hm : 0 < m)
    (U R A : RMatFn m m) (V S B : RMatFn n n) (C : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hR : IsUpperHessenberg m R)
    (hS : IsUpperTriangularFn n S)
    (hdetOrig : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0)) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) /\
      (forall k : Fin n,
        exists hmax : 0 < maxEntryNorm hm
            (sylvesterTriangularShiftedCoeff m R (S k k)),
        exists Ugepp : Fin m -> Fin m -> Real,
          higham9_10_HessenbergGEPPUTrace
            (maxEntryNorm hm (sylvesterTriangularShiftedCoeff m R (S k k)))
            1 m (sylvesterTriangularShiftedCoeff m R (S k k)) Ugepp /\
          growthFactorEntry hm (sylvesterTriangularShiftedCoeff m R (S k k))
              Ugepp hmax <= (m : Real)) := by
  have hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0) := by
    intro k
    exact
      sylvesterTriangularShiftedCoeff_det_ne_zero_of_realQuasiSchur_factors_singleton_vecCoeff_det_ne_zero
        m n U R A V S B (fun i : Fin n => i.val) k hU hV hA hB
        (by
          intro i j hij
          exact hS i j (Fin.lt_def.mpr hij))
        (by
          intro i hi
          exact Fin.ext hi)
        hdetOrig
  constructor
  · exact
      existsUnique_isSylvesterSolutionRect_schurTriangular
        m n U R A V S B C hU hV hA hB hS hshift
  · intro k
    exact
      exists_HessenbergGEPPUTrace_growthFactorEntry_le_card_sylvesterTriangularShiftedCoeff_of_det_ne_zero_exists_hmax
        m hm R (S k k) hR (hshift k)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8):
    source-numbered alias for the original-coordinate Hessenberg-Schur
    solve/trace-growth package from an original vec/Kronecker determinant
    certificate. -/
alias H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_and_HessenbergGEPPUTrace_growth_of_realSchur_upperHessenberg_triangular_vecCoeff_det_ne_zero :=
  existsUnique_isSylvesterSolutionRect_and_HessenbergGEPPUTrace_growth_of_realSchur_upperHessenberg_triangular_vecCoeff_det_ne_zero

/-- Higham, 2nd ed., Chapter 16.2, equations (16.3)-(16.8),
    original-coordinate Hessenberg-Schur handoff with shifted singleton
    determinant certificates discharged from original no-common-complex-spectrum
    data.  This is an exact supplied-factor triangular Hessenberg-Schur bridge;
    it does not model rounded Bartels-Stewart arithmetic or LAPACK estimators. -/
theorem existsUnique_isSylvesterSolutionRect_and_HessenbergGEPPUTrace_growth_of_realSchur_upperHessenberg_triangular_no_common_complex_right_eigenvalue
    (m n : Nat) (hm : 0 < m)
    (U R A : RMatFn m m) (V S B : RMatFn n n) (C : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hR : IsUpperHessenberg m R)
    (hS : IsUpperTriangularFn n S)
    (hnoOrig :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex A)
        (realMatrixToComplex B)) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) /\
      (forall k : Fin n,
        exists hmax : 0 < maxEntryNorm hm
            (sylvesterTriangularShiftedCoeff m R (S k k)),
        exists Ugepp : Fin m -> Fin m -> Real,
          higham9_10_HessenbergGEPPUTrace
            (maxEntryNorm hm (sylvesterTriangularShiftedCoeff m R (S k k)))
            1 m (sylvesterTriangularShiftedCoeff m R (S k k)) Ugepp /\
          growthFactorEntry hm (sylvesterTriangularShiftedCoeff m R (S k k))
              Ugepp hmax <= (m : Real)) := by
  have hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0) := by
    intro k
    exact
      sylvesterTriangularShiftedCoeff_det_ne_zero_of_realQuasiSchur_factors_singleton_no_common_complex_right_eigenvalue
        m n U R A V S B (fun i : Fin n => i.val) k hU hV hA hB
        (by
          intro i j hij
          exact hS i j (Fin.lt_def.mpr hij))
        (by
          intro i hi
          exact Fin.ext hi)
        hnoOrig
  constructor
  · exact
      existsUnique_isSylvesterSolutionRect_schurTriangular
        m n U R A V S B C hU hV hA hB hS hshift
  · intro k
    exact
      exists_HessenbergGEPPUTrace_growthFactorEntry_le_card_sylvesterTriangularShiftedCoeff_of_det_ne_zero_exists_hmax
        m hm R (S k k) hR (hshift k)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.3)-(16.8):
    source-numbered alias for the original-coordinate Hessenberg-Schur
    solve/trace-growth package from no-common-complex-spectrum data. -/
alias H16_eq16_4_8_existsUnique_isSylvesterSolutionRect_and_HessenbergGEPPUTrace_growth_of_realSchur_upperHessenberg_triangular_no_common_complex_right_eigenvalue :=
  existsUnique_isSylvesterSolutionRect_and_HessenbergGEPPUTrace_growth_of_realSchur_upperHessenberg_triangular_no_common_complex_right_eigenvalue

end LeanFpAnalysis.FP
