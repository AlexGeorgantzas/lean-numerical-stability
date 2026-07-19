-- Algorithms/Ch14GJEOperationalBridge.lean
--
-- Operational audit bridges for Higham Chapter 14, Algorithm 14.4 and
-- Theorem 14.5.  This file separates data that can be constructed from an
-- executed source trace from the genuinely missing finalization contract.

import LeanFpAnalysis.FP.Algorithms.Ch14GJETheorem145SourceClosure

namespace LeanFpAnalysis.FP.Ch14Ext

open Filter Asymptotics
open LeanFpAnalysis.FP

/-! ## Canonical output, inverse, and solve witnesses -/

/-- The returned vector of the recursively executed second stage.  With this
definition, the `final_vector` field of the older family contract is
definitionally discharged rather than supplied as an independent certificate. -/
noncomputable def ch14ext_gjeSourceComputedOutput {n : Nat}
    (fp : FPModel) (s : Ch14GJEState n) : Fin n -> Real :=
  ch14ext_gjeSourceTraceRhs fp 1 s n

@[simp] theorem ch14ext_gjeSourceComputedOutput_eq {n : Nat}
    (fp : FPModel) (s : Ch14GJEState n) (i : Fin n) :
    ch14ext_gjeSourceComputedOutput fp s i =
      ch14ext_gjeSourceTraceRhs fp 1 s n i := by
  rfl

/-- The exact inverse used in the analysis is canonical once the computed
upper factor is nonsingular. -/
noncomputable def ch14ext_gjeCanonicalUpperInverse {n : Nat}
    (U : Fin n -> Fin n -> Real) : Fin n -> Fin n -> Real :=
  nonsingInv n U

/-- The exact comparison solution of the computed upper-triangular system is
canonical once its inverse is fixed.  It is an analysis-only object, not an
extra rounded computation. -/
noncomputable def ch14ext_gjeCanonicalUpperSolve {n : Nat}
    (U : Fin n -> Fin n -> Real) (y : Fin n -> Real) : Fin n -> Real :=
  matMulVec n (ch14ext_gjeCanonicalUpperInverse U) y

/-- Nonsingularity constructs the two-sided inverse certificate formerly
passed separately to the source-family endpoint. -/
theorem ch14ext_gjeCanonicalUpperInverse_isInverse {n : Nat}
    (U : Fin n -> Fin n -> Real)
    (hdet : Matrix.det (Matrix.of U : Matrix (Fin n) (Fin n) Real) ≠ 0) :
    IsInverse n U (ch14ext_gjeCanonicalUpperInverse U) := by
  simpa [ch14ext_gjeCanonicalUpperInverse] using
    isInverse_nonsingInv_of_det_ne_zero n U hdet

/-- The canonical comparison solution solves the computed upper system
exactly.  Thus the `hUz`/`upper_solve` fields in the old endpoints are not
independent mathematical assumptions once nonsingularity is known. -/
theorem ch14ext_gjeCanonicalUpperSolve_exact {n : Nat}
    (U : Fin n -> Fin n -> Real) (y : Fin n -> Real)
    (hdet : Matrix.det (Matrix.of U : Matrix (Fin n) (Fin n) Real) ≠ 0) :
    forall i : Fin n,
      matMulVec n U (ch14ext_gjeCanonicalUpperSolve U y) i = y i := by
  have hInv := ch14ext_gjeCanonicalUpperInverse_isInverse U hdet
  have h := matMulVec_of_isRightInverse U
    (ch14ext_gjeCanonicalUpperInverse U) hInv.2 y
  intro i
  exact congrFun h i

/-- Uniform boundedness of the canonical inverse and of the computed RHS
constructs uniform boundedness of the canonical exact comparison solve. -/
theorem ch14ext_gjeCanonicalUpperSolve_family_isBigOOne
    {I : Type*} {l : Filter I} {n : Nat}
    {U : I -> Fin n -> Fin n -> Real} {y : I -> Fin n -> Real}
    (hInv : MatrixFamilyIsBigOOne l
      (fun t => ch14ext_gjeCanonicalUpperInverse (U t)))
    (hy : VectorFamilyIsBigOOne l y) :
    VectorFamilyIsBigOOne l
      (fun t => ch14ext_gjeCanonicalUpperSolve (U t) (y t)) := by
  simpa [ch14ext_gjeCanonicalUpperSolve] using
    ch14ext_matrixFamily_mul_vectorFamily_isBigOOne hInv hy

/-! ## The remaining finalization obstruction -/

/-- A legal `FPModel` whose multiplication always takes the extremal positive
relative error while addition, subtraction, division, and square root are
exact.  It is used to test whether finalization is actually forced by the
abstract model. -/
noncomputable def ch14ext_mulBiasedModel (u : Real) (hu : 0 <= u) : FPModel where
  u := u
  u_nonneg := hu
  fl_add := fun x y => x + y
  fl_sub := fun x y => x - y
  fl_mul := fun x y => (x * y) * (1 + u)
  fl_div := fun x y => x / y
  fl_sqrt := fun x => Real.sqrt x
  fl_add_zero := by
    intro x
    ring
  model_add := by
    intro x y
    refine ⟨0, by simpa using hu, ?_⟩
    ring
  model_sub := by
    intro x y
    refine ⟨0, by simpa using hu, ?_⟩
    ring
  model_mul := by
    intro x y
    exact ⟨u, by simp [abs_of_nonneg hu], rfl⟩
  model_div := by
    intro x y _hy
    refine ⟨0, by simpa using hu, ?_⟩
    ring
  model_sqrt := by
    intro x _hx
    refine ⟨0, by simpa using hu, ?_⟩
    ring

/-- The counterexample model satisfies all gamma guards used by the
two-by-two Theorem-14.5 source trace whenever `3*u < 1`. -/
theorem ch14ext_mulBiasedModel_gammaValid_two_three
    (u : Real) (hu : 0 <= u) (hsmall : 3 * u < 1) :
    gammaValid (ch14ext_mulBiasedModel u hu) 2 ∧
      gammaValid (ch14ext_mulBiasedModel u hu) 3 := by
  constructor
  · unfold gammaValid
    dsimp [ch14ext_mulBiasedModel]
    nlinarith
  · simpa [gammaValid, ch14ext_mulBiasedModel] using hsmall

/-- A normalized two-by-two upper-triangular state. -/
def ch14ext_finalizationCounterMatrix : Fin 2 -> Fin 2 -> Real :=
  !![(1 : Real), 1; 0, 1]

def ch14ext_finalizationCounterState : Ch14GJEState 2 where
  matrix := ch14ext_finalizationCounterMatrix
  rhs := ![(0 : Real), 0]

/-- The sole second-stage pivot in the two-by-two counterexample is nonzero,
so the rounded source trace satisfies the operational pivot-success guard. -/
theorem ch14ext_finalizationCounter_pivot_nonzero
    (u : Real) (hu : 0 <= u) :
    forall t : Nat, (ht : t < 2 - 1) ->
      ch14ext_gjeSourceTraceMatrix (ch14ext_mulBiasedModel u hu) 1
          ch14ext_finalizationCounterState (1 + t)
          ⟨1 + t, by omega⟩ ⟨1 + t, by omega⟩ ≠ 0 := by
  intro t ht
  have ht0 : t = 0 := by omega
  subst t
  norm_num [ch14ext_gjeSourceTraceMatrix, ch14ext_gjeSourceTrace,
    ch14ext_finalizationCounterState, ch14ext_finalizationCounterMatrix]

/-- After the one rounded elimination step, the nominally eliminated entry is
`-u`.  The current executor computes the arithmetic update but does not perform
the structural zero assignment used implicitly by Higham's final `D = I`
normalization. -/
theorem ch14ext_finalizationCounter_entry
    (u : Real) (hu : 0 <= u) :
    ch14ext_gjeSourceTraceMatrix (ch14ext_mulBiasedModel u hu) 1
        ch14ext_finalizationCounterState 2 0 1 = -u := by
  simp [ch14ext_gjeSourceTraceMatrix, ch14ext_gjeSourceTrace,
    ch14ext_gjeSourceStepState, ch14ext_gjeSourceStepMatrix,
    ch14ext_gjeSourceActive, ch14ext_gjeStepMatrix,
    ch14ext_mulBiasedModel, ch14ext_finalizationCounterState,
    ch14ext_finalizationCounterMatrix]

/-- Successful nonzero pivots do not imply the `final_matrix = I` field of
`Ch14GJETheorem145SourceFamily` for the repository's current rounded executor.
Consequently that field cannot be manufactured as an Algorithm-14.4 producer
without changing the executor to model structural zeroing/final scaling (and
then reproving the local-error bridge for that execution). -/
theorem ch14ext_finalizationCounter_not_identity
    (u : Real) (hu : 0 < u) :
    ch14ext_gjeSourceTraceMatrix
        (ch14ext_mulBiasedModel u hu.le) 1
        ch14ext_finalizationCounterState 2 ≠ idMatrix 2 := by
  intro h
  have hentry := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  rw [ch14ext_finalizationCounter_entry u hu.le] at hentry
  simp [idMatrix] at hentry
  linarith

/-- All local model-validity and pivot-success guards can hold while the
current rounded source trace still fails its assumed final-identity field. -/
theorem ch14ext_finalizationCounter_all_local_guards_but_not_identity
    (u : Real) (hu : 0 < u) (hsmall : 3 * u < 1) :
    gammaValid (ch14ext_mulBiasedModel u hu.le) 2 ∧
      gammaValid (ch14ext_mulBiasedModel u hu.le) 3 ∧
      (forall t : Nat, (ht : t < 2 - 1) ->
        ch14ext_gjeSourceTraceMatrix (ch14ext_mulBiasedModel u hu.le) 1
            ch14ext_finalizationCounterState (1 + t)
            ⟨1 + t, by omega⟩ ⟨1 + t, by omega⟩ ≠ 0) ∧
      ch14ext_gjeSourceTraceMatrix (ch14ext_mulBiasedModel u hu.le) 1
          ch14ext_finalizationCounterState 2 ≠ idMatrix 2 := by
  refine ⟨(ch14ext_mulBiasedModel_gammaValid_two_three u hu.le hsmall).1,
    (ch14ext_mulBiasedModel_gammaValid_two_three u hu.le hsmall).2,
    ch14ext_finalizationCounter_pivot_nonzero u hu.le,
    ch14ext_finalizationCounter_not_identity u hu⟩

end LeanFpAnalysis.FP.Ch14Ext
