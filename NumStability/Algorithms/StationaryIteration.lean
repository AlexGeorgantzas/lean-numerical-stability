import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Convergence.Singular.FixedSubspaces
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.ErrorAnalysis.Forward.ComplementDecomposition
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.ErrorAnalysis.Local.OneStep
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.ErrorAnalysis.Residual.Identities
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Execution.Computed.Model
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Projectors.Drazin.Algebra
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Recurrences.Affine.Unrolling
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Splittings.Core.Definitions
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Splittings.Scaling.Diagonal
import NumStability.Analysis.Conditioning.LinearSystems.SubordinatePerturbation
import NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.RealDiagonal
import NumStability.Analysis.MatrixAlgebra
import NumStability.Source.Higham.Chapter17.Equation01.ComputedIteration.Results
import NumStability.Source.Higham.Chapter17.Equation02.LocalError.Results
import NumStability.Source.Higham.Chapter17.Equation03.ComputedRecurrence.Results
import NumStability.Source.Higham.Chapter17.Equation04.FixedPoint.Results
import NumStability.Source.Higham.Chapter17.Equation05.ErrorExpansion.Results
import NumStability.Source.Higham.Chapter17.Equation06.ComponentwiseForward.Results
import NumStability.Source.Higham.Chapter17.Equation07.NormwiseGrowth.Results
import NumStability.Source.Higham.Chapter17.Equation08.NormwiseForward.Results
import NumStability.Source.Higham.Chapter17.Equation09.ComponentwiseGrowth.Results
import NumStability.Source.Higham.Chapter17.Equation10.LocalErrorSimplification.Results
import NumStability.Source.Higham.Chapter17.Equation12.PartialSumBound.Results
import NumStability.Source.Higham.Chapter17.Equation13.ComponentwiseForward.Results
import NumStability.Source.Higham.Chapter17.Equation15.NormwiseForward.Results
import NumStability.Source.Higham.Chapter17.Equation16.Jacobi.Results
import NumStability.Source.Higham.Chapter17.Equation17.SOR.Results
import NumStability.Source.Higham.Chapter17.Equation18.ResidualRecurrence.Results
import NumStability.Source.Higham.Chapter17.Equation19.ResidualBound.Results
import NumStability.Source.Higham.Chapter17.Equation20.ResidualSigma.Results
import NumStability.Source.Higham.Chapter17.Equation21.SingularIteration.Results
import NumStability.Source.Higham.Chapter17.Equation27.SingularErrorSplit.Results
import NumStability.Source.Higham.Chapter17.Equation28.SingularErrorSplit.Results
import NumStability.Source.Higham.Chapter17.Equation29.SingularSource.Results
import NumStability.Source.Higham.Chapter17.Equation33.StoppingTests.Results
import NumStability.Source.Higham.Chapter17.Section02.ScaleIndependence.Results
import NumStability.Source.Higham.Chapter17.Section04.PrintedConclusions.Results

/-!
# NumStability.Algorithms.StationaryIteration historical facade

Historical declaration-bearing W07 facade. Eight genuine private declarations and the 29-node main-owner portion of their exact reverse closure retain their original identities here; every movable command is re-exported from canonical reusable or Chapter 17 modules.
-/

-- Algorithms/StationaryIteration.lean
--
-- Higham Chapter 17: Error analysis of stationary iterative methods.
--
-- Covers §17.2 (forward error analysis) and §17.3 (backward/residual error
-- analysis) for iterations of the form  Mx_{k+1} = Nx_k + b  where A = M − N.














namespace NumStability

open scoped BigOperators

-- ============================================================
-- §17.2  Splitting specification and iteration matrices
-- ============================================================



























































































































































































































































-- ============================================================
-- AG = HA identity
-- ============================================================


































































































































































































































































































-- ============================================================
-- §17.2  Computed iteration and one-step error
-- ============================================================













































































































































































































































































































































































































































































/-- Multiplying two complements expands as
    `(I - A)(I - E) = I - E - A + AE`. -/
private theorem matMul_matSub_id_matSub_id (n : ℕ)
    (A E : Fin n → Fin n → ℝ) :
    matMul n (matSub_id n A) (matSub_id n E) =
      fun i j => idMatrix n i j - E i j - A i j + matMul n A E i j := by
  ext i j
  unfold matMul matSub_id
  simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib]
  have hII :
      ∑ k : Fin n, idMatrix n i k * idMatrix n k j = idMatrix n i j := by
    have h := congrArg (fun T : Fin n → Fin n → ℝ => T i j)
      (matMul_id_left n (idMatrix n))
    simpa [matMul] using h
  have hIE :
      ∑ k : Fin n, idMatrix n i k * E k j = E i j := by
    have h := congrArg (fun T : Fin n → Fin n → ℝ => T i j)
      (matMul_id_left n E)
    simpa [matMul] using h
  have hAI :
      ∑ k : Fin n, A i k * idMatrix n k j = A i j := by
    have h := congrArg (fun T : Fin n → Fin n → ℝ => T i j)
      (matMul_id_right n A)
    simpa [matMul] using h
  rw [hII, hIE, hAI]
  ring

/-- Left multiplication by a complement expands as `(I-A)B = B - AB`. -/
private theorem matMul_matSub_id_left (n : ℕ)
    (A B : Fin n → Fin n → ℝ) :
    matMul n (matSub_id n A) B =
      fun i j => B i j - matMul n A B i j := by
  ext i j
  unfold matMul matSub_id
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  have hIB :
      ∑ k : Fin n, idMatrix n i k * B k j = B i j := by
    have h := congrArg (fun T : Fin n → Fin n → ℝ => T i j)
      (matMul_id_left n B)
    simpa [matMul] using h
  rw [hIB]

/-- Right multiplication by a complement expands as `B(I-A) = B - BA`. -/
private theorem matMul_matSub_id_right (n : ℕ)
    (A B : Fin n → Fin n → ℝ) :
    matMul n B (matSub_id n A) =
      fun i j => B i j - matMul n B A i j := by
  ext i j
  unfold matMul matSub_id
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  have hBI :
      ∑ k : Fin n, B i k * idMatrix n k j = B i j := by
    have h := congrArg (fun T : Fin n → Fin n → ℝ => T i j)
      (matMul_id_right n B)
    simpa [matMul] using h
  rw [hBI]











































/-- The Drazin range projector commutes with the stationary iteration matrix
    `G`. -/
theorem stationaryDrazinRangeProjector_commutes_with_G (n : ℕ)
    (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D) :
    matMul n G (stationaryDrazinRangeProjector n G D) =
      matMul n (stationaryDrazinRangeProjector n G D) G := by
  let A := matSub_id n G
  let E := stationaryDrazinRangeProjector n G D
  have hG : matSub_id n A = G := by
    ext i j
    dsimp [A, matSub_id, idMatrix]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]
  have hAE : matMul n A E = A := by
    simpa [A, E] using
      stationaryDrazinRangeProjector_matSub_id_mul_left n G D hD
  have hEA : matMul n E A = A := by
    simpa [A, E] using
      stationaryDrazinRangeProjector_matSub_id_mul_right n G D hD
  calc
    matMul n G (stationaryDrazinRangeProjector n G D) =
      matMul n (matSub_id n A) E := by
        rw [hG]
    _ = (fun i j => E i j - matMul n A E i j) :=
        matMul_matSub_id_left n A E
    _ = (fun i j => E i j - A i j) := by
        rw [hAE]
    _ = (fun i j => E i j - matMul n E A i j) := by
        rw [hEA]
    _ = matMul n E (matSub_id n A) := by
        exact (matMul_matSub_id_right n A E).symm
    _ = matMul n (stationaryDrazinRangeProjector n G D) G := by
        rw [hG]

/-- The Drazin range projector commutes with every finite power of `G`. -/
theorem stationaryDrazinRangeProjector_commutes_with_matPow (n : ℕ)
    (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D) :
    ∀ k, matMul n (matPow n G k) (stationaryDrazinRangeProjector n G D) =
      matMul n (stationaryDrazinRangeProjector n G D) (matPow n G k) := by
  exact matPow_comm_of_matMul_comm n G
    (stationaryDrazinRangeProjector n G D)
    (stationaryDrazinRangeProjector_commutes_with_G n G D hD)

/-- Sandwiching a powered range component by the Drazin range projector leaves
    it unchanged: `E G^k E = G^k E`. -/
theorem stationaryDrazinRangeProjector_matPow_sandwich (n : ℕ)
    (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D) :
    ∀ k,
      matMul n (stationaryDrazinRangeProjector n G D)
        (matMul n (matPow n G k) (stationaryDrazinRangeProjector n G D)) =
      matMul n (matPow n G k) (stationaryDrazinRangeProjector n G D) := by
  intro k
  let E := stationaryDrazinRangeProjector n G D
  have hEid : matMul n E E = E := by
    simpa [E] using stationaryDrazinRangeProjector_idempotent n G D hD
  have hcomm :
      matMul n (matPow n G k) E = matMul n E (matPow n G k) := by
    simpa [E] using stationaryDrazinRangeProjector_commutes_with_matPow n G D hD k
  calc
    matMul n (stationaryDrazinRangeProjector n G D)
        (matMul n (matPow n G k) (stationaryDrazinRangeProjector n G D)) =
      matMul n E (matMul n (matPow n G k) E) := rfl
    _ = matMul n (matMul n E (matPow n G k)) E := by
        rw [matMul_assoc]
    _ = matMul n (matMul n (matPow n G k) E) E := by
        rw [← hcomm]
    _ = matMul n (matPow n G k) (matMul n E E) := by
        rw [matMul_assoc]
    _ = matMul n (matPow n G k) E := by
        rw [hEid]







































































/-- The complementary Drazin fixed/null projector `I-E` is idempotent. -/
theorem stationaryDrazinFixedProjector_idempotent (n : ℕ)
    (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D) :
    matMul n (stationaryDrazinFixedProjector n G D)
      (stationaryDrazinFixedProjector n G D) =
    stationaryDrazinFixedProjector n G D := by
  let E := stationaryDrazinRangeProjector n G D
  have hEid : matMul n E E = E := by
    simpa [E] using stationaryDrazinRangeProjector_idempotent n G D hD
  calc
    matMul n (stationaryDrazinFixedProjector n G D)
        (stationaryDrazinFixedProjector n G D) =
      matMul n (matSub_id n E) (matSub_id n E) := rfl
    _ = (fun i j => idMatrix n i j - E i j - E i j + matMul n E E i j) :=
        matMul_matSub_id_matSub_id n E E
    _ = stationaryDrazinFixedProjector n G D := by
        ext i j
        rw [hEid]
        unfold stationaryDrazinFixedProjector matSub_id
        ring

/-- Higham, 2nd ed., Chapter 17, Section 17.4, equations (17.25)-(17.27):
    the Drazin fixed/null projector `I - (I - G)D` is fixed by the stationary
    iteration matrix `G`.  This is the algebraic projector fact needed by the
    finite singular error split. -/
theorem stationaryDrazinFixedProjector_fixed_by_G (n : ℕ)
    (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D) :
    matMul n G (stationaryDrazinFixedProjector n G D) =
      stationaryDrazinFixedProjector n G D := by
  let A := matSub_id n G
  let E := stationaryDrazinRangeProjector n G D
  have hG : matSub_id n A = G := by
    ext i j
    dsimp [A, matSub_id, idMatrix]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]
  have hAE : matMul n A E = A := by
    dsimp [A, E, stationaryDrazinRangeProjector]
    rw [← matMul_assoc]
    exact hD.index_one
  calc
    matMul n G (stationaryDrazinFixedProjector n G D)
        = matMul n G (matSub_id n E) := rfl
    _ = matMul n (matSub_id n A) (matSub_id n E) := by
            rw [hG]
    _ = (fun i j => idMatrix n i j - E i j - A i j + matMul n A E i j) :=
            matMul_matSub_id_matSub_id n A E
    _ = matSub_id n E := by
            ext i j
            rw [hAE]
            unfold matSub_id
            ring
    _ = stationaryDrazinFixedProjector n G D := rfl

/-- Every finite power of `G` fixes the Drazin fixed/null projector.  This is
    the finite-power algebraic side of the limiting projector identity used in
    Higham's semiconvergent singular-system analysis. -/
theorem stationaryDrazinFixedProjector_matPow_fixed (n : ℕ)
    (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D) :
    ∀ k, matMul n (matPow n G k) (stationaryDrazinFixedProjector n G D) =
      stationaryDrazinFixedProjector n G D := by
  exact matPow_mul_fixed_of_matMul_fixed n G
    (stationaryDrazinFixedProjector n G D)
    (stationaryDrazinFixedProjector_fixed_by_G n G D hD)

/-- Higham, 2nd ed., Chapter 17, Section 17.4, equations (17.25)-(17.27):
    finite algebraic split behind the singular-system limiting projector.
    Every powered vector decomposes into its propagated Drazin range component
    plus the fixed/null Drazin projector component. -/
theorem stationaryDrazin_matPow_vec_split (n : ℕ)
    (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D)
    (v : Fin n → ℝ) (m : ℕ) :
    ∀ i, matMulVec n (matPow n G m) v i =
      matMulVec n (matMul n (matPow n G m)
        (stationaryDrazinRangeProjector n G D)) v i +
      matMulVec n (stationaryDrazinFixedProjector n G D) v i := by
  intro i
  let E := stationaryDrazinRangeProjector n G D
  let C := stationaryDrazinFixedProjector n G D
  have hsplit : v = fun j => matMulVec n E v j + matMulVec n C v j := by
    ext j
    simpa [E, C, stationaryDrazinFixedProjector] using
      (matMulVec_add_complement_apply n E v j).symm
  have hfixedMat : matMul n (matPow n G m) C = C := by
    simpa [C] using stationaryDrazinFixedProjector_matPow_fixed n G D hD m
  calc
    matMulVec n (matPow n G m) v i =
        matMulVec n (matPow n G m)
          (fun j => matMulVec n E v j + matMulVec n C v j) i := by
          exact congrArg (fun w => matMulVec n (matPow n G m) w i) hsplit
    _ = matMulVec n (matPow n G m) (matMulVec n E v) i +
        matMulVec n (matPow n G m) (matMulVec n C v) i := by
          simpa using congrFun
            (matMulVec_add_right n (matPow n G m)
              (matMulVec n E v) (matMulVec n C v)) i
    _ = matMulVec n (matMul n (matPow n G m) E) v i +
        matMulVec n (matMul n (matPow n G m) C) v i := by
          rw [← matMulVec_matMul n (matPow n G m) E v i]
          rw [← matMulVec_matMul n (matPow n G m) C v i]
    _ = matMulVec n (matMul n (matPow n G m) E) v i +
        matMulVec n C v i := by
          rw [hfixedMat]
    _ = matMulVec n (matMul n (matPow n G m)
          (stationaryDrazinRangeProjector n G D)) v i +
        matMulVec n (stationaryDrazinFixedProjector n G D) v i := by
          rfl

/-- Conditional limiting form of `stationaryDrazin_matPow_vec_split`: if the
    Drazin range component decays to zero, then `G^m v` tends coordinatewise
    to the fixed/null Drazin projector component.  This records the formal
    dependency used by the semiconvergent singular-system discussion without
    asserting semiconvergence or Drazin existence. -/
theorem stationaryDrazin_matPow_vec_tendsto_fixedProjector_of_range_tendsto_zero
    (n : ℕ) (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D)
    (v : Fin n → ℝ)
    (hRange : ∀ i, Filter.Tendsto
      (fun m : ℕ => matMulVec n (matMul n (matPow n G m)
        (stationaryDrazinRangeProjector n G D)) v i)
      Filter.atTop (nhds 0)) :
    ∀ i, Filter.Tendsto
      (fun m : ℕ => matMulVec n (matPow n G m) v i)
      Filter.atTop
      (nhds (matMulVec n (stationaryDrazinFixedProjector n G D) v i)) := by
  intro i
  let E := stationaryDrazinRangeProjector n G D
  let C := stationaryDrazinFixedProjector n G D
  have hRangeE : Filter.Tendsto
      (fun m : ℕ => matMulVec n (matMul n (matPow n G m) E) v i)
      Filter.atTop (nhds 0) := by
    simpa [E] using hRange i
  have hlimSplit : Filter.Tendsto
      (fun m : ℕ =>
        matMulVec n (matMul n (matPow n G m) E) v i +
          matMulVec n C v i)
      Filter.atTop (nhds (0 + matMulVec n C v i)) := by
    exact hRangeE.add tendsto_const_nhds
  have hcongr :
      (fun m : ℕ =>
        matMulVec n (matMul n (matPow n G m) E) v i +
          matMulVec n C v i) =ᶠ[Filter.atTop]
      (fun m : ℕ => matMulVec n (matPow n G m) v i) := by
    exact Filter.Eventually.of_forall fun m => by
      have hsplit := stationaryDrazin_matPow_vec_split n G D hD v m i
      simpa [E, C] using hsplit.symm
  exact Filter.Tendsto.congr'
    (f₁ := fun m : ℕ =>
      matMulVec n (matMul n (matPow n G m) E) v i + matMulVec n C v i)
    (f₂ := fun m : ℕ => matMulVec n (matPow n G m) v i)
    hcongr
    (by simpa [C] using hlimSplit)

/-- Vector-action form of `stationaryDrazinFixedProjector_fixed_by_G`. -/
theorem stationaryDrazinFixedProjector_matMulVec_fixed (n : ℕ)
    (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D)
    (v : Fin n → ℝ) :
    ∀ i, matMulVec n G
        (matMulVec n (stationaryDrazinFixedProjector n G D) v) i =
      matMulVec n (stationaryDrazinFixedProjector n G D) v i := by
  intro i
  calc
    matMulVec n G (matMulVec n (stationaryDrazinFixedProjector n G D) v) i
        = matMulVec n
            (matMul n G (stationaryDrazinFixedProjector n G D)) v i := by
            rw [← matMulVec_matMul]
    _ = matMulVec n (stationaryDrazinFixedProjector n G D) v i := by
            rw [stationaryDrazinFixedProjector_fixed_by_G n G D hD]

/-- The Drazin range projector supplies the fixed-null hypothesis required by
    the finite singular error split: `G` fixes `(I - E)M^{-1}xi_t`. -/
theorem stationaryDrazinRangeProjector_null_component_fixed (n : ℕ)
    (G D M_inv : Fin n → Fin n → ℝ) (xi : ℕ → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D) :
    ∀ t i,
      matMulVec n G
        (matMulVec n (matSub_id n (stationaryDrazinRangeProjector n G D))
          (matMulVec n M_inv (xi t))) i =
      matMulVec n (matSub_id n (stationaryDrazinRangeProjector n G D))
        (matMulVec n M_inv (xi t)) i := by
  intro t i
  simpa [stationaryDrazinFixedProjector] using
    stationaryDrazinFixedProjector_matMulVec_fixed n G D hD
      (matMulVec n M_inv (xi t)) i



































































































































































/-- Higham, 2nd ed., Chapter 17, Section 17.4, equations (17.24), (17.27),
    and (17.28): finite singular-system error split with the source Drazin
    projector `E = (I - G)(I - G)^D`.

    Compared with `singular_error_split_finite`, this wrapper no longer asks
    for the fixed-null hypothesis separately: it is supplied by the
    index-one Drazin inverse certificate for `I - G`.  The limiting
    semiconvergence and infinite-sum bounds remain separate obligations. -/
theorem singular_error_split_finite_of_indexOneDrazin_projector (n : ℕ)
    (A M N M_inv D : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (hD : IndexOneDrazinInverse n (matSub_id n (iterMatrix n M_inv N)) D)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (xi : ℕ → Fin n → ℝ)
    (hIter : SourceComputedIteration n M N b x_hat xi)
    (m : ℕ) :
    ∀ i, x i - x_hat (m + 1) i =
      matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1))
        (fun j => x j - x_hat 0 j) i +
      singularErrorSourceTerm n (iterMatrix n M_inv N)
        (stationaryDrazinRangeProjector n (iterMatrix n M_inv N) D)
        M_inv xi m i +
      matMulVec n
        (stationaryDrazinFixedProjector n (iterMatrix n M_inv N) D)
        (matMulVec n M_inv
          (fun j => ∑ k ∈ Finset.range (m + 1), xi (m - k) j)) i := by
  intro i
  have hNull :
      ∀ t r,
        matMulVec n (iterMatrix n M_inv N)
          (matMulVec n
            (matSub_id n
              (stationaryDrazinRangeProjector n (iterMatrix n M_inv N) D))
            (matMulVec n M_inv (xi t))) r =
        matMulVec n
          (matSub_id n
            (stationaryDrazinRangeProjector n (iterMatrix n M_inv N) D))
          (matMulVec n M_inv (xi t)) r := by
    intro t r
    exact stationaryDrazinRangeProjector_null_component_fixed
      n (iterMatrix n M_inv N) D M_inv xi hD t r
  have hsplit := singular_error_split_finite n A M N M_inv
    (stationaryDrazinRangeProjector n (iterMatrix n M_inv N) D)
    hS b x hAx x_hat xi hIter hNull m i
  simpa [stationaryDrazinFixedProjector] using hsplit




























/-- The action defining `S_m` is the matrix product
    `(G^k E M⁻¹) ξ_{m-k}` term by term. -/
private theorem singularErrorSourceTerm_term_eq (n : ℕ)
    (G E M_inv : Fin n → Fin n → ℝ) (ξ : ℕ → Fin n → ℝ)
    (m k : ℕ) :
    matMulVec n (matPow n G k)
        (matMulVec n E (matMulVec n M_inv (ξ (m - k)))) =
      matMulVec n (matMul n (matMul n (matPow n G k) E) M_inv)
        (ξ (m - k)) := by
  ext i
  calc
    matMulVec n (matPow n G k)
        (matMulVec n E (matMulVec n M_inv (ξ (m - k)))) i =
      matMulVec n (matMul n (matPow n G k) E)
        (matMulVec n M_inv (ξ (m - k))) i := by
        rw [← matMulVec_matMul]
    _ = matMulVec n (matMul n (matMul n (matPow n G k) E) M_inv)
        (ξ (m - k)) i := by
        rw [← matMulVec_matMul]

/-- Higham, 2nd ed., Chapter 17, Section 17.4, equation (17.29), finite
    normwise surface: a uniform local-error norm bound `||ξ_t||∞ ≤ μ` bounds
    `||S_m||∞` by `μ sum ||G^k E M⁻¹||∞`.  The source's displayed
    `c_n u(1+gamma_x)(||M||∞+||N||∞)||x||∞` is obtained by instantiating `μ`
    with the normwise local-error estimate. -/
theorem singularErrorSourceTerm_norm_bound (n : ℕ) (hn : 0 < n)
    (G E M_inv : Fin n → Fin n → ℝ) (ξ : ℕ → Fin n → ℝ)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hξ : ∀ t : ℕ, infNormVec (ξ t) ≤ μ) (m : ℕ) :
    infNormVec (singularErrorSourceTerm n G E M_inv ξ m) ≤
      μ * singularErrorSourceNormSum n G E M_inv m := by
  apply infNormVec_le_of_abs_le
  · intro i
    calc
      |singularErrorSourceTerm n G E M_inv ξ m i|
          = |∑ k ∈ Finset.range (m + 1),
              matMulVec n (matPow n G k)
                (matMulVec n E (matMulVec n M_inv (ξ (m - k)))) i| := by
              rfl
      _ ≤ ∑ k ∈ Finset.range (m + 1),
            |matMulVec n (matPow n G k)
              (matMulVec n E (matMulVec n M_inv (ξ (m - k)))) i| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (m + 1),
            infNorm (matMul n (matMul n (matPow n G k) E) M_inv) * μ := by
            apply Finset.sum_le_sum
            intro k _hk
            let P := matMul n (matMul n (matPow n G k) E) M_inv
            have hterm :=
              congrFun (singularErrorSourceTerm_term_eq n G E M_inv ξ m k) i
            calc
              |matMulVec n (matPow n G k)
                  (matMulVec n E (matMulVec n M_inv (ξ (m - k)))) i|
                  = |matMulVec n P (ξ (m - k)) i| := by
                    rw [hterm]
              _ ≤ infNormVec (matMulVec n P (ξ (m - k))) :=
                    abs_le_infNormVec _ i
              _ ≤ infNorm P * infNormVec (ξ (m - k)) :=
                    infNormVec_matMulVec_le hn P (ξ (m - k))
              _ ≤ infNorm P * μ := by
                    exact mul_le_mul_of_nonneg_left (hξ (m - k)) (infNorm_nonneg P)
      _ = μ * singularErrorSourceNormSum n G E M_inv m := by
            unfold singularErrorSourceNormSum
            rw [← Finset.sum_mul]
            ring
  · unfold singularErrorSourceNormSum
    exact mul_nonneg hμ
      (Finset.sum_nonneg (fun k _hk => infNorm_nonneg _))

/-- Higham, 2nd ed., Chapter 17, Section 17.4, equation (17.29), finite
    componentwise surface: if the local errors satisfy the already-simplified
    componentwise source bound, then the singular source term `S_m` is bounded
    by `c_n u(1+theta_x) sum |G^k E M⁻¹|(|M|+|N|)|x|`. -/
theorem singularErrorSourceTerm_componentwise_bound (n : ℕ)
    (G E M_inv M N : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (ξ : ℕ → Fin n → ℝ) (cn_u theta_x : ℝ)
    (hξ : ∀ (t : ℕ) (j : Fin n),
      |ξ t j| ≤ cn_u * (1 + theta_x) *
        stationaryLocalErrorSourceVector n M N x j)
    (m : ℕ) :
    ∀ i, |singularErrorSourceTerm n G E M_inv ξ m i| ≤
      singularErrorSourceComponentBound n G E M_inv M N x cn_u theta_x m i := by
  intro i
  let coeff := cn_u * (1 + theta_x)
  calc
    |singularErrorSourceTerm n G E M_inv ξ m i|
        = |∑ k ∈ Finset.range (m + 1),
            matMulVec n (matPow n G k)
              (matMulVec n E (matMulVec n M_inv (ξ (m - k)))) i| := by
            rfl
    _ ≤ ∑ k ∈ Finset.range (m + 1),
          |matMulVec n (matPow n G k)
            (matMulVec n E (matMulVec n M_inv (ξ (m - k)))) i| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (m + 1),
          coeff *
            matMulVec n
              (absMatrix n (matMul n (matMul n (matPow n G k) E) M_inv))
              (stationaryLocalErrorSourceVector n M N x) i := by
          apply Finset.sum_le_sum
          intro k _hk
          let P := matMul n (matMul n (matPow n G k) E) M_inv
          have hterm :=
            congrFun (singularErrorSourceTerm_term_eq n G E M_inv ξ m k) i
          calc
            |matMulVec n (matPow n G k)
                (matMulVec n E (matMulVec n M_inv (ξ (m - k)))) i|
                = |matMulVec n P (ξ (m - k)) i| := by
                  rw [hterm]
            _ ≤ ∑ j : Fin n, |P i j| * |ξ (m - k) j| :=
                  abs_matMulVec_le n P (ξ (m - k)) i
            _ ≤ ∑ j : Fin n, |P i j| *
                  (coeff * stationaryLocalErrorSourceVector n M N x j) := by
                  apply Finset.sum_le_sum
                  intro j _hj
                  exact mul_le_mul_of_nonneg_left
                    (by simpa [coeff] using hξ (m - k) j) (abs_nonneg _)
            _ = coeff *
                  matMulVec n (absMatrix n P)
                    (stationaryLocalErrorSourceVector n M N x) i := by
                  unfold matMulVec absMatrix
                  rw [Finset.mul_sum]
                  exact Finset.sum_congr rfl (fun j _hj => by ring)
    _ = singularErrorSourceComponentBound n G E M_inv M N x cn_u theta_x m i := by
          unfold singularErrorSourceComponentBound
          rw [← Finset.mul_sum]

-- ============================================================
-- §17.2  Componentwise forward bound (eq 17.6)
-- ============================================================







































-- ============================================================
-- §17.2  Iterate-growth constants (eqs 17.7, 17.9)
-- ============================================================
































































































-- ============================================================
-- §17.2  Local error bound and simplification (eqs 17.2, 17.10)
-- ============================================================



























































































































































































/-- Higham, 2nd ed., Chapter 17, Section 17.4, equation (17.29), normwise
    surface instantiated from the source local-error model (17.2) and
    `gamma_x` iterate-growth hypothesis (17.7). -/
theorem singularErrorSourceTerm_norm_bound_of_local_error (n : ℕ) (hn : 0 < n)
    (G E M_inv M N : Fin n → Fin n → ℝ)
    (b x : Fin n → ℝ)
    (hAx : ∀ i, ∑ j : Fin n, (M i j - N i j) * x j = b i)
    (x_hat ξ : ℕ → Fin n → ℝ) (cn_u gamma_x : ℝ)
    (hcn : 0 ≤ cn_u) (hgamma : 0 ≤ gamma_x)
    (hx_bound : NormwiseIterateGrowthBound n x x_hat gamma_x)
    (hLocal : LocalErrorBound n M N b x_hat ξ cn_u)
    (m : ℕ) :
    infNormVec (singularErrorSourceTerm n G E M_inv ξ m) ≤
      cn_u * (1 + gamma_x) * (infNorm M + infNorm N) * infNormVec x *
        singularErrorSourceNormSum n G E M_inv m := by
  let μ := cn_u * (1 + gamma_x) * (infNorm M + infNorm N) * infNormVec x
  have hμ : 0 ≤ μ := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hcn (by linarith))
        (add_nonneg (infNorm_nonneg M) (infNorm_nonneg N)))
      (infNormVec_nonneg x)
  have hξ :
      ∀ t : ℕ, infNormVec (ξ t) ≤ μ := by
    simpa [μ] using
      local_error_normwise_simplified n M N b x hAx x_hat ξ
        cn_u gamma_x hcn hgamma hx_bound hLocal
  simpa [μ] using
    singularErrorSourceTerm_norm_bound n hn G E M_inv ξ μ hμ hξ m

/-- Higham, 2nd ed., Chapter 17, Section 17.4, equation (17.29), instantiated
    componentwise surface: the displayed bound for `S_m` follows from the
    source local-error model (17.2), the exact equation `Mx-Nx=b`, and the
    componentwise iterate-growth hypothesis from (17.9). -/
theorem singularErrorSourceTerm_componentwise_bound_of_local_error (n : ℕ)
    (G E M_inv M N : Fin n → Fin n → ℝ)
    (b x : Fin n → ℝ)
    (hAx : ∀ i, ∑ j : Fin n, (M i j - N i j) * x j = b i)
    (x_hat ξ : ℕ → Fin n → ℝ) (cn_u theta_x : ℝ)
    (hcn : 0 ≤ cn_u) (hθ : 0 ≤ theta_x)
    (hx_bound : ComponentwiseIterateGrowthBound n x x_hat theta_x)
    (hLocal : LocalErrorBound n M N b x_hat ξ cn_u)
    (m : ℕ) :
    ∀ i, |singularErrorSourceTerm n G E M_inv ξ m i| ≤
      singularErrorSourceComponentBound n G E M_inv M N x cn_u theta_x m i := by
  have hξ :
      ∀ (t : ℕ) (j : Fin n),
        |ξ t j| ≤ cn_u * (1 + theta_x) *
          stationaryLocalErrorSourceVector n M N x j := by
    intro t j
    simpa [stationaryLocalErrorSourceVector] using
      local_error_simplified n M N b x hAx x_hat ξ cn_u theta_x
        hcn hθ hx_bound hLocal t j
  exact singularErrorSourceTerm_componentwise_bound
    n G E M_inv M N x ξ cn_u theta_x hξ m

-- ============================================================
-- §17.2  c(A) constant and main bound (eqs 17.12–17.13)
-- ============================================================







-- ============================================================
-- §17.2.1  Jacobi specialization
-- ============================================================













-- ============================================================
-- §17.2.2  SOR specialization
-- ============================================================




























































-- ============================================================
-- §17.3  Backward error — residual identity and sigma bound
-- ============================================================











/-- Geometric series partial sum bound: ∑_{k=0}^m q^k ≤ 1/(1-q) for 0 ≤ q < 1. -/
private theorem geom_partial_sum_le (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), q ^ k ≤ 1 / (1 - q) := by
  have hq1' : (0 : ℝ) < 1 - q := by linarith
  rw [le_div_iff₀ hq1']
  calc (∑ k ∈ Finset.range (m + 1), q ^ k) * (1 - q)
      = ∑ k ∈ Finset.range (m + 1), (q ^ k - q ^ (k + 1)) := by
        rw [Finset.sum_mul]; congr 1; ext k; ring
    _ = 1 - q ^ (m + 1) := by
        induction m with
        | zero => simp
        | succ m ih =>
          rw [Finset.sum_range_succ]; linarith
    _ ≤ 1 := by linarith [pow_nonneg hq (m + 1)]

/-- **σ bound** (§17.3): ∑_{k=0}^m ‖H^k(I−H)‖∞ ≤ ‖I−H‖∞/(1−q) when ‖H‖∞ ≤ q < 1. -/
theorem sigma_bound (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hH : infNorm H ≤ q) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1),
      infNorm (matMul n (matPow n H k) (matSub_id n H)) ≤
    infNorm (matSub_id n H) / (1 - q) := by
  have hq1' : (0 : ℝ) < 1 - q := by linarith
  calc ∑ k ∈ Finset.range (m + 1),
        infNorm (matMul n (matPow n H k) (matSub_id n H))
      ≤ ∑ k ∈ Finset.range (m + 1),
        (q ^ k * infNorm (matSub_id n H)) := by
        gcongr with k _
        calc infNorm (matMul n (matPow n H k) (matSub_id n H))
            ≤ infNorm (matPow n H k) * infNorm (matSub_id n H) :=
              infNorm_matMul_le hn _ _
          _ ≤ q ^ k * infNorm (matSub_id n H) := by
              apply mul_le_mul_of_nonneg_right _ (infNorm_nonneg _)
              exact (infNorm_matPow_le hn H k).trans (pow_le_pow_left₀ (infNorm_nonneg H) hH k)
    _ = (∑ k ∈ Finset.range (m + 1), q ^ k) * infNorm (matSub_id n H) := by
        rw [Finset.sum_mul]
    _ ≤ (1 / (1 - q)) * infNorm (matSub_id n H) := by
        apply mul_le_mul_of_nonneg_right (geom_partial_sum_le q hq hq1 m) (infNorm_nonneg _)
    _ = infNorm (matSub_id n H) / (1 - q) := by
        rw [one_div, mul_comm, div_eq_mul_inv]






























































































































private theorem residual_geometric_partial_le_ratio (lam : ℝ)
    (hLam : |lam| < 1) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), |lam| ^ k * |1 - lam| ≤
      |1 - lam| / (1 - |lam|) := by
  have hden : 0 < 1 - |lam| := by linarith
  calc
    ∑ k ∈ Finset.range (m + 1), |lam| ^ k * |1 - lam|
        = (∑ k ∈ Finset.range (m + 1), |lam| ^ k) * |1 - lam| := by
            rw [Finset.sum_mul]
    _ ≤ (1 / (1 - |lam|)) * |1 - lam| := by
            exact mul_le_mul_of_nonneg_right
              (geom_partial_sum_le |lam| (abs_nonneg lam) hLam m) (abs_nonneg _)
    _ = |1 - lam| / (1 - |lam|) := by
            rw [one_div, div_eq_mul_inv]
            ring

private theorem residual_term_entry_abs_le_of_real_diagonalization (n : ℕ)
    (H X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n H X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (k : ℕ) (i j : Fin n) :
    |matMul n (matPow n H k) (matSub_id n H) i j| ≤
      ∑ a : Fin n, |X i a| * (|J a a| ^ k * |1 - J a a|) * |X_inv a j| := by
  have hterm :
      matMul n (matPow n H k) (matSub_id n H) i j =
        matPow n H k i j - matPow n H (k + 1) i j := by
    unfold matMul matSub_id
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    have hid :
        (∑ l : Fin n, matPow n H k i l * idMatrix n l j) =
          matPow n H k i j := by
      unfold idMatrix
      simp [Finset.sum_ite_eq', Finset.mem_univ]
    have hmul :
        (∑ l : Fin n, matPow n H k i l * H l j) =
          matPow n H (k + 1) i j := by
      rw [matPow_succ_right n H k]
      rfl
    rw [hid, hmul]
  have hpow_entry :
      ∀ p (r c : Fin n),
        matPow n H p r c =
          ∑ a : Fin n, X r a * (J a a ^ p * X_inv a c) := by
    intro p r c
    have hpow := congrFun
      (congrFun (matPow_similarity n H X X_inv J hXr hXl hsim p) r) c
    rw [hpow]
    unfold matMul
    apply Finset.sum_congr rfl
    intro a _ha
    congr 1
    have hinner :
        (∑ b : Fin n, matPow n J p a b * X_inv b c) =
          J a a ^ p * X_inv a c := by
      rw [Finset.sum_eq_single a]
      · rw [matPow_diagonal n J hdiag p a a, if_pos rfl]
      · intro b _hb hba
        rw [matPow_diagonal n J hdiag p a b, if_neg (Ne.symm hba), zero_mul]
      · intro hnot
        exact absurd (Finset.mem_univ a) hnot
    exact hinner
  have hsource :
      matMul n (matPow n H k) (matSub_id n H) i j =
        ∑ a : Fin n, X i a * (J a a ^ k * (1 - J a a) * X_inv a j) := by
    rw [hterm, hpow_entry k i j, hpow_entry (k + 1) i j]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [pow_succ]
    ring
  rw [hsource]
  calc
    |∑ a : Fin n, X i a * (J a a ^ k * (1 - J a a) * X_inv a j)|
        ≤ ∑ a : Fin n, |X i a * (J a a ^ k * (1 - J a a) * X_inv a j)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a : Fin n,
          |X i a| * (|J a a| ^ k * |1 - J a a|) * |X_inv a j| := by
          apply Finset.sum_congr rfl
          intro a _ha
          rw [abs_mul, abs_mul, abs_mul, abs_pow]
          ring

/-- Higham, 2nd ed., Chapter 17, Section 17.3, equation (17.20), finite
    diagonalization-certificate form: if `H = X J X^{-1}` with diagonal `J`
    and `|lambda_i| < 1`, then every finite source-sigma partial matrix is
    bounded by `kappa_infty(X) * max_i |1-lambda_i|/(1-|lambda_i|)`.

    The theorem takes the displayed maximum as an explicit scalar upper bound
    `sigmaDiag`; the literal infinite-series sigma is still a later wrapper. -/
theorem finiteResidualSigma_le_diagonalizable_bound (n : ℕ) (_hn : 0 < n)
    (H X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n H X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (sigmaDiag : ℝ) (hsigma : 0 ≤ sigmaDiag)
    (hLam : ∀ i : Fin n, |J i i| < 1)
    (hratio : ∀ i : Fin n, |1 - J i i| / (1 - |J i i|) ≤ sigmaDiag)
    (m : ℕ) :
    finiteResidualSigma n H m ≤ (infNorm X * infNorm X_inv) * sigmaDiag := by
  unfold finiteResidualSigma
  apply infNorm_le_of_row_sum_le
  · intro i
    have hrowEntry_nonneg :
        ∀ j : Fin n, 0 ≤ finiteResidualSigmaMatrix n H m i j := by
      intro j
      unfold finiteResidualSigmaMatrix
      exact Finset.sum_nonneg (fun k _hk => abs_nonneg _)
    calc
      ∑ j : Fin n, |finiteResidualSigmaMatrix n H m i j|
          = ∑ j : Fin n, finiteResidualSigmaMatrix n H m i j := by
              apply Finset.sum_congr rfl
              intro j _hj
              exact abs_of_nonneg (hrowEntry_nonneg j)
      _ = ∑ j : Fin n, ∑ k ∈ Finset.range (m + 1),
            |matMul n (matPow n H k) (matSub_id n H) i j| := by
              rfl
      _ ≤ ∑ j : Fin n, ∑ a : Fin n,
            |X i a| * sigmaDiag * |X_inv a j| := by
              apply Finset.sum_le_sum
              intro j _hj
              calc
                ∑ k ∈ Finset.range (m + 1),
                    |matMul n (matPow n H k) (matSub_id n H) i j|
                    ≤ ∑ k ∈ Finset.range (m + 1), ∑ a : Fin n,
                        |X i a| * (|J a a| ^ k * |1 - J a a|) *
                          |X_inv a j| := by
                        apply Finset.sum_le_sum
                        intro k _hk
                        exact residual_term_entry_abs_le_of_real_diagonalization
                          n H X X_inv J hXr hXl hsim hdiag k i j
                _ = ∑ a : Fin n, ∑ k ∈ Finset.range (m + 1),
                        |X i a| * (|J a a| ^ k * |1 - J a a|) *
                          |X_inv a j| := by
                        rw [Finset.sum_comm]
                _ ≤ ∑ a : Fin n, |X i a| * sigmaDiag * |X_inv a j| := by
                        apply Finset.sum_le_sum
                        intro a _ha
                        have hgeom :
                            ∑ k ∈ Finset.range (m + 1),
                              |J a a| ^ k * |1 - J a a| ≤ sigmaDiag :=
                            (residual_geometric_partial_le_ratio (J a a)
                            (hLam a) m).trans (hratio a)
                        calc
                          ∑ k ∈ Finset.range (m + 1),
                              |X i a| * (|J a a| ^ k * |1 - J a a|) *
                                |X_inv a j|
                              = |X i a| *
                                  (∑ k ∈ Finset.range (m + 1),
                                    |J a a| ^ k * |1 - J a a|) *
                                  |X_inv a j| := by
                                  rw [Finset.mul_sum, Finset.sum_mul]
                          _ ≤ |X i a| * sigmaDiag * |X_inv a j| := by
                                  exact mul_le_mul_of_nonneg_right
                                    (mul_le_mul_of_nonneg_left hgeom (abs_nonneg _))
                                    (abs_nonneg _)
      _ = ∑ a : Fin n, |X i a| * sigmaDiag * (∑ j : Fin n, |X_inv a j|) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro a _ha
              rw [← Finset.mul_sum]
      _ ≤ ∑ a : Fin n, |X i a| * sigmaDiag * infNorm X_inv := by
              apply Finset.sum_le_sum
              intro a _ha
              exact mul_le_mul_of_nonneg_left
                (row_sum_le_infNorm X_inv a)
                (mul_nonneg (abs_nonneg _) hsigma)
      _ = sigmaDiag * infNorm X_inv * (∑ a : Fin n, |X i a|) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro a _ha
              ring
      _ ≤ sigmaDiag * infNorm X_inv * infNorm X := by
              exact mul_le_mul_of_nonneg_left
                (row_sum_le_infNorm X i)
                (mul_nonneg hsigma (infNorm_nonneg _))
      _ = (infNorm X * infNorm X_inv) * sigmaDiag := by
              ring
  · exact mul_nonneg (mul_nonneg (infNorm_nonneg X) (infNorm_nonneg X_inv)) hsigma

/-- Higham, 2nd ed., Chapter 17, Section 17.3, equation (17.20), finite
    maximum form: if `H = X J X^{-1}` with diagonal `J` and `|lambda_i| < 1`,
    then every finite source-sigma partial norm is bounded by
    `kappa_infty(X)` times the displayed maximum eigenvalue ratio. -/
theorem finiteResidualSigma_le_diagonalizable_max_bound (n : ℕ) (hn : 0 < n)
    (H X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n H X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (hLam : ∀ i : Fin n, |J i i| < 1)
    (m : ℕ) :
    finiteResidualSigma n H m ≤
      (infNorm X * infNorm X_inv) * diagonalResidualRatioMax n J hn := by
  exact finiteResidualSigma_le_diagonalizable_bound n hn H X X_inv J
    hXr hXl hsim hdiag (diagonalResidualRatioMax n J hn)
    (diagonalResidualRatioMax_nonneg n J hn hLam) hLam
    (diagonalResidualRatio_le_max n J hn) m

private theorem residualSigmaTsum_entry_le_of_real_diagonalization (n : ℕ)
    (H X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n H X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (sigmaDiag : ℝ)
    (hLam : ∀ i : Fin n, |J i i| < 1)
    (hratio : ∀ i : Fin n, |1 - J i i| / (1 - |J i i|) ≤ sigmaDiag)
    (i j : Fin n) :
    residualSigmaTsumMatrix n H i j ≤
      ∑ a : Fin n, |X i a| * sigmaDiag * |X_inv a j| := by
  let f : ℕ → ℝ :=
    fun k => |matMul n (matPow n H k) (matSub_id n H) i j|
  let g : ℕ → ℝ :=
    fun k => ∑ a : Fin n,
      |X i a| * (|J a a| ^ k * |1 - J a a|) * |X_inv a j|
  have hfg : ∀ k : ℕ, f k ≤ g k := by
    intro k
    simpa [f, g] using
      residual_term_entry_abs_le_of_real_diagonalization
        n H X X_inv J hXr hXl hsim hdiag k i j
  have hg_a : ∀ a : Fin n,
      Summable (fun k : ℕ =>
        |X i a| * (|J a a| ^ k * |1 - J a a|) * |X_inv a j|) := by
    intro a
    have hgeom : Summable (fun k : ℕ => |J a a| ^ k) :=
      summable_geometric_of_lt_one (abs_nonneg _) (hLam a)
    have hscaled :
        Summable (fun k : ℕ => |J a a| ^ k * |1 - J a a|) :=
      Summable.mul_right _ hgeom
    have hleft :
        Summable (fun k : ℕ =>
          |X i a| * (|J a a| ^ k * |1 - J a a|)) :=
      Summable.mul_left _ hscaled
    exact Summable.mul_right _ hleft
  have hg : Summable g := by
    dsimp [g]
    simpa using
      (summable_sum (s := Finset.univ)
        (fun a _ha => hg_a a))
  have hf : Summable f :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hfg hg
  have hle_tsum : (∑' k : ℕ, f k) ≤ ∑' k : ℕ, g k :=
    Summable.tsum_le_tsum hfg hf hg
  have hg_tsum_eq :
      (∑' k : ℕ, g k) =
        ∑ a : Fin n, ∑' k : ℕ,
          |X i a| * (|J a a| ^ k * |1 - J a a|) * |X_inv a j| := by
    dsimp [g]
    simpa using
      (Summable.tsum_finsetSum (s := Finset.univ)
        (fun a _ha => hg_a a))
  have hg_tsum_le :
      (∑' k : ℕ, g k) ≤
        ∑ a : Fin n, |X i a| * sigmaDiag * |X_inv a j| := by
    rw [hg_tsum_eq]
    apply Finset.sum_le_sum
    intro a _ha
    have hgeom_tsum :
        (∑' k : ℕ, |J a a| ^ k * |1 - J a a|) =
          |1 - J a a| / (1 - |J a a|) := by
      rw [tsum_mul_right, tsum_geometric_of_lt_one (abs_nonneg _) (hLam a)]
      rw [div_eq_mul_inv, mul_comm]
    have hweighted_tsum :
        (∑' k : ℕ,
          |X i a| * (|J a a| ^ k * |1 - J a a|) * |X_inv a j|) =
          |X i a| * (|1 - J a a| / (1 - |J a a|)) * |X_inv a j| := by
      rw [tsum_mul_right, tsum_mul_left, hgeom_tsum]
    rw [hweighted_tsum]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hratio a) (abs_nonneg _))
      (abs_nonneg _)
  calc
    residualSigmaTsumMatrix n H i j = ∑' k : ℕ, f k := by rfl
    _ ≤ ∑' k : ℕ, g k := hle_tsum
    _ ≤ ∑ a : Fin n, |X i a| * sigmaDiag * |X_inv a j| := hg_tsum_le

/-- Higham, 2nd ed., Chapter 17, Section 17.3, equation (17.20), literal
    `tsum` diagonalization-certificate form: if `H = X J X^{-1}` with diagonal
    `J` and `|lambda_i| < 1`, then the entrywise infinite source residual sigma
    is bounded by `kappa_infty(X) * sigmaDiag`. -/
theorem residualSigmaTsum_le_diagonalizable_bound (n : ℕ) (_hn : 0 < n)
    (H X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n H X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (sigmaDiag : ℝ) (hsigma : 0 ≤ sigmaDiag)
    (hLam : ∀ i : Fin n, |J i i| < 1)
    (hratio : ∀ i : Fin n, |1 - J i i| / (1 - |J i i|) ≤ sigmaDiag) :
    residualSigmaTsum n H ≤ (infNorm X * infNorm X_inv) * sigmaDiag := by
  apply residualSigmaTsum_le_of_row_sum_le
  · intro i
    have hentry_nonneg :
        ∀ j : Fin n, 0 ≤ residualSigmaTsumMatrix n H i j := by
      intro j
      unfold residualSigmaTsumMatrix
      exact tsum_nonneg (fun k => abs_nonneg _)
    calc
      ∑ j : Fin n, |residualSigmaTsumMatrix n H i j|
          = ∑ j : Fin n, residualSigmaTsumMatrix n H i j := by
              apply Finset.sum_congr rfl
              intro j _hj
              exact abs_of_nonneg (hentry_nonneg j)
      _ ≤ ∑ j : Fin n, ∑ a : Fin n,
            |X i a| * sigmaDiag * |X_inv a j| := by
              apply Finset.sum_le_sum
              intro j _hj
              exact residualSigmaTsum_entry_le_of_real_diagonalization
                n H X X_inv J hXr hXl hsim hdiag sigmaDiag
                hLam hratio i j
      _ = ∑ a : Fin n, |X i a| * sigmaDiag *
            (∑ j : Fin n, |X_inv a j|) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro a _ha
              rw [← Finset.mul_sum]
      _ ≤ ∑ a : Fin n, |X i a| * sigmaDiag * infNorm X_inv := by
              apply Finset.sum_le_sum
              intro a _ha
              exact mul_le_mul_of_nonneg_left
                (row_sum_le_infNorm X_inv a)
                (mul_nonneg (abs_nonneg _) hsigma)
      _ = sigmaDiag * infNorm X_inv * (∑ a : Fin n, |X i a|) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro a _ha
              ring
      _ ≤ sigmaDiag * infNorm X_inv * infNorm X := by
              exact mul_le_mul_of_nonneg_left
                (row_sum_le_infNorm X i)
                (mul_nonneg hsigma (infNorm_nonneg _))
      _ = (infNorm X * infNorm X_inv) * sigmaDiag := by
              ring
  · exact mul_nonneg (mul_nonneg (infNorm_nonneg X) (infNorm_nonneg X_inv)) hsigma

/-- Higham, 2nd ed., Chapter 17, Section 17.3, equation (17.20), literal
    `tsum` maximum form: the entrywise infinite source residual sigma is bounded
    by `kappa_infty(X)` times the displayed maximum eigenvalue ratio. -/
theorem residualSigmaTsum_le_diagonalizable_max_bound_direct (n : ℕ) (hn : 0 < n)
    (H X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n H X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (hLam : ∀ i : Fin n, |J i i| < 1) :
    residualSigmaTsum n H ≤
      (infNorm X * infNorm X_inv) * diagonalResidualRatioMax n J hn := by
  exact residualSigmaTsum_le_diagonalizable_bound n hn H X X_inv J
    hXr hXl hsim hdiag (diagonalResidualRatioMax n J hn)
    (diagonalResidualRatioMax_nonneg n J hn hLam) hLam
    (diagonalResidualRatio_le_max n J hn)

/-- Higham, 2nd ed., Chapter 17, Section 17.3, equation (17.20), supremum
    wrapper: the supremum of all finite source-sigma partial norms is bounded by
    `kappa_infty(X)` times the displayed maximum eigenvalue ratio.  This is a
    source-facing infinite-sigma envelope, not a proof that an entrywise infinite
    matrix series has been constructed as a `tsum`. -/
theorem residualSigmaSup_le_diagonalizable_max_bound (n : ℕ) (hn : 0 < n)
    (H X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n H X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (hLam : ∀ i : Fin n, |J i i| < 1) :
    residualSigmaSup n H ≤
      (infNorm X * infNorm X_inv) * diagonalResidualRatioMax n J hn := by
  apply residualSigmaSup_le_of_finiteResidualSigma_le
  intro m
  exact finiteResidualSigma_le_diagonalizable_max_bound n hn H X X_inv J
    hXr hXl hsim hdiag hLam m

-- ============================================================
-- §17.3  Residual recurrence: r_{k+1} = Hr_k − (I−H)ξ_k
-- ============================================================







































































































































































-- ============================================================
-- §17.2  Normwise one-step bound and forward bound (eqs 17.5, 17.8)
-- ============================================================


























































































































-- ============================================================
-- §17.2  Main forward bound (eq 17.13)
-- ============================================================



























































































































































































































































































































































































































-- ============================================================
-- §17.3  Normwise residual bound (eq 17.19)
-- ============================================================






















































































































































-- ============================================================
-- §17.5  Stopping tests (eqs. 17.33a-c)
-- ============================================================



































































































































































































































end NumStability
