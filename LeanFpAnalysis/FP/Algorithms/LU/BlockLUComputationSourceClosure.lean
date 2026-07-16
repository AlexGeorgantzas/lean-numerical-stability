/-
  Algorithms/LU/BlockLUComputationSourceClosure.lean

  Computation-derived source endpoint for Higham Theorem 13.6.

  The earlier conventional-solve theorem executed both triangular solves but
  accepted a completed `PartitionedLUFirstOrderSpec` for the factorization.
  The theorem below closes that gap: it consumes the recursive Algorithm 13.1
  computation certificate, derives its Theorem 13.5 residual, and only then
  executes the conventional Algorithm 13.3 solve path.
-/

import LeanFpAnalysis.FP.Algorithms.LU.BlockLUFirstOrderFamilies

namespace LeanFpAnalysis.FP

open Filter Asymptotics
open scoped Topology

/-- Family-level aggregation for equation (13.16).  Unlike the legacy
pointwise adapter, the hidden quadratic constants here are uniform along the
roundoff filter. -/
theorem higham13_theorem13_6_eq13_16_family_from_factor_solve_bounds
    {ι : Type*} {l : Filter ι} (Uround : RoundoffFamily ι l)
    (dFact dSolve dn : ℝ)
    (normA normL normU normDeltaFact normDeltaSolve : ι → ℝ)
    (hA : ∀ t, 0 ≤ normA t) (hL : ∀ t, 0 ≤ normL t)
    (hU : ∀ t, 0 ≤ normU t)
    (hFactLe : dFact ≤ dn) (hSolveLe : dSolve ≤ dn)
    (hFact : FamilyFirstOrderLe l Uround.unit
      (fun t => dFact * Uround.unit t *
        (normA t + normL t * normU t)) normDeltaFact)
    (hSolve : FamilyFirstOrderLe l Uround.unit
      (fun t => dSolve * Uround.unit t *
        (normA t + normL t * normU t)) normDeltaSolve) :
    FamilyFirstOrderLe l Uround.unit
        (fun t => dn * Uround.unit t *
          (normA t + normL t * normU t)) normDeltaFact ∧
      FamilyFirstOrderLe l Uround.unit
        (fun t => dn * Uround.unit t *
          (normA t + normL t * normU t)) normDeltaSolve ∧
      FamilyFirstOrderLe l Uround.unit
        (fun t => dn * Uround.unit t *
          (normA t + normL t * normU t))
        (fun t => max (normDeltaFact t) (normDeltaSolve t)) := by
  have hFactDn := hFact.mono_leading (fun t => by
    have hscale : 0 ≤ Uround.unit t *
        (normA t + normL t * normU t) :=
      mul_nonneg (Uround.unit_nonneg t)
        (add_nonneg (hA t) (mul_nonneg (hL t) (hU t)))
    calc
      dFact * Uround.unit t * (normA t + normL t * normU t) =
          dFact * (Uround.unit t *
            (normA t + normL t * normU t)) := by ring
      _ ≤ dn * (Uround.unit t *
            (normA t + normL t * normU t)) :=
        mul_le_mul_of_nonneg_right hFactLe hscale
      _ = dn * Uround.unit t *
            (normA t + normL t * normU t) := by ring)
  have hSolveDn := hSolve.mono_leading (fun t => by
    have hscale : 0 ≤ Uround.unit t *
        (normA t + normL t * normU t) :=
      mul_nonneg (Uround.unit_nonneg t)
        (add_nonneg (hA t) (mul_nonneg (hL t) (hU t)))
    calc
      dSolve * Uround.unit t * (normA t + normL t * normU t) =
          dSolve * (Uround.unit t *
            (normA t + normL t * normU t)) := by ring
      _ ≤ dn * (Uround.unit t *
            (normA t + normL t * normU t)) :=
        mul_le_mul_of_nonneg_right hSolveLe hscale
      _ = dn * Uround.unit t *
            (normA t + normL t * normU t) := by ring)
  exact ⟨hFactDn, hSolveDn,
    FamilyFirstOrderLe.combineMax hFactDn hSolveDn |>.mono_leading
      (fun _ => (max_self _).le)⟩

/-- Family-level Theorem 13.6 factor/solve endpoint with the factorization
half derived from the recursive Algorithm 13.1 computation rather than
accepted as a completed `PartitionedLUFirstOrderSpec`.

The solve perturbation and its equation are tied to the actual displayed
matrix family.  `hSolve` is the remaining implementation-specific DHS solve
estimate; the theorem does not disguise it as a final factorization premise. -/
theorem higham13_theorem13_6_family_from_partitioned_computation_and_solve
    {ι : Type*} {l : Filter ι} (Uround : RoundoffFamily ι l)
    {n m p : ℕ} (hn : 0 < n)
    (c₁ c₂ c₃ dFact dSolve dn : ℝ)
    (A DeltaFact Lhat Uhat DeltaSolve :
      ι → Matrix (Fin n) (Fin n) ℝ)
    (xhat b : ι → Matrix (Fin n) (Fin p) ℝ)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hDelta : blockErrorDelta m ≤ dFact)
    (hTheta : blockErrorTheta c₁ c₂ c₃ m ≤ dFact)
    (hFactLe : dFact ≤ dn) (hSolveLe : dSolve ≤ dn)
    (hmatrix : ∀ t,
      PartitionedLUComputationFirstOrder (Uround.unit t) c₁ c₂ c₃ m
        (maxEntryNorm hn (A t)) (maxEntryNorm hn (Lhat t))
        (maxEntryNorm hn (Uhat t)) (maxEntryNorm hn (DeltaFact t))
        (A t) (DeltaFact t) (Lhat t) (Uhat t))
    (hscalar : Higham13PartitionedLUScalarFamilyComputation
      Uround c₁ c₂ c₃ m
      (fun t => maxEntryNorm hn (A t))
      (fun t => maxEntryNorm hn (Lhat t))
      (fun t => maxEntryNorm hn (Uhat t))
      (fun t => maxEntryNorm hn (DeltaFact t)))
    (hSolveEquation : ∀ t,
      (A t + DeltaSolve t) * xhat t = b t)
    (hSolve : FamilyFirstOrderLe l Uround.unit
      (fun t => dSolve * Uround.unit t *
        (maxEntryNorm hn (A t) +
          maxEntryNorm hn (Lhat t) * maxEntryNorm hn (Uhat t)))
      (fun t => maxEntryNorm hn (DeltaSolve t))) :
    Higham13PartitionedLUFamilySpec Uround hn (blockErrorDelta m)
        (blockErrorTheta c₁ c₂ c₃ m) A DeltaFact Lhat Uhat ∧
      (∀ t, (A t + DeltaSolve t) * xhat t = b t) ∧
      FamilyFirstOrderLe l Uround.unit
          (fun t => dn * Uround.unit t *
            (maxEntryNorm hn (A t) +
              maxEntryNorm hn (Lhat t) * maxEntryNorm hn (Uhat t)))
          (fun t => maxEntryNorm hn (DeltaFact t)) ∧
      FamilyFirstOrderLe l Uround.unit
          (fun t => dn * Uround.unit t *
            (maxEntryNorm hn (A t) +
              maxEntryNorm hn (Lhat t) * maxEntryNorm hn (Uhat t)))
          (fun t => maxEntryNorm hn (DeltaSolve t)) ∧
      FamilyFirstOrderLe l Uround.unit
          (fun t => dn * Uround.unit t *
            (maxEntryNorm hn (A t) +
              maxEntryNorm hn (Lhat t) * maxEntryNorm hn (Uhat t)))
          (fun t => max (maxEntryNorm hn (DeltaFact t))
            (maxEntryNorm hn (DeltaSolve t))) := by
  have hFact := higham13_theorem13_5_eq13_7_family_from_computation
    Uround hn c₁ c₂ c₃ A DeltaFact Lhat Uhat hc₁ hc₂ hc₃ hmatrix hscalar
  have hFactScaled : FamilyFirstOrderLe l Uround.unit
      (fun t => dFact * Uround.unit t *
        (maxEntryNorm hn (A t) +
          maxEntryNorm hn (Lhat t) * maxEntryNorm hn (Uhat t)))
      (fun t => maxEntryNorm hn (DeltaFact t)) := by
    apply hFact.norm_bound.mono_leading
    intro t
    have hA0 := maxEntryNorm_nonneg hn (A t)
    have hL0 := maxEntryNorm_nonneg hn (Lhat t)
    have hU0 := maxEntryNorm_nonneg hn (Uhat t)
    have hu0 := Uround.unit_nonneg t
    have hδA := mul_le_mul_of_nonneg_right hDelta hA0
    have hθLU := mul_le_mul_of_nonneg_right hTheta (mul_nonneg hL0 hU0)
    nlinarith [mul_nonneg hu0
      (add_nonneg hA0 (mul_nonneg hL0 hU0))]
  have hAll := higham13_theorem13_6_eq13_16_family_from_factor_solve_bounds
    Uround dFact dSolve dn
      (fun t => maxEntryNorm hn (A t))
      (fun t => maxEntryNorm hn (Lhat t))
      (fun t => maxEntryNorm hn (Uhat t))
      (fun t => maxEntryNorm hn (DeltaFact t))
      (fun t => maxEntryNorm hn (DeltaSolve t))
      (fun t => maxEntryNorm_nonneg hn (A t))
      (fun t => maxEntryNorm_nonneg hn (Lhat t))
      (fun t => maxEntryNorm_nonneg hn (Uhat t))
      hFactLe hSolveLe hFactScaled hSolve
  exact ⟨hFact, hSolveEquation, hAll.1, hAll.2.1, hAll.2.2⟩

/-- Higham Theorem 13.6 / equation (13.16), Implementation 1, with both the
partitioned factorization and conventional solve paths operation-derived.

The scalar norm occurring in the result is the actual max-entry norm of `A`;
the factor norms in the recursive computation certificate and conclusion are
likewise the actual norms of the flattened computed factors. -/
theorem
    higham13_theorem13_6_implementation1_from_partitioned_computation_and_conventional_recursive_solve
    {m r q : ℕ} {s : Type*}
    (fp : FPModel) (hm : 0 < m) (hr : 0 < r)
    (c₁ c₂ c₃ dFact dn : ℝ)
    (A DeltaFact : Matrix (Fin (m * r)) (Fin (m * r)) ℝ)
    (Lhat U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (b : Fin (m * r) → ℝ)
    (c₄ normLhat21 normA11 normE21 : ℝ)
    (Lhat21 A21 E21 : Matrix s (Fin r) ℝ)
    (A11 : Matrix (Fin r) (Fin r) ℝ)
    (hSmallProduct : (((m * r : ℕ) : ℝ) * fp.u) ≤ 1 / 2)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hδ : blockErrorDelta q ≤ dFact)
    (hθ : blockErrorTheta c₁ c₂ c₃ q ≤ dFact)
    (hdFact : dFact ≤ dn)
    (hdSolve : dFact + (((m * r : ℕ) : ℝ) ^ 2) +
      (((m * r : ℕ) : ℝ) *
        ((((m * r : ℕ) : ℝ) ^ 2 +
          4 * (((m * r : ℕ) : ℝ) + (r : ℝ))) +
          2 * (r : ℝ))) ≤ dn)
    (hFactComputation : PartitionedLUComputationFirstOrder
      fp.u c₁ c₂ c₃ q
      (maxEntryNorm (Nat.mul_pos hm hr) A)
      (maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Lhat))
      (maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin U))
      (maxEntryNorm (Nat.mul_pos hm hr) DeltaFact)
      A DeltaFact (blockMatrixFlatFin Lhat) (blockMatrixFlatFin U))
    (hStep2 : BlockSolveFirstOrderSpec
      fp.u c₄ normLhat21 normA11 normE21 Lhat21 A21 E21 A11)
    (hLdiag : ∀ i : Fin (m * r), blockMatrixFlatFin Lhat i i ≠ 0)
    (hLower : ∀ i j : Fin (m * r), i.val < j.val →
      blockMatrixFlatFin Lhat i j = 0)
    (hUUpper : ∀ i j : Fin m, j.val < i.val → U i j = 0)
    (hDiag : ∀ i : Fin m, ∀ a : Fin r, U i i a a ≠ 0)
    (hUpper : ∀ i : Fin m, ∀ a b : Fin r,
      b.val < a.val → U i i a b = 0) :
    ∃ (DeltaDiag : Fin m → Matrix (Fin r) (Fin r) ℝ)
      (DeltaL : Matrix (Fin (m * r)) (Fin (m * r)) ℝ)
      (DeltaU : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ),
      (∀ i : Fin m,
        maxEntryNorm hr (DeltaDiag i) ≤
          (2 * (r : ℝ)) * fp.u * maxEntryNorm hr (U i i)) ∧
      (∀ i j : Fin (m * r),
        |DeltaL i j| ≤ gamma fp (m * r) *
          |blockMatrixFlatFin Lhat i j|) ∧
      (blockMatrixFlatFin Lhat * blockMatrixFlatFin U = A + DeltaFact) ∧
      ((A + (DeltaFact + DeltaL * blockMatrixFlatFin U +
          blockMatrixFlatFin Lhat * blockMatrixFlatFin DeltaU +
          DeltaL * blockMatrixFlatFin DeltaU)) *
          blockMatrixRowsFlatFin
            (dhsBlockBackConventionalSolution fp U
              (dhsBlockForwardConventionalSolution fp Lhat b)) =
        (fun i (_k : Fin 1) => b i)) ∧
      ((Lhat21 * A11 = A21 + E21 ∧
          BlockSolveFirstOrderBound fp.u c₄ normLhat21 normA11 normE21) ∧
        (∀ i : Fin m,
          (U i i + DeltaDiag i) *
              dhsBlockBackConventionalSolution fp U
                (dhsBlockForwardConventionalSolution fp Lhat b) i =
            dhsBlockBackConventionalRHS fp i U
              (dhsBlockBackConventionalSolution fp U
                (dhsBlockForwardConventionalSolution fp Lhat b))
              (dhsBlockForwardConventionalSolution fp Lhat b) ∧
          DiagonalBlockSolveFirstOrderBound fp.u (2 * (r : ℝ))
            (maxEntryNorm hr (U i i))
            (maxEntryNorm hr (DeltaDiag i)))) ∧
      FirstOrderLe fp.u
        (dn * fp.u *
          (maxEntryNorm (Nat.mul_pos hm hr) A +
            maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Lhat) *
            maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin U)))
        (maxEntryNorm (Nat.mul_pos hm hr) DeltaFact) ∧
      FirstOrderLe fp.u
        (dn * fp.u *
          (maxEntryNorm (Nat.mul_pos hm hr) A +
            maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Lhat) *
            maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin U)))
        (maxEntryNorm (Nat.mul_pos hm hr)
          (DeltaFact + DeltaL * blockMatrixFlatFin U +
            blockMatrixFlatFin Lhat * blockMatrixFlatFin DeltaU +
            DeltaL * blockMatrixFlatFin DeltaU)) ∧
      FirstOrderLe fp.u
        (dn * fp.u *
          (maxEntryNorm (Nat.mul_pos hm hr) A +
            maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin Lhat) *
            maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin U)))
        (max (maxEntryNorm (Nat.mul_pos hm hr) DeltaFact)
          (maxEntryNorm (Nat.mul_pos hm hr)
            (DeltaFact + DeltaL * blockMatrixFlatFin U +
              blockMatrixFlatFin Lhat * blockMatrixFlatFin DeltaU +
              DeltaL * blockMatrixFlatFin DeltaU))) := by
  have hFactSpec :=
    hFactComputation.to_spec fp.u_nonneg hc₁ hc₂ hc₃
  exact
    higham13_theorem13_6_implementation1_from_partitioned_factorization_and_conventional_recursive_solve
      fp hm hr (blockErrorDelta q) (blockErrorTheta c₁ c₂ c₃ q)
      dFact dn (maxEntryNorm (Nat.mul_pos hm hr) A)
      A DeltaFact Lhat U b c₄ normLhat21 normA11 normE21
      Lhat21 A21 E21 A11 hSmallProduct
      (maxEntryNorm_nonneg (Nat.mul_pos hm hr) A)
      hδ hθ hdFact hdSolve hFactSpec hStep2 hLdiag hLower
      hUUpper hDiag hUpper

end LeanFpAnalysis.FP
