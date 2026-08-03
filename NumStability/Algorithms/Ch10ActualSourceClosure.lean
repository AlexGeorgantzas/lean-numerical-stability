import NumStability.Algorithms.HighamChapter10
import NumStability.Source.Higham.Chapter10.Theorem06.RoundedCholesky.ActualClosure

/-!
# Ch10ActualSourceClosure (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.Ch10ActualSourceClosure`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

open scoped BigOperators

namespace NumStability

/-- **Theorem 10.6, actual source closure.**

For an SPD input, a successful concrete Algorithm 10.2 run and its two
concrete rounded triangular solves produce Higham's displayed scaled forward
error bound with

`ε = n γ_(3n+1) / (1 - γ_(n+1))`

and the literal spectral condition number of `H = D⁻¹ A D⁻¹`.  No
factorization-error, solve-error, inverse-action, or operator-norm certificate
is an input to this theorem. -/
theorem higham10_6_actual_source_closed (fp : FPModel) (n : ℕ)
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) (b x : Fin n → ℝ)
    (hSPD : IsSymPosDef n A)
    (hn1 : gammaValid fp (n + 1))
    (hn3 : gammaValid fp (3 * n + 1))
    (hgamma1 : gamma fp (n + 1) < 1)
    (hsuccess : ∀ j : Fin n, 0 < fl_cholPivot fp n A j)
    (hAx : matMulVec n A x = b)
    (hsmall : higham10SourceKappa2 A *
      ((n : ℝ) * (gamma fp (3 * n + 1) /
        (1 - gamma fp (n + 1)))) < 1) :
    let Rhat := fl_cholesky fp n A
    let yhat := fl_forwardSub fp n (fun i j : Fin n => Rhat j i) b
    let xhat := fl_backSub fp n Rhat yhat
    vecNorm2 (fun i => Real.sqrt (A i i) * xhat i -
        Real.sqrt (A i i) * x i) ≤
      higham10SourceKappa2 A *
          ((n : ℝ) * (gamma fp (3 * n + 1) /
            (1 - gamma fp (n + 1)))) /
        (1 - higham10SourceKappa2 A *
          ((n : ℝ) * (gamma fp (3 * n + 1) /
            (1 - gamma fp (n + 1))))) *
      vecNorm2 (fun i => Real.sqrt (A i i) * x i) := by
  let Rhat := fl_cholesky fp n A
  let yhat := fl_forwardSub fp n (fun i j : Fin n => Rhat j i) b
  let xhat := fl_backSub fp n Rhat yhat
  have hu : fp.u < 1 := by
    unfold gammaValid at hn1
    push_cast at hn1
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)) fp.u_nonneg]
  have hdiag : ∀ j : Fin n, Rhat j j ≠ 0 := by
    intro j
    dsimp [Rhat]
    rw [fl_cholesky_diag_eq]
    exact (fl_sqrt_pos fp hu _ (by simpa [fl_cholPivot] using hsuccess j)).ne'
  have hchol : CholeskyBackwardError n A Rhat (gamma fp (n + 1)) := by
    exact fl_cholesky_backward_error fp n A hSPD.1 hn1
      (fun j => (hsuccess j).le) hdiag
  have hpkg := cholesky_solve_backward_error_expanded fp n A Rhat b hdiag hchol hn1
  change ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaA i j| ≤
        (gamma fp (n + 1) + 2 * gamma fp n + gamma fp n ^ 2) *
          ∑ k : Fin n, |Rhat k i| * |Rhat k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * xhat j = b i) at hpkg
  obtain ⟨DeltaA, hDelta, hsolve⟩ := hpkg
  have hAhat : ∀ i : Fin n,
      matMulVec n A xhat i + matMulVec n DeltaA xhat i = b i := by
    intro i
    simpa [matMulVec, Finset.sum_add_distrib, add_mul] using hsolve i
  have hInv := higham10SourceScaledMatrix_nonsingInv_action A hSPD
  have hkappa0 : 0 ≤ higham10SourceKappa2 A := by
    exact mul_nonneg (opNorm2_nonneg _) (opNorm2_nonneg _)
  have hkappa := higham10SourceScaledMatrix_inverse_opNorm2Le_kappa2 hn A hSPD
  exact higham10_6_fl_scaled_forward_error_source fp n A Rhat
    (nonsingInv n (higham10SourceScaledMatrix A)) DeltaA x xhat b
    (fun i => higham10_spd_diag_pos A hSPD i) hgamma1 hn3 hchol hDelta
    hInv (higham10SourceKappa2 A) hkappa0 hkappa hAx hAhat hsmall

end NumStability
