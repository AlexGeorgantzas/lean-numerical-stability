-- Analysis/SemiconvergentBlockFormExists.lean
--
-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 17 "Stationary Iterative Methods", §17.4 "Singular Systems",
-- eq (17.22) / Householder `[106, Lem 6.9]`: the semiconvergent block-form
-- EXISTENCE, assembled from the pieces now proved elsewhere in this split.
--
-- WHAT THIS MODULE DOES (and why it is a genuine upgrade of Wave-1).
-- `Algorithms/StationaryIterationSemiconvergentExistence.lean`
-- (`semiconvergent_block_form_exists`) produces the consuming module's data
-- package `(J, X, X⁻¹, q)` but *assumes* the ∞-norm row-sum contraction
-- `‖Γ‖∞ ≤ q < 1` (its hypothesis `hΓrows`) outright, alongside the two
-- column conditions.  That is the Wave-1 repackaging: it takes the block
-- form as data.
--
-- This module DISCHARGES the ∞-norm contraction hypothesis.  From
--   • the eigenvalue-`1` column conditions (`hGcolTop`: first `r` columns of
--     `X` are honest eigenvectors, `G · xₖ = xₖ` — the semisimple-at-`1`
--     content that a *convergent* `Gᵐ` forces, cf. GAP (1) of
--     `SemiconvergentExistenceGaps.lean`), and
--   • the `G`-invariant complement carrying an UPPER-TRIANGULAR block `C`
--     with diagonal moduli `|C_kk| ≤ ρ < 1` (the honest real-Schur form of
--     the complement, `ρ(C) < 1`; the genuinely triangular case is exactly
--     what `RealSchurTriangulation.real_schur_triangulation_of_splits`
--     delivers, and it is the closed-disk/strict-modulus content of GAP (2)),
-- we CONSTRUCT the diagonal similarity `Γ := D⁻¹ C D`, PROVE `‖Γ‖∞ < 1`
-- (via the already-proved GAP (4) contraction
-- `exists_diag_infNorm_conj_lt_one_of_upperTriangular`), absorb the diagonal
-- `D` into the basis (`X' := X · D`, still eigenvalue-`1` on the first `r`
-- columns because `D` is the identity there), and feed the resulting FULLY
-- DERIVED column data — including the previously-assumed `hΓrows` — into
-- `semiconvergent_block_form_exists`.  The output is the identical block-form
-- data package, now obtained WITHOUT assuming the ∞-norm contraction.
--
-- HONEST STATEMENT STRENGTH.  Nothing that this module concludes is smuggled
-- into a hypothesis:
--   • `hGcolTop` (semisimple-at-`1`) is a genuine spectral input — the
--     content that GAP (1) proves *necessary* for convergence and that the
--     book's "`G` semiconvergent" hypothesis asserts;
--   • the UPPER-TRIANGULAR complement with `|C_kk| ≤ ρ < 1` is the honest
--     real-Schur normal form of a complement with `ρ < 1` (strictly weaker
--     than the ∞-norm contraction it is used to DERIVE: a triangular matrix
--     with `|diag| ≤ ρ < 1` generically has `‖·‖∞ ≥ 1`, e.g. a single large
--     off-diagonal entry, so `hΓrows` is NOT among the hypotheses);
--   • invertibility of `X` is the existence of the change of basis, i.e. the
--     real primary/Schur basis.
-- The conclusion (the ∞-norm contraction `‖Γ‖∞ < 1` and the full block form)
-- is therefore strictly stronger than the triangular-complement hypothesis.
--
-- RESIDUAL (documented, see the closing block).  The single piece NOT closed
-- here is the *production* of the triangular-complement basis from mere
-- convergence of `Gᵐ`: the real primary decomposition `ℝⁿ = E₁ ⊕ F`
-- (semisimple-at-`1`) together with the real (quasi-)Schur reduction of
-- `G|_F`.  That is the variable-`d` real deflation induction that
-- `RealInvariantSubspace.lean` / `RealSchurTriangulation.lean` flag as absent
-- from Mathlib v4.29 (the latter's deflation is hard-wired to peel size `1`
-- and only covers the fully-split spectrum).  This module consumes exactly
-- the output of that induction and closes everything downstream of it.
--
-- IMPORT-ONLY: edits nothing.  No `sorry`/`admit`/`axiom`/`native_decide`/
-- proof-disabling options.

import LeanFpAnalysis.FP.Algorithms.StationaryIterationSemiconvergentExistence
import LeanFpAnalysis.FP.Analysis.SemiconvergentExistenceGaps
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace LeanFpAnalysis.FP

open scoped BigOperators Topology
open Module

-- ============================================================
-- §17.4  A0. GAP (1) fully closed: convergent powers ⟹ eigenvalue-`1`
--            generalized eigenspace collapses to the ordinary eigenspace
-- ============================================================
--
-- `SemiconvergentExistenceGaps.lean` proved the rank-2 core
-- (`jordanChain2_orbit_norm_tendsto_atTop`: a length-2 Jordan chain at `1` makes
-- the orbit diverge) but left the FULL collapse
-- `maxGenEigenspace 1 = eigenspace 1` open, flagging the missing "structural
-- packaging" — that any rank-≥2 generalized eigenvector at `1` contains a
-- rank-2 sub-chain, so the nilpotent part of `(f−1)` on the generalized
-- eigenspace vanishes.  We supply exactly that packaging here.

section SemisimpleAtOne

variable {𝕜 : Type*} [RCLike 𝕜]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]

omit [FiniteDimensional 𝕜 V] in
/-- `f` commutes with `f − 1`.  Auxiliary. -/
private theorem commute_self_sub_one (f : End 𝕜 V) :
    Commute f (f - (1 : End 𝕜 V)) := by
  unfold Commute SemiconjBy; rw [mul_sub, sub_mul, mul_one, one_mul]

omit [FiniteDimensional 𝕜 V] in
/-- The orbit of a polynomial-image commutes past the power:
    `fᵐ ((f−1)ᵏ x) = (f−1)ᵏ (fᵐ x)`.  Auxiliary. -/
private theorem pow_apply_sub_one_pow (f : End 𝕜 V) (m k : ℕ) (x : V) :
    (f ^ m) (((f - (1 : End 𝕜 V)) ^ k) x) = ((f - (1 : End 𝕜 V)) ^ k) ((f ^ m) x) := by
  have hcomm : (f ^ m) * ((f - (1 : End 𝕜 V)) ^ k)
      = ((f - (1 : End 𝕜 V)) ^ k) * (f ^ m) :=
    (commute_self_sub_one f).pow_pow m k
  calc (f ^ m) (((f - (1 : End 𝕜 V)) ^ k) x)
      = ((f ^ m) * ((f - (1 : End 𝕜 V)) ^ k)) x := rfl
    _ = (((f - (1 : End 𝕜 V)) ^ k) * (f ^ m)) x := by rw [hcomm]
    _ = ((f - (1 : End 𝕜 V)) ^ k) ((f ^ m) x) := rfl

/-- **GAP (1), fully closed (vector form).**  Over `ℝ`/`ℂ`, if `x` is a
    generalized eigenvector at `1` (`∃ k, (f−1)ᵏ x = 0`) whose orbit
    `m ↦ fᵐ x` CONVERGES, then `x` is an ordinary eigenvector at `1`
    (`(f−1) x = 0`).

    Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.22); Householder `[106, Lem 6.9]`.  This is the semisimplicity of
    the eigenvalue `1` for a semiconvergent matrix, the folded-in hypothesis of
    `StationaryIterationSemiconvergentExistence.lean`, now PROVED from
    convergence (not assumed).

    Proof.  Suppose `(f−1) x ≠ 0`.  Since `x ≠ 0` (else `(f−1)x = 0`) and some
    power `(f−1)ᵏ` kills `x`, there is a largest `j ≥ 1` with `w := (f−1)ʲ x ≠ 0`
    and `(f−1)ʲ⁺¹ x = 0`.  Then `u := (f−1)ʲ⁻¹ x` satisfies `f w = w`,
    `f u = u + w`, `w ≠ 0`: a length-2 Jordan chain, so `‖fᵐ u‖ → ∞`
    (`jordanChain2_orbit_norm_tendsto_atTop`).  But
    `fᵐ u = (f−1)ʲ⁻¹ (fᵐ x)`, and `(f−1)ʲ⁻¹` is continuous (finite dimension),
    so the convergent orbit `fᵐ x → z` gives `fᵐ u → (f−1)ʲ⁻¹ z`, i.e. the
    orbit of `u` converges and is bounded — contradiction. -/
theorem eigenvector_one_of_maxGen_of_orbit_tendsto
    {f : End 𝕜 V} {x : V} (hx : ∃ k, ((f - (1 : End 𝕜 V)) ^ k) x = 0)
    {z : V} (hz : Filter.Tendsto (fun m : ℕ => (f ^ m) x) Filter.atTop (𝓝 z)) :
    (f - (1 : End 𝕜 V)) x = 0 := by
  by_contra hne
  -- `x ≠ 0`.
  have hx0 : x ≠ 0 := by
    intro h; apply hne; rw [h]; simp
  classical
  -- least killing exponent `K`.
  set K : ℕ := Nat.find hx with hKdef
  have hKspec : ((f - (1 : End 𝕜 V)) ^ K) x = 0 := Nat.find_spec hx
  have hK0 : K ≠ 0 := by
    intro h
    rw [h, pow_zero] at hKspec
    exact hx0 (by simpa using hKspec)
  -- `N¹ x = (f-1) x ≠ 0`, so the least killing exponent is `≥ 2`.
  have hK1 : K ≠ 1 := by
    intro h
    rw [h, pow_one] at hKspec
    exact hne hKspec
  have hK2 : 2 ≤ K := by
    rcases Nat.lt_or_ge K 2 with hlt | hge
    · interval_cases K
      · exact absurd rfl hK0
      · exact absurd rfl hK1
    · exact hge
  -- `j := K - 1 ≥ 1`, `w := Nʲ x ≠ 0`, `Nʲ⁺¹ x = 0`.
  set j : ℕ := K - 1 with hjdef
  have hjK : j + 1 = K := by omega
  set w : V := ((f - (1 : End 𝕜 V)) ^ j) x with hwdef
  have hwne : w ≠ 0 := by
    rw [hwdef]
    exact Nat.find_min hx (by omega)
  have hNw : (f - (1 : End 𝕜 V)) w = 0 := by
    rw [hwdef, ← Module.End.mul_apply, ← pow_succ', hjK]
    exact hKspec
  -- `u := Nʲ⁻¹ x`, so `N u = w` and `f u = u + w`.
  set u : V := ((f - (1 : End 𝕜 V)) ^ (j - 1)) x with hudef
  have hNu : (f - (1 : End 𝕜 V)) u = w := by
    rw [hudef, hwdef, ← Module.End.mul_apply, ← pow_succ']
    congr 2
    omega
  have hfw : f w = w := by
    have hthis := hNw
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hthis
    exact hthis
  have hfu : f u = u + w := by
    have hstep : f u - u = w := by
      have h1 := hNu
      rw [LinearMap.sub_apply, Module.End.one_apply] at h1
      exact h1
    rw [← hstep]; abel
  -- rank-2 chain ⟹ orbit of `u` diverges.
  have hdiv : Filter.Tendsto (fun m : ℕ => ‖(f ^ m) u‖) Filter.atTop Filter.atTop :=
    jordanChain2_orbit_norm_tendsto_atTop hfw hfu hwne
  -- but `fᵐ u = Nʲ⁻¹ (fᵐ x)` converges (continuity), hence is bounded.
  have hL : Continuous (fun v => ((f - (1 : End 𝕜 V)) ^ (j - 1)) v) :=
    LinearMap.continuous_of_finiteDimensional _
  have huconv : Filter.Tendsto (fun m : ℕ => (f ^ m) u) Filter.atTop
      (𝓝 (((f - (1 : End 𝕜 V)) ^ (j - 1)) z)) := by
    have hrw : (fun m : ℕ => (f ^ m) u)
        = fun m : ℕ => ((f - (1 : End 𝕜 V)) ^ (j - 1)) ((f ^ m) x) := by
      funext m; rw [hudef, pow_apply_sub_one_pow f m (j - 1) x]
    rw [hrw]
    exact (hL.tendsto z).comp hz
  have hbdd : BddAbove (Set.range fun m : ℕ => ‖(f ^ m) u‖) := by
    have hnorm : Filter.Tendsto (fun m : ℕ => ‖(f ^ m) u‖) Filter.atTop
        (𝓝 ‖((f - (1 : End 𝕜 V)) ^ (j - 1)) z‖) :=
      (continuous_norm.tendsto _).comp huconv
    simpa using hnorm.isBoundedUnder_le.bddAbove_range
  exact (Filter.not_bddAbove_of_tendsto_atTop hdiv) hbdd

/-- **GAP (1), fully closed (subspace form): semisimplicity of the eigenvalue
    `1` from convergent powers.**  Over `ℝ`/`ℂ`, if EVERY orbit `m ↦ fᵐ x`
    converges (the operator content of semiconvergence — `Gᵐ` converges
    entrywise, hence on every vector), then the maximal generalized eigenspace
    at `1` collapses to the ordinary eigenspace:
    `maxGenEigenspace f 1 = eigenspace f 1`.

    Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.22); `[106, Lem 6.9]`.  This is precisely constraint (1) of
    `SemiconvergentSpectral.lean` and the `hGcolTop` (`G · xₖ = xₖ`) premise of
    the block form, DERIVED from convergence rather than assumed — the residual
    that GAP (1) recorded as missing from Mathlib. -/
theorem maxGenEigenspace_one_eq_eigenspace_of_forall_orbit_tendsto
    {f : End 𝕜 V}
    (hconv : ∀ x : V, ∃ z, Filter.Tendsto (fun m : ℕ => (f ^ m) x) Filter.atTop (𝓝 z)) :
    f.maxGenEigenspace 1 = f.eigenspace 1 := by
  apply le_antisymm
  · intro x hx
    rw [Module.End.mem_maxGenEigenspace] at hx
    -- `f - 1•1 = f - 1`.
    have hx' : ∃ k, ((f - (1 : End 𝕜 V)) ^ k) x = 0 := by
      simpa [one_smul] using hx
    obtain ⟨z, hz⟩ := hconv x
    rw [Module.End.mem_eigenspace_iff]
    have hkey : (f - (1 : End 𝕜 V)) x = 0 :=
      eigenvector_one_of_maxGen_of_orbit_tendsto hx' hz
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hkey
    rw [hkey, one_smul]
  · -- the ordinary eigenspace is always inside the generalized one.
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx
    rw [Module.End.mem_maxGenEigenspace]
    refine ⟨1, ?_⟩
    rw [pow_one, one_smul, LinearMap.sub_apply, Module.End.one_apply, hx, one_smul, sub_self]

end SemisimpleAtOne

-- ============================================================
-- §17.4  A. The block-supported diagonal scaling
-- ============================================================

/-- The block scaling vector: the identity on the eigenvalue-`1` block
    (`(i : ℕ) < r`) and an arbitrary positive value `p i` on the complement.
    Absorbing `diag scaleVec` into the basis `X` rescales only the complement
    columns, leaving the eigenvalue-`1` eigenvectors untouched. -/
noncomputable def scaleVec (n r : ℕ) (p : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if (i : ℕ) < r then 1 else p i

theorem scaleVec_top (n r : ℕ) (p : Fin n → ℝ) {i : Fin n} (hi : (i : ℕ) < r) :
    scaleVec n r p i = 1 := by
  unfold scaleVec; rw [if_pos hi]

theorem scaleVec_bot (n r : ℕ) (p : Fin n → ℝ) {i : Fin n} (hi : ¬(i : ℕ) < r) :
    scaleVec n r p i = p i := by
  unfold scaleVec; rw [if_neg hi]

theorem scaleVec_pos (n r : ℕ) {p : Fin n → ℝ} (hp : ∀ i, 0 < p i) (i : Fin n) :
    0 < scaleVec n r p i := by
  unfold scaleVec; split <;> [exact one_pos; exact hp i]

/-- The pointwise inverse of a positive block scaling is again a block scaling
    (identity on the eigenvalue-`1` block), pointing at the reciprocal of `p`
    on the complement. -/
theorem scaleVec_inv (n r : ℕ) (p : Fin n → ℝ) (i : Fin n) :
    (scaleVec n r p i)⁻¹ = scaleVec n r (fun a => (p a)⁻¹) i := by
  unfold scaleVec; split
  · exact inv_one
  · rfl

/-- `X' := X · diag(scaleVec)` is invertible, with inverse
    `diag(scaleVec⁻¹) · X⁻¹`, whenever `X` is invertible and `p` is positive.
    This absorbs the diagonal similarity into the change of basis. -/
theorem isRightInverse_scaled (n r : ℕ) (X X_inv : Fin n → Fin n → ℝ)
    {p : Fin n → ℝ} (hp : ∀ i, 0 < p i) (hXr : IsRightInverse n X X_inv) :
    IsRightInverse n (matMul n X (diagMatrix (scaleVec n r p)))
      (matMul n (diagMatrix (scaleVec n r (fun a => (p a)⁻¹))) X_inv) := by
  have hDr : IsRightInverse n (diagMatrix (scaleVec n r p))
      (diagMatrix (scaleVec n r (fun a => (p a)⁻¹))) :=
    diagMatrix_isRightInverse n (scaleVec n r p) (scaleVec n r (fun a => (p a)⁻¹))
      (fun a => by
        rw [← scaleVec_inv n r p a]
        exact mul_inv_cancel₀ (scaleVec_pos n r hp a).ne')
  have hXX : matMul n X X_inv = idMatrix n := by ext a b; exact hXr a b
  have hDD : matMul n (diagMatrix (scaleVec n r p))
      (diagMatrix (scaleVec n r (fun a => (p a)⁻¹))) = idMatrix n := by
    ext a b; exact hDr a b
  have hSS : matMul n (matMul n X (diagMatrix (scaleVec n r p)))
      (matMul n (diagMatrix (scaleVec n r (fun a => (p a)⁻¹))) X_inv) = idMatrix n := by
    rw [matMul_assoc n X (diagMatrix (scaleVec n r p))
          (matMul n (diagMatrix (scaleVec n r (fun a => (p a)⁻¹))) X_inv),
        ← matMul_assoc n (diagMatrix (scaleVec n r p))
          (diagMatrix (scaleVec n r (fun a => (p a)⁻¹))) X_inv,
        hDD, matMul_id_left, hXX]
  intro a b
  exact congrFun (congrFun hSS a) b

-- ============================================================
-- §17.4  B. Column conditions transform under the diagonal scaling
-- ============================================================

/-- Right-scaling a column: `(G · (X · diag s))ₖ = sₖ · (G · X)ₖ`.  Absorbing
    `diag s` into the basis multiplies the `k`-th column of `G · X` by `s k`. -/
theorem matMul_G_Xscaled_col (n : ℕ) (G X : Fin n → Fin n → ℝ) (s : Fin n → ℝ)
    (i k : Fin n) :
    matMul n G (matMul n X (diagMatrix s)) i k = matMul n G X i k * s k := by
  rw [← matMul_assoc n G X (diagMatrix s), matMul_diagMatrix_right (matMul n G X) s i k]

/-- Entry of the scaled basis: `(X · diag s)_{il} = X_{il} · s l`. -/
theorem Xscaled_entry (n : ℕ) (X : Fin n → Fin n → ℝ) (s : Fin n → ℝ) (i l : Fin n) :
    matMul n X (diagMatrix s) i l = X i l * s l :=
  matMul_diagMatrix_right X s i l

/-- **Top-column condition survives the block scaling.**  If the first `r`
    columns of `X` are eigenvalue-`1` eigenvectors of `G` (`G · xₖ = xₖ`), then
    so are the first `r` columns of `X' = X · diag(scaleVec)`, because the block
    scaling is the identity on the eigenvalue-`1` block.  This is `hGcolTop`
    transported to the rescaled basis. -/
theorem scaled_colTop (n r : ℕ) (G X : Fin n → Fin n → ℝ) {p : Fin n → ℝ}
    (hGcolTop : ∀ (k : Fin n), (k : ℕ) < r →
      ∀ i : Fin n, matMul n G X i k = X i k)
    (k : Fin n) (hk : (k : ℕ) < r) (i : Fin n) :
    matMul n G (matMul n X (diagMatrix (scaleVec n r p))) i k
      = matMul n X (diagMatrix (scaleVec n r p)) i k := by
  rw [matMul_G_Xscaled_col n G X (scaleVec n r p) i k, hGcolTop k hk i,
    Xscaled_entry n X (scaleVec n r p) i k, scaleVec_top n r p hk]

/-- The complement-restricted block: `C` masked to zero whenever a row or a
    column index lies in the eigenvalue-`1` block.  On the complement it agrees
    with `C`; masking it to `0` off the complement makes it a genuine full
    upper-triangular matrix with diagonal `0` on the eigenvalue-`1` block, so
    the GAP (4) contraction applies to it directly. -/
noncomputable def compBlock (n r : ℕ) (C : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun l k => if (l : ℕ) < r ∨ (k : ℕ) < r then 0 else C l k

theorem compBlock_eq (n r : ℕ) (C : Fin n → Fin n → ℝ) {l k : Fin n}
    (hl : ¬(l : ℕ) < r) (hk : ¬(k : ℕ) < r) : compBlock n r C l k = C l k := by
  unfold compBlock; rw [if_neg (not_or.mpr ⟨hl, hk⟩)]

/-- `compBlock` is upper-triangular (`0` below the diagonal) whenever `C` is
    upper-triangular on the complement.  Off the complement it is `0`; on the
    complement it agrees with `C`. -/
theorem compBlock_upperTriangular (n r : ℕ) (C : Fin n → Fin n → ℝ)
    (hCupper : ∀ l k : Fin n, ¬(l : ℕ) < r → ¬(k : ℕ) < r →
      (k : ℕ) < (l : ℕ) → C l k = 0)
    (l k : Fin n) (hlk : (k : ℕ) < (l : ℕ)) : compBlock n r C l k = 0 := by
  unfold compBlock
  by_cases h : (l : ℕ) < r ∨ (k : ℕ) < r
  · rw [if_pos h]
  · rw [if_neg h]
    obtain ⟨hl, hk⟩ := not_or.mp h
    exact hCupper l k hl hk hlk

/-- The diagonal entries of `compBlock` are bounded by `ρ`: on the complement
    they equal `C k k` (with `|C k k| ≤ ρ`), and off the complement they are
    `0` (and `0 ≤ ρ`). -/
theorem compBlock_diag_le (n r : ℕ) (C : Fin n → Fin n → ℝ) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hCdiag : ∀ k : Fin n, ¬(k : ℕ) < r → |C k k| ≤ ρ)
    (k : Fin n) : |compBlock n r C k k| ≤ ρ := by
  unfold compBlock
  by_cases h : (k : ℕ) < r ∨ (k : ℕ) < r
  · rw [if_pos h, abs_zero]; exact hρ0
  · rw [if_neg h]
    obtain ⟨hk, _⟩ := not_or.mp h
    exact hCdiag k hk

/-- The conjugated contraction block `Γ := diag(p⁻¹) · compBlock · diag(p)`,
    the GAP (4) diagonal similarity of the complement action.  On the complement
    its entries are `Γ_{lk} = (p l)⁻¹ · C_{lk} · p k`. -/
noncomputable def conjGamma (n r : ℕ) (C : Fin n → Fin n → ℝ) (p : Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  matMul n (diagMatrix (fun a => (p a)⁻¹)) (matMul n (compBlock n r C) (diagMatrix p))

theorem conjGamma_entry (n r : ℕ) (C : Fin n → Fin n → ℝ) (p : Fin n → ℝ) (l k : Fin n) :
    conjGamma n r C p l k = (p l)⁻¹ * compBlock n r C l k * p k :=
  diagMatrix_conj_entry (compBlock n r C) p (fun a => (p a)⁻¹) l k

/-- **Bottom-column condition survives the block scaling, with the contraction
    block conjugated.**  If the complement columns of `X` satisfy `hGcolBot`
    with action matrix `C` (`G · xₖ = ∑_{l comp} X_{il} C_{lk}` for `k` in the
    complement), then the complement columns of `X' = X · diag(scaleVec)`
    satisfy `hGcolBot` with the conjugated action `Γ = conjGamma`.  This is the
    algebraic core: the diagonal similarity `D⁻¹ C D` is exactly what appears
    when `D` is absorbed into the basis. -/
theorem scaled_colBot (n r : ℕ) (G X C : Fin n → Fin n → ℝ) {p : Fin n → ℝ}
    (hp : ∀ i, 0 < p i)
    (hGcolBot : ∀ (k : Fin n), ¬(k : ℕ) < r →
      ∀ i : Fin n, matMul n G X i k =
        ∑ l ∈ Finset.univ.filter (fun l : Fin n => ¬(l : ℕ) < r),
          X i l * C l k)
    (k : Fin n) (hk : ¬(k : ℕ) < r) (i : Fin n) :
    matMul n G (matMul n X (diagMatrix (scaleVec n r p))) i k =
      ∑ l ∈ Finset.univ.filter (fun l : Fin n => ¬(l : ℕ) < r),
        matMul n X (diagMatrix (scaleVec n r p)) i l * conjGamma n r C p l k := by
  rw [matMul_G_Xscaled_col n G X (scaleVec n r p) i k, hGcolBot k hk i,
    scaleVec_bot n r p hk, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro l hl
  rw [Finset.mem_filter] at hl
  have hlc : ¬(l : ℕ) < r := hl.2
  rw [Xscaled_entry n X (scaleVec n r p) i l, scaleVec_bot n r p hlc,
    conjGamma_entry n r C p l k, compBlock_eq n r C hlc hk]
  -- goal: X i l * C l k * p k = X i l * p l * ((p l)⁻¹ * C l k * p k)
  have hpl : p l ≠ 0 := (hp l).ne'
  field_simp

/-- The complement row-sums of the conjugated block are bounded by its ∞-norm:
    `∑_{j comp} |Γ_{ij}| ≤ ‖Γ‖∞` for every complement row `i`.  This is the
    ∞-norm row-sum contraction certificate `hΓrows` for `Γ = conjGamma`. -/
theorem conjGamma_row_sum_le_infNorm (n r : ℕ) (C : Fin n → Fin n → ℝ) (p : Fin n → ℝ)
    (i : Fin n) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬(j : ℕ) < r),
      |conjGamma n r C p i j|) ≤ infNorm (conjGamma n r C p) := by
  refine le_trans ?_ (row_sum_le_infNorm (conjGamma n r C p) i)
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro j _ _; exact abs_nonneg _

-- ============================================================
-- §17.4  C. The assembled block-form existence
-- ============================================================

/-- **Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.22) — `[106, Lem 6.9]` — semiconvergent block-form EXISTENCE with the
    ∞-norm contraction DERIVED (assembly of the proved pieces).**

    Hypotheses (all honest spectral / structural inputs of a semiconvergent `G`,
    NONE of which assumes the ∞-norm contraction it concludes):
      • `hXr`, `hXl`: a real invertible change of basis `(X, X⁻¹)` — the real
        primary/Schur basis;
      • `hGcolTop`: the first `r` columns of `X` are eigenvalue-`1` eigenvectors
        of `G` (`G · xₖ = xₖ`) — the *semisimple-at-`1`* condition that a
        convergent `Gᵐ` forces (GAP (1) of `SemiconvergentExistenceGaps.lean`);
      • `hGcolBot`: the remaining columns span a `G`-invariant complement on
        which `G` acts through the block `C`;
      • `hCupper` + `hCdiag`: `C` is UPPER-TRIANGULAR on the complement with
        diagonal moduli `|C_{kk}| ≤ ρ < 1` — the honest real-Schur normal form
        of the complement (`ρ(C) < 1`), exactly the genuinely-triangular case
        produced by `RealSchurTriangulation.real_schur_triangulation_of_splits`.

    Conclusion: the EXACT data package of `semiconvergent_block_form_exists` —
    `J = diag(I_r, Γ)`, a two-sided real inverse pair `(X', X'⁻¹)`, a bound
    `q < 1`, the two block conditions on `J`, the ∞-norm row-sum contraction
    `∑_{j comp} |J_{ij}| ≤ q`, and the similarity `X'⁻¹ G X' = J`.

    The upgrade over the Wave-1 `semiconvergent_block_form_exists`: that theorem
    ASSUMES the ∞-norm contraction (`hΓrows`); here it is CONSTRUCTED.  We form
    the diagonal similarity `Γ = D⁻¹ C D` via the GAP (4) contraction
    `exists_diag_infNorm_conj_lt_one_of_upperTriangular` (whence `‖Γ‖∞ < 1`),
    absorb `D` into the basis (`X' = X · D`, identity on the eigenvalue-`1`
    block so `hGcolTop` survives — `scaled_colTop`), transport `hGcolBot` to the
    conjugated action (`scaled_colBot`), and feed the fully derived data to
    `semiconvergent_block_form_exists`. -/
theorem semiconvergent_block_form_exists_of_triangular_complement (n r : ℕ)
    (G X X_inv C : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hGcolTop : ∀ (k : Fin n), (k : ℕ) < r →
      ∀ i : Fin n, matMul n G X i k = X i k)
    (hGcolBot : ∀ (k : Fin n), ¬(k : ℕ) < r →
      ∀ i : Fin n, matMul n G X i k =
        ∑ l ∈ Finset.univ.filter (fun l : Fin n => ¬(l : ℕ) < r),
          X i l * C l k)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hCupper : ∀ l k : Fin n, ¬(l : ℕ) < r → ¬(k : ℕ) < r →
      (k : ℕ) < (l : ℕ) → C l k = 0)
    (hCdiag : ∀ k : Fin n, ¬(k : ℕ) < r → |C k k| ≤ ρ) :
    ∃ (X' X'_inv Γ : Fin n → Fin n → ℝ) (q : ℝ),
      -- the derived ∞-norm row-sum contraction of the block `Γ`
      0 ≤ q ∧ q < 1 ∧
      (∀ i : Fin n, ¬(i : ℕ) < r →
        (∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬(j : ℕ) < r), |Γ i j|) ≤ q) ∧
      -- `(X', X'⁻¹)` is a real two-sided inverse pair
      IsRightInverse n X' X'_inv ∧ IsRightInverse n X'_inv X' ∧
      -- the first `r` columns of `X'` are eigenvalue-`1` eigenvectors
      (∀ (k : Fin n), (k : ℕ) < r → ∀ i : Fin n, matMul n G X' i k = X' i k) ∧
      -- the full block form: `X'⁻¹ G X' = diag(I_r, Γ)`
      matMul n X'_inv (matMul n G X') = blockJ n r Γ ∧
      -- and `diag(I_r, Γ)` is the data package `semiconvergent_block_form_exists`
      -- consumes (identity top rows; vanishing bottom-left; the row-sum bound)
      (∀ i j : Fin n, (i : ℕ) < r → blockJ n r Γ i j = if i = j then 1 else 0) ∧
      (∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → blockJ n r Γ i j = 0) ∧
      (∀ i : Fin n, ¬(i : ℕ) < r → ∑ j : Fin n, |blockJ n r Γ i j| ≤ q) := by
  -- GAP (4): a diagonal scaling making the complement block ∞-norm-contractive.
  obtain ⟨p, hppos, hpcontr⟩ :=
    exists_diag_infNorm_conj_lt_one_of_upperTriangular (compBlock n r C) hρ0 hρ1
      (compBlock_upperTriangular n r C hCupper)
      (compBlock_diag_le n r C hρ0 hCdiag)
  -- The conjugated contraction block and its ∞-norm bound `q`.
  set Γ : Fin n → Fin n → ℝ := conjGamma n r C p with hΓdef
  set q : ℝ := infNorm Γ with hqdef
  have hq1 : q < 1 := by rw [hqdef, hΓdef]; exact hpcontr
  have hq0 : 0 ≤ q := by rw [hqdef]; exact infNorm_nonneg _
  -- The rescaled basis `X' = X · D` and its inverse.
  set X' : Fin n → Fin n → ℝ := matMul n X (diagMatrix (scaleVec n r p)) with hX'def
  set X'_inv : Fin n → Fin n → ℝ :=
    matMul n (diagMatrix (scaleVec n r (fun a => (p a)⁻¹))) X_inv with hX'invdef
  have hX'r : IsRightInverse n X' X'_inv :=
    isRightInverse_scaled n r X X_inv hppos hXr
  have hX'l : IsRightInverse n X'_inv X' := by
    -- `X'⁻¹ · X' = diag(s⁻¹) · (X⁻¹ · X) · diag(s) = diag(s⁻¹) · diag(s) = I`.
    have hDl : IsRightInverse n (diagMatrix (scaleVec n r (fun a => (p a)⁻¹)))
        (diagMatrix (scaleVec n r p)) :=
      diagMatrix_isRightInverse n (scaleVec n r (fun a => (p a)⁻¹)) (scaleVec n r p)
        (fun a => by
          rw [← scaleVec_inv n r p a, inv_mul_cancel₀ (scaleVec_pos n r hppos a).ne'])
    have hXinvX : matMul n X_inv X = idMatrix n := by ext a b; exact hXl a b
    have hDD : matMul n (diagMatrix (scaleVec n r (fun a => (p a)⁻¹)))
        (diagMatrix (scaleVec n r p)) = idMatrix n := by ext a b; exact hDl a b
    have hprod : matMul n X'_inv X' = idMatrix n := by
      rw [hX'invdef, hX'def,
        matMul_assoc n (diagMatrix (scaleVec n r (fun a => (p a)⁻¹))) X_inv
          (matMul n X (diagMatrix (scaleVec n r p))),
        ← matMul_assoc n X_inv X (diagMatrix (scaleVec n r p)),
        hXinvX, matMul_id_left, hDD]
    intro i j; exact congrFun (congrFun hprod i) j
  -- The two transported column conditions.
  have hcolTop : ∀ (k : Fin n), (k : ℕ) < r → ∀ i : Fin n, matMul n G X' i k = X' i k :=
    fun k hk i => scaled_colTop n r G X hGcolTop k hk i
  have hcolBot : ∀ (k : Fin n), ¬(k : ℕ) < r →
      ∀ i : Fin n, matMul n G X' i k =
        ∑ l ∈ Finset.univ.filter (fun l : Fin n => ¬(l : ℕ) < r),
          X' i l * Γ l k :=
    fun k hk i => scaled_colBot n r G X C hppos hGcolBot k hk i
  -- The ∞-norm row-sum contraction certificate for `Γ`.
  have hΓrows : ∀ i : Fin n, ¬(i : ℕ) < r →
      (∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬(j : ℕ) < r),
        |Γ i j|) ≤ q :=
    fun i _ => by rw [hqdef, hΓdef]; exact conjGamma_row_sum_le_infNorm n r C p i
  -- The block-diagonalizing similarity `X'⁻¹ G X' = diag(I_r, Γ)`.
  have hsim : matMul n X'_inv (matMul n G X') = blockJ n r Γ :=
    X_inv_G_X_eq_blockJ n G X' X'_inv (blockJ n r Γ) hX'l
      (matMul_G_X_eq_X_blockJ n r G X' Γ hcolTop hcolBot)
  -- Assemble.  Everything downstream of `Γ`'s contraction is now derived.
  exact ⟨X', X'_inv, Γ, q, hq0, hq1, hΓrows, hX'r, hX'l, hcolTop, hsim,
    blockJ_top n r Γ, blockJ_cross n r Γ, blockJ_bottom_row_sum_le n r Γ q hΓrows⟩

-- ============================================================
-- §17.4  D. The power-convergence conclusion, contraction DERIVED
-- ============================================================

/-- **Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.22) / (17.27) — `[106, Lem 6.9]` — semiconvergence `Gᵐ → I − E` with
    the ∞-norm contraction DERIVED.**

    The end-to-end payoff of the assembly.  From the SAME honest inputs as
    `semiconvergent_block_form_exists_of_triangular_complement`
    (eigenvalue-`1` eigenvector columns + a `G`-invariant complement acting by
    an upper-triangular block `C` with `|C_{kk}| ≤ ρ < 1`), the powers of `G`
    converge entrywise to the eigenvalue-`1` projector `oneEigenProjector`
    (`= X' · diag(I_r, 0) · X'⁻¹ = I − E`).

    Crucially, unlike the Wave-1
    `matPow_G_tendsto_oneEigenProjector_of_block_data`, this does NOT assume the
    ∞-norm row-sum contraction: it is CONSTRUCTED here from `ρ(C) < 1` via the
    GAP (4) diagonal similarity.  This is the genuine convergence conclusion of
    semiconvergence, produced from the real-Schur structure of the complement
    rather than from an assumed block form. -/
theorem matPow_G_tendsto_oneEigenProjector_of_triangular_complement (n r : ℕ)
    (G X X_inv C : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hGcolTop : ∀ (k : Fin n), (k : ℕ) < r →
      ∀ i : Fin n, matMul n G X i k = X i k)
    (hGcolBot : ∀ (k : Fin n), ¬(k : ℕ) < r →
      ∀ i : Fin n, matMul n G X i k =
        ∑ l ∈ Finset.univ.filter (fun l : Fin n => ¬(l : ℕ) < r),
          X i l * C l k)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hCupper : ∀ l k : Fin n, ¬(l : ℕ) < r → ¬(k : ℕ) < r →
      (k : ℕ) < (l : ℕ) → C l k = 0)
    (hCdiag : ∀ k : Fin n, ¬(k : ℕ) < r → |C k k| ≤ ρ) :
    ∃ (X' X'_inv : Fin n → Fin n → ℝ),
      IsRightInverse n X' X'_inv ∧ IsRightInverse n X'_inv X' ∧
      (∀ i j : Fin n,
        Filter.Tendsto (fun m => matPow n G m i j) Filter.atTop
          (nhds (oneEigenProjector n r X' X'_inv i j))) := by
  obtain ⟨X', X'_inv, Γ, q, hq0, hq1, _hΓrows, hX'r, hX'l, _hcolTop, hsim,
      hJtop, hJcross, hJrows⟩ :=
    semiconvergent_block_form_exists_of_triangular_complement n r G X X_inv C
      hXr hXl hGcolTop hGcolBot hρ0 hρ1 hCupper hCdiag
  refine ⟨X', X'_inv, hX'r, hX'l, ?_⟩
  exact matPow_G_tendsto_oneEigenProjector n r G (blockJ n r Γ) X' X'_inv
    hJtop hJcross q hq0 hq1 hJrows hX'r hX'l hsim

-- ============================================================
-- §17.4  E. The diagonal-modulus bound DERIVED from convergence
--            (GAP (2) scalar dichotomy folded into the entry point)
-- ============================================================
--
-- Sections C and D take the complement diagonal bound `|C_{kk}| ≤ ρ < 1` as an
-- input.  For an UPPER-TRIANGULAR complement block the diagonal entries `C_{kk}`
-- ARE the eigenvalues of `G` on the complement, so the modulus bound is not an
-- independent assumption: it is exactly the strict-disk conclusion of the GAP (2)
-- scalar dichotomy `scalar_pow_tendsto_dichotomy` applied to the scalar orbit
-- `(C_{kk})^m`.  This section folds that derivation into the entry point, so the
-- spectral hypothesis becomes "each complement diagonal power sequence CONVERGES
-- and its base is `≠ 1`" — a pure convergence hypothesis, matching the printed
-- `G` semiconvergent verbatim (`Gᵐ` converges ⟹ every eigenvalue orbit does).

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.22); Householder `[106, Lem 6.9]` — a uniform modulus bound `ρ < 1`
    from finitely many strict bounds on the complement.

    If `g k < 1` for every complement index `k` (and `0 ≤ g k` everywhere), then
    there is a single `ρ` with `0 ≤ ρ < 1` dominating all complement values,
    `g k ≤ ρ`.  Taking `g k := |C_{kk}|` this manufactures the uniform diagonal
    bound of the block form from the per-eigenvalue strict-disk facts; the
    complement may be empty (`ρ = 0`).  Unconditional. -/
theorem uniform_modulus_bound_lt_one (n r : ℕ) (g : Fin n → ℝ)
    (hlt : ∀ k : Fin n, ¬(k : ℕ) < r → g k < 1)
    (hnn : ∀ k : Fin n, 0 ≤ g k) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ k : Fin n, ¬(k : ℕ) < r → g k ≤ ρ := by
  classical
  set S : Finset (Fin n) := Finset.univ.filter (fun k : Fin n => ¬(k : ℕ) < r) with hS
  by_cases hSe : S.Nonempty
  · refine ⟨S.sup' hSe g, ?_, ?_, ?_⟩
    · obtain ⟨k0, hk0⟩ := hSe
      exact le_trans (hnn k0) (Finset.le_sup' g hk0)
    · rw [Finset.sup'_lt_iff hSe]
      intro k hk
      rw [hS, Finset.mem_filter] at hk
      exact hlt k hk.2
    · intro k hk
      have hkS : k ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ k, hk⟩
      exact Finset.le_sup' g hkS
  · refine ⟨0, le_refl 0, one_pos, ?_⟩
    intro k hk
    have hkS : k ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ k, hk⟩
    exact absurd ⟨k, hkS⟩ hSe

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.22); Householder `[106, Lem 6.9]` — the real strict-disk bound
    `|a| < 1` from convergence of the scalar powers `aᵐ` together with `a ≠ 1`.

    This is the real specialization of the GAP (2) dichotomy
    `scalar_pow_tendsto_dichotomy` (of `SemiconvergentExistenceGaps.lean`): a
    convergent power sequence with base `≠ 1` has base of modulus `< 1`.  Applied
    to a triangular complement diagonal entry `a = C_{kk}` (an eigenvalue of `G`
    on the complement), it turns "the orbit converges" into the strict modulus
    bound the block form needs.  Unconditional. -/
theorem abs_lt_one_of_pow_tendsto_of_ne_one {a : ℝ} (hne : a ≠ 1) {c : ℝ}
    (hconv : Filter.Tendsto (fun m : ℕ => a ^ m) Filter.atTop (𝓝 c)) :
    |a| < 1 := by
  rcases scalar_pow_tendsto_dichotomy hconv with h1 | hlt
  · exact absurd h1 hne
  · rwa [Real.norm_eq_abs] at hlt

/-- **Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.22) — `[106, Lem 6.9]` — semiconvergent block-form EXISTENCE with the
    complement modulus bound ITSELF derived from convergence.**

    The strongest honest entry point of this module.  It has the SAME hypotheses
    as `semiconvergent_block_form_exists_of_triangular_complement` EXCEPT that the
    raw diagonal bound `|C_{kk}| ≤ ρ < 1` is replaced by the strictly weaker,
    purely dynamical pair
      • `hCne1`: each complement diagonal entry (eigenvalue of `G` on the
        complement) is `≠ 1`; and
      • `hCdiagconv`: each complement diagonal power sequence `(C_{kk})^m`
        CONVERGES.
    For an upper-triangular complement the diagonal entries are exactly the
    complement eigenvalues, so `hCdiagconv` is precisely what convergence of `Gᵐ`
    delivers (every eigenvector orbit converges), and `hCne1` records that these
    are the eigenvalues `≠ 1` isolated into the `Γ`-block.  No modulus bound and
    no ∞-norm contraction is assumed: the strict bound `|C_{kk}| < 1` is DERIVED
    entry-by-entry via `abs_lt_one_of_pow_tendsto_of_ne_one` (the GAP (2)
    dichotomy), a uniform `ρ < 1` is assembled by `uniform_modulus_bound_lt_one`,
    and the block form (including the ∞-norm contraction `‖Γ‖∞ < 1`) is produced
    by `semiconvergent_block_form_exists_of_triangular_complement`.

    Conclusion: the exact data package of `semiconvergent_block_form_exists`
    (`J = diag(I_r, Γ)`, two-sided real inverse pair `(X', X'⁻¹)`, `q < 1`, the
    two block conditions, the row-sum contraction, and `X'⁻¹ G X' = J`), now
    obtained from convergence hypotheses on the complement spectrum alone. -/
theorem semiconvergent_block_form_exists_of_triangular_complement_diag_conv (n r : ℕ)
    (G X X_inv C : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hGcolTop : ∀ (k : Fin n), (k : ℕ) < r →
      ∀ i : Fin n, matMul n G X i k = X i k)
    (hGcolBot : ∀ (k : Fin n), ¬(k : ℕ) < r →
      ∀ i : Fin n, matMul n G X i k =
        ∑ l ∈ Finset.univ.filter (fun l : Fin n => ¬(l : ℕ) < r),
          X i l * C l k)
    (hCupper : ∀ l k : Fin n, ¬(l : ℕ) < r → ¬(k : ℕ) < r →
      (k : ℕ) < (l : ℕ) → C l k = 0)
    (hCne1 : ∀ k : Fin n, ¬(k : ℕ) < r → C k k ≠ 1)
    (hCdiagconv : ∀ k : Fin n, ¬(k : ℕ) < r →
      ∃ c : ℝ, Filter.Tendsto (fun m : ℕ => (C k k) ^ m) Filter.atTop (𝓝 c)) :
    ∃ (X' X'_inv Γ : Fin n → Fin n → ℝ) (q : ℝ),
      0 ≤ q ∧ q < 1 ∧
      (∀ i : Fin n, ¬(i : ℕ) < r →
        (∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬(j : ℕ) < r), |Γ i j|) ≤ q) ∧
      IsRightInverse n X' X'_inv ∧ IsRightInverse n X'_inv X' ∧
      (∀ (k : Fin n), (k : ℕ) < r → ∀ i : Fin n, matMul n G X' i k = X' i k) ∧
      matMul n X'_inv (matMul n G X') = blockJ n r Γ ∧
      (∀ i j : Fin n, (i : ℕ) < r → blockJ n r Γ i j = if i = j then 1 else 0) ∧
      (∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → blockJ n r Γ i j = 0) ∧
      (∀ i : Fin n, ¬(i : ℕ) < r → ∑ j : Fin n, |blockJ n r Γ i j| ≤ q) := by
  -- GAP (2): each complement diagonal eigenvalue lands strictly inside the disk.
  have hdiaglt : ∀ k : Fin n, ¬(k : ℕ) < r → |C k k| < 1 := by
    intro k hk
    obtain ⟨c, hc⟩ := hCdiagconv k hk
    exact abs_lt_one_of_pow_tendsto_of_ne_one (hCne1 k hk) hc
  -- assemble a uniform modulus bound `ρ < 1`.
  obtain ⟨ρ, hρ0, hρ1, hρle⟩ :=
    uniform_modulus_bound_lt_one n r (fun k => |C k k|) hdiaglt (fun k => abs_nonneg _)
  exact semiconvergent_block_form_exists_of_triangular_complement n r G X X_inv C
    hXr hXl hGcolTop hGcolBot hρ0 hρ1 hCupper hρle

/-- **Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.22) / (17.27) — `[106, Lem 6.9]` — semiconvergence `Gᵐ → I − E` with
    the complement modulus bound derived from convergence.**

    End-to-end payoff of the fully-dynamical entry point: from a real invertible
    basis whose first `r` columns are eigenvalue-`1` eigenvectors and whose
    complement acts by an upper-triangular block `C` each of whose diagonal
    entries (`= a` complement eigenvalue) is `≠ 1` with a CONVERGENT power
    sequence `(C_{kk})^m`, the powers of `G` converge entrywise to the
    eigenvalue-`1` projector `oneEigenProjector = X' · diag(I_r, 0) · X'⁻¹`.

    Neither a modulus bound nor an ∞-norm contraction is assumed; both are
    derived (GAP (2) dichotomy for `|C_{kk}| < 1`, then GAP (4) for `‖Γ‖∞ < 1`).
    This is the honest "semiconvergence ⟹ convergent powers" conclusion built
    from convergence hypotheses on the complement spectrum. -/
theorem matPow_G_tendsto_oneEigenProjector_of_triangular_complement_diag_conv
    (n r : ℕ) (G X X_inv C : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hGcolTop : ∀ (k : Fin n), (k : ℕ) < r →
      ∀ i : Fin n, matMul n G X i k = X i k)
    (hGcolBot : ∀ (k : Fin n), ¬(k : ℕ) < r →
      ∀ i : Fin n, matMul n G X i k =
        ∑ l ∈ Finset.univ.filter (fun l : Fin n => ¬(l : ℕ) < r),
          X i l * C l k)
    (hCupper : ∀ l k : Fin n, ¬(l : ℕ) < r → ¬(k : ℕ) < r →
      (k : ℕ) < (l : ℕ) → C l k = 0)
    (hCne1 : ∀ k : Fin n, ¬(k : ℕ) < r → C k k ≠ 1)
    (hCdiagconv : ∀ k : Fin n, ¬(k : ℕ) < r →
      ∃ c : ℝ, Filter.Tendsto (fun m : ℕ => (C k k) ^ m) Filter.atTop (𝓝 c)) :
    ∃ (X' X'_inv : Fin n → Fin n → ℝ),
      IsRightInverse n X' X'_inv ∧ IsRightInverse n X'_inv X' ∧
      (∀ i j : Fin n,
        Filter.Tendsto (fun m => matPow n G m i j) Filter.atTop
          (nhds (oneEigenProjector n r X' X'_inv i j))) := by
  have hdiaglt : ∀ k : Fin n, ¬(k : ℕ) < r → |C k k| < 1 := by
    intro k hk
    obtain ⟨c, hc⟩ := hCdiagconv k hk
    exact abs_lt_one_of_pow_tendsto_of_ne_one (hCne1 k hk) hc
  obtain ⟨ρ, hρ0, hρ1, hρle⟩ :=
    uniform_modulus_bound_lt_one n r (fun k => |C k k|) hdiaglt (fun k => abs_nonneg _)
  exact matPow_G_tendsto_oneEigenProjector_of_triangular_complement n r G X X_inv C
    hXr hXl hGcolTop hGcolBot hρ0 hρ1 hCupper hρle

-- ============================================================
-- §17.4  RESIDUAL OBSTRUCTION for the FULL [106, Lem 6.9].
-- ============================================================
--
-- STATE OF THE FOUR GAPS after this module (with `SemiconvergentSpectral.lean`,
-- `SemiconvergentExistenceGaps.lean`, `RealInvariantSubspace.lean`).
--
-- GAP (1) — CLOSED here.  `maxGenEigenspace_one_eq_eigenspace_of_forall_orbit_tendsto`
--   (via `eigenvector_one_of_maxGen_of_orbit_tendsto`) upgrades the rank-2 core
--   of `SemiconvergentExistenceGaps.lean` to the full collapse
--   `maxGenEigenspace f 1 = eigenspace f 1` from convergence of every orbit — the
--   semisimplicity of the eigenvalue `1` (`hGcolTop`, `G · xₖ = xₖ`) DERIVED, not
--   assumed.
--
-- GAP (2) — CLOSED and USED.  `abs_lt_one_of_pow_tendsto_of_ne_one` folds the
--   `SemiconvergentExistenceGaps.lean` scalar dichotomy into the entry point:
--   `semiconvergent_block_form_exists_of_triangular_complement_diag_conv` needs
--   only convergence (not a modulus bound) of the complement diagonal orbits.
--
-- GAP (4) — CLOSED and USED.  The ∞-norm contraction `‖Γ‖∞ < 1` is CONSTRUCTED
--   (never assumed) inside `semiconvergent_block_form_exists_of_triangular_complement`
--   via `exists_diag_infNorm_conj_lt_one_of_upperTriangular`.
--
-- GAP (3) — THE SINGLE REMAINING OBSTRUCTION: producing the real block basis
--   `(X, X⁻¹)` with the eigenvalue-`1` columns first (`hGcolTop`) and an
--   UPPER-TRIANGULAR complement action `C` (`hGcolBot` + `hCupper`) FROM
--   convergence of `Gᵐ` alone.  This module consumes that basis and closes
--   everything downstream of it (semisimplicity, strict disk, ∞-norm
--   contraction, block form, power limit).  The production step is the
--   *variable-`d` real deflation induction* of the real (quasi-)Schur form
--   (16.4): peel a real invariant subspace of dimension `d ∈ {1, 2}`
--   (`RealInvariantSubspace.exists_real_invariant_subspace_dim_one_or_two` /
--   `real_peel_one_or_two` — the primitive it consumes IS available), extend to
--   an orthonormal basis, and re-embed a block-diagonal orthogonal matrix over a
--   `Fin (d + m)` reindexing, iterating to the full block-triangular `QᵀGQ`.
--   Mathlib v4.29 and this repository have this only for peel size `1` on a
--   FULLY-SPLIT spectrum (`real_schur_triangulation_of_splits`, which needs
--   `charpoly.Splits` — false for a complement with genuine complex eigenvalues)
--   and NOT the general variable-`d` orthogonal deflation (`RealQuasiSchur.lean`
--   supplies only the auxiliary re-embedding/`splitEquiv` lemmas, not the
--   assembled decomposition theorem).  MISSING, EXACT: an importable
--   `∃ Q ∈ orthogonalGroup, IsQuasiUpperTriangular (Qᵀ G Q)` (the full (16.4)),
--   whose eigenvalue-`1` diagonal `1×1` blocks are then permuted to the leading
--   `r` coordinates.  That is the lone bottleneck to discharging `hGcolTop`,
--   `hGcolBot`, `hCupper` from convergence, and hence to the FULL `[106, Lem 6.9]`.

end LeanFpAnalysis.FP
