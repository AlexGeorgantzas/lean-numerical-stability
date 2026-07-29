import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.Equality.Basic
import NumStability.Algorithms.QR.GramSchmidtPolar
import NumStability.Algorithms.QR.Higham19
import NumStability.Algorithms.QR.Higham19Thm6ColPivot
import NumStability.Algorithms.QR.Higham19Thm6CoxHigham
import NumStability.Algorithms.QR.Higham19Thm6CoxHighamConcrete
import NumStability.Algorithms.QR.Higham19Thm6ElementwisePackaged
import NumStability.Algorithms.QR.Higham19Thm6RowSpecific
import NumStability.Algorithms.Underdetermined.UnderdeterminedSpec

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-!
# KKT systems for equality-constrained least squares

Reusable Karush--Kuhn--Tucker identities for equality-constrained least squares.

Declarations are extracted command-for-command from the historical least-squares owners; only contracted cross-module private helpers are promoted.
-/

/-- Source augmented KKT system for the equality-constrained least-squares
    operator in Higham, 2nd ed., Chapter 20, equations (20.23)-(20.25).

    The unknowns are a residual-like vector `dr`, a solution difference `dx`,
    and a multiplier difference `dlambda`; the right-hand sides are the data,
    stationarity, and constraint rows of the source augmented system. -/
def LSEKKTSystem {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (f : Fin m → ℝ) (g : Fin n → ℝ) (c : Fin p → ℝ)
    (dr : Fin m → ℝ) (dx : Fin n → ℝ) (dlambda : Fin p → ℝ) : Prop :=
  (∀ i : Fin m, dr i + rectMatMulVec A dx i = f i) ∧
  (∀ j : Fin n,
    (∑ i : Fin m, A i j * dr i) -
      (∑ r : Fin p, B r j * dlambda r) = g j) ∧
  (∀ r : Fin p, rectMatMulVec B dx r = c r)

/-- The square linear operator behind `LSEKKTSystem`.

    It maps `(dr, dx, dlambda)` to the three source augmented KKT rows:
    `dr + A*dx`, `A^T*dr - B^T*dlambda`, and `B*dx`. -/
noncomputable def LSEKKTLinearMap {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ) :
    ((Fin m → ℝ) × (Fin n → ℝ) × (Fin p → ℝ)) →ₗ[ℝ]
      ((Fin m → ℝ) × (Fin n → ℝ) × (Fin p → ℝ)) where
  toFun z :=
    (fun i : Fin m => z.1 i + rectMatMulVec A z.2.1 i,
      fun j : Fin n =>
        (∑ i : Fin m, A i j * z.1 i) -
          (∑ r : Fin p, B r j * z.2.2 r),
      fun r : Fin p => rectMatMulVec B z.2.1 r)
  map_add' := by
    intro u v
    apply Prod.ext
    · ext i
      dsimp
      have hmul :
          rectMatMulVec A (u.2.1 + v.2.1) i =
            rectMatMulVec A u.2.1 i + rectMatMulVec A v.2.1 i := by
        simpa using congrFun (rectMatMulVec_add A u.2.1 v.2.1) i
      rw [hmul]
      ring
    · apply Prod.ext
      · ext j
        dsimp
        have hAadd :
            (∑ i : Fin m, A i j * (u.1 i + v.1 i)) =
              (∑ i : Fin m, A i j * u.1 i) +
                (∑ i : Fin m, A i j * v.1 i) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
        have hBadd :
            (∑ r : Fin p, B r j * (u.2.2 r + v.2.2 r)) =
              (∑ r : Fin p, B r j * u.2.2 r) +
                (∑ r : Fin p, B r j * v.2.2 r) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro r _
          ring
        rw [hAadd, hBadd]
        ring
      · ext r
        dsimp
        have hmul :
            rectMatMulVec B (u.2.1 + v.2.1) r =
              rectMatMulVec B u.2.1 r + rectMatMulVec B v.2.1 r := by
          simpa using congrFun (rectMatMulVec_add B u.2.1 v.2.1) r
        exact hmul
  map_smul' := by
    intro a u
    apply Prod.ext
    · ext i
      dsimp
      have hmul :
          rectMatMulVec A (a • u.2.1) i =
            a * rectMatMulVec A u.2.1 i := by
        simpa using congrFun (rectMatMulVec_smul A a u.2.1) i
      rw [hmul]
      ring
    · apply Prod.ext
      · ext j
        dsimp
        have hAsmul :
            (∑ i : Fin m, A i j * (a * u.1 i)) =
              a * (∑ i : Fin m, A i j * u.1 i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        have hBsmul :
            (∑ r : Fin p, B r j * (a * u.2.2 r)) =
              a * (∑ r : Fin p, B r j * u.2.2 r) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          ring
        rw [hAsmul, hBsmul]
        ring
      · ext r
        dsimp
        have hmul :
            rectMatMulVec B (a • u.2.1) r =
              a * rectMatMulVec B u.2.1 r := by
          simpa using congrFun (rectMatMulVec_smul B a u.2.1) r
        exact hmul

/-- Component form of the source KKT linear-map equation. -/
theorem LSEKKTSystem.iff_linearMap_eq {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (f : Fin m → ℝ) (g : Fin n → ℝ) (c : Fin p → ℝ)
    (dr : Fin m → ℝ) (dx : Fin n → ℝ) (dlambda : Fin p → ℝ) :
    LSEKKTSystem A B f g c dr dx dlambda ↔
      LSEKKTLinearMap A B (dr, dx, dlambda) = (f, g, c) := by
  constructor
  · intro hsys
    rcases hsys with ⟨htop, hstat, hconstr⟩
    apply Prod.ext
    · ext i
      exact htop i
    · apply Prod.ext
      · ext j
        exact hstat j
      · ext r
        exact hconstr r
  · intro hmap
    constructor
    · intro i
      exact congrFun (congrArg Prod.fst hmap) i
    · constructor
      · intro j
        exact congrFun (congrArg Prod.fst (congrArg Prod.snd hmap)) j
      · intro r
        exact congrFun (congrArg Prod.snd (congrArg Prod.snd hmap)) r

/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    KKT difference equations for the Cox--Higham augmented-system route.

    Source and perturbed LSE minimizers have Lagrange multipliers whose
    difference satisfies the source augmented-system equations.  The right-hand
    sides are exactly the data, constraint, and stationarity perturbation terms
    that the block inverse in the Cox--Higham proof acts on. -/
theorem IsLSEMinimizer.exists_lagrange_kkt_difference_system_of_fullRowRank
    {m n p : ℕ}
    {A DeltaA : Fin m → Fin n → ℝ} {b Deltab : Fin m → ℝ}
    {B DeltaB : Fin p → Fin n → ℝ} {d Deltad : Fin p → ℝ}
    {x y : Fin n → ℝ}
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hB : LSEFullRowRank B)
    (hBpert : LSEFullRowRank (fun i j => B i j + DeltaB i j)) :
    ∃ lambda mu : Fin p → ℝ,
      (∀ i : Fin m,
        lsResidualHigham (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i) y i -
            lsResidualHigham A b x i +
          rectMatMulVec A (fun j => y j - x j) i =
        Deltab i - rectMatMulVec DeltaA y i) ∧
      (∀ j : Fin n,
        (∑ i : Fin m,
            A i j *
              (lsResidualHigham (fun i j => A i j + DeltaA i j)
                  (fun i => b i + Deltab i) y i -
                lsResidualHigham A b x i)) -
          (∑ r : Fin p, B r j * (mu r - lambda r)) =
        (∑ r : Fin p, DeltaB r j * mu r) -
          (∑ i : Fin m,
            DeltaA i j *
              lsResidualHigham (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i) y i)) ∧
      (∀ r : Fin p,
        rectMatMulVec B (fun j => y j - x j) r =
          Deltad r - rectMatMulVec DeltaB y r) := by
  rcases hx.exists_lagrange_normal_equations_of_fullRowRank hB with
    ⟨lambda, hxfeas, hlambda⟩
  rcases hy.exists_lagrange_normal_equations_of_fullRowRank hBpert with
    ⟨mu, hyfeas, hmu⟩
  refine ⟨lambda, mu, ?_, ?_, ?_⟩
  · intro i
    unfold lsResidualHigham
    rw [congrFun (rectMatMulVec_mat_add A DeltaA y) i]
    rw [congrFun (rectMatMulVec_sub A y x) i]
    ring
  · intro j
    let s : Fin m → ℝ :=
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y
    let rsrc : Fin m → ℝ := lsResidualHigham A b x
    have hmu_expand :
        (∑ i : Fin m, A i j * s i) +
            (∑ i : Fin m, DeltaA i j * s i) =
          (∑ r : Fin p, B r j * mu r) +
            (∑ r : Fin p, DeltaB r j * mu r) := by
      calc
        (∑ i : Fin m, A i j * s i) +
            (∑ i : Fin m, DeltaA i j * s i)
            = ∑ i : Fin m, (A i j + DeltaA i j) * s i := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro i _
                ring
        _ = ∑ r : Fin p, (B r j + DeltaB r j) * mu r := hmu j
        _ = (∑ r : Fin p, B r j * mu r) +
              (∑ r : Fin p, DeltaB r j * mu r) := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro r _
                ring
    have hlambda_j :
        (∑ i : Fin m, A i j * rsrc i) =
          ∑ r : Fin p, B r j * lambda r := hlambda j
    have hsumA :
        (∑ i : Fin m, A i j * (s i - rsrc i)) =
          (∑ i : Fin m, A i j * s i) -
            (∑ i : Fin m, A i j * rsrc i) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hsumB :
        (∑ r : Fin p, B r j * (mu r - lambda r)) =
          (∑ r : Fin p, B r j * mu r) -
            (∑ r : Fin p, B r j * lambda r) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r _
      ring
    change
      (∑ i : Fin m, A i j * (s i - rsrc i)) -
          (∑ r : Fin p, B r j * (mu r - lambda r)) =
        (∑ r : Fin p, DeltaB r j * mu r) -
          (∑ i : Fin m, DeltaA i j * s i)
    rw [hsumA, hsumB]
    linarith
  · intro r
    have hpert_r := hyfeas r
    have hsrc_r := hxfeas r
    rw [congrFun (rectMatMulVec_mat_add B DeltaB y) r] at hpert_r
    rw [congrFun (rectMatMulVec_sub B y x) r]
    linarith

/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    package the Cox--Higham KKT difference equations as one source augmented
    KKT system.  This is the system to which the later block inverse/norm bound
    is applied. -/
theorem IsLSEMinimizer.exists_lagrange_kkt_difference_source_system_of_fullRowRank
    {m n p : ℕ}
    {A DeltaA : Fin m → Fin n → ℝ} {b Deltab : Fin m → ℝ}
    {B DeltaB : Fin p → Fin n → ℝ} {d Deltad : Fin p → ℝ}
    {x y : Fin n → ℝ}
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hB : LSEFullRowRank B)
    (hBpert : LSEFullRowRank (fun i j => B i j + DeltaB i j)) :
    ∃ lambda mu : Fin p → ℝ,
      LSEKKTSystem A B
        (fun i => Deltab i - rectMatMulVec DeltaA y i)
        (fun j =>
          (∑ r : Fin p, DeltaB r j * mu r) -
            (∑ i : Fin m,
              DeltaA i j *
                lsResidualHigham (fun i j => A i j + DeltaA i j)
                  (fun i => b i + Deltab i) y i))
        (fun r => Deltad r - rectMatMulVec DeltaB y r)
        (fun i =>
          lsResidualHigham (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i) y i -
            lsResidualHigham A b x i)
        (fun j => y j - x j)
        (fun r => mu r - lambda r) := by
  rcases hx.exists_lagrange_kkt_difference_system_of_fullRowRank hy hB hBpert with
    ⟨lambda, mu, htop, hstat, hconstr⟩
  exact ⟨lambda, mu, htop, hstat, hconstr⟩

/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the Cox--Higham KKT difference system together with the source normal
    equations for the same source Lagrange multiplier.  This exposes the
    certificate needed to bound the source multiplier from the source residual
    rather than postulating its scale separately. -/
theorem
    IsLSEMinimizer.exists_lagrange_kkt_difference_source_system_of_fullRowRank_sourceNormal
    {m n p : ℕ}
    {A DeltaA : Fin m → Fin n → ℝ} {b Deltab : Fin m → ℝ}
    {B DeltaB : Fin p → Fin n → ℝ} {d Deltad : Fin p → ℝ}
    {x y : Fin n → ℝ}
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hB : LSEFullRowRank B)
    (hBpert : LSEFullRowRank (fun i j => B i j + DeltaB i j)) :
    ∃ lambda mu : Fin p → ℝ,
      (∀ j : Fin n,
        ∑ i : Fin m, A i j * lsResidualHigham A b x i =
          ∑ r : Fin p, B r j * lambda r) ∧
      LSEKKTSystem A B
        (fun i => Deltab i - rectMatMulVec DeltaA y i)
        (fun j =>
          (∑ r : Fin p, DeltaB r j * mu r) -
            (∑ i : Fin m,
              DeltaA i j *
                lsResidualHigham (fun i j => A i j + DeltaA i j)
                  (fun i => b i + Deltab i) y i))
        (fun r => Deltad r - rectMatMulVec DeltaB y r)
        (fun i =>
          lsResidualHigham (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i) y i -
            lsResidualHigham A b x i)
        (fun j => y j - x j)
        (fun r => mu r - lambda r) := by
  rcases hx.exists_lagrange_normal_equations_of_fullRowRank hB with
    ⟨lambda, hxfeas, hlambda⟩
  rcases hy.exists_lagrange_normal_equations_of_fullRowRank hBpert with
    ⟨mu, hyfeas, hmu⟩
  refine ⟨lambda, mu, hlambda, ?_, ?_, ?_⟩
  · intro i
    unfold lsResidualHigham
    dsimp
    rw [congrFun (rectMatMulVec_mat_add A DeltaA y) i]
    rw [congrFun (rectMatMulVec_sub A y x) i]
    ring
  · intro j
    let s : Fin m → ℝ :=
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y
    let rsrc : Fin m → ℝ := lsResidualHigham A b x
    have hmu_expand :
        (∑ i : Fin m, A i j * s i) +
            (∑ i : Fin m, DeltaA i j * s i) =
          (∑ r : Fin p, B r j * mu r) +
            (∑ r : Fin p, DeltaB r j * mu r) := by
      calc
        (∑ i : Fin m, A i j * s i) +
            (∑ i : Fin m, DeltaA i j * s i)
            = ∑ i : Fin m, (A i j + DeltaA i j) * s i := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro i _
                ring
        _ = ∑ r : Fin p, (B r j + DeltaB r j) * mu r := hmu j
        _ = (∑ r : Fin p, B r j * mu r) +
              (∑ r : Fin p, DeltaB r j * mu r) := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro r _
                ring
    have hlambda_j :
        (∑ i : Fin m, A i j * rsrc i) =
          ∑ r : Fin p, B r j * lambda r := hlambda j
    have hsumA :
        (∑ i : Fin m, A i j * (s i - rsrc i)) =
          (∑ i : Fin m, A i j * s i) -
            (∑ i : Fin m, A i j * rsrc i) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hsumB :
        (∑ r : Fin p, B r j * (mu r - lambda r)) =
          (∑ r : Fin p, B r j * mu r) -
            (∑ r : Fin p, B r j * lambda r) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r _
      ring
    change
      (∑ i : Fin m, A i j * (s i - rsrc i)) -
          (∑ r : Fin p, B r j * (mu r - lambda r)) =
        (∑ r : Fin p, DeltaB r j * mu r) -
          (∑ i : Fin m, DeltaA i j * s i)
    rw [hsumA, hsumB]
    linarith
  · intro r
    have hpert_r := hyfeas r
    have hsrc_r := hxfeas r
    rw [congrFun (rectMatMulVec_mat_add B DeltaB y) r] at hpert_r
    rw [congrFun (rectMatMulVec_sub B y x) r]
    linarith

/-- Homogeneous uniqueness for the source equality-constrained KKT augmented
    system under Higham's conditions (20.24).

    This is the nonsingularity kernel for the Cox--Higham block-inverse route:
    with zero data, stationarity, and constraint right-hand sides, the residual,
    solution, and multiplier components are all zero. -/
theorem LSEKKTSystem.eq_zero_of_homogeneous {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {B : Fin p → Fin n → ℝ}
    (hB : LSEFullRowRank B) (hnull : LSENullIntersectionTrivial A B)
    {dr : Fin m → ℝ} {dx : Fin n → ℝ} {dlambda : Fin p → ℝ}
    (hsys : LSEKKTSystem A B (0 : Fin m → ℝ) (0 : Fin n → ℝ)
      (0 : Fin p → ℝ) dr dx dlambda) :
    dr = 0 ∧ dx = 0 ∧ dlambda = 0 := by
  rcases hsys with ⟨htop, hstat, hconstr⟩
  have hA_dot :
      (∑ j : Fin n, dx j * (∑ i : Fin m, A i j * dr i)) =
        ∑ i : Fin m, rectMatMulVec A dx i * dr i := by
    calc
      (∑ j : Fin n, dx j * (∑ i : Fin m, A i j * dr i))
          = ∑ j : Fin n, ∑ i : Fin m, dx j * (A i j * dr i) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.mul_sum]
      _ = ∑ i : Fin m, ∑ j : Fin n, dx j * (A i j * dr i) := by
              rw [Finset.sum_comm]
      _ = ∑ i : Fin m, rectMatMulVec A dx i * dr i := by
              apply Finset.sum_congr rfl
              intro i _
              calc
                (∑ j : Fin n, dx j * (A i j * dr i))
                    = ∑ j : Fin n, (A i j * dx j) * dr i := by
                        apply Finset.sum_congr rfl
                        intro j _
                        ring
                _ = (∑ j : Fin n, A i j * dx j) * dr i := by
                        rw [Finset.sum_mul]
                _ = rectMatMulVec A dx i * dr i := rfl
  have hB_dot :
      (∑ j : Fin n, dx j * (∑ r : Fin p, B r j * dlambda r)) =
        ∑ r : Fin p, rectMatMulVec B dx r * dlambda r := by
    calc
      (∑ j : Fin n, dx j * (∑ r : Fin p, B r j * dlambda r))
          = ∑ j : Fin n, ∑ r : Fin p, dx j * (B r j * dlambda r) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.mul_sum]
      _ = ∑ r : Fin p, ∑ j : Fin n, dx j * (B r j * dlambda r) := by
              rw [Finset.sum_comm]
      _ = ∑ r : Fin p, rectMatMulVec B dx r * dlambda r := by
              apply Finset.sum_congr rfl
              intro r _
              calc
                (∑ j : Fin n, dx j * (B r j * dlambda r))
                    = ∑ j : Fin n, (B r j * dx j) * dlambda r := by
                        apply Finset.sum_congr rfl
                        intro j _
                        ring
                _ = (∑ j : Fin n, B r j * dx j) * dlambda r := by
                        rw [Finset.sum_mul]
                _ = rectMatMulVec B dx r * dlambda r := rfl
  have hstation_sum :
      (∑ j : Fin n,
        dx j *
          ((∑ i : Fin m, A i j * dr i) -
            (∑ r : Fin p, B r j * dlambda r))) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hj : (∑ i : Fin m, A i j * dr i) -
        (∑ r : Fin p, B r j * dlambda r) = 0 := by
      simpa using hstat j
    rw [hj]
    ring
  have hstation_split :
      (∑ j : Fin n,
        dx j *
          ((∑ i : Fin m, A i j * dr i) -
            (∑ r : Fin p, B r j * dlambda r))) =
        (∑ j : Fin n, dx j * (∑ i : Fin m, A i j * dr i)) -
          (∑ j : Fin n, dx j * (∑ r : Fin p, B r j * dlambda r)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hstation_source :
      (∑ i : Fin m, rectMatMulVec A dx i * dr i) -
          (∑ r : Fin p, rectMatMulVec B dx r * dlambda r) = 0 := by
    calc
      (∑ i : Fin m, rectMatMulVec A dx i * dr i) -
          (∑ r : Fin p, rectMatMulVec B dx r * dlambda r)
          = (∑ j : Fin n, dx j * (∑ i : Fin m, A i j * dr i)) -
              (∑ j : Fin n, dx j * (∑ r : Fin p, B r j * dlambda r)) := by
              rw [hA_dot, hB_dot]
      _ = (∑ j : Fin n,
            dx j *
              ((∑ i : Fin m, A i j * dr i) -
                (∑ r : Fin p, B r j * dlambda r))) := by
              rw [hstation_split]
      _ = 0 := hstation_sum
  have hBdot_zero :
      (∑ r : Fin p, rectMatMulVec B dx r * dlambda r) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    have hr : rectMatMulVec B dx r = 0 := by
      simpa using hconstr r
    rw [hr]
    ring
  have hAdot_zero :
      (∑ i : Fin m, rectMatMulVec A dx i * dr i) = 0 := by
    linarith
  have hAdx_neg : ∀ i : Fin m, rectMatMulVec A dx i = -dr i := by
    intro i
    have hi : dr i + rectMatMulVec A dx i = 0 := by
      simpa using htop i
    linarith
  have hAdot_eq_neg_sq :
      (∑ i : Fin m, rectMatMulVec A dx i * dr i) = -vecNorm2Sq dr := by
    unfold vecNorm2Sq
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hAdx_neg i]
    ring
  have hdrsq : vecNorm2Sq dr = 0 := by
    linarith
  have hdrnorm : vecNorm2 dr = 0 := by
    unfold vecNorm2
    rw [Real.sqrt_eq_zero (vecNorm2Sq_nonneg dr)]
    exact hdrsq
  have hdr_zero : dr = 0 := by
    ext i
    exact (vecNorm2_eq_zero_iff dr).mp hdrnorm i
  have hAdx_zero : rectMatMulVec A dx = 0 := by
    ext i
    change rectMatMulVec A dx i = 0
    have hi : dr i + rectMatMulVec A dx i = 0 := by
      simpa using htop i
    have hdri : dr i = 0 := by
      simpa using congrFun hdr_zero i
    linarith
  have hBdx_zero : rectMatMulVec B dx = 0 := by
    ext r
    change rectMatMulVec B dx r = 0
    simpa using hconstr r
  have hdx_zero : dx = 0 := hnull dx hAdx_zero hBdx_zero
  have hBt_zero :
      rectMatMulVec (fun j : Fin n => fun r : Fin p => B r j) dlambda = 0 := by
    ext j
    change (∑ r : Fin p, B r j * dlambda r) = 0
    have hj : (∑ i : Fin m, A i j * dr i) -
        (∑ r : Fin p, B r j * dlambda r) = 0 := by
      simpa using hstat j
    have hArow_zero : (∑ i : Fin m, A i j * dr i) = 0 := by
      rw [hdr_zero]
      simp
    linarith
  have hdlambda_zero : dlambda = 0 := by
    apply hB.transpose_rectMatMulVec_injective
    rw [hBt_zero, rectMatMulVec_zero]
  exact ⟨hdr_zero, hdx_zero, hdlambda_zero⟩

/-- A source LSE Lagrange multiplier satisfying the normal equations solves the
    source KKT system with right-hand side `(r,0,0)`, where
    `r = b - A*x` is Higham's signed residual. -/
theorem LSEKKTSystem.sourceResidual_of_lagrange_normal_equations {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {B : Fin p → Fin n → ℝ} {x : Fin n → ℝ}
    {lambda : Fin p → ℝ}
    (hnormal : ∀ j : Fin n,
      ∑ i : Fin m, A i j * lsResidualHigham A b x i =
        ∑ r : Fin p, B r j * lambda r) :
    LSEKKTSystem A B (lsResidualHigham A b x) 0 0
      (lsResidualHigham A b x) 0 lambda := by
  constructor
  · intro i
    rw [congrFun (rectMatMulVec_zero A) i]
    simp
  · constructor
    · intro j
      rw [hnormal j]
      simp
    · intro r
      rw [congrFun (rectMatMulVec_zero B) r]

namespace Theorem20_10

theorem orthogonal_matMulVec_injective {n : ℕ}
    {U : Fin n → Fin n → ℝ} (hU : IsOrthogonal n U) :
    Function.Injective (matMulVec n U) := by
  intro x y hxy
  ext i
  calc
    x i = matMulVec n (idMatrix n) x i :=
      (congrFun (matMulVec_id n x) i).symm
    _ = matMulVec n (matMul n (matTranspose U) U) x i := by
          congr 2
          ext a b
          exact (hU.left_inv a b).symm
    _ = matMulVec n (matTranspose U) (matMulVec n U x) i :=
          matMulVec_matMul n (matTranspose U) U x i
    _ = matMulVec n (matTranspose U) (matMulVec n U y) i := by
          rw [hxy]
    _ = matMulVec n (matMul n (matTranspose U) U) y i :=
          (matMulVec_matMul n (matTranspose U) U y i).symm
    _ = matMulVec n (idMatrix n) y i := by
          congr 2
          ext a b
          exact hU.left_inv a b
    _ = y i := congrFun (matMulVec_id n y) i

end Theorem20_10

end NumStability
