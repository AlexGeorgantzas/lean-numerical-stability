import LeanFpAnalysis.FP.Algorithms.QR.GivensQR
import LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt
import LeanFpAnalysis.FP.Algorithms.QR.GramSchmidtPolar
import LeanFpAnalysis.FP.Algorithms.QR.HouseholderQR
import LeanFpAnalysis.FP.Algorithms.QR.HouseholderQRSupport
import LeanFpAnalysis.FP.Algorithms.QR.HouseholderSpecSupport

open LeanFpAnalysis.FP

namespace H19

noncomputable section

namespace Problem19_1

/-- Problem 19.1 Householder eigendirection: with the usual normalization
`beta * (v^T v) = 2`, the Householder reflector sends its defining vector to
`-v`.  This records the `-1` eigendirection in the repository's matrix-vector
API. -/
theorem householder_mul_defining_vector_neg {n : Nat}
    (v : Fin n -> Real) (beta : Real)
    (hbeta :
      beta * ((Finset.univ : Finset (Fin n)).sum (fun k => v k * v k)) =
        2) :
    matMulVec n (householder n v beta) v = (fun i => -v i) := by
  ext i
  unfold matMulVec householder idMatrix
  have hterm : forall j : Fin n,
      ((if i = j then 1 else 0) - beta * v i * v j) * v j =
        (if i = j then 1 else 0) * v j -
          (beta * v i) * (v j * v j) := by
    intro j
    ring
  calc
    ((Finset.univ : Finset (Fin n)).sum
        (fun j => ((if i = j then 1 else 0) - beta * v i * v j) * v j))
        =
          ((Finset.univ : Finset (Fin n)).sum
            (fun j => (if i = j then 1 else 0) * v j)) -
            beta * v i *
              ((Finset.univ : Finset (Fin n)).sum (fun j => v j * v j)) := by
            simp_rw [hterm]
            rw [Finset.sum_sub_distrib]
            congr 1
            rw [Finset.mul_sum]
    _ = v i - beta * v i *
          ((Finset.univ : Finset (Fin n)).sum (fun j => v j * v j)) := by
          simp [Finset.sum_ite_eq, Finset.mem_univ]
    _ = v i -
          (beta *
            ((Finset.univ : Finset (Fin n)).sum (fun j => v j * v j))) *
            v i := by
          ring
    _ = -v i := by
          rw [hbeta]
          ring

/-- Problem 19.1 Householder fixed subspace: vectors orthogonal to the defining
Householder vector are fixed by the reflector.  Together with
`householder_mul_defining_vector_neg`, this exposes the usual `+1` and `-1`
eigendirections without adding a new eigenvalue API. -/
theorem householder_mul_orthogonal_vector {n : Nat}
    (v x : Fin n -> Real) (beta : Real)
    (horth :
      ((Finset.univ : Finset (Fin n)).sum (fun j => v j * x j)) = 0) :
    matMulVec n (householder n v beta) x = x := by
  ext i
  unfold matMulVec householder idMatrix
  have hterm : forall j : Fin n,
      ((if i = j then 1 else 0) - beta * v i * v j) * x j =
        (if i = j then 1 else 0) * x j -
          (beta * v i) * (v j * x j) := by
    intro j
    ring
  calc
    ((Finset.univ : Finset (Fin n)).sum
        (fun j => ((if i = j then 1 else 0) - beta * v i * v j) * x j))
        =
          ((Finset.univ : Finset (Fin n)).sum
            (fun j => (if i = j then 1 else 0) * x j)) -
            beta * v i *
              ((Finset.univ : Finset (Fin n)).sum (fun j => v j * x j)) := by
            simp_rw [hterm]
            rw [Finset.sum_sub_distrib]
            congr 1
            rw [Finset.mul_sum]
    _ = x i - beta * v i *
          ((Finset.univ : Finset (Fin n)).sum (fun j => v j * x j)) := by
          simp [Finset.sum_ite_eq, Finset.mem_univ]
    _ = x i := by
          rw [horth]
          ring

/-- Problem 19.1 Givens active-plane action: the two rotated coordinates follow
the standard real two-by-two rotation formula.  This records the real part of
the Givens eigenvalue/fixed-plane calculation in the repository's
matrix-vector API. -/
theorem givens_active_plane_action {n : Nat}
    (p q : Fin n) (c s : Real) (x : Fin n -> Real)
    (hpq : Not (p = q)) :
    matMulVec n (givensRotation n p q c s) x p = c * x p + s * x q /\
    matMulVec n (givensRotation n p q c s) x q = c * x q - s * x p := by
  exact And.intro
    (givensRotation_matMulVec_p n p q c s x hpq)
    (givensRotation_matMulVec_q n p q c s x hpq)

/-- Problem 19.1 Givens fixed subspace: if a vector has zero entries in the two
rotated coordinates, then the exact Givens rotation fixes it.  This records the
real `+1` fixed-plane contribution of a Givens rotation. -/
theorem givens_mul_fixed_of_zero_pair {n : Nat}
    (p q : Fin n) (c s : Real) (x : Fin n -> Real)
    (hpq : Not (p = q)) (hxp : x p = 0) (hxq : x q = 0) :
    matMulVec n (givensRotation n p q c s) x = x := by
  ext i
  exact givensRotation_matMulVec_pair_zero n p q c s x hpq hxp hxq i

/-- Complex matrix-vector action for a real square matrix.  This is kept local
to Problem 19.1 so the complex Givens eigenvalue statement can be recorded
without changing the repository's real `matMulVec` API. -/
noncomputable def complexMatMulVec (n : Nat)
    (A : Fin n -> Fin n -> Real) (x : Fin n -> Complex) :
    Fin n -> Complex :=
  fun i =>
    (Finset.univ : Finset (Fin n)).sum
      (fun j => (A i j : Complex) * x j)

/-- A nonzero complex right-eigenvector/eigenvalue relation for the legacy real
matrix representation used in the QR files. -/
def IsComplexRightEigenpair (n : Nat) (A : Fin n -> Fin n -> Real)
    (lambda : Complex) (x : Fin n -> Complex) : Prop :=
  (Exists fun i : Fin n => Ne (x i) 0) /\
    forall i : Fin n, complexMatMulVec n A x i = lambda * x i

private theorem complex_sum_two_point {n : Nat} (p q : Fin n) (a b : Complex)
    (x : Fin n -> Complex) (hpq : Not (p = q)) :
    ((Finset.univ : Finset (Fin n)).sum
        (fun j => (if j = p then a else if j = q then b else 0) * x j)) =
      a * x p + b * x q := by
  let f : Fin n -> Complex := fun j =>
    (if j = p then a else if j = q then b else 0) * x j
  have hp : Membership.mem (Finset.univ : Finset (Fin n)) p :=
    Finset.mem_univ p
  have hq : Membership.mem ((Finset.univ : Finset (Fin n)).erase p) q :=
    Finset.mem_erase.mpr
      (And.intro (fun h => hpq h.symm) (Finset.mem_univ q))
  have hqp : Not (q = p) := fun h => hpq h.symm
  have hrest :
      (((Finset.univ : Finset (Fin n)).erase p).erase q).sum f = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj
    have hjq : Not (j = q) := hj.1
    have hjp : Not (j = p) := hj.2
    simp [hjp, hjq]
  calc
    ((Finset.univ : Finset (Fin n)).sum
        (fun j => (if j = p then a else if j = q then b else 0) * x j))
        = (Finset.univ : Finset (Fin n)).sum f := rfl
    _ = f p + f q +
          (((Finset.univ : Finset (Fin n)).erase p).erase q).sum f := by
        rw [(Finset.add_sum_erase (Finset.univ : Finset (Fin n)) f hp).symm]
        rw [(Finset.add_sum_erase
          ((Finset.univ : Finset (Fin n)).erase p) f hq).symm]
        ring
    _ = a * x p + b * x q := by
        rw [hrest]
        simp [f, hqp]

/-- Complex `p`-component of applying an exact real Givens rotation. -/
theorem complexMatMulVec_givens_p {n : Nat}
    (p q : Fin n) (c s : Real) (x : Fin n -> Complex)
    (hpq : Not (p = q)) :
    complexMatMulVec n (givensRotation n p q c s) x p =
      (c : Complex) * x p + (s : Complex) * x q := by
  have hqp : Not (q = p) := fun h => hpq h.symm
  unfold complexMatMulVec
  calc
    ((Finset.univ : Finset (Fin n)).sum
        (fun j => (givensRotation n p q c s p j : Complex) * x j))
        = ((Finset.univ : Finset (Fin n)).sum
          (fun j =>
            (if j = p then (c : Complex)
             else if j = q then (s : Complex) else 0) * x j)) := by
            apply Finset.sum_congr rfl
            intro j _
            unfold givensRotation
            by_cases hjp : j = p
            case pos =>
              simp [hjp]
            case neg =>
              have hpj : Not (p = j) := fun h => hjp h.symm
              by_cases hjq : j = q
              case pos =>
                simp [hjq, hpq, hqp]
              case neg =>
                simp [hjp, hpj, hjq, hpq]
    _ = (c : Complex) * x p + (s : Complex) * x q := by
        exact complex_sum_two_point p q (c : Complex) (s : Complex) x hpq

/-- Complex `q`-component of applying an exact real Givens rotation. -/
theorem complexMatMulVec_givens_q {n : Nat}
    (p q : Fin n) (c s : Real) (x : Fin n -> Complex)
    (hpq : Not (p = q)) :
    complexMatMulVec n (givensRotation n p q c s) x q =
      (c : Complex) * x q - (s : Complex) * x p := by
  have hqp : Not (q = p) := fun h => hpq h.symm
  unfold complexMatMulVec
  calc
    ((Finset.univ : Finset (Fin n)).sum
        (fun j => (givensRotation n p q c s q j : Complex) * x j))
        = ((Finset.univ : Finset (Fin n)).sum
          (fun j =>
            (if j = p then (-(s : Complex))
             else if j = q then (c : Complex) else 0) * x j)) := by
            apply Finset.sum_congr rfl
            intro j _
            unfold givensRotation
            by_cases hjp : j = p
            case pos =>
              simp [hjp, hpq, hqp]
            case neg =>
              by_cases hjq : j = q
              case pos =>
                simp [hjq, hqp]
              case neg =>
                have hqj : Not (q = j) := fun h => hjq h.symm
                simp [hjp, hjq, hqj, hqp]
    _ = (-(s : Complex)) * x p + (c : Complex) * x q := by
        exact complex_sum_two_point p q (-(s : Complex)) (c : Complex) x hpq
    _ = (c : Complex) * x q - (s : Complex) * x p := by
        ring

/-- Unaffected complex components of an exact real Givens application are
copied. -/
theorem complexMatMulVec_givens_other {n : Nat}
    (p q i : Fin n) (c s : Real) (x : Fin n -> Complex)
    (hip : Not (i = p)) (hiq : Not (i = q)) :
    complexMatMulVec n (givensRotation n p q c s) x i = x i := by
  unfold complexMatMulVec
  have hrow :
      ((Finset.univ : Finset (Fin n)).sum
        (fun j => (givensRotation n p q c s i j : Complex) * x j)) =
      ((Finset.univ : Finset (Fin n)).sum
        (fun j => (if i = j then (1 : Complex) else 0) * x j)) := by
    apply Finset.sum_congr rfl
    intro j _
    unfold givensRotation
    by_cases hij : i = j
    case pos =>
      subst j
      simp [hip, hiq]
    case neg =>
      simp [hij, hip, hiq]
  rw [hrow]
  simp [Finset.sum_ite_eq, Finset.mem_univ]

/-- The Givens active-plane complex eigenvalue `c + i*s`. -/
noncomputable def givensComplexEigenvaluePlus (c s : Real) : Complex :=
  (c : Complex) + (s : Complex) * Complex.I

/-- The Givens active-plane complex eigenvalue `c - i*s`. -/
noncomputable def givensComplexEigenvalueMinus (c s : Real) : Complex :=
  (c : Complex) - (s : Complex) * Complex.I

/-- Complex eigenvector supported on the Givens active plane for `c + i*s`. -/
noncomputable def givensComplexEigenvectorPlus {n : Nat}
    (p q : Fin n) : Fin n -> Complex :=
  fun i => if i = p then 1 else if i = q then Complex.I else 0

/-- Complex eigenvector supported on the Givens active plane for `c - i*s`. -/
noncomputable def givensComplexEigenvectorMinus {n : Nat}
    (p q : Fin n) : Fin n -> Complex :=
  fun i => if i = p then 1 else if i = q then -Complex.I else 0

/-- Problem 19.1 Givens complex eigendirection for `c + i*s`. -/
theorem givens_complex_eigenpair_plus {n : Nat}
    (p q : Fin n) (c s : Real) (hpq : Not (p = q)) :
    IsComplexRightEigenpair n (givensRotation n p q c s)
      (givensComplexEigenvaluePlus c s)
      (givensComplexEigenvectorPlus p q) := by
  unfold IsComplexRightEigenpair
  constructor
  case left =>
    exact Exists.intro p (by simp [givensComplexEigenvectorPlus])
  case right =>
    have hqp : Not (q = p) := fun h => hpq h.symm
    intro i
    by_cases hip : i = p
    case pos =>
      subst i
      rw [complexMatMulVec_givens_p p q c s
        (givensComplexEigenvectorPlus p q) hpq]
      simp [givensComplexEigenvectorPlus, givensComplexEigenvaluePlus, hqp]
    case neg =>
      by_cases hiq : i = q
      case pos =>
        subst i
        rw [complexMatMulVec_givens_q p q c s
          (givensComplexEigenvectorPlus p q) hpq]
        simp [givensComplexEigenvectorPlus, givensComplexEigenvaluePlus, hqp]
        apply Complex.ext <;>
          simp [Complex.mul_re, Complex.mul_im, Complex.add_re,
            Complex.add_im, Complex.sub_re, Complex.sub_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      case neg =>
        rw [complexMatMulVec_givens_other p q i c s
          (givensComplexEigenvectorPlus p q) hip hiq]
        simp [givensComplexEigenvectorPlus, hip, hiq]

/-- Problem 19.1 Givens complex eigendirection for `c - i*s`. -/
theorem givens_complex_eigenpair_minus {n : Nat}
    (p q : Fin n) (c s : Real) (hpq : Not (p = q)) :
    IsComplexRightEigenpair n (givensRotation n p q c s)
      (givensComplexEigenvalueMinus c s)
      (givensComplexEigenvectorMinus p q) := by
  unfold IsComplexRightEigenpair
  constructor
  case left =>
    exact Exists.intro p (by simp [givensComplexEigenvectorMinus])
  case right =>
    have hqp : Not (q = p) := fun h => hpq h.symm
    intro i
    by_cases hip : i = p
    case pos =>
      subst i
      rw [complexMatMulVec_givens_p p q c s
        (givensComplexEigenvectorMinus p q) hpq]
      simp [givensComplexEigenvectorMinus, givensComplexEigenvalueMinus, hqp]
      ring
    case neg =>
      by_cases hiq : i = q
      case pos =>
        subst i
        rw [complexMatMulVec_givens_q p q c s
          (givensComplexEigenvectorMinus p q) hpq]
        simp [givensComplexEigenvectorMinus, givensComplexEigenvalueMinus, hqp]
        apply Complex.ext <;>
          simp [Complex.mul_re, Complex.mul_im, Complex.sub_re,
            Complex.sub_im, Complex.neg_re, Complex.neg_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      case neg =>
        rw [complexMatMulVec_givens_other p q i c s
          (givensComplexEigenvectorMinus p q) hip hiq]
        simp [givensComplexEigenvectorMinus, hip, hiq]

end Problem19_1

namespace Algorithm19_11

/-- Source-facing state equations for Higham Algorithm 19.11, classical
Gram-Schmidt. -/
abbrev State {m n : Nat}
    (A Q : Fin m -> Fin n -> Real) (R : Fin n -> Fin n -> Real) : Prop :=
  ClassicalGramSchmidtState A Q R

/-- Classical Gram-Schmidt residual `a_j - sum_{k<j} r_kj q_k`. -/
abbrev residual {m n : Nat}
    (A Q : Fin m -> Fin n -> Real) (R : Fin n -> Fin n -> Real)
    (j : Fin n) : Fin m -> Real :=
  classicalGramSchmidtResidual A Q R j

end Algorithm19_11

namespace Algorithm19_12

/-- Exact stage vectors for Higham Algorithm 19.12, modified Gram-Schmidt. -/
abbrev stageVectors {m n : Nat} (A : Fin m -> Fin n -> Real) :
    Nat -> Fin n -> Fin m -> Real :=
  modifiedGramSchmidtVectors A

/-- Exact `Q` columns computed by the MGS skeleton. -/
abbrev computedQ {m n : Nat} (A : Fin m -> Fin n -> Real) :
    Fin m -> Fin n -> Real :=
  modifiedGramSchmidtQ A

/-- Exact `R` coefficients computed by the MGS skeleton. -/
abbrev computedR {m n : Nat} (A : Fin m -> Fin n -> Real) :
    Fin n -> Fin n -> Real :=
  modifiedGramSchmidtR A

/-- Source-style MGS stage matrix `A_t`. -/
abbrev sourceStage {m n : Nat} (A : Fin m -> Fin n -> Real) (t : Nat) :
    Fin m -> Fin n -> Real :=
  modifiedGramSchmidtSourceStage A t

/-- Source-style one-step MGS factor `R_k`. -/
abbrev stepR {m n : Nat} (A : Fin m -> Fin n -> Real) (k : Fin n) :
    Fin n -> Fin n -> Real :=
  modifiedGramSchmidtStepR A k

/-- Source-style product of one-step MGS factors through stage `t`, ordered as
`R_(t-1) * ... * R_0`. -/
abbrev stepRProduct {m n : Nat} (A : Fin m -> Fin n -> Real) :
    Nat -> Fin n -> Fin n -> Real :=
  modifiedGramSchmidtStepRProduct A

/-- Source-facing state equations for Algorithm 19.12. -/
abbrev State {m n : Nat}
    (A Q : Fin m -> Fin n -> Real) (R : Fin n -> Fin n -> Real) : Prop :=
  ModifiedGramSchmidtState A Q R

/-- The exact MGS skeleton satisfies the Algorithm 19.12 state equations. -/
theorem exact_state {m n : Nat} (A : Fin m -> Fin n -> Real) :
    State A (computedQ A) (computedR A) := by
  exact modifiedGramSchmidtState_exact A

/-- The exact MGS `R` factor is upper-trapezoidal. -/
theorem computedR_upper_trapezoidal {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    IsUpperTrapezoidal n n (computedR A) := by
  exact modifiedGramSchmidtR_upper_trapezoidal A

/-- Each source-style one-step MGS factor `R_k` is upper-trapezoidal. -/
theorem stepR_upper_trapezoidal {m n : Nat}
    (A : Fin m -> Fin n -> Real) (k : Fin n) :
    IsUpperTrapezoidal n n (stepR A k) := by
  exact modifiedGramSchmidtStepR_upper_trapezoidal A k

/-- A later MGS stage vector is the projection update from Algorithm 19.12. -/
theorem stageVectors_succ_later {m n : Nat}
    (A : Fin m -> Fin n -> Real) {k j : Fin n} (hkj : k < j) :
    stageVectors A (k.val + 1) j =
      gsProjectAway (stageVectors A k.val j)
        (gsNormalize (stageVectors A k.val k)
          (gsColumnNorm2 (stageVectors A k.val k))) := by
  exact modifiedGramSchmidtVectors_succ_later A hkj

/-- The normalized current MGS column has self-dot equal to its stage norm.
This is the diagonal scalar channel used in the padded Householder-MGS stage
transition. -/
theorem computedQ_stage_self_dot {m n : Nat}
    (A : Fin m -> Fin n -> Real) (k : Fin n)
    (hdiag : Ne (gsColumnNorm2 (stageVectors A k.val k)) 0) :
    gsDot (gsColumn (computedQ A) k) (stageVectors A k.val k) =
      gsColumnNorm2 (stageVectors A k.val k) := by
  simpa [computedQ, stageVectors, gsColumn] using
    (gsDot_normalize_self (stageVectors A k.val k) hdiag)

/-- The normalized current MGS column has unit squared norm under the same
nonzero stage-norm condition. -/
theorem computedQ_column_norm_sq {m n : Nat}
    (A : Fin m -> Fin n -> Real) (k : Fin n)
    (hdiag : Ne (gsColumnNorm2 (stageVectors A k.val k)) 0) :
    finiteVecNorm2Sq (gsColumn (computedQ A) k) = 1 := by
  exact modifiedGramSchmidtQ_column_norm_sq A k hdiag

/-- Current-column recombination for the source-stage recurrence behind
Higham equation (19.32). -/
theorem sourceStage_current_recombine {m n : Nat}
    (A : Fin m -> Fin n -> Real) (k : Fin n)
    (hdiag : Ne (gsColumnNorm2 (stageVectors A k.val k)) 0) :
    gsColumn (sourceStage A k.val) k =
      fun i =>
        gsColumn (sourceStage A (k.val + 1)) k i *
          stepR A k k k := by
  exact modifiedGramSchmidtSourceStage_current_recombine A k hdiag

/-- Strict-upper-column recombination for the source-stage recurrence behind
Higham equation (19.32). -/
theorem sourceStage_later_recombine {m n : Nat}
    (A : Fin m -> Fin n -> Real) {k j : Fin n} (hkj : k < j) :
    gsColumn (sourceStage A k.val) j =
      fun i =>
        gsColumn (sourceStage A (k.val + 1)) j i +
          stepR A k k j * gsColumn (sourceStage A (k.val + 1)) k i := by
  exact modifiedGramSchmidtSourceStage_later_recombine A hkj

/-- Source-stage matrix recurrence `A_k = A_{k+1} R_k` behind Higham
equation (19.32), with the current stage norm required to be nonzero. -/
theorem sourceStage_matrix_recurrence {m n : Nat}
    (A : Fin m -> Fin n -> Real) (k : Fin n)
    (hdiag : Ne (gsColumnNorm2 (stageVectors A k.val k)) 0) :
    sourceStage A k.val =
      matMulRect m n n (sourceStage A (k.val + 1)) (stepR A k) := by
  exact modifiedGramSchmidtSourceStage_matrix_recurrence A k hdiag

/-- Iterated source-stage recurrence behind the product term in Higham
equation (19.33). -/
theorem sourceStage_initial_matrix_recurrence {m n : Nat}
    (A : Fin m -> Fin n -> Real) {t : Nat} (ht : t <= n)
    (hdiag : forall k : Fin n, k.val < t ->
      Ne (gsColumnNorm2 (stageVectors A k.val k)) 0) :
    A = matMulRect m n n (sourceStage A t) (stepRProduct A t) := by
  exact modifiedGramSchmidtSourceStage_initial_matrix_recurrence A ht hdiag

/-- Exact MGS product factorization obtained from the source-stage recurrence.
This is an exact-arithmetic dependency for the MGS stability proof, not the
floating-point theorem of Higham Theorem 19.13. -/
theorem exact_product_factorization {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (hdiag : forall k : Fin n,
      Ne (gsColumnNorm2 (stageVectors A k.val k)) 0) :
    A = matMulRect m n n (computedQ A) (stepRProduct A n) := by
  exact modifiedGramSchmidt_exact_product_factorization A hdiag

/-- The full one-step product is the exact `R` matrix computed by the MGS
skeleton. -/
theorem stepRProduct_eq_computedR {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    stepRProduct A n = computedR A := by
  exact modifiedGramSchmidtStepRProduct_eq_R A

/-- Exact Algorithm 19.12 factorization `A = Q R` for the MGS definitions,
under the nonzero stage-norm assumptions needed for normalization. -/
theorem exact_factorization {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (hdiag : forall k : Fin n,
      Ne (gsColumnNorm2 (stageVectors A k.val k)) 0) :
    A = matMulRect m n n (computedQ A) (computedR A) := by
  exact modifiedGramSchmidt_exact_factorization A hdiag

end Algorithm19_12

namespace Theorem19_13

/-- Source-facing contract shape for Higham Theorem 19.13, using the
repository's predicate-style operator-2 bounds. -/
abbrev MGSQRBounds (m n : Nat)
    (A Qhat : Fin m -> Fin n -> Real) (Rhat : Fin n -> Fin n -> Real)
    (c1 c2 c3 u normA kappaA higherOrder : Real) : Prop :=
  ModifiedGramSchmidtBackwardError m n A Qhat Rhat c1 c2 c3 u normA
    kappaA higherOrder

/-- Source-facing output contract for the QR-sensitivity step used after
equation `(19.34)` in the proof of Theorem 19.13. -/
abbrev QRSensitivityBridge (m n : Nat)
    (A Qhat : Fin m -> Fin n -> Real) (Rhat : Fin n -> Fin n -> Real)
    (c2 c3 u kappaA higherOrder : Real) : Prop :=
  ModifiedGramSchmidtQRSensitivityBridge m n A Qhat Rhat c2 c3 u
    kappaA higherOrder

/-- Source-labeled output contract for the QR-sensitivity step, separating the
`(19.35a)`-`(19.37)` route from the compact bridge used by the MGS theorem. -/
abbrev QRSensitivitySourceOutput (m n : Nat)
    (A Qhat : Fin m -> Fin n -> Real) (Rhat : Fin n -> Fin n -> Real)
    (c2 c3 u kappaA higherOrder : Real) : Prop :=
  ModifiedGramSchmidtQRSensitivitySourceOutput m n A Qhat Rhat c2 c3 u
    kappaA higherOrder

/-- Pure source-shaped correction-map data for Problem 19.12, before choosing
the common right factor `R`. -/
abbrev Problem1912CorrectionMapData (m n : Nat)
    (P11 : Fin n -> Fin n -> Real)
    (P21 Q F : Fin m -> Fin n -> Real) : Prop :=
  MGSProblem1912CorrectionMapData m n P11 P21 Q F

/-- Source-shaped correction-map contract for Problem 19.12, specialized to
the Theorem 19.13 Householder-MGS block notation after choosing `R`. -/
abbrev Problem1912CorrectionMap (m n : Nat)
    (P21 Q : Fin m -> Fin n -> Real)
    (dTop R : Fin n -> Fin n -> Real)
    (F : Fin m -> Fin n -> Real) : Prop :=
  MGSProblem1912CorrectionMap m n P21 Q dTop R F

/-- Source-shaped diagonal CS factor payload for Problem 19.12.  This is the
single data object the remaining CS/polar existence theorem should produce. -/
abbrev Problem1912CSDiagonalFactorData (m n : Nat)
    (P11 : Fin n -> Fin n -> Real)
    (P21 : Fin m -> Fin n -> Real) : Type :=
  MGSProblem1912CSDiagonalFactorData m n P11 P21

/-- Source-shaped polar-factor payload for Problem 19.12.  This is a
non-diagonal payload the remaining CS/polar existence theorem may produce. -/
abbrev Problem1912PolarFactorData (m n : Nat)
    (P11 : Fin n -> Fin n -> Real)
    (P21 : Fin m -> Fin n -> Real) : Type :=
  MGSProblem1912PolarFactorData m n P11 P21

/-- Full-positive right-Gram polar isometry for the lower block in Problem
19.12. -/
abbrev Problem1912RightGramPolarQFull {m n : Nat}
    (P21 : Fin m -> Fin n -> Real) : Fin m -> Fin n -> Real :=
  rectRightGramPolarQFull P21

/-- Zero-safe right-Gram polar isometry candidate for the lower block in
Problem 19.12.  This reconstructs the bottom factor without full positivity,
but still requires an orthonormal completion before it closes the theorem. -/
abbrev Problem1912RightGramPolarQZeroSafe {m n : Nat}
    (P21 : Fin m -> Fin n -> Real) : Fin m -> Fin n -> Real :=
  rectRightGramPolarQZeroSafe P21

/-- Full-positive right-Gram polar positive factor for the lower block in
Problem 19.12. -/
abbrev Problem1912RightGramPolarH {m n : Nat}
    (P21 : Fin m -> Fin n -> Real) : Fin n -> Fin n -> Real :=
  rectRightGramPolarH P21

/-- Spectral `(I+H)^{-1}` factor for the lower-block right-Gram polar factor
in Problem 19.12. -/
abbrev Problem1912RightGramPolarResolvent {m n : Nat}
    (P21 : Fin m -> Fin n -> Real) : Fin n -> Fin n -> Real :=
  rectRightGramPolarResolvent P21

/-- Concrete full-positive polar bridge matrix
`T = (I+H)^{-1} * P11^T` for Problem 19.12. -/
abbrev Problem1912FullPositivePolarBridgeT {m n : Nat}
    (P11 : Fin n -> Fin n -> Real) (P21 : Fin m -> Fin n -> Real) :
    Fin n -> Fin n -> Real :=
  mgsProblem1912_fullPositivePolarBridgeT P11 P21

/-- Name-neutral spectral polar bridge matrix
`T = (I+H)^{-1} * P11^T` for Problem 19.12. -/
abbrev Problem1912RightGramPolarBridgeT {m n : Nat}
    (P11 : Fin n -> Fin n -> Real) (P21 : Fin m -> Fin n -> Real) :
    Fin n -> Fin n -> Real :=
  mgsProblem1912_rightGramPolarBridgeT P11 P21

/-- Corrected source-shaped input for the remaining Problem 19.12 CS/polar
existence theorem: tallness plus the block-column Gram identity. -/
abbrev Problem1912CSPolarInput (m n : Nat)
    (P11 : Fin n -> Fin n -> Real)
    (P21 : Fin m -> Fin n -> Real) : Prop :=
  MGSProblem1912CSPolarInput m n P11 P21

/-- Chapter-labeled CS-algebra factor identity for Problem 19.12:
from `P11 = U C W^T`, `P21 = V S W^T`, `Q = V W^T`, `F = V T U^T`,
and `T C = I - S`, obtain `F P11 = Q - P21`. -/
theorem problem1912_csAlgebra_correction_factor {m n : Nat}
    {P11 U C S T W : Fin n -> Fin n -> Real}
    {P21 Q V F : Fin m -> Fin n -> Real}
    (hP11 : P11 = matMul n U (matMul n C (finiteTranspose W)))
    (hP21 : P21 =
      matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQ : Q = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hU : matMul n (finiteTranspose U) U = idMatrix n)
    (hTC : matMul n T C = fun i j => idMatrix n i j - S i j) :
    matMulRect m n n F P11 = fun i j => Q i j - P21 i j := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_csAlgebra_correction_factor hP11 hP21
      hQ hF hU hTC

/-- Chapter-labeled construction of the pure Problem 19.12 correction-map data
from explicit CS-decomposition algebra data. -/
theorem problem1912_correctionMapData_of_csAlgebra {m n : Nat}
    {P11 U C S T W : Fin n -> Fin n -> Real}
    {P21 Q V F : Fin m -> Fin n -> Real}
    (hP11 : P11 = matMul n U (matMul n C (finiteTranspose W)))
    (hP21 : P21 =
      matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQ : Q = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hU : matMul n (finiteTranspose U) U = idMatrix n)
    (hTC : matMul n T C = fun i j => idMatrix n i j - S i j)
    (hQorth : GramSchmidtOrthonormalColumns Q)
    (hFbound : rectOpNorm2Le F 1) :
    Problem1912CorrectionMapData m n P11 P21 Q F := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_correctionMapData_of_csAlgebra
      hP11 hP21 hQ hF hU hTC hQorth hFbound

/-- Chapter-labeled additive orientation of pure Problem 19.12
correction-map data: `Q = P21 + F * P11`.

This is the orientation expected from the CS/polar existence theorem; the
stored data remains the subtraction form consumed by downstream repair lemmas. -/
theorem problem1912_correctionMapData_add_factor_eq {m n : Nat}
    {P11 : Fin n -> Fin n -> Real}
    {P21 Q F : Fin m -> Fin n -> Real}
    (hdata : Problem1912CorrectionMapData m n P11 P21 Q F) :
    Q = fun i j => P21 i j + matMulRect m n n F P11 i j := by
  exact
    LeanFpAnalysis.FP.MGSProblem1912CorrectionMapData.add_factor_eq hdata

/-- Chapter-labeled constructor for pure Problem 19.12 correction-map data
from the additive CS/polar orientation `Q = P21 + F * P11`. -/
theorem problem1912_correctionMapData_of_add_factor {m n : Nat}
    {P11 : Fin n -> Fin n -> Real}
    {P21 Q F : Fin m -> Fin n -> Real}
    (hQadd : Q = fun i j => P21 i j + matMulRect m n n F P11 i j)
    (hQorth : GramSchmidtOrthonormalColumns Q)
    (hFbound : rectOpNorm2Le F 1) :
    Problem1912CorrectionMapData m n P11 P21 Q F := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_correctionMapData_of_add_factor
      hQadd hQorth hFbound

/-- Chapter-labeled polar-factor algebra for Problem 19.12:
from `P21 = Q*H`, `F = Q*T`, and `T*P11 = I-H`, obtain
`F*P11 = Q-P21`. -/
theorem problem1912_polarAlgebra_correction_factor {m n : Nat}
    {P11 H T : Fin n -> Fin n -> Real}
    {P21 Q F : Fin m -> Fin n -> Real}
    (hP21 : P21 = matMulRect m n n Q H)
    (hF : F = matMulRect m n n Q T)
    (hTP : matMul n T P11 = fun i j => idMatrix n i j - H i j) :
    matMulRect m n n F P11 = fun i j => Q i j - P21 i j := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_polarAlgebra_correction_factor
      hP21 hF hTP

/-- Chapter-labeled construction of pure Problem 19.12 correction-map data
from a polar-style algebraic payload. -/
theorem problem1912_correctionMapData_of_polarAlgebra {m n : Nat}
    {P11 H T : Fin n -> Fin n -> Real}
    {P21 Q F : Fin m -> Fin n -> Real}
    (hP21 : P21 = matMulRect m n n Q H)
    (hF : F = matMulRect m n n Q T)
    (hTP : matMul n T P11 = fun i j => idMatrix n i j - H i j)
    (hQorth : GramSchmidtOrthonormalColumns Q)
    (hFbound : rectOpNorm2Le F 1) :
    Problem1912CorrectionMapData m n P11 P21 Q F := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_correctionMapData_of_polarAlgebra
      hP21 hF hTP hQorth hFbound

/-- Chapter-labeled orthonormality of the full-positive right-Gram polar
isometry for the lower block. -/
theorem problem1912_rightGramPolarQFull_orthonormal_of_pos {m n : Nat}
    (P21 : Fin m -> Fin n -> Real)
    (hpos : forall a : Fin n, 0 < rectRightGramBasisSingularValue P21 a) :
    GramSchmidtOrthonormalColumns
      (Problem1912RightGramPolarQFull P21) := by
  exact rectRightGramPolarQFull_orthonormal_of_pos P21 hpos

/-- Chapter-labeled full-positive right-Gram polar factorization of the lower
block. -/
theorem problem1912_rightGramPolarQFull_mul_polarH_of_pos {m n : Nat}
    (P21 : Fin m -> Fin n -> Real)
    (hpos : forall a : Fin n, 0 < rectRightGramBasisSingularValue P21 a) :
    matMulRect m n n (Problem1912RightGramPolarQFull P21)
        (Problem1912RightGramPolarH P21) =
      P21 := by
  exact rectRightGramPolarQFull_mul_polarH_of_pos P21 hpos

/-- Chapter-labeled zero-safe right-Gram polar factorization of the lower
block.  The factorization holds without full positivity; the remaining
mixed-rank obligation is the orthonormal completion of zero singular
directions. -/
theorem problem1912_rightGramPolarQZeroSafe_mul_polarH {m n : Nat}
    (P21 : Fin m -> Fin n -> Real) :
    matMulRect m n n (Problem1912RightGramPolarQZeroSafe P21)
        (Problem1912RightGramPolarH P21) =
      P21 := by
  exact rectRightGramPolarQZeroSafe_mul_polarH P21

/-- Chapter-labeled symmetry of the full-positive right-Gram polar positive
factor. -/
theorem problem1912_rightGramPolarH_symmetric {m n : Nat}
    (P21 : Fin m -> Fin n -> Real) :
    finiteTranspose (Problem1912RightGramPolarH P21) =
      Problem1912RightGramPolarH P21 := by
  exact rectRightGramPolarH_symmetric P21

/-- Chapter-labeled full-positive right-Gram identity `H^2 = P21^T P21`. -/
theorem problem1912_rightGramPolarH_sq_eq_rectangularGram_of_pos
    {m n : Nat}
    (P21 : Fin m -> Fin n -> Real)
    (hpos : forall a : Fin n, 0 < rectRightGramBasisSingularValue P21 a) :
    matMul n (Problem1912RightGramPolarH P21)
        (Problem1912RightGramPolarH P21) =
      rectangularGram P21 := by
  exact rectRightGramPolarH_sq_eq_rectangularGram_of_pos P21 hpos

/-- Chapter-labeled spectral square identity for the full-positive polar
positive factor. -/
theorem problem1912_rightGramPolarH_sq_eq_spectral_square {m n : Nat}
    (P21 : Fin m -> Fin n -> Real) :
    matMul n (Problem1912RightGramPolarH P21)
        (Problem1912RightGramPolarH P21) =
      matMul n (rectRightGramEigenbasis P21)
        (matMul n (finiteDiagonal
            (fun i => rectRightGramBasisSingularValue P21 i ^ 2))
          (finiteTranspose (rectRightGramEigenbasis P21))) := by
  exact rectRightGramPolarH_sq_eq_spectral_square P21

/-- Chapter-labeled recomposition of the right-Gram spectral square back into
`P21^T P21`. -/
theorem problem1912_rightGram_spectral_square_eq_rectangularGram {m n : Nat}
    (P21 : Fin m -> Fin n -> Real) :
    matMul n (rectRightGramEigenbasis P21)
      (matMul n (finiteDiagonal
          (fun i => rectRightGramBasisSingularValue P21 i ^ 2))
        (finiteTranspose (rectRightGramEigenbasis P21))) =
      rectangularGram P21 := by
  exact rectRightGram_spectral_square_eq_rectangularGram P21

/-- Chapter-labeled right-Gram identity `H^2 = P21^T P21` with no
full-positivity assumption. -/
theorem problem1912_rightGramPolarH_sq_eq_rectangularGram {m n : Nat}
    (P21 : Fin m -> Fin n -> Real) :
    matMul n (Problem1912RightGramPolarH P21)
        (Problem1912RightGramPolarH P21) =
      rectangularGram P21 := by
  exact rectRightGramPolarH_sq_eq_rectangularGram P21

/-- Chapter-labeled contraction bound for the spectral `(I+H)^{-1}` factor. -/
theorem problem1912_rightGramPolarResolvent_opNorm2Le_one {m n : Nat}
    (P21 : Fin m -> Fin n -> Real) :
    opNorm2Le (Problem1912RightGramPolarResolvent P21) 1 := by
  exact rectRightGramPolarResolvent_opNorm2Le_one P21

/-- Chapter-labeled resolvent identity:
`(I+H)^{-1} * (I-H^2) = I-H`. -/
theorem problem1912_rightGramPolarResolvent_mul_id_sub_polarH_sq
    {m n : Nat}
    (P21 : Fin m -> Fin n -> Real) :
    matMul n (Problem1912RightGramPolarResolvent P21)
      (fun i j =>
        idMatrix n i j -
          matMul n (Problem1912RightGramPolarH P21)
            (Problem1912RightGramPolarH P21) i j) =
      fun i j => idMatrix n i j - Problem1912RightGramPolarH P21 i j := by
  exact rectRightGramPolarResolvent_mul_id_sub_polarH_sq P21

/-- Chapter-labeled full-positive polar rewrite of the top Gram:
`P11^T P11 = I - H^2`. -/
theorem problem1912_csPolarInput_p11_gram_eq_id_sub_polarH_sq
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21)
    (hpos : forall a : Fin n, 0 < rectRightGramBasisSingularValue P21 a) :
    rectangularGram P11 =
      fun i j =>
        idMatrix n i j -
          matMul n (Problem1912RightGramPolarH P21)
            (Problem1912RightGramPolarH P21) i j := by
  exact hinput.p11_gram_eq_id_sub_polarH_sq hpos

/-- Chapter-labeled full-positive right-Gram polar payload constructor.  The
bridge `T * P11 = I - H` and contraction bound are the remaining explicit
obligations. -/
def problem1912_polarFactorData_of_fullPositiveRightGram
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    {T : Fin n -> Fin n -> Real}
    (hpos : forall a : Fin n, 0 < rectRightGramBasisSingularValue P21 a)
    (hTP :
      matMul n T P11 =
        fun i j => idMatrix n i j - Problem1912RightGramPolarH P21 i j)
    (hT : opNorm2Le T 1) :
    Problem1912PolarFactorData m n P11 P21 :=
  LeanFpAnalysis.FP.mgsProblem1912_polarFactorData_of_fullPositive_rightGram
    hpos hTP hT

/-- Chapter-labeled concrete bridge identity for the full-positive polar
branch: `((I+H)^{-1} * P11^T) * P11 = I-H`. -/
theorem problem1912_fullPositivePolarBridgeT_mul_p11
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21)
    (hpos : forall a : Fin n, 0 < rectRightGramBasisSingularValue P21 a) :
    matMul n (Problem1912FullPositivePolarBridgeT P11 P21) P11 =
      fun i j => idMatrix n i j - Problem1912RightGramPolarH P21 i j := by
  exact mgsProblem1912_fullPositivePolarBridgeT_mul_p11 hinput hpos

/-- Chapter-labeled contraction bound for the concrete full-positive polar
bridge matrix. -/
theorem problem1912_fullPositivePolarBridgeT_opNorm2Le_one
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21) :
    opNorm2Le (Problem1912FullPositivePolarBridgeT P11 P21) 1 := by
  exact mgsProblem1912_fullPositivePolarBridgeT_opNorm2Le_one hinput

/-- Chapter-labeled completed-polar top-Gram rewrite:
`P11^T P11 = I-H^2` follows from the corrected input and the supplied
right-Gram square identity `H^2 = P21^T P21`. -/
theorem problem1912_csPolarInput_p11_gram_eq_id_sub_polarH_sq_of_polarH_sq
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21)
    (hHsq :
      matMul n (Problem1912RightGramPolarH P21)
          (Problem1912RightGramPolarH P21) =
        rectangularGram P21) :
    rectangularGram P11 =
      fun i j =>
        idMatrix n i j -
          matMul n (Problem1912RightGramPolarH P21)
            (Problem1912RightGramPolarH P21) i j := by
  exact hinput.p11_gram_eq_id_sub_polarH_sq_of_polarH_sq hHsq

/-- Chapter-labeled completed-polar bridge identity:
`((I+H)^{-1} * P11^T) * P11 = I-H`. -/
theorem problem1912_rightGramPolarBridgeT_mul_p11_of_polarH_sq
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21)
    (hHsq :
      matMul n (Problem1912RightGramPolarH P21)
          (Problem1912RightGramPolarH P21) =
        rectangularGram P21) :
    matMul n (Problem1912RightGramPolarBridgeT P11 P21) P11 =
      fun i j => idMatrix n i j - Problem1912RightGramPolarH P21 i j := by
  exact
    mgsProblem1912_rightGramPolarBridgeT_mul_p11_of_polarH_sq
      hinput hHsq

/-- Chapter-labeled contraction bound for the name-neutral spectral polar
bridge matrix. -/
theorem problem1912_rightGramPolarBridgeT_opNorm2Le_one
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21) :
    opNorm2Le (Problem1912RightGramPolarBridgeT P11 P21) 1 := by
  exact mgsProblem1912_rightGramPolarBridgeT_opNorm2Le_one hinput

/-- Chapter-labeled completed right-Gram polar payload constructor.  The
remaining mixed-branch foundation is isolated to the supplied completed polar
factor equations. -/
def problem1912_polarFactorData_of_completedRightGramPolar
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    {Q : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21)
    (hbottom :
      P21 = matMulRect m n n Q (Problem1912RightGramPolarH P21))
    (hQorth : GramSchmidtOrthonormalColumns Q)
    (hHsq :
      matMul n (Problem1912RightGramPolarH P21)
          (Problem1912RightGramPolarH P21) =
        rectangularGram P21) :
    Problem1912PolarFactorData m n P11 P21 :=
  mgsProblem1912_polarFactorData_of_completed_rightGramPolar
    hinput hbottom hQorth hHsq

/-- Chapter-facing pure correction-map data from a completed right-Gram polar
factor. -/
theorem problem1912_correctionMapData_exists_of_completedRightGramPolar
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    {Q : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21)
    (hbottom :
      P21 = matMulRect m n n Q (Problem1912RightGramPolarH P21))
    (hQorth : GramSchmidtOrthonormalColumns Q)
    (hHsq :
      matMul n (Problem1912RightGramPolarH P21)
          (Problem1912RightGramPolarH P21) =
        rectangularGram P21) :
    Exists fun Qout : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      Problem1912CorrectionMapData m n P11 P21 Qout F := by
  exact
    mgsProblem1912_correctionMapData_exists_of_completed_rightGramPolar
      hinput hbottom hQorth hHsq

/-- Chapter-facing additive witnesses from a completed right-Gram polar
factor. -/
theorem problem1912_add_factor_exists_of_completedRightGramPolar
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    {Q : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21)
    (hbottom :
      P21 = matMulRect m n n Q (Problem1912RightGramPolarH P21))
    (hQorth : GramSchmidtOrthonormalColumns Q)
    (hHsq :
      matMul n (Problem1912RightGramPolarH P21)
          (Problem1912RightGramPolarH P21) =
        rectangularGram P21) :
    Exists fun Qout : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      (Qout = fun i j => P21 i j + matMulRect m n n F P11 i j) /\
        GramSchmidtOrthonormalColumns Qout /\
        rectOpNorm2Le F 1 := by
  exact
    mgsProblem1912_add_factor_exists_of_completed_rightGramPolar
      hinput hbottom hQorth hHsq

/-- Chapter-labeled right-Gram polar completion payload constructor.  Since
`H^2 = P21^T P21` is now supplied by the spectral right-Gram construction, the
remaining completion data is just `P21 = Q*H` with orthonormal `Q`. -/
def problem1912_polarFactorData_of_rightGramPolarCompletion
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    {Q : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21)
    (hbottom :
      P21 = matMulRect m n n Q (Problem1912RightGramPolarH P21))
    (hQorth : GramSchmidtOrthonormalColumns Q) :
    Problem1912PolarFactorData m n P11 P21 :=
  mgsProblem1912_polarFactorData_of_rightGramPolar_completion
    hinput hbottom hQorth

/-- Chapter-facing pure correction-map data from a right-Gram polar
completion. -/
theorem problem1912_correctionMapData_exists_of_rightGramPolarCompletion
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    {Q : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21)
    (hbottom :
      P21 = matMulRect m n n Q (Problem1912RightGramPolarH P21))
    (hQorth : GramSchmidtOrthonormalColumns Q) :
    Exists fun Qout : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      Problem1912CorrectionMapData m n P11 P21 Qout F := by
  exact
    mgsProblem1912_correctionMapData_exists_of_rightGramPolar_completion
      hinput hbottom hQorth

/-- Chapter-facing additive witnesses from a right-Gram polar completion. -/
theorem problem1912_add_factor_exists_of_rightGramPolarCompletion
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    {Q : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21)
    (hbottom :
      P21 = matMulRect m n n Q (Problem1912RightGramPolarH P21))
    (hQorth : GramSchmidtOrthonormalColumns Q) :
    Exists fun Qout : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      (Qout = fun i j => P21 i j + matMulRect m n n F P11 i j) /\
        GramSchmidtOrthonormalColumns Qout /\
        rectOpNorm2Le F 1 := by
  exact
    mgsProblem1912_add_factor_exists_of_rightGramPolar_completion
      hinput hbottom hQorth

/-- Chapter-facing tall right-Gram polar completion extracted from the
corrected CS/polar input. -/
theorem problem1912_rightGramPolarCompletion_exists
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21) :
    Exists fun Q : Fin m -> Fin n -> Real =>
      P21 = matMulRect m n n Q (Problem1912RightGramPolarH P21) /\
        GramSchmidtOrthonormalColumns Q := by
  exact exists_rectRightGramPolarCompletion_of_tall P21 hinput.tall

/-- Chapter-facing pure correction-map data from the corrected CS/polar
input.  This closes the tall mixed-rank right-Gram polar completion branch. -/
theorem problem1912_correctionMapData_exists_of_csPolarInput
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21) :
    Exists fun Qout : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      Problem1912CorrectionMapData m n P11 P21 Qout F := by
  exact
    mgsProblem1912_correctionMapData_exists_of_csPolarInput hinput

/-- Chapter-facing additive Problem 19.12 witnesses from the corrected
CS/polar input. -/
theorem problem1912_add_factor_exists_of_csPolarInput
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21) :
    Exists fun Qout : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      (Qout = fun i j => P21 i j + matMulRect m n n F P11 i j) /\
        GramSchmidtOrthonormalColumns Qout /\
        rectOpNorm2Le F 1 := by
  exact
    mgsProblem1912_add_factor_exists_of_csPolarInput hinput

/-- Chapter-labeled full-positive right-Gram polar payload constructor from
the corrected CS/polar input.  The bridge and contraction obligations are
discharged by `T = (I+H)^{-1} * P11^T`. -/
def problem1912_polarFactorData_of_csPolarInput_fullPositiveRightGram
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21)
    (hpos : forall a : Fin n, 0 < rectRightGramBasisSingularValue P21 a) :
    Problem1912PolarFactorData m n P11 P21 :=
  mgsProblem1912_polarFactorData_of_csPolarInput_fullPositive_rightGram
    hinput hpos

/-- Full-positive right-Gram polar factors plus the remaining bridge produce
chapter-facing pure Problem 19.12 correction-map data. -/
theorem problem1912_correctionMapData_exists_of_fullPositiveRightGram
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    {T : Fin n -> Fin n -> Real}
    (hpos : forall a : Fin n, 0 < rectRightGramBasisSingularValue P21 a)
    (hTP :
      matMul n T P11 =
        fun i j => idMatrix n i j - Problem1912RightGramPolarH P21 i j)
    (hT : opNorm2Le T 1) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      Problem1912CorrectionMapData m n P11 P21 Q F := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_correctionMapData_exists_of_fullPositive_rightGram
      hpos hTP hT

/-- Full-positive right-Gram polar factors plus the corrected CS/polar input
produce chapter-facing pure Problem 19.12 correction-map data. -/
theorem problem1912_correctionMapData_exists_of_csPolarInput_fullPositiveRightGram
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21)
    (hpos : forall a : Fin n, 0 < rectRightGramBasisSingularValue P21 a) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      Problem1912CorrectionMapData m n P11 P21 Q F := by
  exact
    mgsProblem1912_correctionMapData_exists_of_csPolarInput_fullPositive_rightGram
      hinput hpos

/-- Full-positive right-Gram polar factors plus the remaining bridge produce
chapter-facing additive Problem 19.12 witnesses. -/
theorem problem1912_add_factor_exists_of_fullPositiveRightGram
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    {T : Fin n -> Fin n -> Real}
    (hpos : forall a : Fin n, 0 < rectRightGramBasisSingularValue P21 a)
    (hTP :
      matMul n T P11 =
        fun i j => idMatrix n i j - Problem1912RightGramPolarH P21 i j)
    (hT : opNorm2Le T 1) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      (Q = fun i j => P21 i j + matMulRect m n n F P11 i j) /\
        GramSchmidtOrthonormalColumns Q /\
        rectOpNorm2Le F 1 := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_add_factor_exists_of_fullPositive_rightGram
      hpos hTP hT

/-- Full-positive right-Gram polar factors plus the corrected CS/polar input
produce chapter-facing additive Problem 19.12 witnesses. -/
theorem problem1912_add_factor_exists_of_csPolarInput_fullPositiveRightGram
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21)
    (hpos : forall a : Fin n, 0 < rectRightGramBasisSingularValue P21 a) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      (Q = fun i j => P21 i j + matMulRect m n n F P11 i j) /\
        GramSchmidtOrthonormalColumns Q /\
        rectOpNorm2Le F 1 := by
  exact
    mgsProblem1912_add_factor_exists_of_csPolarInput_fullPositive_rightGram
      hinput hpos

/-- Chapter-facing branch router for the closed zero-top-Gram and
full-positive right-Gram polar cases of Problem 19.12. -/
theorem problem1912_correctionMapData_exists_of_csPolarInput_zeroOrFullPositiveRightGram
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21)
    (hcase :
      rectangularGram P11 = (fun _ _ => 0) \/
        forall a : Fin n, 0 < rectRightGramBasisSingularValue P21 a) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      Problem1912CorrectionMapData m n P11 P21 Q F := by
  exact
    mgsProblem1912_correctionMapData_exists_of_csPolarInput_zero_or_fullPositive_rightGram
      hinput hcase

/-- Chapter-facing additive branch router for the closed zero-top-Gram and
full-positive right-Gram polar cases of Problem 19.12. -/
theorem problem1912_add_factor_exists_of_csPolarInput_zeroOrFullPositiveRightGram
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21)
    (hcase :
      rectangularGram P11 = (fun _ _ => 0) \/
        forall a : Fin n, 0 < rectRightGramBasisSingularValue P21 a) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      (Q = fun i j => P21 i j + matMulRect m n n F P11 i j) /\
        GramSchmidtOrthonormalColumns Q /\
        rectOpNorm2Le F 1 := by
  exact
    mgsProblem1912_add_factor_exists_of_csPolarInput_zero_or_fullPositive_rightGram
      hinput hcase

/-- Chapter-facing residual branch after the closed zero/full-positive
CS/polar router fails: the top Gram is nonzero and the lower right-Gram surface
has at least one zero singular value. -/
theorem problem1912_remainingMixedBranch_of_not_zeroOrFullPositiveRightGram
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21)
    (hnot :
      Not (rectangularGram P11 = (fun _ _ => 0) \/
        forall a : Fin n, 0 < rectRightGramBasisSingularValue P21 a)) :
    Ne (rectangularGram P11) (fun _ _ => 0) /\
      Exists fun a : Fin n => rectRightGramBasisSingularValue P21 a = 0 := by
  exact
    MGSProblem1912CSPolarInput.remaining_mixedBranch_of_not_zero_or_fullPositive_rightGram
      hinput hnot

/-- Chapter-labeled conversion from a polar-factor payload to pure Problem
19.12 correction-map data. -/
theorem problem1912_polarFactorData_to_correctionMapData {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hpolar : Problem1912PolarFactorData m n P11 P21) :
    Problem1912CorrectionMapData m n P11 P21 hpolar.q
      (matMulRect m n n hpolar.q hpolar.tMat) := by
  exact
    LeanFpAnalysis.FP.MGSProblem1912PolarFactorData.to_correctionMapData
      hpolar

/-- Chapter-facing additive identity supplied by a polar-factor payload. -/
theorem problem1912_polarFactorData_add_factor_eq {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hpolar : Problem1912PolarFactorData m n P11 P21) :
    hpolar.q =
      fun i j =>
        P21 i j +
          matMulRect m n n (matMulRect m n n hpolar.q hpolar.tMat)
            P11 i j := by
  exact
    LeanFpAnalysis.FP.MGSProblem1912PolarFactorData.add_factor_eq
      hpolar

/-- Existential chapter-facing pure correction-map data from a polar-factor
payload. -/
theorem problem1912_correctionMapData_exists_of_polarFactorData
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hpolar : Problem1912PolarFactorData m n P11 P21) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      Problem1912CorrectionMapData m n P11 P21 Q F := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_correctionMapData_exists_of_polarFactorData
      hpolar

/-- Existential chapter-facing additive Problem 19.12 witnesses from a
polar-factor payload. -/
theorem problem1912_add_factor_exists_of_polarFactorData
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hpolar : Problem1912PolarFactorData m n P11 P21) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      (Q = fun i j => P21 i j + matMulRect m n n F P11 i j) /\
        GramSchmidtOrthonormalColumns Q /\
        rectOpNorm2Le F 1 := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_add_factor_exists_of_polarFactorData
      hpolar

/-- Nonempty polar-factor payloads provide pure Problem 19.12 correction-map
data. -/
theorem problem1912_correctionMapData_exists_of_polarFactorData_nonempty
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hpolar : Nonempty (Problem1912PolarFactorData m n P11 P21)) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      Problem1912CorrectionMapData m n P11 P21 Q F := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_correctionMapData_exists_of_polarFactorData_nonempty
      hpolar

/-- Nonempty polar-factor payloads provide additive Problem 19.12 witnesses. -/
theorem problem1912_add_factor_exists_of_polarFactorData_nonempty
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hpolar : Nonempty (Problem1912PolarFactorData m n P11 P21)) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      (Q = fun i j => P21 i j + matMulRect m n n F P11 i j) /\
        GramSchmidtOrthonormalColumns Q /\
        rectOpNorm2Le F 1 := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_add_factor_exists_of_polarFactorData_nonempty
      hpolar

/-- Chapter-labeled specialization from pure Problem 19.12 correction-map data
to the common-`R` correction-map contract. -/
theorem problem1912_correctionMapData_to_correctionMap {m n : Nat}
    {P11 : Fin n -> Fin n -> Real}
    {P21 Q F : Fin m -> Fin n -> Real}
    (hdata : Problem1912CorrectionMapData m n P11 P21 Q F)
    {dTop R : Fin n -> Fin n -> Real}
    (hdTop : dTop = matMul n P11 R) :
    Problem1912CorrectionMap m n P21 Q dTop R F := by
  exact hdata.to_correctionMap hdTop

/-- Chapter-labeled construction of the Problem 19.12 correction-map contract
from explicit CS-decomposition algebra data. -/
theorem problem1912_correctionMap_of_csAlgebra {m n : Nat}
    {P11 U C S T W : Fin n -> Fin n -> Real}
    {P21 Q V F : Fin m -> Fin n -> Real}
    {dTop R : Fin n -> Fin n -> Real}
    (hdTop : dTop = matMul n P11 R)
    (hP11 : P11 = matMul n U (matMul n C (finiteTranspose W)))
    (hP21 : P21 =
      matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQ : Q = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hU : matMul n (finiteTranspose U) U = idMatrix n)
    (hTC : matMul n T C = fun i j => idMatrix n i j - S i j)
    (hQorth : GramSchmidtOrthonormalColumns Q)
    (hFbound : rectOpNorm2Le F 1) :
    Problem1912CorrectionMap m n P21 Q dTop R F := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_correctionMap_of_csAlgebra hdTop hP11
      hP21 hQ hF hU hTC hQorth hFbound

/-- Chapter-labeled construction of the pure Problem 19.12 correction-map data
from CS algebra plus source orthogonality and diagonal-norm data. -/
theorem problem1912_correctionMapData_of_csOrthogonalAlgebra {m n : Nat}
    {P11 U C S T W : Fin n -> Fin n -> Real}
    {P21 Q V F : Fin m -> Fin n -> Real}
    (hP11 : P11 = matMul n U (matMul n C (finiteTranspose W)))
    (hP21 : P21 =
      matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQ : Q = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hTC : matMul n T C = fun i j => idMatrix n i j - S i j)
    (hTbound : opNorm2Le T 1) :
    Problem1912CorrectionMapData m n P11 P21 Q F := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_correctionMapData_of_csOrthogonalAlgebra
      hP11 hP21 hQ hF hUorth hWorth hVorth hTC hTbound

/-- Chapter-labeled construction of the Problem 19.12 correction-map contract
from CS algebra plus source orthogonality and diagonal-norm data. -/
theorem problem1912_correctionMap_of_csOrthogonalAlgebra {m n : Nat}
    {P11 U C S T W : Fin n -> Fin n -> Real}
    {P21 Q V F : Fin m -> Fin n -> Real}
    {dTop R : Fin n -> Fin n -> Real}
    (hdTop : dTop = matMul n P11 R)
    (hP11 : P11 = matMul n U (matMul n C (finiteTranspose W)))
    (hP21 : P21 =
      matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQ : Q = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hTC : matMul n T C = fun i j => idMatrix n i j - S i j)
    (hTbound : opNorm2Le T 1) :
    Problem1912CorrectionMap m n P21 Q dTop R F := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_correctionMap_of_csOrthogonalAlgebra
      hdTop hP11 hP21 hQ hF hUorth hWorth hVorth hTC hTbound

/-- Chapter-labeled diagonal CS norm estimate used in Problem 19.12:
`diag(c/(1+s))` is a contraction when `c_i^2 + s_i^2 = 1` and `s_i >= 0`. -/
theorem problem1912_opNorm2Le_finiteDiagonal_csHalfTangent {n : Nat}
    (c s : Fin n -> Real)
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1) :
    opNorm2Le (finiteDiagonal (fun i => c i / (1 + s i))) 1 := by
  exact
    LeanFpAnalysis.FP.opNorm2Le_finiteDiagonal_csHalfTangent c s hs hcs

/-- Chapter-labeled diagonal CS sine estimate used in Problem 19.12:
`diag(s)` is a contraction when `c_i^2 + s_i^2 = 1`. -/
theorem problem1912_opNorm2Le_finiteDiagonal_csSine {n : Nat}
    (c s : Fin n -> Real)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1) :
    opNorm2Le (finiteDiagonal s) 1 := by
  exact LeanFpAnalysis.FP.opNorm2Le_finiteDiagonal_csSine c s hcs

/-- Chapter-labeled diagonal CS cosine estimate used in Problem 19.12:
`diag(c)` is a contraction when `c_i^2 + s_i^2 = 1`. -/
theorem problem1912_opNorm2Le_finiteDiagonal_csCosine {n : Nat}
    (c s : Fin n -> Real)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1) :
    opNorm2Le (finiteDiagonal c) 1 := by
  exact LeanFpAnalysis.FP.opNorm2Le_finiteDiagonal_csCosine c s hcs

/-- Chapter-labeled diagonal CS square identity used in Problem 19.12:
`diag(c)^2 + diag(s)^2 = I` when `c_i^2 + s_i^2 = 1`. -/
theorem problem1912_matMul_finiteDiagonal_csSquareSum {n : Nat}
    (c s : Fin n -> Real)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1) :
    (fun i j =>
        matMul n (finiteDiagonal c) (finiteDiagonal c) i j +
          matMul n (finiteDiagonal s) (finiteDiagonal s) i j) =
      idMatrix n := by
  exact LeanFpAnalysis.FP.matMul_finiteDiagonal_csSquareSum c s hcs

/-- Chapter-labeled source-shaped diagonal CS square identity:
`C^2 + S^2 = I` when `C = diag(c)`, `S = diag(s)`, and
`c_i^2 + s_i^2 = 1`. -/
theorem problem1912_csDiagonal_square_sum {n : Nat}
    {C S : Fin n -> Fin n -> Real} {c s : Fin n -> Real}
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1) :
    (fun i j => matMul n C C i j + matMul n S S i j) = idMatrix n := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_csDiagonal_square_sum
      hCdiag hSdiag hcs

/-- Chapter-labeled source-shaped CS block-column Gram identity:
`P11^T P11 + P21^T P21 = I` from diagonal CS factor data. -/
theorem problem1912_csDiagonal_gram_sum_eq_id {m n : Nat}
    {P11 U C S W : Fin n -> Fin n -> Real}
    {P21 V : Fin m -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hP11 : P11 = matMul n U (matMul n C (finiteTranspose W)))
    (hP21 : P21 =
      matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1) :
    (fun i j => rectangularGram P11 i j + rectangularGram P21 i j) =
      idMatrix n := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_csDiagonal_gram_sum_eq_id
      hP11 hP21 hUorth hWorth hVorth hCdiag hSdiag hcs

/-- Chapter-labeled diagonal CS identity for Problem 19.12:
`diag(c/(1+s)) * diag(c) = I - diag(s)`. -/
theorem problem1912_matMul_finiteDiagonal_csHalfTangent {n : Nat}
    (c s : Fin n -> Real)
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1) :
    matMul n (finiteDiagonal (fun i => c i / (1 + s i)))
        (finiteDiagonal c) =
      fun i j => idMatrix n i j - finiteDiagonal s i j := by
  exact
    LeanFpAnalysis.FP.matMul_finiteDiagonal_csHalfTangent c s hs hcs

/-- Chapter-labeled construction of the pure Problem 19.12 correction-map data
from diagonal CS data.  The diagonal scalar identities supply the formerly
separate `T C = I - S` and `||T||_2 <= 1` assumptions. -/
theorem problem1912_correctionMapData_of_csDiagonalAlgebra {m n : Nat}
    {P11 U C S T W : Fin n -> Fin n -> Real}
    {P21 Q V F : Fin m -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hP11 : P11 = matMul n U (matMul n C (finiteTranspose W)))
    (hP21 : P21 =
      matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQ : Q = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1) :
    Problem1912CorrectionMapData m n P11 P21 Q F := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_correctionMapData_of_csDiagonalAlgebra
      hP11 hP21 hQ hF hUorth hWorth hVorth
      hCdiag hSdiag hTdiag hs hcs

/-- Chapter-labeled construction of the Problem 19.12 correction-map contract
from diagonal CS data after choosing the common right factor `R`. -/
theorem problem1912_correctionMap_of_csDiagonalAlgebra {m n : Nat}
    {P11 U C S T W : Fin n -> Fin n -> Real}
    {P21 Q V F : Fin m -> Fin n -> Real}
    {dTop R : Fin n -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hdTop : dTop = matMul n P11 R)
    (hP11 : P11 = matMul n U (matMul n C (finiteTranspose W)))
    (hP21 : P21 =
      matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQ : Q = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1) :
    Problem1912CorrectionMap m n P21 Q dTop R F := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_correctionMap_of_csDiagonalAlgebra
      hdTop hP11 hP21 hQ hF hUorth hWorth hVorth
      hCdiag hSdiag hTdiag hs hcs

/-- Chapter-labeled contraction bound for the top CS block
`P11 = U C W^T` in Problem 19.12. -/
theorem problem1912_p11_opNorm2Le_one_of_csDiagonalAlgebra
    {n : Nat}
    {P11 U C W : Fin n -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hP11 : P11 = matMul n U (matMul n C (finiteTranspose W)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hCdiag : C = finiteDiagonal c)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1) :
    opNorm2Le P11 1 := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_p11_opNorm2Le_one_of_csDiagonalAlgebra
      hP11 hUorth hWorth hCdiag hcs

/-- Chapter-labeled contraction bound for the bottom CS block
`P21 = V S W^T` in Problem 19.12. -/
theorem problem1912_p21_rectOpNorm2Le_one_of_csDiagonalAlgebra
    {m n : Nat}
    {P21 V : Fin m -> Fin n -> Real}
    {S W : Fin n -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hP21 : P21 =
      matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hSdiag : S = finiteDiagonal s)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1) :
    rectOpNorm2Le P21 1 := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_p21_rectOpNorm2Le_one_of_csDiagonalAlgebra
      hP21 hWorth hVorth hSdiag hcs

/-- Chapter-labeled packaging of explicit diagonal CS witnesses into the
source-shaped factor-data payload for Problem 19.12. -/
def problem1912_csDiagonalFactorData_of_csDiagonalAlgebra {m n : Nat}
    {P11 U C S T W : Fin n -> Fin n -> Real}
    {P21 Q V F : Fin m -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hP11 : P11 = matMul n U (matMul n C (finiteTranspose W)))
    (hP21 : P21 =
      matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQ : Q = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1) :
    Problem1912CSDiagonalFactorData m n P11 P21 :=
  LeanFpAnalysis.FP.mgsProblem1912_csDiagonalFactorData_of_csDiagonalAlgebra
    hP11 hP21 hQ hF hUorth hWorth hVorth hCdiag hSdiag hTdiag hs hcs

/-- Existential chapter-facing form of the explicit diagonal CS witness
packaging. -/
theorem problem1912_csDiagonalFactorData_exists_of_csDiagonalAlgebra
    {m n : Nat}
    {P11 U C S T W : Fin n -> Fin n -> Real}
    {P21 Q V F : Fin m -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hP11 : P11 = matMul n U (matMul n C (finiteTranspose W)))
    (hP21 : P21 =
      matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQ : Q = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1) :
    Exists fun hdata : Problem1912CSDiagonalFactorData m n P11 P21 =>
      hdata.q = Q /\ hdata.f = F := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_csDiagonalFactorData_exists_of_csDiagonalAlgebra
      hP11 hP21 hQ hF hUorth hWorth hVorth hCdiag hSdiag hTdiag hs hcs

/-- Chapter-facing existence form of the explicit diagonal CS witness
packaging, without selecting the repaired `Q` and correction map `F`. -/
theorem problem1912_csDiagonalFactorData_nonempty_of_csDiagonalAlgebra
    {m n : Nat}
    {P11 U C S T W : Fin n -> Fin n -> Real}
    {P21 Q V F : Fin m -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hP11 : P11 = matMul n U (matMul n C (finiteTranspose W)))
    (hP21 : P21 =
      matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQ : Q = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1) :
    Nonempty (Problem1912CSDiagonalFactorData m n P11 P21) := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_csDiagonalFactorData_nonempty_of_csDiagonalAlgebra
      hP11 hP21 hQ hF hUorth hWorth hVorth hCdiag hSdiag hTdiag hs hcs

/-- Chapter-labeled conversion from packaged diagonal CS factor data to the
pure Problem 19.12 correction-map data. -/
theorem problem1912_correctionMapData_of_csDiagonalFactorData {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hcs : Problem1912CSDiagonalFactorData m n P11 P21) :
    Problem1912CorrectionMapData m n P11 P21 hcs.q hcs.f := by
  exact
    LeanFpAnalysis.FP.MGSProblem1912CSDiagonalFactorData.to_correctionMapData
      hcs

/-- Chapter-facing additive identity supplied by packaged diagonal CS factor
data: `Q = P21 + F * P11`. -/
theorem problem1912_csDiagonalFactorData_add_factor_eq {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hcs : Problem1912CSDiagonalFactorData m n P11 P21) :
    hcs.q = fun i j => P21 i j + matMulRect m n n hcs.f P11 i j := by
  exact
    LeanFpAnalysis.FP.MGSProblem1912CSDiagonalFactorData.add_factor_eq hcs

/-- Existential chapter-facing form of the packaged diagonal CS bridge. -/
theorem problem1912_correctionMapData_exists_of_csDiagonalFactorData
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hcs : Problem1912CSDiagonalFactorData m n P11 P21) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      Problem1912CorrectionMapData m n P11 P21 Q F := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_correctionMapData_exists_of_csDiagonalFactorData
      hcs

/-- Existential chapter-facing additive-orientation form of packaged diagonal
CS factor data. -/
theorem problem1912_add_factor_exists_of_csDiagonalFactorData
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hcs : Problem1912CSDiagonalFactorData m n P11 P21) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      (Q = fun i j => P21 i j + matMulRect m n n F P11 i j) /\
        GramSchmidtOrthonormalColumns Q /\
        rectOpNorm2Le F 1 := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_add_factor_exists_of_csDiagonalFactorData
      hcs

/-- Chapter-facing conversion from existence of packaged diagonal CS factor
data to existence of pure Problem 19.12 correction-map data. -/
theorem problem1912_correctionMapData_exists_of_csDiagonalFactorData_nonempty
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hcs : Nonempty (Problem1912CSDiagonalFactorData m n P11 P21)) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      Problem1912CorrectionMapData m n P11 P21 Q F := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_correctionMapData_exists_of_csDiagonalFactorData_nonempty
      hcs

/-- Chapter-facing conversion from existence of packaged diagonal CS factor
data to existence of additive Problem 19.12 witnesses. -/
theorem problem1912_add_factor_exists_of_csDiagonalFactorData_nonempty
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hcs : Nonempty (Problem1912CSDiagonalFactorData m n P11 P21)) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      (Q = fun i j => P21 i j + matMulRect m n n F P11 i j) /\
        GramSchmidtOrthonormalColumns Q /\
        rectOpNorm2Le F 1 := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_add_factor_exists_of_csDiagonalFactorData_nonempty
      hcs

/-- Chapter-facing zero-correction branch: if the lower block already has
orthonormal columns, it provides the repaired factor with zero correction. -/
theorem problem1912_correctionMapData_exists_of_bottom_orthonormal
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hP21 : GramSchmidtOrthonormalColumns P21) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      Problem1912CorrectionMapData m n P11 P21 Q F := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_correctionMapData_exists_of_bottom_orthonormal
      hP21

/-- Chapter-facing additive form of the zero-correction branch. -/
theorem problem1912_add_factor_exists_of_bottom_orthonormal {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hP21 : GramSchmidtOrthonormalColumns P21) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      (Q = fun i j => P21 i j + matMulRect m n n F P11 i j) /\
        GramSchmidtOrthonormalColumns Q /\
        rectOpNorm2Le F 1 := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_add_factor_exists_of_bottom_orthonormal
      hP21

/-- Chapter-facing degenerate CS/polar reduction: if the top block is zero,
the corrected CS/polar input makes the lower block orthonormal. -/
theorem problem1912_csPolarInput_bottom_orthonormal_of_top_zero
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21)
    (hP11zero : P11 = fun _ _ => 0) :
    GramSchmidtOrthonormalColumns P21 := by
  exact
    LeanFpAnalysis.FP.MGSProblem1912CSPolarInput.bottom_orthonormal_of_top_zero
      hinput hP11zero

/-- Chapter-facing degenerate CS/polar reduction: if the top Gram matrix is
zero, the corrected CS/polar input makes the lower block orthonormal. -/
theorem problem1912_csPolarInput_bottom_orthonormal_of_top_gram_zero
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21)
    (hP11gram : rectangularGram P11 = fun _ _ => 0) :
    GramSchmidtOrthonormalColumns P21 := by
  exact
    LeanFpAnalysis.FP.MGSProblem1912CSPolarInput.bottom_orthonormal_of_top_gram_zero
      hinput hP11gram

/-- Chapter-facing zero-Gram equivalence for rectangular blocks. -/
theorem problem1912_rectangularGram_eq_zero_iff {m n : Nat}
    (Q : Fin m -> Fin n -> Real) :
    rectangularGram Q = (fun _ _ => 0) <-> Q = fun _ _ => 0 := by
  exact LeanFpAnalysis.FP.rectangularGram_eq_zero_iff Q

/-- Chapter-facing degenerate CS/polar reduction: a zero top Gram matrix means
the top block itself is zero. -/
theorem problem1912_csPolarInput_top_zero_of_top_gram_zero
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21)
    (hP11gram : rectangularGram P11 = fun _ _ => 0) :
    P11 = fun _ _ => 0 := by
  exact
    LeanFpAnalysis.FP.MGSProblem1912CSPolarInput.top_zero_of_top_gram_zero
      hinput hP11gram

/-- Chapter-facing correction-data existence for the zero-top-block CS/polar
branch. -/
theorem problem1912_correctionMapData_exists_of_csPolarInput_top_zero
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21)
    (hP11zero : P11 = fun _ _ => 0) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      Problem1912CorrectionMapData m n P11 P21 Q F := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_correctionMapData_exists_of_csPolarInput_top_zero
      hinput hP11zero

/-- Chapter-facing additive-witness existence for the zero-top-block CS/polar
branch. -/
theorem problem1912_add_factor_exists_of_csPolarInput_top_zero
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21)
    (hP11zero : P11 = fun _ _ => 0) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      (Q = fun i j => P21 i j + matMulRect m n n F P11 i j) /\
        GramSchmidtOrthonormalColumns Q /\
        rectOpNorm2Le F 1 := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_add_factor_exists_of_csPolarInput_top_zero
      hinput hP11zero

/-- Chapter-facing correction-data existence for the zero-top-Gram CS/polar
branch. -/
theorem problem1912_correctionMapData_exists_of_csPolarInput_top_gram_zero
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21)
    (hP11gram : rectangularGram P11 = fun _ _ => 0) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      Problem1912CorrectionMapData m n P11 P21 Q F := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_correctionMapData_exists_of_csPolarInput_top_gram_zero
      hinput hP11gram

/-- Chapter-facing additive-witness existence for the zero-top-Gram CS/polar
branch. -/
theorem problem1912_add_factor_exists_of_csPolarInput_top_gram_zero
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21)
    (hP11gram : rectangularGram P11 = fun _ _ => 0) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      (Q = fun i j => P21 i j + matMulRect m n n F P11 i j) /\
        GramSchmidtOrthonormalColumns Q /\
        rectOpNorm2Le F 1 := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_add_factor_exists_of_csPolarInput_top_gram_zero
      hinput hP11gram

/-- Chapter-facing sanity check for the remaining CS/polar target: the
block-column Gram identity alone is not a dimension-free source of additive
Problem 19.12 witnesses.  The final existence theorem must retain the source
tall/full-column-rank side condition. -/
theorem problem1912_add_factor_gram_sum_not_dimension_free :
    let P11 : Fin 1 -> Fin 1 -> Real := idMatrix 1
    let P21 : Fin 0 -> Fin 1 -> Real := fun i => Fin.elim0 i
    (fun i j => rectangularGram P11 i j + rectangularGram P21 i j) =
        idMatrix 1 /\
      Not (Exists fun Q : Fin 0 -> Fin 1 -> Real =>
        Exists fun F : Fin 0 -> Fin 1 -> Real =>
          (Q = fun i j => P21 i j + matMulRect 0 1 1 F P11 i j) /\
            GramSchmidtOrthonormalColumns Q /\
            rectOpNorm2Le F 1) := by
  exact LeanFpAnalysis.FP.mgsProblem1912_add_factor_gram_sum_not_dimension_free

/-- Chapter-facing Gram identity consequence of packaged diagonal CS data. -/
theorem problem1912_csDiagonalFactorData_gram_sum_eq_id {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hcs : Problem1912CSDiagonalFactorData m n P11 P21) :
    (fun i j => rectangularGram P11 i j + rectangularGram P21 i j) =
      idMatrix n := by
  exact
    LeanFpAnalysis.FP.MGSProblem1912CSDiagonalFactorData.gram_sum_eq_id hcs

/-- Chapter-facing bridge from supplied diagonal CS factor data to the corrected
CS/polar input, with the source tallness hypothesis explicit. -/
theorem problem1912_csPolarInput_of_csDiagonalFactorData {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hnm : n <= m)
    (hcs : Problem1912CSDiagonalFactorData m n P11 P21) :
    Problem1912CSPolarInput m n P11 P21 := by
  exact
    LeanFpAnalysis.FP.MGSProblem1912CSPolarInput.of_csDiagonalFactorData
      hnm hcs

/-- Chapter-facing top-block contraction consequence of the corrected
CS/polar input. -/
theorem problem1912_csPolarInput_p11_opNorm2Le_one {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21) :
    opNorm2Le P11 1 := by
  exact
    LeanFpAnalysis.FP.MGSProblem1912CSPolarInput.p11_opNorm2Le_one
      hinput

/-- Chapter-facing bottom-block contraction consequence of the corrected
CS/polar input. -/
theorem problem1912_csPolarInput_p21_rectOpNorm2Le_one {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21) :
    rectOpNorm2Le P21 1 := by
  exact
    LeanFpAnalysis.FP.MGSProblem1912CSPolarInput.p21_rectOpNorm2Le_one
      hinput

/-- Chapter-facing bottom-block Gram complement consequence of the corrected
CS/polar input. -/
theorem problem1912_csPolarInput_p21_gram_eq_id_sub_p11_gram {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21) :
    rectangularGram P21 =
      fun i j => idMatrix n i j - rectangularGram P11 i j := by
  exact
    LeanFpAnalysis.FP.MGSProblem1912CSPolarInput.p21_gram_eq_id_sub_p11_gram
      hinput

/-- Chapter-facing top-block Gram complement consequence of the corrected
CS/polar input. -/
theorem problem1912_csPolarInput_p11_gram_eq_id_sub_p21_gram {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21) :
    rectangularGram P11 =
      fun i j => idMatrix n i j - rectangularGram P21 i j := by
  exact
    LeanFpAnalysis.FP.MGSProblem1912CSPolarInput.p11_gram_eq_id_sub_p21_gram
      hinput

/-- Chapter-facing top-block Gram symmetry consequence of the corrected
CS/polar input. -/
theorem problem1912_csPolarInput_p11_gram_symmetric {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21) :
    forall i j : Fin n, rectangularGram P11 i j = rectangularGram P11 j i := by
  exact
    LeanFpAnalysis.FP.MGSProblem1912CSPolarInput.p11_gram_symmetric
      hinput

/-- Chapter-facing bottom-block Gram symmetry consequence of the corrected
CS/polar input. -/
theorem problem1912_csPolarInput_p21_gram_symmetric {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21) :
    forall i j : Fin n, rectangularGram P21 i j = rectangularGram P21 j i := by
  exact
    LeanFpAnalysis.FP.MGSProblem1912CSPolarInput.p21_gram_symmetric
      hinput

/-- Chapter-facing Gram commutation consequence of the corrected CS/polar
input. -/
theorem problem1912_csPolarInput_grams_commute {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : Problem1912CSPolarInput m n P11 P21) :
    matMul n (rectangularGram P11) (rectangularGram P21) =
      matMul n (rectangularGram P21) (rectangularGram P11) := by
  exact
    LeanFpAnalysis.FP.MGSProblem1912CSPolarInput.grams_commute
      hinput

/-- Chapter-facing top-block contraction consequence of packaged diagonal CS
data. -/
theorem problem1912_csDiagonalFactorData_p11_opNorm2Le_one {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hcs : Problem1912CSDiagonalFactorData m n P11 P21) :
    opNorm2Le P11 1 := by
  exact
    LeanFpAnalysis.FP.MGSProblem1912CSDiagonalFactorData.p11_opNorm2Le_one
      hcs

/-- Chapter-facing bottom-block contraction consequence of packaged diagonal CS
data. -/
theorem problem1912_csDiagonalFactorData_p21_rectOpNorm2Le_one {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hcs : Problem1912CSDiagonalFactorData m n P11 P21) :
    rectOpNorm2Le P21 1 := by
  exact
    LeanFpAnalysis.FP.MGSProblem1912CSDiagonalFactorData.p21_rectOpNorm2Le_one
      hcs

/-- Chapter-labeled column bound for a right product by a correction map. -/
theorem problem1912_columnFrob_matMulRect_le_rectOpNorm2_mul_columnFrob
    {m n p : Nat}
    (F : Fin m -> Fin n -> Real) (B : Fin n -> Fin p -> Real)
    {cF : Real} (hF : rectOpNorm2Le F cF) (j : Fin p) :
    columnFrob (matMulRect m n p F B) j <= cF * columnFrob B j := by
  exact
    LeanFpAnalysis.FP.columnFrob_matMulRect_le_rectOpNorm2_mul_columnFrob
      F B hF j

/-- Chapter-labeled operator budget for the repaired Problem 19.12
perturbation `F * DeltaA_top + DeltaA_bottom`. -/
theorem problem1912_repairedPerturbation_rectOpNorm2Le_of_bounds
    {m n : Nat}
    {F dBottom : Fin m -> Fin n -> Real} {dTop : Fin n -> Fin n -> Real}
    {cF etaTop etaBottom : Real}
    (hcF : 0 <= cF)
    (hF : rectOpNorm2Le F cF)
    (hTop : rectOpNorm2Le dTop etaTop)
    (hBottom : rectOpNorm2Le dBottom etaBottom) :
    rectOpNorm2Le
      (fun i j => matMulRect m n n F dTop i j + dBottom i j)
      (cF * etaTop + etaBottom) := by
  exact
    LeanFpAnalysis.FP.mgsRepairedPerturbation_rectOpNorm2Le_of_bounds
      hcF hF hTop hBottom

/-- Chapter-labeled columnwise budget for the repaired Problem 19.12
perturbation `F * DeltaA_top + DeltaA_bottom`. -/
theorem problem1912_repairedPerturbation_columnFrob_le_of_column_budget
    {m n : Nat}
    {A F dBottom : Fin m -> Fin n -> Real}
    {dTop : Fin n -> Fin n -> Real}
    {topBudget bottomBudget : Fin n -> Real} {cF c3 u : Real}
    (hcF : 0 <= cF)
    (hF : rectOpNorm2Le F cF)
    (hTopCol : forall j, columnFrob dTop j <= topBudget j)
    (hBottomCol : forall j, columnFrob dBottom j <= bottomBudget j)
    (hBudget :
      forall j, cF * topBudget j + bottomBudget j <=
        c3 * u * columnFrob A j) :
    forall j,
      columnFrob
          (fun i j => matMulRect m n n F dTop i j + dBottom i j) j <=
        c3 * u * columnFrob A j := by
  exact
    LeanFpAnalysis.FP.mgsRepairedPerturbation_columnFrob_le_of_column_budget
      (A := A) (F := F) (dBottom := dBottom) (dTop := dTop)
      hcF hF hTopCol hBottomCol hBudget

/-- Chapter-labeled wrapper around the algebraic repair step from Problem
19.12.  The CS/polar construction must still provide the correction map and
its norm/columnwise budgets. -/
theorem problem1912_repair_of_correctionMap {m n : Nat}
    {A P21 Q : Fin m -> Fin n -> Real}
    {dTop R : Fin n -> Fin n -> Real}
    {dBottom F : Fin m -> Fin n -> Real}
    {eta2 c3 u : Real}
    (hbottom :
      (fun i j => A i j + dBottom i j) =
        matMulRect m n n P21 R)
    (hmap : Problem1912CorrectionMap m n P21 Q dTop R F)
    (hnorm :
      rectOpNorm2Le
        (fun i j => matMulRect m n n F dTop i j + dBottom i j)
        eta2)
    (hcol :
      forall j,
        columnFrob
            (fun i j => matMulRect m n n F dTop i j + dBottom i j)
            j <=
          c3 * u * columnFrob A j) :
    Exists fun Qrepair : Fin m -> Fin n -> Real =>
    Exists fun dA2 : Fin m -> Fin n -> Real =>
      GramSchmidtOrthonormalColumns Qrepair /\
      (fun i j => A i j + dA2 i j) =
        matMulRect m n n Qrepair R /\
      rectOpNorm2Le dA2 eta2 /\
      (forall j, columnFrob dA2 j <= c3 * u * columnFrob A j) := by
  exact mgsProblem1912_repair_of_correctionMap hbottom hmap hnorm hcol

/-- Chapter-labeled Problem 19.12 repair with the repaired-perturbation budgets
derived from separate top and bottom perturbation budgets. -/
theorem problem1912_repair_of_correctionMap_of_perturbation_bounds
    {m n : Nat}
    {A P21 Q : Fin m -> Fin n -> Real}
    {dTop R : Fin n -> Fin n -> Real}
    {dBottom F : Fin m -> Fin n -> Real}
    {etaTop etaBottom eta2 c3 u : Real}
    {topBudget bottomBudget : Fin n -> Real}
    (hbottom :
      (fun i j => A i j + dBottom i j) =
        matMulRect m n n P21 R)
    (hmap : Problem1912CorrectionMap m n P21 Q dTop R F)
    (hTop : rectOpNorm2Le dTop etaTop)
    (hBottom : rectOpNorm2Le dBottom etaBottom)
    (hNormBudget : 1 * etaTop + etaBottom <= eta2)
    (hTopCol : forall j, columnFrob dTop j <= topBudget j)
    (hBottomCol : forall j, columnFrob dBottom j <= bottomBudget j)
    (hColBudget :
      forall j, 1 * topBudget j + bottomBudget j <=
        c3 * u * columnFrob A j) :
    Exists fun Qrepair : Fin m -> Fin n -> Real =>
    Exists fun dA2 : Fin m -> Fin n -> Real =>
      GramSchmidtOrthonormalColumns Qrepair /\
      (fun i j => A i j + dA2 i j) =
        matMulRect m n n Qrepair R /\
      rectOpNorm2Le dA2 eta2 /\
      (forall j, columnFrob dA2 j <= c3 * u * columnFrob A j) := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_repair_of_correctionMap_of_perturbation_bounds
      hbottom hmap hTop hBottom hNormBudget
      hTopCol hBottomCol hColBudget

/-- Chapter-labeled Problem 19.12 repair from the pure correction-map data
interface.

This is the wrapper future CS/polar existence work should target first: after
the top-block equation introduces the common `R`, the pure data specializes to
the older correction-map repair contract. -/
theorem problem1912_repair_of_correctionMapData {m n : Nat}
    {A P21 Q F dBottom : Fin m -> Fin n -> Real}
    {P11 dTop R : Fin n -> Fin n -> Real}
    {eta2 c3 u : Real}
    (hbottom :
      (fun i j => A i j + dBottom i j) =
        matMulRect m n n P21 R)
    (hdTop : dTop = matMul n P11 R)
    (hdata : Problem1912CorrectionMapData m n P11 P21 Q F)
    (hnorm :
      rectOpNorm2Le
        (fun i j => matMulRect m n n F dTop i j + dBottom i j)
        eta2)
    (hcol :
      forall j,
        columnFrob
            (fun i j => matMulRect m n n F dTop i j + dBottom i j)
            j <=
          c3 * u * columnFrob A j) :
    Exists fun Qrepair : Fin m -> Fin n -> Real =>
    Exists fun dA2 : Fin m -> Fin n -> Real =>
      GramSchmidtOrthonormalColumns Qrepair /\
      (fun i j => A i j + dA2 i j) =
        matMulRect m n n Qrepair R /\
      rectOpNorm2Le dA2 eta2 /\
      (forall j, columnFrob dA2 j <= c3 * u * columnFrob A j) := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_repair_of_correctionMapData
      hbottom hdTop hdata hnorm hcol

/-- Chapter-labeled Problem 19.12 repair from pure correction-map data, with
the repaired perturbation budgets derived from separate top and bottom
perturbation budgets. -/
theorem problem1912_repair_of_correctionMapData_of_perturbation_bounds
    {m n : Nat}
    {A P21 Q F dBottom : Fin m -> Fin n -> Real}
    {P11 dTop R : Fin n -> Fin n -> Real}
    {etaTop etaBottom eta2 c3 u : Real}
    {topBudget bottomBudget : Fin n -> Real}
    (hbottom :
      (fun i j => A i j + dBottom i j) =
        matMulRect m n n P21 R)
    (hdTop : dTop = matMul n P11 R)
    (hdata : Problem1912CorrectionMapData m n P11 P21 Q F)
    (hTop : rectOpNorm2Le dTop etaTop)
    (hBottom : rectOpNorm2Le dBottom etaBottom)
    (hNormBudget : 1 * etaTop + etaBottom <= eta2)
    (hTopCol : forall j, columnFrob dTop j <= topBudget j)
    (hBottomCol : forall j, columnFrob dBottom j <= bottomBudget j)
    (hColBudget :
      forall j, 1 * topBudget j + bottomBudget j <=
        c3 * u * columnFrob A j) :
    Exists fun Qrepair : Fin m -> Fin n -> Real =>
    Exists fun dA2 : Fin m -> Fin n -> Real =>
      GramSchmidtOrthonormalColumns Qrepair /\
      (fun i j => A i j + dA2 i j) =
        matMulRect m n n Qrepair R /\
      rectOpNorm2Le dA2 eta2 /\
      (forall j, columnFrob dA2 j <= c3 * u * columnFrob A j) := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_repair_of_correctionMapData_of_perturbation_bounds
      hbottom hdTop hdata hTop hBottom hNormBudget
      hTopCol hBottomCol hColBudget

/-- Chapter-labeled diagonal-CS repair theorem for Problem 19.12.

This composes the diagonal-CS correction-map constructor with the downstream
repair algebra, leaving only the source CS/polar existence data and
repaired-perturbation budgets as inputs. -/
theorem problem1912_repair_of_csDiagonalAlgebra {m n : Nat}
    {A P21 Q V F dBottom : Fin m -> Fin n -> Real}
    {P11 U C S T W dTop R : Fin n -> Fin n -> Real}
    {c s : Fin n -> Real}
    {eta2 c3 u : Real}
    (hbottom :
      (fun i j => A i j + dBottom i j) =
        matMulRect m n n P21 R)
    (hdTop : dTop = matMul n P11 R)
    (hP11 : P11 = matMul n U (matMul n C (finiteTranspose W)))
    (hP21 : P21 =
      matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQ : Q = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1)
    (hnorm :
      rectOpNorm2Le
        (fun i j => matMulRect m n n F dTop i j + dBottom i j)
        eta2)
    (hcol :
      forall j,
        columnFrob
            (fun i j => matMulRect m n n F dTop i j + dBottom i j)
            j <=
          c3 * u * columnFrob A j) :
    Exists fun Qrepair : Fin m -> Fin n -> Real =>
    Exists fun dA2 : Fin m -> Fin n -> Real =>
      GramSchmidtOrthonormalColumns Qrepair /\
      (fun i j => A i j + dA2 i j) =
        matMulRect m n n Qrepair R /\
      rectOpNorm2Le dA2 eta2 /\
      (forall j, columnFrob dA2 j <= c3 * u * columnFrob A j) := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_repair_of_csDiagonalAlgebra
      hbottom hdTop hP11 hP21 hQ hF hUorth hWorth hVorth
      hCdiag hSdiag hTdiag hs hcs hnorm hcol

/-- Chapter-labeled diagonal-CS Problem 19.12 repair with the
repaired-perturbation budgets derived from separate top and bottom perturbation
budgets. -/
theorem problem1912_repair_of_csDiagonalAlgebra_of_perturbation_bounds
    {m n : Nat}
    {A P21 Q V F dBottom : Fin m -> Fin n -> Real}
    {P11 U C S T W dTop R : Fin n -> Fin n -> Real}
    {c s : Fin n -> Real}
    {etaTop etaBottom eta2 c3 u : Real}
    {topBudget bottomBudget : Fin n -> Real}
    (hbottom :
      (fun i j => A i j + dBottom i j) =
        matMulRect m n n P21 R)
    (hdTop : dTop = matMul n P11 R)
    (hP11 : P11 = matMul n U (matMul n C (finiteTranspose W)))
    (hP21 : P21 =
      matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQ : Q = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1)
    (hTop : rectOpNorm2Le dTop etaTop)
    (hBottom : rectOpNorm2Le dBottom etaBottom)
    (hNormBudget : 1 * etaTop + etaBottom <= eta2)
    (hTopCol : forall j, columnFrob dTop j <= topBudget j)
    (hBottomCol : forall j, columnFrob dBottom j <= bottomBudget j)
    (hColBudget :
      forall j, 1 * topBudget j + bottomBudget j <=
        c3 * u * columnFrob A j) :
    Exists fun Qrepair : Fin m -> Fin n -> Real =>
    Exists fun dA2 : Fin m -> Fin n -> Real =>
      GramSchmidtOrthonormalColumns Qrepair /\
      (fun i j => A i j + dA2 i j) =
        matMulRect m n n Qrepair R /\
      rectOpNorm2Le dA2 eta2 /\
      (forall j, columnFrob dA2 j <= c3 * u * columnFrob A j) := by
  exact
    LeanFpAnalysis.FP.mgsProblem1912_repair_of_csDiagonalAlgebra_of_perturbation_bounds
      hbottom hdTop hP11 hP21 hQ hF hUorth hWorth hVorth
      hCdiag hSdiag hTdiag hs hcs hTop hBottom hNormBudget
      hTopCol hBottomCol hColBudget

/-- Convert source-labeled QR-sensitivity outputs into the compact bridge used
by the Theorem 19.13 assembly lemmas. -/
theorem qrsensitivityBridge_of_source_output {m n : Nat}
    {A Qhat : Fin m -> Fin n -> Real} {Rhat : Fin n -> Fin n -> Real}
    {c2 c3 u kappaA higherOrder : Real}
    (hsource :
      QRSensitivitySourceOutput m n A Qhat Rhat c2 c3 u kappaA
        higherOrder) :
    QRSensitivityBridge m n A Qhat Rhat c2 c3 u kappaA higherOrder := by
  exact ModifiedGramSchmidtQRSensitivityBridge.of_source_output hsource

/-- Build the source-labeled QR-sensitivity output from the common-`R` norm
route, once the source repair step has produced an orthonormal witness,
perturbation bounds, and a bounded right inverse for the common `Rhat`. -/
theorem qrsensitivitySourceOutput_of_commonR_bounds {m n : Nat}
    {A Qhat Q dA1 dA2 : Fin m -> Fin n -> Real}
    {Rhat Rinv : Fin n -> Fin n -> Real}
    {eta1 eta2 rho c2 c3 u kappaA higherOrder : Real}
    (hhat :
      (fun i j => A i j + dA1 i j) =
        matMulRect m n n Qhat Rhat)
    (hQfact :
      (fun i j => A i j + dA2 i j) =
        matMulRect m n n Q Rhat)
    (hQorth : GramSchmidtOrthonormalColumns Q)
    (hRright : matMul n Rhat Rinv = idMatrix n)
    (hdA1 : rectOpNorm2Le dA1 eta1)
    (hdA2 : rectOpNorm2Le dA2 eta2)
    (hRinv : rectOpNorm2Le Rinv rho)
    (heta : 0 <= eta1 + eta2)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + eta2) * rho) + ((eta1 + eta2) * rho) ^ 2 <=
        c2 * u * kappaA + higherOrder)
    (hcol : forall j, columnFrob dA2 j <= c3 * u * columnFrob A j) :
    QRSensitivitySourceOutput m n A Qhat Rhat c2 c3 u kappaA
      higherOrder := by
  exact
    LeanFpAnalysis.FP.ModifiedGramSchmidtQRSensitivitySourceOutput.of_commonR_bounds
      hhat hQfact hQorth hRright hdA1 hdA2 hRinv heta hrho hbudget hcol

/-- Assemble the Theorem 19.13 contract from an economy-product residual,
an upper-triangular economy `R`, and the separate QR-sensitivity outputs. -/
theorem mgs_qr_bounds_of_economy_product_sensitivity {m n : Nat}
    {A Qhat : Fin m -> Fin n -> Real} {Rhat : Fin n -> Fin n -> Real}
    {dA1 : Fin m -> Fin n -> Real}
    {c1 c2 c3 u normA kappaA higherOrder : Real}
    (hupper : IsUpperTrapezoidal n n Rhat)
    (hprod : (fun i j => A i j + dA1 i j) =
      matMulRect m n n Qhat Rhat)
    (hresidual : rectOpNorm2Le dA1 (c1 * u * normA))
    (hsens :
      QRSensitivityBridge m n A Qhat Rhat c2 c3 u kappaA higherOrder) :
    MGSQRBounds m n A Qhat Rhat c1 c2 c3 u normA kappaA higherOrder := by
  exact ModifiedGramSchmidtBackwardError.of_economy_product_sensitivity
    hupper hprod hresidual hsens

/-- Orthogonality residual `Qhat^T Qhat - I` from Theorem 19.13. -/
abbrev orthogonalityResidual {m n : Nat}
    (Qhat : Fin m -> Fin n -> Real) : Fin n -> Fin n -> Real :=
  gramSchmidtOrthogonalityResidual Qhat

/-- Padded matrix `[0; A]` in the Householder-MGS connection. -/
abbrev paddedInput {m n : Nat} (A : Fin m -> Fin n -> Real) :
    Sum (Fin n) (Fin m) -> Fin n -> Real :=
  mgsPaddedInput A

/-- Padded stage matrix for the Householder-MGS connection. -/
abbrev paddedStage {m n : Nat} (A : Fin m -> Fin n -> Real) (t : Nat) :
    Sum (Fin n) (Fin m) -> Fin n -> Real :=
  mgsPaddedStage A t

/-- Final padded block `[R; 0]` for the exact Householder-MGS bridge. -/
abbrev paddedRBlock {m n : Nat} (A : Fin m -> Fin n -> Real) :
    Sum (Fin n) (Fin m) -> Fin n -> Real :=
  mgsPaddedRBlock A

/-- Top `n x n` block of a padded Householder-MGS matrix. -/
abbrev paddedTopBlock {m n : Nat}
    (B : Sum (Fin n) (Fin m) -> Fin n -> Real) :
    Fin n -> Fin n -> Real :=
  mgsPaddedTopBlock B

/-- Bottom `m x n` block of a padded Householder-MGS matrix. -/
abbrev paddedBottomBlock {m n : Nat}
    (B : Sum (Fin n) (Fin m) -> Fin n -> Real) :
    Fin m -> Fin n -> Real :=
  mgsPaddedBottomBlock B

/-- Reassemble a padded Householder-MGS matrix from explicit top and bottom
blocks. -/
abbrev stackedBlocks {m n : Nat}
    (Top : Fin n -> Fin n -> Real) (Bottom : Fin m -> Fin n -> Real) :
    Sum (Fin n) (Fin m) -> Fin n -> Real :=
  mgsStackedBlocks Top Bottom

/-- Padded input with explicit top and bottom perturbation blocks.  This is
the source shape `[Delta A3; A + Delta A4]` in `(19.34)`. -/
abbrev paddedPerturbedInput {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real) :
    Sum (Fin n) (Fin m) -> Fin n -> Real :=
  mgsPaddedPerturbedInput A dTop dBottom

/-- Top perturbation block extracted from a padded matrix relative to
`[0; A]`. -/
abbrev paddedTopPerturbation {m n : Nat}
    (B : Sum (Fin n) (Fin m) -> Fin n -> Real) :
    Fin n -> Fin n -> Real :=
  mgsPaddedTopPerturbation B

/-- Bottom perturbation block extracted from a padded matrix relative to
`[0; A]`. -/
abbrev paddedBottomPerturbation {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (B : Sum (Fin n) (Fin m) -> Fin n -> Real) :
    Fin m -> Fin n -> Real :=
  mgsPaddedBottomPerturbation A B

/-- Row index map from the sum-indexed padded matrix shape to `Fin (n + m)`.
-/
abbrev paddedRowToFin {m n : Nat} :
    Sum (Fin n) (Fin m) -> Fin (n + m) :=
  mgsPaddedRowToFin

/-- Read a `Fin (n + m)` padded row as either a top or bottom row. -/
abbrev paddedRowFromFin {m n : Nat}
    (r : Fin (n + m)) : Sum (Fin n) (Fin m) :=
  mgsPaddedRowFromFin r

/-- Convert a sum-indexed padded matrix into the `Fin (n + m)` row shape used
by the generic Householder QR theorem. -/
abbrev paddedRowsToFin {m n : Nat}
    (B : Sum (Fin n) (Fin m) -> Fin n -> Real) :
    Fin (n + m) -> Fin n -> Real :=
  mgsPaddedRowsToFin B

/-- Convert a `Fin (n + m)` row-indexed padded matrix back to the explicit
top/bottom sum-indexed shape. -/
abbrev paddedRowsFromFin {m n : Nat}
    (C : Fin (n + m) -> Fin n -> Real) :
    Sum (Fin n) (Fin m) -> Fin n -> Real :=
  mgsPaddedRowsFromFin C

/-- The matrix `[0; A]` in the row shape expected by the generic Householder
QR theorem. -/
abbrev paddedFinInput {m n : Nat} (A : Fin m -> Fin n -> Real) :
    Fin (n + m) -> Fin n -> Real :=
  mgsPaddedFinInput A

/-- Equivalence between explicit top/bottom padded rows and the contiguous
`Fin (n + m)` row indexing used by generic QR theorems. -/
abbrev paddedRowEquivFin {m n : Nat} :
    Equiv (Sum (Fin n) (Fin m)) (Fin (n + m)) :=
  mgsPaddedRowEquivFin

/-- Euclidean norm of one column of a sum-indexed padded matrix. -/
noncomputable abbrev paddedColumnNorm {m n : Nat}
    (B : Sum (Fin n) (Fin m) -> Fin n -> Real) (j : Fin n) : Real :=
  mgsPaddedColumnNorm B j

/-- Column norm of the stacked perturbation `[Delta A3; Delta A4]` appearing
in `(19.34)`. -/
noncomputable abbrev stackedPerturbationColumnNorm {m n : Nat}
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real)
    (j : Fin n) : Real :=
  mgsStackedPerturbationColumnNorm dTop dBottom j

/-- Columnwise perturbation-bound shape for the stacked perturbation
`[Delta A3; Delta A4]` in `(19.34)`. -/
abbrev stackedPerturbationColumnwiseBound {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real)
    (c : Real) : Prop :=
  mgsStackedPerturbationColumnwiseBound A dTop dBottom c

/-- Top block vector `-e_k` in the Householder-MGS connection. -/
abbrev householderTop {n : Nat} (k : Fin n) : Fin n -> Real :=
  mgsHouseholderTop k

/-- Source vector `[-e_k; q_k]` from equation `(19.28)`. -/
abbrev householderVector {m n : Nat} (q : Fin m -> Real) (k : Fin n) :
    Sum (Fin n) (Fin m) -> Real :=
  mgsHouseholderVector q k

/-- Source reflector `P_k = I - v_k v_k^T` from equation `(19.28)`. -/
abbrev householderReflector {m n : Nat} (q : Fin m -> Real) (k : Fin n) :
    Sum (Fin n) (Fin m) -> Sum (Fin n) (Fin m) -> Real :=
  mgsHouseholderReflector q k

/-- Column scalar `v_k^T b_j` for the Householder-MGS bridge. -/
abbrev householderColumnInner {m n : Nat}
    (q : Fin m -> Real) (k : Fin n)
    (B : Sum (Fin n) (Fin m) -> Fin n -> Real) (j : Fin n) : Real :=
  mgsHouseholderColumnInner q k B j

/-- Columnwise application of the source reflector `P_k` to a padded matrix. -/
abbrev householderApply {m n : Nat}
    (q : Fin m -> Real) (k : Fin n)
    (B : Sum (Fin n) (Fin m) -> Fin n -> Real) :
    Sum (Fin n) (Fin m) -> Fin n -> Real :=
  mgsHouseholderApply q k B

/-- Prefix application of the exact source reflectors used in the
Householder-MGS connection. -/
abbrev householderApplyPrefix {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    Nat -> (Sum (Fin n) (Fin m) -> Fin n -> Real) ->
      Sum (Fin n) (Fin m) -> Fin n -> Real :=
  mgsHouseholderApplyPrefix A

/-- Reverse-prefix application of the exact source reflectors used in the
printed Householder-MGS orientation. -/
abbrev householderApplyReversePrefix {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    Nat -> (Sum (Fin n) (Fin m) -> Fin n -> Real) ->
      Sum (Fin n) (Fin m) -> Fin n -> Real :=
  mgsHouseholderApplyReversePrefix A

/-- Processed top rows of the padded stage contain exact MGS `R` rows. -/
theorem paddedStage_top_of_lt {m n : Nat}
    (A : Fin m -> Fin n -> Real) {t : Nat} {i : Fin n}
    (hit : i.val < t) (j : Fin n) :
    paddedStage A t (Sum.inl i) j = Algorithm19_12.computedR A i j := by
  exact mgsPaddedStage_top_of_lt A hit j

/-- Unprocessed top rows of the padded stage are zero. -/
theorem paddedStage_top_of_not_lt {m n : Nat}
    (A : Fin m -> Fin n -> Real) {t : Nat} {i : Fin n}
    (hit : Not (i.val < t)) (j : Fin n) :
    paddedStage A t (Sum.inl i) j = 0 := by
  exact mgsPaddedStage_top_of_not_lt A hit j

/-- Processed bottom columns of the padded stage are zero. -/
theorem paddedStage_bottom_of_lt {m n : Nat}
    (A : Fin m -> Fin n -> Real) {t : Nat} (i : Fin m)
    {j : Fin n} (hjt : j.val < t) :
    paddedStage A t (Sum.inr i) j = 0 := by
  exact mgsPaddedStage_bottom_of_lt A i hjt

/-- Active bottom columns of the padded stage are exact MGS stage vectors. -/
theorem paddedStage_bottom_of_not_lt {m n : Nat}
    (A : Fin m -> Fin n -> Real) {t : Nat} (i : Fin m)
    {j : Fin n} (hjt : Not (j.val < t)) :
    paddedStage A t (Sum.inr i) j =
      Algorithm19_12.stageVectors A t j i := by
  exact mgsPaddedStage_bottom_of_not_lt A i hjt

/-- The zeroth padded stage is the source matrix `[0; A]`. -/
theorem paddedStage_zero {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    paddedStage A 0 = paddedInput A := by
  exact mgsPaddedStage_zero A

/-- The final padded stage is the exact block `[R; 0]`. -/
theorem paddedStage_final {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    paddedStage A n = paddedRBlock A := by
  exact mgsPaddedStage_final A

theorem paddedTopBlock_paddedInput {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    paddedTopBlock (paddedInput A) =
      (fun _ _ => 0 : Fin n -> Fin n -> Real) := by
  exact mgsPaddedTopBlock_paddedInput A

theorem paddedBottomBlock_paddedInput {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    paddedBottomBlock (paddedInput A) = A := by
  exact mgsPaddedBottomBlock_paddedInput A

theorem paddedTopBlock_paddedRBlock {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    paddedTopBlock (paddedRBlock A) =
      Algorithm19_12.computedR A := by
  exact mgsPaddedTopBlock_paddedRBlock A

theorem paddedBottomBlock_paddedRBlock {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    paddedBottomBlock (paddedRBlock A) =
      (fun _ _ => 0 : Fin m -> Fin n -> Real) := by
  exact mgsPaddedBottomBlock_paddedRBlock A

theorem paddedTopBlock_stackedBlocks {m n : Nat}
    (Top : Fin n -> Fin n -> Real) (Bottom : Fin m -> Fin n -> Real) :
    paddedTopBlock (stackedBlocks Top Bottom) = Top := by
  exact mgsPaddedTopBlock_stackedBlocks Top Bottom

theorem paddedBottomBlock_stackedBlocks {m n : Nat}
    (Top : Fin n -> Fin n -> Real) (Bottom : Fin m -> Fin n -> Real) :
    paddedBottomBlock (stackedBlocks Top Bottom) = Bottom := by
  exact mgsPaddedBottomBlock_stackedBlocks Top Bottom

theorem paddedTopBlock_perturbedInput {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real) :
    paddedTopBlock (paddedPerturbedInput A dTop dBottom) =
      dTop := by
  exact mgsPaddedTopBlock_perturbedInput A dTop dBottom

theorem paddedBottomBlock_perturbedInput {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real) :
    paddedBottomBlock (paddedPerturbedInput A dTop dBottom) =
      (fun i j => A i j + dBottom i j) := by
  exact mgsPaddedBottomBlock_perturbedInput A dTop dBottom

theorem paddedTopPerturbation_perturbedInput {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real) :
    paddedTopPerturbation (paddedPerturbedInput A dTop dBottom) =
      dTop := by
  exact mgsPaddedTopPerturbation_perturbedInput A dTop dBottom

theorem paddedBottomPerturbation_perturbedInput {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real) :
    paddedBottomPerturbation A (paddedPerturbedInput A dTop dBottom) =
      dBottom := by
  exact mgsPaddedBottomPerturbation_perturbedInput A dTop dBottom

theorem paddedPerturbedInput_eta {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (B : Sum (Fin n) (Fin m) -> Fin n -> Real) :
    paddedPerturbedInput A
        (paddedTopPerturbation B)
        (paddedBottomPerturbation A B) =
      B := by
  exact mgsPaddedPerturbedInput_eta A B

@[simp] theorem paddedRowFromFin_toFin_inl {m n : Nat}
    (i : Fin n) :
    paddedRowFromFin (m := m) (n := n)
      (paddedRowToFin (Sum.inl i)) = Sum.inl i := by
  exact mgsPaddedRowFromFin_toFin_inl i

@[simp] theorem paddedRowFromFin_toFin_inr {m n : Nat}
    (i : Fin m) :
    paddedRowFromFin (m := m) (n := n)
      (paddedRowToFin (Sum.inr i)) = Sum.inr i := by
  exact mgsPaddedRowFromFin_toFin_inr i

theorem paddedRowsFromFin_toFin {m n : Nat}
    (B : Sum (Fin n) (Fin m) -> Fin n -> Real) :
    paddedRowsFromFin (paddedRowsToFin B) = B := by
  exact mgsPaddedRowsFromFin_toFin B

theorem paddedRowsToFin_fromFin {m n : Nat}
    (C : Fin (n + m) -> Fin n -> Real) :
    paddedRowsToFin (paddedRowsFromFin C) = C := by
  exact mgsPaddedRowsToFin_fromFin C

theorem paddedRowsFromFin_finInput {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    paddedRowsFromFin (paddedFinInput A) = paddedInput A := by
  exact mgsPaddedRowsFromFin_finInput A

/-- Economy-size bottom-left `Q` block induced by the padded
Householder-MGS row split. -/
abbrev paddedEconomyQ {m n : Nat}
    (Q : Fin (n + m) -> Fin (n + m) -> Real) :
    Fin m -> Fin n -> Real :=
  mgsPaddedEconomyQ Q

/-- Top-left `P11` block induced by the padded Householder-MGS row split. -/
abbrev paddedEconomyP11 {m n : Nat}
    (Q : Fin (n + m) -> Fin (n + m) -> Real) :
    Fin n -> Fin n -> Real :=
  mgsPaddedEconomyP11 Q

/-- Top `n x n` `R` block induced by the padded Householder-MGS row split. -/
abbrev paddedEconomyR {m n : Nat}
    (R : Fin (n + m) -> Fin n -> Real) :
    Fin n -> Fin n -> Real :=
  mgsPaddedEconomyR R

/-- The extracted `R11` block from the padded Householder QR computation used
in the Theorem 19.13 MGS handoff. -/
abbrev householder_paddedFinInput_R11 (fp : FPModel) {m n : Nat}
    (A : Fin m -> Fin n -> Real) : Fin n -> Fin n -> Real :=
  paddedEconomyR
    (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))

/-- Hidden-hypothesis audit for the Theorem 19.13 Householder handoff: in
the smallest tall padded case, a zero source matrix has a zero extracted
`R11` diagonal.  Thus the later nonbreakdown wrappers cannot be discharged
from dimensions and roundoff-smallness alone; they need source rank,
condition, or pivot information. -/
theorem householder_paddedFinInput_R11_zero_input_diag_zero
    (fp : FPModel) :
    householder_paddedFinInput_R11
      (m := 1) (n := 1) fp (fun _ _ => (0 : Real))
      (0 : Fin 1) (0 : Fin 1) = 0 := by
  have hcol :
      panelFirstColumn (m := 1 + 1) (p := 0 + 1) (by norm_num)
        (mgsPaddedFinInput (m := 1) (n := 1) (fun _ _ => (0 : Real))) =
        (fun _ => 0) := by
    funext i
    unfold panelFirstColumn mgsPaddedFinInput mgsPaddedRowsToFin mgsPaddedInput
    cases mgsPaddedRowFromFin (m := 1) (n := 1) i <;> rfl
  have hzeroFun : (fun _ : Fin (1 + 1) => (0 : Real)) = 0 := by
    funext i
    rfl
  simp only [
    householder_paddedFinInput_R11,
    paddedEconomyR,
    paddedFinInput,
    fl_householderQRPanel_R,
    hcol,
    hzeroFun
  ]
  simp [
    mgsPaddedEconomyR,
    mgsPaddedTopBlock,
    mgsPaddedRowsFromFin,
    mgsPaddedRowToFin,
    mgsPaddedFinInput,
    mgsPaddedRowsToFin,
    mgsPaddedInput,
    panelFromTopAndTrailing,
    panelTopLeft
  ]
  cases mgsPaddedRowFromFin (m := 1) (n := 1) (0 : Fin (1 + 1)) <;> rfl

/-- Ch19-facing active-entry bridge between the stored panel update and the
ordinary rectangular Householder update.

This closes the kernel-level part of the recursive/stored `R11` handoff: away
from already completed columns and the stored structural zeros below the pivot,
the two routes use the same rounded dot-scale-subtract Householder update for
the same reflector data.  The remaining `R11` bridge must still identify the
shrinking-panel normalized reflector data with the full stored-loop active
reflector data. -/
theorem storedPanelStep_eq_applyMatrixRect_of_active_not_below
    (fp : FPModel) (m n k : Nat) (v : Fin m -> Real) (beta : Real)
    (A : Fin m -> Fin n -> Real) (i : Fin m) (j : Fin n)
    (hactive : k <= j.val)
    (hnotBelowPivot : j.val = k -> Not (k < i.val)) :
    fl_householderStoredPanelStep fp m n k v beta A i j =
      fl_householderApplyMatrixRect fp m n v beta A i j :=
  fl_householderStoredPanelStep_eq_applyMatrixRect_of_active_not_below
    fp m n k v beta A i j hactive hnotBelowPivot

/-- First-pivot storage bridge for the recursive/stored `R11` handoff.

One local rounded rectangular Householder update, followed by the recursive QR
storage convention that zeroes the first-column tail and keeps the top row, is
exactly the stored-panel update at pivot column zero with the same reflector
data.  Instantiating `v` with the normalized first-column reflector and
`beta = 1` gives the structural first-step bridge for the nonzero branch of
`fl_householderQRPanel_R`; the remaining handoff work is to iterate this bridge
through shrinking panels and identify the active reflector data. -/
theorem firstStoredPanelStep_eq_panelFromTopAndTrailing_applyMatrixRect
    (fp : FPModel) {m p : Nat}
    (v : Fin (m + 1) -> Real) (beta : Real)
    (A : Fin (m + 1) -> Fin (p + 1) -> Real) :
    (let Astep := fl_householderApplyMatrixRect fp (m + 1) (p + 1) v beta A
     panelFromTopAndTrailing (panelTopLeft Astep) (panelTopRowTail Astep)
       (trailingPanel Astep)) =
    fl_householderStoredPanelStep fp (m + 1) (p + 1) 0 v beta A := by
  ext i j
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero =>
          simp [fl_householderStoredPanelStep, fl_householderApplyCompactPanel,
            fl_householderApplyMatrixRect, fl_householderApplyCompact,
            fl_householderApply, panelFromTopAndTrailing, panelTopLeft]
      | succ jtail =>
          simp [fl_householderStoredPanelStep, fl_householderApplyCompactPanel,
            fl_householderApplyMatrixRect, fl_householderApplyCompact,
            fl_householderApply, panelFromTopAndTrailing, panelTopRowTail]
  | succ itail =>
      cases j using Fin.cases with
      | zero =>
          simp [fl_householderStoredPanelStep, panelFromTopAndTrailing]
      | succ jtail =>
          simp [fl_householderStoredPanelStep, fl_householderApplyCompactPanel,
            fl_householderApplyMatrixRect, fl_householderApplyCompact,
            fl_householderApply, panelFromTopAndTrailing, trailingPanel]

/-- One-recursion-layer bridge from the nonzero recursive QR branch to the
first stored-panel step.

For a nonzero active first column, the recursive `R` panel can be written as
the QR storage reconstruction over the trailing panel of the first stored step,
provided the stored step uses the same rounded normalized reflector data as the
recursive branch.  This turns the preceding local storage-shape equality into
the first recursive/stored `R11` bridge layer; the remaining handoff work is to
iterate this statement through the shrinking panels and match the stored-loop
active reflector data at later pivots. -/
theorem qrPanel_R_nonzero_eq_firstStoredPanelStep
    (fp : FPModel) {m p : Nat}
    (A : Fin (m + 1) -> Fin (p + 1) -> Real)
    (hcol : Ne (panelFirstColumn (Nat.succ_pos p) A) 0) :
    fl_householderQRPanel_R fp (m + 1) (p + 1) A =
      (let v := fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A)
       let S := fl_householderStoredPanelStep fp (m + 1) (p + 1) 0 v 1 A
       panelFromTopAndTrailing (panelTopLeft S) (panelTopRowTail S)
         (fl_householderQRPanel_R fp m p (trailingPanel S))) := by
  let v : Fin (m + 1) -> Real :=
    fl_householderNormalizedVector fp (Nat.succ_pos m)
      (panelFirstColumn (Nat.succ_pos p) A)
  let Astep : Fin (m + 1) -> Fin (p + 1) -> Real :=
    fl_householderApplyMatrixRect fp (m + 1) (p + 1) v 1 A
  let S : Fin (m + 1) -> Fin (p + 1) -> Real :=
    fl_householderStoredPanelStep fp (m + 1) (p + 1) 0 v 1 A
  have hS :
      S = panelFromTopAndTrailing (panelTopLeft Astep) (panelTopRowTail Astep)
        (trailingPanel Astep) := by
    dsimp [S, Astep, v]
    exact (firstStoredPanelStep_eq_panelFromTopAndTrailing_applyMatrixRect
      fp v 1 A).symm
  rw [fl_householderQRPanel_R_succ_succ_nonzero fp A hcol]
  change panelFromTopAndTrailing (panelTopLeft Astep) (panelTopRowTail Astep)
        (fl_householderQRPanel_R fp m p (trailingPanel Astep)) =
      panelFromTopAndTrailing (panelTopLeft S) (panelTopRowTail S)
        (fl_householderQRPanel_R fp m p (trailingPanel S))
  rw [hS]
  rw [panelTopLeft_panelFromTopAndTrailing,
    panelTopRowTail_panelFromTopAndTrailing,
    trailingPanel_panelFromTopAndTrailing]

/-- Top-left projection of the nonzero recursive/stored bridge.

This is the first scalar component needed by the later `R11` induction: the
top-left entry produced by the nonzero recursive QR branch is exactly the
top-left entry of the first stored step with the same normalized reflector
data. -/
theorem panelTopLeft_qrPanel_R_nonzero_eq_firstStoredPanelStep
    (fp : FPModel) {m p : Nat}
    (A : Fin (m + 1) -> Fin (p + 1) -> Real)
    (hcol : Ne (panelFirstColumn (Nat.succ_pos p) A) 0) :
    panelTopLeft (fl_householderQRPanel_R fp (m + 1) (p + 1) A) =
      (let v := fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A)
       let S := fl_householderStoredPanelStep fp (m + 1) (p + 1) 0 v 1 A
       panelTopLeft S) := by
  rw [qrPanel_R_nonzero_eq_firstStoredPanelStep fp A hcol]
  rfl

/-- Top-row-tail projection of the nonzero recursive/stored bridge. -/
theorem panelTopRowTail_qrPanel_R_nonzero_eq_firstStoredPanelStep
    (fp : FPModel) {m p : Nat}
    (A : Fin (m + 1) -> Fin (p + 1) -> Real)
    (hcol : Ne (panelFirstColumn (Nat.succ_pos p) A) 0) :
    panelTopRowTail (fl_householderQRPanel_R fp (m + 1) (p + 1) A) =
      (let v := fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A)
       let S := fl_householderStoredPanelStep fp (m + 1) (p + 1) 0 v 1 A
       panelTopRowTail S) := by
  rw [qrPanel_R_nonzero_eq_firstStoredPanelStep fp A hcol]
  rfl

/-- Trailing-panel projection of the nonzero recursive/stored bridge.

After a nonzero first pivot, the trailing panel of the recursive QR `R` output
is the recursive QR `R` output on the trailing panel of the corresponding first
stored step.  This is the named recurrence component needed to lift the
recursive/stored `R11` equality through shrinking panels. -/
theorem trailingPanel_qrPanel_R_nonzero_eq_qrPanel_R_firstStoredPanelStep
    (fp : FPModel) {m p : Nat}
    (A : Fin (m + 1) -> Fin (p + 1) -> Real)
    (hcol : Ne (panelFirstColumn (Nat.succ_pos p) A) 0) :
    trailingPanel (fl_householderQRPanel_R fp (m + 1) (p + 1) A) =
      (let v := fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A)
       let S := fl_householderStoredPanelStep fp (m + 1) (p + 1) 0 v 1 A
       fl_householderQRPanel_R fp m p (trailingPanel S)) := by
  rw [qrPanel_R_nonzero_eq_firstStoredPanelStep fp A hcol]
  rfl

/-- Leading-block determinant data selects the nonzero first-pivot branch of
the recursive Householder QR panel.

This is the branch-selection link needed by the final recursive/stored bridge:
the stored-loop nonbreakdown route supplies leading-block determinant
hypotheses, while `fl_householderQRPanel_R` branches on whether the active
first column is zero. -/
theorem panelFirstColumn_ne_zero_of_first_leadingBlock_det_ne_zero
    {m p : Nat}
    (A : Fin (m + 1) -> Fin (p + 1) -> Real)
    (hdetLead :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos p) :
          Matrix (Fin 1) (Fin 1) Real))
        0) :
    Ne (panelFirstColumn (Nat.succ_pos p) A) 0 := by
  classical
  have hdetPrev :
      Ne (Matrix.det
        (qrPreviousLeadingBlockTranspose A
          (le_trans (Nat.le_succ 0)
            (Nat.succ_le_succ (Nat.zero_le m)))
          (Nat.succ_pos p) :
          Matrix (Fin 0) (Fin 0) Real))
        0 := by
    simp
  have hlowerPrev :
      forall (i : Fin (m + 1)) (j : Fin 0),
        0 <= i.val ->
          A i (qrPreviousColumn (p + 1) 0 (Nat.succ_pos p) j) = 0 := by
    intro _i j _hj
    exact Fin.elim0 j
  let hex := exists_active_trailing_entry_ne_of_leading_block_det_ne_zero
      A (Nat.succ_le_succ (Nat.zero_le m)) (Nat.succ_pos p)
      hdetPrev hdetLead hlowerPrev
  match hex with
  | Exists.intro i hrest =>
      match hrest with
      | And.intro _hi hne =>
          intro hzero
          have hentry := congrFun hzero i
          exact hne (by simpa [panelFirstColumn] using hentry)

/-- Determinant-specialized first-step recursive/stored bridge.

The existing first-step bridge consumes the recursive QR nonzero-branch
condition directly.  This version consumes the source-facing first leading
block determinant condition instead, matching the hypotheses used by the
stored-loop nonbreakdown route. -/
theorem qrPanel_R_eq_firstStoredPanelStep_of_first_leadingBlock_det_ne_zero
    (fp : FPModel) {m p : Nat}
    (A : Fin (m + 1) -> Fin (p + 1) -> Real)
    (hdetLead :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos p) :
          Matrix (Fin 1) (Fin 1) Real))
        0) :
    fl_householderQRPanel_R fp (m + 1) (p + 1) A =
      (let v := fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A)
       let S := fl_householderStoredPanelStep fp (m + 1) (p + 1) 0 v 1 A
       panelFromTopAndTrailing (panelTopLeft S) (panelTopRowTail S)
         (fl_householderQRPanel_R fp m p (trailingPanel S))) :=
  qrPanel_R_nonzero_eq_firstStoredPanelStep fp A
    (panelFirstColumn_ne_zero_of_first_leadingBlock_det_ne_zero A hdetLead)

/-- Top-left determinant-specialized projection of the first recursive/stored
bridge. -/
theorem panelTopLeft_qrPanel_R_eq_firstStoredPanelStep_of_first_leadingBlock_det_ne_zero
    (fp : FPModel) {m p : Nat}
    (A : Fin (m + 1) -> Fin (p + 1) -> Real)
    (hdetLead :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos p) :
          Matrix (Fin 1) (Fin 1) Real))
        0) :
    panelTopLeft (fl_householderQRPanel_R fp (m + 1) (p + 1) A) =
      (let v := fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A)
       let S := fl_householderStoredPanelStep fp (m + 1) (p + 1) 0 v 1 A
       panelTopLeft S) :=
  panelTopLeft_qrPanel_R_nonzero_eq_firstStoredPanelStep fp A
    (panelFirstColumn_ne_zero_of_first_leadingBlock_det_ne_zero A hdetLead)

/-- Top-row-tail determinant-specialized projection of the first
recursive/stored bridge. -/
theorem panelTopRowTail_qrPanel_R_eq_firstStoredPanelStep_of_first_leadingBlock_det_ne_zero
    (fp : FPModel) {m p : Nat}
    (A : Fin (m + 1) -> Fin (p + 1) -> Real)
    (hdetLead :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos p) :
          Matrix (Fin 1) (Fin 1) Real))
        0) :
    panelTopRowTail (fl_householderQRPanel_R fp (m + 1) (p + 1) A) =
      (let v := fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A)
       let S := fl_householderStoredPanelStep fp (m + 1) (p + 1) 0 v 1 A
       panelTopRowTail S) :=
  panelTopRowTail_qrPanel_R_nonzero_eq_firstStoredPanelStep fp A
    (panelFirstColumn_ne_zero_of_first_leadingBlock_det_ne_zero A hdetLead)

/-- Trailing-panel determinant-specialized recurrence for the first
recursive/stored bridge. -/
theorem trailingPanel_qrPanel_R_eq_qrPanel_R_firstStoredPanelStep_of_first_leadingBlock_det_ne_zero
    (fp : FPModel) {m p : Nat}
    (A : Fin (m + 1) -> Fin (p + 1) -> Real)
    (hdetLead :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos p) :
          Matrix (Fin 1) (Fin 1) Real))
        0) :
    trailingPanel (fl_householderQRPanel_R fp (m + 1) (p + 1) A) =
      (let v := fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A)
       let S := fl_householderStoredPanelStep fp (m + 1) (p + 1) 0 v 1 A
       fl_householderQRPanel_R fp m p (trailingPanel S)) :=
  trailingPanel_qrPanel_R_nonzero_eq_qrPanel_R_firstStoredPanelStep fp A
    (panelFirstColumn_ne_zero_of_first_leadingBlock_det_ne_zero A hdetLead)

/-- Zero-column recursive QR `R` panels collapse to the input for every row
count.

The core QR file exposes the nonempty-row version as a simp theorem; this
source-facing wrapper is convenient at the end of shrinking-panel handoffs,
where the remaining row count is an arbitrary natural number. -/
theorem qrPanel_R_zero_cols_any (fp : FPModel) (m : Nat)
    (A : Fin m -> Fin 0 -> Real) :
    fl_householderQRPanel_R fp m 0 A = A := by
  cases m with
  | zero => rfl
  | succ m =>
      exact fl_householderQRPanel_R_zero_cols fp (m := m) A

/-- The first stored Householder panel step zeroes the first-column tail. -/
theorem panelFirstColumnTailZero_firstStoredPanelStep
    (fp : FPModel) {m p : Nat}
    (v : Fin (m + 1) -> Real) (beta : Real)
    (A : Fin (m + 1) -> Fin (p + 1) -> Real) :
    panelFirstColumnTailZero
      (fl_householderStoredPanelStep fp (m + 1) (p + 1) 0 v beta A) := by
  intro i
  simp [panelFirstColumnTail, fl_householderStoredPanelStep]

/-- Later stored Householder panel steps preserve a zero first-column tail.

This is the invariant needed by the recursive/stored `R11` handoff: once the
first stored step has completed the first column, every later pivot copies that
completed column because it lies before the active pivot. -/
theorem panelFirstColumnTailZero_storedPanelStep_of_pos
    (fp : FPModel) {m p k : Nat}
    (hk : 0 < k)
    (v : Fin (m + 1) -> Real) (beta : Real)
    (A : Fin (m + 1) -> Fin (p + 1) -> Real)
    (hzero : panelFirstColumnTailZero A) :
    panelFirstColumnTailZero
      (fl_householderStoredPanelStep fp (m + 1) (p + 1) k v beta A) := by
  intro i
  simpa [panelFirstColumnTail, fl_householderStoredPanelStep, hk]
    using hzero i

/-- Successor-pivot stored steps preserve a zero first-column tail. -/
theorem panelFirstColumnTailZero_storedPanelStep_succ
    (fp : FPModel) {m p : Nat} (k : Nat)
    (v : Fin (m + 1) -> Real) (beta : Real)
    (A : Fin (m + 1) -> Fin (p + 1) -> Real)
    (hzero : panelFirstColumnTailZero A) :
    panelFirstColumnTailZero
      (fl_householderStoredPanelStep fp (m + 1) (p + 1) (k + 1) v beta A) :=
  panelFirstColumnTailZero_storedPanelStep_of_pos fp (Nat.succ_pos k)
    v beta A hzero

/-- Finite stored-panel sequences have a zero first-column tail after the
first step, and the invariant is preserved through every later stored pivot. -/
theorem panelFirstColumnTailZero_storedSequence_after_firstStep
    (fp : FPModel) {m p n : Nat}
    (A_hat : Nat -> Fin (m + 1) -> Fin (p + 1) -> Real)
    (v : Nat -> Fin (m + 1) -> Real) (beta : Nat -> Real)
    (hn : 0 < n)
    (hStep : forall k, k < n ->
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (m + 1) (p + 1) k
          (v k) (beta k) (A_hat k)) :
    forall t, t < n -> panelFirstColumnTailZero (A_hat (t + 1)) := by
  intro t ht
  induction t with
  | zero =>
      rw [hStep 0 hn]
      exact panelFirstColumnTailZero_firstStoredPanelStep
        fp (v 0) (beta 0) (A_hat 0)
  | succ t ih =>
      have htprev : t < n := Nat.lt_trans (Nat.lt_succ_self t) ht
      have hprev : panelFirstColumnTailZero (A_hat (t + 1)) :=
        ih htprev
      rw [hStep (t + 1) ht]
      exact panelFirstColumnTailZero_storedPanelStep_succ
        fp t (v (t + 1)) (beta (t + 1)) (A_hat (t + 1)) hprev

/-- Once a stored-panel sequence is past a column, later stored steps leave that
column unchanged.

This is the completed-column preservation invariant needed for the full stored
sequence/top-block handoff: every later pivot copies columns strictly before the
active pivot. -/
theorem storedSequence_prevColumn_eq_add
    (fp : FPModel) {m n N : Nat}
    (A_hat : Nat -> Fin m -> Fin n -> Real)
    (v : Nat -> Fin m -> Real) (beta : Nat -> Real)
    (hStep : forall k, k < N ->
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (v k) (beta k) (A_hat k))
    {s d : Nat} {i : Fin m} {j : Fin n}
    (hj : j.val < s) (hsd : s + d <= N) :
    A_hat (s + d) i j = A_hat s i j := by
  induction d with
  | zero =>
      change A_hat s i j = A_hat s i j
      rfl
  | succ d ih =>
      have hsd_prev : s + d <= N := by
        omega
      have hstep : s + d < N := by
        omega
      have hjprev : j.val < s + d := by
        exact Nat.lt_of_lt_of_le hj (Nat.le_add_right s d)
      rw [Nat.add_succ, hStep (s + d) hstep]
      rw [fl_householderStoredPanelStep_prevColumn_eq fp
        (v (s + d)) (beta (s + d)) (A_hat (s + d)) hjprev]
      exact ih hsd_prev

/-- After a column's own stored pivot has completed, every later stored step
keeps that column fixed. -/
theorem storedSequence_completedColumn_eq_after_pivot
    (fp : FPModel) {m n N : Nat}
    (A_hat : Nat -> Fin m -> Fin n -> Real)
    (v : Nat -> Fin m -> Real) (beta : Nat -> Real)
    (hStep : forall k, k < N ->
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (v k) (beta k) (A_hat k))
    {d : Nat} {i : Fin m} (j : Fin n)
    (hd : j.val + 1 + d <= N) :
    A_hat (j.val + 1 + d) i j = A_hat (j.val + 1) i j :=
  storedSequence_prevColumn_eq_add fp A_hat v beta hStep
    (Nat.lt_succ_self j.val) hd

/-- A completed prefix column is unchanged from its completion stage to the
final stored stage. -/
theorem storedSequence_prevColumn_eq_final
    (fp : FPModel) {m n N k : Nat}
    (A_hat : Nat -> Fin m -> Fin n -> Real)
    (v : Nat -> Fin m -> Real) (beta : Nat -> Real)
    (hStep : forall t, t < N ->
      A_hat (t + 1) =
        fl_householderStoredPanelStep fp m n t
          (v t) (beta t) (A_hat t))
    {i : Fin m} {j : Fin n}
    (hj : j.val < k) (hkN : k <= N) :
    A_hat N i j = A_hat k i j := by
  have hsd : k + (N - k) <= N := by
    omega
  have hkeep :=
    storedSequence_prevColumn_eq_add fp A_hat v beta hStep
      (s := k) (d := N - k) (i := i) (j := j) hj hsd
  have hsum : k + (N - k) = N := Nat.add_sub_of_le hkN
  simpa [hsum] using hkeep

/-- The final stored stage and the stage just after pivot `k` have the same
leading `(k+1) x (k+1)` block. -/
theorem storedSequence_qrLeadingBlock_eq_final
    (fp : FPModel) {m n N k : Nat}
    (A_hat : Nat -> Fin m -> Fin n -> Real)
    (v : Nat -> Fin m -> Real) (beta : Nat -> Real)
    (hStep : forall t, t < N ->
      A_hat (t + 1) =
        fl_householderStoredPanelStep fp m n t
          (v t) (beta t) (A_hat t))
    (hkm : k + 1 <= m) (hk : k < n) (hkN : k + 1 <= N) :
    qrLeadingBlock (A_hat N) hkm hk =
      qrLeadingBlock (A_hat (k + 1)) hkm hk := by
  funext r q
  exact
    storedSequence_prevColumn_eq_final fp A_hat v beta hStep
      (k := k + 1)
      (i := qrLeadingRow m k hkm r)
      (j := qrLeadingColumn n k hk q)
      (by simpa [qrLeadingColumn] using q.isLt)
      hkN

/-- Determinant-nonzero status for a leading block can be read either at the
final stored stage or just after the block's last pivot. -/
theorem storedSequence_qrLeadingBlock_det_ne_zero_final_iff_after_pivot
    (fp : FPModel) {m n N k : Nat}
    (A_hat : Nat -> Fin m -> Fin n -> Real)
    (v : Nat -> Fin m -> Real) (beta : Nat -> Real)
    (hStep : forall t, t < N ->
      A_hat (t + 1) =
        fl_householderStoredPanelStep fp m n t
          (v t) (beta t) (A_hat t))
    (hkm : k + 1 <= m) (hk : k < n) (hkN : k + 1 <= N) :
    Ne
        (Matrix.det
          (qrLeadingBlock (A_hat N) hkm hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) Real))
        0 <->
      Ne
        (Matrix.det
          (qrLeadingBlock (A_hat (k + 1)) hkm hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) Real))
        0 := by
  rw [storedSequence_qrLeadingBlock_eq_final fp A_hat v beta hStep
    hkm hk hkN]

/-- The final stored stage and stage `k` have the same previous-leading-block
transpose, because all of its columns have already been completed by then. -/
theorem storedSequence_qrPreviousLeadingBlockTranspose_eq_final
    (fp : FPModel) {m n N k : Nat}
    (A_hat : Nat -> Fin m -> Fin n -> Real)
    (v : Nat -> Fin m -> Real) (beta : Nat -> Real)
    (hStep : forall t, t < N ->
      A_hat (t + 1) =
        fl_householderStoredPanelStep fp m n t
          (v t) (beta t) (A_hat t))
    (hkm : k <= m) (hk : k < n) (hkN : k <= N) :
    qrPreviousLeadingBlockTranspose (A_hat N) hkm hk =
      qrPreviousLeadingBlockTranspose (A_hat k) hkm hk := by
  funext j s
  exact
    storedSequence_prevColumn_eq_final fp A_hat v beta hStep
      (k := k)
      (i := qrPrefixRow m k hkm s)
      (j := qrPreviousColumn n k hk j)
      (by simp [qrPreviousColumn])
      hkN

/-- Determinant-nonzero status for the previous-leading-block transpose can be
read either at the final stored stage or at stage `k`. -/
theorem storedSequence_qrPreviousLeadingBlockTranspose_det_ne_zero_final_iff_stage
    (fp : FPModel) {m n N k : Nat}
    (A_hat : Nat -> Fin m -> Fin n -> Real)
    (v : Nat -> Fin m -> Real) (beta : Nat -> Real)
    (hStep : forall t, t < N ->
      A_hat (t + 1) =
        fl_householderStoredPanelStep fp m n t
          (v t) (beta t) (A_hat t))
    (hkm : k <= m) (hk : k < n) (hkN : k <= N) :
    Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat N) hkm hk :
            Matrix (Fin k) (Fin k) Real))
        0 <->
      Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat k) hkm hk :
            Matrix (Fin k) (Fin k) Real))
        0 := by
  rw [storedSequence_qrPreviousLeadingBlockTranspose_eq_final fp A_hat v beta
    hStep hkm hk hkN]

/-- The source-shaped signed stored-QR step is the generic stored-panel step
instantiated with the repository's signed-stage vector and beta. -/
theorem storedSignedSequence_step_of_source_step
    (fp : FPModel) {m n : Nat} (hmn : n <= m)
    (A_hat : Nat -> Fin m -> Fin n -> Real)
    (alpha : Nat -> Real)
    (hStep : forall k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            (Fin.mk k (lt_of_lt_of_le hk hmn))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              (Fin.mk k (lt_of_lt_of_le hk hmn))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    {k : Nat} (hk : k < n) :
    A_hat (k + 1) =
      fl_householderStoredPanelStep fp m n k
        (storedQRSignedStageVector hmn A_hat alpha k)
        (storedQRSignedStageBeta hmn A_hat alpha k)
        (A_hat k) := by
  simpa [storedQRSignedStageVector, storedQRSignedStageBeta, hk] using
    hStep k hk

/-- Under the signed stored-QR recurrence, a completed prefix column is
unchanged from stage `k` through the final stored stage. -/
theorem storedSignedSequence_prevColumn_eq_final
    (fp : FPModel) {m n k : Nat} (hmn : n <= m)
    (A_hat : Nat -> Fin m -> Fin n -> Real)
    (alpha : Nat -> Real)
    (hStep : forall t (ht : t < n),
      A_hat (t + 1) =
        fl_householderStoredPanelStep fp m n t
          (householderTrailingActiveVector m
            (Fin.mk t (lt_of_lt_of_le ht hmn))
            (fun a => A_hat t a (Fin.mk t ht)) (alpha t))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              (Fin.mk t (lt_of_lt_of_le ht hmn))
              (fun a => A_hat t a (Fin.mk t ht)) (alpha t)))
          (A_hat t))
    {i : Fin m} {j : Fin n}
    (hj : j.val < k) (hkN : k <= n) :
    A_hat n i j = A_hat k i j := by
  exact
    storedSequence_prevColumn_eq_final fp A_hat
      (fun t => storedQRSignedStageVector hmn A_hat alpha t)
      (fun t => storedQRSignedStageBeta hmn A_hat alpha t)
      (by
        intro t ht
        exact storedSignedSequence_step_of_source_step
          fp hmn A_hat alpha hStep ht)
      hj hkN

/-- Under the signed stored-QR recurrence, the final stored stage and the stage
just after pivot `k` have the same leading `(k+1) x (k+1)` block. -/
theorem storedSignedSequence_qrLeadingBlock_eq_final
    (fp : FPModel) {m n k : Nat} (hmn : n <= m)
    (A_hat : Nat -> Fin m -> Fin n -> Real)
    (alpha : Nat -> Real)
    (hStep : forall t (ht : t < n),
      A_hat (t + 1) =
        fl_householderStoredPanelStep fp m n t
          (householderTrailingActiveVector m
            (Fin.mk t (lt_of_lt_of_le ht hmn))
            (fun a => A_hat t a (Fin.mk t ht)) (alpha t))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              (Fin.mk t (lt_of_lt_of_le ht hmn))
              (fun a => A_hat t a (Fin.mk t ht)) (alpha t)))
          (A_hat t))
    (hkm : k + 1 <= m) (hk : k < n) :
    qrLeadingBlock (A_hat n) hkm hk =
      qrLeadingBlock (A_hat (k + 1)) hkm hk := by
  exact
    storedSequence_qrLeadingBlock_eq_final fp A_hat
      (fun t => storedQRSignedStageVector hmn A_hat alpha t)
      (fun t => storedQRSignedStageBeta hmn A_hat alpha t)
      (by
        intro t ht
        exact storedSignedSequence_step_of_source_step
          fp hmn A_hat alpha hStep ht)
      hkm hk (Nat.succ_le_of_lt hk)

/-- The leading-block nonzero determinant condition for the signed stored-QR
loop can be read at the final stage or just after the last pivot in the block. -/
theorem storedSignedSequence_qrLeadingBlock_det_ne_zero_final_iff_after_pivot
    (fp : FPModel) {m n k : Nat} (hmn : n <= m)
    (A_hat : Nat -> Fin m -> Fin n -> Real)
    (alpha : Nat -> Real)
    (hStep : forall t (ht : t < n),
      A_hat (t + 1) =
        fl_householderStoredPanelStep fp m n t
          (householderTrailingActiveVector m
            (Fin.mk t (lt_of_lt_of_le ht hmn))
            (fun a => A_hat t a (Fin.mk t ht)) (alpha t))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              (Fin.mk t (lt_of_lt_of_le ht hmn))
              (fun a => A_hat t a (Fin.mk t ht)) (alpha t)))
          (A_hat t))
    (hkm : k + 1 <= m) (hk : k < n) :
    Ne
        (Matrix.det
          (qrLeadingBlock (A_hat n) hkm hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) Real))
        0 <->
      Ne
        (Matrix.det
          (qrLeadingBlock (A_hat (k + 1)) hkm hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) Real))
        0 := by
  rw [storedSignedSequence_qrLeadingBlock_eq_final
    fp hmn A_hat alpha hStep hkm hk]

/-- Under the signed stored-QR recurrence, the final stored stage and stage
`k` have the same previous-leading-block transpose. -/
theorem storedSignedSequence_qrPreviousLeadingBlockTranspose_eq_final
    (fp : FPModel) {m n k : Nat} (hmn : n <= m)
    (A_hat : Nat -> Fin m -> Fin n -> Real)
    (alpha : Nat -> Real)
    (hStep : forall t (ht : t < n),
      A_hat (t + 1) =
        fl_householderStoredPanelStep fp m n t
          (householderTrailingActiveVector m
            (Fin.mk t (lt_of_lt_of_le ht hmn))
            (fun a => A_hat t a (Fin.mk t ht)) (alpha t))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              (Fin.mk t (lt_of_lt_of_le ht hmn))
              (fun a => A_hat t a (Fin.mk t ht)) (alpha t)))
          (A_hat t))
    (hkm : k <= m) (hk : k < n) :
    qrPreviousLeadingBlockTranspose (A_hat n) hkm hk =
      qrPreviousLeadingBlockTranspose (A_hat k) hkm hk := by
  exact
    storedSequence_qrPreviousLeadingBlockTranspose_eq_final fp A_hat
      (fun t => storedQRSignedStageVector hmn A_hat alpha t)
      (fun t => storedQRSignedStageBeta hmn A_hat alpha t)
      (by
        intro t ht
        exact storedSignedSequence_step_of_source_step
          fp hmn A_hat alpha hStep ht)
      hkm hk (Nat.le_of_lt hk)

/-- The previous-leading-block determinant condition for the signed stored-QR
loop can be read at the final stage or at stage `k`. -/
theorem storedSignedSequence_qrPreviousLeadingBlockTranspose_det_ne_zero_final_iff_stage
    (fp : FPModel) {m n k : Nat} (hmn : n <= m)
    (A_hat : Nat -> Fin m -> Fin n -> Real)
    (alpha : Nat -> Real)
    (hStep : forall t (ht : t < n),
      A_hat (t + 1) =
        fl_householderStoredPanelStep fp m n t
          (householderTrailingActiveVector m
            (Fin.mk t (lt_of_lt_of_le ht hmn))
            (fun a => A_hat t a (Fin.mk t ht)) (alpha t))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              (Fin.mk t (lt_of_lt_of_le ht hmn))
              (fun a => A_hat t a (Fin.mk t ht)) (alpha t)))
          (A_hat t))
    (hkm : k <= m) (hk : k < n) :
    Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat n) hkm hk :
            Matrix (Fin k) (Fin k) Real))
        0 <->
      Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat k) hkm hk :
            Matrix (Fin k) (Fin k) Real))
        0 := by
  rw [storedSignedSequence_qrPreviousLeadingBlockTranspose_eq_final
    fp hmn A_hat alpha hStep hkm hk]

/-- Under the signed stored-QR recurrence, final-stage previous-leading-block
nonbreakdown supplies the stage-local previous-leading-block nonbreakdown
premise used by the stored-loop R11 route. -/
theorem storedSignedSequence_qrPreviousLeadingBlockTranspose_det_ne_zero_stage_of_final
    (fp : FPModel) {m n k : Nat} (hmn : n <= m)
    (A_hat : Nat -> Fin m -> Fin n -> Real)
    (alpha : Nat -> Real)
    (hStep : forall t (ht : t < n),
      A_hat (t + 1) =
        fl_householderStoredPanelStep fp m n t
          (householderTrailingActiveVector m
            (Fin.mk t (lt_of_lt_of_le ht hmn))
            (fun a => A_hat t a (Fin.mk t ht)) (alpha t))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              (Fin.mk t (lt_of_lt_of_le ht hmn))
              (fun a => A_hat t a (Fin.mk t ht)) (alpha t)))
          (A_hat t))
    (hkm : k <= m) (hk : k < n)
    (hdetFinal :
      Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat n) hkm hk :
            Matrix (Fin k) (Fin k) Real))
        0) :
    Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat k) hkm hk :
            Matrix (Fin k) (Fin k) Real))
        0 :=
  (storedSignedSequence_qrPreviousLeadingBlockTranspose_det_ne_zero_final_iff_stage
    fp hmn A_hat alpha hStep hkm hk).mp hdetFinal

/-- Uniform form of
`storedSignedSequence_qrPreviousLeadingBlockTranspose_det_ne_zero_stage_of_final`
for the per-pivot previous-leading-block hypotheses in the stored-loop R11
route. -/
theorem storedSignedSequence_qrPreviousLeadingBlockTranspose_det_ne_zero_stages_of_final
    (fp : FPModel) {m n : Nat} (hmn : n <= m)
    (A_hat : Nat -> Fin m -> Fin n -> Real)
    (alpha : Nat -> Real)
    (hStep : forall t (ht : t < n),
      A_hat (t + 1) =
        fl_householderStoredPanelStep fp m n t
          (householderTrailingActiveVector m
            (Fin.mk t (lt_of_lt_of_le ht hmn))
            (fun a => A_hat t a (Fin.mk t ht)) (alpha t))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              (Fin.mk t (lt_of_lt_of_le ht hmn))
              (fun a => A_hat t a (Fin.mk t ht)) (alpha t)))
          (A_hat t))
    (hdetFinal : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat n)
            (le_trans (Nat.le_of_lt hk) hmn) hk :
            Matrix (Fin k) (Fin k) Real))
        0) :
    forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat k)
            (le_trans (Nat.le_of_lt hk) hmn) hk :
            Matrix (Fin k) (Fin k) Real))
        0 := by
  intro k hk
  exact
    storedSignedSequence_qrPreviousLeadingBlockTranspose_det_ne_zero_stage_of_final
      fp hmn A_hat alpha hStep (le_trans (Nat.le_of_lt hk) hmn) hk
      (hdetFinal k hk)

/-- The signed stored-QR recurrence implies the lower-zero shape on all
completed previous columns at every pivot stage. -/
theorem storedSignedSequence_lower_previous_columns
    (fp : FPModel) {m n : Nat} (hmn : n <= m)
    (A_hat : Nat -> Fin m -> Fin n -> Real)
    (alpha : Nat -> Real)
    (hStep : forall t (ht : t < n),
      A_hat (t + 1) =
        fl_householderStoredPanelStep fp m n t
          (householderTrailingActiveVector m
            (Fin.mk t (lt_of_lt_of_le ht hmn))
            (fun a => A_hat t a (Fin.mk t ht)) (alpha t))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              (Fin.mk t (lt_of_lt_of_le ht hmn))
              (fun a => A_hat t a (Fin.mk t ht)) (alpha t)))
          (A_hat t)) :
    forall k (hk : k < n) (i : Fin m) (j : Fin k),
      k <= i.val -> A_hat k i (qrPreviousColumn n k hk j) = 0 := by
  let v : Nat -> Fin m -> Real := fun t =>
    storedQRSignedStageVector hmn A_hat alpha t
  let beta : Nat -> Real := fun t =>
    storedQRSignedStageBeta hmn A_hat alpha t
  have hStepStored : forall t, t < n ->
      A_hat (t + 1) =
        fl_householderStoredPanelStep fp m n t
          (v t) (beta t) (A_hat t) := by
    intro t ht
    exact storedSignedSequence_step_of_source_step
      fp hmn A_hat alpha hStep ht
  have hlower :=
    fl_householderStoredPanel_sequence_prefix_lower_zero
      fp v beta A_hat hStepStored
  intro k hk i j hi
  have hcol : (qrPreviousColumn n k hk j).val < k := by
    simp [qrPreviousColumn]
  exact
    hlower k (Nat.le_of_lt hk) i (qrPreviousColumn n k hk j)
      hcol (lt_of_lt_of_le hcol hi)

/-- One-column determinant-specialized recursive/stored `R` bridge.

Once the active panel has only one column, the determinant-selected nonzero
recursive branch performs the first stored step and the trailing recursive call
has zero columns.  This is the terminal base case for the later shrinking-panel
`R11` induction. -/
theorem qrPanel_R_one_col_eq_firstStoredPanelStep_of_first_leadingBlock_det_ne_zero
    (fp : FPModel) {m : Nat}
    (A : Fin (m + 1) -> Fin 1 -> Real)
    (hdetLead :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0) :
    fl_householderQRPanel_R fp (m + 1) 1 A =
      (let v := fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos 0) A)
       fl_householderStoredPanelStep fp (m + 1) 1 0 v 1 A) := by
  let v : Fin (m + 1) -> Real :=
    fl_householderNormalizedVector fp (Nat.succ_pos m)
      (panelFirstColumn (Nat.succ_pos 0) A)
  let S : Fin (m + 1) -> Fin 1 -> Real :=
    fl_householderStoredPanelStep fp (m + 1) 1 0 v 1 A
  have hqr := qrPanel_R_eq_firstStoredPanelStep_of_first_leadingBlock_det_ne_zero
    (fp := fp) (m := m) (p := 0) A hdetLead
  dsimp [v, S] at hqr
  dsimp [v, S]
  rw [hqr]
  change panelFromTopAndTrailing (panelTopLeft S) (panelTopRowTail S)
      (fl_householderQRPanel_R fp m 0 (trailingPanel S)) = S
  rw [qrPanel_R_zero_cols_any]
  exact panelFromTopAndTrailing_of_firstColumnTailZero S
    (panelFirstColumnTailZero_firstStoredPanelStep fp v 1 A)

/-- One-column final-panel bridge for the recursive/stored `R` handoff.

This is the base case for the remaining final-panel equality: if the stored
source step starts from the recursive input and its signed reflector data has
already been identified with the normalized reflector used by the recursive QR
branch, then the stored final panel is the recursive `R` panel. -/
theorem storedSigned_one_col_final_panel_eq_qrPanel_R_of_reflector_data
    (fp : FPModel) {m : Nat}
    (A : Fin (m + 1) -> Fin 1 -> Real)
    (A_hat : Nat -> Fin (m + 1) -> Fin 1 -> Real)
    (alpha : Nat -> Real)
    (hinit : A_hat 0 = A)
    (hStep0 :
      A_hat 1 =
        fl_householderStoredPanelStep fp (m + 1) 1 0
          (householderTrailingActiveVector (m + 1)
            (Fin.mk 0 (Nat.succ_pos m))
            (fun a => A_hat 0 a (Fin.mk 0 (Nat.succ_pos 0))) (alpha 0))
          (householderBetaSpec (m + 1)
            (householderTrailingActiveVector (m + 1)
              (Fin.mk 0 (Nat.succ_pos m))
              (fun a => A_hat 0 a (Fin.mk 0 (Nat.succ_pos 0))) (alpha 0)))
          (A_hat 0))
    (hvec :
      householderTrailingActiveVector (m + 1)
          (Fin.mk 0 (Nat.succ_pos m))
          (fun a => A_hat 0 a (Fin.mk 0 (Nat.succ_pos 0))) (alpha 0) =
        fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos 0) A))
    (hbeta :
      householderBetaSpec (m + 1)
          (householderTrailingActiveVector (m + 1)
            (Fin.mk 0 (Nat.succ_pos m))
            (fun a => A_hat 0 a (Fin.mk 0 (Nat.succ_pos 0))) (alpha 0)) =
        1)
    (hdetLead :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0) :
    A_hat 1 = fl_householderQRPanel_R fp (m + 1) 1 A := by
  have hqr :=
    qrPanel_R_one_col_eq_firstStoredPanelStep_of_first_leadingBlock_det_ne_zero
      fp A hdetLead
  rw [hStep0, hbeta, hvec, hinit]
  exact hqr.symm

/-- One-column final-panel bridge with source-normalized reflector data.

This is the same terminal recursive/stored `R` handoff as
`storedSigned_one_col_final_panel_eq_qrPanel_R_of_reflector_data`, but it
derives the beta-one premise from the source-shaped normalization
`v^T v = 2`. -/
theorem storedSigned_one_col_final_panel_eq_qrPanel_R_of_reflector_self_dot
    (fp : FPModel) {m : Nat}
    (A : Fin (m + 1) -> Fin 1 -> Real)
    (A_hat : Nat -> Fin (m + 1) -> Fin 1 -> Real)
    (alpha : Nat -> Real)
    (hinit : A_hat 0 = A)
    (hStep0 :
      A_hat 1 =
        fl_householderStoredPanelStep fp (m + 1) 1 0
          (householderTrailingActiveVector (m + 1)
            (Fin.mk 0 (Nat.succ_pos m))
            (fun a => A_hat 0 a (Fin.mk 0 (Nat.succ_pos 0))) (alpha 0))
          (householderBetaSpec (m + 1)
            (householderTrailingActiveVector (m + 1)
              (Fin.mk 0 (Nat.succ_pos m))
              (fun a => A_hat 0 a (Fin.mk 0 (Nat.succ_pos 0))) (alpha 0)))
          (A_hat 0))
    (hvec :
      householderTrailingActiveVector (m + 1)
          (Fin.mk 0 (Nat.succ_pos m))
          (fun a => A_hat 0 a (Fin.mk 0 (Nat.succ_pos 0))) (alpha 0) =
        fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos 0) A))
    (hself :
      (Finset.univ : Finset (Fin (m + 1))).sum
        (fun i =>
          householderTrailingActiveVector (m + 1)
              (Fin.mk 0 (Nat.succ_pos m))
              (fun a => A_hat 0 a (Fin.mk 0 (Nat.succ_pos 0))) (alpha 0) i *
            householderTrailingActiveVector (m + 1)
              (Fin.mk 0 (Nat.succ_pos m))
              (fun a => A_hat 0 a (Fin.mk 0 (Nat.succ_pos 0))) (alpha 0) i) =
        2)
    (hdetLead :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0) :
    A_hat 1 = fl_householderQRPanel_R fp (m + 1) 1 A := by
  have hbeta :
      householderBetaSpec (m + 1)
          (householderTrailingActiveVector (m + 1)
            (Fin.mk 0 (Nat.succ_pos m))
            (fun a => A_hat 0 a (Fin.mk 0 (Nat.succ_pos 0))) (alpha 0)) =
        1 := by
    exact
      householderBetaSpec_eq_one_of_inner_self_eq_two (m + 1)
        (householderTrailingActiveVector (m + 1)
          (Fin.mk 0 (Nat.succ_pos m))
          (fun a => A_hat 0 a (Fin.mk 0 (Nat.succ_pos 0))) (alpha 0))
        hself
  exact
    storedSigned_one_col_final_panel_eq_qrPanel_R_of_reflector_data
      fp A A_hat alpha hinit hStep0 hvec hbeta hdetLead

/-- Source-recurrence wrapper for the one-column final-panel bridge.

This form consumes the same signed stored-step recurrence used by the later
stored-loop nonbreakdown routes, then specializes it to pivot zero.  The only
extra data obligations are exactly the reflector identification and beta
normalization needed to match the recursive one-column QR branch. -/
theorem storedSignedSequence_one_col_final_panel_eq_qrPanel_R_of_reflector_data
    (fp : FPModel) {m : Nat}
    (A : Fin (m + 1) -> Fin 1 -> Real)
    (A_hat : Nat -> Fin (m + 1) -> Fin 1 -> Real)
    (alpha : Nat -> Real)
    (hinit : A_hat 0 = A)
    (hStep : forall k (hk : k < 1),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (m + 1) 1 k
          (householderTrailingActiveVector (m + 1)
            (Fin.mk k
              (lt_of_lt_of_le hk (Nat.succ_le_succ (Nat.zero_le m))))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (m + 1)
            (householderTrailingActiveVector (m + 1)
              (Fin.mk k
                (lt_of_lt_of_le hk (Nat.succ_le_succ (Nat.zero_le m))))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (hvec :
      householderTrailingActiveVector (m + 1)
          (Fin.mk 0 (Nat.succ_pos m))
          (fun a => A_hat 0 a (Fin.mk 0 (Nat.succ_pos 0))) (alpha 0) =
        fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos 0) A))
    (hbeta :
      householderBetaSpec (m + 1)
          (householderTrailingActiveVector (m + 1)
            (Fin.mk 0 (Nat.succ_pos m))
            (fun a => A_hat 0 a (Fin.mk 0 (Nat.succ_pos 0))) (alpha 0)) =
        1)
    (hdetLead :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0) :
    A_hat 1 = fl_householderQRPanel_R fp (m + 1) 1 A := by
  exact
    storedSigned_one_col_final_panel_eq_qrPanel_R_of_reflector_data
      fp A A_hat alpha hinit
      (by
        have h0 := hStep 0 (Nat.succ_pos 0)
        simpa using h0)
      hvec hbeta hdetLead

/-- Source-recurrence wrapper for the one-column final-panel bridge with
source-normalized reflector data.

This variant removes the raw beta-one input from the terminal bridge and
instead consumes the source-facing `v^T v = 2` normalization. -/
theorem storedSignedSequence_one_col_final_panel_eq_qrPanel_R_of_reflector_self_dot
    (fp : FPModel) {m : Nat}
    (A : Fin (m + 1) -> Fin 1 -> Real)
    (A_hat : Nat -> Fin (m + 1) -> Fin 1 -> Real)
    (alpha : Nat -> Real)
    (hinit : A_hat 0 = A)
    (hStep : forall k (hk : k < 1),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (m + 1) 1 k
          (householderTrailingActiveVector (m + 1)
            (Fin.mk k
              (lt_of_lt_of_le hk (Nat.succ_le_succ (Nat.zero_le m))))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (m + 1)
            (householderTrailingActiveVector (m + 1)
              (Fin.mk k
                (lt_of_lt_of_le hk (Nat.succ_le_succ (Nat.zero_le m))))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (hvec :
      householderTrailingActiveVector (m + 1)
          (Fin.mk 0 (Nat.succ_pos m))
          (fun a => A_hat 0 a (Fin.mk 0 (Nat.succ_pos 0))) (alpha 0) =
        fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos 0) A))
    (hself :
      (Finset.univ : Finset (Fin (m + 1))).sum
        (fun i =>
          householderTrailingActiveVector (m + 1)
              (Fin.mk 0 (Nat.succ_pos m))
              (fun a => A_hat 0 a (Fin.mk 0 (Nat.succ_pos 0))) (alpha 0) i *
            householderTrailingActiveVector (m + 1)
              (Fin.mk 0 (Nat.succ_pos m))
              (fun a => A_hat 0 a (Fin.mk 0 (Nat.succ_pos 0))) (alpha 0) i) =
        2)
    (hdetLead :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0) :
    A_hat 1 = fl_householderQRPanel_R fp (m + 1) 1 A := by
  exact
    storedSigned_one_col_final_panel_eq_qrPanel_R_of_reflector_self_dot
      fp A A_hat alpha hinit
      (by
        have h0 := hStep 0 (Nat.succ_pos 0)
        simpa using h0)
      hvec hself hdetLead

/-- Two-column terminal recurrence for the determinant-specialized
recursive/stored `R` bridge.

After the determinant-selected first stored step, the trailing recursive call is
a one-column panel.  Under the corresponding determinant condition for that
trailing panel, the one-column bridge collapses the trailing recursion to the
next first stored step on the trailing panel.  This keeps the remaining
shrinking-panel work focused on lifting the trailing stored step back into the
full stored loop and identifying later-pivot reflector data. -/
theorem trailingPanel_qrPanel_R_two_col_eq_firstStoredPanelStep_of_leadingBlock_det_ne_zero
    (fp : FPModel) {m : Nat}
    (A : Fin (m + 2) -> Fin 2 -> Real)
    (hdetFirst :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le (m + 1)))
          (Nat.succ_pos 1) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
              (panelFirstColumn (Nat.succ_pos 1) A)
           let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1 A
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0) :
    trailingPanel (fl_householderQRPanel_R fp (m + 2) 2 A) =
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1) A)
       let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1 A
       let v1 := fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))
       fl_householderStoredPanelStep fp (m + 1) 1 0 v1 1 (trailingPanel S0)) := by
  let v0 : Fin (m + 2) -> Real :=
    fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
      (panelFirstColumn (Nat.succ_pos 1) A)
  let S0 : Fin (m + 2) -> Fin 2 -> Real :=
    fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1 A
  have htrail := trailingPanel_qrPanel_R_eq_qrPanel_R_firstStoredPanelStep_of_first_leadingBlock_det_ne_zero
    (fp := fp) (m := m + 1) (p := 1) A hdetFirst
  dsimp [v0, S0] at htrail
  dsimp [v0, S0]
  rw [htrail]
  exact qrPanel_R_one_col_eq_firstStoredPanelStep_of_first_leadingBlock_det_ne_zero
    fp (trailingPanel S0) hdetTail

/-- Full two-column terminal bridge for the determinant-specialized
recursive/stored `R` handoff.

This packages the first stored step and the one-column trailing stored step into
one whole-panel equality.  It is still a terminal, source-facing bridge rather
than the general stored-loop identification: the full induction must lift the
trailing stored step into the original stored panel and match later-pivot
reflector data. -/
theorem qrPanel_R_two_col_eq_firstStoredPanelStep_trailingStoredStep_of_leadingBlock_det_ne_zero
    (fp : FPModel) {m : Nat}
    (A : Fin (m + 2) -> Fin 2 -> Real)
    (hdetFirst :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le (m + 1)))
          (Nat.succ_pos 1) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
              (panelFirstColumn (Nat.succ_pos 1) A)
           let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1 A
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0) :
    fl_householderQRPanel_R fp (m + 2) 2 A =
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1) A)
       let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1 A
       let v1 := fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))
       let S1 := fl_householderStoredPanelStep fp (m + 1) 1 0 v1 1 (trailingPanel S0)
       panelFromTopAndTrailing (panelTopLeft S0) (panelTopRowTail S0) S1) := by
  let v0 : Fin (m + 2) -> Real :=
    fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
      (panelFirstColumn (Nat.succ_pos 1) A)
  let S0 : Fin (m + 2) -> Fin 2 -> Real :=
    fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1 A
  let v1 : Fin (m + 1) -> Real :=
    fl_householderNormalizedVector fp (Nat.succ_pos m)
      (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))
  let S1 : Fin (m + 1) -> Fin 1 -> Real :=
    fl_householderStoredPanelStep fp (m + 1) 1 0 v1 1 (trailingPanel S0)
  have hfirst := qrPanel_R_eq_firstStoredPanelStep_of_first_leadingBlock_det_ne_zero
    (fp := fp) (m := m + 1) (p := 1) A hdetFirst
  have hone := qrPanel_R_one_col_eq_firstStoredPanelStep_of_first_leadingBlock_det_ne_zero
    fp (trailingPanel S0) hdetTail
  dsimp [v0, S0] at hfirst
  dsimp [v0, S0, v1, S1] at hone
  dsimp [v0, S0, v1, S1]
  rw [hfirst]
  change panelFromTopAndTrailing (panelTopLeft S0) (panelTopRowTail S0)
      (fl_householderQRPanel_R fp (m + 1) 1 (trailingPanel S0)) =
    panelFromTopAndTrailing (panelTopLeft S0) (panelTopRowTail S0) S1
  rw [hone]

/-- Multiplication by zero is exact in the abstract `FPModel`.

The relative-error law alone is enough here because the exact product is zero.
This small support fact is needed when lifting a trailing compact Householder
dot product through a zero-prefixed full reflector. -/
theorem fl_mul_zero_left (fp : FPModel) (x : Real) :
    fp.fl_mul 0 x = 0 := by
  exact Exists.elim (fp.model_mul 0 x) (fun d hd =>
    And.elim (fun _hle hmul => by
      rw [hmul]
      ring) hd)

/-- Right multiplication by zero is exact in the abstract `FPModel`. -/
theorem fl_mul_zero_right (fp : FPModel) (x : Real) :
    fp.fl_mul x 0 = 0 := by
  exact Exists.elim (fp.model_mul x 0) (fun d hd =>
    And.elim (fun _hle hmul => by
      rw [hmul]
      ring) hd)

/-- Named exact-copy convention for the subtract-by-zero operation.

The abstract `FPModel` deliberately does not include this law, but the
recursive/stored Householder bridge can consume it as a model-strengthening
surface instead of carrying an anonymous raw hypothesis. -/
def subtractZeroExact (fp : FPModel) : Prop :=
  forall x : Real, fp.fl_sub x 0 = x

/-- Exact real arithmetic satisfies the Ch19 subtract-zero copy convention. -/
theorem subtractZeroExact_exactWithUnitRoundoff
    (u0 : Real) (hu0 : 0 <= u0) :
    subtractZeroExact (FPModel.exactWithUnitRoundoff u0 hu0) := by
  intro x
  simp [FPModel.exactWithUnitRoundoff]

/-- A stored panel step preserves the top row tail when the active vector has
zero in the top row and subtraction by zero is exact. -/
theorem panelTopRowTail_storedPanelStep_eq_of_top_zero
    (fp : FPModel) {m p k : Nat}
    (v : Fin (m + 1) -> Real) (beta : Real)
    (A : Fin (m + 1) -> Fin (p + 1) -> Real)
    (hv0 : v 0 = 0)
    (hcopy : subtractZeroExact fp) :
    panelTopRowTail
        (fl_householderStoredPanelStep fp (m + 1) (p + 1) k v beta A) =
      panelTopRowTail A := by
  ext j
  have hraw :
      fl_householderApplyCompactPanel fp (m + 1) (p + 1) v beta A
          0 j.succ =
        A 0 j.succ := by
    change fp.fl_sub (A 0 j.succ)
        (fp.fl_mul
          (fp.fl_mul beta
            (fl_dotProduct fp (m + 1) v (fun a => A a j.succ)))
          (v 0)) =
      A 0 j.succ
    rw [hv0, fl_mul_zero_right]
    exact hcopy (A 0 j.succ)
  by_cases hlt : j.val + 1 < k
  · simp [panelTopRowTail, fl_householderStoredPanelStep, Fin.val_succ, hlt]
  · by_cases heq : j.val + 1 = k
    · simp [panelTopRowTail, fl_householderStoredPanelStep, Fin.val_succ,
        heq, hraw]
    · simp [panelTopRowTail, fl_householderStoredPanelStep, Fin.val_succ,
        hlt, heq, hraw]

/-- Top-row-tail preservation for a stored-panel sequence over a suffix of
stages whose active vectors all have zero top entry. -/
theorem panelTopRowTail_storedSequence_eq_add_of_top_zero
    (fp : FPModel) {m p N : Nat}
    (A_hat : Nat -> Fin (m + 1) -> Fin (p + 1) -> Real)
    (v : Nat -> Fin (m + 1) -> Real) (beta : Nat -> Real)
    (hcopy : subtractZeroExact fp)
    (hStep : forall k, k < N ->
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (m + 1) (p + 1) k
          (v k) (beta k) (A_hat k))
    {s d : Nat}
    (hsd : s + d <= N)
    (hvzero : forall t, s <= t -> t < N -> v t 0 = 0) :
    panelTopRowTail (A_hat (s + d)) = panelTopRowTail (A_hat s) := by
  induction d with
  | zero =>
      change panelTopRowTail (A_hat s) = panelTopRowTail (A_hat s)
      rfl
  | succ d ih =>
      have hsd_prev : s + d <= N := by
        omega
      have hstep : s + d < N := by
        omega
      rw [Nat.add_succ, hStep (s + d) hstep]
      rw [panelTopRowTail_storedPanelStep_eq_of_top_zero
        fp (v (s + d)) (beta (s + d)) (A_hat (s + d))
        (hvzero (s + d) (Nat.le_add_right s d) hstep) hcopy]
      exact ih hsd_prev

/-- Final-stage form of top-row-tail preservation for a stored-panel sequence
over a suffix whose active vectors all have zero top entry. -/
theorem panelTopRowTail_storedSequence_eq_final_of_top_zero
    (fp : FPModel) {m p N : Nat}
    (A_hat : Nat -> Fin (m + 1) -> Fin (p + 1) -> Real)
    (v : Nat -> Fin (m + 1) -> Real) (beta : Nat -> Real)
    (hcopy : subtractZeroExact fp)
    (hStep : forall k, k < N ->
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (m + 1) (p + 1) k
          (v k) (beta k) (A_hat k))
    {s : Nat} (hsN : s <= N)
    (hvzero : forall t, s <= t -> t < N -> v t 0 = 0) :
    panelTopRowTail (A_hat N) = panelTopRowTail (A_hat s) := by
  have hsd : s + (N - s) <= N := by
    omega
  have hkeep :=
    panelTopRowTail_storedSequence_eq_add_of_top_zero fp A_hat v beta hcopy
      hStep (s := s) (d := N - s) hsd hvzero
  have hsum : s + (N - s) = N := Nat.add_sub_of_le hsN
  simpa [hsum] using hkeep

/-- A stored panel step preserves the top row tail of the trailing panel when
the active vector has zero in the second row of the original panel and
subtraction by zero is exact. -/
theorem panelTopRowTail_trailingPanel_storedPanelStep_eq_of_second_row_zero
    (fp : FPModel) {m p k : Nat}
    (v : Fin (m + 2) -> Real) (beta : Real)
    (A : Fin (m + 2) -> Fin (p + 2) -> Real)
    (hv1 : v ((0 : Fin (m + 1)).succ) = 0)
    (hcopy : subtractZeroExact fp) :
    panelTopRowTail
        (trailingPanel
          (fl_householderStoredPanelStep fp (m + 2) (p + 2) k v beta A)) =
      panelTopRowTail (trailingPanel A) := by
  ext j
  let row1 : Fin (m + 2) := (0 : Fin (m + 1)).succ
  have hraw :
      fl_householderApplyCompactPanel fp (m + 2) (p + 2) v beta A
          row1 j.succ.succ =
        A row1 j.succ.succ := by
    change fp.fl_sub (A row1 j.succ.succ)
        (fp.fl_mul
          (fp.fl_mul beta
            (fl_dotProduct fp (m + 2) v (fun a => A a j.succ.succ)))
          (v row1)) =
      A row1 j.succ.succ
    rw [show v row1 = 0 by simpa [row1] using hv1, fl_mul_zero_right]
    exact hcopy (A row1 j.succ.succ)
  have hraw1 :
      fl_householderApplyCompactPanel fp (m + 2) (p + 2) v beta A
          ((0 : Fin (m + 1)).succ) j.succ.succ =
        A ((0 : Fin (m + 1)).succ) j.succ.succ := by
    simpa [row1] using hraw
  have hrawOne :
      fl_householderApplyCompactPanel fp (m + 2) (p + 2) v beta A
          (1 : Fin (m + 2)) j.succ.succ =
        A (1 : Fin (m + 2)) j.succ.succ := by
    have hrow : ((0 : Fin (m + 1)).succ : Fin (m + 2)) =
        (1 : Fin (m + 2)) := by
      ext
      simp
    simpa [hrow] using hraw1
  by_cases hlt : j.val + 1 + 1 < k
  · simp [panelTopRowTail, trailingPanel, fl_householderStoredPanelStep,
      Fin.val_succ, hlt]
  · by_cases heq : j.val + 1 + 1 = k
    · have hkne : k ≠ 0 := by
        omega
      simp [panelTopRowTail, trailingPanel, fl_householderStoredPanelStep,
        Fin.val_succ, heq, hkne, hrawOne]
    · simp [panelTopRowTail, trailingPanel, fl_householderStoredPanelStep,
        Fin.val_succ, hlt, heq, hrawOne]

/-- Top-row-tail preservation for the once-trailing panel over a suffix of
stored stages whose active vectors all have zero second-row entry. -/
theorem panelTopRowTail_trailingPanel_storedSequence_eq_add_of_second_row_zero
    (fp : FPModel) {m p N : Nat}
    (A_hat : Nat -> Fin (m + 2) -> Fin (p + 2) -> Real)
    (v : Nat -> Fin (m + 2) -> Real) (beta : Nat -> Real)
    (hcopy : subtractZeroExact fp)
    (hStep : forall k, k < N ->
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (m + 2) (p + 2) k
          (v k) (beta k) (A_hat k))
    {s d : Nat}
    (hsd : s + d <= N)
    (hvzero : forall t, s <= t -> t < N ->
      v t ((0 : Fin (m + 1)).succ) = 0) :
    panelTopRowTail (trailingPanel (A_hat (s + d))) =
      panelTopRowTail (trailingPanel (A_hat s)) := by
  induction d with
  | zero =>
      change panelTopRowTail (trailingPanel (A_hat s)) =
        panelTopRowTail (trailingPanel (A_hat s))
      rfl
  | succ d ih =>
      have hsd_prev : s + d <= N := by
        omega
      have hstep : s + d < N := by
        omega
      have hlocal :=
        panelTopRowTail_trailingPanel_storedPanelStep_eq_of_second_row_zero
          (fp := fp) (k := s + d)
          (v := v (s + d)) (beta := beta (s + d)) (A := A_hat (s + d))
          (hv1 := hvzero (s + d) (Nat.le_add_right s d) hstep)
          (hcopy := hcopy)
      have hpres :
          panelTopRowTail (trailingPanel (A_hat ((s + d) + 1))) =
            panelTopRowTail (trailingPanel (A_hat (s + d))) := by
        simpa [hStep (s + d) hstep] using hlocal
      calc
        panelTopRowTail (trailingPanel (A_hat (s + (d + 1)))) =
            panelTopRowTail (trailingPanel (A_hat ((s + d) + 1))) := by
          have hidx : s + (d + 1) = (s + d) + 1 := by
            omega
          simp [hidx]
        _ = panelTopRowTail (trailingPanel (A_hat (s + d))) := hpres
        _ = panelTopRowTail (trailingPanel (A_hat s)) := ih hsd_prev

/-- Final-stage form of top-row-tail preservation for the once-trailing panel
over a suffix whose active vectors all have zero second-row entry. -/
theorem panelTopRowTail_trailingPanel_storedSequence_eq_final_of_second_row_zero
    (fp : FPModel) {m p N : Nat}
    (A_hat : Nat -> Fin (m + 2) -> Fin (p + 2) -> Real)
    (v : Nat -> Fin (m + 2) -> Real) (beta : Nat -> Real)
    (hcopy : subtractZeroExact fp)
    (hStep : forall k, k < N ->
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (m + 2) (p + 2) k
          (v k) (beta k) (A_hat k))
    {s : Nat} (hsN : s <= N)
    (hvzero : forall t, s <= t -> t < N ->
      v t ((0 : Fin (m + 1)).succ) = 0) :
    panelTopRowTail (trailingPanel (A_hat N)) =
      panelTopRowTail (trailingPanel (A_hat s)) := by
  have hsd : s + (N - s) <= N := by
    omega
  have hkeep :=
    panelTopRowTail_trailingPanel_storedSequence_eq_add_of_second_row_zero
      fp A_hat v beta hcopy hStep (s := s) (d := N - s) hsd hvzero
  have hsum : s + (N - s) = N := Nat.add_sub_of_le hsN
  simpa [hsum] using hkeep

/-- In a signed stored-QR source recurrence of width `p + 2`, all stages after
the first two preserve the first row after the leading entry.

This is the top-row half of the final-panel induction bookkeeping: after the
two-step bridge has identified `A_hat 2`, later signed Householder steps have a
zero top component and copy that row under the subtract-zero exact-copy
convention. -/
theorem storedSignedSequence_panelTopRowTail_final_eq_two_of_subtractZeroExact
    (fp : FPModel) {m p : Nat}
    (hmn : p + 2 <= m + 2)
    (A_hat : Nat -> Fin (m + 2) -> Fin (p + 2) -> Real)
    (alpha : Nat -> Real)
    (hStep : forall k (hk : k < p + 2),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (m + 2) (p + 2) k
          (householderTrailingActiveVector (m + 2)
            (Fin.mk k (lt_of_lt_of_le hk hmn))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (m + 2)
            (householderTrailingActiveVector (m + 2)
              (Fin.mk k (lt_of_lt_of_le hk hmn))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (hcopy : subtractZeroExact fp) :
    panelTopRowTail (A_hat (p + 2)) =
      panelTopRowTail (A_hat 2) := by
  have hStepSigned : forall k, k < p + 2 ->
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (m + 2) (p + 2) k
          (storedQRSignedStageVector hmn A_hat alpha k)
          (storedQRSignedStageBeta hmn A_hat alpha k)
          (A_hat k) := by
    intro k hk
    exact storedSignedSequence_step_of_source_step
      fp hmn A_hat alpha hStep hk
  have hvzero : forall t, 2 <= t -> t < p + 2 ->
      storedQRSignedStageVector hmn A_hat alpha t (0 : Fin (m + 2)) = 0 := by
    intro t ht2 ht
    let pivot : Fin (m + 2) := Fin.mk t (lt_of_lt_of_le ht hmn)
    let col : Fin (p + 2) := Fin.mk t ht
    have hprefix : (0 : Fin (m + 2)).val < pivot.val := by
      dsimp [pivot]
      omega
    have hz :=
      householderTrailingActiveVector_zero_prefix (m + 2) pivot
        (fun a => A_hat t a col) (alpha t) (0 : Fin (m + 2)) hprefix
    simpa [storedQRSignedStageVector, ht, pivot, col] using hz
  exact
    panelTopRowTail_storedSequence_eq_final_of_top_zero
      fp A_hat
      (fun t => storedQRSignedStageVector hmn A_hat alpha t)
      (fun t => storedQRSignedStageBeta hmn A_hat alpha t)
      hcopy hStepSigned (s := 2) (by omega) hvzero

/-- In a signed stored-QR source recurrence of width `p + 2`, all stages after
the first two preserve the first row of the once-trailing panel after its
leading entry. -/
theorem
    storedSignedSequence_trailingPanel_panelTopRowTail_final_eq_two_of_subtractZeroExact
    (fp : FPModel) {m p : Nat}
    (hmn : p + 2 <= m + 2)
    (A_hat : Nat -> Fin (m + 2) -> Fin (p + 2) -> Real)
    (alpha : Nat -> Real)
    (hStep : forall k (hk : k < p + 2),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (m + 2) (p + 2) k
          (householderTrailingActiveVector (m + 2)
            (Fin.mk k (lt_of_lt_of_le hk hmn))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (m + 2)
            (householderTrailingActiveVector (m + 2)
              (Fin.mk k (lt_of_lt_of_le hk hmn))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (hcopy : subtractZeroExact fp) :
    panelTopRowTail (trailingPanel (A_hat (p + 2))) =
      panelTopRowTail (trailingPanel (A_hat 2)) := by
  have hStepSigned : forall k, k < p + 2 ->
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (m + 2) (p + 2) k
          (storedQRSignedStageVector hmn A_hat alpha k)
          (storedQRSignedStageBeta hmn A_hat alpha k)
          (A_hat k) := by
    intro k hk
    exact storedSignedSequence_step_of_source_step
      fp hmn A_hat alpha hStep hk
  have hvzero : forall t, 2 <= t -> t < p + 2 ->
      storedQRSignedStageVector hmn A_hat alpha t
          ((0 : Fin (m + 1)).succ) = 0 := by
    intro t ht2 ht
    let row1 : Fin (m + 2) := (0 : Fin (m + 1)).succ
    let pivot : Fin (m + 2) := Fin.mk t (lt_of_lt_of_le ht hmn)
    let col : Fin (p + 2) := Fin.mk t ht
    have hprefix : row1.val < pivot.val := by
      have hrow : row1.val = 1 := by
        simp [row1]
      have hpivot : pivot.val = t := rfl
      rw [hrow, hpivot]
      omega
    have hz :=
      householderTrailingActiveVector_zero_prefix (m + 2) pivot
        (fun a => A_hat t a col) (alpha t) row1 hprefix
    simpa [storedQRSignedStageVector, ht, row1, pivot, col] using hz
  exact
    panelTopRowTail_trailingPanel_storedSequence_eq_final_of_second_row_zero
      fp A_hat
      (fun t => storedQRSignedStageVector hmn A_hat alpha t)
      (fun t => storedQRSignedStageBeta hmn A_hat alpha t)
      hcopy hStepSigned (s := 2) (by omega) hvzero

/-- Completed column preservation gives the top-left entry of the once-trailing
panel at the final stored stage from the stage after the first two pivots. -/
theorem storedSignedSequence_trailingPanel_panelTopLeft_final_eq_two
    (fp : FPModel) {m p : Nat}
    (hmn : p + 2 <= m + 2)
    (A_hat : Nat -> Fin (m + 2) -> Fin (p + 2) -> Real)
    (alpha : Nat -> Real)
    (hStep : forall k (hk : k < p + 2),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (m + 2) (p + 2) k
          (householderTrailingActiveVector (m + 2)
            (Fin.mk k (lt_of_lt_of_le hk hmn))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (m + 2)
            (householderTrailingActiveVector (m + 2)
              (Fin.mk k (lt_of_lt_of_le hk hmn))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k)) :
    panelTopLeft (trailingPanel (A_hat (p + 2))) =
      panelTopLeft (trailingPanel (A_hat 2)) := by
  have hcol :=
    storedSignedSequence_prevColumn_eq_final
      (fp := fp) (m := m + 2) (n := p + 2) (k := 2)
      (hmn := hmn) (A_hat := A_hat) (alpha := alpha) (hStep := hStep)
      (i := ((0 : Fin (m + 1)).succ))
      (j := ((0 : Fin (p + 1)).succ))
      (hj := by simp)
      (hkN := by omega)
  simpa [panelTopLeft, trailingPanel] using hcol

/-- Completed column preservation gives the top-left entry of the final stored
panel from the stage after the first two pivots. -/
theorem storedSignedSequence_panelTopLeft_final_eq_two
    (fp : FPModel) {m p : Nat}
    (hmn : p + 2 <= m + 2)
    (A_hat : Nat -> Fin (m + 2) -> Fin (p + 2) -> Real)
    (alpha : Nat -> Real)
    (hStep : forall k (hk : k < p + 2),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (m + 2) (p + 2) k
          (householderTrailingActiveVector (m + 2)
            (Fin.mk k (lt_of_lt_of_le hk hmn))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (m + 2)
            (householderTrailingActiveVector (m + 2)
              (Fin.mk k (lt_of_lt_of_le hk hmn))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k)) :
    panelTopLeft (A_hat (p + 2)) =
      panelTopLeft (A_hat 2) := by
  have hcol :=
    storedSignedSequence_prevColumn_eq_final
      (fp := fp) (m := m + 2) (n := p + 2) (k := 2)
      (hmn := hmn) (A_hat := A_hat) (alpha := alpha) (hStep := hStep)
      (i := (0 : Fin (m + 2))) (j := (0 : Fin (p + 2)))
      (hj := by simp)
      (hkN := by omega)
  simpa [panelTopLeft] using hcol

/-- The final signed stored-QR panel has zero first-column tail, purely from
the stored lower-trapezoidal shape. -/
theorem storedSignedSequence_panelFirstColumnTailZero_final
    (fp : FPModel) {m p : Nat}
    (hmn : p + 2 <= m + 2)
    (A_hat : Nat -> Fin (m + 2) -> Fin (p + 2) -> Real)
    (alpha : Nat -> Real)
    (hStep : forall k (hk : k < p + 2),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (m + 2) (p + 2) k
          (householderTrailingActiveVector (m + 2)
            (Fin.mk k (lt_of_lt_of_le hk hmn))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (m + 2)
            (householderTrailingActiveVector (m + 2)
              (Fin.mk k (lt_of_lt_of_le hk hmn))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k)) :
    panelFirstColumnTailZero (A_hat (p + 2)) := by
  have hStepSigned : forall k, k < p + 2 ->
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (m + 2) (p + 2) k
          (storedQRSignedStageVector hmn A_hat alpha k)
          (storedQRSignedStageBeta hmn A_hat alpha k)
          (A_hat k) := by
    intro k hk
    exact storedSignedSequence_step_of_source_step
      fp hmn A_hat alpha hStep hk
  have hlower :=
    fl_householderStoredPanel_sequence_lower_zero
      fp
      (fun k => storedQRSignedStageVector hmn A_hat alpha k)
      (fun k => storedQRSignedStageBeta hmn A_hat alpha k)
      A_hat hStepSigned
  intro i
  have hji : (0 : Fin (p + 2)).val < i.succ.val := by
    simp
  simpa [panelFirstColumnTail] using
    hlower i.succ (0 : Fin (p + 2)) hji

/-- The once-trailing final signed stored-QR panel has zero first-column tail,
again as a direct consequence of the stored lower-trapezoidal shape. -/
theorem storedSignedSequence_trailingPanel_panelFirstColumnTailZero_final
    (fp : FPModel) {m p : Nat}
    (hmn : p + 2 <= m + 2)
    (A_hat : Nat -> Fin (m + 2) -> Fin (p + 2) -> Real)
    (alpha : Nat -> Real)
    (hStep : forall k (hk : k < p + 2),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (m + 2) (p + 2) k
          (householderTrailingActiveVector (m + 2)
            (Fin.mk k (lt_of_lt_of_le hk hmn))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (m + 2)
            (householderTrailingActiveVector (m + 2)
              (Fin.mk k (lt_of_lt_of_le hk hmn))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k)) :
    panelFirstColumnTailZero (trailingPanel (A_hat (p + 2))) := by
  have hStepSigned : forall k, k < p + 2 ->
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (m + 2) (p + 2) k
          (storedQRSignedStageVector hmn A_hat alpha k)
          (storedQRSignedStageBeta hmn A_hat alpha k)
          (A_hat k) := by
    intro k hk
    exact storedSignedSequence_step_of_source_step
      fp hmn A_hat alpha hStep hk
  have hlower :=
    fl_householderStoredPanel_sequence_lower_zero
      fp
      (fun k => storedQRSignedStageVector hmn A_hat alpha k)
      (fun k => storedQRSignedStageBeta hmn A_hat alpha k)
      A_hat hStepSigned
  intro i
  have hji :
      ((0 : Fin (p + 1)).succ : Fin (p + 2)).val < i.succ.succ.val := by
    simp [Fin.val_succ]
  simpa [panelFirstColumnTail, trailingPanel] using
    hlower i.succ.succ ((0 : Fin (p + 1)).succ) hji

/-- Assemble the full signed stored-QR final panel once the two-step QR
recursion and the twice-trailing recursive subproblem have been identified.

This is the structural induction step for the remaining recursive/stored final
panel equality: the top block is transported from stage `2`, the once-trailing
top row is transported from stage `2`, and the only genuine recursive premise is
the twice-trailing final-panel equality. -/
theorem
    storedSignedSequence_final_panel_eq_qrPanel_R_of_two_step_qrPanel_R_of_twice_trailing_final
    (fp : FPModel) {m p : Nat}
    (hmn : p + 2 <= m + 2)
    (A : Fin (m + 2) -> Fin (p + 2) -> Real)
    (A_hat : Nat -> Fin (m + 2) -> Fin (p + 2) -> Real)
    (alpha : Nat -> Real)
    (hStep : forall k (hk : k < p + 2),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (m + 2) (p + 2) k
          (householderTrailingActiveVector (m + 2)
            (Fin.mk k (lt_of_lt_of_le hk hmn))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (m + 2)
            (householderTrailingActiveVector (m + 2)
              (Fin.mk k (lt_of_lt_of_le hk hmn))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (hcopy : subtractZeroExact fp)
    (hQR2 :
      fl_householderQRPanel_R fp (m + 2) (p + 2) A =
        panelFromTopAndTrailing (panelTopLeft (A_hat 2))
          (panelTopRowTail (A_hat 2))
          (panelFromTopAndTrailing
            (panelTopLeft (trailingPanel (A_hat 2)))
            (panelTopRowTail (trailingPanel (A_hat 2)))
            (fl_householderQRPanel_R fp m p
              (trailingPanel (trailingPanel (A_hat 2))))))
    (hTailFinal :
      trailingPanel (trailingPanel (A_hat (p + 2))) =
        fl_householderQRPanel_R fp m p
          (trailingPanel (trailingPanel (A_hat 2)))) :
    A_hat (p + 2) =
      fl_householderQRPanel_R fp (m + 2) (p + 2) A := by
  have htopLeft :
      panelTopLeft (A_hat (p + 2)) = panelTopLeft (A_hat 2) :=
    storedSignedSequence_panelTopLeft_final_eq_two fp hmn A_hat alpha hStep
  have htop :
      panelTopRowTail (A_hat (p + 2)) = panelTopRowTail (A_hat 2) :=
    storedSignedSequence_panelTopRowTail_final_eq_two_of_subtractZeroExact
      fp hmn A_hat alpha hStep hcopy
  have htrailTopLeft :
      panelTopLeft (trailingPanel (A_hat (p + 2))) =
        panelTopLeft (trailingPanel (A_hat 2)) :=
    storedSignedSequence_trailingPanel_panelTopLeft_final_eq_two
      fp hmn A_hat alpha hStep
  have htrailTop :
      panelTopRowTail (trailingPanel (A_hat (p + 2))) =
        panelTopRowTail (trailingPanel (A_hat 2)) :=
    storedSignedSequence_trailingPanel_panelTopRowTail_final_eq_two_of_subtractZeroExact
      fp hmn A_hat alpha hStep hcopy
  have hzero :
      panelFirstColumnTailZero (A_hat (p + 2)) :=
    storedSignedSequence_panelFirstColumnTailZero_final fp hmn A_hat alpha hStep
  have hzeroTrail :
      panelFirstColumnTailZero (trailingPanel (A_hat (p + 2))) :=
    storedSignedSequence_trailingPanel_panelFirstColumnTailZero_final
      fp hmn A_hat alpha hStep
  have htrail :
      trailingPanel (A_hat (p + 2)) =
        panelFromTopAndTrailing
          (panelTopLeft (trailingPanel (A_hat 2)))
          (panelTopRowTail (trailingPanel (A_hat 2)))
          (fl_householderQRPanel_R fp m p
            (trailingPanel (trailingPanel (A_hat 2)))) := by
    rw [<- panelFromTopAndTrailing_of_firstColumnTailZero
      (trailingPanel (A_hat (p + 2))) hzeroTrail]
    rw [htrailTopLeft, htrailTop, hTailFinal]
  rw [<- panelFromTopAndTrailing_of_firstColumnTailZero
    (A_hat (p + 2)) hzero]
  rw [htopLeft, htop, htrail]
  exact hQR2.symm

/-- Zero-prefix dot-product lift for compact Householder support.

Adding one leading component whose left factor is zero does not change the
sequential floating-point dot product: the first rounded product is zero and
the following addition from zero is exact by the `FPModel` law
`fl_add 0 x = x`. -/
theorem fl_dotProduct_zero_cons (fp : FPModel) {m : Nat}
    (v b : Fin (m + 1) -> Real) (b0 : Real) :
    fl_dotProduct fp (m + 2) (Fin.cases 0 v) (Fin.cases b0 b) =
      fl_dotProduct fp (m + 1) v b := by
  simp [fl_dotProduct, Fin.foldl_succ, fl_mul_zero_left, fp.fl_add_zero]

/-- Zero-prefix dot-product lift without a nonempty-tail side condition. -/
theorem fl_dotProduct_zero_cons_any (fp : FPModel) {n : Nat}
    (v b : Fin n -> Real) (b0 : Real) :
    fl_dotProduct fp (n + 1) (Fin.cases 0 v) (Fin.cases b0 b) =
      fl_dotProduct fp n v b := by
  cases n with
  | zero => simp [fl_dotProduct, fl_mul_zero_left]
  | succ m => exact fl_dotProduct_zero_cons fp v b b0

/-- Compact Householder tail lift for a zero-prefixed reflector.

After adding one leading zero to the reflector and one leading entry to the
column being transformed, the updated active tail is the same compact
Householder update on the original tail. -/
theorem fl_householderApplyCompact_zero_cons_tail
    (fp : FPModel) {m : Nat}
    (v b : Fin (m + 1) -> Real) (b0 beta : Real) :
    (fun i : Fin (m + 1) =>
        fl_householderApplyCompact fp (m + 2) (Fin.cases 0 v) beta
          (Fin.cases b0 b) i.succ) =
      fl_householderApplyCompact fp (m + 1) v beta b := by
  funext i
  simp [fl_householderApplyCompact, fl_dotProduct_zero_cons]

/-- Compact Householder tail lift for a zero-prefixed reflector, including the
empty-tail boundary case. -/
theorem fl_householderApplyCompact_zero_cons_tail_any
    (fp : FPModel) {n : Nat}
    (v b : Fin n -> Real) (b0 beta : Real) :
    (fun i : Fin n =>
        fl_householderApplyCompact fp (n + 1) (Fin.cases 0 v) beta
          (Fin.cases b0 b) i.succ) =
      fl_householderApplyCompact fp n v beta b := by
  funext i
  simp [fl_householderApplyCompact, fl_dotProduct_zero_cons_any]

/-- Successor-pivot trailing active vector as a zero-prefixed active vector on
the once-shrunk panel.

This is the general reflector-data indexing bridge needed by the later
full-loop induction: after dropping the first row, the full stored-loop active
vector at pivot `p.succ` is exactly a leading zero followed by the active
vector at pivot `p` of the shrinking trailing panel. -/
theorem householderTrailingActiveVector_succ_zeroPrefix_of_succ {m : Nat}
    (p : Fin (m + 1)) (x : Fin (m + 2) -> Real) (alpha : Real) :
    householderTrailingActiveVector (m + 2) p.succ x alpha =
      Fin.cases 0
        (householderTrailingActiveVector (m + 1) p
          (fun i => x i.succ) alpha) := by
  funext i
  cases i using Fin.cases with
  | zero =>
      simp [householderTrailingActiveVector, householderActiveVector,
        householderTrailingPart]
      intro h
      have hv := congrArg Fin.val h
      simp at hv
  | succ i =>
      simp [householderTrailingActiveVector, householderActiveVector,
        householderTrailingPart]

/-- Successor-pivot trailing-active-vector zero-prefixing, including the
vacuous zero-dimensional pivot boundary. -/
theorem householderTrailingActiveVector_succ_zeroPrefix_of_succ_any
    {n : Nat} (p : Fin n) (x : Fin (n + 1) -> Real) (alpha : Real) :
    householderTrailingActiveVector (n + 1) p.succ x alpha =
      Fin.cases 0
        (householderTrailingActiveVector n p (fun i => x i.succ) alpha) := by
  cases n with
  | zero => exact Fin.elim0 p
  | succ m => exact householderTrailingActiveVector_succ_zeroPrefix_of_succ p x alpha

/-- Pivot-1 trailing active vector as a zero-prefixed pivot-0 active vector. -/
theorem householderTrailingActiveVector_succ_zeroPrefix {m : Nat}
    (x : Fin (m + 2) -> Real) (alpha : Real) :
    householderTrailingActiveVector (m + 2) ((0 : Fin (m + 1)).succ) x alpha =
      Fin.cases 0
        (householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
          (fun i => x i.succ) alpha) :=
  householderTrailingActiveVector_succ_zeroPrefix_of_succ
    (0 : Fin (m + 1)) x alpha

/-- Adding a leading zero to Householder data leaves the exact beta unchanged. -/
theorem householderBetaSpec_zero_cons {m : Nat}
    (v : Fin (m + 1) -> Real) :
    householderBetaSpec (m + 2) (Fin.cases 0 v) =
      householderBetaSpec (m + 1) v := by
  simp [householderBetaSpec, Fin.sum_univ_succ]

/-- Zero-prefixing leaves the exact beta unchanged, with no nonempty-tail side
condition. -/
theorem householderBetaSpec_zero_cons_any {n : Nat}
    (v : Fin n -> Real) :
    householderBetaSpec (n + 1) (Fin.cases 0 v) =
      householderBetaSpec n v := by
  cases n with
  | zero => simp [householderBetaSpec]
  | succ m => exact householderBetaSpec_zero_cons v

/-- Successor-pivot active-vector zero-prefixing leaves the exact beta equal to
the once-shrunk panel beta. -/
theorem householderBetaSpec_trailingActiveVector_succ_zeroPrefix_of_succ
    {m : Nat} (p : Fin (m + 1))
    (x : Fin (m + 2) -> Real) (alpha : Real) :
    householderBetaSpec (m + 2)
        (householderTrailingActiveVector (m + 2) p.succ x alpha) =
      householderBetaSpec (m + 1)
        (householderTrailingActiveVector (m + 1) p
          (fun i => x i.succ) alpha) := by
  rw [householderTrailingActiveVector_succ_zeroPrefix_of_succ p x alpha]
  exact householderBetaSpec_zero_cons
    (householderTrailingActiveVector (m + 1) p
      (fun i => x i.succ) alpha)

/-- Adding a leading zero preserves the beta-one consequence of the
source-normalized self-dot condition. -/
theorem householderBetaSpec_zero_cons_eq_one_of_inner_self_eq_two {m : Nat}
    (v : Fin (m + 1) -> Real)
    (hself :
      (Finset.univ : Finset (Fin (m + 1))).sum
        (fun i => v i * v i) = 2) :
    householderBetaSpec (m + 2) (Fin.cases 0 v) = 1 := by
  rw [householderBetaSpec_zero_cons]
  exact householderBetaSpec_eq_one_of_inner_self_eq_two (m + 1) v hself

/-- Dropping two leading rows and columns from a double-zero-prefixed stored
step gives the corresponding stored step on the twice-trailing panel.

This is the storage-level shape needed by the final recursive/stored `R`
handoff: a full pivot `k + 2` step becomes pivot `k` after the first two
completed columns have been removed. -/
theorem
    trailingPanel_trailingPanel_storedPanelStep_succ_succ_zeroPrefix_eq_storedPanelStep_trailingPanel_trailingPanel
    (fp : FPModel) {m p : Nat} (k : Nat)
    (v : Fin m -> Real) (beta : Real)
    (A : Fin (m + 2) -> Fin (p + 2) -> Real) :
    trailingPanel (trailingPanel
        (fl_householderStoredPanelStep fp (m + 2) (p + 2) (k + 2)
          (Fin.cases 0 (Fin.cases 0 v)) beta A)) =
      fl_householderStoredPanelStep fp m p k v beta
        (trailingPanel (trailingPanel A)) := by
  ext i j
  have hraw_one :
      fl_householderApplyCompact fp (m + 2)
          (Fin.cases 0 (Fin.cases 0 v)) beta
          (fun a => A a j.succ.succ) i.succ.succ =
        fl_householderApplyCompact fp (m + 1)
          (Fin.cases 0 v) beta
          (fun a => A a.succ j.succ.succ) i.succ := by
    have h := congrFun
      (fl_householderApplyCompact_zero_cons_tail_any fp
        (v := Fin.cases 0 v)
        (b := fun a : Fin (m + 1) => A a.succ j.succ.succ)
        (b0 := A 0 j.succ.succ) (beta := beta)) i.succ
    simpa using h
  have hraw_two :
      fl_householderApplyCompact fp (m + 1)
          (Fin.cases 0 v) beta
          (fun a => A a.succ j.succ.succ) i.succ =
        fl_householderApplyCompact fp m v beta
          (fun a => A a.succ.succ j.succ.succ) i := by
    have h := congrFun
      (fl_householderApplyCompact_zero_cons_tail_any fp
        (v := v)
        (b := fun a : Fin m => A a.succ.succ j.succ.succ)
        (b0 := A ((0 : Fin (m + 1)).succ) j.succ.succ) (beta := beta)) i
    simpa using h
  have hraw :
      fl_householderApplyCompactPanel fp (m + 2) (p + 2)
          (Fin.cases 0 (Fin.cases 0 v)) beta A i.succ.succ j.succ.succ =
        fl_householderApplyCompactPanel fp m p v beta
          (trailingPanel (trailingPanel A)) i j := by
    simp [fl_householderApplyCompactPanel, trailingPanel, hraw_one, hraw_two]
  by_cases hjlt : j.val < k
  case pos =>
    simp [trailingPanel, fl_householderStoredPanelStep, hjlt]
  case neg =>
    have hjnot_full : Not (j.succ.succ.val < k + 2) := by
      intro h
      apply hjlt
      have h' : j.val + 2 < k + 2 := by simpa [Fin.val_succ] using h
      omega
    by_cases hjeq : j.val = k
    case pos =>
      have hjeq_full : j.succ.succ.val = k + 2 := by
        simp [Fin.val_succ, hjeq]
      by_cases hik : k < i.val
      case pos =>
        simp [trailingPanel, fl_householderStoredPanelStep, hjeq, hik]
      case neg =>
        have hiknot_full : Not (k + 2 < i.succ.succ.val) := by
          intro h
          apply hik
          have h' : k + 2 < i.val + 2 := by simpa [Fin.val_succ] using h
          omega
        simpa [trailingPanel, fl_householderStoredPanelStep, hjlt, hjnot_full,
          hjeq, hjeq_full, hik, hiknot_full,
          fl_householderApplyCompactPanel] using hraw
    case neg =>
      have hjeqnot_full : Not (j.succ.succ.val = k + 2) := by
        intro h
        apply hjeq
        have h' : j.val + 2 = k + 2 := by simpa [Fin.val_succ] using h
        omega
      simpa [trailingPanel, fl_householderStoredPanelStep, hjlt, hjnot_full,
        hjeq, hjeqnot_full, fl_householderApplyCompactPanel] using hraw

/-- Double-trailing lift for an actual later-pivot stored Householder step.

After dropping the first two rows and columns, the full stored-loop pivot
`q + 2` active vector and beta become the pivot-`q` active vector and beta on
the twice-trailing panel. -/
theorem
    trailingPanel_trailingPanel_storedPanelStep_succ_succ_trailingActiveVector_eq_storedPanelStep_trailingPanel_trailingPanel_of_succ_succ
    (fp : FPModel) {m p : Nat} (q : Fin m) (hq : q.val < p)
    (A : Fin (m + 2) -> Fin (p + 2) -> Real) (alpha : Real) :
    trailingPanel (trailingPanel
        (fl_householderStoredPanelStep fp (m + 2) (p + 2) (q.val + 2)
          (householderTrailingActiveVector (m + 2) q.succ.succ
            (fun a => A a (Fin.mk q.val hq).succ.succ) alpha)
          (householderBetaSpec (m + 2)
            (householderTrailingActiveVector (m + 2) q.succ.succ
              (fun a => A a (Fin.mk q.val hq).succ.succ) alpha)) A)) =
      fl_householderStoredPanelStep fp m p q.val
        (householderTrailingActiveVector m q
          (fun i => trailingPanel (trailingPanel A) i (Fin.mk q.val hq)) alpha)
        (householderBetaSpec m
          (householderTrailingActiveVector m q
            (fun i => trailingPanel (trailingPanel A) i (Fin.mk q.val hq)) alpha))
        (trailingPanel (trailingPanel A)) := by
  let tailCol : Fin p := Fin.mk q.val hq
  let vtail : Fin m -> Real :=
    householderTrailingActiveVector m q
      (fun i => trailingPanel (trailingPanel A) i tailCol) alpha
  have hv_inner :
      householderTrailingActiveVector (m + 1) q.succ
          (fun i => A i.succ tailCol.succ.succ) alpha =
        Fin.cases 0 vtail := by
    simpa [vtail, trailingPanel, tailCol] using
      (householderTrailingActiveVector_succ_zeroPrefix_of_succ_any
        (p := q) (x := fun i : Fin (m + 1) => A i.succ tailCol.succ.succ)
        (alpha := alpha))
  have hv :
      householderTrailingActiveVector (m + 2) q.succ.succ
          (fun a => A a tailCol.succ.succ) alpha =
        Fin.cases 0 (Fin.cases 0 vtail) := by
    rw [householderTrailingActiveVector_succ_zeroPrefix_of_succ_any
      (p := q.succ) (x := fun a : Fin (m + 2) => A a tailCol.succ.succ)
      (alpha := alpha)]
    rw [hv_inner]
  have hbeta :
      householderBetaSpec (m + 2) (Fin.cases 0 (Fin.cases 0 vtail)) =
        householderBetaSpec m vtail := by
    rw [householderBetaSpec_zero_cons_any]
    rw [householderBetaSpec_zero_cons_any]
  change trailingPanel (trailingPanel
        (fl_householderStoredPanelStep fp (m + 2) (p + 2) (q.val + 2)
          (householderTrailingActiveVector (m + 2) q.succ.succ
            (fun a => A a tailCol.succ.succ) alpha)
          (householderBetaSpec (m + 2)
            (householderTrailingActiveVector (m + 2) q.succ.succ
              (fun a => A a tailCol.succ.succ) alpha)) A)) =
      fl_householderStoredPanelStep fp m p q.val vtail
        (householderBetaSpec m vtail) (trailingPanel (trailingPanel A))
  rw [hv]
  rw [hbeta]
  exact
    trailingPanel_trailingPanel_storedPanelStep_succ_succ_zeroPrefix_eq_storedPanelStep_trailingPanel_trailingPanel
      fp q.val vtail (householderBetaSpec m vtail) A

/-- Exact normalized-reflector bridge for stored trailing-active Householder
data.

The stored source recurrence carries an unnormalized vector with its
`householderBetaSpec`; the recursive QR branch uses the beta-one normalized
reflector.  This exact algebra fact names the equality between those two
reflector matrices before any rounded compact-application obligations are
introduced. -/
theorem householderTrailingActiveVector_normalized_reflector_eq_betaSpec
    {n : Nat} (p : Fin n) (x : Fin n -> Real) (alpha : Real) :
    householder n
        (householderNormalizedVector n
          (householderTrailingActiveVector n p x alpha)
          (householderBetaSpec n
            (householderTrailingActiveVector n p x alpha))) 1 =
      householder n
        (householderTrailingActiveVector n p x alpha)
        (householderBetaSpec n
          (householderTrailingActiveVector n p x alpha)) :=
  householder_normalizedVector_eq_betaSpec n
    (householderTrailingActiveVector n p x alpha)

/-- Beta-one consequence for a source-normalized trailing-active reflector.

This names the exact bridge used by the stored/recursive final-panel route when
the source side supplies `v^T v = 2` instead of a raw beta hypothesis. -/
theorem householderTrailingActiveVector_betaSpec_eq_one_of_self_dot
    {n : Nat} (p : Fin n) (x : Fin n -> Real) (alpha : Real)
    (hself :
      (Finset.univ : Finset (Fin n)).sum
        (fun i =>
          householderTrailingActiveVector n p x alpha i *
            householderTrailingActiveVector n p x alpha i) = 2) :
    householderBetaSpec n (householderTrailingActiveVector n p x alpha) =
      1 := by
  exact
    householderBetaSpec_eq_one_of_inner_self_eq_two n
      (householderTrailingActiveVector n p x alpha) hself

/-- Successor-pivot beta-one bridge from the once-shrunk panel self-dot
normalization.

This packages the zero-prefix equality with the source-shaped `v^T v = 2`
condition for the trailing panel, so later stored-loop lifts can use the actual
successor-pivot active vector without assuming beta-one separately. -/
theorem
    householderBetaSpec_trailingActiveVector_succ_zeroPrefix_eq_one_of_tail_self_dot
    {m : Nat} (p : Fin (m + 1))
    (x : Fin (m + 2) -> Real) (alpha : Real)
    (hself :
      (Finset.univ : Finset (Fin (m + 1))).sum
        (fun i =>
          householderTrailingActiveVector (m + 1) p
              (fun a => x a.succ) alpha i *
            householderTrailingActiveVector (m + 1) p
              (fun a => x a.succ) alpha i) =
        2) :
    householderBetaSpec (m + 2)
        (householderTrailingActiveVector (m + 2) p.succ x alpha) =
      1 := by
  rw [householderBetaSpec_trailingActiveVector_succ_zeroPrefix_of_succ]
  exact householderTrailingActiveVector_betaSpec_eq_one_of_self_dot
    p (fun a => x a.succ) alpha hself

/-- Successor-pivot trailing-panel lift for a full stored step with a
zero-prefixed reflector.

Deleting the first row and first column after a pivot `k + 1` full stored step
with reflector `0 :: v` is exactly the pivot-`k` stored step on the trailing
panel. -/
theorem trailingPanel_storedPanelStep_succ_zeroPrefix_eq_storedPanelStep_trailingPanel_of_succ
    (fp : FPModel) {m p : Nat} (k : Nat)
    (v : Fin (m + 1) -> Real) (beta : Real)
    (A : Fin (m + 2) -> Fin (p + 2) -> Real) :
    trailingPanel
        (fl_householderStoredPanelStep fp (m + 2) (p + 2) (k + 1)
          (Fin.cases 0 v) beta A) =
      fl_householderStoredPanelStep fp (m + 1) (p + 1) k v beta
        (trailingPanel A) := by
  ext i j
  have htail := congrFun
    (fl_householderApplyCompact_zero_cons_tail fp
      (v := v) (b := fun a => A a.succ j.succ)
      (b0 := A 0 j.succ) (beta := beta)) i
  by_cases hjlt : j.val < k
  case pos =>
    simp [trailingPanel, fl_householderStoredPanelStep, hjlt, Fin.val_succ]
  case neg =>
    have hjnot_succ : Not (j.succ.val < k + 1) := by
      intro h
      have h' : j.val < k := by
        exact Nat.succ_lt_succ_iff.mp (by simpa [Fin.val_succ] using h)
      exact hjlt h'
    by_cases hjeq : j.val = k
    case pos =>
      have hjeq_succ : j.succ.val = k + 1 := by
        simp [Fin.val_succ, hjeq]
      by_cases hik : k < i.val
      case pos =>
        simp [trailingPanel, fl_householderStoredPanelStep, hjeq, hik,
          Fin.val_succ]
      case neg =>
        have hiknot_succ : Not (k + 1 < i.succ.val) := by
          intro h
          have h' : k < i.val := by
            exact Nat.succ_lt_succ_iff.mp (by simpa [Fin.val_succ] using h)
          exact hik h'
        simpa [trailingPanel, fl_householderStoredPanelStep, hjlt,
          hjnot_succ, hjeq, hjeq_succ, hik, hiknot_succ,
          fl_householderApplyCompactPanel] using htail
    case neg =>
      have hjeqnot_succ : Not (j.succ.val = k + 1) := by
        intro h
        apply hjeq
        exact Nat.succ.inj (by simpa [Fin.val_succ] using h)
      simpa [trailingPanel, fl_householderStoredPanelStep, hjlt,
        hjnot_succ, hjeq, hjeqnot_succ,
        fl_householderApplyCompactPanel] using htail

/-- Arbitrary-width trailing-panel lift for a pivot-1 full stored step with a
zero-prefixed reflector. -/
theorem trailingPanel_storedPanelStep_succ_zeroPrefix_eq_storedPanelStep_trailingPanel_anyCols
    (fp : FPModel) {m p : Nat}
    (v : Fin (m + 1) -> Real) (beta : Real)
    (A : Fin (m + 2) -> Fin (p + 2) -> Real) :
    trailingPanel
        (fl_householderStoredPanelStep fp (m + 2) (p + 2) 1
          (Fin.cases 0 v) beta A) =
      fl_householderStoredPanelStep fp (m + 1) (p + 1) 0 v beta
        (trailingPanel A) := by
  exact
    trailingPanel_storedPanelStep_succ_zeroPrefix_eq_storedPanelStep_trailingPanel_of_succ
      fp 0 v beta A

/-- Trailing-panel lift for a full stored step with a zero-prefixed reflector.

This is the first concrete bridge from the terminal recursive/stored panel
equalities back toward the full stored loop: the trailing panel of a pivot-1
stored step with reflector `0 :: v` is exactly the pivot-0 stored step on the
trailing panel. -/
theorem trailingPanel_storedPanelStep_succ_zeroPrefix_eq_storedPanelStep_trailingPanel
    (fp : FPModel) {m : Nat}
    (v : Fin (m + 1) -> Real) (beta : Real)
    (A : Fin (m + 2) -> Fin 2 -> Real) :
    trailingPanel
        (fl_householderStoredPanelStep fp (m + 2) 2 1 (Fin.cases 0 v) beta A) =
      fl_householderStoredPanelStep fp (m + 1) 1 0 v beta (trailingPanel A) :=
  trailingPanel_storedPanelStep_succ_zeroPrefix_eq_storedPanelStep_trailingPanel_anyCols
    fp v beta A

/-- Successor-pivot top-row-tail preservation for a zero-prefixed stored step
under an explicit exact subtract-zero copy convention. -/
theorem panelTopRowTail_storedPanelStep_succ_zeroPrefix_eq_of_fl_sub_zero_of_succ
    (fp : FPModel) {m p : Nat} (k : Nat)
    (v : Fin (m + 1) -> Real) (beta : Real)
    (A : Fin (m + 2) -> Fin (p + 2) -> Real)
    (hsubZero : (x : Real) -> fp.fl_sub x 0 = x) :
    panelTopRowTail
        (fl_householderStoredPanelStep fp (m + 2) (p + 2) (k + 1)
          (Fin.cases 0 v) beta A) =
      panelTopRowTail A := by
  ext j
  simp [panelTopRowTail, fl_householderStoredPanelStep,
    fl_householderApplyCompactPanel, fl_householderApplyCompact,
    fl_mul_zero_right, hsubZero, Fin.val_succ]

/-- Arbitrary-width top-row-tail preservation for a pivot-1 zero-prefixed
stored step under an explicit exact subtract-zero copy convention. -/
theorem panelTopRowTail_storedPanelStep_succ_zeroPrefix_eq_of_fl_sub_zero_anyCols
    (fp : FPModel) {m p : Nat}
    (v : Fin (m + 1) -> Real) (beta : Real)
    (A : Fin (m + 2) -> Fin (p + 2) -> Real)
    (hsubZero : (x : Real) -> fp.fl_sub x 0 = x) :
    panelTopRowTail
        (fl_householderStoredPanelStep fp (m + 2) (p + 2) 1
          (Fin.cases 0 v) beta A) =
      panelTopRowTail A :=
  panelTopRowTail_storedPanelStep_succ_zeroPrefix_eq_of_fl_sub_zero_of_succ
    fp 0 v beta A hsubZero

/-- Successor-pivot full zero-prefix stored-step reconstruction.

Deleting the leading row and column turns a pivot `k + 1` stored step with a
zero-prefixed reflector into the pivot-`k` stored step on the trailing panel.
Together with top-row preservation and the incoming first-column-tail invariant,
this reconstructs the full stored panel. -/
theorem storedPanelStep_succ_zeroPrefix_eq_panelFromTopAndTrailing_of_topRowTail_of_succ
    (fp : FPModel) {m p : Nat} (k : Nat)
    (v : Fin (m + 1) -> Real) (beta : Real)
    (A : Fin (m + 2) -> Fin (p + 2) -> Real)
    (hfirstTail : panelFirstColumnTailZero A)
    (htop :
      panelTopRowTail
          (fl_householderStoredPanelStep fp (m + 2) (p + 2) (k + 1)
            (Fin.cases 0 v) beta A) =
        panelTopRowTail A) :
    fl_householderStoredPanelStep fp (m + 2) (p + 2) (k + 1)
        (Fin.cases 0 v) beta A =
      panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A)
        (fl_householderStoredPanelStep fp (m + 1) (p + 1) k v beta
          (trailingPanel A)) := by
  let Sfull : Fin (m + 2) -> Fin (p + 2) -> Real :=
    fl_householderStoredPanelStep fp (m + 2) (p + 2) (k + 1)
      (Fin.cases 0 v) beta A
  let Strail : Fin (m + 1) -> Fin (p + 1) -> Real :=
    fl_householderStoredPanelStep fp (m + 1) (p + 1) k v beta
      (trailingPanel A)
  have htrail : trailingPanel Sfull = Strail := by
    dsimp [Sfull, Strail]
    exact
      trailingPanel_storedPanelStep_succ_zeroPrefix_eq_storedPanelStep_trailingPanel_of_succ
        fp k v beta A
  ext i j
  cases j using Fin.cases with
  | zero =>
      cases i using Fin.cases with
      | zero =>
          simp [fl_householderStoredPanelStep,
            panelFromTopAndTrailing, panelTopLeft]
      | succ itail =>
          have htail0 := hfirstTail itail
          simpa [Sfull, fl_householderStoredPanelStep,
            panelFromTopAndTrailing, panelFirstColumnTail] using htail0
  | succ jtail =>
      cases i using Fin.cases with
      | zero =>
          have hentry := congrFun htop jtail
          simpa [Sfull, panelTopRowTail, panelFromTopAndTrailing] using hentry
      | succ itail =>
          have hentry := congrFun (congrFun htrail itail) jtail
          simpa [Sfull, Strail, trailingPanel, panelFromTopAndTrailing] using hentry

/-- Arbitrary-width full pivot-1 zero-prefix stored-step reconstruction.

This removes the two-column restriction from the storage-shape lemma.  It keeps
the top-row-tail preservation hypothesis explicit so callers can choose either
the exact-copy route or a later copy-error route. -/
theorem storedPanelStep_succ_zeroPrefix_eq_panelFromTopAndTrailing_of_topRowTail_anyCols
    (fp : FPModel) {m p : Nat}
    (v : Fin (m + 1) -> Real) (beta : Real)
    (A : Fin (m + 2) -> Fin (p + 2) -> Real)
    (hfirstTail : panelFirstColumnTailZero A)
    (htop :
      panelTopRowTail
          (fl_householderStoredPanelStep fp (m + 2) (p + 2) 1
            (Fin.cases 0 v) beta A) =
        panelTopRowTail A) :
    fl_householderStoredPanelStep fp (m + 2) (p + 2) 1
        (Fin.cases 0 v) beta A =
      panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A)
        (fl_householderStoredPanelStep fp (m + 1) (p + 1) 0 v beta
          (trailingPanel A)) :=
  storedPanelStep_succ_zeroPrefix_eq_panelFromTopAndTrailing_of_topRowTail_of_succ
    fp 0 v beta A hfirstTail htop

/-- Successor-pivot zero-prefix reconstruction under exact subtract-zero copy. -/
theorem storedPanelStep_succ_zeroPrefix_eq_panelFromTopAndTrailing_of_fl_sub_zero_of_succ
    (fp : FPModel) {m p : Nat} (k : Nat)
    (v : Fin (m + 1) -> Real) (beta : Real)
    (A : Fin (m + 2) -> Fin (p + 2) -> Real)
    (hfirstTail : panelFirstColumnTailZero A)
    (hsubZero : (x : Real) -> fp.fl_sub x 0 = x) :
    fl_householderStoredPanelStep fp (m + 2) (p + 2) (k + 1)
        (Fin.cases 0 v) beta A =
      panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A)
        (fl_householderStoredPanelStep fp (m + 1) (p + 1) k v beta
          (trailingPanel A)) :=
  storedPanelStep_succ_zeroPrefix_eq_panelFromTopAndTrailing_of_topRowTail_of_succ
    fp k v beta A hfirstTail
    (panelTopRowTail_storedPanelStep_succ_zeroPrefix_eq_of_fl_sub_zero_of_succ
      fp k v beta A hsubZero)

/-- Arbitrary-width full pivot-1 zero-prefix reconstruction under exact
subtract-zero copy. -/
theorem storedPanelStep_succ_zeroPrefix_eq_panelFromTopAndTrailing_of_fl_sub_zero_anyCols
    (fp : FPModel) {m p : Nat}
    (v : Fin (m + 1) -> Real) (beta : Real)
    (A : Fin (m + 2) -> Fin (p + 2) -> Real)
    (hfirstTail : panelFirstColumnTailZero A)
    (hsubZero : (x : Real) -> fp.fl_sub x 0 = x) :
    fl_householderStoredPanelStep fp (m + 2) (p + 2) 1
        (Fin.cases 0 v) beta A =
      panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A)
        (fl_householderStoredPanelStep fp (m + 1) (p + 1) 0 v beta
          (trailingPanel A)) :=
  storedPanelStep_succ_zeroPrefix_eq_panelFromTopAndTrailing_of_topRowTail_anyCols
    fp v beta A hfirstTail
    (panelTopRowTail_storedPanelStep_succ_zeroPrefix_eq_of_fl_sub_zero_anyCols
      fp v beta A hsubZero)

/-- Successor-pivot top-row-tail preservation using the named subtract-zero
exact-copy convention. -/
theorem panelTopRowTail_storedPanelStep_succ_zeroPrefix_eq_of_subtractZeroExact_of_succ
    (fp : FPModel) {m p : Nat} (k : Nat)
    (v : Fin (m + 1) -> Real) (beta : Real)
    (A : Fin (m + 2) -> Fin (p + 2) -> Real)
    (hcopy : subtractZeroExact fp) :
    panelTopRowTail
        (fl_householderStoredPanelStep fp (m + 2) (p + 2) (k + 1)
          (Fin.cases 0 v) beta A) =
      panelTopRowTail A :=
  panelTopRowTail_storedPanelStep_succ_zeroPrefix_eq_of_fl_sub_zero_of_succ
    fp k v beta A hcopy

/-- Arbitrary-width top-row-tail preservation using the named subtract-zero
exact-copy convention. -/
theorem panelTopRowTail_storedPanelStep_succ_zeroPrefix_eq_of_subtractZeroExact_anyCols
    (fp : FPModel) {m p : Nat}
    (v : Fin (m + 1) -> Real) (beta : Real)
    (A : Fin (m + 2) -> Fin (p + 2) -> Real)
    (hcopy : subtractZeroExact fp) :
    panelTopRowTail
        (fl_householderStoredPanelStep fp (m + 2) (p + 2) 1
          (Fin.cases 0 v) beta A) =
      panelTopRowTail A :=
  panelTopRowTail_storedPanelStep_succ_zeroPrefix_eq_of_subtractZeroExact_of_succ
    fp 0 v beta A hcopy

/-- Successor-pivot zero-prefix reconstruction using the named subtract-zero
exact-copy convention. -/
theorem storedPanelStep_succ_zeroPrefix_eq_panelFromTopAndTrailing_of_subtractZeroExact_of_succ
    (fp : FPModel) {m p : Nat} (k : Nat)
    (v : Fin (m + 1) -> Real) (beta : Real)
    (A : Fin (m + 2) -> Fin (p + 2) -> Real)
    (hfirstTail : panelFirstColumnTailZero A)
    (hcopy : subtractZeroExact fp) :
    fl_householderStoredPanelStep fp (m + 2) (p + 2) (k + 1)
        (Fin.cases 0 v) beta A =
      panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A)
        (fl_householderStoredPanelStep fp (m + 1) (p + 1) k v beta
          (trailingPanel A)) :=
  storedPanelStep_succ_zeroPrefix_eq_panelFromTopAndTrailing_of_fl_sub_zero_of_succ
    fp k v beta A hfirstTail hcopy

/-- Arbitrary-width full pivot-1 zero-prefix reconstruction using the named
subtract-zero exact-copy convention. -/
theorem storedPanelStep_succ_zeroPrefix_eq_panelFromTopAndTrailing_of_subtractZeroExact_anyCols
    (fp : FPModel) {m p : Nat}
    (v : Fin (m + 1) -> Real) (beta : Real)
    (A : Fin (m + 2) -> Fin (p + 2) -> Real)
    (hfirstTail : panelFirstColumnTailZero A)
    (hcopy : subtractZeroExact fp) :
    fl_householderStoredPanelStep fp (m + 2) (p + 2) 1
        (Fin.cases 0 v) beta A =
      panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A)
        (fl_householderStoredPanelStep fp (m + 1) (p + 1) 0 v beta
          (trailingPanel A)) :=
  storedPanelStep_succ_zeroPrefix_eq_panelFromTopAndTrailing_of_subtractZeroExact_of_succ
    fp 0 v beta A hfirstTail hcopy

/-- Successor-pivot stored-step reconstruction with actual trailing-active
Householder data under exact subtract-zero copy.

This is the later-pivot version of the pivot-1 actual-data bridge below.  A
stored step at full pivot `q.succ` has a zero-prefixed active vector and the
same beta as the pivot `q` active vector of the once-shrunk trailing panel, so
the full stored step reconstructs from the unchanged top row and the trailing
stored step. -/
theorem
    storedPanelStep_succ_trailingActiveVector_eq_panelFromTopAndTrailing_of_subtractZeroExact_of_succ
    (fp : FPModel) {m p : Nat} (q : Fin (m + 1))
    (hq : q.val < p + 1)
    (A : Fin (m + 2) -> Fin (p + 2) -> Real) (alpha : Real)
    (hfirstTail : panelFirstColumnTailZero A)
    (hcopy : subtractZeroExact fp) :
    fl_householderStoredPanelStep fp (m + 2) (p + 2) (q.val + 1)
        (householderTrailingActiveVector (m + 2) q.succ
          (fun a => A a (Fin.mk (q.val + 1) (Nat.succ_lt_succ hq))) alpha)
        (householderBetaSpec (m + 2)
          (householderTrailingActiveVector (m + 2) q.succ
            (fun a => A a (Fin.mk (q.val + 1) (Nat.succ_lt_succ hq))) alpha)) A =
      panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A)
        (fl_householderStoredPanelStep fp (m + 1) (p + 1) q.val
          (householderTrailingActiveVector (m + 1) q
            (fun i => trailingPanel A i (Fin.mk q.val hq)) alpha)
          (householderBetaSpec (m + 1)
            (householderTrailingActiveVector (m + 1) q
              (fun i => trailingPanel A i (Fin.mk q.val hq)) alpha))
          (trailingPanel A)) := by
  let fullCol : Fin (p + 2) := Fin.mk (q.val + 1) (Nat.succ_lt_succ hq)
  let tailCol : Fin (p + 1) := Fin.mk q.val hq
  let vtail : Fin (m + 1) -> Real :=
    householderTrailingActiveVector (m + 1) q
      (fun i => trailingPanel A i tailCol) alpha
  have hcol : tailCol.succ = fullCol := by
    ext
    simp [tailCol, fullCol]
  have hv :
      householderTrailingActiveVector (m + 2) q.succ
          (fun a => A a fullCol) alpha =
        Fin.cases 0 vtail := by
    simpa [vtail, trailingPanel, hcol] using
      (householderTrailingActiveVector_succ_zeroPrefix_of_succ
        q (fun a => A a fullCol) alpha)
  have hbeta :
      householderBetaSpec (m + 2) (Fin.cases 0 vtail) =
        householderBetaSpec (m + 1) vtail :=
    householderBetaSpec_zero_cons vtail
  change
    fl_householderStoredPanelStep fp (m + 2) (p + 2) (q.val + 1)
        (householderTrailingActiveVector (m + 2) q.succ
          (fun a => A a fullCol) alpha)
        (householderBetaSpec (m + 2)
          (householderTrailingActiveVector (m + 2) q.succ
            (fun a => A a fullCol) alpha)) A =
      panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A)
        (fl_householderStoredPanelStep fp (m + 1) (p + 1) q.val
          vtail (householderBetaSpec (m + 1) vtail) (trailingPanel A))
  rw [hv]
  rw [hbeta]
  exact
    storedPanelStep_succ_zeroPrefix_eq_panelFromTopAndTrailing_of_subtractZeroExact_of_succ
      fp q.val vtail (householderBetaSpec (m + 1) vtail) A hfirstTail hcopy

/-- Pivot-1 stored-step reconstruction with actual trailing-active
Householder data under exact subtract-zero copy.

The earlier zero-prefix reconstruction was phrased for an arbitrary
`Fin.cases 0 v` reflector.  This version instantiates that bridge with the
stored loop's own pivot-1 active vector and the corresponding `beta`, reducing
the later `R11` induction to the remaining equality between this pivot-0
trailing active data and the recursive normalized reflector data. -/
theorem
    storedPanelStep_succ_trailingActiveVector_eq_panelFromTopAndTrailing_of_subtractZeroExact_anyCols
    (fp : FPModel) {m p : Nat}
    (A : Fin (m + 2) -> Fin (p + 2) -> Real) (alpha : Real)
    (hfirstTail : panelFirstColumnTailZero A)
    (hcopy : subtractZeroExact fp) :
    fl_householderStoredPanelStep fp (m + 2) (p + 2) 1
        (householderTrailingActiveVector (m + 2) ((0 : Fin (m + 1)).succ)
          (fun a => A a ((0 : Fin (p + 1)).succ)) alpha)
        (householderBetaSpec (m + 2)
          (householderTrailingActiveVector (m + 2) ((0 : Fin (m + 1)).succ)
            (fun a => A a ((0 : Fin (p + 1)).succ)) alpha)) A =
      panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A)
        (fl_householderStoredPanelStep fp (m + 1) (p + 1) 0
          (householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
            (panelFirstColumn (Nat.succ_pos p) (trailingPanel A)) alpha)
          (householderBetaSpec (m + 1)
            (householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
              (panelFirstColumn (Nat.succ_pos p) (trailingPanel A)) alpha))
          (trailingPanel A)) := by
  let vtail : Fin (m + 1) -> Real :=
    householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
      (panelFirstColumn (Nat.succ_pos p) (trailingPanel A)) alpha
  have hv :
      householderTrailingActiveVector (m + 2) ((0 : Fin (m + 1)).succ)
          (fun a => A a ((0 : Fin (p + 1)).succ)) alpha =
        Fin.cases 0 vtail := by
    simpa [vtail, panelFirstColumn, trailingPanel] using
      (householderTrailingActiveVector_succ_zeroPrefix
        (m := m) (x := fun a => A a ((0 : Fin (p + 1)).succ)) alpha)
  have hbeta :
      householderBetaSpec (m + 2) (Fin.cases 0 vtail) =
        householderBetaSpec (m + 1) vtail :=
    householderBetaSpec_zero_cons vtail
  rw [hv]
  rw [hbeta]
  exact
    storedPanelStep_succ_zeroPrefix_eq_panelFromTopAndTrailing_of_subtractZeroExact_anyCols
      fp vtail (householderBetaSpec (m + 1) vtail) A hfirstTail hcopy

/-- Successor-pivot stored-step reconstruction with beta-one data from the
once-shrunk panel self-dot normalization.

This is the source-normalized version of
`storedPanelStep_succ_trailingActiveVector_eq_panelFromTopAndTrailing_of_subtractZeroExact_of_succ`:
the tail-panel condition `v^T v = 2` changes both the full successor-pivot beta
and the once-shrunk beta to `1`.  It is the exact step needed when the recursive
QR branch has already normalized the trailing Householder reflector. -/
theorem
    storedPanelStep_succ_trailingActiveVector_one_eq_panelFromTopAndTrailing_one_of_tail_self_dot_of_subtractZeroExact_of_succ
    (fp : FPModel) {m p : Nat} (q : Fin (m + 1))
    (hq : q.val < p + 1)
    (A : Fin (m + 2) -> Fin (p + 2) -> Real) (alpha : Real)
    (hself :
      (Finset.univ : Finset (Fin (m + 1))).sum
        (fun i =>
          householderTrailingActiveVector (m + 1) q
              (fun a => trailingPanel A a (Fin.mk q.val hq)) alpha i *
            householderTrailingActiveVector (m + 1) q
              (fun a => trailingPanel A a (Fin.mk q.val hq)) alpha i) =
        2)
    (hfirstTail : panelFirstColumnTailZero A)
    (hcopy : subtractZeroExact fp) :
    fl_householderStoredPanelStep fp (m + 2) (p + 2) (q.val + 1)
        (householderTrailingActiveVector (m + 2) q.succ
          (fun a => A a (Fin.mk (q.val + 1) (Nat.succ_lt_succ hq))) alpha)
        1 A =
      panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A)
        (fl_householderStoredPanelStep fp (m + 1) (p + 1) q.val
          (householderTrailingActiveVector (m + 1) q
            (fun i => trailingPanel A i (Fin.mk q.val hq)) alpha)
          1
          (trailingPanel A)) := by
  let fullCol : Fin (p + 2) := Fin.mk (q.val + 1) (Nat.succ_lt_succ hq)
  let tailCol : Fin (p + 1) := Fin.mk q.val hq
  have hcol : tailCol.succ = fullCol := by
    ext
    simp [tailCol, fullCol]
  have hselfFull :
      (Finset.univ : Finset (Fin (m + 1))).sum
        (fun i =>
          householderTrailingActiveVector (m + 1) q
              (fun a => (fun b => A b fullCol) a.succ) alpha i *
            householderTrailingActiveVector (m + 1) q
              (fun a => (fun b => A b fullCol) a.succ) alpha i) =
        2 := by
    simpa [fullCol, tailCol, trailingPanel, hcol] using hself
  have hfullBeta :
      householderBetaSpec (m + 2)
          (householderTrailingActiveVector (m + 2) q.succ
            (fun a => A a fullCol) alpha) =
        1 := by
    exact
      householderBetaSpec_trailingActiveVector_succ_zeroPrefix_eq_one_of_tail_self_dot
        q (fun a => A a fullCol) alpha hselfFull
  have htailBetaFull :
      householderBetaSpec (m + 1)
          (householderTrailingActiveVector (m + 1) q
            (fun i => A i.succ fullCol) alpha) =
        1 := by
    exact
      householderTrailingActiveVector_betaSpec_eq_one_of_self_dot
        q (fun i => A i.succ fullCol) alpha hselfFull
  have hstep :=
    storedPanelStep_succ_trailingActiveVector_eq_panelFromTopAndTrailing_of_subtractZeroExact_of_succ
      fp q hq A alpha hfirstTail hcopy
  simpa [fullCol, hfullBeta, htailBetaFull] using hstep

/-- Pivot-1 stored-step reconstruction with beta-one data from the trailing
panel self-dot normalization, in arbitrary column width. -/
theorem
    storedPanelStep_succ_trailingActiveVector_one_eq_panelFromTopAndTrailing_one_of_tail_self_dot_of_subtractZeroExact_anyCols
    (fp : FPModel) {m p : Nat}
    (A : Fin (m + 2) -> Fin (p + 2) -> Real) (alpha : Real)
    (hself :
      (Finset.univ : Finset (Fin (m + 1))).sum
        (fun i =>
          householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
              (panelFirstColumn (Nat.succ_pos p) (trailingPanel A)) alpha i *
            householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
              (panelFirstColumn (Nat.succ_pos p) (trailingPanel A)) alpha i) =
        2)
    (hfirstTail : panelFirstColumnTailZero A)
    (hcopy : subtractZeroExact fp) :
    fl_householderStoredPanelStep fp (m + 2) (p + 2) 1
        (householderTrailingActiveVector (m + 2) ((0 : Fin (m + 1)).succ)
          (fun a => A a ((0 : Fin (p + 1)).succ)) alpha)
        1 A =
      panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A)
        (fl_householderStoredPanelStep fp (m + 1) (p + 1) 0
          (householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
            (panelFirstColumn (Nat.succ_pos p) (trailingPanel A)) alpha)
          1
          (trailingPanel A)) := by
  have hself' :
      (Finset.univ : Finset (Fin (m + 1))).sum
        (fun i =>
          householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
              (fun a => trailingPanel A a (Fin.mk 0 (Nat.succ_pos p))) alpha i *
            householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
              (fun a => trailingPanel A a (Fin.mk 0 (Nat.succ_pos p))) alpha i) =
        2 := by
    simpa [panelFirstColumn] using hself
  have h :=
    storedPanelStep_succ_trailingActiveVector_one_eq_panelFromTopAndTrailing_one_of_tail_self_dot_of_subtractZeroExact_of_succ
      fp (0 : Fin (m + 1)) (Nat.succ_pos p) A alpha hself' hfirstTail hcopy
  simpa [panelFirstColumn] using h

/-- Full pivot-1 zero-prefix stored-step reconstruction.

The trailing panel of the full stored step is the compact trailing stored step.
The top row of the active column is kept as an explicit hypothesis because the
current abstract `FPModel` does not state that a rounded subtraction by zero is
an exact copy.  This isolates the exact-copy convention needed to lift the
two-column terminal bridge into the full stored loop. -/
theorem storedPanelStep_succ_zeroPrefix_eq_panelFromTopAndTrailing_of_topRowTail
    (fp : FPModel) {m : Nat}
    (v : Fin (m + 1) -> Real) (beta : Real)
    (A : Fin (m + 2) -> Fin 2 -> Real)
    (hfirstTail : panelFirstColumnTailZero A)
    (htop :
      panelTopRowTail
          (fl_householderStoredPanelStep fp (m + 2) 2 1 (Fin.cases 0 v) beta A) =
        panelTopRowTail A) :
    fl_householderStoredPanelStep fp (m + 2) 2 1 (Fin.cases 0 v) beta A =
      panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A)
        (fl_householderStoredPanelStep fp (m + 1) 1 0 v beta (trailingPanel A)) := by
  let Sfull : Fin (m + 2) -> Fin 2 -> Real :=
    fl_householderStoredPanelStep fp (m + 2) 2 1 (Fin.cases 0 v) beta A
  let Strail : Fin (m + 1) -> Fin 1 -> Real :=
    fl_householderStoredPanelStep fp (m + 1) 1 0 v beta (trailingPanel A)
  have htrail : trailingPanel Sfull = Strail := by
    dsimp [Sfull, Strail]
    exact trailingPanel_storedPanelStep_succ_zeroPrefix_eq_storedPanelStep_trailingPanel
      fp v beta A
  ext i j
  cases j using Fin.cases with
  | zero =>
      cases i using Fin.cases with
      | zero =>
          simp [fl_householderStoredPanelStep,
            panelFromTopAndTrailing, panelTopLeft]
      | succ itail =>
          have htail0 := hfirstTail itail
          simpa [Sfull, fl_householderStoredPanelStep,
            panelFromTopAndTrailing, panelFirstColumnTail] using htail0
  | succ jtail =>
      fin_cases jtail
      cases i using Fin.cases with
      | zero =>
          have hentry := congrFun htop 0
          simpa [Sfull, panelTopRowTail, panelFromTopAndTrailing] using hentry
      | succ itail =>
          have hentry := congrFun (congrFun htrail itail) 0
          simpa [Sfull, Strail, trailingPanel, panelFromTopAndTrailing] using hentry

/-- Two-column recursive/stored bridge into the actual second full stored step.

This packages the previous two-column terminal equality with the zero-prefix
full-step reconstruction above.  The remaining full-loop work is now explicit:
the caller must supply the top-row-tail preservation/rounding-copy convention
for the pivot-1 stored step, and later work must still identify the pivot-1
reflector data with the full stored-loop data. -/
theorem qrPanel_R_two_col_eq_secondStoredStep_of_leadingBlock_det_ne_zero
    (fp : FPModel) {m : Nat}
    (A : Fin (m + 2) -> Fin 2 -> Real)
    (hdetFirst :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le (m + 1)))
          (Nat.succ_pos 1) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
              (panelFirstColumn (Nat.succ_pos 1) A)
           let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1 A
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (htop :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1) A)
       let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1 A
       let v1 := fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))
       panelTopRowTail
          (fl_householderStoredPanelStep fp (m + 2) 2 1 (Fin.cases 0 v1) 1 S0) =
        panelTopRowTail S0)) :
    fl_householderQRPanel_R fp (m + 2) 2 A =
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1) A)
       let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1 A
       let v1 := fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))
       fl_householderStoredPanelStep fp (m + 2) 2 1 (Fin.cases 0 v1) 1 S0) := by
  let v0 : Fin (m + 2) -> Real :=
    fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
      (panelFirstColumn (Nat.succ_pos 1) A)
  let S0 : Fin (m + 2) -> Fin 2 -> Real :=
    fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1 A
  let v1 : Fin (m + 1) -> Real :=
    fl_householderNormalizedVector fp (Nat.succ_pos m)
      (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))
  let Sfull : Fin (m + 2) -> Fin 2 -> Real :=
    fl_householderStoredPanelStep fp (m + 2) 2 1 (Fin.cases 0 v1) 1 S0
  let S1 : Fin (m + 1) -> Fin 1 -> Real :=
    fl_householderStoredPanelStep fp (m + 1) 1 0 v1 1 (trailingPanel S0)
  have hqr :=
    qrPanel_R_two_col_eq_firstStoredPanelStep_trailingStoredStep_of_leadingBlock_det_ne_zero
      (fp := fp) (m := m) A hdetFirst hdetTail
  have hSfull :
      Sfull = panelFromTopAndTrailing (panelTopLeft S0) (panelTopRowTail S0) S1 := by
    dsimp [Sfull, S1]
    exact storedPanelStep_succ_zeroPrefix_eq_panelFromTopAndTrailing_of_topRowTail
      fp v1 1 S0
      (panelFirstColumnTailZero_firstStoredPanelStep fp v0 1 A)
      (by simpa [v0, S0, v1, Sfull] using htop)
  dsimp [v0, S0, v1, Sfull, S1] at hqr
  dsimp [v0, S0, v1, Sfull, S1]
  rw [hqr]
  exact hSfull.symm

/-- Top-row-tail preservation for a pivot-1 zero-prefixed stored step under
an explicit exact subtract-zero copy convention.

The repository's base `FPModel` does not imply `fl_sub x 0 = x`; other
computed-object APIs charge that operation as storage/copy.  This lemma states
the precise extra convention needed by the full stored-loop lift. -/
theorem panelTopRowTail_storedPanelStep_succ_zeroPrefix_eq_of_fl_sub_zero
    (fp : FPModel) {m : Nat}
    (v : Fin (m + 1) -> Real) (beta : Real)
    (A : Fin (m + 2) -> Fin 2 -> Real)
    (hsubZero : (x : Real) -> fp.fl_sub x 0 = x) :
    panelTopRowTail
        (fl_householderStoredPanelStep fp (m + 2) 2 1 (Fin.cases 0 v) beta A) =
      panelTopRowTail A := by
  ext j
  fin_cases j
  simp [panelTopRowTail, fl_householderStoredPanelStep,
    fl_householderApplyCompactPanel, fl_householderApplyCompact,
    fl_mul_zero_right, hsubZero]

/-- Full pivot-1 zero-prefix stored-step reconstruction under exact
subtract-zero copy.

This discharges the explicit top-row-tail preservation hypothesis of
`storedPanelStep_succ_zeroPrefix_eq_panelFromTopAndTrailing_of_topRowTail`
from the model convention `fl_sub x 0 = x`. -/
theorem storedPanelStep_succ_zeroPrefix_eq_panelFromTopAndTrailing_of_fl_sub_zero
    (fp : FPModel) {m : Nat}
    (v : Fin (m + 1) -> Real) (beta : Real)
    (A : Fin (m + 2) -> Fin 2 -> Real)
    (hfirstTail : panelFirstColumnTailZero A)
    (hsubZero : (x : Real) -> fp.fl_sub x 0 = x) :
    fl_householderStoredPanelStep fp (m + 2) 2 1 (Fin.cases 0 v) beta A =
      panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A)
        (fl_householderStoredPanelStep fp (m + 1) 1 0 v beta (trailingPanel A)) :=
  storedPanelStep_succ_zeroPrefix_eq_panelFromTopAndTrailing_of_topRowTail
    fp v beta A hfirstTail
    (panelTopRowTail_storedPanelStep_succ_zeroPrefix_eq_of_fl_sub_zero
      fp v beta A hsubZero)

/-- Two-column recursive/stored bridge under exact subtract-zero copy.

Compared with
`qrPanel_R_two_col_eq_secondStoredStep_of_leadingBlock_det_ne_zero`, this
version replaces the abstract top-row-tail preservation premise by the reusable
model convention `fl_sub x 0 = x`.  The remaining open work is the general
full-loop induction and later-pivot reflector-data identification. -/
theorem qrPanel_R_two_col_eq_secondStoredStep_of_leadingBlock_det_ne_zero_of_fl_sub_zero
    (fp : FPModel) {m : Nat}
    (A : Fin (m + 2) -> Fin 2 -> Real)
    (hdetFirst :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le (m + 1)))
          (Nat.succ_pos 1) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
              (panelFirstColumn (Nat.succ_pos 1) A)
           let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1 A
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hsubZero : (x : Real) -> fp.fl_sub x 0 = x) :
    fl_householderQRPanel_R fp (m + 2) 2 A =
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1) A)
       let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1 A
       let v1 := fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))
       fl_householderStoredPanelStep fp (m + 2) 2 1 (Fin.cases 0 v1) 1 S0) := by
  exact qrPanel_R_two_col_eq_secondStoredStep_of_leadingBlock_det_ne_zero
    fp A hdetFirst hdetTail
    (by
      dsimp
      exact panelTopRowTail_storedPanelStep_succ_zeroPrefix_eq_of_fl_sub_zero
        fp _ 1 _ hsubZero)

/-- Top-row-tail preservation using the named subtract-zero exact-copy
convention. -/
theorem panelTopRowTail_storedPanelStep_succ_zeroPrefix_eq_of_subtractZeroExact
    (fp : FPModel) {m : Nat}
    (v : Fin (m + 1) -> Real) (beta : Real)
    (A : Fin (m + 2) -> Fin 2 -> Real)
    (hcopy : subtractZeroExact fp) :
    panelTopRowTail
        (fl_householderStoredPanelStep fp (m + 2) 2 1 (Fin.cases 0 v) beta A) =
      panelTopRowTail A :=
  panelTopRowTail_storedPanelStep_succ_zeroPrefix_eq_of_fl_sub_zero
    fp v beta A hcopy

/-- Full pivot-1 zero-prefix stored-step reconstruction using the named
subtract-zero exact-copy convention. -/
theorem storedPanelStep_succ_zeroPrefix_eq_panelFromTopAndTrailing_of_subtractZeroExact
    (fp : FPModel) {m : Nat}
    (v : Fin (m + 1) -> Real) (beta : Real)
    (A : Fin (m + 2) -> Fin 2 -> Real)
    (hfirstTail : panelFirstColumnTailZero A)
    (hcopy : subtractZeroExact fp) :
    fl_householderStoredPanelStep fp (m + 2) 2 1 (Fin.cases 0 v) beta A =
      panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A)
        (fl_householderStoredPanelStep fp (m + 1) 1 0 v beta (trailingPanel A)) :=
  storedPanelStep_succ_zeroPrefix_eq_panelFromTopAndTrailing_of_fl_sub_zero
    fp v beta A hfirstTail hcopy

/-- Two-column recursive/stored bridge using the named subtract-zero
exact-copy convention. -/
theorem qrPanel_R_two_col_eq_secondStoredStep_of_leadingBlock_det_ne_zero_of_subtractZeroExact
    (fp : FPModel) {m : Nat}
    (A : Fin (m + 2) -> Fin 2 -> Real)
    (hdetFirst :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le (m + 1)))
          (Nat.succ_pos 1) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
              (panelFirstColumn (Nat.succ_pos 1) A)
           let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1 A
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hcopy : subtractZeroExact fp) :
    fl_householderQRPanel_R fp (m + 2) 2 A =
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1) A)
       let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1 A
       let v1 := fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))
       fl_householderStoredPanelStep fp (m + 2) 2 1 (Fin.cases 0 v1) 1 S0) :=
  qrPanel_R_two_col_eq_secondStoredStep_of_leadingBlock_det_ne_zero_of_fl_sub_zero
    fp A hdetFirst hdetTail hcopy

/-- Two-column recursive/stored bridge with actual pivot-1 active-vector data.

This removes the artificial `Fin.cases 0 v1` normalized-vector endpoint from the
terminal two-column bridge.  If the tail-panel source active vector is the
recursive normalized reflector and satisfies the source normalization
`v^T v = 2`, then the recursive two-column `R` panel is exactly the second full
stored step with the actual successor-pivot active vector and beta one. -/
theorem
    qrPanel_R_two_col_eq_secondStoredActiveStep_one_of_tail_reflector_self_dot_of_subtractZeroExact
    (fp : FPModel) {m : Nat}
    (A : Fin (m + 2) -> Fin 2 -> Real) (alpha : Real)
    (hdetFirst :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le (m + 1)))
          (Nat.succ_pos 1) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
              (panelFirstColumn (Nat.succ_pos 1) A)
           let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1 A
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTail :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1) A)
       let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1 A
       householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
            (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0)) alpha =
          fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))))
    (hselfTail :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1) A)
       let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1 A
       (Finset.univ : Finset (Fin (m + 1))).sum
          (fun i =>
            householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0)) alpha i *
              householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0)) alpha i) =
        2))
    (hcopy : subtractZeroExact fp) :
    fl_householderQRPanel_R fp (m + 2) 2 A =
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1) A)
       let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1 A
       fl_householderStoredPanelStep fp (m + 2) 2 1
        (householderTrailingActiveVector (m + 2) ((0 : Fin (m + 1)).succ)
          (fun a => S0 a ((0 : Fin 1).succ)) alpha)
        1 S0) := by
  let v0 : Fin (m + 2) -> Real :=
    fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
      (panelFirstColumn (Nat.succ_pos 1) A)
  let S0 : Fin (m + 2) -> Fin 2 -> Real :=
    fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1 A
  let vTail : Fin (m + 1) -> Real :=
    householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
      (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0)) alpha
  let v1 : Fin (m + 1) -> Real :=
    fl_householderNormalizedVector fp (Nat.succ_pos m)
      (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))
  let S1Tail : Fin (m + 1) -> Fin 1 -> Real :=
    fl_householderStoredPanelStep fp (m + 1) 1 0 vTail 1
      (trailingPanel S0)
  let S1Norm : Fin (m + 1) -> Fin 1 -> Real :=
    fl_householderStoredPanelStep fp (m + 1) 1 0 v1 1
      (trailingPanel S0)
  let Sfull : Fin (m + 2) -> Fin 2 -> Real :=
    fl_householderStoredPanelStep fp (m + 2) 2 1
      (householderTrailingActiveVector (m + 2) ((0 : Fin (m + 1)).succ)
        (fun a => S0 a ((0 : Fin 1).succ)) alpha) 1 S0
  have hqr :=
    qrPanel_R_two_col_eq_firstStoredPanelStep_trailingStoredStep_of_leadingBlock_det_ne_zero
      (fp := fp) (m := m) A hdetFirst hdetTail
  have hvecTail' : vTail = v1 := by
    dsimp [vTail, v1]
    simpa [v0, S0] using hvecTail
  have hS1 : S1Tail = S1Norm := by
    dsimp [S1Tail, S1Norm]
    rw [hvecTail']
  have hfull :
      Sfull =
        panelFromTopAndTrailing (panelTopLeft S0) (panelTopRowTail S0) S1Tail := by
    dsimp [Sfull, S1Tail, vTail]
    exact
      storedPanelStep_succ_trailingActiveVector_one_eq_panelFromTopAndTrailing_one_of_tail_self_dot_of_subtractZeroExact_anyCols
        fp S0 alpha
        (by simpa [v0, S0] using hselfTail)
        (panelFirstColumnTailZero_firstStoredPanelStep fp v0 1 A)
        hcopy
  have hqr' :
      fl_householderQRPanel_R fp (m + 2) 2 A =
        panelFromTopAndTrailing (panelTopLeft S0) (panelTopRowTail S0)
          S1Norm := by
    simpa [v0, S0, v1, S1Norm] using hqr
  have hpanelNorm_eq_Sfull :
      panelFromTopAndTrailing (panelTopLeft S0) (panelTopRowTail S0)
          S1Norm =
        Sfull := by
    simpa [hS1] using hfull.symm
  simpa [v0, S0, Sfull] using hqr'.trans hpanelNorm_eq_Sfull

/-- Two-column signed stored-sequence final-panel bridge.

This is the terminal source-recurrence base case for the recursive/stored
final-panel handoff.  If the first stored source step matches the recursive
normalized first reflector, and the second source step's tail reflector matches
the recursive normalized trailing reflector with source self-dot normalization,
then the two-step stored sequence final panel is exactly the recursive
Householder `R` panel. -/
theorem
    storedSignedSequence_two_col_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_subtractZeroExact
    (fp : FPModel) {m : Nat}
    (A : Fin (m + 2) -> Fin 2 -> Real)
    (A_hat : Nat -> Fin (m + 2) -> Fin 2 -> Real)
    (alpha : Nat -> Real)
    (hrows : 2 <= m + 2)
    (hinit : A_hat 0 = A)
    (hStep : forall k (hk : k < 2),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (m + 2) 2 k
          (householderTrailingActiveVector (m + 2)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (m + 2)
            (householderTrailingActiveVector (m + 2)
              (Fin.mk k (lt_of_lt_of_le hk hrows))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (hvec0 :
      householderTrailingActiveVector (m + 2)
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
          (fun a => A_hat 0 a (Fin.mk 0 (Nat.succ_pos 1))) (alpha 0) =
        fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1) A))
    (hself0 :
      (Finset.univ : Finset (Fin (m + 2))).sum
        (fun i =>
          householderTrailingActiveVector (m + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
              (fun a => A_hat 0 a (Fin.mk 0 (Nat.succ_pos 1))) (alpha 0) i *
            householderTrailingActiveVector (m + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
              (fun a => A_hat 0 a (Fin.mk 0 (Nat.succ_pos 1))) (alpha 0) i) =
        2)
    (hdetFirst :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le (m + 1)))
          (Nat.succ_pos 1) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
              (panelFirstColumn (Nat.succ_pos 1) A)
           let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1 A
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTail :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1) A)
       let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1 A
       householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
            (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0)) (alpha 1) =
          fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))))
    (hselfTail :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1) A)
       let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1 A
       (Finset.univ : Finset (Fin (m + 1))).sum
          (fun i =>
            householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0)) (alpha 1) i *
              householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0)) (alpha 1) i) =
        2))
    (hcopy : subtractZeroExact fp) :
    A_hat 2 = fl_householderQRPanel_R fp (m + 2) 2 A := by
  let v0 : Fin (m + 2) -> Real :=
    fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
      (panelFirstColumn (Nat.succ_pos 1) A)
  let S0 : Fin (m + 2) -> Fin 2 -> Real :=
    fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1 A
  let Sfull : Fin (m + 2) -> Fin 2 -> Real :=
    fl_householderStoredPanelStep fp (m + 2) 2 1
      (householderTrailingActiveVector (m + 2) ((0 : Fin (m + 1)).succ)
        (fun a => S0 a ((0 : Fin 1).succ)) (alpha 1)) 1 S0
  have hbeta0 :
      householderBetaSpec (m + 2)
          (householderTrailingActiveVector (m + 2)
            (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
            (fun a => A_hat 0 a (Fin.mk 0 (Nat.succ_pos 1))) (alpha 0)) =
        1 := by
    exact
      householderBetaSpec_eq_one_of_inner_self_eq_two (m + 2)
        (householderTrailingActiveVector (m + 2)
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
          (fun a => A_hat 0 a (Fin.mk 0 (Nat.succ_pos 1))) (alpha 0))
        hself0
  have hA1 : A_hat 1 = S0 := by
    have h0 := hStep 0 (Nat.succ_pos 1)
    rw [h0, hbeta0, hvec0, hinit]
  have hrow1 :
      Fin.mk 1 (lt_of_lt_of_le (Nat.lt_succ_self 1) hrows) =
        ((0 : Fin (m + 1)).succ) := by
    ext
    rfl
  have hcol1 :
      Fin.mk 1 (Nat.lt_succ_self 1) = ((0 : Fin 1).succ) := by
    ext
    rfl
  have hbeta1Active :
      householderBetaSpec (m + 2)
          (householderTrailingActiveVector (m + 2) ((0 : Fin (m + 1)).succ)
            (fun a => S0 a ((0 : Fin 1).succ)) (alpha 1)) =
        1 := by
    exact
      householderBetaSpec_trailingActiveVector_succ_zeroPrefix_eq_one_of_tail_self_dot
        (0 : Fin (m + 1)) (fun a => S0 a ((0 : Fin 1).succ)) (alpha 1)
        (by simpa [v0, S0] using hselfTail)
  have hA2 : A_hat 2 = Sfull := by
    have h1 := hStep 1 (Nat.lt_succ_self 1)
    rw [h1, hA1]
    rw [hrow1, hcol1, hbeta1Active]
  have hqr :
      fl_householderQRPanel_R fp (m + 2) 2 A = Sfull := by
    simpa [v0, S0, Sfull] using
      qrPanel_R_two_col_eq_secondStoredActiveStep_one_of_tail_reflector_self_dot_of_subtractZeroExact
        fp A (alpha 1) hdetFirst hdetTail hvecTail hselfTail hcopy
  exact hA2.trans hqr.symm

/-- Exact-arithmetic instance of the two-column recursive/stored bridge.

This is not the finite-precision source theorem; it records that the new named
copy-convention surface is strong enough to discharge the top-row-tail gate for
the exact model. -/
theorem qrPanel_R_two_col_eq_secondStoredStep_of_leadingBlock_det_ne_zero_exactWithUnitRoundoff
    (u0 : Real) (hu0 : 0 <= u0) {m : Nat}
    (A : Fin (m + 2) -> Fin 2 -> Real)
    (hdetFirst :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le (m + 1)))
          (Nat.succ_pos 1) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let fp := FPModel.exactWithUnitRoundoff u0 hu0
           let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
              (panelFirstColumn (Nat.succ_pos 1) A)
           let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1 A
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0) :
    fl_householderQRPanel_R (FPModel.exactWithUnitRoundoff u0 hu0)
        (m + 2) 2 A =
      (let fp := FPModel.exactWithUnitRoundoff u0 hu0
       let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1) A)
       let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1 A
       let v1 := fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))
       fl_householderStoredPanelStep fp (m + 2) 2 1 (Fin.cases 0 v1) 1 S0) := by
  let fp : FPModel := FPModel.exactWithUnitRoundoff u0 hu0
  exact
    qrPanel_R_two_col_eq_secondStoredStep_of_leadingBlock_det_ne_zero_of_subtractZeroExact
      fp A hdetFirst hdetTail
      (subtractZeroExact_exactWithUnitRoundoff u0 hu0)

/-- Arbitrary-width two-step recursive/stored bridge under exact
subtract-zero copy.

This is the first induction-shaped version of the terminal two-column bridge:
after the first two determinant-selected recursive branches, the recursive QR
panel is reconstructed from the full second stored panel and the remaining
recursive QR on the twice-shrunk trailing panel.  The statement still leaves
the later-pivot reflector-data induction open, but it removes the endpoint
width restriction from the two-step storage shape. -/
theorem
    qrPanel_R_succ_succ_eq_secondStoredStep_trailingQR_of_leadingBlock_det_ne_zero_of_fl_sub_zero
    (fp : FPModel) {m p : Nat}
    (A : Fin (m + 2) -> Fin (p + 2) -> Real)
    (hdetFirst :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le (m + 1)))
          (Nat.succ_pos (p + 1)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
              (panelFirstColumn (Nat.succ_pos (p + 1)) A)
           let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1 A
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos p) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hsubZero : (x : Real) -> fp.fl_sub x 0 = x) :
    fl_householderQRPanel_R fp (m + 2) (p + 2) A =
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1)) A)
       let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1 A
       let v1 := fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
       let Sfull :=
          fl_householderStoredPanelStep fp (m + 2) (p + 2) 1
            (Fin.cases 0 v1) 1 S0
       panelFromTopAndTrailing (panelTopLeft Sfull) (panelTopRowTail Sfull)
        (panelFromTopAndTrailing
          (panelTopLeft (trailingPanel Sfull))
          (panelTopRowTail (trailingPanel Sfull))
          (fl_householderQRPanel_R fp m p
            (trailingPanel (trailingPanel Sfull))))) := by
  let v0 : Fin (m + 2) -> Real :=
    fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
      (panelFirstColumn (Nat.succ_pos (p + 1)) A)
  let S0 : Fin (m + 2) -> Fin (p + 2) -> Real :=
    fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1 A
  let v1 : Fin (m + 1) -> Real :=
    fl_householderNormalizedVector fp (Nat.succ_pos m)
      (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
  let S1 : Fin (m + 1) -> Fin (p + 1) -> Real :=
    fl_householderStoredPanelStep fp (m + 1) (p + 1) 0 v1 1
      (trailingPanel S0)
  let Sfull : Fin (m + 2) -> Fin (p + 2) -> Real :=
    fl_householderStoredPanelStep fp (m + 2) (p + 2) 1
      (Fin.cases 0 v1) 1 S0
  have hfirst :=
    qrPanel_R_eq_firstStoredPanelStep_of_first_leadingBlock_det_ne_zero
      (fp := fp) (m := m + 1) (p := p + 1) A hdetFirst
  have htail :=
    qrPanel_R_eq_firstStoredPanelStep_of_first_leadingBlock_det_ne_zero
      (fp := fp) (m := m) (p := p) (trailingPanel S0) hdetTail
  have hSfull :
      Sfull = panelFromTopAndTrailing (panelTopLeft S0) (panelTopRowTail S0) S1 := by
    dsimp [Sfull, S1]
    exact
      storedPanelStep_succ_zeroPrefix_eq_panelFromTopAndTrailing_of_fl_sub_zero_anyCols
        fp v1 1 S0
        (panelFirstColumnTailZero_firstStoredPanelStep fp v0 1 A)
        hsubZero
  dsimp [v0, S0] at hfirst
  dsimp [v0, S0, v1, S1] at htail
  dsimp [v0, S0, v1, Sfull]
  rw [hfirst]
  change panelFromTopAndTrailing (panelTopLeft S0) (panelTopRowTail S0)
      (fl_householderQRPanel_R fp (m + 1) (p + 1) (trailingPanel S0)) =
    panelFromTopAndTrailing (panelTopLeft Sfull) (panelTopRowTail Sfull)
      (panelFromTopAndTrailing
        (panelTopLeft (trailingPanel Sfull))
        (panelTopRowTail (trailingPanel Sfull))
        (fl_householderQRPanel_R fp m p
          (trailingPanel (trailingPanel Sfull))))
  rw [htail]
  rw [hSfull]
  simp [v0, S0, v1, S1]

/-- Arbitrary-width two-step recursive/stored bridge using the named
subtract-zero exact-copy convention. -/
theorem
    qrPanel_R_succ_succ_eq_secondStoredStep_trailingQR_of_leadingBlock_det_ne_zero_of_subtractZeroExact
    (fp : FPModel) {m p : Nat}
    (A : Fin (m + 2) -> Fin (p + 2) -> Real)
    (hdetFirst :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le (m + 1)))
          (Nat.succ_pos (p + 1)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
              (panelFirstColumn (Nat.succ_pos (p + 1)) A)
           let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1 A
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos p) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hcopy : subtractZeroExact fp) :
    fl_householderQRPanel_R fp (m + 2) (p + 2) A =
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1)) A)
       let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1 A
       let v1 := fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
       let Sfull :=
          fl_householderStoredPanelStep fp (m + 2) (p + 2) 1
            (Fin.cases 0 v1) 1 S0
       panelFromTopAndTrailing (panelTopLeft Sfull) (panelTopRowTail Sfull)
        (panelFromTopAndTrailing
          (panelTopLeft (trailingPanel Sfull))
          (panelTopRowTail (trailingPanel Sfull))
          (fl_householderQRPanel_R fp m p
            (trailingPanel (trailingPanel Sfull))))) :=
  qrPanel_R_succ_succ_eq_secondStoredStep_trailingQR_of_leadingBlock_det_ne_zero_of_fl_sub_zero
    fp A hdetFirst hdetTail hcopy

/-- Arbitrary-width recursive/stored bridge with actual pivot-1 active-vector
data.

This generalizes the terminal two-column actual-data bridge to the induction
shape used by the full panel recursion.  The second stored step is the stored
loop's own successor-pivot active vector with beta one, while the trailing
subproblem remains the recursive QR panel on the twice-shrunk stored panel. -/
theorem
    qrPanel_R_succ_succ_eq_secondStoredActiveStep_trailingQR_of_tail_reflector_self_dot_of_subtractZeroExact
    (fp : FPModel) {m p : Nat}
    (A : Fin (m + 2) -> Fin (p + 2) -> Real) (alpha : Real)
    (hdetFirst :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le (m + 1)))
          (Nat.succ_pos (p + 1)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
              (panelFirstColumn (Nat.succ_pos (p + 1)) A)
           let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1 A
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos p) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTail :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1)) A)
       let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1 A
       householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
            (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0)) alpha =
          fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))))
    (hselfTail :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1)) A)
       let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1 A
       (Finset.univ : Finset (Fin (m + 1))).sum
          (fun i =>
            householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0)) alpha i *
              householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0)) alpha i) =
        2))
    (hcopy : subtractZeroExact fp) :
    fl_householderQRPanel_R fp (m + 2) (p + 2) A =
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1)) A)
       let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1 A
       let Sfull :=
          fl_householderStoredPanelStep fp (m + 2) (p + 2) 1
            (householderTrailingActiveVector (m + 2) ((0 : Fin (m + 1)).succ)
              (fun a => S0 a ((0 : Fin (p + 1)).succ)) alpha)
            1 S0
       panelFromTopAndTrailing (panelTopLeft Sfull) (panelTopRowTail Sfull)
        (panelFromTopAndTrailing
          (panelTopLeft (trailingPanel Sfull))
          (panelTopRowTail (trailingPanel Sfull))
          (fl_householderQRPanel_R fp m p
            (trailingPanel (trailingPanel Sfull))))) := by
  let v0 : Fin (m + 2) -> Real :=
    fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
      (panelFirstColumn (Nat.succ_pos (p + 1)) A)
  let S0 : Fin (m + 2) -> Fin (p + 2) -> Real :=
    fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1 A
  let vTail : Fin (m + 1) -> Real :=
    householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
      (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0)) alpha
  let v1 : Fin (m + 1) -> Real :=
    fl_householderNormalizedVector fp (Nat.succ_pos m)
      (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
  let S1Tail : Fin (m + 1) -> Fin (p + 1) -> Real :=
    fl_householderStoredPanelStep fp (m + 1) (p + 1) 0 vTail 1
      (trailingPanel S0)
  let S1Norm : Fin (m + 1) -> Fin (p + 1) -> Real :=
    fl_householderStoredPanelStep fp (m + 1) (p + 1) 0 v1 1
      (trailingPanel S0)
  let SfullNorm : Fin (m + 2) -> Fin (p + 2) -> Real :=
    fl_householderStoredPanelStep fp (m + 2) (p + 2) 1
      (Fin.cases 0 v1) 1 S0
  let SfullActive : Fin (m + 2) -> Fin (p + 2) -> Real :=
    fl_householderStoredPanelStep fp (m + 2) (p + 2) 1
      (householderTrailingActiveVector (m + 2) ((0 : Fin (m + 1)).succ)
        (fun a => S0 a ((0 : Fin (p + 1)).succ)) alpha) 1 S0
  have hqr :=
    qrPanel_R_succ_succ_eq_secondStoredStep_trailingQR_of_leadingBlock_det_ne_zero_of_subtractZeroExact
      fp A hdetFirst hdetTail hcopy
  have hvecTail' : vTail = v1 := by
    dsimp [vTail, v1]
    simpa [v0, S0] using hvecTail
  have hS1 : S1Tail = S1Norm := by
    dsimp [S1Tail, S1Norm]
    rw [hvecTail']
  have hfullActive :
      SfullActive =
        panelFromTopAndTrailing (panelTopLeft S0) (panelTopRowTail S0) S1Tail := by
    dsimp [SfullActive, S1Tail, vTail]
    exact
      storedPanelStep_succ_trailingActiveVector_one_eq_panelFromTopAndTrailing_one_of_tail_self_dot_of_subtractZeroExact_anyCols
        fp S0 alpha
        (by simpa [v0, S0] using hselfTail)
        (panelFirstColumnTailZero_firstStoredPanelStep fp v0 1 A)
        hcopy
  have hfullNorm :
      SfullNorm =
        panelFromTopAndTrailing (panelTopLeft S0) (panelTopRowTail S0) S1Norm := by
    dsimp [SfullNorm, S1Norm]
    exact
      storedPanelStep_succ_zeroPrefix_eq_panelFromTopAndTrailing_of_subtractZeroExact_anyCols
        fp v1 1 S0
        (panelFirstColumnTailZero_firstStoredPanelStep fp v0 1 A)
        hcopy
  have hSfull : SfullNorm = SfullActive := by
    calc
      SfullNorm =
          panelFromTopAndTrailing (panelTopLeft S0) (panelTopRowTail S0) S1Norm :=
        hfullNorm
      _ = panelFromTopAndTrailing (panelTopLeft S0) (panelTopRowTail S0) S1Tail := by
        simp [hS1]
      _ = SfullActive := hfullActive.symm
  have hqr' :
      fl_householderQRPanel_R fp (m + 2) (p + 2) A =
        panelFromTopAndTrailing (panelTopLeft SfullNorm) (panelTopRowTail SfullNorm)
          (panelFromTopAndTrailing
            (panelTopLeft (trailingPanel SfullNorm))
            (panelTopRowTail (trailingPanel SfullNorm))
            (fl_householderQRPanel_R fp m p
              (trailingPanel (trailingPanel SfullNorm)))) := by
    simpa [v0, S0, v1, SfullNorm] using hqr
  have htailExpr :
      panelFromTopAndTrailing (panelTopLeft SfullNorm) (panelTopRowTail SfullNorm)
          (panelFromTopAndTrailing
            (panelTopLeft (trailingPanel SfullNorm))
            (panelTopRowTail (trailingPanel SfullNorm))
            (fl_householderQRPanel_R fp m p
              (trailingPanel (trailingPanel SfullNorm)))) =
        panelFromTopAndTrailing (panelTopLeft SfullActive) (panelTopRowTail SfullActive)
          (panelFromTopAndTrailing
            (panelTopLeft (trailingPanel SfullActive))
            (panelTopRowTail (trailingPanel SfullActive))
            (fl_householderQRPanel_R fp m p
              (trailingPanel (trailingPanel SfullActive)))) := by
    simp [hSfull]
  simpa [v0, S0, SfullActive] using hqr'.trans htailExpr

/-- Arbitrary-width two-step signed stored-sequence bridge.

This is the source-recurrence half of the two-step final-panel induction
shape.  Under the source step equation, first-reflector identification, and
source self-dot normalizations for the first two active reflectors, the stored
sequence after two steps is exactly the full second active stored step. -/
theorem storedSignedSequence_two_step_eq_secondStoredActiveStep_of_reflector_self_dot
    (fp : FPModel) {m p : Nat}
    (A : Fin (m + 2) -> Fin (p + 2) -> Real)
    (A_hat : Nat -> Fin (m + 2) -> Fin (p + 2) -> Real)
    (alpha : Nat -> Real)
    (hrows : 2 <= m + 2)
    (hcols : 2 <= p + 2)
    (hinit : A_hat 0 = A)
    (hStep : forall k (hk : k < 2),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (m + 2) (p + 2) k
          (householderTrailingActiveVector (m + 2)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun a => A_hat k a (Fin.mk k (lt_of_lt_of_le hk hcols)))
            (alpha k))
          (householderBetaSpec (m + 2)
            (householderTrailingActiveVector (m + 2)
              (Fin.mk k (lt_of_lt_of_le hk hrows))
              (fun a => A_hat k a (Fin.mk k (lt_of_lt_of_le hk hcols)))
              (alpha k)))
          (A_hat k))
    (hvec0 :
      householderTrailingActiveVector (m + 2)
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
          (fun a =>
            A_hat 0 a
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
          (alpha 0) =
        fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1)) A))
    (hself0 :
      (Finset.univ : Finset (Fin (m + 2))).sum
        (fun i =>
          householderTrailingActiveVector (m + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
              (fun a =>
                A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
              (alpha 0) i *
            householderTrailingActiveVector (m + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
              (fun a =>
                A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
              (alpha 0) i) =
        2)
    (hselfTail :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1)) A)
       let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1 A
       (Finset.univ : Finset (Fin (m + 1))).sum
          (fun i =>
            householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
                (alpha 1) i *
              householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
                (alpha 1) i) =
        2)) :
    A_hat 2 =
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1)) A)
       let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1 A
       fl_householderStoredPanelStep fp (m + 2) (p + 2) 1
        (householderTrailingActiveVector (m + 2) ((0 : Fin (m + 1)).succ)
          (fun a => S0 a ((0 : Fin (p + 1)).succ)) (alpha 1))
        1 S0) := by
  let v0 : Fin (m + 2) -> Real :=
    fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
      (panelFirstColumn (Nat.succ_pos (p + 1)) A)
  let S0 : Fin (m + 2) -> Fin (p + 2) -> Real :=
    fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1 A
  let Sfull : Fin (m + 2) -> Fin (p + 2) -> Real :=
    fl_householderStoredPanelStep fp (m + 2) (p + 2) 1
      (householderTrailingActiveVector (m + 2) ((0 : Fin (m + 1)).succ)
        (fun a => S0 a ((0 : Fin (p + 1)).succ)) (alpha 1)) 1 S0
  have hbeta0 :
      householderBetaSpec (m + 2)
          (householderTrailingActiveVector (m + 2)
            (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
            (fun a =>
              A_hat 0 a
                (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
            (alpha 0)) =
        1 := by
    exact
      householderBetaSpec_eq_one_of_inner_self_eq_two (m + 2)
        (householderTrailingActiveVector (m + 2)
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
          (fun a =>
            A_hat 0 a
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
          (alpha 0))
        hself0
  have hA1 : A_hat 1 = S0 := by
    have h0 := hStep 0 (Nat.succ_pos 1)
    rw [h0, hbeta0, hvec0, hinit]
  have hrow1 :
      Fin.mk 1 (lt_of_lt_of_le (Nat.lt_succ_self 1) hrows) =
        ((0 : Fin (m + 1)).succ) := by
    ext
    rfl
  have hcol1 :
      Fin.mk 1 (lt_of_lt_of_le (Nat.lt_succ_self 1) hcols) =
        ((0 : Fin (p + 1)).succ) := by
    ext
    rfl
  have hbeta1Active :
      householderBetaSpec (m + 2)
          (householderTrailingActiveVector (m + 2) ((0 : Fin (m + 1)).succ)
            (fun a => S0 a ((0 : Fin (p + 1)).succ)) (alpha 1)) =
        1 := by
    exact
      householderBetaSpec_trailingActiveVector_succ_zeroPrefix_eq_one_of_tail_self_dot
        (0 : Fin (m + 1)) (fun a => S0 a ((0 : Fin (p + 1)).succ))
        (alpha 1)
        (by simpa [v0, S0, panelFirstColumn, trailingPanel] using hselfTail)
  have hA2 : A_hat 2 = Sfull := by
    have h1 := hStep 1 (Nat.lt_succ_self 1)
    rw [h1, hA1]
    rw [hrow1, hcol1, hbeta1Active]
  simpa [v0, S0, Sfull] using hA2

/-- Arbitrary-width QR recursion expressed through the first two stored source
steps.

This combines the source-recurrence two-step bridge with the QR-side
active-reflector theorem, leaving the remaining twice-shrunk QR panel explicit
for the full final-panel induction. -/
theorem
    qrPanel_R_succ_succ_eq_storedSignedSequence_two_step_trailingQR_of_reflector_self_dot_of_subtractZeroExact
    (fp : FPModel) {m p : Nat}
    (A : Fin (m + 2) -> Fin (p + 2) -> Real)
    (A_hat : Nat -> Fin (m + 2) -> Fin (p + 2) -> Real)
    (alpha : Nat -> Real)
    (hrows : 2 <= m + 2)
    (hcols : 2 <= p + 2)
    (hinit : A_hat 0 = A)
    (hStep : forall k (hk : k < 2),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (m + 2) (p + 2) k
          (householderTrailingActiveVector (m + 2)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun a => A_hat k a (Fin.mk k (lt_of_lt_of_le hk hcols)))
            (alpha k))
          (householderBetaSpec (m + 2)
            (householderTrailingActiveVector (m + 2)
              (Fin.mk k (lt_of_lt_of_le hk hrows))
              (fun a => A_hat k a (Fin.mk k (lt_of_lt_of_le hk hcols)))
              (alpha k)))
          (A_hat k))
    (hvec0 :
      householderTrailingActiveVector (m + 2)
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
          (fun a =>
            A_hat 0 a
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
          (alpha 0) =
        fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1)) A))
    (hself0 :
      (Finset.univ : Finset (Fin (m + 2))).sum
        (fun i =>
          householderTrailingActiveVector (m + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
              (fun a =>
                A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
              (alpha 0) i *
            householderTrailingActiveVector (m + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
              (fun a =>
                A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
              (alpha 0) i) =
        2)
    (hdetFirst :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le (m + 1)))
          (Nat.succ_pos (p + 1)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
              (panelFirstColumn (Nat.succ_pos (p + 1)) A)
           let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1 A
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos p) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTail :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1)) A)
       let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1 A
       householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
            (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0)) (alpha 1) =
          fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))))
    (hselfTail :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1)) A)
       let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1 A
       (Finset.univ : Finset (Fin (m + 1))).sum
          (fun i =>
            householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
                (alpha 1) i *
              householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
                (alpha 1) i) =
        2))
    (hcopy : subtractZeroExact fp) :
    fl_householderQRPanel_R fp (m + 2) (p + 2) A =
      panelFromTopAndTrailing (panelTopLeft (A_hat 2))
        (panelTopRowTail (A_hat 2))
        (panelFromTopAndTrailing
          (panelTopLeft (trailingPanel (A_hat 2)))
          (panelTopRowTail (trailingPanel (A_hat 2)))
          (fl_householderQRPanel_R fp m p
            (trailingPanel (trailingPanel (A_hat 2))))) := by
  have hA2 :
      A_hat 2 =
        (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
            (panelFirstColumn (Nat.succ_pos (p + 1)) A)
         let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1 A
         fl_householderStoredPanelStep fp (m + 2) (p + 2) 1
          (householderTrailingActiveVector (m + 2) ((0 : Fin (m + 1)).succ)
            (fun a => S0 a ((0 : Fin (p + 1)).succ)) (alpha 1))
          1 S0) :=
    storedSignedSequence_two_step_eq_secondStoredActiveStep_of_reflector_self_dot
      fp A A_hat alpha hrows hcols hinit hStep hvec0 hself0 hselfTail
  have hqr :=
    qrPanel_R_succ_succ_eq_secondStoredActiveStep_trailingQR_of_tail_reflector_self_dot_of_subtractZeroExact
      fp A (alpha 1) hdetFirst hdetTail hvecTail hselfTail hcopy
  simpa [hA2] using hqr

/-- Source-recurrence final-panel bridge with the two-step QR side discharged.

Compared with
`storedSignedSequence_final_panel_eq_qrPanel_R_of_two_step_qrPanel_R_of_twice_trailing_final`,
this supplies the two-step recursive/stored QR expression from the signed
source recurrence, first-reflector data, and first two reflector self-dot
normalizations.  The remaining premise is exactly the recursive equality for the
twice-trailing panel. -/
theorem
    storedSignedSequence_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_twice_trailing_final
    (fp : FPModel) {m p : Nat}
    (hmn : p + 2 <= m + 2)
    (A : Fin (m + 2) -> Fin (p + 2) -> Real)
    (A_hat : Nat -> Fin (m + 2) -> Fin (p + 2) -> Real)
    (alpha : Nat -> Real)
    (hrows : 2 <= m + 2)
    (hcols : 2 <= p + 2)
    (hinit : A_hat 0 = A)
    (hStep : forall k (hk : k < p + 2),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (m + 2) (p + 2) k
          (householderTrailingActiveVector (m + 2)
            (Fin.mk k (lt_of_lt_of_le hk hmn))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (m + 2)
            (householderTrailingActiveVector (m + 2)
              (Fin.mk k (lt_of_lt_of_le hk hmn))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (hvec0 :
      householderTrailingActiveVector (m + 2)
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
          (fun a =>
            A_hat 0 a
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
          (alpha 0) =
        fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1)) A))
    (hself0 :
      (Finset.univ : Finset (Fin (m + 2))).sum
        (fun i =>
          householderTrailingActiveVector (m + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
              (fun a =>
                A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
              (alpha 0) i *
            householderTrailingActiveVector (m + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
              (fun a =>
                A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
              (alpha 0) i) =
        2)
    (hdetFirst :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le (m + 1)))
          (Nat.succ_pos (p + 1)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
              (panelFirstColumn (Nat.succ_pos (p + 1)) A)
           let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1 A
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos p) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTail :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1)) A)
       let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1 A
       householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
            (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0)) (alpha 1) =
          fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))))
    (hselfTail :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1)) A)
       let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1 A
       (Finset.univ : Finset (Fin (m + 1))).sum
          (fun i =>
            householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
                (alpha 1) i *
              householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
                (alpha 1) i) =
        2))
    (hcopy : subtractZeroExact fp)
    (hTailFinal :
      trailingPanel (trailingPanel (A_hat (p + 2))) =
        fl_householderQRPanel_R fp m p
          (trailingPanel (trailingPanel (A_hat 2)))) :
    A_hat (p + 2) =
      fl_householderQRPanel_R fp (m + 2) (p + 2) A := by
  have hStepTwo : forall k (hk : k < 2),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (m + 2) (p + 2) k
          (householderTrailingActiveVector (m + 2)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun a => A_hat k a (Fin.mk k (lt_of_lt_of_le hk hcols)))
            (alpha k))
          (householderBetaSpec (m + 2)
            (householderTrailingActiveVector (m + 2)
              (Fin.mk k (lt_of_lt_of_le hk hrows))
              (fun a => A_hat k a (Fin.mk k (lt_of_lt_of_le hk hcols)))
              (alpha k)))
          (A_hat k) := by
    intro k hk
    simpa using hStep k (lt_of_lt_of_le hk hcols)
  have hQR2 :=
    qrPanel_R_succ_succ_eq_storedSignedSequence_two_step_trailingQR_of_reflector_self_dot_of_subtractZeroExact
      fp A A_hat alpha hrows hcols hinit hStepTwo hvec0 hself0
      hdetFirst hdetTail hvecTail hselfTail hcopy
  exact
    storedSignedSequence_final_panel_eq_qrPanel_R_of_two_step_qrPanel_R_of_twice_trailing_final
      fp hmn A A_hat alpha hStep hcopy hQR2 hTailFinal

/-- The twice-trailing panels of a signed stored-QR source recurrence form the
same signed stored-QR recurrence on the twice-shrunk panel.

This is the induction-step handoff needed by the remaining final-panel bridge:
the full pivot `k + 2` source step becomes the pivot `k` stored step after the
first two completed rows and columns are removed. -/
theorem storedSignedSequence_twice_trailing_step_of_source_step
    (fp : FPModel) {m p : Nat}
    (hmn : p + 2 <= m + 2)
    (A_hat : Nat -> Fin (m + 2) -> Fin (p + 2) -> Real)
    (alpha : Nat -> Real)
    (hStep : forall k (hk : k < p + 2),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (m + 2) (p + 2) k
          (householderTrailingActiveVector (m + 2)
            (Fin.mk k (lt_of_lt_of_le hk hmn))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (m + 2)
            (householderTrailingActiveVector (m + 2)
              (Fin.mk k (lt_of_lt_of_le hk hmn))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (k : Nat) (hk : k < p) :
    trailingPanel (trailingPanel (A_hat ((k + 2) + 1))) =
      fl_householderStoredPanelStep fp m p k
        (householderTrailingActiveVector m
          (Fin.mk k (by omega))
          (fun a => trailingPanel (trailingPanel (A_hat (k + 2))) a
            (Fin.mk k hk)) (alpha (k + 2)))
        (householderBetaSpec m
          (householderTrailingActiveVector m
            (Fin.mk k (by omega))
            (fun a => trailingPanel (trailingPanel (A_hat (k + 2))) a
              (Fin.mk k hk)) (alpha (k + 2))))
        (trailingPanel (trailingPanel (A_hat (k + 2)))) := by
  have hkfull : k + 2 < p + 2 := by omega
  let q : Fin m := Fin.mk k (by omega)
  let tailCol : Fin p := Fin.mk k hk
  have hrow : Fin.mk (k + 2) (lt_of_lt_of_le hkfull hmn) = q.succ.succ := by
    ext
    simp [q]
  have hcol : Fin.mk (k + 2) hkfull = tailCol.succ.succ := by
    ext
    simp [tailCol]
  have hstep := hStep (k + 2) hkfull
  rw [hstep]
  rw [hrow, hcol]
  simpa only [q, tailCol]
    using
      trailingPanel_trailingPanel_storedPanelStep_succ_succ_trailingActiveVector_eq_storedPanelStep_trailingPanel_trailingPanel_of_succ_succ
        (fp := fp) (m := m) (p := p) q hk (A_hat (k + 2)) (alpha (k + 2))

/-- Sequence-shaped form of the twice-trailing source-step bridge.

This packages `storedSignedSequence_twice_trailing_step_of_source_step` in the
same recurrence surface expected by a recursive final-panel induction on the
twice-shrunk panel. -/
theorem storedSignedSequence_twice_trailing_source_recurrence_of_source_step
    (fp : FPModel) {m p : Nat}
    (hmn : p + 2 <= m + 2)
    (A_hat : Nat -> Fin (m + 2) -> Fin (p + 2) -> Real)
    (alpha : Nat -> Real)
    (hStep : forall k (hk : k < p + 2),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (m + 2) (p + 2) k
          (householderTrailingActiveVector (m + 2)
            (Fin.mk k (lt_of_lt_of_le hk hmn))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (m + 2)
            (householderTrailingActiveVector (m + 2)
              (Fin.mk k (lt_of_lt_of_le hk hmn))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (k : Nat) (hk : k < p) :
    (fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) (k + 1) =
      fl_householderStoredPanelStep fp m p k
        (householderTrailingActiveVector m
          (Fin.mk k (by omega))
          (fun a => (fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) k a
            (Fin.mk k hk)) (alpha (k + 2)))
        (householderBetaSpec m
          (householderTrailingActiveVector m
            (Fin.mk k (by omega))
            (fun a => (fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) k a
              (Fin.mk k hk)) (alpha (k + 2))))
        ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) k) := by
  have h :=
    storedSignedSequence_twice_trailing_step_of_source_step
      fp hmn A_hat alpha hStep k hk
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- One-column final-panel closure for the twice-trailing tail sequence.

This is the base case needed after two leading stored steps have been peeled
off: if the twice-trailing recurrence has one remaining column, the existing
one-column recursive/stored bridge closes the tail final-panel obligation. -/
theorem storedSignedSequence_twice_trailing_one_col_tail_final_of_tail_reflector_self_dot
    (fp : FPModel) {m : Nat}
    (A_hat : Nat -> Fin ((m + 1) + 2) -> Fin (1 + 2) -> Real)
    (alpha : Nat -> Real)
    (hTailRec : forall k (hk : k < 1),
      (fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) (k + 1) =
        fl_householderStoredPanelStep fp (m + 1) 1 k
          (householderTrailingActiveVector (m + 1)
            (Fin.mk k (by omega))
            (fun a => (fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) k a
              (Fin.mk k hk)) (alpha (k + 2)))
          (householderBetaSpec (m + 1)
            (householderTrailingActiveVector (m + 1)
              (Fin.mk k (by omega))
              (fun a => (fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) k a
                (Fin.mk k hk)) (alpha (k + 2))))
          ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) k))
    (hvecTailTail :
      householderTrailingActiveVector (m + 1)
          (Fin.mk 0 (Nat.succ_pos m))
          (fun a =>
            trailingPanel (trailingPanel (A_hat 2)) a
              (Fin.mk 0 (Nat.succ_pos 0)))
          (alpha 2) =
        fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos 0)
            (trailingPanel (trailingPanel (A_hat 2)))))
    (hselfTailTail :
      (Finset.univ : Finset (Fin (m + 1))).sum
        (fun i =>
          householderTrailingActiveVector (m + 1)
              (Fin.mk 0 (Nat.succ_pos m))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (Nat.succ_pos 0)))
              (alpha 2) i *
            householderTrailingActiveVector (m + 1)
              (Fin.mk 0 (Nat.succ_pos m))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (Nat.succ_pos 0)))
              (alpha 2) i) =
        2)
    (hdetTailTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (trailingPanel (trailingPanel (A_hat 2)))
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0) :
    trailingPanel (trailingPanel (A_hat (1 + 2))) =
      fl_householderQRPanel_R fp (m + 1) 1
        (trailingPanel (trailingPanel (A_hat 2))) := by
  let TailSeq : Nat -> Fin (m + 1) -> Fin 1 -> Real :=
    fun t => trailingPanel (trailingPanel (A_hat (t + 2)))
  let TailAlpha : Nat -> Real := fun t => alpha (t + 2)
  have hTailStep : forall k (hk : k < 1),
      TailSeq (k + 1) =
        fl_householderStoredPanelStep fp (m + 1) 1 k
          (householderTrailingActiveVector (m + 1)
            (Fin.mk k
              (lt_of_lt_of_le hk (Nat.succ_le_succ (Nat.zero_le m))))
            (fun a => TailSeq k a (Fin.mk k hk)) (TailAlpha k))
          (householderBetaSpec (m + 1)
            (householderTrailingActiveVector (m + 1)
              (Fin.mk k
                (lt_of_lt_of_le hk (Nat.succ_le_succ (Nat.zero_le m))))
              (fun a => TailSeq k a (Fin.mk k hk)) (TailAlpha k)))
          (TailSeq k) := by
    intro k hk
    simpa [TailSeq, TailAlpha] using hTailRec k hk
  have htail :=
    storedSignedSequence_one_col_final_panel_eq_qrPanel_R_of_reflector_self_dot
      fp (TailSeq 0) TailSeq TailAlpha rfl hTailStep
      (by
        simpa [TailSeq, TailAlpha] using hvecTailTail)
      (by
        simpa [TailSeq, TailAlpha] using hselfTailTail)
      (by
        simpa [TailSeq] using hdetTailTail)
  simpa [TailSeq] using htail

/-- Two-column final-panel closure for the twice-trailing tail sequence.

This is the next recursive base after two leading stored steps have been peeled
off: if the twice-trailing recurrence has two columns left, the existing
two-column recursive/stored bridge closes the tail final-panel obligation. -/
theorem storedSignedSequence_twice_trailing_two_col_tail_final_of_tail_reflector_self_dot
    (fp : FPModel) {m : Nat}
    (A_hat : Nat -> Fin ((m + 2) + 2) -> Fin (2 + 2) -> Real)
    (alpha : Nat -> Real)
    (hTailRec : forall k (hk : k < 2),
      (fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) (k + 1) =
        fl_householderStoredPanelStep fp (m + 2) 2 k
          (householderTrailingActiveVector (m + 2)
            (Fin.mk k (by omega))
            (fun a => (fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) k a
              (Fin.mk k hk)) (alpha (k + 2)))
          (householderBetaSpec (m + 2)
            (householderTrailingActiveVector (m + 2)
              (Fin.mk k (by omega))
              (fun a => (fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) k a
                (Fin.mk k hk)) (alpha (k + 2))))
          ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) k))
    (hvecTailTail0 :
      householderTrailingActiveVector (m + 2)
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
          (fun a =>
            trailingPanel (trailingPanel (A_hat 2)) a
              (Fin.mk 0 (Nat.succ_pos 1)))
          (alpha 2) =
        fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1)
            (trailingPanel (trailingPanel (A_hat 2)))))
    (hselfTailTail0 :
      (Finset.univ : Finset (Fin (m + 2))).sum
        (fun i =>
          householderTrailingActiveVector (m + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (Nat.succ_pos 1)))
              (alpha 2) i *
            householderTrailingActiveVector (m + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (Nat.succ_pos 1)))
              (alpha 2) i) =
        2)
    (hdetTailTailFirst :
      Ne (Matrix.det
        (qrLeadingBlock
          (trailingPanel (trailingPanel (A_hat 2)))
          (Nat.succ_le_succ (Nat.zero_le (m + 1)))
          (Nat.succ_pos 1) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTailTailTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
              (panelFirstColumn (Nat.succ_pos 1)
                (trailingPanel (trailingPanel (A_hat 2))))
           let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1
              (trailingPanel (trailingPanel (A_hat 2)))
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTailTail1 :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1)
            (trailingPanel (trailingPanel (A_hat 2))))
       let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1
          (trailingPanel (trailingPanel (A_hat 2)))
       householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
            (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0)) (alpha 3) =
          fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))))
    (hselfTailTail1 :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1)
            (trailingPanel (trailingPanel (A_hat 2))))
       let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1
          (trailingPanel (trailingPanel (A_hat 2)))
       (Finset.univ : Finset (Fin (m + 1))).sum
          (fun i =>
            householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))
                (alpha 3) i *
              householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))
                (alpha 3) i) =
        2))
    (hcopy : subtractZeroExact fp) :
    trailingPanel (trailingPanel (A_hat (2 + 2))) =
      fl_householderQRPanel_R fp (m + 2) 2
        (trailingPanel (trailingPanel (A_hat 2))) := by
  let TailSeq : Nat -> Fin (m + 2) -> Fin 2 -> Real :=
    fun t => trailingPanel (trailingPanel (A_hat (t + 2)))
  let TailAlpha : Nat -> Real := fun t => alpha (t + 2)
  have hTailStep : forall k (hk : k < 2),
      TailSeq (k + 1) =
        fl_householderStoredPanelStep fp (m + 2) 2 k
          (householderTrailingActiveVector (m + 2)
            (Fin.mk k (lt_of_lt_of_le hk (by omega)))
            (fun a => TailSeq k a (Fin.mk k hk)) (TailAlpha k))
          (householderBetaSpec (m + 2)
            (householderTrailingActiveVector (m + 2)
              (Fin.mk k (lt_of_lt_of_le hk (by omega)))
              (fun a => TailSeq k a (Fin.mk k hk)) (TailAlpha k)))
          (TailSeq k) := by
    intro k hk
    simpa [TailSeq, TailAlpha] using hTailRec k hk
  have htail :=
    storedSignedSequence_two_col_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_subtractZeroExact
      fp (TailSeq 0) TailSeq TailAlpha (by omega) rfl hTailStep
      (by
        simpa [TailSeq, TailAlpha] using hvecTailTail0)
      (by
        simpa [TailSeq, TailAlpha] using hselfTailTail0)
      (by
        simpa [TailSeq] using hdetTailTailFirst)
      (by
        simpa [TailSeq] using hdetTailTailTail)
      (by
        simpa [TailSeq, TailAlpha] using hvecTailTail1)
      (by
        simpa [TailSeq, TailAlpha] using hselfTailTail1)
      hcopy
  simpa [TailSeq] using htail

/-- The twice-trailing source sequence obtained after peeling off two stored
Householder steps. -/
abbrev storedSignedSequenceTwiceTrailingSeq
    {m p : Nat}
    (A_hat : Nat -> Fin (m + 2) -> Fin (p + 2) -> Real) :
    Nat -> Fin m -> Fin p -> Real :=
  fun t => trailingPanel (trailingPanel (A_hat (t + 2)))

/-- The matching two-step-shifted signed-reflector scalar sequence. -/
abbrev storedSignedSequenceTailAlpha2 (alpha : Nat -> Real) : Nat -> Real :=
  fun t => alpha (t + 2)

/-- First-two-step reflector data for a stored signed sequence.

This is the reusable local contract needed by the recursive final-panel
closure step: the first two stored reflectors of a sequence agree with the
recursive QR normalized reflectors, their source self-dot normalizations give
beta one, and the two determinant premises select the nonzero recursive
branches. -/
structure storedSignedSequenceFirstTwoReflectorData
    (fp : FPModel) {m p : Nat}
    (S : Nat -> Fin (m + 2) -> Fin (p + 2) -> Real)
    (alpha : Nat -> Real) : Prop where
  hvec0 :
    householderTrailingActiveVector (m + 2)
        (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
        (fun a => S 0 a (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega))))
        (alpha 0) =
      fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
        (panelFirstColumn (Nat.succ_pos (p + 1)) (S 0))
  hself0 :
    (Finset.univ : Finset (Fin (m + 2))).sum
      (fun i =>
        householderTrailingActiveVector (m + 2)
            (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
            (fun a => S 0 a
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega))))
            (alpha 0) i *
          householderTrailingActiveVector (m + 2)
            (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
            (fun a => S 0 a
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega))))
            (alpha 0) i) =
      2
  hdetFirst :
    Ne (Matrix.det
      (qrLeadingBlock (S 0)
        (Nat.succ_le_succ (Nat.zero_le (m + 1)))
        (Nat.succ_pos (p + 1)) :
        Matrix (Fin 1) (Fin 1) Real))
      0
  hdetTail :
    Ne (Matrix.det
      (qrLeadingBlock
        (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
            (panelFirstColumn (Nat.succ_pos (p + 1)) (S 0))
         let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1
            (S 0)
         trailingPanel S0)
        (Nat.succ_le_succ (Nat.zero_le m))
        (Nat.succ_pos p) :
        Matrix (Fin 1) (Fin 1) Real))
      0
  hvecTail :
    (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
        (panelFirstColumn (Nat.succ_pos (p + 1)) (S 0))
     let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1
        (S 0)
     householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
          (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
          (alpha 1) =
        fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0)))
  hselfTail :
    (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
        (panelFirstColumn (Nat.succ_pos (p + 1)) (S 0))
     let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1
        (S 0)
     (Finset.univ : Finset (Fin (m + 1))).sum
        (fun i =>
          householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
              (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
              (alpha 1) i *
            householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
              (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
              (alpha 1) i) =
      2)

/-- One-step reflector data for a one-column signed stored sequence.

This is the odd-width base counterpart to
`storedSignedSequenceFirstTwoReflectorData`: once the twice-trailing tail has one
column left, only its first reflector data and determinant branch are needed to
close the final-panel equality. -/
structure storedSignedSequenceOneReflectorData
    (fp : FPModel) {m : Nat}
    (S : Nat -> Fin (m + 1) -> Fin 1 -> Real)
    (alpha : Nat -> Real) : Prop where
  hvec0 :
    householderTrailingActiveVector (m + 1)
        (Fin.mk 0 (Nat.succ_pos m))
        (fun a => S 0 a (Fin.mk 0 (Nat.succ_pos 0)))
        (alpha 0) =
      fl_householderNormalizedVector fp (Nat.succ_pos m)
        (panelFirstColumn (Nat.succ_pos 0) (S 0))
  hself0 :
    (Finset.univ : Finset (Fin (m + 1))).sum
      (fun i =>
        householderTrailingActiveVector (m + 1)
            (Fin.mk 0 (Nat.succ_pos m))
            (fun a => S 0 a (Fin.mk 0 (Nat.succ_pos 0)))
            (alpha 0) i *
          householderTrailingActiveVector (m + 1)
            (Fin.mk 0 (Nat.succ_pos m))
            (fun a => S 0 a (Fin.mk 0 (Nat.succ_pos 0)))
            (alpha 0) i) =
      2
  hdetFirst :
    Ne (Matrix.det
      (qrLeadingBlock (S 0)
        (Nat.succ_le_succ (Nat.zero_le m))
        (Nat.succ_pos 0) :
        Matrix (Fin 1) (Fin 1) Real))
      0

/-- Package explicit one-column twice-trailing reflector facts as one-reflector
data for the recursive closure contract. -/
theorem storedSignedSequenceOneReflectorData_of_tail_reflector_self_dot
    (fp : FPModel) {m : Nat}
    (A_hat : Nat -> Fin ((m + 1) + 2) -> Fin (1 + 2) -> Real)
    (alpha : Nat -> Real)
    (hvecTailTail :
      householderTrailingActiveVector (m + 1)
          (Fin.mk 0 (Nat.succ_pos m))
          (fun a =>
            trailingPanel (trailingPanel (A_hat 2)) a
              (Fin.mk 0 (Nat.succ_pos 0)))
          (alpha 2) =
        fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos 0)
            (trailingPanel (trailingPanel (A_hat 2)))))
    (hselfTailTail :
      (Finset.univ : Finset (Fin (m + 1))).sum
        (fun i =>
          householderTrailingActiveVector (m + 1)
              (Fin.mk 0 (Nat.succ_pos m))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (Nat.succ_pos 0)))
              (alpha 2) i *
            householderTrailingActiveVector (m + 1)
              (Fin.mk 0 (Nat.succ_pos m))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (Nat.succ_pos 0)))
              (alpha 2) i) =
        2)
    (hdetTailTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (trailingPanel (trailingPanel (A_hat 2)))
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0) :
    storedSignedSequenceOneReflectorData fp
      (storedSignedSequenceTwiceTrailingSeq A_hat)
      (storedSignedSequenceTailAlpha2 alpha) := by
  refine { hvec0 := ?_, hself0 := ?_, hdetFirst := ?_ }
  · simpa [storedSignedSequenceTwiceTrailingSeq, storedSignedSequenceTailAlpha2]
      using hvecTailTail
  · simpa [storedSignedSequenceTwiceTrailingSeq, storedSignedSequenceTailAlpha2]
      using hselfTailTail
  · simpa [storedSignedSequenceTwiceTrailingSeq] using hdetTailTail

/-- Package explicit twice-trailing tail reflector facts as first-two data for
the recursive closure contract. -/
theorem storedSignedSequenceFirstTwoReflectorData_of_tail_reflector_self_dot
    (fp : FPModel) {m p : Nat}
    (A_hat : Nat -> Fin ((m + 2) + 2) -> Fin ((p + 2) + 2) -> Real)
    (alpha : Nat -> Real)
    (hvecTailTail0 :
      householderTrailingActiveVector (m + 2)
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
          (fun a =>
            trailingPanel (trailingPanel (A_hat 2)) a
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega))))
          (alpha 2) =
        fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1))
            (trailingPanel (trailingPanel (A_hat 2)))))
    (hselfTailTail0 :
      (Finset.univ : Finset (Fin (m + 2))).sum
        (fun i =>
          householderTrailingActiveVector (m + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega))))
              (alpha 2) i *
            householderTrailingActiveVector (m + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega))))
              (alpha 2) i) =
        2)
    (hdetTailTailFirst :
      Ne (Matrix.det
        (qrLeadingBlock
          (trailingPanel (trailingPanel (A_hat 2)))
          (Nat.succ_le_succ (Nat.zero_le (m + 1)))
          (Nat.succ_pos (p + 1)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTailTailTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
              (panelFirstColumn (Nat.succ_pos (p + 1))
                (trailingPanel (trailingPanel (A_hat 2))))
           let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1
              (trailingPanel (trailingPanel (A_hat 2)))
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos p) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTailTail1 :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1))
            (trailingPanel (trailingPanel (A_hat 2))))
       let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1
          (trailingPanel (trailingPanel (A_hat 2)))
       householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
            (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0)) (alpha 3) =
          fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))))
    (hselfTailTail1 :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1))
            (trailingPanel (trailingPanel (A_hat 2))))
       let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1
          (trailingPanel (trailingPanel (A_hat 2)))
       (Finset.univ : Finset (Fin (m + 1))).sum
          (fun i =>
            householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
                (alpha 3) i *
              householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
                (alpha 3) i) =
        2)) :
    storedSignedSequenceFirstTwoReflectorData fp
      (storedSignedSequenceTwiceTrailingSeq A_hat)
      (storedSignedSequenceTailAlpha2 alpha) := by
  refine
    { hvec0 := ?_
      hself0 := ?_
      hdetFirst := ?_
      hdetTail := ?_
      hvecTail := ?_
      hselfTail := ?_ }
  · simpa [storedSignedSequenceTwiceTrailingSeq, storedSignedSequenceTailAlpha2]
      using hvecTailTail0
  · simpa [storedSignedSequenceTwiceTrailingSeq, storedSignedSequenceTailAlpha2]
      using hselfTailTail0
  · simpa [storedSignedSequenceTwiceTrailingSeq] using hdetTailTailFirst
  · simpa [storedSignedSequenceTwiceTrailingSeq] using hdetTailTailTail
  · simpa [storedSignedSequenceTwiceTrailingSeq, storedSignedSequenceTailAlpha2]
      using hvecTailTail1
  · simpa [storedSignedSequenceTwiceTrailingSeq, storedSignedSequenceTailAlpha2]
      using hselfTailTail1

/-- Recursive final-panel closure predicate for the twice-trailing tail.

This is the induction-hypothesis surface required by the general
recursive/stored final-panel bridge: if the twice-trailing sequence satisfies
its source recurrence, then its final panel agrees with recursive QR on its
initial tail.  Fixed-width tail closures are instances of this predicate; the
arbitrary-width source row remains open until this predicate is proved from the
full reflector-data induction. -/
abbrev storedSignedSequenceTwiceTrailingFinalClosed
    (fp : FPModel) {m p : Nat} (hmn : p + 2 <= m + 2)
    (A_hat : Nat -> Fin (m + 2) -> Fin (p + 2) -> Real)
    (alpha : Nat -> Real) : Prop :=
  (forall k (hk : k < p),
    storedSignedSequenceTwiceTrailingSeq A_hat (k + 1) =
      fl_householderStoredPanelStep fp m p k
        (householderTrailingActiveVector m
          (Fin.mk k (by omega))
          (fun a =>
            storedSignedSequenceTwiceTrailingSeq A_hat k a (Fin.mk k hk))
          (storedSignedSequenceTailAlpha2 alpha k))
        (householderBetaSpec m
          (householderTrailingActiveVector m
            (Fin.mk k (by omega))
            (fun a =>
              storedSignedSequenceTwiceTrailingSeq A_hat k a (Fin.mk k hk))
            (storedSignedSequenceTailAlpha2 alpha k)))
        (storedSignedSequenceTwiceTrailingSeq A_hat k)) ->
    storedSignedSequenceTwiceTrailingSeq A_hat p =
      fl_householderQRPanel_R fp m p
        (storedSignedSequenceTwiceTrailingSeq A_hat 0)

/-- Recursive data contract for arbitrary-width twice-trailing closure.

The row dimension is expressed as a row surplus `r` plus the active column
count.  This keeps the two-step shrink definitionally aligned: after removing
two rows and columns, the same surplus `r` remains.  The contract records the
exact remaining source obligation for the arbitrary-width route: zero columns
need no data, one column needs one-reflector data, and every wider case needs
the first-two reflector package plus recursively the data for its twice-trailing
tail. -/
def storedSignedSequenceTwiceTrailingClosureData
    (fp : FPModel) :
    (r p : Nat) ->
      (Nat -> Fin (r + p + 2) -> Fin (p + 2) -> Real) ->
      (Nat -> Real) -> Prop
  | _r, 0, _A_hat, _alpha => True
  | _r, 1, A_hat, alpha =>
      storedSignedSequenceOneReflectorData fp
        (storedSignedSequenceTwiceTrailingSeq A_hat)
        (storedSignedSequenceTailAlpha2 alpha)
  | r, p + 2, A_hat, alpha =>
      storedSignedSequenceFirstTwoReflectorData fp
        (storedSignedSequenceTwiceTrailingSeq A_hat)
        (storedSignedSequenceTailAlpha2 alpha) /\
      storedSignedSequenceTwiceTrailingClosureData fp r p
        (storedSignedSequenceTwiceTrailingSeq A_hat)
        (storedSignedSequenceTailAlpha2 alpha)

/-- Zero-column constructor for recursive twice-trailing closure data. -/
theorem storedSignedSequenceTwiceTrailingClosureData_zero
    (fp : FPModel) (r : Nat)
    (A_hat : Nat -> Fin (r + 0 + 2) -> Fin (0 + 2) -> Real)
    (alpha : Nat -> Real) :
    storedSignedSequenceTwiceTrailingClosureData fp r 0 A_hat alpha := by
  trivial

/-- One-column constructor for recursive twice-trailing closure data. -/
theorem storedSignedSequenceTwiceTrailingClosureData_one_of_reflectorData
    (fp : FPModel) (r : Nat)
    (A_hat : Nat -> Fin (r + 1 + 2) -> Fin (1 + 2) -> Real)
    (alpha : Nat -> Real)
    (hdata :
      storedSignedSequenceOneReflectorData fp
        (storedSignedSequenceTwiceTrailingSeq A_hat)
        (storedSignedSequenceTailAlpha2 alpha)) :
    storedSignedSequenceTwiceTrailingClosureData fp r 1 A_hat alpha :=
  hdata

/-- One-column recursive closure data from explicit twice-trailing reflector
facts. -/
theorem storedSignedSequenceTwiceTrailingClosureData_one_of_tail_reflector_self_dot
    (fp : FPModel) {m : Nat}
    (A_hat : Nat -> Fin (m + 1 + 2) -> Fin (1 + 2) -> Real)
    (alpha : Nat -> Real)
    (hvecTailTail :
      householderTrailingActiveVector (m + 1)
          (Fin.mk 0 (Nat.succ_pos m))
          (fun a =>
            trailingPanel (trailingPanel (A_hat 2)) a
              (Fin.mk 0 (Nat.succ_pos 0)))
          (alpha 2) =
        fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos 0)
            (trailingPanel (trailingPanel (A_hat 2)))))
    (hselfTailTail :
      (Finset.univ : Finset (Fin (m + 1))).sum
        (fun i =>
          householderTrailingActiveVector (m + 1)
              (Fin.mk 0 (Nat.succ_pos m))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (Nat.succ_pos 0)))
              (alpha 2) i *
            householderTrailingActiveVector (m + 1)
              (Fin.mk 0 (Nat.succ_pos m))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (Nat.succ_pos 0)))
              (alpha 2) i) =
        2)
    (hdetTailTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (trailingPanel (trailingPanel (A_hat 2)))
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0) :
    storedSignedSequenceTwiceTrailingClosureData fp m 1 A_hat alpha :=
  storedSignedSequenceTwiceTrailingClosureData_one_of_reflectorData
    fp m A_hat alpha
    (storedSignedSequenceOneReflectorData_of_tail_reflector_self_dot
      fp A_hat alpha hvecTailTail hselfTailTail hdetTailTail)

/-- Two-step constructor for recursive twice-trailing closure data.

This is the shape produced by the eventual stored-loop induction: the current
twice-trailing tail supplies its first two reflector facts, and the twice-shrunk
tail supplies the recursive closure package. -/
theorem storedSignedSequenceTwiceTrailingClosureData_succ_succ_of_firstTwoReflectorData
    (fp : FPModel) (r p : Nat)
    (A_hat : Nat -> Fin (r + (p + 2) + 2) -> Fin ((p + 2) + 2) -> Real)
    (alpha : Nat -> Real)
    (hfirst :
      storedSignedSequenceFirstTwoReflectorData fp
        (storedSignedSequenceTwiceTrailingSeq A_hat)
        (storedSignedSequenceTailAlpha2 alpha))
    (htail :
      storedSignedSequenceTwiceTrailingClosureData fp r p
        (storedSignedSequenceTwiceTrailingSeq A_hat)
        (storedSignedSequenceTailAlpha2 alpha)) :
    storedSignedSequenceTwiceTrailingClosureData fp r (p + 2) A_hat alpha :=
  And.intro hfirst htail

/-- Two-step recursive closure data from explicit first-two twice-trailing
reflector facts and recursive tail closure.

This is the data-level counterpart of
`storedSignedSequenceTwiceTrailingFinalClosed_succ_succ_of_reflector_self_dot`:
it packages the per-tail source facts into `storedSignedSequenceFirstTwoReflectorData`
and then applies the recursive closure-data constructor. -/
theorem storedSignedSequenceTwiceTrailingClosureData_succ_succ_of_reflector_self_dot
    (fp : FPModel) (r p : Nat)
    (A_hat : Nat -> Fin (r + (p + 2) + 2) -> Fin ((p + 2) + 2) -> Real)
    (alpha : Nat -> Real)
    (hvec0 :
      householderTrailingActiveVector (r + (p + 2))
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
          (fun a =>
            storedSignedSequenceTwiceTrailingSeq A_hat 0 a
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega))))
          (storedSignedSequenceTailAlpha2 alpha 0) =
        fl_householderNormalizedVector fp
          (show 0 < r + (p + 2) by omega)
          (panelFirstColumn (Nat.succ_pos (p + 1))
            (storedSignedSequenceTwiceTrailingSeq A_hat 0)))
    (hself0 :
      (Finset.univ : Finset (Fin (r + (p + 2)))).sum
        (fun i =>
          householderTrailingActiveVector (r + (p + 2))
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
              (fun a =>
                storedSignedSequenceTwiceTrailingSeq A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega))))
              (storedSignedSequenceTailAlpha2 alpha 0) i *
            householderTrailingActiveVector (r + (p + 2))
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
              (fun a =>
                storedSignedSequenceTwiceTrailingSeq A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega))))
              (storedSignedSequenceTailAlpha2 alpha 0) i) =
        2)
    (hdetFirst :
      Ne (Matrix.det
        (qrLeadingBlock
          (storedSignedSequenceTwiceTrailingSeq A_hat 0)
          (by omega)
          (Nat.succ_pos (p + 1)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp
              (show 0 < r + (p + 2) by omega)
              (panelFirstColumn (Nat.succ_pos (p + 1))
                (storedSignedSequenceTwiceTrailingSeq A_hat 0))
           let S0 := fl_householderStoredPanelStep fp
              (r + (p + 2)) (p + 2) 0 v0 1
              (storedSignedSequenceTwiceTrailingSeq A_hat 0)
           trailingPanel S0)
          (show 1 <= r + (p + 1) by omega)
          (Nat.succ_pos p) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTail :
      (let v0 := fl_householderNormalizedVector fp
          (show 0 < r + (p + 2) by omega)
          (panelFirstColumn (Nat.succ_pos (p + 1))
            (storedSignedSequenceTwiceTrailingSeq A_hat 0))
       let S0 := fl_householderStoredPanelStep fp
          (r + (p + 2)) (p + 2) 0 v0 1
          (storedSignedSequenceTwiceTrailingSeq A_hat 0)
       householderTrailingActiveVector (r + (p + 1))
            (0 : Fin (r + (p + 1)))
            (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
            (storedSignedSequenceTailAlpha2 alpha 1) =
          fl_householderNormalizedVector fp
            (show 0 < r + (p + 1) by omega)
            (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))))
    (hselfTail :
      (let v0 := fl_householderNormalizedVector fp
          (show 0 < r + (p + 2) by omega)
          (panelFirstColumn (Nat.succ_pos (p + 1))
            (storedSignedSequenceTwiceTrailingSeq A_hat 0))
       let S0 := fl_householderStoredPanelStep fp
          (r + (p + 2)) (p + 2) 0 v0 1
          (storedSignedSequenceTwiceTrailingSeq A_hat 0)
       (Finset.univ : Finset (Fin (r + (p + 1)))).sum
          (fun i =>
            householderTrailingActiveVector (r + (p + 1))
                (0 : Fin (r + (p + 1)))
                (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
                (storedSignedSequenceTailAlpha2 alpha 1) i *
              householderTrailingActiveVector (r + (p + 1))
                (0 : Fin (r + (p + 1)))
                (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
                (storedSignedSequenceTailAlpha2 alpha 1) i) =
        2))
    (htail :
      storedSignedSequenceTwiceTrailingClosureData fp r p
        (storedSignedSequenceTwiceTrailingSeq A_hat)
        (storedSignedSequenceTailAlpha2 alpha)) :
    storedSignedSequenceTwiceTrailingClosureData fp r (p + 2) A_hat alpha := by
  have hfirst :
      storedSignedSequenceFirstTwoReflectorData fp
        (storedSignedSequenceTwiceTrailingSeq A_hat)
        (storedSignedSequenceTailAlpha2 alpha) := by
    refine
      { hvec0 := ?_
        hself0 := ?_
        hdetFirst := ?_
        hdetTail := ?_
        hvecTail := ?_
        hselfTail := ?_ }
    · simpa using hvec0
    · simpa using hself0
    · simpa using hdetFirst
    · simpa using hdetTail
    · simpa using hvecTail
    · simpa using hselfTail
  exact
    storedSignedSequenceTwiceTrailingClosureData_succ_succ_of_firstTwoReflectorData
      fp r p A_hat alpha hfirst htail

/-- Two-step recursive closure data from raw twice-trailing tail reflector
facts.

This is the source-tail entry point for the eventual stored-loop induction:
the first two facts are stated on `trailingPanel (trailingPanel (A_hat 2))`
and `alpha 2`, `alpha 3`, while the conclusion is the recursive closure-data
package for the original sequence. -/
theorem storedSignedSequenceTwiceTrailingClosureData_succ_succ_of_tail_reflector_self_dot
    (fp : FPModel) (r p : Nat)
    (A_hat : Nat -> Fin (r + (p + 2) + 2) -> Fin ((p + 2) + 2) -> Real)
    (alpha : Nat -> Real)
    (hvecTailTail0 :
      householderTrailingActiveVector (r + (p + 2))
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
          (fun a =>
            trailingPanel (trailingPanel (A_hat 2)) a
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega))))
          (alpha 2) =
        fl_householderNormalizedVector fp
          (show 0 < r + (p + 2) by omega)
          (panelFirstColumn (Nat.succ_pos (p + 1))
            (trailingPanel (trailingPanel (A_hat 2)))))
    (hselfTailTail0 :
      (Finset.univ : Finset (Fin (r + (p + 2)))).sum
        (fun i =>
          householderTrailingActiveVector (r + (p + 2))
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega))))
              (alpha 2) i *
            householderTrailingActiveVector (r + (p + 2))
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega))))
              (alpha 2) i) =
        2)
    (hdetTailTailFirst :
      Ne (Matrix.det
        (qrLeadingBlock
          (trailingPanel (trailingPanel (A_hat 2)))
          (show 1 <= r + (p + 2) by omega)
          (Nat.succ_pos (p + 1)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTailTailTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp
              (show 0 < r + (p + 2) by omega)
              (panelFirstColumn (Nat.succ_pos (p + 1))
                (trailingPanel (trailingPanel (A_hat 2))))
           let S0 := fl_householderStoredPanelStep fp
              (r + (p + 2)) (p + 2) 0 v0 1
              (trailingPanel (trailingPanel (A_hat 2)))
           trailingPanel S0)
          (show 1 <= r + (p + 1) by omega)
          (Nat.succ_pos p) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTailTail1 :
      (let v0 := fl_householderNormalizedVector fp
          (show 0 < r + (p + 2) by omega)
          (panelFirstColumn (Nat.succ_pos (p + 1))
            (trailingPanel (trailingPanel (A_hat 2))))
       let S0 := fl_householderStoredPanelStep fp
          (r + (p + 2)) (p + 2) 0 v0 1
          (trailingPanel (trailingPanel (A_hat 2)))
       householderTrailingActiveVector (r + (p + 1))
            (0 : Fin (r + (p + 1)))
            (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
            (alpha 3) =
          fl_householderNormalizedVector fp
            (show 0 < r + (p + 1) by omega)
            (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))))
    (hselfTailTail1 :
      (let v0 := fl_householderNormalizedVector fp
          (show 0 < r + (p + 2) by omega)
          (panelFirstColumn (Nat.succ_pos (p + 1))
            (trailingPanel (trailingPanel (A_hat 2))))
       let S0 := fl_householderStoredPanelStep fp
          (r + (p + 2)) (p + 2) 0 v0 1
          (trailingPanel (trailingPanel (A_hat 2)))
       (Finset.univ : Finset (Fin (r + (p + 1)))).sum
          (fun i =>
            householderTrailingActiveVector (r + (p + 1))
                (0 : Fin (r + (p + 1)))
                (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
                (alpha 3) i *
              householderTrailingActiveVector (r + (p + 1))
                (0 : Fin (r + (p + 1)))
                (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
                (alpha 3) i) =
        2))
    (htail :
      storedSignedSequenceTwiceTrailingClosureData fp r p
        (storedSignedSequenceTwiceTrailingSeq A_hat)
        (storedSignedSequenceTailAlpha2 alpha)) :
    storedSignedSequenceTwiceTrailingClosureData fp r (p + 2) A_hat alpha :=
  storedSignedSequenceTwiceTrailingClosureData_succ_succ_of_reflector_self_dot
    fp r p A_hat alpha
    (by
      simpa [storedSignedSequenceTwiceTrailingSeq,
        storedSignedSequenceTailAlpha2] using hvecTailTail0)
    (by
      simpa [storedSignedSequenceTwiceTrailingSeq,
        storedSignedSequenceTailAlpha2] using hselfTailTail0)
    (by
      simpa [storedSignedSequenceTwiceTrailingSeq] using hdetTailTailFirst)
    (by
      simpa [storedSignedSequenceTwiceTrailingSeq] using hdetTailTailTail)
    (by
      simpa [storedSignedSequenceTwiceTrailingSeq,
        storedSignedSequenceTailAlpha2] using hvecTailTail1)
    (by
      simpa [storedSignedSequenceTwiceTrailingSeq,
        storedSignedSequenceTailAlpha2] using hselfTailTail1)
    htail

/-- Raw one-reflector source facts for a one-column twice-trailing tail.

This is the source-facing counterpart of `storedSignedSequenceOneReflectorData`;
the facts are stated directly on `trailingPanel (trailingPanel (A_hat 2))`,
as they arise from the full stored loop at stage two. -/
structure storedSignedSequenceOneTailReflectorFacts
    (fp : FPModel) {m : Nat}
    (A_hat : Nat -> Fin (m + 1 + 2) -> Fin (1 + 2) -> Real)
    (alpha : Nat -> Real) : Prop where
  hvecTailTail :
    householderTrailingActiveVector (m + 1)
        (Fin.mk 0 (Nat.succ_pos m))
        (fun a =>
          trailingPanel (trailingPanel (A_hat 2)) a
            (Fin.mk 0 (Nat.succ_pos 0)))
        (alpha 2) =
      fl_householderNormalizedVector fp (Nat.succ_pos m)
        (panelFirstColumn (Nat.succ_pos 0)
          (trailingPanel (trailingPanel (A_hat 2))))
  hselfTailTail :
    (Finset.univ : Finset (Fin (m + 1))).sum
      (fun i =>
        householderTrailingActiveVector (m + 1)
            (Fin.mk 0 (Nat.succ_pos m))
            (fun a =>
              trailingPanel (trailingPanel (A_hat 2)) a
                (Fin.mk 0 (Nat.succ_pos 0)))
            (alpha 2) i *
          householderTrailingActiveVector (m + 1)
            (Fin.mk 0 (Nat.succ_pos m))
            (fun a =>
              trailingPanel (trailingPanel (A_hat 2)) a
                (Fin.mk 0 (Nat.succ_pos 0)))
            (alpha 2) i) =
      2
  hdetTailTail :
    Ne (Matrix.det
      (qrLeadingBlock
        (trailingPanel (trailingPanel (A_hat 2)))
        (Nat.succ_le_succ (Nat.zero_le m))
        (Nat.succ_pos 0) :
        Matrix (Fin 1) (Fin 1) Real))
      0

/-- Raw first-two source facts for an arbitrary-width twice-trailing tail.

The facts are stated at stages two and three of the original stored sequence.
This is the contract the eventual full stored-loop induction should populate
from per-pivot reflector normalization, self-dot, and determinant facts. -/
structure storedSignedSequenceFirstTwoTailReflectorFacts
    (fp : FPModel) {r p : Nat}
    (A_hat : Nat -> Fin (r + (p + 2) + 2) -> Fin ((p + 2) + 2) -> Real)
    (alpha : Nat -> Real) : Prop where
  hvecTailTail0 :
    householderTrailingActiveVector (r + (p + 2))
        (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
        (fun a =>
          trailingPanel (trailingPanel (A_hat 2)) a
            (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega))))
        (alpha 2) =
      fl_householderNormalizedVector fp
        (show 0 < r + (p + 2) by omega)
        (panelFirstColumn (Nat.succ_pos (p + 1))
          (trailingPanel (trailingPanel (A_hat 2))))
  hselfTailTail0 :
    (Finset.univ : Finset (Fin (r + (p + 2)))).sum
      (fun i =>
        householderTrailingActiveVector (r + (p + 2))
            (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
            (fun a =>
              trailingPanel (trailingPanel (A_hat 2)) a
                (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega))))
            (alpha 2) i *
          householderTrailingActiveVector (r + (p + 2))
            (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
            (fun a =>
              trailingPanel (trailingPanel (A_hat 2)) a
                (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega))))
            (alpha 2) i) =
      2
  hdetTailTailFirst :
    Ne (Matrix.det
      (qrLeadingBlock
        (trailingPanel (trailingPanel (A_hat 2)))
        (show 1 <= r + (p + 2) by omega)
        (Nat.succ_pos (p + 1)) :
        Matrix (Fin 1) (Fin 1) Real))
      0
  hdetTailTailTail :
    Ne (Matrix.det
      (qrLeadingBlock
        (let v0 := fl_householderNormalizedVector fp
            (show 0 < r + (p + 2) by omega)
            (panelFirstColumn (Nat.succ_pos (p + 1))
              (trailingPanel (trailingPanel (A_hat 2))))
         let S0 := fl_householderStoredPanelStep fp
            (r + (p + 2)) (p + 2) 0 v0 1
            (trailingPanel (trailingPanel (A_hat 2)))
         trailingPanel S0)
        (show 1 <= r + (p + 1) by omega)
        (Nat.succ_pos p) :
        Matrix (Fin 1) (Fin 1) Real))
      0
  hvecTailTail1 :
    (let v0 := fl_householderNormalizedVector fp
        (show 0 < r + (p + 2) by omega)
        (panelFirstColumn (Nat.succ_pos (p + 1))
          (trailingPanel (trailingPanel (A_hat 2))))
     let S0 := fl_householderStoredPanelStep fp
        (r + (p + 2)) (p + 2) 0 v0 1
        (trailingPanel (trailingPanel (A_hat 2)))
     householderTrailingActiveVector (r + (p + 1))
          (0 : Fin (r + (p + 1)))
          (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
          (alpha 3) =
        fl_householderNormalizedVector fp
          (show 0 < r + (p + 1) by omega)
          (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0)))
  hselfTailTail1 :
    (let v0 := fl_householderNormalizedVector fp
        (show 0 < r + (p + 2) by omega)
        (panelFirstColumn (Nat.succ_pos (p + 1))
          (trailingPanel (trailingPanel (A_hat 2))))
     let S0 := fl_householderStoredPanelStep fp
        (r + (p + 2)) (p + 2) 0 v0 1
        (trailingPanel (trailingPanel (A_hat 2)))
     (Finset.univ : Finset (Fin (r + (p + 1)))).sum
        (fun i =>
          householderTrailingActiveVector (r + (p + 1))
              (0 : Fin (r + (p + 1)))
              (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
              (alpha 3) i *
            householderTrailingActiveVector (r + (p + 1))
              (0 : Fin (r + (p + 1)))
              (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
              (alpha 3) i) =
      2)

/-- Package actual one-column stage-two twice-trailing facts as the raw
source-tail reflector-fact contract.

This is the odd-width base analogue of the two-step bridge below. It does not
derive the normalized-vector or self-dot facts; it records the exact local
surface that the stored-loop induction should produce at stage two. -/
theorem storedSignedSequenceOneTailReflectorFacts_of_twice_trailing_stage_facts
    (fp : FPModel) {m : Nat}
    (A_hat : Nat -> Fin (m + 1 + 2) -> Fin (1 + 2) -> Real)
    (alpha : Nat -> Real)
    (hvecTailTail :
      householderTrailingActiveVector (m + 1)
          (Fin.mk 0 (Nat.succ_pos m))
          (fun a =>
            trailingPanel (trailingPanel (A_hat 2)) a
              (Fin.mk 0 (Nat.succ_pos 0)))
          (alpha 2) =
        fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos 0)
            (trailingPanel (trailingPanel (A_hat 2)))))
    (hselfTailTail :
      (Finset.univ : Finset (Fin (m + 1))).sum
        (fun i =>
          householderTrailingActiveVector (m + 1)
              (Fin.mk 0 (Nat.succ_pos m))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (Nat.succ_pos 0)))
              (alpha 2) i *
            householderTrailingActiveVector (m + 1)
              (Fin.mk 0 (Nat.succ_pos m))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (Nat.succ_pos 0)))
              (alpha 2) i) =
        2)
    (hdetTailTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (trailingPanel (trailingPanel (A_hat 2)))
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0) :
    storedSignedSequenceOneTailReflectorFacts fp A_hat alpha :=
  { hvecTailTail := hvecTailTail
    hselfTailTail := hselfTailTail
    hdetTailTail := hdetTailTail }

/-- Package actual stage-two/stage-three twice-trailing stored-loop facts as
raw first-two source-tail reflector facts.

The stage-three facts are stated on the real source panel
`trailingPanel (trailingPanel (trailingPanel (A_hat 3)))`. The proof uses the
stage-two stored recurrence, plus the stage-two normalized-vector and self-dot
facts, to identify that source panel with the synthetic `trailingPanel S0` used
by the recursive QR bridge. Thus this theorem removes a panel-rewrite obligation
from the full stored-loop induction without deriving the hard normalization
facts themselves. -/
theorem
    storedSignedSequenceFirstTwoTailReflectorFacts_of_twice_trailing_stage_facts
    (fp : FPModel) (r p : Nat)
    (A_hat : Nat -> Fin (r + (p + 2) + 2) -> Fin ((p + 2) + 2) -> Real)
    (alpha : Nat -> Real)
    (hStep : forall k (hk : k < (p + 2) + 2),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (r + (p + 2) + 2) ((p + 2) + 2) k
          (householderTrailingActiveVector (r + (p + 2) + 2)
            (Fin.mk k
              (lt_of_lt_of_le hk
                (by omega : (p + 2) + 2 <= r + (p + 2) + 2)))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (r + (p + 2) + 2)
            (householderTrailingActiveVector (r + (p + 2) + 2)
              (Fin.mk k
                (lt_of_lt_of_le hk
                  (by omega : (p + 2) + 2 <= r + (p + 2) + 2)))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (hvecTailTail0 :
      householderTrailingActiveVector (r + (p + 2))
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
          (fun a =>
            trailingPanel (trailingPanel (A_hat 2)) a
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega))))
          (alpha 2) =
        fl_householderNormalizedVector fp
          (show 0 < r + (p + 2) by omega)
          (panelFirstColumn (Nat.succ_pos (p + 1))
            (trailingPanel (trailingPanel (A_hat 2)))))
    (hselfTailTail0 :
      (Finset.univ : Finset (Fin (r + (p + 2)))).sum
        (fun i =>
          householderTrailingActiveVector (r + (p + 2))
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega))))
              (alpha 2) i *
            householderTrailingActiveVector (r + (p + 2))
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega))))
              (alpha 2) i) =
        2)
    (hdetTailTailFirst :
      Ne (Matrix.det
        (qrLeadingBlock
          (trailingPanel (trailingPanel (A_hat 2)))
          (show 1 <= r + (p + 2) by omega)
          (Nat.succ_pos (p + 1)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTailTailTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (trailingPanel (trailingPanel (trailingPanel (A_hat 3))))
          (show 1 <= r + (p + 1) by omega)
          (Nat.succ_pos p) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTailTail1 :
      householderTrailingActiveVector (r + (p + 1))
          (0 : Fin (r + (p + 1)))
          (panelFirstColumn (Nat.succ_pos p)
            (trailingPanel (trailingPanel (trailingPanel (A_hat 3)))))
          (alpha 3) =
        fl_householderNormalizedVector fp
          (show 0 < r + (p + 1) by omega)
          (panelFirstColumn (Nat.succ_pos p)
            (trailingPanel (trailingPanel (trailingPanel (A_hat 3))))))
    (hselfTailTail1 :
      (Finset.univ : Finset (Fin (r + (p + 1)))).sum
        (fun i =>
          householderTrailingActiveVector (r + (p + 1))
              (0 : Fin (r + (p + 1)))
              (panelFirstColumn (Nat.succ_pos p)
                (trailingPanel (trailingPanel (trailingPanel (A_hat 3)))))
              (alpha 3) i *
            householderTrailingActiveVector (r + (p + 1))
              (0 : Fin (r + (p + 1)))
              (panelFirstColumn (Nat.succ_pos p)
                (trailingPanel (trailingPanel (trailingPanel (A_hat 3)))))
              (alpha 3) i) =
        2) :
    storedSignedSequenceFirstTwoTailReflectorFacts fp A_hat alpha := by
  have hselfTailTail0_norm :
      (Finset.univ : Finset (Fin (r + (p + 2)))).sum
        (fun i =>
          fl_householderNormalizedVector fp
              (show 0 < r + (p + 2) by omega)
              (panelFirstColumn (Nat.succ_pos (p + 1))
                (trailingPanel (trailingPanel (A_hat 2)))) i *
            fl_householderNormalizedVector fp
              (show 0 < r + (p + 2) by omega)
              (panelFirstColumn (Nat.succ_pos (p + 1))
                (trailingPanel (trailingPanel (A_hat 2)))) i) =
        2 := by
    rw [<- hvecTailTail0]
    exact hselfTailTail0
  have hbetaTailTail0_norm :
      householderBetaSpec (r + (p + 2))
          (fl_householderNormalizedVector fp
            (show 0 < r + (p + 2) by omega)
            (panelFirstColumn (Nat.succ_pos (p + 1))
              (trailingPanel (trailingPanel (A_hat 2))))) =
        1 := by
    exact
      householderBetaSpec_eq_one_of_inner_self_eq_two (r + (p + 2))
        (fl_householderNormalizedVector fp
          (show 0 < r + (p + 2) by omega)
          (panelFirstColumn (Nat.succ_pos (p + 1))
            (trailingPanel (trailingPanel (A_hat 2)))))
        hselfTailTail0_norm
  have htailStep0 :
      trailingPanel (trailingPanel (A_hat 3)) =
        fl_householderStoredPanelStep fp (r + (p + 2)) (p + 2) 0
          (fl_householderNormalizedVector fp
            (show 0 < r + (p + 2) by omega)
            (panelFirstColumn (Nat.succ_pos (p + 1))
              (trailingPanel (trailingPanel (A_hat 2)))))
          1
          (trailingPanel (trailingPanel (A_hat 2))) := by
    have h :=
      storedSignedSequence_twice_trailing_step_of_source_step
        (fp := fp) (m := r + (p + 2)) (p := p + 2)
        (hmn := by omega)
        (A_hat := A_hat) (alpha := alpha) hStep 0 (by omega)
    change trailingPanel (trailingPanel (A_hat 3)) =
      fl_householderStoredPanelStep fp (r + (p + 2)) (p + 2) 0
        (householderTrailingActiveVector (r + (p + 2))
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
          (fun a =>
            trailingPanel (trailingPanel (A_hat 2)) a
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega))))
          (alpha 2))
        (householderBetaSpec (r + (p + 2))
          (householderTrailingActiveVector (r + (p + 2))
            (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
            (fun a =>
              trailingPanel (trailingPanel (A_hat 2)) a
                (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega))))
            (alpha 2)))
        (trailingPanel (trailingPanel (A_hat 2))) at h
    rw [hvecTailTail0, hbetaTailTail0_norm] at h
    simpa using h
  refine
    { hvecTailTail0 := hvecTailTail0
      hselfTailTail0 := hselfTailTail0
      hdetTailTailFirst := hdetTailTailFirst
      hdetTailTailTail := ?_
      hvecTailTail1 := ?_
      hselfTailTail1 := ?_ }
  · simpa [htailStep0] using hdetTailTailTail
  · simpa [htailStep0] using hvecTailTail1
  · simpa [htailStep0] using hselfTailTail1

/-- Source-facing recursive reflector facts for arbitrary twice-trailing
closure.

Unlike `storedSignedSequenceTwiceTrailingClosureData`, this contract stores the
raw facts as they appear on the actual twice-trailing source panels.  The theorem
below proves that it is sufficient to build the existing closure-data package. -/
def storedSignedSequenceTwiceTrailingSourceClosureData
    (fp : FPModel) :
    (r p : Nat) ->
      (Nat -> Fin (r + p + 2) -> Fin (p + 2) -> Real) ->
      (Nat -> Real) -> Prop
  | _r, 0, _A_hat, _alpha => True
  | _r, 1, A_hat, alpha =>
      storedSignedSequenceOneTailReflectorFacts fp A_hat alpha
  | r, p + 2, A_hat, alpha =>
      storedSignedSequenceFirstTwoTailReflectorFacts fp A_hat alpha /\
      storedSignedSequenceTwiceTrailingSourceClosureData fp r p
        (storedSignedSequenceTwiceTrailingSeq A_hat)
        (storedSignedSequenceTailAlpha2 alpha)

/-- Zero-column constructor for recursive source-tail closure facts. -/
theorem storedSignedSequenceTwiceTrailingSourceClosureData_zero
    (fp : FPModel) (r : Nat)
    (A_hat : Nat -> Fin (r + 0 + 2) -> Fin (0 + 2) -> Real)
    (alpha : Nat -> Real) :
    storedSignedSequenceTwiceTrailingSourceClosureData fp r 0 A_hat alpha := by
  trivial

/-- One-column constructor for recursive source-tail closure facts. -/
theorem storedSignedSequenceTwiceTrailingSourceClosureData_one_of_tail_reflector_facts
    (fp : FPModel) {m : Nat}
    (A_hat : Nat -> Fin (m + 1 + 2) -> Fin (1 + 2) -> Real)
    (alpha : Nat -> Real)
    (hfacts : storedSignedSequenceOneTailReflectorFacts fp A_hat alpha) :
    storedSignedSequenceTwiceTrailingSourceClosureData fp m 1 A_hat alpha :=
  hfacts

/-- One-column recursive source-tail closure data from the explicit
twice-trailing reflector facts produced by the stored loop. -/
theorem storedSignedSequenceTwiceTrailingSourceClosureData_one_of_tail_reflector_self_dot
    (fp : FPModel) {m : Nat}
    (A_hat : Nat -> Fin (m + 1 + 2) -> Fin (1 + 2) -> Real)
    (alpha : Nat -> Real)
    (hvecTailTail :
      householderTrailingActiveVector (m + 1)
          (Fin.mk 0 (Nat.succ_pos m))
          (fun a =>
            trailingPanel (trailingPanel (A_hat 2)) a
              (Fin.mk 0 (Nat.succ_pos 0)))
          (alpha 2) =
        fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos 0)
            (trailingPanel (trailingPanel (A_hat 2)))))
    (hselfTailTail :
      (Finset.univ : Finset (Fin (m + 1))).sum
        (fun i =>
          householderTrailingActiveVector (m + 1)
              (Fin.mk 0 (Nat.succ_pos m))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (Nat.succ_pos 0)))
              (alpha 2) i *
            householderTrailingActiveVector (m + 1)
              (Fin.mk 0 (Nat.succ_pos m))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (Nat.succ_pos 0)))
              (alpha 2) i) =
        2)
    (hdetTailTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (trailingPanel (trailingPanel (A_hat 2)))
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0) :
    storedSignedSequenceTwiceTrailingSourceClosureData fp m 1 A_hat alpha :=
  storedSignedSequenceTwiceTrailingSourceClosureData_one_of_tail_reflector_facts
    fp A_hat alpha
    { hvecTailTail := hvecTailTail
      hselfTailTail := hselfTailTail
      hdetTailTail := hdetTailTail }

/-- Two-step constructor for recursive source-tail closure facts. -/
theorem storedSignedSequenceTwiceTrailingSourceClosureData_succ_succ_of_firstTwoTailReflectorFacts
    (fp : FPModel) (r p : Nat)
    (A_hat : Nat -> Fin (r + (p + 2) + 2) -> Fin ((p + 2) + 2) -> Real)
    (alpha : Nat -> Real)
    (hfirst : storedSignedSequenceFirstTwoTailReflectorFacts fp A_hat alpha)
    (htail :
      storedSignedSequenceTwiceTrailingSourceClosureData fp r p
        (storedSignedSequenceTwiceTrailingSeq A_hat)
        (storedSignedSequenceTailAlpha2 alpha)) :
    storedSignedSequenceTwiceTrailingSourceClosureData fp r (p + 2) A_hat alpha :=
  And.intro hfirst htail

/-- Two-step recursive source-tail closure data from explicit first-two
twice-trailing reflector facts and recursive source-tail closure.

This is the constructor shape needed by the eventual stored-loop induction:
the current twice-trailing source panel supplies the first two raw reflector
facts, and the twice-shrunk tail supplies the recursive source closure. -/
theorem storedSignedSequenceTwiceTrailingSourceClosureData_succ_succ_of_tail_reflector_self_dot
    (fp : FPModel) (r p : Nat)
    (A_hat : Nat -> Fin (r + (p + 2) + 2) -> Fin ((p + 2) + 2) -> Real)
    (alpha : Nat -> Real)
    (hvecTailTail0 :
      householderTrailingActiveVector (r + (p + 2))
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
          (fun a =>
            trailingPanel (trailingPanel (A_hat 2)) a
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega))))
          (alpha 2) =
        fl_householderNormalizedVector fp
          (show 0 < r + (p + 2) by omega)
          (panelFirstColumn (Nat.succ_pos (p + 1))
            (trailingPanel (trailingPanel (A_hat 2)))))
    (hselfTailTail0 :
      (Finset.univ : Finset (Fin (r + (p + 2)))).sum
        (fun i =>
          householderTrailingActiveVector (r + (p + 2))
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega))))
              (alpha 2) i *
            householderTrailingActiveVector (r + (p + 2))
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega))))
              (alpha 2) i) =
        2)
    (hdetTailTailFirst :
      Ne (Matrix.det
        (qrLeadingBlock
          (trailingPanel (trailingPanel (A_hat 2)))
          (show 1 <= r + (p + 2) by omega)
          (Nat.succ_pos (p + 1)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTailTailTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp
              (show 0 < r + (p + 2) by omega)
              (panelFirstColumn (Nat.succ_pos (p + 1))
                (trailingPanel (trailingPanel (A_hat 2))))
           let S0 := fl_householderStoredPanelStep fp
              (r + (p + 2)) (p + 2) 0 v0 1
              (trailingPanel (trailingPanel (A_hat 2)))
           trailingPanel S0)
          (show 1 <= r + (p + 1) by omega)
          (Nat.succ_pos p) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTailTail1 :
      (let v0 := fl_householderNormalizedVector fp
          (show 0 < r + (p + 2) by omega)
          (panelFirstColumn (Nat.succ_pos (p + 1))
            (trailingPanel (trailingPanel (A_hat 2))))
       let S0 := fl_householderStoredPanelStep fp
          (r + (p + 2)) (p + 2) 0 v0 1
          (trailingPanel (trailingPanel (A_hat 2)))
       householderTrailingActiveVector (r + (p + 1))
            (0 : Fin (r + (p + 1)))
            (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
            (alpha 3) =
          fl_householderNormalizedVector fp
            (show 0 < r + (p + 1) by omega)
            (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))))
    (hselfTailTail1 :
      (let v0 := fl_householderNormalizedVector fp
          (show 0 < r + (p + 2) by omega)
          (panelFirstColumn (Nat.succ_pos (p + 1))
            (trailingPanel (trailingPanel (A_hat 2))))
       let S0 := fl_householderStoredPanelStep fp
          (r + (p + 2)) (p + 2) 0 v0 1
          (trailingPanel (trailingPanel (A_hat 2)))
       (Finset.univ : Finset (Fin (r + (p + 1)))).sum
          (fun i =>
            householderTrailingActiveVector (r + (p + 1))
                (0 : Fin (r + (p + 1)))
                (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
                (alpha 3) i *
              householderTrailingActiveVector (r + (p + 1))
                (0 : Fin (r + (p + 1)))
                (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
                (alpha 3) i) =
        2))
    (htail :
      storedSignedSequenceTwiceTrailingSourceClosureData fp r p
        (storedSignedSequenceTwiceTrailingSeq A_hat)
        (storedSignedSequenceTailAlpha2 alpha)) :
    storedSignedSequenceTwiceTrailingSourceClosureData fp r (p + 2) A_hat alpha :=
  storedSignedSequenceTwiceTrailingSourceClosureData_succ_succ_of_firstTwoTailReflectorFacts
    fp r p A_hat alpha
    { hvecTailTail0 := hvecTailTail0
      hselfTailTail0 := hselfTailTail0
      hdetTailTailFirst := hdetTailTailFirst
      hdetTailTailTail := hdetTailTailTail
      hvecTailTail1 := hvecTailTail1
      hselfTailTail1 := hselfTailTail1 }
    htail

/-- Raw source-tail closure facts imply the recursive closure-data contract. -/
theorem storedSignedSequenceTwiceTrailingClosureData_of_sourceClosureData
    (fp : FPModel) (r p : Nat)
    (A_hat : Nat -> Fin (r + p + 2) -> Fin (p + 2) -> Real)
    (alpha : Nat -> Real)
    (hdata :
      storedSignedSequenceTwiceTrailingSourceClosureData fp r p A_hat alpha) :
    storedSignedSequenceTwiceTrailingClosureData fp r p A_hat alpha := by
  revert r A_hat alpha
  refine
    Nat.twoStepInduction
      (P := fun p =>
        forall (r : Nat)
            (A_hat : Nat -> Fin (r + p + 2) -> Fin (p + 2) -> Real)
            (alpha : Nat -> Real),
          storedSignedSequenceTwiceTrailingSourceClosureData fp r p
              A_hat alpha ->
            storedSignedSequenceTwiceTrailingClosureData fp r p A_hat alpha)
      ?hzero ?hone ?hstep p
  · intro r A_hat alpha _hdata
    exact storedSignedSequenceTwiceTrailingClosureData_zero fp r A_hat alpha
  · intro r A_hat alpha hdata
    exact
      storedSignedSequenceTwiceTrailingClosureData_one_of_tail_reflector_self_dot
        fp A_hat alpha hdata.hvecTailTail hdata.hselfTailTail
        hdata.hdetTailTail
  · intro p ih _ihSucc r A_hat alpha hdata
    exact
      storedSignedSequenceTwiceTrailingClosureData_succ_succ_of_tail_reflector_self_dot
        fp r p A_hat alpha hdata.left.hvecTailTail0
        hdata.left.hselfTailTail0 hdata.left.hdetTailTailFirst
        hdata.left.hdetTailTailTail hdata.left.hvecTailTail1
        hdata.left.hselfTailTail1
        (ih r (storedSignedSequenceTwiceTrailingSeq A_hat)
          (storedSignedSequenceTailAlpha2 alpha) hdata.right)

/-- Final-panel bridge with the twice-trailing obligation exposed as a recursive
tail-sequence theorem.

The premise `hTailFinalOfRec` has the exact recurrence surface produced by
`storedSignedSequence_twice_trailing_source_recurrence_of_source_step`, so an
induction hypothesis for the smaller panel can be threaded directly into the
existing two-step final-panel bridge. -/
theorem
    storedSignedSequence_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_twice_trailing_recurrence_bridge
    (fp : FPModel) {m p : Nat}
    (hmn : p + 2 <= m + 2)
    (A : Fin (m + 2) -> Fin (p + 2) -> Real)
    (A_hat : Nat -> Fin (m + 2) -> Fin (p + 2) -> Real)
    (alpha : Nat -> Real)
    (hrows : 2 <= m + 2)
    (hcols : 2 <= p + 2)
    (hinit : A_hat 0 = A)
    (hStep : forall k (hk : k < p + 2),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (m + 2) (p + 2) k
          (householderTrailingActiveVector (m + 2)
            (Fin.mk k (lt_of_lt_of_le hk hmn))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (m + 2)
            (householderTrailingActiveVector (m + 2)
              (Fin.mk k (lt_of_lt_of_le hk hmn))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (hvec0 :
      householderTrailingActiveVector (m + 2)
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
          (fun a =>
            A_hat 0 a
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
          (alpha 0) =
        fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1)) A))
    (hself0 :
      (Finset.univ : Finset (Fin (m + 2))).sum
        (fun i =>
          householderTrailingActiveVector (m + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
              (fun a =>
                A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
              (alpha 0) i *
            householderTrailingActiveVector (m + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
              (fun a =>
                A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
              (alpha 0) i) =
        2)
    (hdetFirst :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le (m + 1)))
          (Nat.succ_pos (p + 1)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
              (panelFirstColumn (Nat.succ_pos (p + 1)) A)
           let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1 A
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos p) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTail :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1)) A)
       let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1 A
       householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
            (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0)) (alpha 1) =
          fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))))
    (hselfTail :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1)) A)
       let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1 A
       (Finset.univ : Finset (Fin (m + 1))).sum
          (fun i =>
            householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
                (alpha 1) i *
              householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
                (alpha 1) i) =
        2))
    (hcopy : subtractZeroExact fp)
    (hTailFinalOfRec :
      (forall k (hk : k < p),
        (fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) (k + 1) =
          fl_householderStoredPanelStep fp m p k
            (householderTrailingActiveVector m
              (Fin.mk k (by omega))
              (fun a =>
                (fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) k a
                  (Fin.mk k hk)) (alpha (k + 2)))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                (Fin.mk k (by omega))
                (fun a =>
                  (fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) k a
                    (Fin.mk k hk)) (alpha (k + 2))))
            ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) k)) ->
        (fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) p =
          fl_householderQRPanel_R fp m p
            ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 0)) :
    A_hat (p + 2) =
      fl_householderQRPanel_R fp (m + 2) (p + 2) A := by
  have hTailRec : forall k (hk : k < p),
      (fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) (k + 1) =
        fl_householderStoredPanelStep fp m p k
          (householderTrailingActiveVector m
            (Fin.mk k (by omega))
            (fun a =>
              (fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) k a
                (Fin.mk k hk)) (alpha (k + 2)))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              (Fin.mk k (by omega))
              (fun a =>
                (fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) k a
                  (Fin.mk k hk)) (alpha (k + 2))))
          ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) k) := by
    intro k hk
    exact
      storedSignedSequence_twice_trailing_source_recurrence_of_source_step
        fp hmn A_hat alpha hStep k hk
  have hTailFinalSeq := hTailFinalOfRec hTailRec
  have hTailFinal :
      trailingPanel (trailingPanel (A_hat (p + 2))) =
        fl_householderQRPanel_R fp m p
          (trailingPanel (trailingPanel (A_hat 2))) := by
    simpa using hTailFinalSeq
  exact
    storedSignedSequence_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_twice_trailing_final
      fp hmn A A_hat alpha hrows hcols hinit hStep hvec0 hself0
      hdetFirst hdetTail hvecTail hselfTail hcopy hTailFinal

/-- Final-panel bridge consuming the named recursive tail-closure interface.

This is the same mathematical handoff as
`storedSignedSequence_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_twice_trailing_recurrence_bridge`,
but with the induction hypothesis packaged as
`storedSignedSequenceTwiceTrailingFinalClosed`. -/
theorem
    storedSignedSequence_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_twice_trailing_closed
    (fp : FPModel) {m p : Nat}
    (hmn : p + 2 <= m + 2)
    (A : Fin (m + 2) -> Fin (p + 2) -> Real)
    (A_hat : Nat -> Fin (m + 2) -> Fin (p + 2) -> Real)
    (alpha : Nat -> Real)
    (hrows : 2 <= m + 2)
    (hcols : 2 <= p + 2)
    (hinit : A_hat 0 = A)
    (hStep : forall k (hk : k < p + 2),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (m + 2) (p + 2) k
          (householderTrailingActiveVector (m + 2)
            (Fin.mk k (lt_of_lt_of_le hk hmn))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (m + 2)
            (householderTrailingActiveVector (m + 2)
              (Fin.mk k (lt_of_lt_of_le hk hmn))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (hvec0 :
      householderTrailingActiveVector (m + 2)
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
          (fun a =>
            A_hat 0 a
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
          (alpha 0) =
        fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1)) A))
    (hself0 :
      (Finset.univ : Finset (Fin (m + 2))).sum
        (fun i =>
          householderTrailingActiveVector (m + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
              (fun a =>
                A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
              (alpha 0) i *
            householderTrailingActiveVector (m + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
              (fun a =>
                A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
              (alpha 0) i) =
        2)
    (hdetFirst :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le (m + 1)))
          (Nat.succ_pos (p + 1)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
              (panelFirstColumn (Nat.succ_pos (p + 1)) A)
           let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1 A
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos p) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTail :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1)) A)
       let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1 A
       householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
            (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0)) (alpha 1) =
          fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))))
    (hselfTail :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1)) A)
       let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1 A
       (Finset.univ : Finset (Fin (m + 1))).sum
          (fun i =>
            householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
                (alpha 1) i *
              householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
                (alpha 1) i) =
        2))
    (hcopy : subtractZeroExact fp)
    (hTailClosed :
      storedSignedSequenceTwiceTrailingFinalClosed fp hmn A_hat alpha) :
    A_hat (p + 2) =
      fl_householderQRPanel_R fp (m + 2) (p + 2) A :=
  storedSignedSequence_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_twice_trailing_recurrence_bridge
    fp hmn A A_hat alpha hrows hcols hinit hStep hvec0 hself0 hdetFirst
    hdetTail hvecTail hselfTail hcopy hTailClosed

/-- One recursive step for the named twice-trailing final-panel closure.

If the twice-trailing sequence has the reflector data needed for its first two
stored steps, and its own twice-trailing tail is already closed, then the
original twice-trailing sequence is closed.  This is the induction step needed
for the arbitrary-width final-panel route; the remaining source work is to
derive these reflector-data hypotheses uniformly from the full stored loop. -/
theorem storedSignedSequenceTwiceTrailingFinalClosed_succ_succ_of_reflector_self_dot
    (fp : FPModel) {m p : Nat}
    (hmn : (p + 2) + 2 <= (m + 2) + 2)
    (A_hat : Nat -> Fin ((m + 2) + 2) -> Fin ((p + 2) + 2) -> Real)
    (alpha : Nat -> Real)
    (hvec0 :
      householderTrailingActiveVector (m + 2)
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
          (fun a =>
            storedSignedSequenceTwiceTrailingSeq A_hat 0 a
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega))))
          (storedSignedSequenceTailAlpha2 alpha 0) =
        fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1))
            (storedSignedSequenceTwiceTrailingSeq A_hat 0)))
    (hself0 :
      (Finset.univ : Finset (Fin (m + 2))).sum
        (fun i =>
          householderTrailingActiveVector (m + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
              (fun a =>
                storedSignedSequenceTwiceTrailingSeq A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega))))
              (storedSignedSequenceTailAlpha2 alpha 0) i *
            householderTrailingActiveVector (m + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
              (fun a =>
                storedSignedSequenceTwiceTrailingSeq A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega))))
              (storedSignedSequenceTailAlpha2 alpha 0) i) =
        2)
    (hdetFirst :
      Ne (Matrix.det
        (qrLeadingBlock
          (storedSignedSequenceTwiceTrailingSeq A_hat 0)
          (Nat.succ_le_succ (Nat.zero_le (m + 1)))
          (Nat.succ_pos (p + 1)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
              (panelFirstColumn (Nat.succ_pos (p + 1))
                (storedSignedSequenceTwiceTrailingSeq A_hat 0))
           let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1
              (storedSignedSequenceTwiceTrailingSeq A_hat 0)
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos p) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTail :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1))
            (storedSignedSequenceTwiceTrailingSeq A_hat 0))
       let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1
          (storedSignedSequenceTwiceTrailingSeq A_hat 0)
       householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
            (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
            (storedSignedSequenceTailAlpha2 alpha 1) =
          fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))))
    (hselfTail :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1))
            (storedSignedSequenceTwiceTrailingSeq A_hat 0))
       let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1
          (storedSignedSequenceTwiceTrailingSeq A_hat 0)
       (Finset.univ : Finset (Fin (m + 1))).sum
          (fun i =>
            householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
                (storedSignedSequenceTailAlpha2 alpha 1) i *
              householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
                (storedSignedSequenceTailAlpha2 alpha 1) i) =
        2))
    (hcopy : subtractZeroExact fp)
    (hTailClosed :
      storedSignedSequenceTwiceTrailingFinalClosed fp (by omega)
        (storedSignedSequenceTwiceTrailingSeq A_hat)
        (storedSignedSequenceTailAlpha2 alpha)) :
    storedSignedSequenceTwiceTrailingFinalClosed fp hmn A_hat alpha := by
  intro hTailRec
  let TailSeq : Nat -> Fin (m + 2) -> Fin (p + 2) -> Real :=
    storedSignedSequenceTwiceTrailingSeq A_hat
  let TailAlpha : Nat -> Real := storedSignedSequenceTailAlpha2 alpha
  have hTailStep : forall k (hk : k < p + 2),
      TailSeq (k + 1) =
        fl_householderStoredPanelStep fp (m + 2) (p + 2) k
          (householderTrailingActiveVector (m + 2)
            (Fin.mk k (lt_of_lt_of_le hk (by omega)))
            (fun a => TailSeq k a (Fin.mk k hk)) (TailAlpha k))
          (householderBetaSpec (m + 2)
            (householderTrailingActiveVector (m + 2)
              (Fin.mk k (lt_of_lt_of_le hk (by omega)))
              (fun a => TailSeq k a (Fin.mk k hk)) (TailAlpha k)))
          (TailSeq k) := by
    intro k hk
    simpa [TailSeq, TailAlpha, storedSignedSequenceTwiceTrailingSeq,
      storedSignedSequenceTailAlpha2] using hTailRec k hk
  have hfinal :=
    storedSignedSequence_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_twice_trailing_closed
      fp (by omega) (TailSeq 0) TailSeq TailAlpha (by omega) (by omega)
      rfl hTailStep
      (by
        simpa [TailSeq, TailAlpha] using hvec0)
      (by
        simpa [TailSeq, TailAlpha] using hself0)
      (by
        simpa [TailSeq] using hdetFirst)
      (by
        simpa [TailSeq] using hdetTail)
      (by
        simpa [TailSeq, TailAlpha] using hvecTail)
      (by
        simpa [TailSeq, TailAlpha] using hselfTail)
      hcopy
      (by
        simpa [TailSeq, TailAlpha] using hTailClosed)
  simpa [TailSeq, storedSignedSequenceTwiceTrailingSeq] using hfinal

/-- Recursive final-panel closure step consuming packaged first-two reflector
data for the twice-trailing sequence.

This is the theorem surface intended for the eventual arbitrary-width
induction: after proving a uniform source lemma that constructs
`storedSignedSequenceFirstTwoReflectorData` for every twice-trailing tail, the
induction only needs the smaller tail-closure hypothesis. -/
theorem storedSignedSequenceTwiceTrailingFinalClosed_succ_succ_of_firstTwoReflectorData
    (fp : FPModel) {m p : Nat}
    (hmn : (p + 2) + 2 <= (m + 2) + 2)
    (A_hat : Nat -> Fin ((m + 2) + 2) -> Fin ((p + 2) + 2) -> Real)
    (alpha : Nat -> Real)
    (hdata :
      storedSignedSequenceFirstTwoReflectorData fp
        (storedSignedSequenceTwiceTrailingSeq A_hat)
        (storedSignedSequenceTailAlpha2 alpha))
    (hcopy : subtractZeroExact fp)
    (hTailClosed :
      storedSignedSequenceTwiceTrailingFinalClosed fp (by omega)
        (storedSignedSequenceTwiceTrailingSeq A_hat)
        (storedSignedSequenceTailAlpha2 alpha)) :
    storedSignedSequenceTwiceTrailingFinalClosed fp hmn A_hat alpha :=
  storedSignedSequenceTwiceTrailingFinalClosed_succ_succ_of_reflector_self_dot
    fp hmn A_hat alpha hdata.hvec0 hdata.hself0 hdata.hdetFirst
    hdata.hdetTail hdata.hvecTail hdata.hselfTail hcopy hTailClosed

/-- Zero-column instance of the named twice-trailing closure predicate. -/
theorem storedSignedSequenceTwiceTrailingFinalClosed_zero_col
    (fp : FPModel) {m : Nat}
    (A_hat : Nat -> Fin (m + 2) -> Fin (0 + 2) -> Real)
    (alpha : Nat -> Real) :
    storedSignedSequenceTwiceTrailingFinalClosed fp (by omega) A_hat alpha := by
  intro _hTailRec
  exact (qrPanel_R_zero_cols_any fp m
    (storedSignedSequenceTwiceTrailingSeq A_hat 0)).symm

/-- One-column instance of the named twice-trailing closure predicate. -/
theorem storedSignedSequenceTwiceTrailingFinalClosed_one_col_of_reflector_self_dot
    (fp : FPModel) {m : Nat}
    (A_hat : Nat -> Fin ((m + 1) + 2) -> Fin (1 + 2) -> Real)
    (alpha : Nat -> Real)
    (hvecTailTail :
      householderTrailingActiveVector (m + 1)
          (Fin.mk 0 (Nat.succ_pos m))
          (fun a =>
            trailingPanel (trailingPanel (A_hat 2)) a
              (Fin.mk 0 (Nat.succ_pos 0)))
          (alpha 2) =
        fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos 0)
            (trailingPanel (trailingPanel (A_hat 2)))))
    (hselfTailTail :
      (Finset.univ : Finset (Fin (m + 1))).sum
        (fun i =>
          householderTrailingActiveVector (m + 1)
              (Fin.mk 0 (Nat.succ_pos m))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (Nat.succ_pos 0)))
              (alpha 2) i *
            householderTrailingActiveVector (m + 1)
              (Fin.mk 0 (Nat.succ_pos m))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (Nat.succ_pos 0)))
              (alpha 2) i) =
        2)
    (hdetTailTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (trailingPanel (trailingPanel (A_hat 2)))
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0) :
    storedSignedSequenceTwiceTrailingFinalClosed fp (by omega) A_hat alpha := by
  intro hTailRec
  exact
    storedSignedSequence_twice_trailing_one_col_tail_final_of_tail_reflector_self_dot
      fp A_hat alpha hTailRec hvecTailTail hselfTailTail hdetTailTail

/-- One-column closure from packaged one-reflector data. -/
theorem storedSignedSequenceTwiceTrailingFinalClosed_one_col_of_reflectorData
    (fp : FPModel) {m : Nat}
    (A_hat : Nat -> Fin ((m + 1) + 2) -> Fin (1 + 2) -> Real)
    (alpha : Nat -> Real)
    (hdata :
      storedSignedSequenceOneReflectorData fp
        (storedSignedSequenceTwiceTrailingSeq A_hat)
        (storedSignedSequenceTailAlpha2 alpha)) :
    storedSignedSequenceTwiceTrailingFinalClosed fp (by omega) A_hat alpha :=
  storedSignedSequenceTwiceTrailingFinalClosed_one_col_of_reflector_self_dot
    fp A_hat alpha
    (by
      simpa [storedSignedSequenceTwiceTrailingSeq,
        storedSignedSequenceTailAlpha2] using hdata.hvec0)
    (by
      simpa [storedSignedSequenceTwiceTrailingSeq,
        storedSignedSequenceTailAlpha2] using hdata.hself0)
    (by
      simpa [storedSignedSequenceTwiceTrailingSeq] using hdata.hdetFirst)

/-- Two-column instance of the named twice-trailing closure predicate.

This re-expresses the existing two-column tail endpoint in the recursive
closure language used by the arbitrary-width induction. -/
theorem storedSignedSequenceTwiceTrailingFinalClosed_two_col_of_reflector_self_dot
    (fp : FPModel) {m : Nat}
    (A_hat : Nat -> Fin ((m + 2) + 2) -> Fin (2 + 2) -> Real)
    (alpha : Nat -> Real)
    (hvecTailTail0 :
      householderTrailingActiveVector (m + 2)
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
          (fun a =>
            trailingPanel (trailingPanel (A_hat 2)) a
              (Fin.mk 0 (Nat.succ_pos 1)))
          (alpha 2) =
        fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1)
            (trailingPanel (trailingPanel (A_hat 2)))))
    (hselfTailTail0 :
      (Finset.univ : Finset (Fin (m + 2))).sum
        (fun i =>
          householderTrailingActiveVector (m + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (Nat.succ_pos 1)))
              (alpha 2) i *
            householderTrailingActiveVector (m + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (Nat.succ_pos 1)))
              (alpha 2) i) =
        2)
    (hdetTailTailFirst :
      Ne (Matrix.det
        (qrLeadingBlock
          (trailingPanel (trailingPanel (A_hat 2)))
          (Nat.succ_le_succ (Nat.zero_le (m + 1)))
          (Nat.succ_pos 1) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTailTailTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
              (panelFirstColumn (Nat.succ_pos 1)
                (trailingPanel (trailingPanel (A_hat 2))))
           let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1
              (trailingPanel (trailingPanel (A_hat 2)))
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTailTail1 :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1)
            (trailingPanel (trailingPanel (A_hat 2))))
       let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1
          (trailingPanel (trailingPanel (A_hat 2)))
       householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
            (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0)) (alpha 3) =
          fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))))
    (hselfTailTail1 :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1)
            (trailingPanel (trailingPanel (A_hat 2))))
       let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1
          (trailingPanel (trailingPanel (A_hat 2)))
       (Finset.univ : Finset (Fin (m + 1))).sum
          (fun i =>
            householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))
                (alpha 3) i *
              householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))
                (alpha 3) i) =
        2))
    (hcopy : subtractZeroExact fp) :
    storedSignedSequenceTwiceTrailingFinalClosed fp (by omega) A_hat alpha := by
  intro hTailRec
  exact
    storedSignedSequence_twice_trailing_two_col_tail_final_of_tail_reflector_self_dot
      fp A_hat alpha hTailRec hvecTailTail0 hselfTailTail0
      hdetTailTailFirst hdetTailTailTail hvecTailTail1 hselfTailTail1 hcopy

/-- Arbitrary-width twice-trailing closure from recursive reflector data.

This theorem is the induction shell for the remaining Ch19 final-panel source
route.  It does not manufacture reflector data; instead it proves that the
visible recursive data contract is sufficient for every column count, leaving
the source-facing work as the construction of
`storedSignedSequenceTwiceTrailingClosureData` from the stored loop. -/
theorem storedSignedSequenceTwiceTrailingFinalClosed_of_closureData
    (fp : FPModel) (r p : Nat)
    (A_hat : Nat -> Fin (r + p + 2) -> Fin (p + 2) -> Real)
    (alpha : Nat -> Real)
    (hdata :
      storedSignedSequenceTwiceTrailingClosureData fp r p A_hat alpha)
    (hcopy : subtractZeroExact fp) :
    storedSignedSequenceTwiceTrailingFinalClosed fp
      (Nat.add_le_add_right (Nat.le_add_left p r) 2) A_hat alpha := by
  revert r A_hat alpha
  refine
    Nat.twoStepInduction
      (P := fun p =>
        forall (r : Nat)
            (A_hat : Nat -> Fin (r + p + 2) -> Fin (p + 2) -> Real)
            (alpha : Nat -> Real),
          storedSignedSequenceTwiceTrailingClosureData fp r p A_hat alpha ->
            storedSignedSequenceTwiceTrailingFinalClosed fp
              (Nat.add_le_add_right (Nat.le_add_left p r) 2) A_hat alpha)
      ?hzero ?hone ?hstep p
  · intro r A_hat alpha _hdata
    exact storedSignedSequenceTwiceTrailingFinalClosed_zero_col fp A_hat alpha
  · intro r A_hat alpha hdata
    exact
      storedSignedSequenceTwiceTrailingFinalClosed_one_col_of_reflectorData
        fp A_hat alpha hdata
  · intro p ih _ihSucc r A_hat alpha hdata
    rcases hdata with ⟨hfirst, htail⟩
    exact
      storedSignedSequenceTwiceTrailingFinalClosed_succ_succ_of_firstTwoReflectorData
        fp (Nat.add_le_add_right (Nat.le_add_left (p + 2) r) 2)
        A_hat alpha hfirst hcopy
        (ih r (storedSignedSequenceTwiceTrailingSeq A_hat)
          (storedSignedSequenceTailAlpha2 alpha) htail)

/-- Source-facing final-panel bridge consuming recursive closure data.

This is the arbitrary-width final-panel route with the recursive tail obligation
expressed as `storedSignedSequenceTwiceTrailingClosureData`.  The remaining
source work is therefore to construct that data package from the full stored
Householder loop's reflector normalization and determinant facts. -/
theorem
    storedSignedSequence_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_closureData
    (fp : FPModel) (r p : Nat)
    (A : Fin (r + p + 2) -> Fin (p + 2) -> Real)
    (A_hat : Nat -> Fin (r + p + 2) -> Fin (p + 2) -> Real)
    (alpha : Nat -> Real)
    (hrows : 2 <= r + p + 2)
    (hcols : 2 <= p + 2)
    (hinit : A_hat 0 = A)
    (hStep : forall k (hk : k < p + 2),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (r + p + 2) (p + 2) k
          (householderTrailingActiveVector (r + p + 2)
            (Fin.mk k
              (lt_of_lt_of_le hk
                (Nat.add_le_add_right (Nat.le_add_left p r) 2)))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (r + p + 2)
            (householderTrailingActiveVector (r + p + 2)
              (Fin.mk k
                (lt_of_lt_of_le hk
                  (Nat.add_le_add_right (Nat.le_add_left p r) 2)))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (hvec0 :
      householderTrailingActiveVector (r + p + 2)
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
          (fun a =>
            A_hat 0 a
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
          (alpha 0) =
        fl_householderNormalizedVector fp (Nat.succ_pos (r + p + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1)) A))
    (hself0 :
      (Finset.univ : Finset (Fin (r + p + 2))).sum
        (fun i =>
          householderTrailingActiveVector (r + p + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
              (fun a =>
                A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
              (alpha 0) i *
            householderTrailingActiveVector (r + p + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
              (fun a =>
                A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
              (alpha 0) i) =
        2)
    (hdetFirst :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le (r + p + 1)))
          (Nat.succ_pos (p + 1)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp
              (Nat.succ_pos (r + p + 1))
              (panelFirstColumn (Nat.succ_pos (p + 1)) A)
           let S0 := fl_householderStoredPanelStep fp
              (r + p + 2) (p + 2) 0 v0 1 A
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le (r + p)))
          (Nat.succ_pos p) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTail :
      (let v0 := fl_householderNormalizedVector fp
          (Nat.succ_pos (r + p + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1)) A)
       let S0 := fl_householderStoredPanelStep fp
          (r + p + 2) (p + 2) 0 v0 1 A
       householderTrailingActiveVector (r + p + 1) (0 : Fin (r + p + 1))
            (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0)) (alpha 1) =
          fl_householderNormalizedVector fp (Nat.succ_pos (r + p))
            (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))))
    (hselfTail :
      (let v0 := fl_householderNormalizedVector fp
          (Nat.succ_pos (r + p + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1)) A)
       let S0 := fl_householderStoredPanelStep fp
          (r + p + 2) (p + 2) 0 v0 1 A
       (Finset.univ : Finset (Fin (r + p + 1))).sum
          (fun i =>
            householderTrailingActiveVector (r + p + 1) (0 : Fin (r + p + 1))
                (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
                (alpha 1) i *
              householderTrailingActiveVector (r + p + 1) (0 : Fin (r + p + 1))
                (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
                (alpha 1) i) =
        2))
    (hclosure :
      storedSignedSequenceTwiceTrailingClosureData fp r p A_hat alpha)
    (hcopy : subtractZeroExact fp) :
    A_hat (p + 2) =
      fl_householderQRPanel_R fp (r + p + 2) (p + 2) A := by
  have hTailClosed :
      storedSignedSequenceTwiceTrailingFinalClosed fp
        (Nat.add_le_add_right (Nat.le_add_left p r) 2) A_hat alpha :=
    storedSignedSequenceTwiceTrailingFinalClosed_of_closureData
      fp r p A_hat alpha hclosure hcopy
  exact
    storedSignedSequence_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_twice_trailing_closed
      fp (Nat.add_le_add_right (Nat.le_add_left p r) 2)
      A A_hat alpha hrows hcols hinit hStep hvec0 hself0 hdetFirst
      hdetTail hvecTail hselfTail hcopy hTailClosed

/-- Source-facing final-panel bridge consuming raw recursive source facts.

This composes the raw source-tail closure contract with the closure-data bridge,
so the remaining stored-loop induction can target
`storedSignedSequenceTwiceTrailingSourceClosureData` directly. -/
theorem
    storedSignedSequence_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_sourceClosureData
    (fp : FPModel) (r p : Nat)
    (A : Fin (r + p + 2) -> Fin (p + 2) -> Real)
    (A_hat : Nat -> Fin (r + p + 2) -> Fin (p + 2) -> Real)
    (alpha : Nat -> Real)
    (hrows : 2 <= r + p + 2)
    (hcols : 2 <= p + 2)
    (hinit : A_hat 0 = A)
    (hStep : forall k (hk : k < p + 2),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (r + p + 2) (p + 2) k
          (householderTrailingActiveVector (r + p + 2)
            (Fin.mk k
              (lt_of_lt_of_le hk
                (Nat.add_le_add_right (Nat.le_add_left p r) 2)))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (r + p + 2)
            (householderTrailingActiveVector (r + p + 2)
              (Fin.mk k
                (lt_of_lt_of_le hk
                  (Nat.add_le_add_right (Nat.le_add_left p r) 2)))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (hvec0 :
      householderTrailingActiveVector (r + p + 2)
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
          (fun a =>
            A_hat 0 a
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
          (alpha 0) =
        fl_householderNormalizedVector fp (Nat.succ_pos (r + p + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1)) A))
    (hself0 :
      (Finset.univ : Finset (Fin (r + p + 2))).sum
        (fun i =>
          householderTrailingActiveVector (r + p + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
              (fun a =>
                A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
              (alpha 0) i *
            householderTrailingActiveVector (r + p + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
              (fun a =>
                A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
              (alpha 0) i) =
        2)
    (hdetFirst :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le (r + p + 1)))
          (Nat.succ_pos (p + 1)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp
              (Nat.succ_pos (r + p + 1))
              (panelFirstColumn (Nat.succ_pos (p + 1)) A)
           let S0 := fl_householderStoredPanelStep fp
              (r + p + 2) (p + 2) 0 v0 1 A
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le (r + p)))
          (Nat.succ_pos p) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTail :
      (let v0 := fl_householderNormalizedVector fp
          (Nat.succ_pos (r + p + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1)) A)
       let S0 := fl_householderStoredPanelStep fp
          (r + p + 2) (p + 2) 0 v0 1 A
       householderTrailingActiveVector (r + p + 1) (0 : Fin (r + p + 1))
            (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0)) (alpha 1) =
          fl_householderNormalizedVector fp (Nat.succ_pos (r + p))
            (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))))
    (hselfTail :
      (let v0 := fl_householderNormalizedVector fp
          (Nat.succ_pos (r + p + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1)) A)
       let S0 := fl_householderStoredPanelStep fp
          (r + p + 2) (p + 2) 0 v0 1 A
       (Finset.univ : Finset (Fin (r + p + 1))).sum
          (fun i =>
            householderTrailingActiveVector (r + p + 1) (0 : Fin (r + p + 1))
                (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
                (alpha 1) i *
              householderTrailingActiveVector (r + p + 1) (0 : Fin (r + p + 1))
                (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
                (alpha 1) i) =
        2))
    (hsource :
      storedSignedSequenceTwiceTrailingSourceClosureData fp r p A_hat alpha)
    (hcopy : subtractZeroExact fp) :
    A_hat (p + 2) =
      fl_householderQRPanel_R fp (r + p + 2) (p + 2) A :=
  storedSignedSequence_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_closureData
    fp r p A A_hat alpha hrows hcols hinit hStep hvec0 hself0
    hdetFirst hdetTail hvecTail hselfTail
    (storedSignedSequenceTwiceTrailingClosureData_of_sourceClosureData
      fp r p A_hat alpha hsource)
    hcopy

/-- One recursive source-facing final-panel bridge for closure data.

This is the handoff surface for the stored-loop induction: prove the current
twice-trailing first-two reflector package, prove recursive closure data for
the twice-shrunk tail, and the arbitrary-width final-panel equality follows. -/
theorem
    storedSignedSequence_final_panel_eq_qrPanel_R_of_firstTwoReflectorData_and_tailClosureData
    (fp : FPModel) (r p : Nat)
    (A : Fin (r + (p + 2) + 2) -> Fin ((p + 2) + 2) -> Real)
    (A_hat : Nat -> Fin (r + (p + 2) + 2) -> Fin ((p + 2) + 2) -> Real)
    (alpha : Nat -> Real)
    (hrows : 2 <= r + (p + 2) + 2)
    (hcols : 2 <= (p + 2) + 2)
    (hinit : A_hat 0 = A)
    (hStep : forall k (hk : k < (p + 2) + 2),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (r + (p + 2) + 2) ((p + 2) + 2) k
          (householderTrailingActiveVector (r + (p + 2) + 2)
            (Fin.mk k
              (lt_of_lt_of_le hk
                (Nat.add_le_add_right (Nat.le_add_left (p + 2) r) 2)))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (r + (p + 2) + 2)
            (householderTrailingActiveVector (r + (p + 2) + 2)
              (Fin.mk k
                (lt_of_lt_of_le hk
                  (Nat.add_le_add_right (Nat.le_add_left (p + 2) r) 2)))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (hvec0 :
      householderTrailingActiveVector (r + (p + 2) + 2)
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
          (fun a =>
            A_hat 0 a
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
          (alpha 0) =
        fl_householderNormalizedVector fp (Nat.succ_pos (r + (p + 2) + 1))
          (panelFirstColumn (Nat.succ_pos ((p + 2) + 1)) A))
    (hself0 :
      (Finset.univ : Finset (Fin (r + (p + 2) + 2))).sum
        (fun i =>
          householderTrailingActiveVector (r + (p + 2) + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
              (fun a =>
                A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
              (alpha 0) i *
            householderTrailingActiveVector (r + (p + 2) + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
              (fun a =>
                A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
              (alpha 0) i) =
        2)
    (hdetFirst :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le (r + (p + 2) + 1)))
          (Nat.succ_pos ((p + 2) + 1)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp
              (Nat.succ_pos (r + (p + 2) + 1))
              (panelFirstColumn (Nat.succ_pos ((p + 2) + 1)) A)
           let S0 := fl_householderStoredPanelStep fp
              (r + (p + 2) + 2) ((p + 2) + 2) 0 v0 1 A
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le (r + (p + 2))))
          (Nat.succ_pos (p + 2)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTail :
      (let v0 := fl_householderNormalizedVector fp
          (Nat.succ_pos (r + (p + 2) + 1))
          (panelFirstColumn (Nat.succ_pos ((p + 2) + 1)) A)
       let S0 := fl_householderStoredPanelStep fp
          (r + (p + 2) + 2) ((p + 2) + 2) 0 v0 1 A
       householderTrailingActiveVector (r + (p + 2) + 1)
            (0 : Fin (r + (p + 2) + 1))
            (panelFirstColumn (Nat.succ_pos (p + 2)) (trailingPanel S0))
            (alpha 1) =
          fl_householderNormalizedVector fp (Nat.succ_pos (r + (p + 2)))
            (panelFirstColumn (Nat.succ_pos (p + 2)) (trailingPanel S0))))
    (hselfTail :
      (let v0 := fl_householderNormalizedVector fp
          (Nat.succ_pos (r + (p + 2) + 1))
          (panelFirstColumn (Nat.succ_pos ((p + 2) + 1)) A)
       let S0 := fl_householderStoredPanelStep fp
          (r + (p + 2) + 2) ((p + 2) + 2) 0 v0 1 A
       (Finset.univ : Finset (Fin (r + (p + 2) + 1))).sum
          (fun i =>
            householderTrailingActiveVector (r + (p + 2) + 1)
                (0 : Fin (r + (p + 2) + 1))
                (panelFirstColumn (Nat.succ_pos (p + 2)) (trailingPanel S0))
                (alpha 1) i *
              householderTrailingActiveVector (r + (p + 2) + 1)
                (0 : Fin (r + (p + 2) + 1))
                (panelFirstColumn (Nat.succ_pos (p + 2)) (trailingPanel S0))
                (alpha 1) i) =
        2))
    (hfirst :
      storedSignedSequenceFirstTwoReflectorData fp
        (storedSignedSequenceTwiceTrailingSeq A_hat)
        (storedSignedSequenceTailAlpha2 alpha))
    (htail :
      storedSignedSequenceTwiceTrailingClosureData fp r p
        (storedSignedSequenceTwiceTrailingSeq A_hat)
        (storedSignedSequenceTailAlpha2 alpha))
    (hcopy : subtractZeroExact fp) :
    A_hat ((p + 2) + 2) =
      fl_householderQRPanel_R fp (r + (p + 2) + 2) ((p + 2) + 2) A := by
  have hclosure :
      storedSignedSequenceTwiceTrailingClosureData fp r (p + 2) A_hat alpha :=
    storedSignedSequenceTwiceTrailingClosureData_succ_succ_of_firstTwoReflectorData
      fp r p A_hat alpha hfirst htail
  exact
    storedSignedSequence_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_closureData
      fp r (p + 2) A A_hat alpha hrows hcols hinit hStep hvec0
      hself0 hdetFirst hdetTail hvecTail hselfTail hclosure hcopy

/-- One recursive source-facing final-panel bridge for raw source-tail facts.

This is the source-closure counterpart of
`storedSignedSequence_final_panel_eq_qrPanel_R_of_firstTwoReflectorData_and_tailClosureData`:
the current twice-trailing tail supplies raw first-two reflector facts, the
twice-shrunk tail supplies recursive source closure, and the final-panel
equality follows through the source-closure bridge. -/
theorem
    storedSignedSequence_final_panel_eq_qrPanel_R_of_firstTwoTailReflectorFacts_and_tailSourceClosureData
    (fp : FPModel) (r p : Nat)
    (A : Fin (r + (p + 2) + 2) -> Fin ((p + 2) + 2) -> Real)
    (A_hat : Nat -> Fin (r + (p + 2) + 2) -> Fin ((p + 2) + 2) -> Real)
    (alpha : Nat -> Real)
    (hrows : 2 <= r + (p + 2) + 2)
    (hcols : 2 <= (p + 2) + 2)
    (hinit : A_hat 0 = A)
    (hStep : forall k (hk : k < (p + 2) + 2),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (r + (p + 2) + 2) ((p + 2) + 2) k
          (householderTrailingActiveVector (r + (p + 2) + 2)
            (Fin.mk k
              (lt_of_lt_of_le hk
                (Nat.add_le_add_right (Nat.le_add_left (p + 2) r) 2)))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (r + (p + 2) + 2)
            (householderTrailingActiveVector (r + (p + 2) + 2)
              (Fin.mk k
                (lt_of_lt_of_le hk
                  (Nat.add_le_add_right (Nat.le_add_left (p + 2) r) 2)))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (hvec0 :
      householderTrailingActiveVector (r + (p + 2) + 2)
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
          (fun a =>
            A_hat 0 a
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
          (alpha 0) =
        fl_householderNormalizedVector fp (Nat.succ_pos (r + (p + 2) + 1))
          (panelFirstColumn (Nat.succ_pos ((p + 2) + 1)) A))
    (hself0 :
      (Finset.univ : Finset (Fin (r + (p + 2) + 2))).sum
        (fun i =>
          householderTrailingActiveVector (r + (p + 2) + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
              (fun a =>
                A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
              (alpha 0) i *
            householderTrailingActiveVector (r + (p + 2) + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
              (fun a =>
                A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
              (alpha 0) i) =
        2)
    (hdetFirst :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le (r + (p + 2) + 1)))
          (Nat.succ_pos ((p + 2) + 1)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp
              (Nat.succ_pos (r + (p + 2) + 1))
              (panelFirstColumn (Nat.succ_pos ((p + 2) + 1)) A)
           let S0 := fl_householderStoredPanelStep fp
              (r + (p + 2) + 2) ((p + 2) + 2) 0 v0 1 A
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le (r + (p + 2))))
          (Nat.succ_pos (p + 2)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTail :
      (let v0 := fl_householderNormalizedVector fp
          (Nat.succ_pos (r + (p + 2) + 1))
          (panelFirstColumn (Nat.succ_pos ((p + 2) + 1)) A)
       let S0 := fl_householderStoredPanelStep fp
          (r + (p + 2) + 2) ((p + 2) + 2) 0 v0 1 A
       householderTrailingActiveVector (r + (p + 2) + 1)
            (0 : Fin (r + (p + 2) + 1))
            (panelFirstColumn (Nat.succ_pos (p + 2)) (trailingPanel S0))
            (alpha 1) =
          fl_householderNormalizedVector fp (Nat.succ_pos (r + (p + 2)))
            (panelFirstColumn (Nat.succ_pos (p + 2)) (trailingPanel S0))))
    (hselfTail :
      (let v0 := fl_householderNormalizedVector fp
          (Nat.succ_pos (r + (p + 2) + 1))
          (panelFirstColumn (Nat.succ_pos ((p + 2) + 1)) A)
       let S0 := fl_householderStoredPanelStep fp
          (r + (p + 2) + 2) ((p + 2) + 2) 0 v0 1 A
       (Finset.univ : Finset (Fin (r + (p + 2) + 1))).sum
          (fun i =>
            householderTrailingActiveVector (r + (p + 2) + 1)
                (0 : Fin (r + (p + 2) + 1))
                (panelFirstColumn (Nat.succ_pos (p + 2)) (trailingPanel S0))
                (alpha 1) i *
              householderTrailingActiveVector (r + (p + 2) + 1)
                (0 : Fin (r + (p + 2) + 1))
                (panelFirstColumn (Nat.succ_pos (p + 2)) (trailingPanel S0))
                (alpha 1) i) =
        2))
    (hfirst : storedSignedSequenceFirstTwoTailReflectorFacts fp A_hat alpha)
    (htail :
      storedSignedSequenceTwiceTrailingSourceClosureData fp r p
        (storedSignedSequenceTwiceTrailingSeq A_hat)
        (storedSignedSequenceTailAlpha2 alpha))
    (hcopy : subtractZeroExact fp) :
    A_hat ((p + 2) + 2) =
      fl_householderQRPanel_R fp (r + (p + 2) + 2) ((p + 2) + 2) A := by
  have hsource :
      storedSignedSequenceTwiceTrailingSourceClosureData fp r (p + 2)
        A_hat alpha :=
    storedSignedSequenceTwiceTrailingSourceClosureData_succ_succ_of_firstTwoTailReflectorFacts
      fp r p A_hat alpha hfirst htail
  exact
    storedSignedSequence_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_sourceClosureData
      fp r (p + 2) A A_hat alpha hrows hcols hinit hStep hvec0
      hself0 hdetFirst hdetTail hvecTail hselfTail hsource hcopy

/-- Three-column instance of the named twice-trailing closure predicate.

The first two steps are supplied by `storedSignedSequenceFirstTwoReflectorData`;
the remaining twice-trailing one-column tail is closed by the named one-column
closure above. -/
theorem storedSignedSequenceTwiceTrailingFinalClosed_three_col_of_firstTwoReflectorData
    (fp : FPModel) {m : Nat}
    (A_hat : Nat -> Fin (((m + 1) + 2) + 2) -> Fin ((1 + 2) + 2) -> Real)
    (alpha : Nat -> Real)
    (hdata :
      storedSignedSequenceFirstTwoReflectorData fp
        (storedSignedSequenceTwiceTrailingSeq A_hat)
        (storedSignedSequenceTailAlpha2 alpha))
    (hvecTailTail :
      householderTrailingActiveVector (m + 1)
          (Fin.mk 0 (Nat.succ_pos m))
          (fun a =>
            trailingPanel (trailingPanel
                (storedSignedSequenceTwiceTrailingSeq A_hat 2)) a
              (Fin.mk 0 (Nat.succ_pos 0)))
          (alpha 4) =
        fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos 0)
            (trailingPanel (trailingPanel
              (storedSignedSequenceTwiceTrailingSeq A_hat 2)))))
    (hselfTailTail :
      (Finset.univ : Finset (Fin (m + 1))).sum
        (fun i =>
          householderTrailingActiveVector (m + 1)
              (Fin.mk 0 (Nat.succ_pos m))
              (fun a =>
                trailingPanel (trailingPanel
                    (storedSignedSequenceTwiceTrailingSeq A_hat 2)) a
                  (Fin.mk 0 (Nat.succ_pos 0)))
              (alpha 4) i *
            householderTrailingActiveVector (m + 1)
              (Fin.mk 0 (Nat.succ_pos m))
              (fun a =>
                trailingPanel (trailingPanel
                    (storedSignedSequenceTwiceTrailingSeq A_hat 2)) a
                  (Fin.mk 0 (Nat.succ_pos 0)))
              (alpha 4) i) =
        2)
    (hdetTailTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (trailingPanel (trailingPanel
            (storedSignedSequenceTwiceTrailingSeq A_hat 2)))
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hcopy : subtractZeroExact fp) :
    storedSignedSequenceTwiceTrailingFinalClosed fp (by omega) A_hat alpha := by
  refine
    storedSignedSequenceTwiceTrailingFinalClosed_succ_succ_of_firstTwoReflectorData
      fp (by omega) A_hat alpha hdata hcopy ?_
  exact
    storedSignedSequenceTwiceTrailingFinalClosed_one_col_of_reflector_self_dot
      fp (storedSignedSequenceTwiceTrailingSeq A_hat)
      (storedSignedSequenceTailAlpha2 alpha)
      (by
        simpa [storedSignedSequenceTwiceTrailingSeq,
          storedSignedSequenceTailAlpha2] using hvecTailTail)
      (by
        simpa [storedSignedSequenceTwiceTrailingSeq,
          storedSignedSequenceTailAlpha2] using hselfTailTail)
      (by
        simpa [storedSignedSequenceTwiceTrailingSeq] using hdetTailTail)

/-- Four-column instance of the named twice-trailing closure predicate.

The first two steps are supplied by `storedSignedSequenceFirstTwoReflectorData`;
the remaining twice-trailing two-column tail is closed by the named two-column
closure above. -/
theorem storedSignedSequenceTwiceTrailingFinalClosed_four_col_of_firstTwoReflectorData
    (fp : FPModel) {m : Nat}
    (A_hat : Nat -> Fin (((m + 2) + 2) + 2) -> Fin ((2 + 2) + 2) -> Real)
    (alpha : Nat -> Real)
    (hdata :
      storedSignedSequenceFirstTwoReflectorData fp
        (storedSignedSequenceTwiceTrailingSeq A_hat)
        (storedSignedSequenceTailAlpha2 alpha))
    (hvecTailTail0 :
      householderTrailingActiveVector (m + 2)
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
          (fun a =>
            trailingPanel (trailingPanel
                (storedSignedSequenceTwiceTrailingSeq A_hat 2)) a
              (Fin.mk 0 (Nat.succ_pos 1)))
          (alpha 4) =
        fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1)
            (trailingPanel (trailingPanel
              (storedSignedSequenceTwiceTrailingSeq A_hat 2)))))
    (hselfTailTail0 :
      (Finset.univ : Finset (Fin (m + 2))).sum
        (fun i =>
          householderTrailingActiveVector (m + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
              (fun a =>
                trailingPanel (trailingPanel
                    (storedSignedSequenceTwiceTrailingSeq A_hat 2)) a
                  (Fin.mk 0 (Nat.succ_pos 1)))
              (alpha 4) i *
            householderTrailingActiveVector (m + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
              (fun a =>
                trailingPanel (trailingPanel
                    (storedSignedSequenceTwiceTrailingSeq A_hat 2)) a
                  (Fin.mk 0 (Nat.succ_pos 1)))
              (alpha 4) i) =
        2)
    (hdetTailTailFirst :
      Ne (Matrix.det
        (qrLeadingBlock
          (trailingPanel (trailingPanel
            (storedSignedSequenceTwiceTrailingSeq A_hat 2)))
          (Nat.succ_le_succ (Nat.zero_le (m + 1)))
          (Nat.succ_pos 1) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTailTailTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
              (panelFirstColumn (Nat.succ_pos 1)
                (trailingPanel (trailingPanel
                  (storedSignedSequenceTwiceTrailingSeq A_hat 2))))
           let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1
              (trailingPanel (trailingPanel
                (storedSignedSequenceTwiceTrailingSeq A_hat 2)))
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTailTail1 :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1)
            (trailingPanel (trailingPanel
              (storedSignedSequenceTwiceTrailingSeq A_hat 2))))
       let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1
          (trailingPanel (trailingPanel
            (storedSignedSequenceTwiceTrailingSeq A_hat 2)))
       householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
            (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0)) (alpha 5) =
          fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))))
    (hselfTailTail1 :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1)
            (trailingPanel (trailingPanel
              (storedSignedSequenceTwiceTrailingSeq A_hat 2))))
       let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1
          (trailingPanel (trailingPanel
            (storedSignedSequenceTwiceTrailingSeq A_hat 2)))
       (Finset.univ : Finset (Fin (m + 1))).sum
          (fun i =>
            householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))
                (alpha 5) i *
              householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))
                (alpha 5) i) =
        2))
    (hcopy : subtractZeroExact fp) :
    storedSignedSequenceTwiceTrailingFinalClosed fp (by omega) A_hat alpha := by
  refine
    storedSignedSequenceTwiceTrailingFinalClosed_succ_succ_of_firstTwoReflectorData
      fp (by omega) A_hat alpha hdata hcopy ?_
  exact
    storedSignedSequenceTwiceTrailingFinalClosed_two_col_of_reflector_self_dot
      fp (storedSignedSequenceTwiceTrailingSeq A_hat)
      (storedSignedSequenceTailAlpha2 alpha)
      (by
        simpa [storedSignedSequenceTwiceTrailingSeq,
          storedSignedSequenceTailAlpha2] using hvecTailTail0)
      (by
        simpa [storedSignedSequenceTwiceTrailingSeq,
          storedSignedSequenceTailAlpha2] using hselfTailTail0)
      (by
        simpa [storedSignedSequenceTwiceTrailingSeq] using hdetTailTailFirst)
      (by
        simpa [storedSignedSequenceTwiceTrailingSeq] using hdetTailTailTail)
      (by
        simpa [storedSignedSequenceTwiceTrailingSeq,
          storedSignedSequenceTailAlpha2] using hvecTailTail1)
      (by
        simpa [storedSignedSequenceTwiceTrailingSeq,
          storedSignedSequenceTailAlpha2] using hselfTailTail1)
      hcopy

/-- Three-column final-panel bridge from the twice-trailing one-column base
case.

This packages the first nontrivial use of the twice-trailing recurrence bridge:
after two leading stored steps, the remaining one-column tail is closed by
`storedSignedSequence_twice_trailing_one_col_tail_final_of_tail_reflector_self_dot`. -/
theorem
    storedSignedSequence_three_col_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_subtractZeroExact
    (fp : FPModel) {m : Nat}
    (hmn : 1 + 2 <= (m + 1) + 2)
    (A : Fin ((m + 1) + 2) -> Fin (1 + 2) -> Real)
    (A_hat : Nat -> Fin ((m + 1) + 2) -> Fin (1 + 2) -> Real)
    (alpha : Nat -> Real)
    (hrows : 2 <= (m + 1) + 2)
    (hcols : 2 <= 1 + 2)
    (hinit : A_hat 0 = A)
    (hStep : forall k (hk : k < 1 + 2),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp ((m + 1) + 2) (1 + 2) k
          (householderTrailingActiveVector ((m + 1) + 2)
            (Fin.mk k (lt_of_lt_of_le hk hmn))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec ((m + 1) + 2)
            (householderTrailingActiveVector ((m + 1) + 2)
              (Fin.mk k (lt_of_lt_of_le hk hmn))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (hvec0 :
      householderTrailingActiveVector ((m + 1) + 2)
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
          (fun a =>
            A_hat 0 a
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
          (alpha 0) =
        fl_householderNormalizedVector fp (Nat.succ_pos ((m + 1) + 1))
          (panelFirstColumn (Nat.succ_pos (1 + 1)) A))
    (hself0 :
      (Finset.univ : Finset (Fin ((m + 1) + 2))).sum
        (fun i =>
          householderTrailingActiveVector ((m + 1) + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
              (fun a =>
                A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
              (alpha 0) i *
            householderTrailingActiveVector ((m + 1) + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
              (fun a =>
                A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
              (alpha 0) i) =
        2)
    (hdetFirst :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le ((m + 1) + 1)))
          (Nat.succ_pos (1 + 1)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos ((m + 1) + 1))
              (panelFirstColumn (Nat.succ_pos (1 + 1)) A)
           let S0 := fl_householderStoredPanelStep fp ((m + 1) + 2) (1 + 2) 0 v0 1 A
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le (m + 1)))
          (Nat.succ_pos 1) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTail :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos ((m + 1) + 1))
          (panelFirstColumn (Nat.succ_pos (1 + 1)) A)
       let S0 := fl_householderStoredPanelStep fp ((m + 1) + 2) (1 + 2) 0 v0 1 A
       householderTrailingActiveVector ((m + 1) + 1) (0 : Fin ((m + 1) + 1))
            (panelFirstColumn (Nat.succ_pos 1) (trailingPanel S0)) (alpha 1) =
          fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
            (panelFirstColumn (Nat.succ_pos 1) (trailingPanel S0))))
    (hselfTail :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos ((m + 1) + 1))
          (panelFirstColumn (Nat.succ_pos (1 + 1)) A)
       let S0 := fl_householderStoredPanelStep fp ((m + 1) + 2) (1 + 2) 0 v0 1 A
       (Finset.univ : Finset (Fin ((m + 1) + 1))).sum
          (fun i =>
            householderTrailingActiveVector ((m + 1) + 1) (0 : Fin ((m + 1) + 1))
                (panelFirstColumn (Nat.succ_pos 1) (trailingPanel S0))
                (alpha 1) i *
              householderTrailingActiveVector ((m + 1) + 1) (0 : Fin ((m + 1) + 1))
                (panelFirstColumn (Nat.succ_pos 1) (trailingPanel S0))
                (alpha 1) i) =
        2))
    (hvecTailTail :
      householderTrailingActiveVector (m + 1)
          (Fin.mk 0 (Nat.succ_pos m))
          (fun a =>
            trailingPanel (trailingPanel (A_hat 2)) a
              (Fin.mk 0 (Nat.succ_pos 0)))
          (alpha 2) =
        fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos 0)
            (trailingPanel (trailingPanel (A_hat 2)))))
    (hselfTailTail :
      (Finset.univ : Finset (Fin (m + 1))).sum
        (fun i =>
          householderTrailingActiveVector (m + 1)
              (Fin.mk 0 (Nat.succ_pos m))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (Nat.succ_pos 0)))
              (alpha 2) i *
            householderTrailingActiveVector (m + 1)
              (Fin.mk 0 (Nat.succ_pos m))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (Nat.succ_pos 0)))
              (alpha 2) i) =
        2)
    (hdetTailTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (trailingPanel (trailingPanel (A_hat 2)))
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hcopy : subtractZeroExact fp) :
    A_hat (1 + 2) =
      fl_householderQRPanel_R fp ((m + 1) + 2) (1 + 2) A := by
  have hTailClosed :
      storedSignedSequenceTwiceTrailingFinalClosed fp hmn A_hat alpha := by
    exact
      storedSignedSequenceTwiceTrailingFinalClosed_one_col_of_reflector_self_dot
        fp A_hat alpha hvecTailTail hselfTailTail hdetTailTail
  exact
    storedSignedSequence_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_twice_trailing_recurrence_bridge
      fp hmn A A_hat alpha hrows hcols hinit hStep hvec0 hself0
      hdetFirst hdetTail hvecTail hselfTail hcopy hTailClosed

/-- Four-column final-panel bridge from the twice-trailing two-column base case.

This is the next endpoint rung toward the general final-panel induction: after
two leading stored steps, the remaining two-column twice-trailing tail is closed
by the two-column final-panel bridge. -/
theorem
    storedSignedSequence_four_col_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_subtractZeroExact
    (fp : FPModel) {m : Nat}
    (hmn : 2 + 2 <= (m + 2) + 2)
    (A : Fin ((m + 2) + 2) -> Fin (2 + 2) -> Real)
    (A_hat : Nat -> Fin ((m + 2) + 2) -> Fin (2 + 2) -> Real)
    (alpha : Nat -> Real)
    (hrows : 2 <= (m + 2) + 2)
    (hcols : 2 <= 2 + 2)
    (hinit : A_hat 0 = A)
    (hStep : forall k (hk : k < 2 + 2),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp ((m + 2) + 2) (2 + 2) k
          (householderTrailingActiveVector ((m + 2) + 2)
            (Fin.mk k (lt_of_lt_of_le hk hmn))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec ((m + 2) + 2)
            (householderTrailingActiveVector ((m + 2) + 2)
              (Fin.mk k (lt_of_lt_of_le hk hmn))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (hvec0 :
      householderTrailingActiveVector ((m + 2) + 2)
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
          (fun a =>
            A_hat 0 a
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
          (alpha 0) =
        fl_householderNormalizedVector fp (Nat.succ_pos ((m + 2) + 1))
          (panelFirstColumn (Nat.succ_pos (2 + 1)) A))
    (hself0 :
      (Finset.univ : Finset (Fin ((m + 2) + 2))).sum
        (fun i =>
          householderTrailingActiveVector ((m + 2) + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
              (fun a =>
                A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
              (alpha 0) i *
            householderTrailingActiveVector ((m + 2) + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
              (fun a =>
                A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
              (alpha 0) i) =
        2)
    (hdetFirst :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le ((m + 2) + 1)))
          (Nat.succ_pos (2 + 1)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos ((m + 2) + 1))
              (panelFirstColumn (Nat.succ_pos (2 + 1)) A)
           let S0 := fl_householderStoredPanelStep fp ((m + 2) + 2) (2 + 2) 0 v0 1 A
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le (m + 2)))
          (Nat.succ_pos 2) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTail :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos ((m + 2) + 1))
          (panelFirstColumn (Nat.succ_pos (2 + 1)) A)
       let S0 := fl_householderStoredPanelStep fp ((m + 2) + 2) (2 + 2) 0 v0 1 A
       householderTrailingActiveVector ((m + 2) + 1) (0 : Fin ((m + 2) + 1))
            (panelFirstColumn (Nat.succ_pos 2) (trailingPanel S0)) (alpha 1) =
          fl_householderNormalizedVector fp (Nat.succ_pos (m + 2))
            (panelFirstColumn (Nat.succ_pos 2) (trailingPanel S0))))
    (hselfTail :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos ((m + 2) + 1))
          (panelFirstColumn (Nat.succ_pos (2 + 1)) A)
       let S0 := fl_householderStoredPanelStep fp ((m + 2) + 2) (2 + 2) 0 v0 1 A
       (Finset.univ : Finset (Fin ((m + 2) + 1))).sum
          (fun i =>
            householderTrailingActiveVector ((m + 2) + 1) (0 : Fin ((m + 2) + 1))
                (panelFirstColumn (Nat.succ_pos 2) (trailingPanel S0))
                (alpha 1) i *
              householderTrailingActiveVector ((m + 2) + 1) (0 : Fin ((m + 2) + 1))
                (panelFirstColumn (Nat.succ_pos 2) (trailingPanel S0))
                (alpha 1) i) =
        2))
    (hvecTailTail0 :
      householderTrailingActiveVector (m + 2)
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
          (fun a =>
            trailingPanel (trailingPanel (A_hat 2)) a
              (Fin.mk 0 (Nat.succ_pos 1)))
          (alpha 2) =
        fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1)
            (trailingPanel (trailingPanel (A_hat 2)))))
    (hselfTailTail0 :
      (Finset.univ : Finset (Fin (m + 2))).sum
        (fun i =>
          householderTrailingActiveVector (m + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (Nat.succ_pos 1)))
              (alpha 2) i *
            householderTrailingActiveVector (m + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (Nat.succ_pos 1)))
              (alpha 2) i) =
        2)
    (hdetTailTailFirst :
      Ne (Matrix.det
        (qrLeadingBlock
          (trailingPanel (trailingPanel (A_hat 2)))
          (Nat.succ_le_succ (Nat.zero_le (m + 1)))
          (Nat.succ_pos 1) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTailTailTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
              (panelFirstColumn (Nat.succ_pos 1)
                (trailingPanel (trailingPanel (A_hat 2))))
           let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1
              (trailingPanel (trailingPanel (A_hat 2)))
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTailTail1 :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1)
            (trailingPanel (trailingPanel (A_hat 2))))
       let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1
          (trailingPanel (trailingPanel (A_hat 2)))
       householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
            (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0)) (alpha 3) =
          fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))))
    (hselfTailTail1 :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1)
            (trailingPanel (trailingPanel (A_hat 2))))
       let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1
          (trailingPanel (trailingPanel (A_hat 2)))
       (Finset.univ : Finset (Fin (m + 1))).sum
          (fun i =>
            householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))
                (alpha 3) i *
              householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))
                (alpha 3) i) =
        2))
    (hcopy : subtractZeroExact fp) :
    A_hat (2 + 2) =
      fl_householderQRPanel_R fp ((m + 2) + 2) (2 + 2) A := by
  have hTailClosed :
      storedSignedSequenceTwiceTrailingFinalClosed fp hmn A_hat alpha := by
    exact
      storedSignedSequenceTwiceTrailingFinalClosed_two_col_of_reflector_self_dot
        fp A_hat alpha hvecTailTail0 hselfTailTail0
        hdetTailTailFirst hdetTailTailTail hvecTailTail1 hselfTailTail1
        hcopy
  exact
    storedSignedSequence_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_twice_trailing_recurrence_bridge
      fp hmn A A_hat alpha hrows hcols hinit hStep hvec0 hself0
      hdetFirst hdetTail hvecTail hselfTail hcopy hTailClosed

/-- Three-column final-panel closure for the twice-trailing tail sequence.

This is the next recursive tail closure after the two-column base: after two
leading stored steps have been peeled off, a three-column twice-trailing tail is
closed by the already-proved three-column final-panel bridge. -/
theorem storedSignedSequence_twice_trailing_three_col_tail_final_of_tail_reflector_self_dot
    (fp : FPModel) {m : Nat}
    (A_hat : Nat -> Fin (((m + 1) + 2) + 2) -> Fin ((1 + 2) + 2) -> Real)
    (alpha : Nat -> Real)
    (hTailRec : forall k (hk : k < 1 + 2),
      (fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) (k + 1) =
        fl_householderStoredPanelStep fp ((m + 1) + 2) (1 + 2) k
          (householderTrailingActiveVector ((m + 1) + 2)
            (Fin.mk k (by omega))
            (fun a => (fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) k a
              (Fin.mk k hk)) (alpha (k + 2)))
          (householderBetaSpec ((m + 1) + 2)
            (householderTrailingActiveVector ((m + 1) + 2)
              (Fin.mk k (by omega))
              (fun a => (fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) k a
                (Fin.mk k hk)) (alpha (k + 2))))
          ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) k))
    (hvecTailTail0 :
      householderTrailingActiveVector ((m + 1) + 2)
          (Fin.mk 0 (by omega))
          (fun a =>
            trailingPanel (trailingPanel (A_hat 2)) a
              (Fin.mk 0 (by omega)))
          (alpha 2) =
        fl_householderNormalizedVector fp (Nat.succ_pos ((m + 1) + 1))
          (panelFirstColumn (Nat.succ_pos (1 + 1))
            (trailingPanel (trailingPanel (A_hat 2)))))
    (hselfTailTail0 :
      (Finset.univ : Finset (Fin ((m + 1) + 2))).sum
        (fun i =>
          householderTrailingActiveVector ((m + 1) + 2)
              (Fin.mk 0 (by omega))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (by omega)))
              (alpha 2) i *
            householderTrailingActiveVector ((m + 1) + 2)
              (Fin.mk 0 (by omega))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (by omega)))
              (alpha 2) i) =
        2)
    (hdetTailTailFirst :
      Ne (Matrix.det
        (qrLeadingBlock
          (trailingPanel (trailingPanel (A_hat 2)))
          (Nat.succ_le_succ (Nat.zero_le ((m + 1) + 1)))
          (Nat.succ_pos (1 + 1)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTailTailTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos ((m + 1) + 1))
              (panelFirstColumn (Nat.succ_pos (1 + 1))
                (trailingPanel (trailingPanel (A_hat 2))))
           let S0 := fl_householderStoredPanelStep fp ((m + 1) + 2) (1 + 2) 0 v0 1
              (trailingPanel (trailingPanel (A_hat 2)))
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le (m + 1)))
          (Nat.succ_pos 1) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTailTail1 :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos ((m + 1) + 1))
          (panelFirstColumn (Nat.succ_pos (1 + 1))
            (trailingPanel (trailingPanel (A_hat 2))))
       let S0 := fl_householderStoredPanelStep fp ((m + 1) + 2) (1 + 2) 0 v0 1
          (trailingPanel (trailingPanel (A_hat 2)))
       householderTrailingActiveVector ((m + 1) + 1) (0 : Fin ((m + 1) + 1))
            (panelFirstColumn (Nat.succ_pos 1) (trailingPanel S0)) (alpha 3) =
          fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
            (panelFirstColumn (Nat.succ_pos 1) (trailingPanel S0))))
    (hselfTailTail1 :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos ((m + 1) + 1))
          (panelFirstColumn (Nat.succ_pos (1 + 1))
            (trailingPanel (trailingPanel (A_hat 2))))
       let S0 := fl_householderStoredPanelStep fp ((m + 1) + 2) (1 + 2) 0 v0 1
          (trailingPanel (trailingPanel (A_hat 2)))
       (Finset.univ : Finset (Fin ((m + 1) + 1))).sum
          (fun i =>
            householderTrailingActiveVector ((m + 1) + 1) (0 : Fin ((m + 1) + 1))
                (panelFirstColumn (Nat.succ_pos 1) (trailingPanel S0))
                (alpha 3) i *
              householderTrailingActiveVector ((m + 1) + 1) (0 : Fin ((m + 1) + 1))
                (panelFirstColumn (Nat.succ_pos 1) (trailingPanel S0))
                (alpha 3) i) =
        2))
    (hvecTailTail2 :
      householderTrailingActiveVector (m + 1)
          (Fin.mk 0 (Nat.succ_pos m))
          (fun a =>
            trailingPanel
                (trailingPanel
                  ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2)) a
              (Fin.mk 0 (Nat.succ_pos 0)))
          (alpha 4) =
        fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos 0)
            (trailingPanel
              (trailingPanel
                ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2)))))
    (hselfTailTail2 :
      (Finset.univ : Finset (Fin (m + 1))).sum
        (fun i =>
          householderTrailingActiveVector (m + 1)
              (Fin.mk 0 (Nat.succ_pos m))
              (fun a =>
                trailingPanel
                    (trailingPanel
                      ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2)) a
                  (Fin.mk 0 (Nat.succ_pos 0)))
              (alpha 4) i *
            householderTrailingActiveVector (m + 1)
              (Fin.mk 0 (Nat.succ_pos m))
              (fun a =>
                trailingPanel
                    (trailingPanel
                      ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2)) a
                  (Fin.mk 0 (Nat.succ_pos 0)))
              (alpha 4) i) =
        2)
    (hdetTailTailTailTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (trailingPanel
            (trailingPanel
              ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2)))
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hcopy : subtractZeroExact fp) :
    trailingPanel (trailingPanel (A_hat ((1 + 2) + 2))) =
      fl_householderQRPanel_R fp ((m + 1) + 2) (1 + 2)
        (trailingPanel (trailingPanel (A_hat 2))) := by
  let TailSeq : Nat -> Fin ((m + 1) + 2) -> Fin (1 + 2) -> Real :=
    fun t => trailingPanel (trailingPanel (A_hat (t + 2)))
  let TailAlpha : Nat -> Real := fun t => alpha (t + 2)
  have hTailStep : forall k (hk : k < 1 + 2),
      TailSeq (k + 1) =
        fl_householderStoredPanelStep fp ((m + 1) + 2) (1 + 2) k
          (householderTrailingActiveVector ((m + 1) + 2)
            (Fin.mk k (lt_of_lt_of_le hk (by omega)))
            (fun a => TailSeq k a (Fin.mk k hk)) (TailAlpha k))
          (householderBetaSpec ((m + 1) + 2)
            (householderTrailingActiveVector ((m + 1) + 2)
              (Fin.mk k (lt_of_lt_of_le hk (by omega)))
              (fun a => TailSeq k a (Fin.mk k hk)) (TailAlpha k)))
          (TailSeq k) := by
    intro k hk
    simpa [TailSeq, TailAlpha] using hTailRec k hk
  have htail :=
    storedSignedSequence_three_col_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_subtractZeroExact
      fp (by omega) (TailSeq 0) TailSeq TailAlpha (by omega) (by omega)
      rfl hTailStep
      (by
        simpa [TailSeq, TailAlpha] using hvecTailTail0)
      (by
        simpa [TailSeq, TailAlpha] using hselfTailTail0)
      (by
        simpa [TailSeq] using hdetTailTailFirst)
      (by
        simpa [TailSeq] using hdetTailTailTail)
      (by
        simpa [TailSeq, TailAlpha] using hvecTailTail1)
      (by
        simpa [TailSeq, TailAlpha] using hselfTailTail1)
      (by
        simpa [TailSeq, TailAlpha] using hvecTailTail2)
      (by
        simpa [TailSeq, TailAlpha] using hselfTailTail2)
      (by
        simpa [TailSeq] using hdetTailTailTailTail)
      hcopy
  simpa [TailSeq] using htail

/-- Five-column final-panel bridge from the twice-trailing three-column tail
closure.

This is an induction-rung theorem: after two leading stored steps, the
remaining three-column twice-trailing tail is closed by the three-column
final-panel bridge.  It does not close the arbitrary-width source theorem, but
it removes the next fixed-width endpoint from the final-panel queue. -/
theorem
    storedSignedSequence_five_col_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_subtractZeroExact
    (fp : FPModel) {m : Nat}
    (hmn : (1 + 2) + 2 <= (((m + 1) + 2) + 2))
    (A : Fin (((m + 1) + 2) + 2) -> Fin ((1 + 2) + 2) -> Real)
    (A_hat : Nat -> Fin (((m + 1) + 2) + 2) -> Fin ((1 + 2) + 2) -> Real)
    (alpha : Nat -> Real)
    (hrows : 2 <= (((m + 1) + 2) + 2))
    (hcols : 2 <= (1 + 2) + 2)
    (hinit : A_hat 0 = A)
    (hStep : forall k (hk : k < (1 + 2) + 2),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (((m + 1) + 2) + 2) ((1 + 2) + 2) k
          (householderTrailingActiveVector (((m + 1) + 2) + 2)
            (Fin.mk k (lt_of_lt_of_le hk hmn))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (((m + 1) + 2) + 2)
            (householderTrailingActiveVector (((m + 1) + 2) + 2)
              (Fin.mk k (lt_of_lt_of_le hk hmn))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (hvec0 :
      householderTrailingActiveVector (((m + 1) + 2) + 2)
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
          (fun a =>
            A_hat 0 a
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
          (alpha 0) =
        fl_householderNormalizedVector fp (Nat.succ_pos (((m + 1) + 2) + 1))
          (panelFirstColumn (Nat.succ_pos ((1 + 2) + 1)) A))
    (hself0 :
      (Finset.univ : Finset (Fin (((m + 1) + 2) + 2))).sum
        (fun i =>
          householderTrailingActiveVector (((m + 1) + 2) + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
              (fun a =>
                A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
              (alpha 0) i *
            householderTrailingActiveVector (((m + 1) + 2) + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
              (fun a =>
                A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
              (alpha 0) i) =
        2)
    (hdetFirst :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le (((m + 1) + 2) + 1)))
          (Nat.succ_pos ((1 + 2) + 1)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp
              (Nat.succ_pos (((m + 1) + 2) + 1))
              (panelFirstColumn (Nat.succ_pos ((1 + 2) + 1)) A)
           let S0 := fl_householderStoredPanelStep fp
              (((m + 1) + 2) + 2) ((1 + 2) + 2) 0 v0 1 A
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le ((m + 1) + 2)))
          (Nat.succ_pos (1 + 2)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTail :
      (let v0 := fl_householderNormalizedVector fp
          (Nat.succ_pos (((m + 1) + 2) + 1))
          (panelFirstColumn (Nat.succ_pos ((1 + 2) + 1)) A)
       let S0 := fl_householderStoredPanelStep fp
          (((m + 1) + 2) + 2) ((1 + 2) + 2) 0 v0 1 A
       householderTrailingActiveVector (((m + 1) + 2) + 1)
            (0 : Fin (((m + 1) + 2) + 1))
            (panelFirstColumn (Nat.succ_pos (1 + 2)) (trailingPanel S0))
            (alpha 1) =
          fl_householderNormalizedVector fp (Nat.succ_pos ((m + 1) + 2))
            (panelFirstColumn (Nat.succ_pos (1 + 2)) (trailingPanel S0))))
    (hselfTail :
      (let v0 := fl_householderNormalizedVector fp
          (Nat.succ_pos (((m + 1) + 2) + 1))
          (panelFirstColumn (Nat.succ_pos ((1 + 2) + 1)) A)
       let S0 := fl_householderStoredPanelStep fp
          (((m + 1) + 2) + 2) ((1 + 2) + 2) 0 v0 1 A
       (Finset.univ : Finset (Fin (((m + 1) + 2) + 1))).sum
          (fun i =>
            householderTrailingActiveVector (((m + 1) + 2) + 1)
                (0 : Fin (((m + 1) + 2) + 1))
                (panelFirstColumn (Nat.succ_pos (1 + 2)) (trailingPanel S0))
                (alpha 1) i *
              householderTrailingActiveVector (((m + 1) + 2) + 1)
                (0 : Fin (((m + 1) + 2) + 1))
                (panelFirstColumn (Nat.succ_pos (1 + 2)) (trailingPanel S0))
                (alpha 1) i) =
        2))
    (hvecTailTail0 :
      householderTrailingActiveVector ((m + 1) + 2)
          (Fin.mk 0 (by omega))
          (fun a =>
            trailingPanel (trailingPanel (A_hat 2)) a
              (Fin.mk 0 (by omega)))
          (alpha 2) =
        fl_householderNormalizedVector fp (Nat.succ_pos ((m + 1) + 1))
          (panelFirstColumn (Nat.succ_pos (1 + 1))
            (trailingPanel (trailingPanel (A_hat 2)))))
    (hselfTailTail0 :
      (Finset.univ : Finset (Fin ((m + 1) + 2))).sum
        (fun i =>
          householderTrailingActiveVector ((m + 1) + 2)
              (Fin.mk 0 (by omega))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (by omega)))
              (alpha 2) i *
            householderTrailingActiveVector ((m + 1) + 2)
              (Fin.mk 0 (by omega))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (by omega)))
              (alpha 2) i) =
        2)
    (hdetTailTailFirst :
      Ne (Matrix.det
        (qrLeadingBlock
          (trailingPanel (trailingPanel (A_hat 2)))
          (Nat.succ_le_succ (Nat.zero_le ((m + 1) + 1)))
          (Nat.succ_pos (1 + 1)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTailTailTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos ((m + 1) + 1))
              (panelFirstColumn (Nat.succ_pos (1 + 1))
                (trailingPanel (trailingPanel (A_hat 2))))
           let S0 := fl_householderStoredPanelStep fp ((m + 1) + 2) (1 + 2) 0 v0 1
              (trailingPanel (trailingPanel (A_hat 2)))
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le (m + 1)))
          (Nat.succ_pos 1) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTailTail1 :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos ((m + 1) + 1))
          (panelFirstColumn (Nat.succ_pos (1 + 1))
            (trailingPanel (trailingPanel (A_hat 2))))
       let S0 := fl_householderStoredPanelStep fp ((m + 1) + 2) (1 + 2) 0 v0 1
          (trailingPanel (trailingPanel (A_hat 2)))
       householderTrailingActiveVector ((m + 1) + 1) (0 : Fin ((m + 1) + 1))
            (panelFirstColumn (Nat.succ_pos 1) (trailingPanel S0)) (alpha 3) =
          fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
            (panelFirstColumn (Nat.succ_pos 1) (trailingPanel S0))))
    (hselfTailTail1 :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos ((m + 1) + 1))
          (panelFirstColumn (Nat.succ_pos (1 + 1))
            (trailingPanel (trailingPanel (A_hat 2))))
       let S0 := fl_householderStoredPanelStep fp ((m + 1) + 2) (1 + 2) 0 v0 1
          (trailingPanel (trailingPanel (A_hat 2)))
       (Finset.univ : Finset (Fin ((m + 1) + 1))).sum
          (fun i =>
            householderTrailingActiveVector ((m + 1) + 1) (0 : Fin ((m + 1) + 1))
                (panelFirstColumn (Nat.succ_pos 1) (trailingPanel S0))
                (alpha 3) i *
              householderTrailingActiveVector ((m + 1) + 1) (0 : Fin ((m + 1) + 1))
                (panelFirstColumn (Nat.succ_pos 1) (trailingPanel S0))
                (alpha 3) i) =
        2))
    (hvecTailTail2 :
      householderTrailingActiveVector (m + 1)
          (Fin.mk 0 (Nat.succ_pos m))
          (fun a =>
            trailingPanel
                (trailingPanel
                  ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2)) a
              (Fin.mk 0 (Nat.succ_pos 0)))
          (alpha 4) =
        fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos 0)
            (trailingPanel
              (trailingPanel
                ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2)))))
    (hselfTailTail2 :
      (Finset.univ : Finset (Fin (m + 1))).sum
        (fun i =>
          householderTrailingActiveVector (m + 1)
              (Fin.mk 0 (Nat.succ_pos m))
              (fun a =>
                trailingPanel
                    (trailingPanel
                      ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2)) a
                  (Fin.mk 0 (Nat.succ_pos 0)))
              (alpha 4) i *
            householderTrailingActiveVector (m + 1)
              (Fin.mk 0 (Nat.succ_pos m))
              (fun a =>
                trailingPanel
                    (trailingPanel
                      ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2)) a
                  (Fin.mk 0 (Nat.succ_pos 0)))
              (alpha 4) i) =
        2)
    (hdetTailTailTailTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (trailingPanel
            (trailingPanel
              ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2)))
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hcopy : subtractZeroExact fp) :
    A_hat ((1 + 2) + 2) =
      fl_householderQRPanel_R fp (((m + 1) + 2) + 2) ((1 + 2) + 2) A := by
  have hTailData :
      storedSignedSequenceFirstTwoReflectorData fp
        (storedSignedSequenceTwiceTrailingSeq A_hat)
        (storedSignedSequenceTailAlpha2 alpha) :=
    storedSignedSequenceFirstTwoReflectorData_of_tail_reflector_self_dot
      fp A_hat alpha hvecTailTail0 hselfTailTail0 hdetTailTailFirst
      hdetTailTailTail hvecTailTail1 hselfTailTail1
  have hTailClosed :
      storedSignedSequenceTwiceTrailingFinalClosed fp hmn A_hat alpha := by
    exact
      storedSignedSequenceTwiceTrailingFinalClosed_three_col_of_firstTwoReflectorData
        fp A_hat alpha hTailData
        (by
          simpa [storedSignedSequenceTwiceTrailingSeq,
            storedSignedSequenceTailAlpha2] using hvecTailTail2)
        (by
          simpa [storedSignedSequenceTwiceTrailingSeq,
            storedSignedSequenceTailAlpha2] using hselfTailTail2)
        (by
          simpa [storedSignedSequenceTwiceTrailingSeq] using hdetTailTailTailTail)
        hcopy
  exact
    storedSignedSequence_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_twice_trailing_recurrence_bridge
      fp hmn A A_hat alpha hrows hcols hinit hStep hvec0 hself0
      hdetFirst hdetTail hvecTail hselfTail hcopy hTailClosed

/-- Four-column final-panel closure for a twice-trailing tail sequence.

This packages the already-proved four-column endpoint for the smaller panel
that remains after two leading stored steps have been peeled off.  It is a
dependency for the next fixed-width endpoint and keeps the arbitrary-width
source theorem open until the full reflector-data induction is available. -/
theorem storedSignedSequence_twice_trailing_four_col_tail_final_of_tail_reflector_self_dot
    (fp : FPModel) {m : Nat}
    (A_tail : Fin ((m + 2) + 2) -> Fin (2 + 2) -> Real)
    (A_hat : Nat -> Fin (((m + 2) + 2) + 2) -> Fin ((2 + 2) + 2) -> Real)
    (alpha : Nat -> Real)
    (hinitTail : trailingPanel (trailingPanel (A_hat 2)) = A_tail)
    (hTailRec : forall k (hk : k < 2 + 2),
      (fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) (k + 1) =
        fl_householderStoredPanelStep fp ((m + 2) + 2) (2 + 2) k
          (householderTrailingActiveVector ((m + 2) + 2)
            (Fin.mk k (by omega))
            (fun a => (fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) k a
              (Fin.mk k hk)) (alpha (k + 2)))
          (householderBetaSpec ((m + 2) + 2)
            (householderTrailingActiveVector ((m + 2) + 2)
              (Fin.mk k (by omega))
              (fun a => (fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) k a
                (Fin.mk k hk)) (alpha (k + 2))))
          ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) k))
    (hvec0 :
      householderTrailingActiveVector ((m + 2) + 2)
          (Fin.mk 0 (by omega))
          (fun a =>
            trailingPanel (trailingPanel (A_hat 2)) a
              (Fin.mk 0 (by omega)))
          (alpha 2) =
        fl_householderNormalizedVector fp (Nat.succ_pos ((m + 2) + 1))
          (panelFirstColumn (Nat.succ_pos (2 + 1)) A_tail))
    (hself0 :
      (Finset.univ : Finset (Fin ((m + 2) + 2))).sum
        (fun i =>
          householderTrailingActiveVector ((m + 2) + 2)
              (Fin.mk 0 (by omega))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (by omega)))
              (alpha 2) i *
            householderTrailingActiveVector ((m + 2) + 2)
              (Fin.mk 0 (by omega))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (by omega)))
              (alpha 2) i) =
        2)
    (hdetFirst :
      Ne (Matrix.det
        (qrLeadingBlock A_tail
          (Nat.succ_le_succ (Nat.zero_le ((m + 2) + 1)))
          (Nat.succ_pos (2 + 1)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos ((m + 2) + 1))
              (panelFirstColumn (Nat.succ_pos (2 + 1)) A_tail)
           let S0 := fl_householderStoredPanelStep fp ((m + 2) + 2) (2 + 2) 0 v0 1
              A_tail
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le (m + 2)))
          (Nat.succ_pos 2) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTail :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos ((m + 2) + 1))
          (panelFirstColumn (Nat.succ_pos (2 + 1)) A_tail)
       let S0 := fl_householderStoredPanelStep fp ((m + 2) + 2) (2 + 2) 0 v0 1
          A_tail
       householderTrailingActiveVector ((m + 2) + 1) (0 : Fin ((m + 2) + 1))
            (panelFirstColumn (Nat.succ_pos 2) (trailingPanel S0)) (alpha 3) =
          fl_householderNormalizedVector fp (Nat.succ_pos (m + 2))
            (panelFirstColumn (Nat.succ_pos 2) (trailingPanel S0))))
    (hselfTail :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos ((m + 2) + 1))
          (panelFirstColumn (Nat.succ_pos (2 + 1)) A_tail)
       let S0 := fl_householderStoredPanelStep fp ((m + 2) + 2) (2 + 2) 0 v0 1
          A_tail
       (Finset.univ : Finset (Fin ((m + 2) + 1))).sum
          (fun i =>
            householderTrailingActiveVector ((m + 2) + 1) (0 : Fin ((m + 2) + 1))
                (panelFirstColumn (Nat.succ_pos 2) (trailingPanel S0))
                (alpha 3) i *
              householderTrailingActiveVector ((m + 2) + 1) (0 : Fin ((m + 2) + 1))
                (panelFirstColumn (Nat.succ_pos 2) (trailingPanel S0))
                (alpha 3) i) =
        2))
    (hvecTailTail0 :
      householderTrailingActiveVector (m + 2)
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
          (fun a =>
            trailingPanel
                (trailingPanel
                  ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2)) a
              (Fin.mk 0 (Nat.succ_pos 1)))
          (alpha 4) =
        fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1)
            (trailingPanel
              (trailingPanel
                ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2)))))
    (hselfTailTail0 :
      (Finset.univ : Finset (Fin (m + 2))).sum
        (fun i =>
          householderTrailingActiveVector (m + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
              (fun a =>
                trailingPanel
                    (trailingPanel
                      ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2)) a
                  (Fin.mk 0 (Nat.succ_pos 1)))
              (alpha 4) i *
            householderTrailingActiveVector (m + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
              (fun a =>
                trailingPanel
                    (trailingPanel
                      ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2)) a
                  (Fin.mk 0 (Nat.succ_pos 1)))
              (alpha 4) i) =
        2)
    (hdetTailTailFirst :
      Ne (Matrix.det
        (qrLeadingBlock
          (trailingPanel
            (trailingPanel
              ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2)))
          (Nat.succ_le_succ (Nat.zero_le (m + 1)))
          (Nat.succ_pos 1) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTailTailTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
              (panelFirstColumn (Nat.succ_pos 1)
                (trailingPanel
                  (trailingPanel
                    ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2))))
           let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1
              (trailingPanel
                (trailingPanel
                  ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2)))
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTailTail1 :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1)
            (trailingPanel
              (trailingPanel
                ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2))))
       let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1
          (trailingPanel
            (trailingPanel
              ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2)))
       householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
            (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0)) (alpha 5) =
          fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))))
    (hselfTailTail1 :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1)
            (trailingPanel
              (trailingPanel
                ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2))))
       let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1
          (trailingPanel
            (trailingPanel
              ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2)))
       (Finset.univ : Finset (Fin (m + 1))).sum
          (fun i =>
            householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))
                (alpha 5) i *
              householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))
                (alpha 5) i) =
        2))
    (hcopy : subtractZeroExact fp) :
    (fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) (2 + 2) =
      fl_householderQRPanel_R fp ((m + 2) + 2) (2 + 2) A_tail := by
  let TailSeq : Nat -> Fin ((m + 2) + 2) -> Fin (2 + 2) -> Real :=
    fun t => trailingPanel (trailingPanel (A_hat (t + 2)))
  let TailAlpha : Nat -> Real := fun t => alpha (t + 2)
  have hTailStep : forall k (hk : k < 2 + 2),
      TailSeq (k + 1) =
        fl_householderStoredPanelStep fp ((m + 2) + 2) (2 + 2) k
          (householderTrailingActiveVector ((m + 2) + 2)
            (Fin.mk k (lt_of_lt_of_le hk (by omega)))
            (fun a => TailSeq k a (Fin.mk k hk)) (TailAlpha k))
          (householderBetaSpec ((m + 2) + 2)
            (householderTrailingActiveVector ((m + 2) + 2)
              (Fin.mk k (lt_of_lt_of_le hk (by omega)))
              (fun a => TailSeq k a (Fin.mk k hk)) (TailAlpha k)))
          (TailSeq k) := by
    intro k hk
    simpa [TailSeq, TailAlpha] using hTailRec k hk
  have htail :=
    storedSignedSequence_four_col_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_subtractZeroExact
      fp (by omega) A_tail TailSeq TailAlpha (by omega) (by omega)
      (by
        simpa [TailSeq] using hinitTail)
      hTailStep
      (by
        simpa [TailSeq, TailAlpha] using hvec0)
      (by
        simpa [TailSeq, TailAlpha] using hself0)
      (by
        simpa using hdetFirst)
      (by
        simpa using hdetTail)
      (by
        simpa [TailAlpha] using hvecTail)
      (by
        simpa [TailAlpha] using hselfTail)
      (by
        simpa [TailSeq, TailAlpha] using hvecTailTail0)
      (by
        simpa [TailSeq, TailAlpha] using hselfTailTail0)
      (by
        simpa [TailSeq] using hdetTailTailFirst)
      (by
        simpa [TailSeq] using hdetTailTailTail)
      (by
        simpa [TailSeq, TailAlpha] using hvecTailTail1)
      (by
        simpa [TailSeq, TailAlpha] using hselfTailTail1)
      hcopy
  simpa [TailSeq] using htail

/-- Six-column final-panel bridge from the twice-trailing four-column tail
closure.

This is another dependency rung for the general final-panel induction.  It
does not close the arbitrary-width source theorem; it records that the new
four-column twice-trailing tail closure is sufficient to discharge the next
fixed endpoint through the same two-step recurrence bridge. -/
theorem
    storedSignedSequence_six_col_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_subtractZeroExact
    (fp : FPModel) {m : Nat}
    (hmn : (2 + 2) + 2 <= (((m + 2) + 2) + 2))
    (A : Fin (((m + 2) + 2) + 2) -> Fin ((2 + 2) + 2) -> Real)
    (A_hat : Nat -> Fin (((m + 2) + 2) + 2) -> Fin ((2 + 2) + 2) -> Real)
    (alpha : Nat -> Real)
    (hrows : 2 <= (((m + 2) + 2) + 2))
    (hcols : 2 <= (2 + 2) + 2)
    (hinit : A_hat 0 = A)
    (hStep : forall k (hk : k < (2 + 2) + 2),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (((m + 2) + 2) + 2) ((2 + 2) + 2) k
          (householderTrailingActiveVector (((m + 2) + 2) + 2)
            (Fin.mk k (lt_of_lt_of_le hk hmn))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (((m + 2) + 2) + 2)
            (householderTrailingActiveVector (((m + 2) + 2) + 2)
              (Fin.mk k (lt_of_lt_of_le hk hmn))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (hvec0 :
      householderTrailingActiveVector (((m + 2) + 2) + 2)
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
          (fun a =>
            A_hat 0 a
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
          (alpha 0) =
        fl_householderNormalizedVector fp (Nat.succ_pos (((m + 2) + 2) + 1))
          (panelFirstColumn (Nat.succ_pos ((2 + 2) + 1)) A))
    (hself0 :
      (Finset.univ : Finset (Fin (((m + 2) + 2) + 2))).sum
        (fun i =>
          householderTrailingActiveVector (((m + 2) + 2) + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
              (fun a =>
                A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
              (alpha 0) i *
            householderTrailingActiveVector (((m + 2) + 2) + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hrows))
              (fun a =>
                A_hat 0 a
                  (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) hcols)))
              (alpha 0) i) =
        2)
    (hdetFirst :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le (((m + 2) + 2) + 1)))
          (Nat.succ_pos ((2 + 2) + 1)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp
              (Nat.succ_pos (((m + 2) + 2) + 1))
              (panelFirstColumn (Nat.succ_pos ((2 + 2) + 1)) A)
           let S0 := fl_householderStoredPanelStep fp
              (((m + 2) + 2) + 2) ((2 + 2) + 2) 0 v0 1 A
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le ((m + 2) + 2)))
          (Nat.succ_pos (2 + 2)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTail :
      (let v0 := fl_householderNormalizedVector fp
          (Nat.succ_pos (((m + 2) + 2) + 1))
          (panelFirstColumn (Nat.succ_pos ((2 + 2) + 1)) A)
       let S0 := fl_householderStoredPanelStep fp
          (((m + 2) + 2) + 2) ((2 + 2) + 2) 0 v0 1 A
       householderTrailingActiveVector (((m + 2) + 2) + 1)
            (0 : Fin (((m + 2) + 2) + 1))
            (panelFirstColumn (Nat.succ_pos (2 + 2)) (trailingPanel S0))
            (alpha 1) =
          fl_householderNormalizedVector fp (Nat.succ_pos ((m + 2) + 2))
            (panelFirstColumn (Nat.succ_pos (2 + 2)) (trailingPanel S0))))
    (hselfTail :
      (let v0 := fl_householderNormalizedVector fp
          (Nat.succ_pos (((m + 2) + 2) + 1))
          (panelFirstColumn (Nat.succ_pos ((2 + 2) + 1)) A)
       let S0 := fl_householderStoredPanelStep fp
          (((m + 2) + 2) + 2) ((2 + 2) + 2) 0 v0 1 A
       (Finset.univ : Finset (Fin (((m + 2) + 2) + 1))).sum
          (fun i =>
            householderTrailingActiveVector (((m + 2) + 2) + 1)
                (0 : Fin (((m + 2) + 2) + 1))
                (panelFirstColumn (Nat.succ_pos (2 + 2)) (trailingPanel S0))
                (alpha 1) i *
              householderTrailingActiveVector (((m + 2) + 2) + 1)
                (0 : Fin (((m + 2) + 2) + 1))
                (panelFirstColumn (Nat.succ_pos (2 + 2)) (trailingPanel S0))
                (alpha 1) i) =
        2))
    (A_tail : Fin ((m + 2) + 2) -> Fin (2 + 2) -> Real)
    (hinitTail : trailingPanel (trailingPanel (A_hat 2)) = A_tail)
    (hvecTailTail0 :
      householderTrailingActiveVector ((m + 2) + 2)
          (Fin.mk 0 (by omega))
          (fun a =>
            trailingPanel (trailingPanel (A_hat 2)) a
              (Fin.mk 0 (by omega)))
          (alpha 2) =
        fl_householderNormalizedVector fp (Nat.succ_pos ((m + 2) + 1))
          (panelFirstColumn (Nat.succ_pos (2 + 1)) A_tail))
    (hselfTailTail0 :
      (Finset.univ : Finset (Fin ((m + 2) + 2))).sum
        (fun i =>
          householderTrailingActiveVector ((m + 2) + 2)
              (Fin.mk 0 (by omega))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (by omega)))
              (alpha 2) i *
            householderTrailingActiveVector ((m + 2) + 2)
              (Fin.mk 0 (by omega))
              (fun a =>
                trailingPanel (trailingPanel (A_hat 2)) a
                  (Fin.mk 0 (by omega)))
              (alpha 2) i) =
        2)
    (hdetTailTailFirst :
      Ne (Matrix.det
        (qrLeadingBlock A_tail
          (Nat.succ_le_succ (Nat.zero_le ((m + 2) + 1)))
          (Nat.succ_pos (2 + 1)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTailTailTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos ((m + 2) + 1))
              (panelFirstColumn (Nat.succ_pos (2 + 1)) A_tail)
           let S0 := fl_householderStoredPanelStep fp ((m + 2) + 2) (2 + 2) 0 v0 1
              A_tail
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le (m + 2)))
          (Nat.succ_pos 2) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTailTail1 :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos ((m + 2) + 1))
          (panelFirstColumn (Nat.succ_pos (2 + 1)) A_tail)
       let S0 := fl_householderStoredPanelStep fp ((m + 2) + 2) (2 + 2) 0 v0 1
          A_tail
       householderTrailingActiveVector ((m + 2) + 1) (0 : Fin ((m + 2) + 1))
            (panelFirstColumn (Nat.succ_pos 2) (trailingPanel S0)) (alpha 3) =
          fl_householderNormalizedVector fp (Nat.succ_pos (m + 2))
            (panelFirstColumn (Nat.succ_pos 2) (trailingPanel S0))))
    (hselfTailTail1 :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos ((m + 2) + 1))
          (panelFirstColumn (Nat.succ_pos (2 + 1)) A_tail)
       let S0 := fl_householderStoredPanelStep fp ((m + 2) + 2) (2 + 2) 0 v0 1
          A_tail
       (Finset.univ : Finset (Fin ((m + 2) + 1))).sum
          (fun i =>
            householderTrailingActiveVector ((m + 2) + 1) (0 : Fin ((m + 2) + 1))
                (panelFirstColumn (Nat.succ_pos 2) (trailingPanel S0))
                (alpha 3) i *
              householderTrailingActiveVector ((m + 2) + 1) (0 : Fin ((m + 2) + 1))
                (panelFirstColumn (Nat.succ_pos 2) (trailingPanel S0))
                (alpha 3) i) =
        2))
    (hvecTailTail2 :
      householderTrailingActiveVector (m + 2)
          (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
          (fun a =>
            trailingPanel
                (trailingPanel
                  ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2)) a
              (Fin.mk 0 (Nat.succ_pos 1)))
          (alpha 4) =
        fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1)
            (trailingPanel
              (trailingPanel
                ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2)))))
    (hselfTailTail2 :
      (Finset.univ : Finset (Fin (m + 2))).sum
        (fun i =>
          householderTrailingActiveVector (m + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
              (fun a =>
                trailingPanel
                    (trailingPanel
                      ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2)) a
                  (Fin.mk 0 (Nat.succ_pos 1)))
              (alpha 4) i *
            householderTrailingActiveVector (m + 2)
              (Fin.mk 0 (lt_of_lt_of_le (Nat.succ_pos 1) (by omega)))
              (fun a =>
                trailingPanel
                    (trailingPanel
                      ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2)) a
                  (Fin.mk 0 (Nat.succ_pos 1)))
              (alpha 4) i) =
        2)
    (hdetTailTailTailFirst :
      Ne (Matrix.det
        (qrLeadingBlock
          (trailingPanel
            (trailingPanel
              ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2)))
          (Nat.succ_le_succ (Nat.zero_le (m + 1)))
          (Nat.succ_pos 1) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTailTailTailTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
              (panelFirstColumn (Nat.succ_pos 1)
                (trailingPanel
                  (trailingPanel
                    ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2))))
           let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1
              (trailingPanel
                (trailingPanel
                  ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2)))
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos 0) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hvecTailTail3 :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1)
            (trailingPanel
              (trailingPanel
                ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2))))
       let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1
          (trailingPanel
            (trailingPanel
              ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2)))
       householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
            (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0)) (alpha 5) =
          fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))))
    (hselfTailTail3 :
      (let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos 1)
            (trailingPanel
              (trailingPanel
                ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2))))
       let S0 := fl_householderStoredPanelStep fp (m + 2) 2 0 v0 1
          (trailingPanel
            (trailingPanel
              ((fun t => trailingPanel (trailingPanel (A_hat (t + 2)))) 2)))
       (Finset.univ : Finset (Fin (m + 1))).sum
          (fun i =>
            householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))
                (alpha 5) i *
              householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
                (panelFirstColumn (Nat.succ_pos 0) (trailingPanel S0))
                (alpha 5) i) =
        2))
    (hcopy : subtractZeroExact fp) :
    A_hat ((2 + 2) + 2) =
      fl_householderQRPanel_R fp (((m + 2) + 2) + 2) ((2 + 2) + 2) A := by
  have hTailData :
      storedSignedSequenceFirstTwoReflectorData fp
        (storedSignedSequenceTwiceTrailingSeq A_hat)
        (storedSignedSequenceTailAlpha2 alpha) :=
    storedSignedSequenceFirstTwoReflectorData_of_tail_reflector_self_dot
      fp A_hat alpha
      (by simpa [hinitTail] using hvecTailTail0)
      (by simpa [hinitTail] using hselfTailTail0)
      (by simpa [hinitTail] using hdetTailTailFirst)
      (by simpa [hinitTail] using hdetTailTailTail)
      (by simpa [hinitTail] using hvecTailTail1)
      (by simpa [hinitTail] using hselfTailTail1)
  have hTailClosed :
      storedSignedSequenceTwiceTrailingFinalClosed fp hmn A_hat alpha := by
    exact
      storedSignedSequenceTwiceTrailingFinalClosed_four_col_of_firstTwoReflectorData
        fp A_hat alpha hTailData
        (by
          simpa [storedSignedSequenceTwiceTrailingSeq,
            storedSignedSequenceTailAlpha2] using hvecTailTail2)
        (by
          simpa [storedSignedSequenceTwiceTrailingSeq,
            storedSignedSequenceTailAlpha2] using hselfTailTail2)
        (by
          simpa [storedSignedSequenceTwiceTrailingSeq] using hdetTailTailTailFirst)
        (by
          simpa [storedSignedSequenceTwiceTrailingSeq] using hdetTailTailTailTail)
        (by
          simpa [storedSignedSequenceTwiceTrailingSeq,
            storedSignedSequenceTailAlpha2] using hvecTailTail3)
        (by
          simpa [storedSignedSequenceTwiceTrailingSeq,
            storedSignedSequenceTailAlpha2] using hselfTailTail3)
        hcopy
  exact
    storedSignedSequence_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_twice_trailing_closed
      fp hmn A A_hat alpha hrows hcols hinit hStep hvec0 hself0
      hdetFirst hdetTail hvecTail hselfTail hcopy hTailClosed

/-- Exact-arithmetic instance of the arbitrary-width two-step
recursive/stored bridge. -/
theorem
    qrPanel_R_succ_succ_eq_secondStoredStep_trailingQR_of_leadingBlock_det_ne_zero_exactWithUnitRoundoff
    (u0 : Real) (hu0 : 0 <= u0) {m p : Nat}
    (A : Fin (m + 2) -> Fin (p + 2) -> Real)
    (hdetFirst :
      Ne (Matrix.det
        (qrLeadingBlock A
          (Nat.succ_le_succ (Nat.zero_le (m + 1)))
          (Nat.succ_pos (p + 1)) :
          Matrix (Fin 1) (Fin 1) Real))
        0)
    (hdetTail :
      Ne (Matrix.det
        (qrLeadingBlock
          (let fp := FPModel.exactWithUnitRoundoff u0 hu0
           let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
              (panelFirstColumn (Nat.succ_pos (p + 1)) A)
           let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1 A
           trailingPanel S0)
          (Nat.succ_le_succ (Nat.zero_le m))
          (Nat.succ_pos p) :
          Matrix (Fin 1) (Fin 1) Real))
        0) :
    fl_householderQRPanel_R (FPModel.exactWithUnitRoundoff u0 hu0)
        (m + 2) (p + 2) A =
      (let fp := FPModel.exactWithUnitRoundoff u0 hu0
       let v0 := fl_householderNormalizedVector fp (Nat.succ_pos (m + 1))
          (panelFirstColumn (Nat.succ_pos (p + 1)) A)
       let S0 := fl_householderStoredPanelStep fp (m + 2) (p + 2) 0 v0 1 A
       let v1 := fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) (trailingPanel S0))
       let Sfull :=
          fl_householderStoredPanelStep fp (m + 2) (p + 2) 1
            (Fin.cases 0 v1) 1 S0
       panelFromTopAndTrailing (panelTopLeft Sfull) (panelTopRowTail Sfull)
        (panelFromTopAndTrailing
          (panelTopLeft (trailingPanel Sfull))
          (panelTopRowTail (trailingPanel Sfull))
          (fl_householderQRPanel_R fp m p
            (trailingPanel (trailingPanel Sfull))))) := by
  let fp : FPModel := FPModel.exactWithUnitRoundoff u0 hu0
  exact
    qrPanel_R_succ_succ_eq_secondStoredStep_trailingQR_of_leadingBlock_det_ne_zero_of_subtractZeroExact
      fp A hdetFirst hdetTail
      (subtractZeroExact_exactWithUnitRoundoff u0 hu0)

/-- Source-facing nonbreakdown route for the stored Householder QR loop.
Nonsingular local leading blocks, the stored lower-zero invariant, the source
sign convention, and a per-pivot square-root component budget imply that the
final top-block diagonal is nonzero.  This is the leading-minor route that the
concrete `R11` handoff can later instantiate. -/
theorem storedTrailingPanel_R_diag_ne_zero_of_leading_block_det_ne_zero_sqrt_budget
    {m n : Nat}
    (fp : FPModel) (hmn : n ≤ m)
    (A_hat : Nat → Fin m → Fin n → Real)
    (alpha : Nat → Real)
    (hm : gammaValid fp m)
    (hStep : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun i => A_hat k i ⟨k, hk⟩))
    (hdetPrev : ∀ k (hk : k < n),
      Matrix.det
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_trans (Nat.le_of_lt hk) hmn) hk :
          Matrix (Fin k) (Fin k) Real) ≠ 0)
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (le_trans (Nat.succ_le_of_lt hk) hmn) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) Real) ≠ 0)
    (hlowerPrev : ∀ k (hk : k < n) (i : Fin m) (j : Fin k),
      k ≤ i.val → A_hat k i (qrPreviousColumn n k hk j) = 0)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hbudgetSqrt : ∀ k (hk : k < n),
      householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩ <
        Real.sqrt
          (householderTrailingNorm2Sq m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun i => A_hat k i ⟨k, hk⟩))) :
    ∀ i : Fin n, A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ i ≠ 0 := by
  exact
    fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_leading_block_det_ne_zero_sqrt_budget
      fp hmn A_hat alpha hm hStep halpha hdetPrev hdetLead hlowerPrev
      hsign hbudgetSqrt

/-- Sequence-budget form of the stored Householder nonbreakdown route.
The deterministic summed compact-update budget controls each active pivot
component budget, so a per-pivot sequence-budget margin is enough to feed the
leading-minor square-root nonbreakdown theorem. -/
theorem storedTrailingPanel_R_diag_ne_zero_of_leading_block_det_ne_zero_sequence_budget
    {m n : Nat}
    (fp : FPModel) (hmn : n ≤ m)
    (A_hat : Nat → Fin m → Fin n → Real)
    (b_hat : Nat → Fin m → Real)
    (alpha : Nat → Real)
    (hm : gammaValid fp m)
    (hStep : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun i => A_hat k i ⟨k, hk⟩))
    (hdetPrev : ∀ k (hk : k < n),
      Matrix.det
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_trans (Nat.le_of_lt hk) hmn) hk :
          Matrix (Fin k) (Fin k) Real) ≠ 0)
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (le_trans (Nat.succ_le_of_lt hk) hmn) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) Real) ≠ 0)
    (hlowerPrev : ∀ k (hk : k < n) (i : Fin m) (j : Fin k),
      k ≤ i.val → A_hat k i (qrPreviousColumn n k hk j) = 0)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hsequenceBudget : ∀ k (hk : k < n),
      storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
          vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩) <
        Real.sqrt
          (householderTrailingNorm2Sq m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun i => A_hat k i ⟨k, hk⟩))) :
    ∀ i : Fin n, A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ i ≠ 0 := by
  refine
    storedTrailingPanel_R_diag_ne_zero_of_leading_block_det_ne_zero_sqrt_budget
      fp hmn A_hat alpha hm hStep halpha hdetPrev hdetLead hlowerPrev
      hsign ?_
  intro k hk
  exact
    lt_of_le_of_lt
      (storedQRCompactPivotBudget_le_sequence_column_norm
        hmn fp A_hat b_hat alpha hm k hk)
      (hsequenceBudget k hk)

/-- Uniform-step-budget form of the stored Householder nonbreakdown route.
If each compact stored-QR update has relative budget at most `cStep`, then the
sequence budget is at most `n * cStep`; a per-pivot margin for that uniform cap
therefore feeds the leading-minor nonbreakdown theorem. -/
theorem storedTrailingPanel_R_diag_ne_zero_of_leading_block_det_ne_zero_uniform_step_budget
    {m n : Nat}
    (fp : FPModel) (hmn : n ≤ m)
    (A_hat : Nat → Fin m → Fin n → Real)
    (b_hat : Nat → Fin m → Real)
    (alpha : Nat → Real)
    (cStep : Real)
    (hm : gammaValid fp m)
    (hStep : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun i => A_hat k i ⟨k, hk⟩))
    (hdetPrev : ∀ k (hk : k < n),
      Matrix.det
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_trans (Nat.le_of_lt hk) hmn) hk :
          Matrix (Fin k) (Fin k) Real) ≠ 0)
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (le_trans (Nat.succ_le_of_lt hk) hmn) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) Real) ≠ 0)
    (hlowerPrev : ∀ k (hk : k < n) (i : Fin m) (j : Fin k),
      k ≤ i.val → A_hat k i (qrPreviousColumn n k hk j) = 0)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hStepBudget : ∀ k : Fin n,
      storedQRCompactStepRelativeBudget hmn fp A_hat b_hat alpha k ≤ cStep)
    (huniformBudget : ∀ k (hk : k < n),
      ((n : Real) * cStep) *
          vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩) <
        Real.sqrt
          (householderTrailingNorm2Sq m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun i => A_hat k i ⟨k, hk⟩))) :
    ∀ i : Fin n, A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ i ≠ 0 := by
  refine
    storedTrailingPanel_R_diag_ne_zero_of_leading_block_det_ne_zero_sequence_budget
      fp hmn A_hat b_hat alpha hm hStep halpha hdetPrev hdetLead
      hlowerPrev hsign ?_
  intro k hk
  have hseq :
      storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha ≤
        (n : Real) * cStep :=
    storedQRCompactSequenceRelativeBudget_le_mul_of_step_le
      hmn fp A_hat b_hat alpha cStep hStepBudget
  have hseqMul :
      storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
          vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩) ≤
        ((n : Real) * cStep) *
          vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩) :=
    mul_le_mul_of_nonneg_right hseq
      (vecNorm2_nonneg (fun i : Fin m => A_hat k i ⟨k, hk⟩))
  exact lt_of_le_of_lt hseqMul (huniformBudget k hk)

/-- Transport the stored-loop uniform-budget nonbreakdown theorem across an
explicit top-block identification.

This is a bridge theorem: it does not prove that a concrete QR implementation
has the stored-loop top block.  Instead it records the exact equality that must
be supplied to reuse the stored leading-minor nonbreakdown route for another
named `R` block. -/
theorem storedTrailingPanel_R_diag_ne_zero_of_uniform_step_budget_of_top_block_eq
    {m n : Nat}
    (fp : FPModel) (hmn : n <= m)
    (A_hat : Nat -> Fin m -> Fin n -> Real)
    (b_hat : Nat -> Fin m -> Real)
    (alpha : Nat -> Real)
    (cStep : Real)
    (hm : gammaValid fp m)
    (hStep : forall k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            (Fin.mk k (lt_of_lt_of_le hk hmn))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              (Fin.mk k (lt_of_lt_of_le hk hmn))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (halpha : forall k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          (Fin.mk k (lt_of_lt_of_le hk hmn))
          (fun i => A_hat k i (Fin.mk k hk)))
    (hdetPrev : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat k)
            (le_trans (Nat.le_of_lt hk) hmn) hk :
            Matrix (Fin k) (Fin k) Real))
        0)
    (hdetLead : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrLeadingBlock (A_hat k)
            (le_trans (Nat.succ_le_of_lt hk) hmn) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) Real))
        0)
    (hlowerPrev : forall k (hk : k < n) (i : Fin m) (j : Fin k),
      k <= i.val -> A_hat k i (qrPreviousColumn n k hk j) = 0)
    (hsign : forall k (hk : k < n),
      alpha k *
          A_hat k (Fin.mk k (lt_of_lt_of_le hk hmn)) (Fin.mk k hk) <= 0)
    (hStepBudget : forall k : Fin n,
      storedQRCompactStepRelativeBudget hmn fp A_hat b_hat alpha k <= cStep)
    (huniformBudget : forall k (hk : k < n),
      ((n : Real) * cStep) *
          vecNorm2 (fun i : Fin m => A_hat k i (Fin.mk k hk)) <
        Real.sqrt
          (householderTrailingNorm2Sq m
            (Fin.mk k (lt_of_lt_of_le hk hmn))
            (fun i => A_hat k i (Fin.mk k hk))))
    (R : Fin n -> Fin n -> Real)
    (hR : forall i j,
      R i j = A_hat n (Fin.mk i.val (lt_of_lt_of_le i.isLt hmn)) j) :
    forall i : Fin n, Ne (R i i) 0 := by
  have hdiag :
      forall i : Fin n,
        Ne (A_hat n (Fin.mk i.val (lt_of_lt_of_le i.isLt hmn)) i) 0 :=
    storedTrailingPanel_R_diag_ne_zero_of_leading_block_det_ne_zero_uniform_step_budget
      fp hmn A_hat b_hat alpha cStep hm hStep halpha hdetPrev hdetLead
      hlowerPrev hsign hStepBudget huniformBudget
  intro i
  rw [hR i i]
  exact hdiag i

/-- Concrete `R11` transport form of the stored-loop uniform-budget
nonbreakdown route.

The only extra hypothesis is the algorithm-identification equality between the
named padded Householder `R11` block and the top block of the stored-loop final
panel.  This keeps the remaining recursive/stored-QR bridge explicit for the
final Theorem 19.13 route. -/
theorem householder_paddedFinInput_R11_diag_ne_zero_of_storedTrailingPanel_uniform_step_budget
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hrows : n <= n + m)
    (A_hat : Nat -> Fin (n + m) -> Fin n -> Real)
    (b_hat : Nat -> Fin (n + m) -> Real)
    (alpha : Nat -> Real)
    (cStep : Real)
    (hm : gammaValid fp (n + m))
    (hStep : forall k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (n + m) n k
          (householderTrailingActiveVector (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (n + m)
            (householderTrailingActiveVector (n + m)
              (Fin.mk k (lt_of_lt_of_le hk hrows))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (halpha : forall k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq (n + m)
          (Fin.mk k (lt_of_lt_of_le hk hrows))
          (fun i => A_hat k i (Fin.mk k hk)))
    (hdetPrev : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat k)
            (le_trans (Nat.le_of_lt hk) hrows) hk :
            Matrix (Fin k) (Fin k) Real))
        0)
    (hdetLead : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrLeadingBlock (A_hat k)
            (le_trans (Nat.succ_le_of_lt hk) hrows) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) Real))
        0)
    (hlowerPrev :
      forall k (hk : k < n) (i : Fin (n + m)) (j : Fin k),
        k <= i.val -> A_hat k i (qrPreviousColumn n k hk j) = 0)
    (hsign : forall k (hk : k < n),
      alpha k *
          A_hat k (Fin.mk k (lt_of_lt_of_le hk hrows)) (Fin.mk k hk) <= 0)
    (hStepBudget : forall k : Fin n,
      storedQRCompactStepRelativeBudget hrows fp A_hat b_hat alpha k <= cStep)
    (huniformBudget : forall k (hk : k < n),
      ((n : Real) * cStep) *
          vecNorm2 (fun i : Fin (n + m) => A_hat k i (Fin.mk k hk)) <
        Real.sqrt
          (householderTrailingNorm2Sq (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun i => A_hat k i (Fin.mk k hk))))
    (hR11 : forall i j,
      householder_paddedFinInput_R11 fp A i j =
        A_hat n (Fin.mk i.val (lt_of_lt_of_le i.isLt hrows)) j) :
    forall i : Fin n, Ne (householder_paddedFinInput_R11 fp A i i) 0 :=
  storedTrailingPanel_R_diag_ne_zero_of_uniform_step_budget_of_top_block_eq
    fp hrows A_hat b_hat alpha cStep hm hStep halpha hdetPrev hdetLead
    hlowerPrev hsign hStepBudget huniformBudget
    (householder_paddedFinInput_R11 fp A) hR11

/-- Turn a full final-panel identification into the exact top-block equality
needed by the concrete padded Householder `R11` handoff.

This is the row-indexing layer of the remaining recursive/stored bridge: once
the stored loop's final panel is known to be the recursive QR panel on the
padded input, the extracted `R11` block is definitionally the stored final top
block. -/
theorem householder_paddedFinInput_R11_eq_top_block_of_final_panel_eq
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hrows : n <= n + m)
    (A_hat : Nat -> Fin (n + m) -> Fin n -> Real)
    (hFinal :
      A_hat n = fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
    forall i j,
      householder_paddedFinInput_R11 fp A i j =
        A_hat n (Fin.mk i.val (lt_of_lt_of_le i.isLt hrows)) j := by
  intro i j
  rw [hFinal]
  have hidx :
      (Fin.castAdd m i : Fin (n + m)) =
        Fin.mk i.val (lt_of_lt_of_le i.isLt hrows) := by
    ext
    rfl
  rw [<- hidx]
  simp [householder_paddedFinInput_R11, paddedEconomyR, mgsPaddedEconomyR,
    mgsPaddedTopBlock, mgsPaddedRowsFromFin, mgsPaddedRowToFin]

/-- Concrete `R11` nonbreakdown from the stored-loop uniform-step route, with
the remaining algorithm bridge stated as a full final-panel equality.

Compared with
`householder_paddedFinInput_R11_diag_ne_zero_of_storedTrailingPanel_uniform_step_budget`,
this removes the ad hoc pointwise `hR11` premise.  The open bridge is now the
more natural statement that the stored loop's final panel is the recursive
Householder QR panel on the padded input. -/
theorem
    householder_paddedFinInput_R11_diag_ne_zero_of_storedTrailingPanel_final_panel_eq_uniform_step_budget
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hrows : n <= n + m)
    (A_hat : Nat -> Fin (n + m) -> Fin n -> Real)
    (b_hat : Nat -> Fin (n + m) -> Real)
    (alpha : Nat -> Real)
    (cStep : Real)
    (hm : gammaValid fp (n + m))
    (hStep : forall k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (n + m) n k
          (householderTrailingActiveVector (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (n + m)
            (householderTrailingActiveVector (n + m)
              (Fin.mk k (lt_of_lt_of_le hk hrows))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (halpha : forall k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq (n + m)
          (Fin.mk k (lt_of_lt_of_le hk hrows))
          (fun i => A_hat k i (Fin.mk k hk)))
    (hdetPrev : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat k)
            (le_trans (Nat.le_of_lt hk) hrows) hk :
            Matrix (Fin k) (Fin k) Real))
        0)
    (hdetLead : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrLeadingBlock (A_hat k)
            (le_trans (Nat.succ_le_of_lt hk) hrows) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) Real))
        0)
    (hlowerPrev :
      forall k (hk : k < n) (i : Fin (n + m)) (j : Fin k),
        k <= i.val -> A_hat k i (qrPreviousColumn n k hk j) = 0)
    (hsign : forall k (hk : k < n),
      alpha k *
          A_hat k (Fin.mk k (lt_of_lt_of_le hk hrows)) (Fin.mk k hk) <= 0)
    (hStepBudget : forall k : Fin n,
      storedQRCompactStepRelativeBudget hrows fp A_hat b_hat alpha k <= cStep)
    (huniformBudget : forall k (hk : k < n),
      ((n : Real) * cStep) *
          vecNorm2 (fun i : Fin (n + m) => A_hat k i (Fin.mk k hk)) <
        Real.sqrt
          (householderTrailingNorm2Sq (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun i => A_hat k i (Fin.mk k hk))))
    (hFinal :
      A_hat n = fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
    forall i : Fin n, Ne (householder_paddedFinInput_R11 fp A i i) 0 :=
  householder_paddedFinInput_R11_diag_ne_zero_of_storedTrailingPanel_uniform_step_budget
    (fp := fp) (m := m) (n := n) A hrows A_hat b_hat alpha cStep
    hm hStep halpha hdetPrev hdetLead hlowerPrev hsign hStepBudget
    huniformBudget
    (householder_paddedFinInput_R11_eq_top_block_of_final_panel_eq
      fp A hrows A_hat hFinal)

/-- Concrete `R11` nonbreakdown from the stored-loop uniform-step route, with
the previous-leading-block and lower-zero stage premises supplied by the signed
stored sequence itself.

This moves the remaining nonbreakdown surface closer to the source algorithm:
callers may give previous-leading-block determinant hypotheses at the final
stored panel, while the stage-local previous-block hypotheses and completed
column lower-zero shape are transported internally.  The current-leading-block
nonbreakdown hypotheses remain stage-local, because column `k` is not completed
until after pivot `k`. -/
theorem
    householder_paddedFinInput_R11_diag_ne_zero_of_storedTrailingPanel_final_prevBlocks_uniform_step_budget
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hrows : n <= n + m)
    (A_hat : Nat -> Fin (n + m) -> Fin n -> Real)
    (b_hat : Nat -> Fin (n + m) -> Real)
    (alpha : Nat -> Real)
    (cStep : Real)
    (hm : gammaValid fp (n + m))
    (hStep : forall k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (n + m) n k
          (householderTrailingActiveVector (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (n + m)
            (householderTrailingActiveVector (n + m)
              (Fin.mk k (lt_of_lt_of_le hk hrows))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (halpha : forall k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq (n + m)
          (Fin.mk k (lt_of_lt_of_le hk hrows))
          (fun i => A_hat k i (Fin.mk k hk)))
    (hdetPrevFinal : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat n)
            (le_trans (Nat.le_of_lt hk) hrows) hk :
            Matrix (Fin k) (Fin k) Real))
        0)
    (hdetLead : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrLeadingBlock (A_hat k)
            (le_trans (Nat.succ_le_of_lt hk) hrows) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) Real))
        0)
    (hsign : forall k (hk : k < n),
      alpha k *
          A_hat k (Fin.mk k (lt_of_lt_of_le hk hrows)) (Fin.mk k hk) <= 0)
    (hStepBudget : forall k : Fin n,
      storedQRCompactStepRelativeBudget hrows fp A_hat b_hat alpha k <= cStep)
    (huniformBudget : forall k (hk : k < n),
      ((n : Real) * cStep) *
          vecNorm2 (fun i : Fin (n + m) => A_hat k i (Fin.mk k hk)) <
        Real.sqrt
          (householderTrailingNorm2Sq (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun i => A_hat k i (Fin.mk k hk))))
    (hR11 : forall i j,
      householder_paddedFinInput_R11 fp A i j =
        A_hat n (Fin.mk i.val (lt_of_lt_of_le i.isLt hrows)) j) :
    forall i : Fin n, Ne (householder_paddedFinInput_R11 fp A i i) 0 := by
  have hdetPrev :
      forall k (hk : k < n),
        Ne
          (Matrix.det
            (qrPreviousLeadingBlockTranspose (A_hat k)
              (le_trans (Nat.le_of_lt hk) hrows) hk :
              Matrix (Fin k) (Fin k) Real))
          0 :=
    storedSignedSequence_qrPreviousLeadingBlockTranspose_det_ne_zero_stages_of_final
      fp hrows A_hat alpha hStep hdetPrevFinal
  have hlowerPrev :
      forall k (hk : k < n) (i : Fin (n + m)) (j : Fin k),
        k <= i.val -> A_hat k i (qrPreviousColumn n k hk j) = 0 :=
    storedSignedSequence_lower_previous_columns fp hrows A_hat alpha hStep
  exact
    householder_paddedFinInput_R11_diag_ne_zero_of_storedTrailingPanel_uniform_step_budget
      (fp := fp) (m := m) (n := n) A hrows A_hat b_hat alpha cStep
      hm hStep halpha hdetPrev hdetLead hlowerPrev hsign hStepBudget
      huniformBudget hR11

/-- Final-panel equality version of
`householder_paddedFinInput_R11_diag_ne_zero_of_storedTrailingPanel_final_prevBlocks_uniform_step_budget`.

The pointwise `R11`/stored-final-top-block equality is supplied internally from
the full recursive/stored final-panel identification. -/
theorem
    householder_paddedFinInput_R11_diag_ne_zero_of_storedTrailingPanel_final_panel_eq_final_prevBlocks_uniform_step_budget
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hrows : n <= n + m)
    (A_hat : Nat -> Fin (n + m) -> Fin n -> Real)
    (b_hat : Nat -> Fin (n + m) -> Real)
    (alpha : Nat -> Real)
    (cStep : Real)
    (hm : gammaValid fp (n + m))
    (hStep : forall k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (n + m) n k
          (householderTrailingActiveVector (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (n + m)
            (householderTrailingActiveVector (n + m)
              (Fin.mk k (lt_of_lt_of_le hk hrows))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (halpha : forall k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq (n + m)
          (Fin.mk k (lt_of_lt_of_le hk hrows))
          (fun i => A_hat k i (Fin.mk k hk)))
    (hdetPrevFinal : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat n)
            (le_trans (Nat.le_of_lt hk) hrows) hk :
            Matrix (Fin k) (Fin k) Real))
        0)
    (hdetLead : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrLeadingBlock (A_hat k)
            (le_trans (Nat.succ_le_of_lt hk) hrows) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) Real))
        0)
    (hsign : forall k (hk : k < n),
      alpha k *
          A_hat k (Fin.mk k (lt_of_lt_of_le hk hrows)) (Fin.mk k hk) <= 0)
    (hStepBudget : forall k : Fin n,
      storedQRCompactStepRelativeBudget hrows fp A_hat b_hat alpha k <= cStep)
    (huniformBudget : forall k (hk : k < n),
      ((n : Real) * cStep) *
          vecNorm2 (fun i : Fin (n + m) => A_hat k i (Fin.mk k hk)) <
        Real.sqrt
          (householderTrailingNorm2Sq (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun i => A_hat k i (Fin.mk k hk))))
    (hFinal :
      A_hat n = fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
    forall i : Fin n, Ne (householder_paddedFinInput_R11 fp A i i) 0 :=
  householder_paddedFinInput_R11_diag_ne_zero_of_storedTrailingPanel_final_prevBlocks_uniform_step_budget
    (fp := fp) (m := m) (n := n) A hrows A_hat b_hat alpha cStep
    hm hStep halpha hdetPrevFinal hdetLead hsign hStepBudget
    huniformBudget
    (householder_paddedFinInput_R11_eq_top_block_of_final_panel_eq
      fp A hrows A_hat hFinal)

/-- Stored-loop Higham handoff with uniform-step nonbreakdown.

This packages the checked stored Householder factorization/top-block shape with
the uniform step-budget leading-minor nonbreakdown route.  It is still a stored
loop handoff, not the final concrete padded `R11` instantiation. -/
theorem storedTrailingPanel_higham_columnwise_factorization_and_R_diag_ne_zero_of_uniform_step_budget
    {m n : Nat}
    (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → Real) (b : Fin m → Real)
    (A_hat : Nat → Fin m → Fin n → Real)
    (b_hat : Nat → Fin m → Real)
    (alpha : Nat → Real)
    (c cStep : Real)
    (hc : 0 ≤ c) (hm : gammaValid fp m)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hden : ∀ k (hk : k < n),
      (∑ i : Fin m,
        householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i *
          householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i) ≠ 0)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        c * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        c * vecNorm2 (b_hat k))
    (hdetPrev : ∀ k (hk : k < n),
      Matrix.det
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_trans (Nat.le_of_lt hk) hmn) hk :
          Matrix (Fin k) (Fin k) Real) ≠ 0)
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (le_trans (Nat.succ_le_of_lt hk) hmn) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) Real) ≠ 0)
    (hlowerPrev : ∀ k (hk : k < n) (i : Fin m) (j : Fin k),
      k ≤ i.val → A_hat k i (qrPreviousColumn n k hk j) = 0)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hStepBudget : ∀ k : Fin n,
      storedQRCompactStepRelativeBudget hmn fp A_hat b_hat alpha k ≤ cStep)
    (huniformBudget : ∀ k (hk : k < n),
      ((n : Real) * cStep) *
          vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩) <
        Real.sqrt
          (householderTrailingNorm2Sq m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun i => A_hat k i ⟨k, hk⟩))) :
    let R : Fin n → Fin n → Real :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    let cTop : Fin n → Real :=
      fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩
    ∃ (Q : Fin m → Fin m → Real)
        (ΔA : Fin m → Fin n → Real) (Δb : Fin m → Real),
      IsOrthogonal m Q ∧
      (∀ i j, A_hat n i j =
        matMulRectLeft (matTranspose Q) (fun a b => A a b + ΔA a b) i j) ∧
      (∀ i, b_hat n i =
        matMulVec m (matTranspose Q) (fun a => b a + Δb a) i) ∧
      (∀ j : Fin n,
        vecNorm2 (fun i => ΔA i j) ≤
          ((1 + c) ^ n - 1) * vecNorm2 (fun i => A i j)) ∧
      vecNorm2 Δb ≤ ((1 + c) ^ n - 1) * vecNorm2 b ∧
      (∀ (i : Fin m) (j : Fin n) (hi : i.val < n),
        A_hat n i j = R ⟨i.val, hi⟩ j) ∧
      (∀ (i : Fin m) (j : Fin n), n ≤ i.val → A_hat n i j = 0) ∧
      (∀ (i : Fin m) (hi : i.val < n),
        b_hat n i = cTop ⟨i.val, hi⟩) ∧
      (∀ i j : Fin n, j.val < i.val → R i j = 0) ∧
      (∀ i : Fin n, R i i ≠ 0) := by
  classical
  intro R cTop
  rcases
    fl_householderStoredTrailingPanel_higham_columnwise_factorization
      fp hmn A b A_hat b_hat alpha c hc hm
      hInitA hInitb hStepA hStepb halpha hden hA_budget hb_budget with
    ⟨Q, ΔA, Δb, hQ, hArep, hbrep, hΔA_cols, hΔb,
      hA_top, hA_bottom, hb_top, hupper⟩
  have hdiag :
      ∀ i : Fin n,
        A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ i ≠ 0 :=
    storedTrailingPanel_R_diag_ne_zero_of_leading_block_det_ne_zero_uniform_step_budget
      fp hmn A_hat b_hat alpha cStep hm hStepA halpha hdetPrev hdetLead
      hlowerPrev hsign hStepBudget huniformBudget
  have hdiagR : ∀ i : Fin n, R i i ≠ 0 := by
    intro i
    simpa [R] using hdiag i
  exact
    ⟨Q, ΔA, Δb, hQ, hArep, hbrep, hΔA_cols, hΔb,
      hA_top, hA_bottom, hb_top, hupper, hdiagR⟩

theorem paddedEconomyR_upper_trapezoidal {m n : Nat}
    (R : Fin (n + m) -> Fin n -> Real)
    (hR : IsUpperTrapezoidal (n + m) n R) :
    IsUpperTrapezoidal n n (paddedEconomyR R) := by
  exact mgsPaddedEconomyR_upper_trapezoidal R hR

theorem paddedTopBlock_rowsFromFin {m n : Nat}
    (R : Fin (n + m) -> Fin n -> Real) :
    paddedTopBlock (paddedRowsFromFin R) =
      (fun i j => R (paddedRowToFin (Sum.inl i)) j) := by
  exact mgsPaddedTopBlock_rowsFromFin R

theorem paddedBottomBlock_rowsFromFin {m n : Nat}
    (R : Fin (n + m) -> Fin n -> Real) :
    paddedBottomBlock (paddedRowsFromFin R) =
      (fun i j => R (paddedRowToFin (Sum.inr i)) j) := by
  exact mgsPaddedBottomBlock_rowsFromFin R

theorem paddedTopBlock_rowsFromFin_matMul_of_bottom_zero {m n : Nat}
    (Q : Fin (n + m) -> Fin (n + m) -> Real)
    (R : Fin (n + m) -> Fin n -> Real)
    (hRbot :
      paddedBottomBlock (paddedRowsFromFin R) =
        (fun _ _ => 0 : Fin m -> Fin n -> Real)) :
    paddedTopBlock
        (paddedRowsFromFin (matMulRect (n + m) (n + m) n Q R)) =
      matMulRect n n n (paddedEconomyP11 Q) (paddedEconomyR R) := by
  exact mgsPaddedTopBlock_rowsFromFin_matMul_of_bottom_zero Q R hRbot

theorem paddedBottomBlock_rowsFromFin_of_upper {m n : Nat}
    (R : Fin (n + m) -> Fin n -> Real)
    (hR : IsUpperTrapezoidal (n + m) n R) :
    paddedBottomBlock (paddedRowsFromFin R) =
      (fun _ _ => 0 : Fin m -> Fin n -> Real) := by
  exact mgsPaddedBottomBlock_rowsFromFin_of_upper R hR

theorem paddedBottomBlock_rowsFromFin_matMul_of_bottom_zero {m n : Nat}
    (Q : Fin (n + m) -> Fin (n + m) -> Real)
    (R : Fin (n + m) -> Fin n -> Real)
    (hRbot :
      paddedBottomBlock (paddedRowsFromFin R) =
        (fun _ _ => 0 : Fin m -> Fin n -> Real)) :
    paddedBottomBlock
        (paddedRowsFromFin (matMulRect (n + m) (n + m) n Q R)) =
      matMulRect m n n (paddedEconomyQ Q) (paddedEconomyR R) := by
  exact mgsPaddedBottomBlock_rowsFromFin_matMul_of_bottom_zero Q R hRbot

theorem paddedPerturbedInput_bottom_eq_economyProduct {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real)
    (Q : Fin (n + m) -> Fin (n + m) -> Real)
    (R : Fin (n + m) -> Fin n -> Real)
    (hprod :
      paddedPerturbedInput A dTop dBottom =
        paddedRowsFromFin (matMulRect (n + m) (n + m) n Q R))
    (hRbot :
      paddedBottomBlock (paddedRowsFromFin R) =
        (fun _ _ => 0 : Fin m -> Fin n -> Real)) :
    (fun i j => A i j + dBottom i j) =
      matMulRect m n n (paddedEconomyQ Q) (paddedEconomyR R) := by
  exact
    mgsPaddedPerturbedInput_bottom_eq_economyProduct
      A dTop dBottom Q R hprod hRbot

theorem paddedPerturbedInput_top_eq_economyProduct {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real)
    (Q : Fin (n + m) -> Fin (n + m) -> Real)
    (R : Fin (n + m) -> Fin n -> Real)
    (hprod :
      paddedPerturbedInput A dTop dBottom =
        paddedRowsFromFin (matMulRect (n + m) (n + m) n Q R))
    (hRbot :
      paddedBottomBlock (paddedRowsFromFin R) =
        (fun _ _ => 0 : Fin m -> Fin n -> Real)) :
    dTop =
      matMulRect n n n (paddedEconomyP11 Q) (paddedEconomyR R) := by
  exact
    mgsPaddedPerturbedInput_top_eq_economyProduct
      A dTop dBottom Q R hprod hRbot

theorem paddedColumnNorm_rowsFromFin {m n : Nat}
    (C : Fin (n + m) -> Fin n -> Real) (j : Fin n) :
    paddedColumnNorm (paddedRowsFromFin C) j = columnFrob C j := by
  exact mgsPaddedColumnNorm_rowsFromFin C j

theorem paddedColumnNorm_paddedInput {m n : Nat}
    (A : Fin m -> Fin n -> Real) (j : Fin n) :
    paddedColumnNorm (paddedInput A) j = columnFrob A j := by
  exact mgsPaddedColumnNorm_paddedInput A j

theorem columnFrob_paddedFinInput {m n : Nat}
    (A : Fin m -> Fin n -> Real) (j : Fin n) :
    columnFrob (paddedFinInput A) j = columnFrob A j := by
  exact LeanFpAnalysis.FP.columnFrob_paddedFinInput A j

theorem stackedPerturbationColumnNorm_rowsFromFin_add {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (dA : Fin (n + m) -> Fin n -> Real) (j : Fin n) :
    stackedPerturbationColumnNorm
        (paddedTopPerturbation
          (paddedRowsFromFin
            (fun r j => paddedFinInput A r j + dA r j)))
        (paddedBottomPerturbation A
          (paddedRowsFromFin
            (fun r j => paddedFinInput A r j + dA r j))) j =
      columnFrob dA j := by
  exact mgsStackedPerturbationColumnNorm_rowsFromFin_add A dA j

theorem stackedPerturbationColumnwiseBound_of_rowsFromFin_add_bound
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (dA : Fin (n + m) -> Fin n -> Real) {c : Real}
    (hbound : forall j : Fin n, columnFrob dA j <= c * columnFrob A j) :
    stackedPerturbationColumnwiseBound A
      (paddedTopPerturbation
        (paddedRowsFromFin
          (fun r j => paddedFinInput A r j + dA r j)))
      (paddedBottomPerturbation A
        (paddedRowsFromFin
          (fun r j => paddedFinInput A r j + dA r j)))
      c := by
  exact mgsStackedPerturbationColumnwiseBound_of_rowsFromFin_add_bound
    A dA hbound

theorem stackedPerturbationColumnwiseBound_of_rowsFromFin_add_padded_bound
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (dA : Fin (n + m) -> Fin n -> Real) {c : Real}
    (hbound : forall j : Fin n,
      columnFrob dA j <= c * columnFrob (paddedFinInput A) j) :
    stackedPerturbationColumnwiseBound A
      (paddedTopPerturbation
        (paddedRowsFromFin
          (fun r j => paddedFinInput A r j + dA r j)))
      (paddedBottomPerturbation A
        (paddedRowsFromFin
          (fun r j => paddedFinInput A r j + dA r j)))
      c := by
  exact
    mgsStackedPerturbationColumnwiseBound_of_rowsFromFin_add_padded_bound
      A dA hbound

theorem paddedPerturbedInput_zero {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    paddedPerturbedInput A
        (fun _ _ => 0 : Fin n -> Fin n -> Real)
        (fun _ _ => 0 : Fin m -> Fin n -> Real) =
      paddedInput A := by
  exact mgsPaddedPerturbedInput_zero A

theorem stackedPerturbationColumnNorm_zero {m n : Nat}
    (j : Fin n) :
    stackedPerturbationColumnNorm
        (fun _ _ => 0 : Fin n -> Fin n -> Real)
        (fun _ _ => 0 : Fin m -> Fin n -> Real) j = 0 := by
  exact mgsStackedPerturbationColumnNorm_zero j

theorem stackedPerturbationColumnwiseBound_zero {m n : Nat}
    (A : Fin m -> Fin n -> Real) {c : Real} (hc : 0 <= c) :
    stackedPerturbationColumnwiseBound A
      (fun _ _ => 0 : Fin n -> Fin n -> Real)
      (fun _ _ => 0 : Fin m -> Fin n -> Real)
      c := by
  exact mgsStackedPerturbationColumnwiseBound_zero A hc

theorem bottomPerturbationColumnNorm_le_stacked {m n : Nat}
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real)
    (j : Fin n) :
    columnFrob dBottom j <=
      stackedPerturbationColumnNorm dTop dBottom j := by
  exact mgsBottomPerturbationColumnNorm_le_stacked dTop dBottom j

theorem topPerturbationColumnNorm_le_stacked {m n : Nat}
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real)
    (j : Fin n) :
    columnFrob dTop j <=
      stackedPerturbationColumnNorm dTop dBottom j := by
  exact mgsTopPerturbationColumnNorm_le_stacked dTop dBottom j

theorem topPerturbation_columnFrob_le_of_stackedColumnwiseBound
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real)
    {c : Real}
    (hbound : stackedPerturbationColumnwiseBound A dTop dBottom c) :
    forall j, columnFrob dTop j <= c * columnFrob A j := by
  exact
    mgsTopPerturbation_columnFrob_le_of_stackedColumnwiseBound
      A dTop dBottom hbound

theorem bottomPerturbation_columnFrob_le_of_stackedColumnwiseBound
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real)
    {c : Real}
    (hbound : stackedPerturbationColumnwiseBound A dTop dBottom c) :
    forall j, columnFrob dBottom j <= c * columnFrob A j := by
  exact
    mgsBottomPerturbation_columnFrob_le_of_stackedColumnwiseBound
      A dTop dBottom hbound

theorem topPerturbation_frobNormRect_le_of_stackedColumnwiseBound
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real)
    {c : Real} (hc : 0 <= c)
    (hbound : stackedPerturbationColumnwiseBound A dTop dBottom c) :
    frobNormRect dTop <= c * frobNormRect A := by
  exact
    mgsTopPerturbation_frobNormRect_le_of_stackedColumnwiseBound
      A dTop dBottom hc hbound

theorem topPerturbation_rectOpNorm2Le_of_stackedColumnwiseBound
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real)
    {c residualBound : Real} (hc : 0 <= c)
    (hbound : stackedPerturbationColumnwiseBound A dTop dBottom c)
    (hresidual : c * frobNormRect A <= residualBound) :
    rectOpNorm2Le dTop residualBound := by
  exact
    mgsTopPerturbation_rectOpNorm2Le_of_stackedColumnwiseBound
      A dTop dBottom hc hbound hresidual

theorem bottomPerturbation_frobNormRect_le_of_stackedColumnwiseBound
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real)
    {c : Real} (hc : 0 <= c)
    (hbound : stackedPerturbationColumnwiseBound A dTop dBottom c) :
    frobNormRect dBottom <= c * frobNormRect A := by
  exact
    mgsBottomPerturbation_frobNormRect_le_of_stackedColumnwiseBound
      A dTop dBottom hc hbound

theorem bottomPerturbation_rectOpNorm2Le_of_stackedColumnwiseBound
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real)
    {c residualBound : Real} (hc : 0 <= c)
    (hbound : stackedPerturbationColumnwiseBound A dTop dBottom c)
    (hresidual : c * frobNormRect A <= residualBound) :
    rectOpNorm2Le dBottom residualBound := by
  exact
    mgsBottomPerturbation_rectOpNorm2Le_of_stackedColumnwiseBound
      A dTop dBottom hc hbound hresidual

/-- Squared norm of the source vector `[-e_k; q_k]`. -/
theorem householderVector_norm_sq {m n : Nat}
    (q : Fin m -> Real) (k : Fin n) :
    finiteVecNorm2Sq (householderVector q k) =
      1 + finiteVecNorm2Sq q := by
  exact mgsHouseholderVector_norm_sq q k

/-- Equation `(19.28)` normalization channel: if the MGS column is unit
length, then the Householder-MGS vector satisfies `v_k^T v_k = 2`. -/
theorem householderVector_self_dot {m n : Nat}
    {q : Fin m -> Real} {k : Fin n}
    (hq : finiteVecNorm2Sq q = 1) :
    (Finset.univ.sum fun a : Sum (Fin n) (Fin m) =>
      householderVector q k a * householderVector q k a) = 2 := by
  exact mgsHouseholderVector_self_dot hq

/-- The source vector built from the exact MGS column satisfies
`v_k^T v_k = 2` under the nonzero MGS stage-normalizer condition. -/
theorem householderVector_self_dot_computedQ {m n : Nat}
    (A : Fin m -> Fin n -> Real) (k : Fin n)
    (hdiag :
      Ne (gsColumnNorm2 (Algorithm19_12.stageVectors A k.val k)) 0) :
    (Finset.univ.sum fun a : Sum (Fin n) (Fin m) =>
      householderVector (gsColumn (Algorithm19_12.computedQ A) k) k a *
        householderVector (gsColumn (Algorithm19_12.computedQ A) k) k a) =
      2 := by
  exact mgsHouseholderVector_self_dot_computedQ A k hdiag

/-- The source reflector `I - v_k v_k^T` from equation `(19.28)` is
symmetric. -/
theorem householderReflector_symmetric {m n : Nat}
    (q : Fin m -> Real) (k : Fin n) :
    IsSymmetricFiniteMatrix (householderReflector q k) := by
  exact mgsHouseholderReflector_symmetric q k

/-- If `v_k^T v_k = 2`, the source reflector from equation `(19.28)` squares
to the identity. -/
theorem householderReflector_mul_self_of_self_dot {m n : Nat}
    {q : Fin m -> Real} {k : Fin n}
    (hv : (Finset.univ.sum fun a : Sum (Fin n) (Fin m) =>
      householderVector q k a * householderVector q k a) = 2) :
    finiteMatMul (householderReflector q k)
        (householderReflector q k) =
      (finiteIdMatrix :
        Sum (Fin n) (Fin m) -> Sum (Fin n) (Fin m) -> Real) := by
  exact mgsHouseholderReflector_mul_self_of_self_dot hv

/-- For the source padded matrix `[0; A]`, the scalar `v_k^T b_j` is the MGS
dot product `q^T a_j`. -/
theorem householderColumnInner_padded {m n : Nat}
    (A : Fin m -> Fin n -> Real) (q : Fin m -> Real)
    (k j : Fin n) :
    householderColumnInner q k (paddedInput A) j =
      gsDot q (gsColumn A j) := by
  exact mgsHouseholderColumnInner_padded A q k j

/-- At padded stage `k`, the scalar `v_k^T b_j` is the exact MGS row entry
`R_kj`. -/
theorem householderColumnInner_paddedStage {m n : Nat}
    (A : Fin m -> Fin n -> Real) (k j : Fin n)
    (hdiag :
      Ne (gsColumnNorm2 (Algorithm19_12.stageVectors A k.val k)) 0) :
    householderColumnInner (gsColumn (Algorithm19_12.computedQ A) k) k
      (paddedStage A k.val) j =
      Algorithm19_12.computedR A k j := by
  exact mgsHouseholderColumnInner_paddedStage A k j hdiag

/-- Applying the source reflector at stage `k` advances the exact padded
Householder-MGS stage from `k` to `k+1`. -/
theorem householderApply_paddedStage_eq_succ {m n : Nat}
    (A : Fin m -> Fin n -> Real) (k : Fin n)
    (hdiag :
      Ne (gsColumnNorm2 (Algorithm19_12.stageVectors A k.val k)) 0) :
    householderApply (gsColumn (Algorithm19_12.computedQ A) k) k
      (paddedStage A k.val) =
      paddedStage A (k.val + 1) := by
  exact mgsHouseholderApply_paddedStage_eq_succ A k hdiag

/-- If the source vector satisfies `v_k^T v_k = 2`, applying its source
reflector twice is the identity on padded matrices. -/
theorem householderApply_apply_self_of_self_dot {m n : Nat}
    {q : Fin m -> Real} {k : Fin n}
    (hv : (Finset.univ.sum fun a : Sum (Fin n) (Fin m) =>
      householderVector q k a * householderVector q k a) = 2)
    (B : Sum (Fin n) (Fin m) -> Fin n -> Real) :
    householderApply q k (householderApply q k B) = B := by
  exact mgsHouseholderApply_apply_self_of_self_dot hv B

/-- Reverse exact one-step transition: because the source reflector is its own
inverse, applying it to stage `k+1` returns padded stage `k`. -/
theorem householderApply_paddedStage_succ_eq_current {m n : Nat}
    (A : Fin m -> Fin n -> Real) (k : Fin n)
    (hdiag :
      Ne (gsColumnNorm2 (Algorithm19_12.stageVectors A k.val k)) 0) :
    householderApply (gsColumn (Algorithm19_12.computedQ A) k) k
      (paddedStage A (k.val + 1)) =
      paddedStage A k.val := by
  exact mgsHouseholderApply_paddedStage_succ_eq_current A k hdiag

/-- Iterating the exact source reflectors advances the padded MGS stage from
`[0; A]` to stage `t`. -/
theorem householderApplyPrefix_paddedInput {m n : Nat}
    (A : Fin m -> Fin n -> Real) {t : Nat} (ht : t <= n)
    (hdiag : forall k : Fin n, k.val < t ->
      Ne (gsColumnNorm2 (Algorithm19_12.stageVectors A k.val k)) 0) :
    householderApplyPrefix A t (paddedInput A) =
      paddedStage A t := by
  exact mgsHouseholderApplyPrefix_paddedInput A ht hdiag

/-- Full exact endpoint for the forward Householder-MGS prefix product:
applying all source reflectors to `[0; A]` gives `[R; 0]`. -/
theorem householderApplyPrefix_paddedInput_final {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (hdiag : forall k : Fin n,
      Ne (gsColumnNorm2 (Algorithm19_12.stageVectors A k.val k)) 0) :
    householderApplyPrefix A n (paddedInput A) =
      paddedRBlock A := by
  exact mgsHouseholderApplyPrefix_paddedInput_final A hdiag

/-- Iterating the reverse source reflectors sends padded stage `t` back to
the initial padded matrix `[0; A]`. -/
theorem householderApplyReversePrefix_paddedStage {m n : Nat}
    (A : Fin m -> Fin n -> Real) {t : Nat} (ht : t <= n)
    (hdiag : forall k : Fin n, k.val < t ->
      Ne (gsColumnNorm2 (Algorithm19_12.stageVectors A k.val k)) 0) :
    householderApplyReversePrefix A t (paddedStage A t) =
      paddedInput A := by
  exact mgsHouseholderApplyReversePrefix_paddedStage A ht hdiag

/-- Printed-orientation exact endpoint for the Householder-MGS connection:
applying the reverse source-reflector prefix to `[R; 0]` recovers `[0; A]`. -/
theorem householderApplyReversePrefix_paddedRBlock {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (hdiag : forall k : Fin n,
      Ne (gsColumnNorm2 (Algorithm19_12.stageVectors A k.val k)) 0) :
    householderApplyReversePrefix A n (paddedRBlock A) =
      paddedInput A := by
  exact mgsHouseholderApplyReversePrefix_paddedRBlock A hdiag

/-- Top block extracted from the printed-orientation endpoint of `(19.34)`.
In exact arithmetic this is the zero block. -/
theorem householderApplyReversePrefix_paddedRBlock_topBlock {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (hdiag : forall k : Fin n,
      Ne (gsColumnNorm2 (Algorithm19_12.stageVectors A k.val k)) 0) :
    paddedTopBlock
        (householderApplyReversePrefix A n (paddedRBlock A)) =
      (fun _ _ => 0 : Fin n -> Fin n -> Real) := by
  exact mgsHouseholderApplyReversePrefix_paddedRBlock_topBlock A hdiag

/-- Bottom block extracted from the printed-orientation endpoint of `(19.34)`.
In exact arithmetic this recovers the original input matrix. -/
theorem householderApplyReversePrefix_paddedRBlock_bottomBlock {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (hdiag : forall k : Fin n,
      Ne (gsColumnNorm2 (Algorithm19_12.stageVectors A k.val k)) 0) :
    paddedBottomBlock
        (householderApplyReversePrefix A n (paddedRBlock A)) =
      A := by
  exact mgsHouseholderApplyReversePrefix_paddedRBlock_bottomBlock A hdiag

/-- Block form of the exact printed-orientation Householder-MGS endpoint. -/
theorem householderApplyReversePrefix_paddedRBlock_blocks {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (hdiag : forall k : Fin n,
      Ne (gsColumnNorm2 (Algorithm19_12.stageVectors A k.val k)) 0) :
    paddedTopBlock
        (householderApplyReversePrefix A n (paddedRBlock A)) =
        (fun _ _ => 0 : Fin n -> Fin n -> Real) /\
      paddedBottomBlock
        (householderApplyReversePrefix A n (paddedRBlock A)) =
        A := by
  exact mgsHouseholderApplyReversePrefix_paddedRBlock_blocks A hdiag

/-- Exact `(19.34)` perturbed-input form with zero perturbation blocks. -/
theorem householderApplyReversePrefix_paddedRBlock_perturbedInput_zero
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hdiag : forall k : Fin n,
      Ne (gsColumnNorm2 (Algorithm19_12.stageVectors A k.val k)) 0) :
    householderApplyReversePrefix A n (paddedRBlock A) =
      paddedPerturbedInput A
        (fun _ _ => 0 : Fin n -> Fin n -> Real)
        (fun _ _ => 0 : Fin m -> Fin n -> Real) := by
  exact
    mgsHouseholderApplyReversePrefix_paddedRBlock_perturbedInput_zero A hdiag

/-- Current top row after applying the source reflector to `[0; A]`. -/
theorem householderApply_padded_top_current {m n : Nat}
    (A : Fin m -> Fin n -> Real) (q : Fin m -> Real)
    (k j : Fin n) :
    householderApply q k (paddedInput A) (Sum.inl k) j =
      gsDot q (gsColumn A j) := by
  exact mgsHouseholderApply_padded_top_current A q k j

/-- Inactive top rows remain zero after applying the source reflector to
`[0; A]`. -/
theorem householderApply_padded_top_ne {m n : Nat}
    (A : Fin m -> Fin n -> Real) (q : Fin m -> Real)
    {k i : Fin n} (hki : Ne i k) (j : Fin n) :
    householderApply q k (paddedInput A) (Sum.inl i) j = 0 := by
  exact mgsHouseholderApply_padded_top_ne A q hki j

/-- Bottom block after applying the source reflector to `[0; A]`; this is the
MGS projection update. -/
theorem householderApply_padded_bottom {m n : Nat}
    (A : Fin m -> Fin n -> Real) (q : Fin m -> Real)
    (k : Fin n) (i : Fin m) (j : Fin n) :
    householderApply q k (paddedInput A) (Sum.inr i) j =
      A i j - q i * gsDot q (gsColumn A j) := by
  exact mgsHouseholderApply_padded_bottom A q k i j

end Theorem19_13

namespace Theorem19_4

/-- Formal coefficient used for the Higham 19.4 Householder QR bound.

The printed theorem writes this as a dimension-dependent `gamma_tilde_mn`.
The current implementation realizes that coefficient with the repository's
concrete Householder construction/application gamma index. -/
noncomputable def gamma_tilde (fp : FPModel) (m n : Nat) : Real :=
  gamma fp (n * householderConstructApplyGammaIndex m)

/-- The Householder QR coefficient is nonnegative under the same smallness
condition used by the backward-error theorem. -/
theorem gamma_tilde_nonneg (fp : FPModel) {m n : Nat}
    (hvalid : gammaValid fp (n * householderConstructApplyGammaIndex m)) :
    0 <= gamma_tilde fp m n := by
  simpa [gamma_tilde] using gamma_nonneg fp hvalid

/-- Linear-in-unit-roundoff cap for the Householder QR coefficient under the
standard smallness condition on its operation index. -/
theorem gamma_tilde_le_two_index_mul_unit_roundoff_of_small
    (fp : FPModel) (m n : Nat)
    (hsmall :
      (((n * householderConstructApplyGammaIndex m : Nat) : Real) *
        fp.u <= 1 / 2)) :
    gamma_tilde fp m n <=
      (2 * ((n * householderConstructApplyGammaIndex m : Nat) : Real)) *
        fp.u := by
  have hgamma :=
    gamma_le_two_mul_n_u_of_nu_le_half
      fp (n * householderConstructApplyGammaIndex m) hsmall
  simpa [gamma_tilde, mul_assoc, mul_left_comm, mul_comm] using hgamma

/-- Source-facing form of Higham, Theorem 19.4.

The contract records the computed upper-trapezoidal `R_hat`, an exact
orthogonal witness `Q`, the equation `A + dA = Q * R_hat`, and the advertised
columnwise Euclidean perturbation bound. -/
structure HouseholderQRBackwardError (m n : Nat)
    (A : Fin m -> Fin n -> Real) (Q : Fin m -> Fin m -> Real)
    (R_hat : Fin m -> Fin n -> Real) (c : Real) : Prop where
  upper : IsUpperTrapezoidal m n R_hat
  orth : IsOrthogonal m Q
  result : Exists fun dA : Fin m -> Fin n -> Real =>
    (forall i j, A i j + dA i j = matMulRect m m n Q R_hat i j) /\
    (forall j, columnFrob dA j <= c * columnFrob A j)

/-- Componentwise `G |A|` form of the Higham 19.4 Householder QR backward
error, with the printed orientation `A + dA = Q * R_hat`. -/
structure HouseholderQRComponentwiseBackwardError (m n : Nat)
    (A : Fin m -> Fin n -> Real) (Q : Fin m -> Fin m -> Real)
    (R_hat : Fin m -> Fin n -> Real) (c_norm c_comp : Real) : Prop where
  upper : IsUpperTrapezoidal m n R_hat
  orth : IsOrthogonal m Q
  result : Exists fun dA : Fin m -> Fin n -> Real =>
    Exists fun G : Fin m -> Fin m -> Real =>
      (forall i j, A i j + dA i j = matMulRect m m n Q R_hat i j) /\
      frobNorm dA <= c_norm /\
      (forall i j, 0 <= G i j) /\
      frobNorm G = 1 /\
      (forall i j, |dA i j| <=
        c_comp * matMulRect m m n G (fun a b => |A a b|) i j)

/-- Convert the repository's panel representation `R = Q^T (A + dA)` into
the printed Higham 19.4 equation `A + dA = Q R`. -/
theorem of_panel_columnwise {m n : Nat}
    {A : Fin m -> Fin n -> Real} {Q : Fin m -> Fin m -> Real}
    {R_hat : Fin m -> Fin n -> Real} {c_norm c_col : Real}
    (h : HouseholderQRPanelColumnwiseBackwardError m n A Q R_hat c_norm c_col) :
    HouseholderQRBackwardError m n A Q R_hat c_col := by
  cases h.result with
  | intro dA hdA =>
    cases hdA with
    | intro hR hTail =>
      cases hTail with
      | intro _hNorm hCol =>
        refine { upper := h.upper, orth := h.orth, result := ?_ }
        refine Exists.intro dA ?_
        refine And.intro ?_ hCol
        intro i j
        have hRmat :
            R_hat =
              matMulRect m m n (matTranspose Q)
                (fun a b => A a b + dA a b) := by
          ext a b
          exact hR a b
        have hQQT : matMul m Q (matTranspose Q) = idMatrix m := by
          ext a b
          exact h.orth.right_inv a b
        calc
          A i j + dA i j =
              matMulRect m m n (idMatrix m)
                (fun a b => A a b + dA a b) i j := by
                rw [matMulRect_id_left]
          _ = matMulRect m m n (matMul m Q (matTranspose Q))
                (fun a b => A a b + dA a b) i j := by
                rw [hQQT]
          _ = matMulRect m m n Q
                (matMulRect m m n (matTranspose Q)
                  (fun a b => A a b + dA a b)) i j := by
                rw [matMulRect_assoc_square_left]
          _ = matMulRect m m n Q R_hat i j := by
                rw [<- hRmat]

/-- Convert the proof-facing componentwise panel representation
`R = Q^T (A + dA)` into the printed Higham 19.4 orientation
`A + dA = Q R`. -/
theorem of_panel_componentwise {m n : Nat}
    {A : Fin m -> Fin n -> Real} {Q : Fin m -> Fin m -> Real}
    {R_hat : Fin m -> Fin n -> Real} {c_norm c_comp : Real}
    (h : StructuredHouseholderQRPanelHighamBackwardError
      m n A Q R_hat c_norm c_comp) :
    HouseholderQRComponentwiseBackwardError
      m n A Q R_hat c_norm c_comp := by
  rcases h.result with ⟨dA, G, hR, hNorm, hGnonneg, hGfrob, hComp⟩
  refine { upper := h.upper, orth := h.orth, result := ?_ }
  refine Exists.intro dA ?_
  refine Exists.intro G ?_
  refine And.intro ?_ ?_
  · intro i j
    have hRmat :
        R_hat =
          matMulRect m m n (matTranspose Q)
            (fun a b => A a b + dA a b) := by
      ext a b
      exact hR a b
    have hQQT : matMul m Q (matTranspose Q) = idMatrix m := by
      ext a b
      exact h.orth.right_inv a b
    calc
      A i j + dA i j =
          matMulRect m m n (idMatrix m)
            (fun a b => A a b + dA a b) i j := by
            rw [matMulRect_id_left]
      _ = matMulRect m m n (matMul m Q (matTranspose Q))
            (fun a b => A a b + dA a b) i j := by
            rw [hQQT]
      _ = matMulRect m m n Q
            (matMulRect m m n (matTranspose Q)
              (fun a b => A a b + dA a b)) i j := by
            rw [matMulRect_assoc_square_left]
      _ = matMulRect m m n Q R_hat i j := by
            rw [<- hRmat]
  · exact And.intro hNorm
      (And.intro hGnonneg (And.intro hGfrob hComp))

/-- Higham, Theorem 19.4: Householder QR backward error for a tall rectangular
matrix, stated with the public Split 3B source-facing name.

For `A : R^(m x n)` with `0 < n` and `n <= m`, the concrete zero-aware
Householder QR panel algorithm returns an upper-trapezoidal `R_hat` and an
exact orthogonal witness `Q` such that `A + dA = Q R_hat`, with each
perturbation column bounded by `gamma_tilde fp m n` times the corresponding
input column norm. -/
theorem householder_qr_backward_error
    (fp : FPModel) (m n : Nat) (A : Fin m -> Fin n -> Real)
    (hn : 0 < n) (hnm : n <= m)
    (hvalid : gammaValid fp (n * householderConstructApplyGammaIndex m)) :
    HouseholderQRBackwardError m n A
      (fl_householderQRPanel_Q fp m n A)
      (fl_householderQRPanel_R fp m n A)
      (gamma_tilde fp m n) := by
  have hsteps : 0 < Nat.min m n := by
    simpa [Nat.min_eq_right hnm] using hn
  have hpanel :
      HouseholderQRPanelColumnwiseBackwardError m n A
        (fl_householderQRPanel_Q fp m n A)
        (fl_householderQRPanel_R fp m n A)
        (gamma fp (Nat.min m n * householderConstructApplyGammaIndex m) *
          frobNorm A)
        (gamma fp (Nat.min m n * householderConstructApplyGammaIndex m)) :=
    fl_householderQRPanel_R_columnwise_backward_error_gammaHigham_of_global_gammaValid
      fp m n A hsteps (by
        simpa [Nat.min_eq_right hnm] using hvalid)
  simpa [gamma_tilde, Nat.min_eq_right hnm] using of_panel_columnwise hpanel

/-- Equation `(19.11)`/Theorem 19.4 columnwise backward-error form, using the
public source-facing theorem name. -/
theorem eq19_11_columnwise_backward_error
    (fp : FPModel) (m n : Nat) (A : Fin m -> Fin n -> Real)
    (hn : 0 < n) (hnm : n <= m)
    (hvalid : gammaValid fp (n * householderConstructApplyGammaIndex m)) :
    HouseholderQRBackwardError m n A
      (fl_householderQRPanel_Q fp m n A)
      (fl_householderQRPanel_R fp m n A)
      (gamma_tilde fp m n) :=
  householder_qr_backward_error fp m n A hn hnm hvalid

/-- Higham, Theorem 19.4 componentwise `G |A|` form for the concrete
Householder QR panel path.

This is the source-facing equation `(19.12)` shape: the same exact orthogonal
`Q` and computed `R_hat` give `A + dA = Q * R_hat`, with a nonnegative
Frobenius-unit matrix `G` controlling `|dA|` componentwise. -/
theorem householder_qr_componentwise_backward_error
    (fp : FPModel) (m n : Nat) (A : Fin m -> Fin n -> Real)
    (hn : 0 < n) (hnm : n <= m)
    (hvalid : gammaValid fp (n * householderConstructApplyGammaIndex m)) :
    HouseholderQRComponentwiseBackwardError m n A
      (fl_householderQRPanel_Q fp m n A)
      (fl_householderQRPanel_R fp m n A)
      (gamma_tilde fp m n * frobNorm A)
      ((m : Real) * gamma_tilde fp m n) := by
  have hm : 0 < m := Nat.lt_of_lt_of_le hn hnm
  have hsteps : 0 < Nat.min m n := by
    simpa [Nat.min_eq_right hnm] using hn
  have hvalid_min :
      gammaValid fp (Nat.min m n * householderConstructApplyGammaIndex m) := by
    simpa [Nat.min_eq_right hnm] using hvalid
  have hgamma_nonneg :
      0 <= gamma fp (Nat.min m n * householderConstructApplyGammaIndex m) :=
    gamma_nonneg fp hvalid_min
  have hpanel :
      HouseholderQRPanelColumnwiseBackwardError m n A
        (fl_householderQRPanel_Q fp m n A)
        (fl_householderQRPanel_R fp m n A)
        (gamma fp (Nat.min m n * householderConstructApplyGammaIndex m) *
          frobNorm A)
        (gamma fp (Nat.min m n * householderConstructApplyGammaIndex m)) :=
    fl_householderQRPanel_R_columnwise_backward_error_gammaHigham_of_global_gammaValid
      fp m n A hsteps hvalid_min
  have hhigham :
      StructuredHouseholderQRPanelHighamBackwardError m n A
        (fl_householderQRPanel_Q fp m n A)
        (fl_householderQRPanel_R fp m n A)
        (gamma fp (Nat.min m n * householderConstructApplyGammaIndex m) *
          frobNorm A)
        ((m : Real) *
          gamma fp (Nat.min m n * householderConstructApplyGammaIndex m)) :=
    HouseholderQRPanelColumnwiseBackwardError.to_higham
      hpanel hm hgamma_nonneg
  simpa [gamma_tilde, Nat.min_eq_right hnm] using
    of_panel_componentwise hhigham

/-- Equation `(19.12)` componentwise backward-error form, exposed as a
source-labeled wrapper around the componentwise Theorem 19.4 surface. -/
theorem eq19_12_componentwise_backward_error
    (fp : FPModel) (m n : Nat) (A : Fin m -> Fin n -> Real)
    (hn : 0 < n) (hnm : n <= m)
    (hvalid : gammaValid fp (n * householderConstructApplyGammaIndex m)) :
    HouseholderQRComponentwiseBackwardError m n A
      (fl_householderQRPanel_Q fp m n A)
      (fl_householderQRPanel_R fp m n A)
      (gamma_tilde fp m n * frobNorm A)
      ((m : Real) * gamma_tilde fp m n) :=
  householder_qr_componentwise_backward_error fp m n A hn hnm hvalid

end Theorem19_4

namespace Theorem19_13

/-- Instantiate Theorem 19.4 on the padded MGS input and convert its
columnwise Householder perturbation bound into the stacked perturbation shape
used in equation `(19.34)`. -/
theorem householder_paddedFinInput_stackedPerturbation
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m))) :
    Exists fun dA : Fin (n + m) -> Fin n -> Real =>
      (forall r j,
        paddedFinInput A r j + dA r j =
          matMulRect (n + m) (n + m) n
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A))
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            r j) /\
      stackedPerturbationColumnwiseBound A
        (paddedTopPerturbation
          (paddedRowsFromFin
            (fun r j => paddedFinInput A r j + dA r j)))
        (paddedBottomPerturbation A
          (paddedRowsFromFin
            (fun r j => paddedFinInput A r j + dA r j)))
        (Theorem19_4.gamma_tilde fp (n + m) n) := by
  have hnm : n <= n + m := Nat.le_add_right n m
  have hqr :=
    Theorem19_4.householder_qr_backward_error
      fp (n + m) n (paddedFinInput A) hn hnm hvalid
  cases hqr.result with
  | intro dA hres =>
      cases hres with
      | intro heq hbound =>
          refine Exists.intro dA ?_
          exact And.intro heq
            (stackedPerturbationColumnwiseBound_of_rowsFromFin_add_padded_bound
              A dA hbound)

/-- Block-form version of the padded Householder handoff for equation
`(19.34)`: the perturbed padded input is a product with an upper-trapezoidal
Householder `Rhat`, whose bottom block is zero in the sum-indexed view. -/
theorem householder_paddedFinInput_perturbedInput_blocks
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m))) :
    Exists fun dTop : Fin n -> Fin n -> Real =>
    Exists fun dBottom : Fin m -> Fin n -> Real =>
      let Q : Fin (n + m) -> Fin (n + m) -> Real :=
        fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)
      let Rhat : Fin (n + m) -> Fin n -> Real :=
        fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)
      paddedPerturbedInput A dTop dBottom =
        paddedRowsFromFin (matMulRect (n + m) (n + m) n Q Rhat) /\
      paddedBottomBlock (paddedRowsFromFin Rhat) =
        (fun _ _ => 0 : Fin m -> Fin n -> Real) /\
      stackedPerturbationColumnwiseBound A dTop dBottom
        (Theorem19_4.gamma_tilde fp (n + m) n) := by
  let Q : Fin (n + m) -> Fin (n + m) -> Real :=
    fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)
  let Rhat : Fin (n + m) -> Fin n -> Real :=
    fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)
  have hnm : n <= n + m := Nat.le_add_right n m
  have hqr :=
    Theorem19_4.householder_qr_backward_error
      fp (n + m) n (paddedFinInput A) hn hnm hvalid
  cases hqr.result with
  | intro dA hres =>
      cases hres with
      | intro heq hbound =>
          let Badd : Sum (Fin n) (Fin m) -> Fin n -> Real :=
            paddedRowsFromFin (fun r j => paddedFinInput A r j + dA r j)
          let dTop : Fin n -> Fin n -> Real := paddedTopPerturbation Badd
          let dBottom : Fin m -> Fin n -> Real :=
            paddedBottomPerturbation A Badd
          refine Exists.intro dTop ?_
          refine Exists.intro dBottom ?_
          have hB :
              Badd =
                paddedRowsFromFin
                  (matMulRect (n + m) (n + m) n Q Rhat) := by
            ext a j
            simp [Badd, Q, Rhat, paddedRowsFromFin, heq]
          have hinput :
              paddedPerturbedInput A dTop dBottom =
                paddedRowsFromFin
                  (matMulRect (n + m) (n + m) n Q Rhat) := by
            calc
              paddedPerturbedInput A dTop dBottom = Badd := by
                exact paddedPerturbedInput_eta A Badd
              _ = paddedRowsFromFin
                    (matMulRect (n + m) (n + m) n Q Rhat) := hB
          have hbottom :
              paddedBottomBlock (paddedRowsFromFin Rhat) =
                (fun _ _ => 0 : Fin m -> Fin n -> Real) := by
            exact paddedBottomBlock_rowsFromFin_of_upper Rhat hqr.upper
          have hstack :
              stackedPerturbationColumnwiseBound A dTop dBottom
                (Theorem19_4.gamma_tilde fp (n + m) n) := by
            exact
              stackedPerturbationColumnwiseBound_of_rowsFromFin_add_padded_bound
                A dA hbound
          exact And.intro hinput (And.intro hbottom hstack)

/-- Economy-product version of the padded Householder handoff.  It extracts
the bottom block of `(19.34)` as
`A + Delta A4 = Q21 * R11`, while retaining the zero lower `Rhat` block and
the stacked perturbation bound. -/
theorem householder_paddedFinInput_economyProduct
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m))) :
    Exists fun dTop : Fin n -> Fin n -> Real =>
    Exists fun dBottom : Fin m -> Fin n -> Real =>
      let Q : Fin (n + m) -> Fin (n + m) -> Real :=
        fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)
      let Rhat : Fin (n + m) -> Fin n -> Real :=
        fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)
      (fun i j => A i j + dBottom i j) =
        matMulRect m n n (paddedEconomyQ Q) (paddedEconomyR Rhat) /\
      paddedBottomBlock (paddedRowsFromFin Rhat) =
        (fun _ _ => 0 : Fin m -> Fin n -> Real) /\
      stackedPerturbationColumnwiseBound A dTop dBottom
        (Theorem19_4.gamma_tilde fp (n + m) n) := by
  let Q : Fin (n + m) -> Fin (n + m) -> Real :=
    fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)
  let Rhat : Fin (n + m) -> Fin n -> Real :=
    fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)
  have hblock :=
    householder_paddedFinInput_perturbedInput_blocks fp A hn hvalid
  cases hblock with
  | intro dTop htop =>
      cases htop with
      | intro dBottom hres =>
          refine Exists.intro dTop ?_
          refine Exists.intro dBottom ?_
          dsimp only
          have hprod :
              paddedPerturbedInput A dTop dBottom =
                paddedRowsFromFin (matMulRect (n + m) (n + m) n Q Rhat) :=
            hres.1
          have hRbot :
              paddedBottomBlock (paddedRowsFromFin Rhat) =
                (fun _ _ => 0 : Fin m -> Fin n -> Real) :=
            hres.2.1
          have hbottomProduct :
              (fun i j => A i j + dBottom i j) =
                matMulRect m n n (paddedEconomyQ Q)
                  (paddedEconomyR Rhat) := by
            exact paddedPerturbedInput_bottom_eq_economyProduct
              A dTop dBottom Q Rhat hprod hRbot
          exact And.intro hbottomProduct
            (And.intro hRbot hres.2.2)

/-- Economy-product handoff with the upper-trapezoidal shape of the extracted
`R11` block made explicit for the Theorem 19.13 stability contract. -/
theorem householder_paddedFinInput_economyProduct_with_upper
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m))) :
    Exists fun dTop : Fin n -> Fin n -> Real =>
    Exists fun dBottom : Fin m -> Fin n -> Real =>
      let Q : Fin (n + m) -> Fin (n + m) -> Real :=
        fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)
      let Rhat : Fin (n + m) -> Fin n -> Real :=
        fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)
      (fun i j => A i j + dBottom i j) =
        matMulRect m n n (paddedEconomyQ Q) (paddedEconomyR Rhat) /\
      IsUpperTrapezoidal n n (paddedEconomyR Rhat) /\
      paddedBottomBlock (paddedRowsFromFin Rhat) =
        (fun _ _ => 0 : Fin m -> Fin n -> Real) /\
      stackedPerturbationColumnwiseBound A dTop dBottom
        (Theorem19_4.gamma_tilde fp (n + m) n) := by
  let Q : Fin (n + m) -> Fin (n + m) -> Real :=
    fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)
  let Rhat : Fin (n + m) -> Fin n -> Real :=
    fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)
  have hnm : n <= n + m := Nat.le_add_right n m
  have hqr :=
    Theorem19_4.householder_qr_backward_error
      fp (n + m) n (paddedFinInput A) hn hnm hvalid
  have hupper :
      IsUpperTrapezoidal n n (paddedEconomyR Rhat) := by
    exact paddedEconomyR_upper_trapezoidal Rhat hqr.upper
  have hecon :=
    householder_paddedFinInput_economyProduct fp A hn hvalid
  cases hecon with
  | intro dTop htop =>
      cases htop with
      | intro dBottom hres =>
          refine Exists.intro dTop ?_
          refine Exists.intro dBottom ?_
          dsimp only
          exact And.intro hres.1
            (And.intro hupper hres.2)

/-- Full source-facing block data for the padded Householder handoff in
`(19.34)`.  This keeps the top equation `Delta A3 = P11 * R11`, the bottom
economy product, the full padded orthogonality witness, the upper shape of
`R11`, and the stacked perturbation bound together for the subsequent
orthonormal-repair/QR-sensitivity step. -/
theorem householder_paddedFinInput_full_block_data
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m))) :
    Exists fun dTop : Fin n -> Fin n -> Real =>
    Exists fun dBottom : Fin m -> Fin n -> Real =>
      let Q : Fin (n + m) -> Fin (n + m) -> Real :=
        fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)
      let Rhat : Fin (n + m) -> Fin n -> Real :=
        fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)
      dTop =
        matMulRect n n n (paddedEconomyP11 Q) (paddedEconomyR Rhat) /\
      (fun i j => A i j + dBottom i j) =
        matMulRect m n n (paddedEconomyQ Q) (paddedEconomyR Rhat) /\
      IsOrthogonal (n + m) Q /\
      IsUpperTrapezoidal n n (paddedEconomyR Rhat) /\
      paddedBottomBlock (paddedRowsFromFin Rhat) =
        (fun _ _ => 0 : Fin m -> Fin n -> Real) /\
      stackedPerturbationColumnwiseBound A dTop dBottom
        (Theorem19_4.gamma_tilde fp (n + m) n) := by
  let Q : Fin (n + m) -> Fin (n + m) -> Real :=
    fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)
  let Rhat : Fin (n + m) -> Fin n -> Real :=
    fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)
  have hnm : n <= n + m := Nat.le_add_right n m
  have hqr :=
    Theorem19_4.householder_qr_backward_error
      fp (n + m) n (paddedFinInput A) hn hnm hvalid
  have hupper :
      IsUpperTrapezoidal n n (paddedEconomyR Rhat) := by
    exact paddedEconomyR_upper_trapezoidal Rhat hqr.upper
  have hblock :=
    householder_paddedFinInput_perturbedInput_blocks fp A hn hvalid
  cases hblock with
  | intro dTop htop =>
      cases htop with
      | intro dBottom hres =>
          refine Exists.intro dTop ?_
          refine Exists.intro dBottom ?_
          dsimp only
          have hprod :
              paddedPerturbedInput A dTop dBottom =
                paddedRowsFromFin (matMulRect (n + m) (n + m) n Q Rhat) :=
            hres.1
          have hRbot :
              paddedBottomBlock (paddedRowsFromFin Rhat) =
                (fun _ _ => 0 : Fin m -> Fin n -> Real) :=
            hres.2.1
          have htopProduct :
              dTop =
                matMulRect n n n (paddedEconomyP11 Q)
                  (paddedEconomyR Rhat) := by
            exact paddedPerturbedInput_top_eq_economyProduct
              A dTop dBottom Q Rhat hprod hRbot
          have hbottomProduct :
              (fun i j => A i j + dBottom i j) =
                matMulRect m n n (paddedEconomyQ Q)
                  (paddedEconomyR Rhat) := by
            exact paddedPerturbedInput_bottom_eq_economyProduct
              A dTop dBottom Q Rhat hprod hRbot
          exact And.intro htopProduct
            (And.intro hbottomProduct
              (And.intro hqr.orth
                (And.intro hupper (And.intro hRbot hres.2.2))))

/-- Block-column orthogonality extracted from the padded Householder-MGS
orthogonal witness: `P11^T P11 + Q21^T Q21 = I`. -/
theorem paddedEconomy_blocks_gram_sum_eq_id {m n : Nat}
    {P : Fin (n + m) -> Fin (n + m) -> Real}
    (hP : IsOrthogonal (n + m) P) :
    (fun i j =>
        rectangularGram (paddedEconomyP11 P) i j +
          rectangularGram (paddedEconomyQ P) i j) =
      idMatrix n := by
  exact LeanFpAnalysis.FP.mgsPaddedEconomy_blocks_gram_sum_eq_id hP

/-- Chapter-facing bridge from full padded orthogonality to the corrected
Problem 19.12 CS/polar input for the economy blocks. -/
theorem problem1912_csPolarInput_of_paddedEconomy_blocks {m n : Nat}
    {P : Fin (n + m) -> Fin (n + m) -> Real}
    (hnm : n <= m)
    (hP : IsOrthogonal (n + m) P) :
    Problem1912CSPolarInput m n
      (paddedEconomyP11 P) (paddedEconomyQ P) := by
  exact
    LeanFpAnalysis.FP.MGSProblem1912CSPolarInput.of_paddedEconomy_blocks
      hnm hP

/-- The actual padded Householder block data used in `(19.34)` supplies the
corrected Problem 19.12 CS/polar input for its economy blocks. -/
theorem householder_paddedFinInput_csPolarInput
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m))) :
    Problem1912CSPolarInput m n
      (paddedEconomyP11
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A))) := by
  let Q : Fin (n + m) -> Fin (n + m) -> Real :=
    fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)
  have hblock :=
    householder_paddedFinInput_full_block_data fp A hn hvalid
  cases hblock with
  | intro dTop htop =>
      cases htop with
      | intro dBottom hres =>
          dsimp only at hres
          exact
            problem1912_csPolarInput_of_paddedEconomy_blocks
              (m := m) (n := n) (P := Q) hnm hres.2.2.1

/-- The actual padded Householder block data supplies pure Problem 19.12
correction-map data for the economy blocks. -/
theorem householder_paddedFinInput_correctionMapData_exists
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m))) :
    Exists fun Qrepair : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      Problem1912CorrectionMapData m n
        (paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        Qrepair F := by
  exact
    problem1912_correctionMapData_exists_of_csPolarInput
      (householder_paddedFinInput_csPolarInput fp A hn hnm hvalid)

/-- The actual padded Householder block data supplies the additive Problem
19.12 repair witnesses for the economy blocks. -/
theorem householder_paddedFinInput_add_factor_exists
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m))) :
    Exists fun Qrepair : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      (Qrepair =
          fun i j =>
            paddedEconomyQ
                (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A))
                i j +
              matMulRect m n n F
                (paddedEconomyP11
                  (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
                i j) /\
        GramSchmidtOrthonormalColumns Qrepair /\
        rectOpNorm2Le F 1 := by
  exact
    problem1912_add_factor_exists_of_csPolarInput
      (householder_paddedFinInput_csPolarInput fp A hn hnm hvalid)

/-- The actual padded Householder top-left economy block is a contraction once
the corrected Problem 19.12 input is instantiated. -/
theorem householder_paddedFinInput_p11_opNorm2Le_one
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m))) :
    opNorm2Le
      (paddedEconomyP11
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      1 := by
  exact
    problem1912_csPolarInput_p11_opNorm2Le_one
      (householder_paddedFinInput_csPolarInput fp A hn hnm hvalid)

/-- The actual padded Householder bottom-left economy block is a contraction
once the corrected Problem 19.12 input is instantiated. -/
theorem householder_paddedFinInput_p21_rectOpNorm2Le_one
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m))) :
    rectOpNorm2Le
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      1 := by
  exact
    problem1912_csPolarInput_p21_rectOpNorm2Le_one
      (householder_paddedFinInput_csPolarInput fp A hn hnm hvalid)

/-- The actual padded Householder bottom-left economy block has Gram matrix
`I - P11^T P11` once the corrected Problem 19.12 input is instantiated. -/
theorem householder_paddedFinInput_p21_gram_eq_id_sub_p11_gram
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m))) :
    rectangularGram
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A))) =
      fun i j => idMatrix n i j -
        rectangularGram
          (paddedEconomyP11
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A))) i j := by
  exact
    problem1912_csPolarInput_p21_gram_eq_id_sub_p11_gram
      (householder_paddedFinInput_csPolarInput fp A hn hnm hvalid)

/-- The actual padded Householder top-left economy block has Gram matrix
`I - Q21^T Q21` once the corrected Problem 19.12 input is instantiated. -/
theorem householder_paddedFinInput_p11_gram_eq_id_sub_p21_gram
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m))) :
    rectangularGram
        (paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A))) =
      fun i j => idMatrix n i j -
        rectangularGram
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A))) i j := by
  exact
    problem1912_csPolarInput_p11_gram_eq_id_sub_p21_gram
      (householder_paddedFinInput_csPolarInput fp A hn hnm hvalid)

/-- The actual padded Householder top-left economy-block Gram matrix is
symmetric once the corrected Problem 19.12 input is instantiated. -/
theorem householder_paddedFinInput_p11_gram_symmetric
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m))) :
    forall i j : Fin n,
      rectangularGram
          (paddedEconomyP11
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A))) i j =
        rectangularGram
          (paddedEconomyP11
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A))) j i := by
  exact
    problem1912_csPolarInput_p11_gram_symmetric
      (householder_paddedFinInput_csPolarInput fp A hn hnm hvalid)

/-- The actual padded Householder bottom-left economy-block Gram matrix is
symmetric once the corrected Problem 19.12 input is instantiated. -/
theorem householder_paddedFinInput_p21_gram_symmetric
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m))) :
    forall i j : Fin n,
      rectangularGram
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A))) i j =
        rectangularGram
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A))) j i := by
  exact
    problem1912_csPolarInput_p21_gram_symmetric
      (householder_paddedFinInput_csPolarInput fp A hn hnm hvalid)

/-- The actual padded Householder top and bottom economy-block Gram matrices
commute once the corrected Problem 19.12 input is instantiated. -/
theorem householder_paddedFinInput_grams_commute
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m))) :
    matMul n
        (rectangularGram
          (paddedEconomyP11
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A))))
        (rectangularGram
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))) =
      matMul n
        (rectangularGram
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A))))
        (rectangularGram
          (paddedEconomyP11
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))) := by
  exact
    problem1912_csPolarInput_grams_commute
      (householder_paddedFinInput_csPolarInput fp A hn hnm hvalid)

/-- Bottom-left economy-block Gram identity, equivalently
`Q21^T Q21 = I - P11^T P11`. -/
theorem paddedEconomyQ_gram_eq_id_sub_P11_gram {m n : Nat}
    {P : Fin (n + m) -> Fin (n + m) -> Real}
    (hP : IsOrthogonal (n + m) P) :
    rectangularGram (paddedEconomyQ P) =
      fun i j => idMatrix n i j -
        rectangularGram (paddedEconomyP11 P) i j := by
  exact LeanFpAnalysis.FP.mgsPaddedEconomyQ_gram_eq_id_sub_P11_gram hP

/-- Orthogonality residual of the bottom-left economy block from full padded
orthogonality, before the CS/polar repair step. -/
theorem paddedEconomyQ_orthogonalityResidual_eq_neg_P11_gram {m n : Nat}
    {P : Fin (n + m) -> Fin (n + m) -> Real}
    (hP : IsOrthogonal (n + m) P) :
    orthogonalityResidual (paddedEconomyQ P) =
      fun i j => -rectangularGram (paddedEconomyP11 P) i j := by
  exact LeanFpAnalysis.FP.mgsPaddedEconomyQ_orthogonalityResidual_eq_neg_P11_gram hP

/-- Norm consequence of the padded block identity before the CS/polar repair:
if the top-left block `P11` is small, then the economy block has small Gram
orthogonality residual. -/
theorem paddedEconomyQ_orthogonalityResidual_opNorm2Le_of_P11_rectOpNorm2Le
    {m n : Nat} {P : Fin (n + m) -> Fin (n + m) -> Real} {eta : Real}
    (hP : IsOrthogonal (n + m) P)
    (heta : 0 <= eta)
    (hP11 : rectOpNorm2Le (paddedEconomyP11 P) eta) :
    opNorm2Le (orthogonalityResidual (paddedEconomyQ P)) (eta ^ 2) := by
  exact
    LeanFpAnalysis.FP.mgsPaddedEconomyQ_orthogonalityResidual_opNorm2Le_of_P11_rectOpNorm2Le
      hP heta hP11

/-- Source-facing top-block right-inverse bridge: the equation
`Delta A3 = P11 * R11` and a bounded right inverse for `R11` control `P11`. -/
theorem paddedEconomyP11_rectOpNorm2Le_of_top_product_right_inverse
    {m n : Nat} {P : Fin (n + m) -> Fin (n + m) -> Real}
    {dTop Rhat Rinv : Fin n -> Fin n -> Real} {eta rho : Real}
    (htop : dTop = matMulRect n n n (paddedEconomyP11 P) Rhat)
    (hRright : matMul n Rhat Rinv = idMatrix n)
    (hdTop : rectOpNorm2Le dTop eta)
    (hRinv : rectOpNorm2Le Rinv rho)
    (heta : 0 <= eta) :
    rectOpNorm2Le (paddedEconomyP11 P) (eta * rho) := by
  exact
    LeanFpAnalysis.FP.mgsPaddedEconomyP11_rectOpNorm2Le_of_top_product_right_inverse
      htop hRright hdTop hRinv heta

/-- Source-facing pre-repair Gram-residual bound obtained from the top block
`Delta A3 = P11 * R11`, full padded orthogonality, and a bounded right inverse
for `R11`. -/
theorem paddedEconomyQ_orthogonalityResidual_opNorm2Le_of_top_product_right_inverse
    {m n : Nat} {P : Fin (n + m) -> Fin (n + m) -> Real}
    {dTop Rhat Rinv : Fin n -> Fin n -> Real} {eta rho : Real}
    (hP : IsOrthogonal (n + m) P)
    (htop : dTop = matMulRect n n n (paddedEconomyP11 P) Rhat)
    (hRright : matMul n Rhat Rinv = idMatrix n)
    (hdTop : rectOpNorm2Le dTop eta)
    (hRinv : rectOpNorm2Le Rinv rho)
    (heta : 0 <= eta)
    (hrho : 0 <= rho) :
    opNorm2Le (orthogonalityResidual (paddedEconomyQ P))
      ((eta * rho) ^ 2) := by
  exact
    LeanFpAnalysis.FP.mgsPaddedEconomyQ_orthogonalityResidual_opNorm2Le_of_top_product_right_inverse
      hP htop hRright hdTop hRinv heta hrho

/-- Source-facing pre-repair Gram-residual bound driven by the stacked
`(19.34)` perturbation bound, the top block equation, and a bounded right
inverse for `R11`. -/
theorem paddedEconomyQ_orthogonalityResidual_opNorm2Le_of_stacked_bound_top_product_right_inverse
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    {P : Fin (n + m) -> Fin (n + m) -> Real}
    {dTop : Fin n -> Fin n -> Real} {dBottom : Fin m -> Fin n -> Real}
    {Rhat Rinv : Fin n -> Fin n -> Real} {c eta rho : Real}
    (hP : IsOrthogonal (n + m) P)
    (htop : dTop = matMulRect n n n (paddedEconomyP11 P) Rhat)
    (hRright : matMul n Rhat Rinv = idMatrix n)
    (hc : 0 <= c)
    (hbound : stackedPerturbationColumnwiseBound A dTop dBottom c)
    (hresidual : c * frobNormRect A <= eta)
    (hRinv : rectOpNorm2Le Rinv rho)
    (heta : 0 <= eta)
    (hrho : 0 <= rho) :
    opNorm2Le (orthogonalityResidual (paddedEconomyQ P))
      ((eta * rho) ^ 2) := by
  exact
    LeanFpAnalysis.FP.mgsPaddedEconomyQ_orthogonalityResidual_opNorm2Le_of_stacked_bound_top_product_right_inverse
      A hP htop hRright hc hbound hresidual hRinv heta hrho

/-- Concrete pre-repair Gram-residual bound for the padded Householder-MGS
handoff.  The remaining source-facing numerical input is a bounded right
inverse for the extracted `R11` block. -/
theorem householder_paddedFinInput_pre_repair_gram_bound_of_right_inverse_budget
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)))
    {Rinv : Fin n -> Fin n -> Real} {eta rho : Real}
    (hRright :
      matMul n
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
        Rinv = idMatrix n)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta)
    (hRinv : rectOpNorm2Le Rinv rho)
    (heta : 0 <= eta)
    (hrho : 0 <= rho) :
    opNorm2Le
      (orthogonalityResidual
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A))))
      ((eta * rho) ^ 2) := by
  let Q : Fin (n + m) -> Fin (n + m) -> Real :=
    fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)
  let Rhat : Fin (n + m) -> Fin n -> Real :=
    fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)
  have hfull := householder_paddedFinInput_full_block_data fp A hn hvalid
  cases hfull with
  | intro dTop htopExists =>
      cases htopExists with
      | intro dBottom hblock =>
          dsimp only at hblock
          exact
            paddedEconomyQ_orthogonalityResidual_opNorm2Le_of_stacked_bound_top_product_right_inverse
              A hblock.2.2.1 hblock.1 hRright
              (Theorem19_4.gamma_tilde_nonneg fp hvalid)
              hblock.2.2.2.2.2 hresidual hRinv heta hrho

/-- The concrete padded Householder handoff supplies the upper-trapezoidal
shape of the extracted `R11` block, so a pointwise nonzero diagonal gives the
determinant-nonzero certificate needed by the repository inverse API. -/
theorem householder_paddedFinInput_R11_det_ne_zero_of_diag_ne_zero
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)))
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0) :
    Ne
      (Matrix.det
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
          Matrix (Fin n) (Fin n) Real))
      0 := by
  let R11 : Fin n -> Fin n -> Real :=
    paddedEconomyR
      (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
  have hfull := householder_paddedFinInput_full_block_data fp A hn hvalid
  cases hfull with
  | intro dTop htopExists =>
      cases htopExists with
      | intro dBottom hblock =>
          dsimp only at hblock
          have hupper : IsUpperTrapezoidal n n R11 := hblock.2.2.2.1
          have hdiagR : forall i : Fin n, Ne (R11 i i) 0 := by
            intro i
            simpa [R11] using hdiag i
          have hdetR :
              Ne (Matrix.det (R11 : Matrix (Fin n) (Fin n) Real)) 0 :=
            det_ne_zero_of_upper_triangular_diag_ne_zero n R11 hupper hdiagR
          simpa [R11] using hdetR

/-- Determinant-nonzero form of the `R11` right-inverse equation for the
repository `nonsingInv`. -/
theorem householder_paddedFinInput_R11_nonsingInv_right_inverse_of_det_ne_zero
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hdet :
      Ne
        (Matrix.det
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
            Matrix (Fin n) (Fin n) Real))
        0) :
    matMul n
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (nonsingInv n
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))) =
      idMatrix n := by
  let R11 : Fin n -> Fin n -> Real :=
    paddedEconomyR
      (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
  have hdetR : Ne (Matrix.det (R11 : Matrix (Fin n) (Fin n) Real)) 0 := by
    simpa [R11] using hdet
  have hrightPred : IsRightInverse n R11 (nonsingInv n R11) :=
    (isInverse_nonsingInv_of_det_ne_zero n R11 hdetR).2
  change matMul n R11 (nonsingInv n R11) = idMatrix n
  ext i j
  exact hrightPred i j

/-- Diagonal-nonzero form of the `R11` right-inverse equation for the
repository `nonsingInv`. -/
theorem householder_paddedFinInput_R11_nonsingInv_right_inverse_of_diag_ne_zero
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)))
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0) :
    matMul n
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (nonsingInv n
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))) =
      idMatrix n := by
  have hdet :=
    householder_paddedFinInput_R11_det_ne_zero_of_diag_ne_zero
      fp A hn hvalid hdiag
  exact
    householder_paddedFinInput_R11_nonsingInv_right_inverse_of_det_ne_zero
      fp A hdet

/-- Determinant-specialized form of the concrete pre-repair Gram-residual
bound.  A nonzero determinant for the extracted `R11` block supplies the
repository `nonsingInv` right-inverse equation; the remaining condition
estimate is the operator-norm budget for that inverse. -/
theorem householder_paddedFinInput_pre_repair_gram_bound_of_det_ne_zero_inverse_budget
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)))
    {eta rho : Real}
    (hdet :
      Ne
        (Matrix.det
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
            Matrix (Fin n) (Fin n) Real))
        0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (heta : 0 <= eta)
    (hrho : 0 <= rho) :
    opNorm2Le
      (orthogonalityResidual
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A))))
      ((eta * rho) ^ 2) := by
  have hRright :=
    householder_paddedFinInput_R11_nonsingInv_right_inverse_of_det_ne_zero
      fp A hdet
  exact
    householder_paddedFinInput_pre_repair_gram_bound_of_right_inverse_budget
      fp A hn hvalid hRright hresidual hRinv heta hrho

/-- Diagonal-nonzero form of the concrete pre-repair Gram-residual bound.
The full block-data theorem supplies the upper-trapezoidal shape of the
extracted `R11`; a nonzero diagonal then supplies the determinant hypothesis
for the repository `nonsingInv` route. -/
theorem householder_paddedFinInput_pre_repair_gram_bound_of_upper_diag_inverse_budget
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)))
    {eta rho : Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (heta : 0 <= eta)
    (hrho : 0 <= rho) :
    opNorm2Le
      (orthogonalityResidual
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A))))
      ((eta * rho) ^ 2) := by
  have hdet :=
    householder_paddedFinInput_R11_det_ne_zero_of_diag_ne_zero
      fp A hn hvalid hdiag
  exact
    householder_paddedFinInput_pre_repair_gram_bound_of_det_ne_zero_inverse_budget
      fp A hn hvalid hdet hresidual hRinv heta hrho

/-- The concrete padded Householder handoff supplies the upper-trapezoidal
shape of the extracted `R11` block, so a determinant-nonzero certificate is
enough to recover the pointwise nonzero-diagonal hypothesis used by the
upper-diagonal source-output wrappers. -/
theorem householder_paddedFinInput_R11_diag_ne_zero_of_det_ne_zero
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)))
    (hdet :
      Ne
        (Matrix.det
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
            Matrix (Fin n) (Fin n) Real))
        0) :
    forall i : Fin n,
      Ne
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
          i i)
        0 := by
  let R11 : Fin n -> Fin n -> Real :=
    paddedEconomyR
      (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
  have hdetR : Ne (Matrix.det (R11 : Matrix (Fin n) (Fin n) Real)) 0 := by
    simpa [R11] using hdet
  have hfull := householder_paddedFinInput_full_block_data fp A hn hvalid
  cases hfull with
  | intro dTop htopExists =>
      cases htopExists with
      | intro dBottom hblock =>
          dsimp only at hblock
          have hupper : IsUpperTrapezoidal n n R11 := hblock.2.2.2.1
          have hdiag : forall i : Fin n, Ne (R11 i i) 0 :=
            diag_ne_zero_of_upper_triangular_det_ne_zero n R11 hupper hdetR
          intro i
          simpa [R11] using hdiag i

/-- The concrete padded Householder `R11` block is upper triangular, so its
determinant-nonzero and pointwise nonzero-diagonal nonbreakdown surfaces are
equivalent. -/
theorem householder_paddedFinInput_R11_det_ne_zero_iff_diag_ne_zero
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m))) :
    Ne
      (Matrix.det
        (householder_paddedFinInput_R11 fp A :
          Matrix (Fin n) (Fin n) Real))
      0 <->
      forall i : Fin n,
        Ne (householder_paddedFinInput_R11 fp A i i) 0 := by
  constructor
  · intro hdet i
    have hdet_expanded :
        Ne
          (Matrix.det
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
              Matrix (Fin n) (Fin n) Real))
          0 := by
      simpa [householder_paddedFinInput_R11] using hdet
    simpa [householder_paddedFinInput_R11] using
      householder_paddedFinInput_R11_diag_ne_zero_of_det_ne_zero
        fp A hn hvalid hdet_expanded i
  · intro hdiag
    have hdiag_expanded :
        forall i : Fin n,
          Ne
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
              i i)
            0 := by
      intro i
      simpa [householder_paddedFinInput_R11] using hdiag i
    have hdet_expanded :
        Ne
          (Matrix.det
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
              Matrix (Fin n) (Fin n) Real))
          0 :=
      householder_paddedFinInput_R11_det_ne_zero_of_diag_ne_zero
        fp A hn hvalid hdiag_expanded
    simpa [householder_paddedFinInput_R11] using hdet_expanded

/-- Determinant-nonzero form of
`householder_paddedFinInput_R11_diag_ne_zero_of_storedTrailingPanel_final_prevBlocks_uniform_step_budget`.

The stored-loop route proves pointwise nonzero diagonal entries for the
concrete padded Householder `R11`; the already-checked upper-trapezoidal
Householder block data converts this to the determinant certificate consumed by
the condition-budget MGS route. -/
theorem
    householder_paddedFinInput_R11_det_ne_zero_of_storedTrailingPanel_final_prevBlocks_uniform_step_budget
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hrows : n <= n + m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    (A_hat : Nat -> Fin (n + m) -> Fin n -> Real)
    (b_hat : Nat -> Fin (n + m) -> Real)
    (alpha : Nat -> Real)
    (cStep : Real)
    (hm : gammaValid fp (n + m))
    (hStep : forall k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (n + m) n k
          (householderTrailingActiveVector (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (n + m)
            (householderTrailingActiveVector (n + m)
              (Fin.mk k (lt_of_lt_of_le hk hrows))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (halpha : forall k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq (n + m)
          (Fin.mk k (lt_of_lt_of_le hk hrows))
          (fun i => A_hat k i (Fin.mk k hk)))
    (hdetPrevFinal : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat n)
            (le_trans (Nat.le_of_lt hk) hrows) hk :
            Matrix (Fin k) (Fin k) Real))
        0)
    (hdetLead : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrLeadingBlock (A_hat k)
            (le_trans (Nat.succ_le_of_lt hk) hrows) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) Real))
        0)
    (hsign : forall k (hk : k < n),
      alpha k *
          A_hat k (Fin.mk k (lt_of_lt_of_le hk hrows)) (Fin.mk k hk) <= 0)
    (hStepBudget : forall k : Fin n,
      storedQRCompactStepRelativeBudget hrows fp A_hat b_hat alpha k <= cStep)
    (huniformBudget : forall k (hk : k < n),
      ((n : Real) * cStep) *
          vecNorm2 (fun i : Fin (n + m) => A_hat k i (Fin.mk k hk)) <
        Real.sqrt
          (householderTrailingNorm2Sq (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun i => A_hat k i (Fin.mk k hk))))
    (hR11 : forall i j,
      householder_paddedFinInput_R11 fp A i j =
        A_hat n (Fin.mk i.val (lt_of_lt_of_le i.isLt hrows)) j) :
    Ne
      (Matrix.det
        (householder_paddedFinInput_R11 fp A :
          Matrix (Fin n) (Fin n) Real))
      0 := by
  have hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)) := by
    unfold gammaValid
    have hhalf_lt_one : (1 / 2 : Real) < 1 := by norm_num
    exact lt_of_le_of_lt hsmall hhalf_lt_one
  have hdiag :
      forall i : Fin n,
        Ne (householder_paddedFinInput_R11 fp A i i) 0 :=
    householder_paddedFinInput_R11_diag_ne_zero_of_storedTrailingPanel_final_prevBlocks_uniform_step_budget
      (fp := fp) (m := m) (n := n) A hrows A_hat b_hat alpha cStep
      hm hStep halpha hdetPrevFinal hdetLead hsign hStepBudget
      huniformBudget hR11
  exact
    (householder_paddedFinInput_R11_det_ne_zero_iff_diag_ne_zero
      fp A hn hvalid).2 hdiag

/-- Final-panel equality version of
`householder_paddedFinInput_R11_det_ne_zero_of_storedTrailingPanel_final_prevBlocks_uniform_step_budget`.

The full recursive/stored final-panel equality supplies the top-block `R11`
identification internally before converting diagonal nonbreakdown to determinant
nonbreakdown. -/
theorem
    householder_paddedFinInput_R11_det_ne_zero_of_storedTrailingPanel_final_panel_eq_final_prevBlocks_uniform_step_budget
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hrows : n <= n + m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    (A_hat : Nat -> Fin (n + m) -> Fin n -> Real)
    (b_hat : Nat -> Fin (n + m) -> Real)
    (alpha : Nat -> Real)
    (cStep : Real)
    (hm : gammaValid fp (n + m))
    (hStep : forall k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (n + m) n k
          (householderTrailingActiveVector (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (n + m)
            (householderTrailingActiveVector (n + m)
              (Fin.mk k (lt_of_lt_of_le hk hrows))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (halpha : forall k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq (n + m)
          (Fin.mk k (lt_of_lt_of_le hk hrows))
          (fun i => A_hat k i (Fin.mk k hk)))
    (hdetPrevFinal : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat n)
            (le_trans (Nat.le_of_lt hk) hrows) hk :
            Matrix (Fin k) (Fin k) Real))
        0)
    (hdetLead : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrLeadingBlock (A_hat k)
            (le_trans (Nat.succ_le_of_lt hk) hrows) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) Real))
        0)
    (hsign : forall k (hk : k < n),
      alpha k *
          A_hat k (Fin.mk k (lt_of_lt_of_le hk hrows)) (Fin.mk k hk) <= 0)
    (hStepBudget : forall k : Fin n,
      storedQRCompactStepRelativeBudget hrows fp A_hat b_hat alpha k <= cStep)
    (huniformBudget : forall k (hk : k < n),
      ((n : Real) * cStep) *
          vecNorm2 (fun i : Fin (n + m) => A_hat k i (Fin.mk k hk)) <
        Real.sqrt
          (householderTrailingNorm2Sq (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun i => A_hat k i (Fin.mk k hk))))
    (hFinal :
      A_hat n = fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
    Ne
      (Matrix.det
        (householder_paddedFinInput_R11 fp A :
          Matrix (Fin n) (Fin n) Real))
      0 :=
  householder_paddedFinInput_R11_det_ne_zero_of_storedTrailingPanel_final_prevBlocks_uniform_step_budget
    (fp := fp) (m := m) (n := n) A hn hrows hsmall
    A_hat b_hat alpha cStep hm hStep halpha hdetPrevFinal hdetLead
    hsign hStepBudget huniformBudget
    (householder_paddedFinInput_R11_eq_top_block_of_final_panel_eq
      fp A hrows A_hat hFinal)

/-- Fallback rectangular operator certificate for the repository inverse.

Source condition-number estimates should eventually provide a sharper budget
for `nonsingInv R11`; this wrapper records the always-available Frobenius
upper bound in the rectangular norm predicate used by the QR route. -/
theorem rectOpNorm2Le_nonsingInv_frobNorm {n : Nat}
    (R : Fin n -> Fin n -> Real) :
    rectOpNorm2Le (nonsingInv n R) (frobNorm (nonsingInv n R)) := by
  exact
    LeanFpAnalysis.FP.rectOpNorm2Le_of_opNorm2Le_square
      (nonsingInv n R)
      (LeanFpAnalysis.FP.opNorm2Le_of_frobNorm_self (nonsingInv n R))

/-- Concrete source-output assembly for the Theorem 19.13 route after the
Problem 19.12-style repair step is supplied.

The local Householder-MGS handoff provides `A + Delta A4 = Q21 * R11`, the
upper-diagonal hypothesis provides the `nonsingInv R11` right inverse, and the
repair certificate supplies the nearby orthonormal common-`R` factorization
that remains open in the source proof route. -/
theorem qrsensitivitySourceOutput_of_householder_upper_diag_repair
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)))
    {eta1 eta2 rho c2 c3 u kappaA higherOrder : Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hrepair :
      opNorm2Le
        (orthogonalityResidual
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A))))
        ((eta1 * rho) ^ 2) ->
      Exists fun Q : Fin m -> Fin n -> Real =>
      Exists fun dA2 : Fin m -> Fin n -> Real =>
        GramSchmidtOrthonormalColumns Q /\
        (fun i j => A i j + dA2 i j) =
          matMulRect m n n Q
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) /\
        rectOpNorm2Le dA2 eta2 /\
        (forall j, columnFrob dA2 j <= c3 * u * columnFrob A j))
    (heta1 : 0 <= eta1)
    (heta12 : 0 <= eta1 + eta2)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + eta2) * rho) + ((eta1 + eta2) * rho) ^ 2 <=
        c2 * u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2 c3 u kappaA higherOrder := by
  let R11 : Fin n -> Fin n -> Real :=
    paddedEconomyR
      (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
  have hpre :
      opNorm2Le
        (orthogonalityResidual
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A))))
        ((eta1 * rho) ^ 2) :=
    householder_paddedFinInput_pre_repair_gram_bound_of_upper_diag_inverse_budget
      fp A hn hvalid hdiag hresidual hRinv heta1 hrho
  have hfull := householder_paddedFinInput_full_block_data fp A hn hvalid
  cases hfull with
  | intro dTop htopExists =>
      cases htopExists with
      | intro dBottom hblock =>
          dsimp only at hblock
          have hRright : matMul n R11 (nonsingInv n R11) = idMatrix n := by
            simpa [R11] using
              householder_paddedFinInput_R11_nonsingInv_right_inverse_of_diag_ne_zero
                fp A hn hvalid hdiag
          have hdA1 : rectOpNorm2Le dBottom eta1 :=
            bottomPerturbation_rectOpNorm2Le_of_stackedColumnwiseBound
              A dTop dBottom (Theorem19_4.gamma_tilde_nonneg fp hvalid)
              hblock.2.2.2.2.2 hresidual
          cases hrepair hpre with
          | intro Q hQExists =>
              cases hQExists with
              | intro dA2 hrep =>
                  exact
                    qrsensitivitySourceOutput_of_commonR_bounds
                      hblock.2.1 hrep.2.1 hrep.1 hRright
                      hdA1 hrep.2.2.1 hRinv heta12 hrho hbudget
                      hrep.2.2.2

/-- Concrete source-output assembly for the Theorem 19.13 route when Problem
19.12 supplies pure correction-map data.

This is the data-first version of
`qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair`: the
future CS/polar theorem only has to produce `Problem1912CorrectionMapData` for
the actual `(P11, P21)` blocks, and the common-`R` transport is handled here. -/
theorem qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)))
    {eta1 eta2 rho c2 c3 u kappaA higherOrder : Real}
    {Qrepair F : Fin m -> Fin n -> Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hdata :
      Problem1912CorrectionMapData m n
        (paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        Qrepair F)
    (hnorm :
      forall (dTop : Fin n -> Fin n -> Real)
          (dBottom : Fin m -> Fin n -> Real),
        dTop =
          matMul n
            (paddedEconomyP11
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        (fun i j => A i j + dBottom i j) =
          matMulRect m n n
            (paddedEconomyQ
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        rectOpNorm2Le
          (fun i j => matMulRect m n n F dTop i j + dBottom i j)
          eta2)
    (hcol :
      forall (dTop : Fin n -> Fin n -> Real)
          (dBottom : Fin m -> Fin n -> Real),
        dTop =
          matMul n
            (paddedEconomyP11
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        (fun i j => A i j + dBottom i j) =
          matMulRect m n n
            (paddedEconomyQ
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        forall j,
          columnFrob
              (fun i j => matMulRect m n n F dTop i j + dBottom i j)
              j <=
            c3 * u * columnFrob A j)
    (heta12 : 0 <= eta1 + eta2)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + eta2) * rho) + ((eta1 + eta2) * rho) ^ 2 <=
        c2 * u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2 c3 u kappaA higherOrder := by
  let R11 : Fin n -> Fin n -> Real :=
    paddedEconomyR
      (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
  have hfull := householder_paddedFinInput_full_block_data fp A hn hvalid
  cases hfull with
  | intro dTop htopExists =>
      cases htopExists with
      | intro dBottom hblock =>
          dsimp only at hblock
          have hRright : matMul n R11 (nonsingInv n R11) = idMatrix n := by
            simpa [R11] using
              householder_paddedFinInput_R11_nonsingInv_right_inverse_of_diag_ne_zero
                fp A hn hvalid hdiag
          have hdA1 : rectOpNorm2Le dBottom eta1 :=
            bottomPerturbation_rectOpNorm2Le_of_stackedColumnwiseBound
              A dTop dBottom (Theorem19_4.gamma_tilde_nonneg fp hvalid)
              hblock.2.2.2.2.2 hresidual
          have hdTop :
              dTop =
                matMul n
                  (paddedEconomyP11
                    (fl_householderQRPanel_Q fp (n + m) n
                      (paddedFinInput A)))
                  R11 := by
            simpa [R11, matMulRect, matMul] using hblock.1
          have hrepair :
              Exists fun Q : Fin m -> Fin n -> Real =>
              Exists fun dA2 : Fin m -> Fin n -> Real =>
                GramSchmidtOrthonormalColumns Q /\
                (fun i j => A i j + dA2 i j) =
                  matMulRect m n n Q R11 /\
                rectOpNorm2Le dA2 eta2 /\
                (forall j, columnFrob dA2 j <=
                  c3 * u * columnFrob A j) :=
            problem1912_repair_of_correctionMapData
              hblock.2.1 hdTop hdata
              (hnorm dTop dBottom hdTop hblock.2.1)
              (hcol dTop dBottom hdTop hblock.2.1)
          cases hrepair with
          | intro Q hQExists =>
              cases hQExists with
              | intro dA2 hrep =>
                  exact
                    qrsensitivitySourceOutput_of_commonR_bounds
                      hblock.2.1 hrep.2.1 hrep.1 hRright
                      hdA1 hrep.2.2.1 hRinv heta12 hrho hbudget
                      hrep.2.2.2

/-- Data-first source-output assembly where the repaired perturbation budgets
are derived from separate top and bottom perturbation budgets. -/
theorem qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_perturbation_bounds
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)))
    {eta1 etaTop etaBottom eta2 rho c2 c3 u kappaA higherOrder : Real}
    {Qrepair F : Fin m -> Fin n -> Real}
    {topBudget bottomBudget : Fin n -> Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hdata :
      Problem1912CorrectionMapData m n
        (paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        Qrepair F)
    (hTop :
      forall dTop : Fin n -> Fin n -> Real,
        dTop =
          matMul n
            (paddedEconomyP11
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        rectOpNorm2Le dTop etaTop)
    (hBottom :
      forall dBottom : Fin m -> Fin n -> Real,
        (fun i j => A i j + dBottom i j) =
          matMulRect m n n
            (paddedEconomyQ
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        rectOpNorm2Le dBottom etaBottom)
    (hNormBudget : 1 * etaTop + etaBottom <= eta2)
    (hTopCol :
      forall dTop : Fin n -> Fin n -> Real,
        dTop =
          matMul n
            (paddedEconomyP11
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        forall j, columnFrob dTop j <= topBudget j)
    (hBottomCol :
      forall dBottom : Fin m -> Fin n -> Real,
        (fun i j => A i j + dBottom i j) =
          matMulRect m n n
            (paddedEconomyQ
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        forall j, columnFrob dBottom j <= bottomBudget j)
    (hColBudget :
      forall j, 1 * topBudget j + bottomBudget j <=
        c3 * u * columnFrob A j)
    (heta12 : 0 <= eta1 + eta2)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + eta2) * rho) + ((eta1 + eta2) * rho) ^ 2 <=
        c2 * u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2 c3 u kappaA higherOrder := by
  refine
    qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair
      fp A hn hvalid hdiag hresidual hRinv hdata ?_ ?_
      heta12 hrho hbudget
  next =>
    intro dTop dBottom hdTop hbottom
    exact
      rectOpNorm2Le_mono hNormBudget
        (problem1912_repairedPerturbation_rectOpNorm2Le_of_bounds
          (by norm_num : (0 : Real) <= 1) hdata.map_bound
          (hTop dTop hdTop) (hBottom dBottom hbottom))
  next =>
    intro dTop dBottom hdTop hbottom
    exact
      problem1912_repairedPerturbation_columnFrob_le_of_column_budget
        (A := A) (F := F) (dBottom := dBottom) (dTop := dTop)
        (by norm_num : (0 : Real) <= 1) hdata.map_bound
        (hTopCol dTop hdTop) (hBottomCol dBottom hbottom)
        hColBudget

/-- Data-first source-output assembly driven directly by a stacked columnwise
perturbation budget for `[Delta A_top; Delta A_bottom]`. -/
theorem qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_stacked_budget
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)))
    {eta1 etaTop etaBottom eta2 rho c2 c3 u kappaA higherOrder
        cStack : Real}
    {Qrepair F : Fin m -> Fin n -> Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hdata :
      Problem1912CorrectionMapData m n
        (paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        Qrepair F)
    (hstack :
      forall (dTop : Fin n -> Fin n -> Real)
          (dBottom : Fin m -> Fin n -> Real),
        dTop =
          matMul n
            (paddedEconomyP11
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        (fun i j => A i j + dBottom i j) =
          matMulRect m n n
            (paddedEconomyQ
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        stackedPerturbationColumnwiseBound A dTop dBottom cStack)
    (hcStack : 0 <= cStack)
    (hTopResidual : cStack * frobNormRect A <= etaTop)
    (hBottomResidual : cStack * frobNormRect A <= etaBottom)
    (hNormBudget : 1 * etaTop + etaBottom <= eta2)
    (hColBudget :
      forall j,
        1 * (cStack * columnFrob A j) +
            (cStack * columnFrob A j) <=
          c3 * u * columnFrob A j)
    (heta12 : 0 <= eta1 + eta2)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + eta2) * rho) + ((eta1 + eta2) * rho) ^ 2 <=
        c2 * u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2 c3 u kappaA higherOrder := by
  refine
    qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair
      fp A hn hvalid hdiag hresidual hRinv hdata ?_ ?_
      heta12 hrho hbudget
  next =>
    intro dTop dBottom hdTop hbottom
    have hstackLocal :
        stackedPerturbationColumnwiseBound A dTop dBottom cStack :=
      hstack dTop dBottom hdTop hbottom
    have hTop : rectOpNorm2Le dTop etaTop :=
      topPerturbation_rectOpNorm2Le_of_stackedColumnwiseBound
        A dTop dBottom hcStack hstackLocal hTopResidual
    have hBottom : rectOpNorm2Le dBottom etaBottom :=
      bottomPerturbation_rectOpNorm2Le_of_stackedColumnwiseBound
        A dTop dBottom hcStack hstackLocal hBottomResidual
    exact
      rectOpNorm2Le_mono hNormBudget
        (problem1912_repairedPerturbation_rectOpNorm2Le_of_bounds
          (by norm_num : (0 : Real) <= 1) hdata.map_bound
          hTop hBottom)
  next =>
    intro dTop dBottom hdTop hbottom
    have hstackLocal :
        stackedPerturbationColumnwiseBound A dTop dBottom cStack :=
      hstack dTop dBottom hdTop hbottom
    exact
      problem1912_repairedPerturbation_columnFrob_le_of_column_budget
        (A := A) (F := F) (dBottom := dBottom) (dTop := dTop)
        (topBudget := fun j => cStack * columnFrob A j)
        (bottomBudget := fun j => cStack * columnFrob A j)
        (by norm_num : (0 : Real) <= 1) hdata.map_bound
        (topPerturbation_columnFrob_le_of_stackedColumnwiseBound
          A dTop dBottom hstackLocal)
        (bottomPerturbation_columnFrob_le_of_stackedColumnwiseBound
          A dTop dBottom hstackLocal)
        hColBudget

/-- Data-first source-output assembly using the actual stacked perturbation
bound returned by the padded Householder handoff. -/
theorem qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_budget
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)))
    {eta1 etaTop etaBottom eta2 rho c2 c3 u kappaA higherOrder : Real}
    {Qrepair F : Fin m -> Fin n -> Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hdata :
      Problem1912CorrectionMapData m n
        (paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        Qrepair F)
    (hTopResidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= etaTop)
    (hBottomResidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= etaBottom)
    (hNormBudget : 1 * etaTop + etaBottom <= eta2)
    (hColBudget :
      forall j,
        1 * (Theorem19_4.gamma_tilde fp (n + m) n * columnFrob A j) +
            (Theorem19_4.gamma_tilde fp (n + m) n * columnFrob A j) <=
          c3 * u * columnFrob A j)
    (heta12 : 0 <= eta1 + eta2)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + eta2) * rho) + ((eta1 + eta2) * rho) ^ 2 <=
        c2 * u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2 c3 u kappaA higherOrder := by
  let R11 : Fin n -> Fin n -> Real :=
    paddedEconomyR
      (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
  have hfull := householder_paddedFinInput_full_block_data fp A hn hvalid
  cases hfull with
  | intro dTop htopExists =>
      cases htopExists with
      | intro dBottom hblock =>
          dsimp only at hblock
          have hRright : matMul n R11 (nonsingInv n R11) = idMatrix n := by
            simpa [R11] using
              householder_paddedFinInput_R11_nonsingInv_right_inverse_of_diag_ne_zero
                fp A hn hvalid hdiag
          have hdA1 : rectOpNorm2Le dBottom eta1 :=
            bottomPerturbation_rectOpNorm2Le_of_stackedColumnwiseBound
              A dTop dBottom (Theorem19_4.gamma_tilde_nonneg fp hvalid)
              hblock.2.2.2.2.2 hresidual
          have hdTop :
              dTop =
                matMul n
                  (paddedEconomyP11
                    (fl_householderQRPanel_Q fp (n + m) n
                      (paddedFinInput A)))
                  R11 := by
            simpa [R11, matMulRect, matMul] using hblock.1
          have hTop : rectOpNorm2Le dTop etaTop :=
            topPerturbation_rectOpNorm2Le_of_stackedColumnwiseBound
              A dTop dBottom (Theorem19_4.gamma_tilde_nonneg fp hvalid)
              hblock.2.2.2.2.2 hTopResidual
          have hBottom : rectOpNorm2Le dBottom etaBottom :=
            bottomPerturbation_rectOpNorm2Le_of_stackedColumnwiseBound
              A dTop dBottom (Theorem19_4.gamma_tilde_nonneg fp hvalid)
              hblock.2.2.2.2.2 hBottomResidual
          have hTopCol :
              forall j,
                columnFrob dTop j <=
                  Theorem19_4.gamma_tilde fp (n + m) n *
                    columnFrob A j :=
            topPerturbation_columnFrob_le_of_stackedColumnwiseBound
              A dTop dBottom hblock.2.2.2.2.2
          have hBottomCol :
              forall j,
                columnFrob dBottom j <=
                  Theorem19_4.gamma_tilde fp (n + m) n *
                    columnFrob A j :=
            bottomPerturbation_columnFrob_le_of_stackedColumnwiseBound
              A dTop dBottom hblock.2.2.2.2.2
          have hrepair :
              Exists fun Q : Fin m -> Fin n -> Real =>
              Exists fun dA2 : Fin m -> Fin n -> Real =>
                GramSchmidtOrthonormalColumns Q /\
                (fun i j => A i j + dA2 i j) =
                  matMulRect m n n Q R11 /\
                rectOpNorm2Le dA2 eta2 /\
                (forall j, columnFrob dA2 j <=
                  c3 * u * columnFrob A j) :=
            problem1912_repair_of_correctionMapData_of_perturbation_bounds
              hblock.2.1 hdTop hdata hTop hBottom hNormBudget
              hTopCol hBottomCol hColBudget
          cases hrepair with
          | intro Q hQExists =>
              cases hQExists with
              | intro dA2 hrep =>
                  exact
                    qrsensitivitySourceOutput_of_commonR_bounds
                      hblock.2.1 hrep.2.1 hrep.1 hRright
                      hdA1 hrep.2.2.1 hRinv heta12 hrho hbudget
                      hrep.2.2.2

/-- Concrete source-output assembly for the Theorem 19.13 route when the
Problem 19.12 repair step is supplied by diagonal CS data.

This removes the abstract repair-certificate input from
`qrsensitivitySourceOutput_of_householder_upper_diag_repair`: the local
Householder handoff provides the actual `P11`, `P21`, and `R11` blocks, and
the diagonal CS hypotheses provide the correction map used to repair the
common-`R` factorization. -/
theorem qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)))
    {eta1 eta2 rho c2 c3 u kappaA higherOrder : Real}
    {U C S T W : Fin n -> Fin n -> Real}
    {V Qcs F : Fin m -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hP11 :
      paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMul n U (matMul n C (finiteTranspose W)))
    (hP21 :
      paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQcs : Qcs = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1)
    (hnorm :
      forall (dTop : Fin n -> Fin n -> Real)
          (dBottom : Fin m -> Fin n -> Real),
        dTop =
          matMul n
            (paddedEconomyP11
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        (fun i j => A i j + dBottom i j) =
          matMulRect m n n
            (paddedEconomyQ
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        rectOpNorm2Le
          (fun i j => matMulRect m n n F dTop i j + dBottom i j)
          eta2)
    (hcol :
      forall (dTop : Fin n -> Fin n -> Real)
          (dBottom : Fin m -> Fin n -> Real),
        dTop =
          matMul n
            (paddedEconomyP11
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        (fun i j => A i j + dBottom i j) =
          matMulRect m n n
            (paddedEconomyQ
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        forall j,
          columnFrob
              (fun i j => matMulRect m n n F dTop i j + dBottom i j)
              j <=
            c3 * u * columnFrob A j)
    (heta12 : 0 <= eta1 + eta2)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + eta2) * rho) + ((eta1 + eta2) * rho) ^ 2 <=
        c2 * u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2 c3 u kappaA higherOrder := by
  let R11 : Fin n -> Fin n -> Real :=
    paddedEconomyR
      (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
  have hfull := householder_paddedFinInput_full_block_data fp A hn hvalid
  cases hfull with
  | intro dTop htopExists =>
      cases htopExists with
      | intro dBottom hblock =>
          dsimp only at hblock
          have hRright : matMul n R11 (nonsingInv n R11) = idMatrix n := by
            simpa [R11] using
              householder_paddedFinInput_R11_nonsingInv_right_inverse_of_diag_ne_zero
                fp A hn hvalid hdiag
          have hdA1 : rectOpNorm2Le dBottom eta1 :=
            bottomPerturbation_rectOpNorm2Le_of_stackedColumnwiseBound
              A dTop dBottom (Theorem19_4.gamma_tilde_nonneg fp hvalid)
              hblock.2.2.2.2.2 hresidual
          have hdTop :
              dTop =
                matMul n
                  (paddedEconomyP11
                    (fl_householderQRPanel_Q fp (n + m) n
                      (paddedFinInput A)))
                  R11 := by
            simpa [R11, matMulRect, matMul] using hblock.1
          have hrepair :
              Exists fun Q : Fin m -> Fin n -> Real =>
              Exists fun dA2 : Fin m -> Fin n -> Real =>
                GramSchmidtOrthonormalColumns Q /\
                (fun i j => A i j + dA2 i j) =
                  matMulRect m n n Q R11 /\
                rectOpNorm2Le dA2 eta2 /\
                (forall j, columnFrob dA2 j <=
                  c3 * u * columnFrob A j) :=
            problem1912_repair_of_csDiagonalAlgebra
              hblock.2.1 hdTop hP11 hP21 hQcs hF hUorth hWorth hVorth
              hCdiag hSdiag hTdiag hs hcs
              (hnorm dTop dBottom hdTop hblock.2.1)
              (hcol dTop dBottom hdTop hblock.2.1)
          cases hrepair with
          | intro Q hQExists =>
              cases hQExists with
          | intro dA2 hrep =>
                  exact
                    qrsensitivitySourceOutput_of_commonR_bounds
                      hblock.2.1 hrep.2.1 hrep.1 hRright
                      hdA1 hrep.2.2.1 hRinv heta12 hrho hbudget
                      hrep.2.2.2

/-- Concrete diagonal-CS source-output assembly where the repaired
perturbation budgets are derived from separate top and bottom perturbation
budgets.

Compared with
`qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair`, this
removes the direct `F * DeltaA_top + DeltaA_bottom` norm and column hypotheses:
the caller supplies bounds for the top perturbation, the bottom perturbation,
and scalar budget inequalities that combine them. -/
theorem qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_perturbation_bounds
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)))
    {eta1 etaTop etaBottom eta2 rho c2 c3 u kappaA higherOrder : Real}
    {U C S T W : Fin n -> Fin n -> Real}
    {V Qcs F : Fin m -> Fin n -> Real}
    {c s : Fin n -> Real}
    {topBudget bottomBudget : Fin n -> Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hP11 :
      paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMul n U (matMul n C (finiteTranspose W)))
    (hP21 :
      paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQcs : Qcs = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1)
    (hTop :
      forall dTop : Fin n -> Fin n -> Real,
        dTop =
          matMul n
            (paddedEconomyP11
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        rectOpNorm2Le dTop etaTop)
    (hBottom :
      forall dBottom : Fin m -> Fin n -> Real,
        (fun i j => A i j + dBottom i j) =
          matMulRect m n n
            (paddedEconomyQ
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        rectOpNorm2Le dBottom etaBottom)
    (hNormBudget : 1 * etaTop + etaBottom <= eta2)
    (hTopCol :
      forall dTop : Fin n -> Fin n -> Real,
        dTop =
          matMul n
            (paddedEconomyP11
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        forall j, columnFrob dTop j <= topBudget j)
    (hBottomCol :
      forall dBottom : Fin m -> Fin n -> Real,
        (fun i j => A i j + dBottom i j) =
          matMulRect m n n
            (paddedEconomyQ
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        forall j, columnFrob dBottom j <= bottomBudget j)
    (hColBudget :
      forall j, 1 * topBudget j + bottomBudget j <=
        c3 * u * columnFrob A j)
    (heta12 : 0 <= eta1 + eta2)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + eta2) * rho) + ((eta1 + eta2) * rho) ^ 2 <=
        c2 * u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2 c3 u kappaA higherOrder := by
  refine
    qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair
      fp A hn hvalid hdiag hresidual hRinv hP11 hP21 hQcs hF
      hUorth hWorth hVorth hCdiag hSdiag hTdiag hs hcs ?_ ?_
      heta12 hrho hbudget
  next =>
    intro dTop dBottom hdTop hbottom
    have hmap :
        Problem1912CorrectionMap m n
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          Qcs dTop
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
          F :=
      problem1912_correctionMap_of_csDiagonalAlgebra
        hdTop hP11 hP21 hQcs hF hUorth hWorth hVorth
        hCdiag hSdiag hTdiag hs hcs
    exact
      rectOpNorm2Le_mono hNormBudget
        (problem1912_repairedPerturbation_rectOpNorm2Le_of_bounds
          (by norm_num : (0 : Real) <= 1) hmap.map_bound
          (hTop dTop hdTop) (hBottom dBottom hbottom))
  next =>
    intro dTop dBottom hdTop hbottom
    have hmap :
        Problem1912CorrectionMap m n
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          Qcs dTop
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
          F :=
      problem1912_correctionMap_of_csDiagonalAlgebra
        hdTop hP11 hP21 hQcs hF hUorth hWorth hVorth
        hCdiag hSdiag hTdiag hs hcs
    exact
      problem1912_repairedPerturbation_columnFrob_le_of_column_budget
        (A := A) (F := F) (dBottom := dBottom) (dTop := dTop)
        (by norm_num : (0 : Real) <= 1) hmap.map_bound
        (hTopCol dTop hdTop) (hBottomCol dBottom hbottom)
        hColBudget

/-- Concrete diagonal-CS source-output assembly driven directly by a stacked
columnwise perturbation budget for `[Delta A_top; Delta A_bottom]`.

This removes the separate top and bottom operator/column hypotheses from
`qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_perturbation_bounds`:
the source `(19.34)` budget supplies them through the top/bottom extraction
lemmas. -/
theorem qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_stacked_budget
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)))
    {eta1 etaTop etaBottom eta2 rho c2 c3 u kappaA higherOrder
        cStack : Real}
    {U C S T W : Fin n -> Fin n -> Real}
    {V Qcs F : Fin m -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hP11 :
      paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMul n U (matMul n C (finiteTranspose W)))
    (hP21 :
      paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQcs : Qcs = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1)
    (hstack :
      forall (dTop : Fin n -> Fin n -> Real)
          (dBottom : Fin m -> Fin n -> Real),
        dTop =
          matMul n
            (paddedEconomyP11
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        (fun i j => A i j + dBottom i j) =
          matMulRect m n n
            (paddedEconomyQ
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        stackedPerturbationColumnwiseBound A dTop dBottom cStack)
    (hcStack : 0 <= cStack)
    (hTopResidual : cStack * frobNormRect A <= etaTop)
    (hBottomResidual : cStack * frobNormRect A <= etaBottom)
    (hNormBudget : 1 * etaTop + etaBottom <= eta2)
    (hColBudget :
      forall j,
        1 * (cStack * columnFrob A j) +
            (cStack * columnFrob A j) <=
          c3 * u * columnFrob A j)
    (heta12 : 0 <= eta1 + eta2)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + eta2) * rho) + ((eta1 + eta2) * rho) ^ 2 <=
        c2 * u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2 c3 u kappaA higherOrder := by
  refine
    qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair
      fp A hn hvalid hdiag hresidual hRinv hP11 hP21 hQcs hF
      hUorth hWorth hVorth hCdiag hSdiag hTdiag hs hcs ?_ ?_
      heta12 hrho hbudget
  next =>
    intro dTop dBottom hdTop hbottom
    have hmap :
        Problem1912CorrectionMap m n
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          Qcs dTop
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
          F :=
      problem1912_correctionMap_of_csDiagonalAlgebra
        hdTop hP11 hP21 hQcs hF hUorth hWorth hVorth
        hCdiag hSdiag hTdiag hs hcs
    have hstackLocal :
        stackedPerturbationColumnwiseBound A dTop dBottom cStack :=
      hstack dTop dBottom hdTop hbottom
    have hTop : rectOpNorm2Le dTop etaTop :=
      topPerturbation_rectOpNorm2Le_of_stackedColumnwiseBound
        A dTop dBottom hcStack hstackLocal hTopResidual
    have hBottom : rectOpNorm2Le dBottom etaBottom :=
      bottomPerturbation_rectOpNorm2Le_of_stackedColumnwiseBound
        A dTop dBottom hcStack hstackLocal hBottomResidual
    exact
      rectOpNorm2Le_mono hNormBudget
        (problem1912_repairedPerturbation_rectOpNorm2Le_of_bounds
          (by norm_num : (0 : Real) <= 1) hmap.map_bound
          hTop hBottom)
  next =>
    intro dTop dBottom hdTop hbottom
    have hmap :
        Problem1912CorrectionMap m n
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          Qcs dTop
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
          F :=
      problem1912_correctionMap_of_csDiagonalAlgebra
        hdTop hP11 hP21 hQcs hF hUorth hWorth hVorth
        hCdiag hSdiag hTdiag hs hcs
    have hstackLocal :
        stackedPerturbationColumnwiseBound A dTop dBottom cStack :=
      hstack dTop dBottom hdTop hbottom
    exact
      problem1912_repairedPerturbation_columnFrob_le_of_column_budget
        (A := A) (F := F) (dBottom := dBottom) (dTop := dTop)
        (topBudget := fun j => cStack * columnFrob A j)
        (bottomBudget := fun j => cStack * columnFrob A j)
        (by norm_num : (0 : Real) <= 1) hmap.map_bound
        (topPerturbation_columnFrob_le_of_stackedColumnwiseBound
          A dTop dBottom hstackLocal)
        (bottomPerturbation_columnFrob_le_of_stackedColumnwiseBound
          A dTop dBottom hstackLocal)
        hColBudget

/-- Concrete diagonal-CS source-output assembly using the actual stacked
perturbation bound returned by the padded Householder handoff.

Compared with
`qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_stacked_budget`,
this theorem does not require an external uniqueness-style stacked-budget
hypothesis.  The internally extracted `(19.34)` block data supplies the
stacked bound for the same `Delta A_top` and `Delta A_bottom` used in the
repair step. -/
theorem qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_budget
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)))
    {eta1 etaTop etaBottom eta2 rho c2 c3 u kappaA higherOrder : Real}
    {U C S T W : Fin n -> Fin n -> Real}
    {V Qcs F : Fin m -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hP11 :
      paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMul n U (matMul n C (finiteTranspose W)))
    (hP21 :
      paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQcs : Qcs = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1)
    (hTopResidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= etaTop)
    (hBottomResidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= etaBottom)
    (hNormBudget : 1 * etaTop + etaBottom <= eta2)
    (hColBudget :
      forall j,
        1 * (Theorem19_4.gamma_tilde fp (n + m) n * columnFrob A j) +
            (Theorem19_4.gamma_tilde fp (n + m) n * columnFrob A j) <=
          c3 * u * columnFrob A j)
    (heta12 : 0 <= eta1 + eta2)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + eta2) * rho) + ((eta1 + eta2) * rho) ^ 2 <=
        c2 * u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2 c3 u kappaA higherOrder := by
  let R11 : Fin n -> Fin n -> Real :=
    paddedEconomyR
      (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
  have hfull := householder_paddedFinInput_full_block_data fp A hn hvalid
  cases hfull with
  | intro dTop htopExists =>
      cases htopExists with
      | intro dBottom hblock =>
          dsimp only at hblock
          have hRright : matMul n R11 (nonsingInv n R11) = idMatrix n := by
            simpa [R11] using
              householder_paddedFinInput_R11_nonsingInv_right_inverse_of_diag_ne_zero
                fp A hn hvalid hdiag
          have hdA1 : rectOpNorm2Le dBottom eta1 :=
            bottomPerturbation_rectOpNorm2Le_of_stackedColumnwiseBound
              A dTop dBottom (Theorem19_4.gamma_tilde_nonneg fp hvalid)
              hblock.2.2.2.2.2 hresidual
          have hdTop :
              dTop =
                matMul n
                  (paddedEconomyP11
                    (fl_householderQRPanel_Q fp (n + m) n
                      (paddedFinInput A)))
                  R11 := by
            simpa [R11, matMulRect, matMul] using hblock.1
          have hTop : rectOpNorm2Le dTop etaTop :=
            topPerturbation_rectOpNorm2Le_of_stackedColumnwiseBound
              A dTop dBottom (Theorem19_4.gamma_tilde_nonneg fp hvalid)
              hblock.2.2.2.2.2 hTopResidual
          have hBottom : rectOpNorm2Le dBottom etaBottom :=
            bottomPerturbation_rectOpNorm2Le_of_stackedColumnwiseBound
              A dTop dBottom (Theorem19_4.gamma_tilde_nonneg fp hvalid)
              hblock.2.2.2.2.2 hBottomResidual
          have hTopCol :
              forall j,
                columnFrob dTop j <=
                  Theorem19_4.gamma_tilde fp (n + m) n *
                    columnFrob A j :=
            topPerturbation_columnFrob_le_of_stackedColumnwiseBound
              A dTop dBottom hblock.2.2.2.2.2
          have hBottomCol :
              forall j,
                columnFrob dBottom j <=
                  Theorem19_4.gamma_tilde fp (n + m) n *
                    columnFrob A j :=
            bottomPerturbation_columnFrob_le_of_stackedColumnwiseBound
              A dTop dBottom hblock.2.2.2.2.2
          have hrepair :
              Exists fun Q : Fin m -> Fin n -> Real =>
              Exists fun dA2 : Fin m -> Fin n -> Real =>
                GramSchmidtOrthonormalColumns Q /\
                (fun i j => A i j + dA2 i j) =
                  matMulRect m n n Q R11 /\
                rectOpNorm2Le dA2 eta2 /\
                (forall j, columnFrob dA2 j <=
                  c3 * u * columnFrob A j) :=
            problem1912_repair_of_csDiagonalAlgebra_of_perturbation_bounds
              hblock.2.1 hdTop hP11 hP21 hQcs hF hUorth hWorth hVorth
              hCdiag hSdiag hTdiag hs hcs hTop hBottom hNormBudget
              hTopCol hBottomCol hColBudget
          cases hrepair with
          | intro Q hQExists =>
              cases hQExists with
          | intro dA2 hrep =>
                  exact
                    qrsensitivitySourceOutput_of_commonR_bounds
                      hblock.2.1 hrep.2.1 hrep.1 hRright
                      hdA1 hrep.2.2.1 hRinv heta12 hrho hbudget
                      hrep.2.2.2

/-- Frobenius-inverse fallback for the concrete diagonal-CS source-output
assembly.

This keeps the source diagonal-nonbreakdown and CS/polar repair data explicit,
but discharges the inverse-norm certificate by taking
`rho = ||nonsingInv R11||_F`.  A sharper source condition estimate can later
replace this fallback through
`qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair`. -/
theorem qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_frobInv
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)))
    {eta1 eta2 c2 c3 u kappaA higherOrder : Real}
    {U C S T W : Fin n -> Fin n -> Real}
    {V Qcs F : Fin m -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hP11 :
      paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMul n U (matMul n C (finiteTranspose W)))
    (hP21 :
      paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQcs : Qcs = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1)
    (hnorm :
      forall (dTop : Fin n -> Fin n -> Real)
          (dBottom : Fin m -> Fin n -> Real),
        dTop =
          matMul n
            (paddedEconomyP11
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        (fun i j => A i j + dBottom i j) =
          matMulRect m n n
            (paddedEconomyQ
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        rectOpNorm2Le
          (fun i j => matMulRect m n n F dTop i j + dBottom i j)
          eta2)
    (hcol :
      forall (dTop : Fin n -> Fin n -> Real)
          (dBottom : Fin m -> Fin n -> Real),
        dTop =
          matMul n
            (paddedEconomyP11
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        (fun i j => A i j + dBottom i j) =
          matMulRect m n n
            (paddedEconomyQ
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        forall j,
          columnFrob
              (fun i j => matMulRect m n n F dTop i j + dBottom i j)
              j <=
            c3 * u * columnFrob A j)
    (heta12 : 0 <= eta1 + eta2)
    (hbudget :
      2 * ((eta1 + eta2) *
          frobNorm
            (nonsingInv n
              (paddedEconomyR
                (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) +
          ((eta1 + eta2) *
            frobNorm
              (nonsingInv n
                (paddedEconomyR
                  (fl_householderQRPanel_R fp (n + m) n
                    (paddedFinInput A))))) ^ 2 <=
        c2 * u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2 c3 u kappaA higherOrder := by
  let R11 : Fin n -> Fin n -> Real :=
    paddedEconomyR
      (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
  have hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        (frobNorm
          (nonsingInv n
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) := by
    simpa [R11] using rectOpNorm2Le_nonsingInv_frobNorm R11
  have hrho :
      0 <=
        frobNorm
          (nonsingInv n
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))) := by
    simpa [R11] using frobNorm_nonneg (nonsingInv n R11)
  exact
    qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair
      fp A hn hvalid hdiag hresidual hRinv hP11 hP21 hQcs hF hUorth
      hWorth hVorth hCdiag hSdiag hTdiag hs hcs hnorm hcol heta12
      hrho hbudget

/-- Common-`R` product-difference algebra for the post-repair Theorem 19.13
route.  Once two perturbation factorizations use the same `Rhat`, this turns
their difference into `(Qhat - Q) * Rhat = dA1 - dA2`. -/
theorem commonR_difference_product_eq_perturbation_difference {m n : Nat}
    {A Qhat Q dA1 dA2 : Fin m -> Fin n -> Real}
    {Rhat : Fin n -> Fin n -> Real}
    (hhat :
      (fun i j => A i j + dA1 i j) =
        matMulRect m n n Qhat Rhat)
    (hQ :
      (fun i j => A i j + dA2 i j) =
        matMulRect m n n Q Rhat) :
    matMulRect m n n (fun i k => Qhat i k - Q i k) Rhat =
      fun i j => dA1 i j - dA2 i j := by
  exact
    LeanFpAnalysis.FP.commonR_difference_product_eq_perturbation_difference
      hhat hQ

/-- Right-inverse form of the common-`R` algebra for the post-repair Theorem
19.13 route. -/
theorem commonR_difference_eq_perturbation_difference_mul_right_inverse
    {m n : Nat}
    {A Qhat Q dA1 dA2 : Fin m -> Fin n -> Real}
    {Rhat Rinv : Fin n -> Fin n -> Real}
    (hhat :
      (fun i j => A i j + dA1 i j) =
        matMulRect m n n Qhat Rhat)
    (hQ :
      (fun i j => A i j + dA2 i j) =
        matMulRect m n n Q Rhat)
    (hRright : matMul n Rhat Rinv = idMatrix n) :
    (fun i k => Qhat i k - Q i k) =
      matMulRect m n n (fun i j => dA1 i j - dA2 i j) Rinv := by
  exact
    LeanFpAnalysis.FP.commonR_difference_eq_perturbation_difference_mul_right_inverse
      hhat hQ hRright

/-- Operator-norm consequence of the common-`R` right-inverse algebra. -/
theorem commonR_difference_rectOpNorm2Le_of_perturbation_difference_mul_right_inverse
    {m n : Nat}
    {A Qhat Q dA1 dA2 : Fin m -> Fin n -> Real}
    {Rhat Rinv : Fin n -> Fin n -> Real}
    {eta rho : Real}
    (hhat :
      (fun i j => A i j + dA1 i j) =
        matMulRect m n n Qhat Rhat)
    (hQ :
      (fun i j => A i j + dA2 i j) =
        matMulRect m n n Q Rhat)
    (hRright : matMul n Rhat Rinv = idMatrix n)
    (hdiff : rectOpNorm2Le (fun i j => dA1 i j - dA2 i j) eta)
    (hRinv : rectOpNorm2Le Rinv rho)
    (heta : 0 <= eta) :
    rectOpNorm2Le (fun i k => Qhat i k - Q i k) (eta * rho) := by
  exact
    LeanFpAnalysis.FP.commonR_difference_rectOpNorm2Le_of_perturbation_difference_mul_right_inverse
      hhat hQ hRright hdiff hRinv heta

/-- Common-`R` norm bridge using separate perturbation certificates for `dA1`
and `dA2`. -/
theorem commonR_difference_rectOpNorm2Le_of_perturbation_bounds_mul_right_inverse
    {m n : Nat}
    {A Qhat Q dA1 dA2 : Fin m -> Fin n -> Real}
    {Rhat Rinv : Fin n -> Fin n -> Real}
    {eta1 eta2 rho : Real}
    (hhat :
      (fun i j => A i j + dA1 i j) =
        matMulRect m n n Qhat Rhat)
    (hQ :
      (fun i j => A i j + dA2 i j) =
        matMulRect m n n Q Rhat)
    (hRright : matMul n Rhat Rinv = idMatrix n)
    (hdA1 : rectOpNorm2Le dA1 eta1)
    (hdA2 : rectOpNorm2Le dA2 eta2)
    (hRinv : rectOpNorm2Le Rinv rho)
    (heta : 0 <= eta1 + eta2) :
    rectOpNorm2Le (fun i k => Qhat i k - Q i k) ((eta1 + eta2) * rho) := by
  exact
    LeanFpAnalysis.FP.commonR_difference_rectOpNorm2Le_of_perturbation_bounds_mul_right_inverse
      hhat hQ hRright hdA1 hdA2 hRinv heta

/-- Exact Gram-residual expansion used after bounding `Qhat - Q` in the
Theorem 19.13 orthogonality-loss route. -/
theorem gramSchmidtOrthogonalityResidual_eq_close_expansion {m n : Nat}
    {Qhat Q : Fin m -> Fin n -> Real}
    (hQ : GramSchmidtOrthonormalColumns Q) :
    gramSchmidtOrthogonalityResidual Qhat =
      fun i j =>
        (Finset.univ.sum fun r : Fin m =>
          Q r i * (Qhat r j - Q r j)) +
        (Finset.univ.sum fun r : Fin m =>
          (Qhat r i - Q r i) * Q r j) +
        (Finset.univ.sum fun r : Fin m =>
          (Qhat r i - Q r i) * (Qhat r j - Q r j)) := by
  exact LeanFpAnalysis.FP.gramSchmidtOrthogonalityResidual_eq_close_expansion hQ

/-- Orthonormal columns give the unit operator-2 certificate needed in the
Theorem 19.13 orthogonality-loss conversion. -/
theorem orthonormalColumns_rectOpNorm2Le_one {m n : Nat}
    {Q : Fin m -> Fin n -> Real}
    (hQ : GramSchmidtOrthonormalColumns Q) :
    rectOpNorm2Le Q 1 := by
  exact LeanFpAnalysis.FP.GramSchmidtOrthonormalColumns.rectOpNorm2Le_one hQ

/-- Source-facing `2*delta + delta^2` Gram-residual conversion for the
Theorem 19.13 orthogonality-loss route. -/
theorem gramSchmidtOrthogonalityResidual_opNorm2Le_of_close_orthonormal
    {m n : Nat}
    {Qhat Q : Fin m -> Fin n -> Real} {delta : Real}
    (hQ : GramSchmidtOrthonormalColumns Q)
    (hclose : rectOpNorm2Le (fun i j => Qhat i j - Q i j) delta)
    (hdelta : 0 <= delta) :
    opNorm2Le (gramSchmidtOrthogonalityResidual Qhat)
      (2 * delta + delta ^ 2) := by
  exact
    LeanFpAnalysis.FP.gramSchmidtOrthogonalityResidual_opNorm2Le_of_close_orthonormal
      hQ hclose hdelta

/-- The current end-of-pipeline bridge for Theorem 19.13: the compiled
Householder-MGS economy product supplies the residual equation and upper
economy `R`; the two visible hypotheses are the residual norm conversion and
the QR-sensitivity output from `(19.35)`-`(19.37)`. -/
theorem mgs_qr_bounds_of_householder_economy_product_sensitivity
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)))
    {c1 c2 c3 u normA kappaA higherOrder : Real}
    (hresidual :
      forall dTop : Fin n -> Fin n -> Real,
      forall dBottom : Fin m -> Fin n -> Real,
        stackedPerturbationColumnwiseBound A dTop dBottom
          (Theorem19_4.gamma_tilde fp (n + m) n) ->
        rectOpNorm2Le dBottom (c1 * u * normA))
    (hsensitivity :
      forall dTop : Fin n -> Fin n -> Real,
      forall dBottom : Fin m -> Fin n -> Real,
        (fun i j => A i j + dBottom i j) =
          matMulRect m n n
            (paddedEconomyQ
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        stackedPerturbationColumnwiseBound A dTop dBottom
          (Theorem19_4.gamma_tilde fp (n + m) n) ->
        QRSensitivityBridge m n A
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
          c2 c3 u kappaA higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c1 c2 c3 u normA kappaA higherOrder := by
  have hecon :=
    householder_paddedFinInput_economyProduct_with_upper fp A hn hvalid
  cases hecon with
  | intro dTop htop =>
      cases htop with
      | intro dBottom hres =>
          exact mgs_qr_bounds_of_economy_product_sensitivity
            hres.2.1 hres.1
            (hresidual dTop dBottom hres.2.2.2)
            (hsensitivity dTop dBottom hres.1 hres.2.2.2)

/-- Same assembly as
`mgs_qr_bounds_of_householder_economy_product_sensitivity`, but with the
residual channel discharged from the stacked columnwise perturbation bound and
a scalar Frobenius budget.  The remaining proof-heavy input is the
QR-sensitivity bridge. -/
theorem mgs_qr_bounds_of_householder_economy_product_sensitivity_of_residual_budget
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)))
    {c1 c2 c3 u normA kappaA higherOrder : Real}
    (hgamma_nonneg : 0 <= Theorem19_4.gamma_tilde fp (n + m) n)
    (hresidualBudget :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <=
        c1 * u * normA)
    (hsensitivity :
      forall dTop : Fin n -> Fin n -> Real,
      forall dBottom : Fin m -> Fin n -> Real,
        (fun i j => A i j + dBottom i j) =
          matMulRect m n n
            (paddedEconomyQ
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        stackedPerturbationColumnwiseBound A dTop dBottom
          (Theorem19_4.gamma_tilde fp (n + m) n) ->
        QRSensitivityBridge m n A
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
          c2 c3 u kappaA higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c1 c2 c3 u normA kappaA higherOrder := by
  exact
    mgs_qr_bounds_of_householder_economy_product_sensitivity
      fp A hn hvalid
      (by
        intro dTop dBottom hstack
        exact
          bottomPerturbation_rectOpNorm2Le_of_stackedColumnwiseBound
            A dTop dBottom hgamma_nonneg hstack hresidualBudget)
      hsensitivity

/-- Residual-budget assembly with the Householder gamma nonnegativity fact
derived from the existing `gammaValid` guard. -/
theorem mgs_qr_bounds_of_householder_economy_product_sensitivity_of_valid_residual_budget
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)))
    {c1 c2 c3 u normA kappaA higherOrder : Real}
    (hresidualBudget :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <=
        c1 * u * normA)
    (hsensitivity :
      forall dTop : Fin n -> Fin n -> Real,
      forall dBottom : Fin m -> Fin n -> Real,
        (fun i j => A i j + dBottom i j) =
          matMulRect m n n
            (paddedEconomyQ
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        stackedPerturbationColumnwiseBound A dTop dBottom
          (Theorem19_4.gamma_tilde fp (n + m) n) ->
        QRSensitivityBridge m n A
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
          c2 c3 u kappaA higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c1 c2 c3 u normA kappaA higherOrder := by
  exact
    mgs_qr_bounds_of_householder_economy_product_sensitivity_of_residual_budget
      fp A hn hvalid (Theorem19_4.gamma_tilde_nonneg fp hvalid)
      hresidualBudget hsensitivity

/-- A scalar residual budget follows from a coefficient budget for
`gamma_tilde` and a chosen upper bound for the input Frobenius norm. -/
theorem residualBudget_of_gamma_tilde_le_mul_norm_bound
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)))
    {c1 u normA : Real}
    (hgamma : Theorem19_4.gamma_tilde fp (n + m) n <= c1 * u)
    (hnormA : frobNormRect A <= normA) :
    Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <=
      c1 * u * normA := by
  have hgamma_nonneg :
      0 <= Theorem19_4.gamma_tilde fp (n + m) n :=
    Theorem19_4.gamma_tilde_nonneg fp hvalid
  have hfrob_nonneg : 0 <= frobNormRect A := frobNormRect_nonneg A
  have hcu_nonneg : 0 <= c1 * u := le_trans hgamma_nonneg hgamma
  calc
    Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A
        <= (c1 * u) * frobNormRect A :=
          mul_le_mul_of_nonneg_right hgamma hfrob_nonneg
    _ <= (c1 * u) * normA :=
          mul_le_mul_of_nonneg_left hnormA hcu_nonneg
    _ = c1 * u * normA := by ring

/-- Exact-norm residual budget from the coefficient budget
`gamma_tilde <= c1*u`. -/
theorem residualBudget_of_gamma_tilde_le_mul_self
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)))
    {c1 u : Real}
    (hgamma : Theorem19_4.gamma_tilde fp (n + m) n <= c1 * u) :
    Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <=
      c1 * u * frobNormRect A := by
  simpa using
    (residualBudget_of_gamma_tilde_le_mul_norm_bound
      (fp := fp) (m := m) (n := n) A hvalid
      (c1 := c1) (u := u) (normA := frobNormRect A)
      hgamma (le_rfl : frobNormRect A <= frobNormRect A))

/-- Residual-budget assembly expressed in terms of a coefficient budget
`gamma_tilde <= c1*u` and an input norm budget `||A||_F <= normA`. -/
theorem mgs_qr_bounds_of_householder_economy_product_sensitivity_of_coefficient_norm_budget
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)))
    {c1 c2 c3 u normA kappaA higherOrder : Real}
    (hgamma : Theorem19_4.gamma_tilde fp (n + m) n <= c1 * u)
    (hnormA : frobNormRect A <= normA)
    (hsensitivity :
      forall dTop : Fin n -> Fin n -> Real,
      forall dBottom : Fin m -> Fin n -> Real,
        (fun i j => A i j + dBottom i j) =
          matMulRect m n n
            (paddedEconomyQ
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        stackedPerturbationColumnwiseBound A dTop dBottom
          (Theorem19_4.gamma_tilde fp (n + m) n) ->
        QRSensitivityBridge m n A
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
          c2 c3 u kappaA higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c1 c2 c3 u normA kappaA higherOrder := by
  exact
    mgs_qr_bounds_of_householder_economy_product_sensitivity_of_valid_residual_budget
      fp A hn hvalid
      (residualBudget_of_gamma_tilde_le_mul_norm_bound
        fp A hvalid hgamma hnormA)
      hsensitivity

/-- Exact-norm residual-budget assembly from only the coefficient budget
`gamma_tilde <= c1*u`, plus the QR-sensitivity bridge. -/
theorem mgs_qr_bounds_of_householder_economy_product_sensitivity_of_coefficient_budget
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)))
    {c1 c2 c3 u kappaA higherOrder : Real}
    (hgamma : Theorem19_4.gamma_tilde fp (n + m) n <= c1 * u)
    (hsensitivity :
      forall dTop : Fin n -> Fin n -> Real,
      forall dBottom : Fin m -> Fin n -> Real,
        (fun i j => A i j + dBottom i j) =
          matMulRect m n n
            (paddedEconomyQ
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        stackedPerturbationColumnwiseBound A dTop dBottom
          (Theorem19_4.gamma_tilde fp (n + m) n) ->
        QRSensitivityBridge m n A
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
          c2 c3 u kappaA higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c1 c2 c3 u (frobNormRect A) kappaA higherOrder := by
  exact
    mgs_qr_bounds_of_householder_economy_product_sensitivity_of_coefficient_norm_budget
      fp A hn hvalid hgamma
      (le_rfl : frobNormRect A <= frobNormRect A)
      hsensitivity

/-- Exact-norm coefficient-budget assembly whose remaining QR-sensitivity
input is stated with source labels from `(19.35a)`-`(19.37)`. -/
theorem mgs_qr_bounds_of_householder_economy_product_source_sensitivity_of_coefficient_budget
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)))
    {c1 c2 c3 u kappaA higherOrder : Real}
    (hgamma : Theorem19_4.gamma_tilde fp (n + m) n <= c1 * u)
    (hsourceSensitivity :
      forall dTop : Fin n -> Fin n -> Real,
      forall dBottom : Fin m -> Fin n -> Real,
        (fun i j => A i j + dBottom i j) =
          matMulRect m n n
            (paddedEconomyQ
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        stackedPerturbationColumnwiseBound A dTop dBottom
          (Theorem19_4.gamma_tilde fp (n + m) n) ->
        QRSensitivitySourceOutput m n A
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
          c2 c3 u kappaA higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c1 c2 c3 u (frobNormRect A) kappaA higherOrder := by
  exact
    mgs_qr_bounds_of_householder_economy_product_sensitivity_of_coefficient_budget
      fp A hn hvalid hgamma
      (by
        intro dTop dBottom hprod hstack
        exact qrsensitivityBridge_of_source_output
          (hsourceSensitivity dTop dBottom hprod hstack))

/-- Exact-unit-roundoff assembly for Theorem 19.13's current route.  The
coefficient budget for the Householder perturbation is discharged from the
standard smallness condition on the concrete `gamma_tilde` index, leaving only
the source-labeled QR-sensitivity outputs from `(19.35a)`-`(19.37)`. -/
theorem mgs_qr_bounds_of_householder_economy_product_source_sensitivity_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {c2 c3 kappaA higherOrder : Real}
    (hsourceSensitivity :
      forall dTop : Fin n -> Fin n -> Real,
      forall dBottom : Fin m -> Fin n -> Real,
        (fun i j => A i j + dBottom i j) =
          matMulRect m n n
            (paddedEconomyQ
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        stackedPerturbationColumnwiseBound A dTop dBottom
          (Theorem19_4.gamma_tilde fp (n + m) n) ->
        QRSensitivitySourceOutput m n A
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
          c2 c3 fp.u kappaA higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2 c3 fp.u (frobNormRect A) kappaA higherOrder := by
  have hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)) := by
    unfold gammaValid
    have hhalf_lt_one : (1 / 2 : Real) < 1 := by norm_num
    exact lt_of_le_of_lt hsmall hhalf_lt_one
  exact
    mgs_qr_bounds_of_householder_economy_product_source_sensitivity_of_coefficient_budget
      fp A hn hvalid
      (Theorem19_4.gamma_tilde_le_two_index_mul_unit_roundoff_of_small
        fp (n + m) n hsmall)
      hsourceSensitivity

/-- Small-unit-roundoff Theorem 19.13 assembly with the remaining
source-facing obligations exposed as diagonal nonbreakdown, an inverse-norm
budget for `R11`, and the Problem 19.12-style repair certificate. -/
theorem mgs_qr_bounds_of_householder_upper_diag_repair_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 eta2 rho c2 c3 kappaA higherOrder : Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hrepair :
      opNorm2Le
        (orthogonalityResidual
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A))))
        ((eta1 * rho) ^ 2) ->
      Exists fun Q : Fin m -> Fin n -> Real =>
      Exists fun dA2 : Fin m -> Fin n -> Real =>
        GramSchmidtOrthonormalColumns Q /\
        (fun i j => A i j + dA2 i j) =
          matMulRect m n n Q
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) /\
        rectOpNorm2Le dA2 eta2 /\
        (forall j, columnFrob dA2 j <= c3 * fp.u * columnFrob A j))
    (heta1 : 0 <= eta1)
    (heta12 : 0 <= eta1 + eta2)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + eta2) * rho) + ((eta1 + eta2) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2 c3 fp.u (frobNormRect A) kappaA higherOrder := by
  have hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)) := by
    unfold gammaValid
    have hhalf_lt_one : (1 / 2 : Real) < 1 := by norm_num
    exact lt_of_le_of_lt hsmall hhalf_lt_one
  have hsource :
      QRSensitivitySourceOutput m n A
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
        c2 c3 fp.u kappaA higherOrder :=
    qrsensitivitySourceOutput_of_householder_upper_diag_repair
      fp A hn hvalid hdiag hresidual hRinv hrepair
      heta1 heta12 hrho hbudget
  exact
    mgs_qr_bounds_of_householder_economy_product_source_sensitivity_of_small_unit_roundoff
      fp A hn hsmall
      (by
        intro dTop dBottom hprod hstack
        exact hsource)

/-- Small-unit-roundoff Theorem 19.13 assembly with the Problem 19.12 repair
certificate replaced by diagonal CS data and repaired-perturbation budgets. -/
theorem
    mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 eta2 rho c2 c3 kappaA higherOrder : Real}
    {U C S T W : Fin n -> Fin n -> Real}
    {V Qcs F : Fin m -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hP11 :
      paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMul n U (matMul n C (finiteTranspose W)))
    (hP21 :
      paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQcs : Qcs = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1)
    (hnorm :
      forall (dTop : Fin n -> Fin n -> Real)
          (dBottom : Fin m -> Fin n -> Real),
        dTop =
          matMul n
            (paddedEconomyP11
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        (fun i j => A i j + dBottom i j) =
          matMulRect m n n
            (paddedEconomyQ
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        rectOpNorm2Le
          (fun i j => matMulRect m n n F dTop i j + dBottom i j)
          eta2)
    (hcol :
      forall (dTop : Fin n -> Fin n -> Real)
          (dBottom : Fin m -> Fin n -> Real),
        dTop =
          matMul n
            (paddedEconomyP11
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        (fun i j => A i j + dBottom i j) =
          matMulRect m n n
            (paddedEconomyQ
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        forall j,
          columnFrob
              (fun i j => matMulRect m n n F dTop i j + dBottom i j)
              j <=
            c3 * fp.u * columnFrob A j)
    (heta12 : 0 <= eta1 + eta2)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + eta2) * rho) + ((eta1 + eta2) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2 c3 fp.u (frobNormRect A) kappaA higherOrder := by
  have hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)) := by
    unfold gammaValid
    have hhalf_lt_one : (1 / 2 : Real) < 1 := by norm_num
    exact lt_of_le_of_lt hsmall hhalf_lt_one
  have hsource :
      QRSensitivitySourceOutput m n A
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
        c2 c3 fp.u kappaA higherOrder :=
    qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair
      fp A hn hvalid hdiag hresidual hRinv hP11 hP21 hQcs hF hUorth
      hWorth hVorth hCdiag hSdiag hTdiag hs hcs hnorm hcol heta12
      hrho hbudget
  exact
    mgs_qr_bounds_of_householder_economy_product_source_sensitivity_of_small_unit_roundoff
      fp A hn hsmall
      (by
        intro dTop dBottom hprod hstack
        exact hsource)

/-- Small-unit-roundoff Theorem 19.13 assembly with the Problem 19.12 repair
certificate replaced by diagonal CS data and a single stacked perturbation
budget for `[Delta A_top; Delta A_bottom]`. -/
theorem
    mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_stacked_budget_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 etaTop etaBottom eta2 rho c2 c3 kappaA higherOrder
        cStack : Real}
    {U C S T W : Fin n -> Fin n -> Real}
    {V Qcs F : Fin m -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hP11 :
      paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMul n U (matMul n C (finiteTranspose W)))
    (hP21 :
      paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQcs : Qcs = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1)
    (hstack :
      forall (dTop : Fin n -> Fin n -> Real)
          (dBottom : Fin m -> Fin n -> Real),
        dTop =
          matMul n
            (paddedEconomyP11
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        (fun i j => A i j + dBottom i j) =
          matMulRect m n n
            (paddedEconomyQ
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        stackedPerturbationColumnwiseBound A dTop dBottom cStack)
    (hcStack : 0 <= cStack)
    (hTopResidual : cStack * frobNormRect A <= etaTop)
    (hBottomResidual : cStack * frobNormRect A <= etaBottom)
    (hNormBudget : 1 * etaTop + etaBottom <= eta2)
    (hColBudget :
      forall j,
        1 * (cStack * columnFrob A j) +
            (cStack * columnFrob A j) <=
          c3 * fp.u * columnFrob A j)
    (heta12 : 0 <= eta1 + eta2)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + eta2) * rho) + ((eta1 + eta2) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2 c3 fp.u (frobNormRect A) kappaA higherOrder := by
  have hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)) := by
    unfold gammaValid
    have hhalf_lt_one : (1 / 2 : Real) < 1 := by norm_num
    exact lt_of_le_of_lt hsmall hhalf_lt_one
  have hsource :
      QRSensitivitySourceOutput m n A
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
        c2 c3 fp.u kappaA higherOrder :=
    qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_stacked_budget
      fp A hn hvalid hdiag hresidual hRinv hP11 hP21 hQcs hF
      hUorth hWorth hVorth hCdiag hSdiag hTdiag hs hcs hstack
      hcStack hTopResidual hBottomResidual hNormBudget hColBudget
      heta12 hrho hbudget
  exact
    mgs_qr_bounds_of_householder_economy_product_source_sensitivity_of_small_unit_roundoff
      fp A hn hsmall
      (by
        intro dTop dBottom hprod hstack
        exact hsource)

/-- Small-unit-roundoff Theorem 19.13 assembly using the actual stacked
perturbation budget returned by the padded Householder handoff. -/
theorem
    mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_budget_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 etaTop etaBottom eta2 rho c2 c3 kappaA higherOrder : Real}
    {U C S T W : Fin n -> Fin n -> Real}
    {V Qcs F : Fin m -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hP11 :
      paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMul n U (matMul n C (finiteTranspose W)))
    (hP21 :
      paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQcs : Qcs = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1)
    (hTopResidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= etaTop)
    (hBottomResidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= etaBottom)
    (hNormBudget : 1 * etaTop + etaBottom <= eta2)
    (hColBudget :
      forall j,
        1 * (Theorem19_4.gamma_tilde fp (n + m) n * columnFrob A j) +
            (Theorem19_4.gamma_tilde fp (n + m) n * columnFrob A j) <=
          c3 * fp.u * columnFrob A j)
    (heta12 : 0 <= eta1 + eta2)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + eta2) * rho) + ((eta1 + eta2) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2 c3 fp.u (frobNormRect A) kappaA higherOrder := by
  have hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)) := by
    unfold gammaValid
    have hhalf_lt_one : (1 / 2 : Real) < 1 := by norm_num
    exact lt_of_le_of_lt hsmall hhalf_lt_one
  have hsource :
      QRSensitivitySourceOutput m n A
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
        c2 c3 fp.u kappaA higherOrder :=
    qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_budget
      fp A hn hvalid hdiag hresidual hRinv hP11 hP21 hQcs hF
      hUorth hWorth hVorth hCdiag hSdiag hTdiag hs hcs
      hTopResidual hBottomResidual hNormBudget hColBudget
      heta12 hrho hbudget
  exact
    mgs_qr_bounds_of_householder_economy_product_source_sensitivity_of_small_unit_roundoff
      fp A hn hsmall
      (by
        intro dTop dBottom hprod hstack
        exact hsource)

/-- Small-unit-roundoff Theorem 19.13 assembly using pure Problem 19.12
correction-map data and the actual stacked perturbation budget from the padded
Householder handoff. -/
theorem
    mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_budget_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 etaTop etaBottom eta2 rho c2 c3 kappaA higherOrder : Real}
    {Qrepair F : Fin m -> Fin n -> Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hdata :
      Problem1912CorrectionMapData m n
        (paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        Qrepair F)
    (hTopResidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= etaTop)
    (hBottomResidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= etaBottom)
    (hNormBudget : 1 * etaTop + etaBottom <= eta2)
    (hColBudget :
      forall j,
        1 * (Theorem19_4.gamma_tilde fp (n + m) n * columnFrob A j) +
            (Theorem19_4.gamma_tilde fp (n + m) n * columnFrob A j) <=
          c3 * fp.u * columnFrob A j)
    (heta12 : 0 <= eta1 + eta2)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + eta2) * rho) + ((eta1 + eta2) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2 c3 fp.u (frobNormRect A) kappaA higherOrder := by
  have hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)) := by
    unfold gammaValid
    have hhalf_lt_one : (1 / 2 : Real) < 1 := by norm_num
    exact lt_of_le_of_lt hsmall hhalf_lt_one
  have hsource :
      QRSensitivitySourceOutput m n A
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
        c2 c3 fp.u kappaA higherOrder :=
    qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_budget
      fp A hn hvalid hdiag hresidual hRinv hdata
      hTopResidual hBottomResidual hNormBudget hColBudget
      heta12 hrho hbudget
  exact
    mgs_qr_bounds_of_householder_economy_product_source_sensitivity_of_small_unit_roundoff
      fp A hn hsmall
      (by
        intro dTop dBottom hprod hstack
        exact hsource)

/-- Frobenius-inverse fallback for the pure correction-map-data
Householder-stacked source-output assembly.

Once the CS/polar route supplies `Problem1912CorrectionMapData`, this wrapper
discharges the separate inverse-norm certificate by taking
`rho = ||nonsingInv R11||_F`.  The sharper source condition estimate remains
the next refinement, but it is no longer needed for this fallback transport. -/
theorem
    qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_budget_frobInv
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)))
    {eta1 etaTop etaBottom eta2 c2 c3 u kappaA higherOrder : Real}
    {Qrepair F : Fin m -> Fin n -> Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hdata :
      Problem1912CorrectionMapData m n
        (paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        Qrepair F)
    (hTopResidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= etaTop)
    (hBottomResidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= etaBottom)
    (hNormBudget : 1 * etaTop + etaBottom <= eta2)
    (hColBudget :
      forall j,
        1 * (Theorem19_4.gamma_tilde fp (n + m) n * columnFrob A j) +
            (Theorem19_4.gamma_tilde fp (n + m) n * columnFrob A j) <=
          c3 * u * columnFrob A j)
    (heta12 : 0 <= eta1 + eta2)
    (hbudget :
      2 * ((eta1 + eta2) *
          frobNorm
            (nonsingInv n
              (paddedEconomyR
                (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) +
          ((eta1 + eta2) *
            frobNorm
              (nonsingInv n
                (paddedEconomyR
                  (fl_householderQRPanel_R fp (n + m) n
                    (paddedFinInput A))))) ^ 2 <=
        c2 * u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2 c3 u kappaA higherOrder := by
  let R11 : Fin n -> Fin n -> Real :=
    paddedEconomyR
      (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
  have hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        (frobNorm
          (nonsingInv n
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) := by
    simpa [R11] using rectOpNorm2Le_nonsingInv_frobNorm R11
  have hrho :
      0 <=
        frobNorm
          (nonsingInv n
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))) := by
    simpa [R11] using frobNorm_nonneg (nonsingInv n R11)
  exact
    qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_budget
      (fp := fp) (m := m) (n := n) A hn hvalid
      (eta1 := eta1) (etaTop := etaTop) (etaBottom := etaBottom)
      (eta2 := eta2)
      (rho :=
        frobNorm
          (nonsingInv n
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))))
      (c2 := c2) (c3 := c3) (u := u)
      (kappaA := kappaA) (higherOrder := higherOrder)
      hdiag hresidual hRinv hdata hTopResidual hBottomResidual hNormBudget
      hColBudget heta12 hrho hbudget

/-- Small-unit-roundoff pure-data `MGSQRBounds` fallback using the Frobenius
norm of `nonsingInv R11` as the inverse budget.

This is the pure correction-map-data analogue of the diagonal-CS fallback:
after CS/polar provides the data payload, the downstream route can reach the
current `MGSQRBounds` contract without a separate inverse-norm certificate. -/
theorem
    mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_budget_frobInv_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 etaTop etaBottom eta2 c2 c3 kappaA higherOrder : Real}
    {Qrepair F : Fin m -> Fin n -> Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hdata :
      Problem1912CorrectionMapData m n
        (paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        Qrepair F)
    (hTopResidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= etaTop)
    (hBottomResidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= etaBottom)
    (hNormBudget : 1 * etaTop + etaBottom <= eta2)
    (hColBudget :
      forall j,
        1 * (Theorem19_4.gamma_tilde fp (n + m) n * columnFrob A j) +
            (Theorem19_4.gamma_tilde fp (n + m) n * columnFrob A j) <=
          c3 * fp.u * columnFrob A j)
    (heta12 : 0 <= eta1 + eta2)
    (hbudget :
      2 * ((eta1 + eta2) *
          frobNorm
            (nonsingInv n
              (paddedEconomyR
                (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) +
          ((eta1 + eta2) *
            frobNorm
              (nonsingInv n
                (paddedEconomyR
                  (fl_householderQRPanel_R fp (n + m) n
                    (paddedFinInput A))))) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2 c3 fp.u (frobNormRect A) kappaA higherOrder := by
  let R11 : Fin n -> Fin n -> Real :=
    paddedEconomyR
      (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
  have hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        (frobNorm
          (nonsingInv n
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) := by
    simpa [R11] using rectOpNorm2Le_nonsingInv_frobNorm R11
  have hrho :
      0 <=
        frobNorm
          (nonsingInv n
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))) := by
    simpa [R11] using frobNorm_nonneg (nonsingInv n R11)
  exact
    mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_budget_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hsmall
      (eta1 := eta1) (etaTop := etaTop) (etaBottom := etaBottom)
      (eta2 := eta2)
      (rho :=
        frobNorm
          (nonsingInv n
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))))
      (c2 := c2) (c3 := c3) (kappaA := kappaA)
      (higherOrder := higherOrder)
      hdiag hresidual hRinv hdata hTopResidual hBottomResidual hNormBudget
      hColBudget heta12 hrho hbudget

/-- Columnwise repaired-budget assembly from a single scalar coefficient
budget for the two stacked Householder perturbation columns. -/
theorem gamma_tilde_two_column_budget
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    {c3 u : Real}
    (hgamma :
      2 * Theorem19_4.gamma_tilde fp (n + m) n <= c3 * u) :
    forall j,
      1 * (Theorem19_4.gamma_tilde fp (n + m) n * columnFrob A j) +
          (Theorem19_4.gamma_tilde fp (n + m) n * columnFrob A j) <=
        c3 * u * columnFrob A j := by
  intro j
  have hcol : 0 <= columnFrob A j := columnFrob_nonneg A j
  calc
    1 * (Theorem19_4.gamma_tilde fp (n + m) n * columnFrob A j) +
          (Theorem19_4.gamma_tilde fp (n + m) n * columnFrob A j)
        = (2 * Theorem19_4.gamma_tilde fp (n + m) n) *
            columnFrob A j := by
          ring
    _ <= (c3 * u) * columnFrob A j :=
          mul_le_mul_of_nonneg_right hgamma hcol
    _ = c3 * u * columnFrob A j := by ring

/-- Concrete diagonal-CS source-output assembly where the same residual budget
is used for the top and bottom stacked perturbations, and the column budget is
reduced to the scalar coefficient inequality `2*gamma_tilde <= c3*u`. -/
theorem
    qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_same_residual_budget
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)))
    {eta1 eta2 rho c2 c3 u kappaA higherOrder : Real}
    {U C S T W : Fin n -> Fin n -> Real}
    {V Qcs F : Fin m -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hP11 :
      paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMul n U (matMul n C (finiteTranspose W)))
    (hP21 :
      paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQcs : Qcs = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1)
    (hNormBudget : 1 * eta1 + eta1 <= eta2)
    (hGammaColumnBudget :
      2 * Theorem19_4.gamma_tilde fp (n + m) n <= c3 * u)
    (heta12 : 0 <= eta1 + eta2)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + eta2) * rho) + ((eta1 + eta2) * rho) ^ 2 <=
        c2 * u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2 c3 u kappaA higherOrder := by
  exact
    qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_budget
      fp A hn hvalid hdiag hresidual hRinv hP11 hP21 hQcs hF
      hUorth hWorth hVorth hCdiag hSdiag hTdiag hs hcs
      hresidual hresidual hNormBudget
      (gamma_tilde_two_column_budget
        (fp := fp) (m := m) (n := n) (c3 := c3) (u := u)
        A hGammaColumnBudget)
      heta12 hrho hbudget

/-- Small-unit-roundoff Theorem 19.13 assembly with one residual budget and a
single scalar column coefficient budget. -/
theorem
    mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_same_residual_budget_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 eta2 rho c2 c3 kappaA higherOrder : Real}
    {U C S T W : Fin n -> Fin n -> Real}
    {V Qcs F : Fin m -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hP11 :
      paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMul n U (matMul n C (finiteTranspose W)))
    (hP21 :
      paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQcs : Qcs = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1)
    (hNormBudget : 1 * eta1 + eta1 <= eta2)
    (hGammaColumnBudget :
      2 * Theorem19_4.gamma_tilde fp (n + m) n <= c3 * fp.u)
    (heta12 : 0 <= eta1 + eta2)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + eta2) * rho) + ((eta1 + eta2) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2 c3 fp.u (frobNormRect A) kappaA higherOrder := by
  exact
    mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_budget_of_small_unit_roundoff
      fp A hn hsmall hdiag hresidual hRinv hP11 hP21 hQcs hF
      hUorth hWorth hVorth hCdiag hSdiag hTdiag hs hcs
      hresidual hresidual hNormBudget
      (gamma_tilde_two_column_budget
        (fp := fp) (m := m) (n := n) (c3 := c3) (u := fp.u)
        A hGammaColumnBudget)
      heta12 hrho hbudget

/-- Concrete diagonal-CS source-output assembly with the repaired perturbation
budget specialized to `eta2 = 2*eta1`.  The residual budget also supplies the
nonnegativity side condition for the final QR-sensitivity radius. -/
theorem
    qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_budget
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)))
    {eta1 rho c2 c3 u kappaA higherOrder : Real}
    {U C S T W : Fin n -> Fin n -> Real}
    {V Qcs F : Fin m -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hP11 :
      paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMul n U (matMul n C (finiteTranspose W)))
    (hP21 :
      paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQcs : Qcs = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1)
    (hGammaColumnBudget :
      2 * Theorem19_4.gamma_tilde fp (n + m) n <= c3 * u)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + 2 * eta1) * rho) +
          ((eta1 + 2 * eta1) * rho) ^ 2 <=
        c2 * u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2 c3 u kappaA higherOrder := by
  have hgamma_nonneg :
      0 <= Theorem19_4.gamma_tilde fp (n + m) n :=
    Theorem19_4.gamma_tilde_nonneg fp hvalid
  have hresidual_nonneg :
      0 <= Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A :=
    mul_nonneg hgamma_nonneg (frobNormRect_nonneg A)
  have heta1_nonneg : 0 <= eta1 := le_trans hresidual_nonneg hresidual
  have hNormBudget : 1 * eta1 + eta1 <= 2 * eta1 := by
    calc
      1 * eta1 + eta1 = 2 * eta1 := by ring
      _ <= 2 * eta1 := le_rfl
  have heta12 : 0 <= eta1 + 2 * eta1 :=
    add_nonneg heta1_nonneg
      (mul_nonneg (by norm_num : (0 : Real) <= 2) heta1_nonneg)
  exact
    qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_same_residual_budget
      (fp := fp) (m := m) (n := n) A hn hvalid
      (eta1 := eta1) (eta2 := 2 * eta1) (rho := rho)
      (c2 := c2) (c3 := c3) (u := u)
      (kappaA := kappaA) (higherOrder := higherOrder)
      hdiag hresidual hRinv hP11 hP21 hQcs hF
      hUorth hWorth hVorth hCdiag hSdiag hTdiag hs hcs
      hNormBudget hGammaColumnBudget heta12 hrho hbudget

/-- Small-unit-roundoff Theorem 19.13 assembly with `eta2` specialized to
`2*eta1`; the residual budget supplies the needed nonnegative radius. -/
theorem
    mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_budget_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 rho c2 c3 kappaA higherOrder : Real}
    {U C S T W : Fin n -> Fin n -> Real}
    {V Qcs F : Fin m -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hP11 :
      paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMul n U (matMul n C (finiteTranspose W)))
    (hP21 :
      paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQcs : Qcs = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1)
    (hGammaColumnBudget :
      2 * Theorem19_4.gamma_tilde fp (n + m) n <= c3 * fp.u)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + 2 * eta1) * rho) +
          ((eta1 + 2 * eta1) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2 c3 fp.u (frobNormRect A) kappaA higherOrder := by
  have hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)) := by
    unfold gammaValid
    have hhalf_lt_one : (1 / 2 : Real) < 1 := by norm_num
    exact lt_of_le_of_lt hsmall hhalf_lt_one
  have hgamma_nonneg :
      0 <= Theorem19_4.gamma_tilde fp (n + m) n :=
    Theorem19_4.gamma_tilde_nonneg fp hvalid
  have hresidual_nonneg :
      0 <= Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A :=
    mul_nonneg hgamma_nonneg (frobNormRect_nonneg A)
  have heta1_nonneg : 0 <= eta1 := le_trans hresidual_nonneg hresidual
  have hNormBudget : 1 * eta1 + eta1 <= 2 * eta1 := by
    calc
      1 * eta1 + eta1 = 2 * eta1 := by ring
      _ <= 2 * eta1 := le_rfl
  have heta12 : 0 <= eta1 + 2 * eta1 :=
    add_nonneg heta1_nonneg
      (mul_nonneg (by norm_num : (0 : Real) <= 2) heta1_nonneg)
  exact
    mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_same_residual_budget_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hsmall
      (eta1 := eta1) (eta2 := 2 * eta1) (rho := rho)
      (c2 := c2) (c3 := c3)
      (kappaA := kappaA) (higherOrder := higherOrder)
      hdiag hresidual hRinv hP11 hP21 hQcs hF
      hUorth hWorth hVorth hCdiag hSdiag hTdiag hs hcs
      hNormBudget hGammaColumnBudget heta12 hrho hbudget

/-- Under the standard small-unit-roundoff guard, the doubled Householder QR
coefficient is bounded by the source-facing `4*k*u` column coefficient. -/
theorem gamma_tilde_two_le_four_index_mul_unit_roundoff_of_small
    (fp : FPModel) {m n : Nat}
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2)) :
    2 * Theorem19_4.gamma_tilde fp (n + m) n <=
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real)) *
        fp.u := by
  have hgamma :
      Theorem19_4.gamma_tilde fp (n + m) n <=
        (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real)) *
          fp.u :=
    Theorem19_4.gamma_tilde_le_two_index_mul_unit_roundoff_of_small
      fp (n + m) n hsmall
  calc
    2 * Theorem19_4.gamma_tilde fp (n + m) n
        <= 2 *
            ((2 *
              ((n * householderConstructApplyGammaIndex (n + m) : Nat) :
                Real)) * fp.u) :=
          mul_le_mul_of_nonneg_left hgamma (by norm_num : (0 : Real) <= 2)
    _ =
        (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real)) *
          fp.u := by ring

/-- Pure-data source-output assembly with the repaired perturbation budget and
the column coefficient budget both specialized to source-facing
small-unit-roundoff constants.

Once the CS/polar route supplies `Problem1912CorrectionMapData`, this wrapper
is the direct data-first analogue of the diagonal-CS fixed-coefficient
assembly: the actual Householder stacked perturbation supplies both top and
bottom residual budgets, and the small-unit-roundoff guard supplies
`c3 = 4*k`. -/
theorem
    qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 rho c2 kappaA higherOrder : Real}
    {Qrepair F : Fin m -> Fin n -> Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hdata :
      Problem1912CorrectionMapData m n
        (paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        Qrepair F)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + 2 * eta1) * rho) +
          ((eta1 + 2 * eta1) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u kappaA higherOrder := by
  have hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)) := by
    unfold gammaValid
    have hhalf_lt_one : (1 / 2 : Real) < 1 := by norm_num
    exact lt_of_le_of_lt hsmall hhalf_lt_one
  have hgamma_nonneg :
      0 <= Theorem19_4.gamma_tilde fp (n + m) n :=
    Theorem19_4.gamma_tilde_nonneg fp hvalid
  have hresidual_nonneg :
      0 <= Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A :=
    mul_nonneg hgamma_nonneg (frobNormRect_nonneg A)
  have heta1_nonneg : 0 <= eta1 := le_trans hresidual_nonneg hresidual
  have hNormBudget : 1 * eta1 + eta1 <= 2 * eta1 := by
    calc
      1 * eta1 + eta1 = 2 * eta1 := by ring
      _ <= 2 * eta1 := le_rfl
  have heta12 : 0 <= eta1 + 2 * eta1 :=
    add_nonneg heta1_nonneg
      (mul_nonneg (by norm_num : (0 : Real) <= 2) heta1_nonneg)
  exact
    qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_budget
      (fp := fp) (m := m) (n := n) A hn hvalid
      (eta1 := eta1) (etaTop := eta1) (etaBottom := eta1)
      (eta2 := 2 * eta1) (rho := rho) (c2 := c2)
      (c3 :=
        4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (u := fp.u) (kappaA := kappaA) (higherOrder := higherOrder)
      hdiag hresidual hRinv hdata hresidual hresidual hNormBudget
      (gamma_tilde_two_column_budget
        (fp := fp) (m := m) (n := n)
        (c3 :=
          4 *
            ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
        (u := fp.u) A
        (gamma_tilde_two_le_four_index_mul_unit_roundoff_of_small
          (fp := fp) (m := m) (n := n) hsmall))
      heta12 hrho hbudget

/-- Small-unit-roundoff pure-data `MGSQRBounds` assembly with
`eta2 = 2*eta1` and the source-facing fixed column coefficient
`c3 = 4*k`. -/
theorem
    mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 rho c2 kappaA higherOrder : Real}
    {Qrepair F : Fin m -> Fin n -> Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hdata :
      Problem1912CorrectionMapData m n
        (paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        Qrepair F)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + 2 * eta1) * rho) +
          ((eta1 + 2 * eta1) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  have hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)) := by
    unfold gammaValid
    have hhalf_lt_one : (1 / 2 : Real) < 1 := by norm_num
    exact lt_of_le_of_lt hsmall hhalf_lt_one
  have hgamma_nonneg :
      0 <= Theorem19_4.gamma_tilde fp (n + m) n :=
    Theorem19_4.gamma_tilde_nonneg fp hvalid
  have hresidual_nonneg :
      0 <= Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A :=
    mul_nonneg hgamma_nonneg (frobNormRect_nonneg A)
  have heta1_nonneg : 0 <= eta1 := le_trans hresidual_nonneg hresidual
  have hNormBudget : 1 * eta1 + eta1 <= 2 * eta1 := by
    calc
      1 * eta1 + eta1 = 2 * eta1 := by ring
      _ <= 2 * eta1 := le_rfl
  have heta12 : 0 <= eta1 + 2 * eta1 :=
    add_nonneg heta1_nonneg
      (mul_nonneg (by norm_num : (0 : Real) <= 2) heta1_nonneg)
  exact
    mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_budget_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hsmall
      (eta1 := eta1) (etaTop := eta1) (etaBottom := eta1)
      (eta2 := 2 * eta1) (rho := rho) (c2 := c2)
      (c3 :=
        4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (kappaA := kappaA) (higherOrder := higherOrder)
      hdiag hresidual hRinv hdata hresidual hresidual hNormBudget
      (gamma_tilde_two_column_budget
        (fp := fp) (m := m) (n := n)
        (c3 :=
          4 *
            ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
        (u := fp.u) A
        (gamma_tilde_two_le_four_index_mul_unit_roundoff_of_small
          (fp := fp) (m := m) (n := n) hsmall))
      heta12 hrho hbudget

/-- Pure-data source-output assembly with determinant nonzero replacing the
pointwise nonzero-diagonal hypothesis for the extracted `R11` block. -/
theorem
    qrsensitivitySourceOutput_of_householder_det_ne_zero_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 rho c2 kappaA higherOrder : Real}
    {Qrepair F : Fin m -> Fin n -> Real}
    (hdet :
      Ne
        (Matrix.det
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
            Matrix (Fin n) (Fin n) Real))
        0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hdata :
      Problem1912CorrectionMapData m n
        (paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        Qrepair F)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + 2 * eta1) * rho) +
          ((eta1 + 2 * eta1) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u kappaA higherOrder := by
  have hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)) := by
    unfold gammaValid
    have hhalf_lt_one : (1 / 2 : Real) < 1 := by norm_num
    exact lt_of_le_of_lt hsmall hhalf_lt_one
  have hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0 :=
    householder_paddedFinInput_R11_diag_ne_zero_of_det_ne_zero
      fp A hn hvalid hdet
  exact
    qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hsmall
      (eta1 := eta1) (rho := rho) (c2 := c2)
      (kappaA := kappaA) (higherOrder := higherOrder)
      (Qrepair := Qrepair) (F := F)
      hdiag hresidual hRinv hdata hrho hbudget

/-- Pure-data `MGSQRBounds` assembly with determinant nonzero replacing the
pointwise nonzero-diagonal hypothesis for the extracted `R11` block. -/
theorem
    mgs_qr_bounds_of_householder_det_ne_zero_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 rho c2 kappaA higherOrder : Real}
    {Qrepair F : Fin m -> Fin n -> Real}
    (hdet :
      Ne
        (Matrix.det
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
            Matrix (Fin n) (Fin n) Real))
        0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hdata :
      Problem1912CorrectionMapData m n
        (paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        Qrepair F)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + 2 * eta1) * rho) +
          ((eta1 + 2 * eta1) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  have hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)) := by
    unfold gammaValid
    have hhalf_lt_one : (1 / 2 : Real) < 1 := by norm_num
    exact lt_of_le_of_lt hsmall hhalf_lt_one
  have hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0 :=
    householder_paddedFinInput_R11_diag_ne_zero_of_det_ne_zero
      fp A hn hvalid hdet
  exact
    mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hsmall
      (eta1 := eta1) (rho := rho) (c2 := c2)
      (kappaA := kappaA) (higherOrder := higherOrder)
      (Qrepair := Qrepair) (F := F)
      hdiag hresidual hRinv hdata hrho hbudget

/-- Frobenius-inverse fallback for the pure-data Householder-stacked,
fixed-coefficient source-output assembly.

This removes the explicit inverse-norm certificate from the pure data-first
fixed-budget route while keeping source diagonal nonbreakdown explicit. -/
theorem
    qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 c2 kappaA higherOrder : Real}
    {Qrepair F : Fin m -> Fin n -> Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hdata :
      Problem1912CorrectionMapData m n
        (paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        Qrepair F)
    (hbudget :
      2 * ((eta1 + 2 * eta1) *
          frobNorm
            (nonsingInv n
              (paddedEconomyR
                (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) +
          ((eta1 + 2 * eta1) *
            frobNorm
              (nonsingInv n
                (paddedEconomyR
                  (fl_householderQRPanel_R fp (n + m) n
                    (paddedFinInput A))))) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u kappaA higherOrder := by
  let R11 : Fin n -> Fin n -> Real :=
    paddedEconomyR
      (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
  have hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        (frobNorm
          (nonsingInv n
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) := by
    simpa [R11] using rectOpNorm2Le_nonsingInv_frobNorm R11
  have hrho :
      0 <=
        frobNorm
          (nonsingInv n
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))) := by
    simpa [R11] using frobNorm_nonneg (nonsingInv n R11)
  exact
    qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hsmall
      (eta1 := eta1)
      (rho :=
        frobNorm
          (nonsingInv n
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))))
      (c2 := c2) (kappaA := kappaA) (higherOrder := higherOrder)
      hdiag hresidual hRinv hdata hrho hbudget

/-- Frobenius-inverse fallback for the pure-data Householder-stacked,
fixed-coefficient `MGSQRBounds` assembly. -/
theorem
    mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 c2 kappaA higherOrder : Real}
    {Qrepair F : Fin m -> Fin n -> Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hdata :
      Problem1912CorrectionMapData m n
        (paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        Qrepair F)
    (hbudget :
      2 * ((eta1 + 2 * eta1) *
          frobNorm
            (nonsingInv n
              (paddedEconomyR
                (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) +
          ((eta1 + 2 * eta1) *
            frobNorm
              (nonsingInv n
                (paddedEconomyR
                  (fl_householderQRPanel_R fp (n + m) n
                    (paddedFinInput A))))) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  let R11 : Fin n -> Fin n -> Real :=
    paddedEconomyR
      (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
  have hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        (frobNorm
          (nonsingInv n
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) := by
    simpa [R11] using rectOpNorm2Le_nonsingInv_frobNorm R11
  have hrho :
      0 <=
        frobNorm
          (nonsingInv n
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))) := by
    simpa [R11] using frobNorm_nonneg (nonsingInv n R11)
  exact
    mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hsmall
      (eta1 := eta1)
      (rho :=
        frobNorm
          (nonsingInv n
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))))
      (c2 := c2) (kappaA := kappaA) (higherOrder := higherOrder)
      hdiag hresidual hRinv hdata hrho hbudget

/-- Frobenius-inverse fallback for the pure-data Householder-stacked route
with determinant nonzero replacing the pointwise nonzero-diagonal hypothesis
for the extracted `R11` block. -/
theorem
    qrsensitivitySourceOutput_of_householder_det_ne_zero_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 c2 kappaA higherOrder : Real}
    {Qrepair F : Fin m -> Fin n -> Real}
    (hdet :
      Ne
        (Matrix.det
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
            Matrix (Fin n) (Fin n) Real))
        0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hdata :
      Problem1912CorrectionMapData m n
        (paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        Qrepair F)
    (hbudget :
      2 * ((eta1 + 2 * eta1) *
          frobNorm
            (nonsingInv n
              (paddedEconomyR
                (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) +
          ((eta1 + 2 * eta1) *
            frobNorm
              (nonsingInv n
                (paddedEconomyR
                  (fl_householderQRPanel_R fp (n + m) n
                    (paddedFinInput A))))) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u kappaA higherOrder := by
  have hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)) := by
    unfold gammaValid
    have hhalf_lt_one : (1 / 2 : Real) < 1 := by norm_num
    exact lt_of_le_of_lt hsmall hhalf_lt_one
  have hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0 :=
    householder_paddedFinInput_R11_diag_ne_zero_of_det_ne_zero
      fp A hn hvalid hdet
  exact
    qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hsmall
      (eta1 := eta1) (c2 := c2) (kappaA := kappaA)
      (higherOrder := higherOrder)
      (Qrepair := Qrepair) (F := F)
      hdiag hresidual hdata hbudget

/-- Frobenius-inverse `MGSQRBounds` fallback for the pure-data
Householder-stacked route with determinant nonzero replacing the pointwise
nonzero-diagonal hypothesis for the extracted `R11` block. -/
theorem
    mgs_qr_bounds_of_householder_det_ne_zero_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 c2 kappaA higherOrder : Real}
    {Qrepair F : Fin m -> Fin n -> Real}
    (hdet :
      Ne
        (Matrix.det
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
            Matrix (Fin n) (Fin n) Real))
        0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hdata :
      Problem1912CorrectionMapData m n
        (paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        Qrepair F)
    (hbudget :
      2 * ((eta1 + 2 * eta1) *
          frobNorm
            (nonsingInv n
              (paddedEconomyR
                (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) +
          ((eta1 + 2 * eta1) *
            frobNorm
              (nonsingInv n
                (paddedEconomyR
                  (fl_householderQRPanel_R fp (n + m) n
                    (paddedFinInput A))))) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  have hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)) := by
    unfold gammaValid
    have hhalf_lt_one : (1 / 2 : Real) < 1 := by norm_num
    exact lt_of_le_of_lt hsmall hhalf_lt_one
  have hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0 :=
    householder_paddedFinInput_R11_diag_ne_zero_of_det_ne_zero
      fp A hn hvalid hdet
  exact
    mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hsmall
      (eta1 := eta1) (c2 := c2) (kappaA := kappaA)
      (higherOrder := higherOrder)
      (Qrepair := Qrepair) (F := F)
      hdiag hresidual hdata hbudget

/-- Source-output assembly from existence of pure Problem 19.12
correction-map data.

This is the weakest data interface for the remaining CS/polar route: once it
proves that some repaired `Q` and correction map `F` exist for the actual
Householder blocks, this wrapper selects them and reuses the fixed-budget
source-output assembly. -/
theorem
    qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 rho c2 kappaA higherOrder : Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hdata :
      Exists fun Qrepair : Fin m -> Fin n -> Real =>
      Exists fun F : Fin m -> Fin n -> Real =>
        Problem1912CorrectionMapData m n
          (paddedEconomyP11
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          Qrepair F)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + 2 * eta1) * rho) +
          ((eta1 + 2 * eta1) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u kappaA higherOrder := by
  cases hdata with
  | intro Qrepair hQ =>
      cases hQ with
      | intro F hdata =>
          exact
            qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
              (fp := fp) (m := m) (n := n) A hn hsmall
              (eta1 := eta1) (rho := rho) (c2 := c2)
              (kappaA := kappaA) (higherOrder := higherOrder)
              (Qrepair := Qrepair) (F := F)
              hdiag hresidual hRinv hdata hrho hbudget

/-- `MGSQRBounds` assembly from existence of pure Problem 19.12
correction-map data, with the fixed small-unit-roundoff constants. -/
theorem
    mgs_qr_bounds_of_householder_upper_diag_correctionMapDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 rho c2 kappaA higherOrder : Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hdata :
      Exists fun Qrepair : Fin m -> Fin n -> Real =>
      Exists fun F : Fin m -> Fin n -> Real =>
        Problem1912CorrectionMapData m n
          (paddedEconomyP11
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          Qrepair F)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + 2 * eta1) * rho) +
          ((eta1 + 2 * eta1) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  cases hdata with
  | intro Qrepair hQ =>
      cases hQ with
      | intro F hdata =>
          exact
            mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
              (fp := fp) (m := m) (n := n) A hn hsmall
              (eta1 := eta1) (rho := rho) (c2 := c2)
              (kappaA := kappaA) (higherOrder := higherOrder)
              (Qrepair := Qrepair) (F := F)
              hdiag hresidual hRinv hdata hrho hbudget

/-- Frobenius-inverse source-output fallback from existence of pure Problem
19.12 correction-map data. -/
theorem
    qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 c2 kappaA higherOrder : Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hdata :
      Exists fun Qrepair : Fin m -> Fin n -> Real =>
      Exists fun F : Fin m -> Fin n -> Real =>
        Problem1912CorrectionMapData m n
          (paddedEconomyP11
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          Qrepair F)
    (hbudget :
      2 * ((eta1 + 2 * eta1) *
          frobNorm
            (nonsingInv n
              (paddedEconomyR
                (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) +
          ((eta1 + 2 * eta1) *
            frobNorm
              (nonsingInv n
                (paddedEconomyR
                  (fl_householderQRPanel_R fp (n + m) n
                    (paddedFinInput A))))) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u kappaA higherOrder := by
  cases hdata with
  | intro Qrepair hQ =>
      cases hQ with
      | intro F hdata =>
          exact
            qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
              (fp := fp) (m := m) (n := n) A hn hsmall
              (eta1 := eta1) (c2 := c2) (kappaA := kappaA)
              (higherOrder := higherOrder)
              (Qrepair := Qrepair) (F := F)
              hdiag hresidual hdata hbudget

/-- Frobenius-inverse `MGSQRBounds` fallback from existence of pure Problem
19.12 correction-map data. -/
theorem
    mgs_qr_bounds_of_householder_upper_diag_correctionMapDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 c2 kappaA higherOrder : Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hdata :
      Exists fun Qrepair : Fin m -> Fin n -> Real =>
      Exists fun F : Fin m -> Fin n -> Real =>
        Problem1912CorrectionMapData m n
          (paddedEconomyP11
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          Qrepair F)
    (hbudget :
      2 * ((eta1 + 2 * eta1) *
          frobNorm
            (nonsingInv n
              (paddedEconomyR
                (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) +
          ((eta1 + 2 * eta1) *
            frobNorm
              (nonsingInv n
                (paddedEconomyR
                  (fl_householderQRPanel_R fp (n + m) n
                    (paddedFinInput A))))) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  cases hdata with
  | intro Qrepair hQ =>
      cases hQ with
      | intro F hdata =>
          exact
            mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
              (fp := fp) (m := m) (n := n) A hn hsmall
              (eta1 := eta1) (c2 := c2) (kappaA := kappaA)
              (higherOrder := higherOrder)
              (Qrepair := Qrepair) (F := F)
              hdiag hresidual hdata hbudget

/-- Source-output assembly from existence of pure Problem 19.12
correction-map data, using determinant nonzero for the extracted `R11` block. -/
theorem
    qrsensitivitySourceOutput_of_householder_det_ne_zero_correctionMapDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 rho c2 kappaA higherOrder : Real}
    (hdet :
      Ne
        (Matrix.det
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
            Matrix (Fin n) (Fin n) Real))
        0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hdata :
      Exists fun Qrepair : Fin m -> Fin n -> Real =>
      Exists fun F : Fin m -> Fin n -> Real =>
        Problem1912CorrectionMapData m n
          (paddedEconomyP11
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          Qrepair F)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + 2 * eta1) * rho) +
          ((eta1 + 2 * eta1) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u kappaA higherOrder := by
  cases hdata with
  | intro Qrepair hQ =>
      cases hQ with
      | intro F hdata =>
          exact
            qrsensitivitySourceOutput_of_householder_det_ne_zero_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
              (fp := fp) (m := m) (n := n) A hn hsmall
              (eta1 := eta1) (rho := rho) (c2 := c2)
              (kappaA := kappaA) (higherOrder := higherOrder)
              (Qrepair := Qrepair) (F := F)
              hdet hresidual hRinv hdata hrho hbudget

/-- `MGSQRBounds` assembly from existence of pure Problem 19.12
correction-map data, using determinant nonzero for the extracted `R11` block. -/
theorem
    mgs_qr_bounds_of_householder_det_ne_zero_correctionMapDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 rho c2 kappaA higherOrder : Real}
    (hdet :
      Ne
        (Matrix.det
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
            Matrix (Fin n) (Fin n) Real))
        0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hdata :
      Exists fun Qrepair : Fin m -> Fin n -> Real =>
      Exists fun F : Fin m -> Fin n -> Real =>
        Problem1912CorrectionMapData m n
          (paddedEconomyP11
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          Qrepair F)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + 2 * eta1) * rho) +
          ((eta1 + 2 * eta1) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  cases hdata with
  | intro Qrepair hQ =>
      cases hQ with
      | intro F hdata =>
          exact
            mgs_qr_bounds_of_householder_det_ne_zero_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
              (fp := fp) (m := m) (n := n) A hn hsmall
              (eta1 := eta1) (rho := rho) (c2 := c2)
              (kappaA := kappaA) (higherOrder := higherOrder)
              (Qrepair := Qrepair) (F := F)
              hdet hresidual hRinv hdata hrho hbudget

/-- Frobenius-inverse source-output fallback from existence of pure Problem
19.12 correction-map data, using determinant nonzero for the extracted `R11`
block. -/
theorem
    qrsensitivitySourceOutput_of_householder_det_ne_zero_correctionMapDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 c2 kappaA higherOrder : Real}
    (hdet :
      Ne
        (Matrix.det
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
            Matrix (Fin n) (Fin n) Real))
        0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hdata :
      Exists fun Qrepair : Fin m -> Fin n -> Real =>
      Exists fun F : Fin m -> Fin n -> Real =>
        Problem1912CorrectionMapData m n
          (paddedEconomyP11
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          Qrepair F)
    (hbudget :
      2 * ((eta1 + 2 * eta1) *
          frobNorm
            (nonsingInv n
              (paddedEconomyR
                (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) +
          ((eta1 + 2 * eta1) *
            frobNorm
              (nonsingInv n
                (paddedEconomyR
                  (fl_householderQRPanel_R fp (n + m) n
                    (paddedFinInput A))))) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u kappaA higherOrder := by
  cases hdata with
  | intro Qrepair hQ =>
      cases hQ with
      | intro F hdata =>
          exact
            qrsensitivitySourceOutput_of_householder_det_ne_zero_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
              (fp := fp) (m := m) (n := n) A hn hsmall
              (eta1 := eta1) (c2 := c2) (kappaA := kappaA)
              (higherOrder := higherOrder)
              (Qrepair := Qrepair) (F := F)
              hdet hresidual hdata hbudget

/-- Frobenius-inverse `MGSQRBounds` fallback from existence of pure Problem
19.12 correction-map data, using determinant nonzero for the extracted `R11`
block. -/
theorem
    mgs_qr_bounds_of_householder_det_ne_zero_correctionMapDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 c2 kappaA higherOrder : Real}
    (hdet :
      Ne
        (Matrix.det
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
            Matrix (Fin n) (Fin n) Real))
        0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hdata :
      Exists fun Qrepair : Fin m -> Fin n -> Real =>
      Exists fun F : Fin m -> Fin n -> Real =>
        Problem1912CorrectionMapData m n
          (paddedEconomyP11
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          Qrepair F)
    (hbudget :
      2 * ((eta1 + 2 * eta1) *
          frobNorm
            (nonsingInv n
              (paddedEconomyR
                (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) +
          ((eta1 + 2 * eta1) *
            frobNorm
              (nonsingInv n
                (paddedEconomyR
                  (fl_householderQRPanel_R fp (n + m) n
                    (paddedFinInput A))))) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  cases hdata with
  | intro Qrepair hQ =>
      cases hQ with
      | intro F hdata =>
          exact
            mgs_qr_bounds_of_householder_det_ne_zero_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
              (fp := fp) (m := m) (n := n) A hn hsmall
              (eta1 := eta1) (c2 := c2) (kappaA := kappaA)
              (higherOrder := higherOrder)
              (Qrepair := Qrepair) (F := F)
              hdet hresidual hdata hbudget

/-- Concrete source-output assembly using the general CS/polar witness for the
actual padded Householder economy blocks. -/
theorem
    qrsensitivitySourceOutput_of_householder_upper_diag_csPolarRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 rho c2 kappaA higherOrder : Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + 2 * eta1) * rho) +
          ((eta1 + 2 * eta1) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u kappaA higherOrder := by
  have hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)) := by
    unfold gammaValid
    have hhalf_lt_one : (1 / 2 : Real) < 1 := by norm_num
    exact lt_of_le_of_lt hsmall hhalf_lt_one
  exact
    qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hsmall
      (eta1 := eta1) (rho := rho) (c2 := c2)
      (kappaA := kappaA) (higherOrder := higherOrder)
      hdiag hresidual hRinv
      (householder_paddedFinInput_correctionMapData_exists
        fp A hn hnm hvalid)
      hrho hbudget

/-- Concrete `MGSQRBounds` assembly using the general CS/polar witness for the
actual padded Householder economy blocks. -/
theorem
    mgs_qr_bounds_of_householder_upper_diag_csPolarRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 rho c2 kappaA higherOrder : Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + 2 * eta1) * rho) +
          ((eta1 + 2 * eta1) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  have hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)) := by
    unfold gammaValid
    have hhalf_lt_one : (1 / 2 : Real) < 1 := by norm_num
    exact lt_of_le_of_lt hsmall hhalf_lt_one
  exact
    mgs_qr_bounds_of_householder_upper_diag_correctionMapDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hsmall
      (eta1 := eta1) (rho := rho) (c2 := c2)
      (kappaA := kappaA) (higherOrder := higherOrder)
      hdiag hresidual hRinv
      (householder_paddedFinInput_correctionMapData_exists
        fp A hn hnm hvalid)
      hrho hbudget

/-- Frobenius-inverse source-output fallback using the general CS/polar witness
for the actual padded Householder economy blocks. -/
theorem
    qrsensitivitySourceOutput_of_householder_upper_diag_csPolarRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 c2 kappaA higherOrder : Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hbudget :
      2 * ((eta1 + 2 * eta1) *
          frobNorm
            (nonsingInv n
              (paddedEconomyR
                (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) +
          ((eta1 + 2 * eta1) *
            frobNorm
              (nonsingInv n
                (paddedEconomyR
                  (fl_householderQRPanel_R fp (n + m) n
                    (paddedFinInput A))))) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u kappaA higherOrder := by
  have hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)) := by
    unfold gammaValid
    have hhalf_lt_one : (1 / 2 : Real) < 1 := by norm_num
    exact lt_of_le_of_lt hsmall hhalf_lt_one
  exact
    qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hsmall
      (eta1 := eta1) (c2 := c2) (kappaA := kappaA)
      (higherOrder := higherOrder)
      hdiag hresidual
      (householder_paddedFinInput_correctionMapData_exists
        fp A hn hnm hvalid)
      hbudget

/-- Frobenius-inverse `MGSQRBounds` fallback using the general CS/polar witness
for the actual padded Householder economy blocks. -/
theorem
    mgs_qr_bounds_of_householder_upper_diag_csPolarRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 c2 kappaA higherOrder : Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hbudget :
      2 * ((eta1 + 2 * eta1) *
          frobNorm
            (nonsingInv n
              (paddedEconomyR
                (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) +
          ((eta1 + 2 * eta1) *
            frobNorm
              (nonsingInv n
                (paddedEconomyR
                  (fl_householderQRPanel_R fp (n + m) n
                    (paddedFinInput A))))) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  have hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)) := by
    unfold gammaValid
    have hhalf_lt_one : (1 / 2 : Real) < 1 := by norm_num
    exact lt_of_le_of_lt hsmall hhalf_lt_one
  exact
    mgs_qr_bounds_of_householder_upper_diag_correctionMapDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hsmall
      (eta1 := eta1) (c2 := c2) (kappaA := kappaA)
      (higherOrder := higherOrder)
      hdiag hresidual
      (householder_paddedFinInput_correctionMapData_exists
        fp A hn hnm hvalid)
      hbudget

/-- Determinant-nonzero source-output assembly using the general CS/polar
witness for the actual padded Householder economy blocks. -/
theorem
    qrsensitivitySourceOutput_of_householder_det_ne_zero_csPolarRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 rho c2 kappaA higherOrder : Real}
    (hdet :
      Ne
        (Matrix.det
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
            Matrix (Fin n) (Fin n) Real))
        0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + 2 * eta1) * rho) +
          ((eta1 + 2 * eta1) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u kappaA higherOrder := by
  have hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)) := by
    unfold gammaValid
    have hhalf_lt_one : (1 / 2 : Real) < 1 := by norm_num
    exact lt_of_le_of_lt hsmall hhalf_lt_one
  exact
    qrsensitivitySourceOutput_of_householder_det_ne_zero_correctionMapDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hsmall
      (eta1 := eta1) (rho := rho) (c2 := c2)
      (kappaA := kappaA) (higherOrder := higherOrder)
      hdet hresidual hRinv
      (householder_paddedFinInput_correctionMapData_exists
        fp A hn hnm hvalid)
      hrho hbudget

/-- Determinant-nonzero `MGSQRBounds` assembly using the general CS/polar
witness for the actual padded Householder economy blocks. -/
theorem
    mgs_qr_bounds_of_householder_det_ne_zero_csPolarRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 rho c2 kappaA higherOrder : Real}
    (hdet :
      Ne
        (Matrix.det
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
            Matrix (Fin n) (Fin n) Real))
        0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + 2 * eta1) * rho) +
          ((eta1 + 2 * eta1) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  have hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)) := by
    unfold gammaValid
    have hhalf_lt_one : (1 / 2 : Real) < 1 := by norm_num
    exact lt_of_le_of_lt hsmall hhalf_lt_one
  exact
    mgs_qr_bounds_of_householder_det_ne_zero_correctionMapDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hsmall
      (eta1 := eta1) (rho := rho) (c2 := c2)
      (kappaA := kappaA) (higherOrder := higherOrder)
      hdet hresidual hRinv
      (householder_paddedFinInput_correctionMapData_exists
        fp A hn hnm hvalid)
      hrho hbudget

/-- Determinant-nonzero Frobenius-inverse source-output fallback using the
general CS/polar witness for the actual padded Householder economy blocks. -/
theorem
    qrsensitivitySourceOutput_of_householder_det_ne_zero_csPolarRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 c2 kappaA higherOrder : Real}
    (hdet :
      Ne
        (Matrix.det
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
            Matrix (Fin n) (Fin n) Real))
        0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hbudget :
      2 * ((eta1 + 2 * eta1) *
          frobNorm
            (nonsingInv n
              (paddedEconomyR
                (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) +
          ((eta1 + 2 * eta1) *
            frobNorm
              (nonsingInv n
                (paddedEconomyR
                  (fl_householderQRPanel_R fp (n + m) n
                    (paddedFinInput A))))) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u kappaA higherOrder := by
  have hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)) := by
    unfold gammaValid
    have hhalf_lt_one : (1 / 2 : Real) < 1 := by norm_num
    exact lt_of_le_of_lt hsmall hhalf_lt_one
  exact
    qrsensitivitySourceOutput_of_householder_det_ne_zero_correctionMapDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hsmall
      (eta1 := eta1) (c2 := c2) (kappaA := kappaA)
      (higherOrder := higherOrder)
      hdet hresidual
      (householder_paddedFinInput_correctionMapData_exists
        fp A hn hnm hvalid)
      hbudget

/-- Determinant-nonzero Frobenius-inverse `MGSQRBounds` fallback using the
general CS/polar witness for the actual padded Householder economy blocks. -/
theorem
    mgs_qr_bounds_of_householder_det_ne_zero_csPolarRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 c2 kappaA higherOrder : Real}
    (hdet :
      Ne
        (Matrix.det
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
            Matrix (Fin n) (Fin n) Real))
        0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hbudget :
      2 * ((eta1 + 2 * eta1) *
          frobNorm
            (nonsingInv n
              (paddedEconomyR
                (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) +
          ((eta1 + 2 * eta1) *
            frobNorm
              (nonsingInv n
                (paddedEconomyR
                  (fl_householderQRPanel_R fp (n + m) n
                    (paddedFinInput A))))) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  have hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)) := by
    unfold gammaValid
    have hhalf_lt_one : (1 / 2 : Real) < 1 := by norm_num
    exact lt_of_le_of_lt hsmall hhalf_lt_one
  exact
    mgs_qr_bounds_of_householder_det_ne_zero_correctionMapDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hsmall
      (eta1 := eta1) (c2 := c2) (kappaA := kappaA)
      (higherOrder := higherOrder)
      hdet hresidual
      (householder_paddedFinInput_correctionMapData_exists
        fp A hn hnm hvalid)
      hbudget

/-- Source-output assembly from a packaged diagonal CS factor-data certificate.

This is the source-shaped form of the pure-data fixed-budget wrapper: the
remaining CS/polar existence theorem only has to provide one
`Problem1912CSDiagonalFactorData` object for the Householder block. -/
theorem
    qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalFactorDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 rho c2 kappaA higherOrder : Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hcsdata :
      Problem1912CSDiagonalFactorData m n
        (paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A))))
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + 2 * eta1) * rho) +
          ((eta1 + 2 * eta1) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u kappaA higherOrder := by
  exact
    qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hsmall
      (eta1 := eta1) (rho := rho) (c2 := c2)
      (kappaA := kappaA) (higherOrder := higherOrder)
      (Qrepair := hcsdata.q) (F := hcsdata.f)
      hdiag hresidual hRinv
      (problem1912_correctionMapData_of_csDiagonalFactorData hcsdata)
      hrho hbudget

/-- `MGSQRBounds` assembly from a packaged diagonal CS factor-data certificate,
with the fixed small-unit-roundoff constants. -/
theorem
    mgs_qr_bounds_of_householder_upper_diag_csDiagonalFactorDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 rho c2 kappaA higherOrder : Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hcsdata :
      Problem1912CSDiagonalFactorData m n
        (paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A))))
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + 2 * eta1) * rho) +
          ((eta1 + 2 * eta1) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  exact
    mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hsmall
      (eta1 := eta1) (rho := rho) (c2 := c2)
      (kappaA := kappaA) (higherOrder := higherOrder)
      (Qrepair := hcsdata.q) (F := hcsdata.f)
      hdiag hresidual hRinv
      (problem1912_correctionMapData_of_csDiagonalFactorData hcsdata)
      hrho hbudget

/-- Frobenius-inverse source-output fallback from packaged diagonal CS
factor-data. -/
theorem
    qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalFactorDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 c2 kappaA higherOrder : Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hcsdata :
      Problem1912CSDiagonalFactorData m n
        (paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A))))
    (hbudget :
      2 * ((eta1 + 2 * eta1) *
          frobNorm
            (nonsingInv n
              (paddedEconomyR
                (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) +
          ((eta1 + 2 * eta1) *
            frobNorm
              (nonsingInv n
                (paddedEconomyR
                  (fl_householderQRPanel_R fp (n + m) n
                    (paddedFinInput A))))) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u kappaA higherOrder := by
  exact
    qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hsmall
      (eta1 := eta1) (c2 := c2) (kappaA := kappaA)
      (higherOrder := higherOrder)
      (Qrepair := hcsdata.q) (F := hcsdata.f)
      hdiag hresidual
      (problem1912_correctionMapData_of_csDiagonalFactorData hcsdata)
      hbudget

/-- Frobenius-inverse `MGSQRBounds` fallback from packaged diagonal CS
factor-data. -/
theorem
    mgs_qr_bounds_of_householder_upper_diag_csDiagonalFactorDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 c2 kappaA higherOrder : Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hcsdata :
      Problem1912CSDiagonalFactorData m n
        (paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A))))
    (hbudget :
      2 * ((eta1 + 2 * eta1) *
          frobNorm
            (nonsingInv n
              (paddedEconomyR
                (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) +
          ((eta1 + 2 * eta1) *
            frobNorm
              (nonsingInv n
                (paddedEconomyR
                  (fl_householderQRPanel_R fp (n + m) n
                    (paddedFinInput A))))) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  exact
    mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hsmall
      (eta1 := eta1) (c2 := c2) (kappaA := kappaA)
      (higherOrder := higherOrder)
      (Qrepair := hcsdata.q) (F := hcsdata.f)
      hdiag hresidual
      (problem1912_correctionMapData_of_csDiagonalFactorData hcsdata)
      hbudget

/-- Source-output assembly from existence of packaged diagonal CS factor data.

This is the form expected after the remaining CS/polar theorem proves that the
Householder block admits a source-shaped factor-data payload. -/
theorem
    qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalFactorDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 rho c2 kappaA higherOrder : Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hcsdata :
      Nonempty
        (Problem1912CSDiagonalFactorData m n
          (paddedEconomyP11
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))))
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + 2 * eta1) * rho) +
          ((eta1 + 2 * eta1) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u kappaA higherOrder := by
  cases hcsdata with
  | intro hcsdata =>
      exact
        qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalFactorDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
          (fp := fp) (m := m) (n := n) A hn hsmall
          (eta1 := eta1) (rho := rho) (c2 := c2)
          (kappaA := kappaA) (higherOrder := higherOrder)
          hdiag hresidual hRinv hcsdata hrho hbudget

/-- `MGSQRBounds` assembly from existence of packaged diagonal CS factor data,
with the fixed small-unit-roundoff constants. -/
theorem
    mgs_qr_bounds_of_householder_upper_diag_csDiagonalFactorDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 rho c2 kappaA higherOrder : Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hcsdata :
      Nonempty
        (Problem1912CSDiagonalFactorData m n
          (paddedEconomyP11
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))))
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + 2 * eta1) * rho) +
          ((eta1 + 2 * eta1) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  cases hcsdata with
  | intro hcsdata =>
      exact
        mgs_qr_bounds_of_householder_upper_diag_csDiagonalFactorDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
          (fp := fp) (m := m) (n := n) A hn hsmall
          (eta1 := eta1) (rho := rho) (c2 := c2)
          (kappaA := kappaA) (higherOrder := higherOrder)
          hdiag hresidual hRinv hcsdata hrho hbudget

/-- Frobenius-inverse source-output fallback from existence of packaged
diagonal CS factor data. -/
theorem
    qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalFactorDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 c2 kappaA higherOrder : Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hcsdata :
      Nonempty
        (Problem1912CSDiagonalFactorData m n
          (paddedEconomyP11
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))))
    (hbudget :
      2 * ((eta1 + 2 * eta1) *
          frobNorm
            (nonsingInv n
              (paddedEconomyR
                (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) +
          ((eta1 + 2 * eta1) *
            frobNorm
              (nonsingInv n
                (paddedEconomyR
                  (fl_householderQRPanel_R fp (n + m) n
                    (paddedFinInput A))))) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u kappaA higherOrder := by
  cases hcsdata with
  | intro hcsdata =>
      exact
        qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalFactorDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
          (fp := fp) (m := m) (n := n) A hn hsmall
          (eta1 := eta1) (c2 := c2) (kappaA := kappaA)
          (higherOrder := higherOrder)
          hdiag hresidual hcsdata hbudget

/-- Frobenius-inverse `MGSQRBounds` fallback from existence of packaged
diagonal CS factor data. -/
theorem
    mgs_qr_bounds_of_householder_upper_diag_csDiagonalFactorDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 c2 kappaA higherOrder : Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hcsdata :
      Nonempty
        (Problem1912CSDiagonalFactorData m n
          (paddedEconomyP11
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))))
    (hbudget :
      2 * ((eta1 + 2 * eta1) *
          frobNorm
            (nonsingInv n
              (paddedEconomyR
                (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) +
          ((eta1 + 2 * eta1) *
            frobNorm
              (nonsingInv n
                (paddedEconomyR
                  (fl_householderQRPanel_R fp (n + m) n
                    (paddedFinInput A))))) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  cases hcsdata with
  | intro hcsdata =>
      exact
        mgs_qr_bounds_of_householder_upper_diag_csDiagonalFactorDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
          (fp := fp) (m := m) (n := n) A hn hsmall
          (eta1 := eta1) (c2 := c2) (kappaA := kappaA)
          (higherOrder := higherOrder)
          hdiag hresidual hcsdata hbudget

/-- Source-output assembly from packaged diagonal CS factor data, using
determinant nonzero for the extracted `R11` block. -/
theorem
    qrsensitivitySourceOutput_of_householder_det_ne_zero_csDiagonalFactorDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 rho c2 kappaA higherOrder : Real}
    (hdet :
      Ne
        (Matrix.det
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
            Matrix (Fin n) (Fin n) Real))
        0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hcsdata :
      Problem1912CSDiagonalFactorData m n
        (paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A))))
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + 2 * eta1) * rho) +
          ((eta1 + 2 * eta1) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u kappaA higherOrder := by
  exact
    qrsensitivitySourceOutput_of_householder_det_ne_zero_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hsmall
      (eta1 := eta1) (rho := rho) (c2 := c2)
      (kappaA := kappaA) (higherOrder := higherOrder)
      (Qrepair := hcsdata.q) (F := hcsdata.f)
      hdet hresidual hRinv
      (problem1912_correctionMapData_of_csDiagonalFactorData hcsdata)
      hrho hbudget

/-- `MGSQRBounds` assembly from packaged diagonal CS factor data, using
determinant nonzero for the extracted `R11` block. -/
theorem
    mgs_qr_bounds_of_householder_det_ne_zero_csDiagonalFactorDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 rho c2 kappaA higherOrder : Real}
    (hdet :
      Ne
        (Matrix.det
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
            Matrix (Fin n) (Fin n) Real))
        0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hcsdata :
      Problem1912CSDiagonalFactorData m n
        (paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A))))
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + 2 * eta1) * rho) +
          ((eta1 + 2 * eta1) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  exact
    mgs_qr_bounds_of_householder_det_ne_zero_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hsmall
      (eta1 := eta1) (rho := rho) (c2 := c2)
      (kappaA := kappaA) (higherOrder := higherOrder)
      (Qrepair := hcsdata.q) (F := hcsdata.f)
      hdet hresidual hRinv
      (problem1912_correctionMapData_of_csDiagonalFactorData hcsdata)
      hrho hbudget

/-- Frobenius-inverse source-output fallback from packaged diagonal CS factor
data, using determinant nonzero for the extracted `R11` block. -/
theorem
    qrsensitivitySourceOutput_of_householder_det_ne_zero_csDiagonalFactorDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 c2 kappaA higherOrder : Real}
    (hdet :
      Ne
        (Matrix.det
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
            Matrix (Fin n) (Fin n) Real))
        0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hcsdata :
      Problem1912CSDiagonalFactorData m n
        (paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A))))
    (hbudget :
      2 * ((eta1 + 2 * eta1) *
          frobNorm
            (nonsingInv n
              (paddedEconomyR
                (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) +
          ((eta1 + 2 * eta1) *
            frobNorm
              (nonsingInv n
                (paddedEconomyR
                  (fl_householderQRPanel_R fp (n + m) n
                    (paddedFinInput A))))) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u kappaA higherOrder := by
  exact
    qrsensitivitySourceOutput_of_householder_det_ne_zero_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hsmall
      (eta1 := eta1) (c2 := c2) (kappaA := kappaA)
      (higherOrder := higherOrder)
      (Qrepair := hcsdata.q) (F := hcsdata.f)
      hdet hresidual
      (problem1912_correctionMapData_of_csDiagonalFactorData hcsdata)
      hbudget

/-- Frobenius-inverse `MGSQRBounds` fallback from packaged diagonal CS factor
data, using determinant nonzero for the extracted `R11` block. -/
theorem
    mgs_qr_bounds_of_householder_det_ne_zero_csDiagonalFactorDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 c2 kappaA higherOrder : Real}
    (hdet :
      Ne
        (Matrix.det
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
            Matrix (Fin n) (Fin n) Real))
        0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hcsdata :
      Problem1912CSDiagonalFactorData m n
        (paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
        (paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A))))
    (hbudget :
      2 * ((eta1 + 2 * eta1) *
          frobNorm
            (nonsingInv n
              (paddedEconomyR
                (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) +
          ((eta1 + 2 * eta1) *
            frobNorm
              (nonsingInv n
                (paddedEconomyR
                  (fl_householderQRPanel_R fp (n + m) n
                    (paddedFinInput A))))) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  exact
    mgs_qr_bounds_of_householder_det_ne_zero_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hsmall
      (eta1 := eta1) (c2 := c2) (kappaA := kappaA)
      (higherOrder := higherOrder)
      (Qrepair := hcsdata.q) (F := hcsdata.f)
      hdet hresidual
      (problem1912_correctionMapData_of_csDiagonalFactorData hcsdata)
      hbudget

/-- Source-output assembly from existence of packaged diagonal CS factor data,
using determinant nonzero for the extracted `R11` block. -/
theorem
    qrsensitivitySourceOutput_of_householder_det_ne_zero_csDiagonalFactorDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 rho c2 kappaA higherOrder : Real}
    (hdet :
      Ne
        (Matrix.det
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
            Matrix (Fin n) (Fin n) Real))
        0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hcsdata :
      Nonempty
        (Problem1912CSDiagonalFactorData m n
          (paddedEconomyP11
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))))
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + 2 * eta1) * rho) +
          ((eta1 + 2 * eta1) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u kappaA higherOrder := by
  cases hcsdata with
  | intro hcsdata =>
      exact
        qrsensitivitySourceOutput_of_householder_det_ne_zero_csDiagonalFactorDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
          (fp := fp) (m := m) (n := n) A hn hsmall
          (eta1 := eta1) (rho := rho) (c2 := c2)
          (kappaA := kappaA) (higherOrder := higherOrder)
          hdet hresidual hRinv hcsdata hrho hbudget

/-- `MGSQRBounds` assembly from existence of packaged diagonal CS factor data,
using determinant nonzero for the extracted `R11` block. -/
theorem
    mgs_qr_bounds_of_householder_det_ne_zero_csDiagonalFactorDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 rho c2 kappaA higherOrder : Real}
    (hdet :
      Ne
        (Matrix.det
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
            Matrix (Fin n) (Fin n) Real))
        0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hcsdata :
      Nonempty
        (Problem1912CSDiagonalFactorData m n
          (paddedEconomyP11
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))))
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + 2 * eta1) * rho) +
          ((eta1 + 2 * eta1) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  cases hcsdata with
  | intro hcsdata =>
      exact
        mgs_qr_bounds_of_householder_det_ne_zero_csDiagonalFactorDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
          (fp := fp) (m := m) (n := n) A hn hsmall
          (eta1 := eta1) (rho := rho) (c2 := c2)
          (kappaA := kappaA) (higherOrder := higherOrder)
          hdet hresidual hRinv hcsdata hrho hbudget

/-- Frobenius-inverse source-output fallback from existence of packaged
diagonal CS factor data, using determinant nonzero for the extracted `R11`
block. -/
theorem
    qrsensitivitySourceOutput_of_householder_det_ne_zero_csDiagonalFactorDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 c2 kappaA higherOrder : Real}
    (hdet :
      Ne
        (Matrix.det
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
            Matrix (Fin n) (Fin n) Real))
        0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hcsdata :
      Nonempty
        (Problem1912CSDiagonalFactorData m n
          (paddedEconomyP11
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))))
    (hbudget :
      2 * ((eta1 + 2 * eta1) *
          frobNorm
            (nonsingInv n
              (paddedEconomyR
                (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) +
          ((eta1 + 2 * eta1) *
            frobNorm
              (nonsingInv n
                (paddedEconomyR
                  (fl_householderQRPanel_R fp (n + m) n
                    (paddedFinInput A))))) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u kappaA higherOrder := by
  cases hcsdata with
  | intro hcsdata =>
      exact
        qrsensitivitySourceOutput_of_householder_det_ne_zero_csDiagonalFactorDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
          (fp := fp) (m := m) (n := n) A hn hsmall
          (eta1 := eta1) (c2 := c2) (kappaA := kappaA)
          (higherOrder := higherOrder)
          hdet hresidual hcsdata hbudget

/-- Frobenius-inverse `MGSQRBounds` fallback from existence of packaged
diagonal CS factor data, using determinant nonzero for the extracted `R11`
block. -/
theorem
    mgs_qr_bounds_of_householder_det_ne_zero_csDiagonalFactorDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 c2 kappaA higherOrder : Real}
    (hdet :
      Ne
        (Matrix.det
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
            Matrix (Fin n) (Fin n) Real))
        0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hcsdata :
      Nonempty
        (Problem1912CSDiagonalFactorData m n
          (paddedEconomyP11
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
          (paddedEconomyQ
            (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))))
    (hbudget :
      2 * ((eta1 + 2 * eta1) *
          frobNorm
            (nonsingInv n
              (paddedEconomyR
                (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) +
          ((eta1 + 2 * eta1) *
            frobNorm
              (nonsingInv n
                (paddedEconomyR
                  (fl_householderQRPanel_R fp (n + m) n
                    (paddedFinInput A))))) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  cases hcsdata with
  | intro hcsdata =>
      exact
        mgs_qr_bounds_of_householder_det_ne_zero_csDiagonalFactorDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
          (fp := fp) (m := m) (n := n) A hn hsmall
          (eta1 := eta1) (c2 := c2) (kappaA := kappaA)
          (higherOrder := higherOrder)
          hdet hresidual hcsdata hbudget

/-- Concrete diagonal-CS source-output assembly with both the repaired
perturbation budget and the column coefficient budget specialized to the
standard small-unit-roundoff constants. -/
theorem
    qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 rho c2 kappaA higherOrder : Real}
    {U C S T W : Fin n -> Fin n -> Real}
    {V Qcs F : Fin m -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hP11 :
      paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMul n U (matMul n C (finiteTranspose W)))
    (hP21 :
      paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQcs : Qcs = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + 2 * eta1) * rho) +
          ((eta1 + 2 * eta1) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u kappaA higherOrder := by
  have hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)) := by
    unfold gammaValid
    have hhalf_lt_one : (1 / 2 : Real) < 1 := by norm_num
    exact lt_of_le_of_lt hsmall hhalf_lt_one
  exact
    qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_budget
      (fp := fp) (m := m) (n := n) A hn hvalid
      (eta1 := eta1) (rho := rho) (c2 := c2)
      (c3 :=
        4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (u := fp.u) (kappaA := kappaA) (higherOrder := higherOrder)
      hdiag hresidual hRinv hP11 hP21 hQcs hF
      hUorth hWorth hVorth hCdiag hSdiag hTdiag hs hcs
      (gamma_tilde_two_le_four_index_mul_unit_roundoff_of_small
        (fp := fp) (m := m) (n := n) hsmall)
      hrho hbudget

/-- Small-unit-roundoff Theorem 19.13 assembly with the repaired perturbation
budget and the column coefficient budget both specialized to source-facing
small-unit-roundoff constants. -/
theorem
    mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 rho c2 kappaA higherOrder : Real}
    {U C S T W : Fin n -> Fin n -> Real}
    {V Qcs F : Fin m -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        rho)
    (hP11 :
      paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMul n U (matMul n C (finiteTranspose W)))
    (hP21 :
      paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQcs : Qcs = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + 2 * eta1) * rho) +
          ((eta1 + 2 * eta1) * rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  exact
    mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_budget_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hsmall
      (eta1 := eta1) (rho := rho) (c2 := c2)
      (c3 :=
        4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (kappaA := kappaA) (higherOrder := higherOrder)
      hdiag hresidual hRinv hP11 hP21 hQcs hF
      hUorth hWorth hVorth hCdiag hSdiag hTdiag hs hcs
      (gamma_tilde_two_le_four_index_mul_unit_roundoff_of_small
        (fp := fp) (m := m) (n := n) hsmall)
      hrho hbudget

/-- Frobenius-inverse fallback for the concrete Householder-stacked,
fixed-coefficient diagonal-CS source-output assembly.

This keeps the CS/polar repair data and source diagonal nonbreakdown explicit,
but discharges the inverse-norm certificate by taking
`rho = ||nonsingInv R11||_F`. -/
theorem
    qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 c2 kappaA higherOrder : Real}
    {U C S T W : Fin n -> Fin n -> Real}
    {V Qcs F : Fin m -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hP11 :
      paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMul n U (matMul n C (finiteTranspose W)))
    (hP21 :
      paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQcs : Qcs = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1)
    (hbudget :
      2 * ((eta1 + 2 * eta1) *
          frobNorm
            (nonsingInv n
              (paddedEconomyR
                (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) +
          ((eta1 + 2 * eta1) *
            frobNorm
              (nonsingInv n
                (paddedEconomyR
                  (fl_householderQRPanel_R fp (n + m) n
                    (paddedFinInput A))))) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    QRSensitivitySourceOutput m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u kappaA higherOrder := by
  let R11 : Fin n -> Fin n -> Real :=
    paddedEconomyR
      (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
  have hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        (frobNorm
          (nonsingInv n
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) := by
    simpa [R11] using rectOpNorm2Le_nonsingInv_frobNorm R11
  have hrho :
      0 <=
        frobNorm
          (nonsingInv n
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))) := by
    simpa [R11] using frobNorm_nonneg (nonsingInv n R11)
  exact
    qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hsmall
      (eta1 := eta1)
      (rho :=
        frobNorm
          (nonsingInv n
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))))
      (c2 := c2) (kappaA := kappaA) (higherOrder := higherOrder)
      hdiag hresidual hRinv hP11 hP21 hQcs hF hUorth hWorth hVorth
      hCdiag hSdiag hTdiag hs hcs hrho hbudget

/-- Frobenius-inverse fallback for the concrete Householder-stacked,
fixed-coefficient `MGSQRBounds` assembly.

This removes the separate inverse-norm certificate from the current fallback
route while leaving the sharper source condition-number estimate as the next
source-facing refinement. -/
theorem
    mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 c2 kappaA higherOrder : Real}
    {U C S T W : Fin n -> Fin n -> Real}
    {V Qcs F : Fin m -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hP11 :
      paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMul n U (matMul n C (finiteTranspose W)))
    (hP21 :
      paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQcs : Qcs = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1)
    (hbudget :
      2 * ((eta1 + 2 * eta1) *
          frobNorm
            (nonsingInv n
              (paddedEconomyR
                (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) +
          ((eta1 + 2 * eta1) *
            frobNorm
              (nonsingInv n
                (paddedEconomyR
                  (fl_householderQRPanel_R fp (n + m) n
                    (paddedFinInput A))))) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  let R11 : Fin n -> Fin n -> Real :=
    paddedEconomyR
      (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
  have hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        (frobNorm
          (nonsingInv n
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) := by
    simpa [R11] using rectOpNorm2Le_nonsingInv_frobNorm R11
  have hrho :
      0 <=
        frobNorm
          (nonsingInv n
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))) := by
    simpa [R11] using frobNorm_nonneg (nonsingInv n R11)
  exact
    mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hsmall
      (eta1 := eta1)
      (rho :=
        frobNorm
          (nonsingInv n
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))))
      (c2 := c2) (kappaA := kappaA) (higherOrder := higherOrder)
      hdiag hresidual hRinv hP11 hP21 hQcs hF hUorth hWorth hVorth
      hCdiag hSdiag hTdiag hs hcs hrho hbudget

/-- Small-unit-roundoff Theorem 19.13 fallback assembly using the Frobenius
norm of `nonsingInv R11` as the inverse budget.

This is weaker than the intended source condition-number estimate, but it
removes the separate inverse-norm certificate from the concrete diagonal-CS
route and leaves the sharp budget as the remaining source-facing refinement. -/
theorem
    mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_frobInv_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {eta1 eta2 c2 c3 kappaA higherOrder : Real}
    {U C S T W : Fin n -> Fin n -> Real}
    {V Qcs F : Fin m -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hdiag :
      forall i : Fin n,
        Ne
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
            i i)
          0)
    (hresidual :
      Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A <= eta1)
    (hP11 :
      paddedEconomyP11
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMul n U (matMul n C (finiteTranspose W)))
    (hP21 :
      paddedEconomyQ
          (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)) =
        matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQcs : Qcs = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1)
    (hnorm :
      forall (dTop : Fin n -> Fin n -> Real)
          (dBottom : Fin m -> Fin n -> Real),
        dTop =
          matMul n
            (paddedEconomyP11
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        (fun i j => A i j + dBottom i j) =
          matMulRect m n n
            (paddedEconomyQ
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        rectOpNorm2Le
          (fun i j => matMulRect m n n F dTop i j + dBottom i j)
          eta2)
    (hcol :
      forall (dTop : Fin n -> Fin n -> Real)
          (dBottom : Fin m -> Fin n -> Real),
        dTop =
          matMul n
            (paddedEconomyP11
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        (fun i j => A i j + dBottom i j) =
          matMulRect m n n
            (paddedEconomyQ
              (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))) ->
        forall j,
          columnFrob
              (fun i j => matMulRect m n n F dTop i j + dBottom i j)
              j <=
            c3 * fp.u * columnFrob A j)
    (heta12 : 0 <= eta1 + eta2)
    (hbudget :
      2 * ((eta1 + eta2) *
          frobNorm
            (nonsingInv n
              (paddedEconomyR
                (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) +
          ((eta1 + eta2) *
            frobNorm
              (nonsingInv n
                (paddedEconomyR
                  (fl_householderQRPanel_R fp (n + m) n
                    (paddedFinInput A))))) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (paddedEconomyR
        (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2 c3 fp.u (frobNormRect A) kappaA higherOrder := by
  let R11 : Fin n -> Fin n -> Real :=
    paddedEconomyR
      (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
  have hRinv :
      rectOpNorm2Le
        (nonsingInv n
          (paddedEconomyR
            (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))
        (frobNorm
          (nonsingInv n
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))))) := by
    simpa [R11] using rectOpNorm2Le_nonsingInv_frobNorm R11
  have hrho :
      0 <=
        frobNorm
          (nonsingInv n
            (paddedEconomyR
              (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)))) := by
    simpa [R11] using frobNorm_nonneg (nonsingInv n R11)
  exact
    mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_small_unit_roundoff
      fp A hn hsmall hdiag hresidual hRinv hP11 hP21 hQcs hF hUorth
      hWorth hVorth hCdiag hSdiag hTdiag hs hcs hnorm hcol heta12
      hrho hbudget

/-- Source-nonbreakdown form of the chapter-facing Theorem 19.13 assembly.

The diagonal-nonzero hypothesis is stated directly on the extracted `R11`
block. The CS/polar repair witness and the fallback `nonsingInv` operator
certificate are selected internally; the remaining visible obligation is the
Frobenius-inverse budget that will eventually be replaced by the sharper
source condition-number estimate. -/
theorem mgs_qr_bounds_of_R11_diag_ne_zero
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {c2 kappaA higherOrder : Real}
    (hdiag :
      forall i : Fin n,
        Ne (householder_paddedFinInput_R11 fp A i i) 0)
    (hbudget :
      2 *
          (((Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A) +
                2 *
                  (Theorem19_4.gamma_tilde fp (n + m) n *
                    frobNormRect A)) *
              frobNorm (nonsingInv n (householder_paddedFinInput_R11 fp A))) +
            (((Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A) +
                  2 *
                    (Theorem19_4.gamma_tilde fp (n + m) n *
                      frobNormRect A)) *
                frobNorm
                  (nonsingInv n (householder_paddedFinInput_R11 fp A))) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (householder_paddedFinInput_R11 fp A)
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  exact
    mgs_qr_bounds_of_householder_upper_diag_csPolarRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hnm hsmall
      (eta1 := Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A)
      (c2 := c2) (kappaA := kappaA) (higherOrder := higherOrder)
      (by
        intro i
        simpa [householder_paddedFinInput_R11] using hdiag i)
      (le_rfl)
      (by
        simpa [householder_paddedFinInput_R11] using hbudget)

/-- Compact-budget version of `mgs_qr_bounds_of_R11_diag_ne_zero`.

This records the current concrete residual combination as `3 * gamma_tilde *
||A||_F`, leaving only the source inverse/condition estimate as the remaining
budget refinement. -/
theorem mgs_qr_bounds_of_R11_diag_ne_zero_compact_budget
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {c2 kappaA higherOrder : Real}
    (hdiag :
      forall i : Fin n,
        Ne (householder_paddedFinInput_R11 fp A i i) 0)
    (hbudget :
      2 *
          ((3 * (Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A)) *
              frobNorm (nonsingInv n (householder_paddedFinInput_R11 fp A))) +
            ((3 *
                  (Theorem19_4.gamma_tilde fp (n + m) n *
                    frobNormRect A)) *
                frobNorm
                  (nonsingInv n (householder_paddedFinInput_R11 fp A))) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (householder_paddedFinInput_R11 fp A)
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  refine
    mgs_qr_bounds_of_R11_diag_ne_zero
      (fp := fp) (m := m) (n := n) A hn hnm hsmall
      (c2 := c2) (kappaA := kappaA) (higherOrder := higherOrder)
      hdiag ?_
  ring_nf at hbudget
  ring_nf
  exact hbudget

/-- Source-nonbreakdown form of the chapter-facing Theorem 19.13 assembly with
an explicit inverse-norm budget for the extracted `R11` block.

This is the plug-in point for the remaining source condition estimate: future
work can replace the visible `rectOpNorm2Le (nonsingInv R11) rho` premise by a
proved bound in terms of the chapter's advertised conditioning quantity. -/
theorem mgs_qr_bounds_of_R11_diag_ne_zero_inverse_budget
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {rho c2 kappaA higherOrder : Real}
    (hdiag :
      forall i : Fin n,
        Ne (householder_paddedFinInput_R11 fp A i i) 0)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n (householder_paddedFinInput_R11 fp A))
        rho)
    (hrho : 0 <= rho)
    (hbudget :
      2 *
          (((Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A) +
                2 *
                  (Theorem19_4.gamma_tilde fp (n + m) n *
                    frobNormRect A)) *
              rho) +
            (((Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A) +
                  2 *
                    (Theorem19_4.gamma_tilde fp (n + m) n *
                      frobNormRect A)) *
                rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (householder_paddedFinInput_R11 fp A)
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  simpa [householder_paddedFinInput_R11] using
    mgs_qr_bounds_of_householder_upper_diag_csPolarRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hnm hsmall
      (eta1 := Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A)
      (rho := rho) (c2 := c2)
      (kappaA := kappaA) (higherOrder := higherOrder)
      (by
        intro i
        simpa [householder_paddedFinInput_R11] using hdiag i)
      (le_rfl)
      (by
        simpa [householder_paddedFinInput_R11] using hRinv)
      hrho
      (by
        simpa using hbudget)

/-- Compact-budget version of
`mgs_qr_bounds_of_R11_diag_ne_zero_inverse_budget`.

The residual contribution is exposed as `3 * gamma_tilde * ||A||_F`, while the
inverse-norm estimate is left as the explicit source-facing quantity `rho`. -/
theorem mgs_qr_bounds_of_R11_diag_ne_zero_compact_inverse_budget
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {rho c2 kappaA higherOrder : Real}
    (hdiag :
      forall i : Fin n,
        Ne (householder_paddedFinInput_R11 fp A i i) 0)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n (householder_paddedFinInput_R11 fp A))
        rho)
    (hrho : 0 <= rho)
    (hbudget :
      2 *
          ((3 * (Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A)) *
              rho) +
            ((3 *
                  (Theorem19_4.gamma_tilde fp (n + m) n *
                    frobNormRect A)) *
                rho) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (householder_paddedFinInput_R11 fp A)
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  refine
    mgs_qr_bounds_of_R11_diag_ne_zero_inverse_budget
      (fp := fp) (m := m) (n := n) A hn hnm hsmall
      (rho := rho) (c2 := c2)
      (kappaA := kappaA) (higherOrder := higherOrder)
      hdiag hRinv hrho ?_
  ring_nf at hbudget
  ring_nf
  exact hbudget

/-- Scalar budget bridge for the compact inverse-budget route.

The source sensitivity estimate is expected to bound the product
`||A||_F * rho` by the advertised conditioning quantity.  This lemma turns that
product estimate into the exact `2*delta + delta^2` budget used by the checked
common-`R` orthogonality-loss proof. -/
theorem compact_inverse_budget_of_condition_budget
    {gamma normA rho kappaA budget : Real}
    (hgamma : 0 <= gamma)
    (hnormA : 0 <= normA)
    (hrho : 0 <= rho)
    (hcondition : normA * rho <= kappaA)
    (hbudget :
      2 * ((3 * gamma) * kappaA) + ((3 * gamma) * kappaA) ^ 2 <= budget) :
    2 * ((3 * (gamma * normA)) * rho) +
        ((3 * (gamma * normA)) * rho) ^ 2 <= budget := by
  let delta : Real := (3 * (gamma * normA)) * rho
  let sourceRadius : Real := (3 * gamma) * kappaA
  have hthree_gamma : 0 <= 3 * gamma := by nlinarith
  have hdelta_nonneg : 0 <= delta := by
    have hgn : 0 <= gamma * normA := mul_nonneg hgamma hnormA
    have hleft : 0 <= 3 * (gamma * normA) := by nlinarith
    simpa [delta] using mul_nonneg hleft hrho
  have hdelta_le : delta <= sourceRadius := by
    have hprod :
        (3 * gamma) * (normA * rho) <= (3 * gamma) * kappaA := by
      exact mul_le_mul_of_nonneg_left hcondition hthree_gamma
    dsimp [delta, sourceRadius]
    nlinarith
  have hmono :
      2 * delta + delta ^ 2 <= 2 * sourceRadius + sourceRadius ^ 2 := by
    have hsq : delta ^ 2 <= sourceRadius ^ 2 := by
      nlinarith [sq_nonneg (sourceRadius - delta)]
    nlinarith
  exact hmono.trans hbudget

/-- Source-condition-budget version of the chapter-facing Theorem 19.13 route.

This exposes the remaining QR sensitivity estimate in the same product shape as
the printed condition-number discussion: a bound for
`||A||_F * ||R11^{-1}||` feeds the compact inverse-budget wrapper, while the
final scalar budget carries the printed constants and higher-order term. -/
theorem mgs_qr_bounds_of_R11_diag_ne_zero_compact_condition_budget
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {rho c2 kappaA higherOrder : Real}
    (hdiag :
      forall i : Fin n,
        Ne (householder_paddedFinInput_R11 fp A i i) 0)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n (householder_paddedFinInput_R11 fp A))
        rho)
    (hrho : 0 <= rho)
    (hcondition : frobNormRect A * rho <= kappaA)
    (hbudget :
      2 * ((3 * Theorem19_4.gamma_tilde fp (n + m) n) * kappaA) +
          ((3 * Theorem19_4.gamma_tilde fp (n + m) n) * kappaA) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (householder_paddedFinInput_R11 fp A)
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  refine
    mgs_qr_bounds_of_R11_diag_ne_zero_compact_inverse_budget
      (fp := fp) (m := m) (n := n) A hn hnm hsmall
      (rho := rho) (c2 := c2)
      (kappaA := kappaA) (higherOrder := higherOrder)
      hdiag hRinv hrho ?_
  have hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)) := by
    unfold gammaValid
    have hhalf_lt_one : (1 / 2 : Real) < 1 := by norm_num
    exact lt_of_le_of_lt hsmall hhalf_lt_one
  exact
    compact_inverse_budget_of_condition_budget
      (gamma := Theorem19_4.gamma_tilde fp (n + m) n)
      (normA := frobNormRect A) (rho := rho)
      (kappaA := kappaA)
      (budget := c2 * fp.u * kappaA + higherOrder)
      (Theorem19_4.gamma_tilde_nonneg fp hvalid)
      (frobNormRect_nonneg A)
      hrho hcondition hbudget

/-- Determinant-nonzero version of
`mgs_qr_bounds_of_R11_diag_ne_zero_compact_condition_budget`.

The full padded Householder block data already gives the extracted `R11`
upper-trapezoidal shape, so a determinant certificate supplies the
source-style nonzero diagonal required by the compact condition-budget route. -/
theorem mgs_qr_bounds_of_R11_det_ne_zero_compact_condition_budget
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {rho c2 kappaA higherOrder : Real}
    (hdet :
      Ne
        (Matrix.det
        (householder_paddedFinInput_R11 fp A :
          Matrix (Fin n) (Fin n) Real))
        0)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n (householder_paddedFinInput_R11 fp A))
        rho)
    (hrho : 0 <= rho)
    (hcondition : frobNormRect A * rho <= kappaA)
    (hbudget :
      2 * ((3 * Theorem19_4.gamma_tilde fp (n + m) n) * kappaA) +
          ((3 * Theorem19_4.gamma_tilde fp (n + m) n) * kappaA) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (householder_paddedFinInput_R11 fp A)
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  have hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)) := by
    unfold gammaValid
    have hhalf_lt_one : (1 / 2 : Real) < 1 := by norm_num
    exact lt_of_le_of_lt hsmall hhalf_lt_one
  have hdet_expanded :
      Ne
        (Matrix.det
        (paddedEconomyR
          (fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
            Matrix (Fin n) (Fin n) Real))
        0 := by
    simpa [householder_paddedFinInput_R11] using hdet
  have hdiag :
      forall i : Fin n,
        Ne (householder_paddedFinInput_R11 fp A i i) 0 := by
    intro i
    simpa [householder_paddedFinInput_R11] using
      householder_paddedFinInput_R11_diag_ne_zero_of_det_ne_zero
        fp A hn hvalid hdet_expanded i
  exact
    mgs_qr_bounds_of_R11_diag_ne_zero_compact_condition_budget
      (fp := fp) (m := m) (n := n) A hn hnm hsmall
      (rho := rho) (c2 := c2)
      (kappaA := kappaA) (higherOrder := higherOrder)
      hdiag hRinv hrho hcondition hbudget

/-- Scalar final-radius bridge for the compact source-condition route.

The linear part is discharged from a coefficient bound
`gamma <= c1*u` and a printed-style constant inequality `6*c1 <= c2`;
the quadratic part is recorded as the higher-order contribution. -/
theorem compact_condition_radius_budget_of_coefficient_budget
    {gamma u kappaA c1 c2 higherOrder : Real}
    (hu : 0 <= u)
    (hkappa : 0 <= kappaA)
    (hgamma_le : gamma <= c1 * u)
    (hc2 : 6 * c1 <= c2)
    (hquad : ((3 * gamma) * kappaA) ^ 2 <= higherOrder) :
    2 * ((3 * gamma) * kappaA) + ((3 * gamma) * kappaA) ^ 2 <=
      c2 * u * kappaA + higherOrder := by
  have hlinear_coeff : 6 * gamma <= 6 * (c1 * u) := by
    exact mul_le_mul_of_nonneg_left hgamma_le (by norm_num : (0 : Real) <= 6)
  have hlinear1 : (6 * gamma) * kappaA <= (6 * (c1 * u)) * kappaA := by
    exact mul_le_mul_of_nonneg_right hlinear_coeff hkappa
  have hu_kappa : 0 <= u * kappaA := mul_nonneg hu hkappa
  have hlinear2 : (6 * c1) * (u * kappaA) <= c2 * (u * kappaA) := by
    exact mul_le_mul_of_nonneg_right hc2 hu_kappa
  have hlinear : 2 * ((3 * gamma) * kappaA) <= c2 * u * kappaA := by
    nlinarith
  nlinarith

/-- Determinant-nonzero compact condition route with the final radius budget
split into the source-style linear coefficient and a quadratic higher-order
term.

This removes the monolithic final scalar-budget hypothesis from
`mgs_qr_bounds_of_R11_det_ne_zero_compact_condition_budget`; the remaining
assumptions are the source condition estimate, the coefficient bound for
`gamma_tilde`, and the explicit quadratic higher-order allowance. -/
theorem mgs_qr_bounds_of_R11_det_ne_zero_compact_condition_radius_budget
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {rho c1 c2 kappaA higherOrder : Real}
    (hdet :
      Ne
        (Matrix.det
        (householder_paddedFinInput_R11 fp A :
          Matrix (Fin n) (Fin n) Real))
        0)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n (householder_paddedFinInput_R11 fp A))
        rho)
    (hrho : 0 <= rho)
    (hcondition : frobNormRect A * rho <= kappaA)
    (hkappaA : 0 <= kappaA)
    (hgamma_coeff :
      Theorem19_4.gamma_tilde fp (n + m) n <= c1 * fp.u)
    (hc2 : 6 * c1 <= c2)
    (hhigher :
      ((3 * Theorem19_4.gamma_tilde fp (n + m) n) * kappaA) ^ 2 <=
        higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (householder_paddedFinInput_R11 fp A)
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  refine
    mgs_qr_bounds_of_R11_det_ne_zero_compact_condition_budget
      (fp := fp) (m := m) (n := n) A hn hnm hsmall
      (rho := rho) (c2 := c2)
      (kappaA := kappaA) (higherOrder := higherOrder)
      hdet hRinv hrho hcondition ?_
  exact
    compact_condition_radius_budget_of_coefficient_budget
      (gamma := Theorem19_4.gamma_tilde fp (n + m) n)
      (u := fp.u) (kappaA := kappaA)
      (c1 := c1) (c2 := c2) (higherOrder := higherOrder)
      fp.u_nonneg hkappaA hgamma_coeff hc2 hhigher

/-- Small-unit-roundoff version of the determinant compact condition route
with source-style final-radius assumptions.

The standard `k*u <= 1/2` guard supplies
`gamma_tilde <= 2*k*u`; the linear printed constant is therefore exposed as
`12*k <= c2`, and the quadratic term is left as the explicit higher-order
allowance. -/
theorem
    mgs_qr_bounds_of_R11_det_ne_zero_compact_condition_radius_budget_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {rho c2 kappaA higherOrder : Real}
    (hdet :
      Ne
        (Matrix.det
        (householder_paddedFinInput_R11 fp A :
          Matrix (Fin n) (Fin n) Real))
        0)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n (householder_paddedFinInput_R11 fp A))
        rho)
    (hrho : 0 <= rho)
    (hcondition : frobNormRect A * rho <= kappaA)
    (hkappaA : 0 <= kappaA)
    (hc2 :
      12 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) <=
        c2)
    (hhigher :
      ((3 * Theorem19_4.gamma_tilde fp (n + m) n) * kappaA) ^ 2 <=
        higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (householder_paddedFinInput_R11 fp A)
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  let k : Real :=
    ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real)
  have hgamma_coeff :
      Theorem19_4.gamma_tilde fp (n + m) n <= (2 * k) * fp.u := by
    dsimp [k]
    exact
      Theorem19_4.gamma_tilde_le_two_index_mul_unit_roundoff_of_small
        fp (n + m) n hsmall
  have hcoeff : 6 * (2 * k) <= c2 := by
    dsimp [k]
    nlinarith [hc2]
  exact
    mgs_qr_bounds_of_R11_det_ne_zero_compact_condition_radius_budget
      (fp := fp) (m := m) (n := n) A hn hnm hsmall
      (rho := rho) (c1 := 2 * k) (c2 := c2)
      (kappaA := kappaA) (higherOrder := higherOrder)
      hdet hRinv hrho hcondition hkappaA hgamma_coeff hcoeff hhigher

/-- Fully explicit small-unit-roundoff compact condition route.

This specializes the final radius bookkeeping to the concrete first-order
coefficient `c2 = 12*k` and the exact quadratic higher-order term.  The
remaining hypotheses are the genuinely source-facing `R11` determinant and
condition-estimate inputs. -/
theorem
    mgs_qr_bounds_of_R11_det_ne_zero_compact_condition_explicit_radius_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {rho kappaA : Real}
    (hdet :
      Ne
        (Matrix.det
        (householder_paddedFinInput_R11 fp A :
          Matrix (Fin n) (Fin n) Real))
        0)
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n (householder_paddedFinInput_R11 fp A))
        rho)
    (hrho : 0 <= rho)
    (hcondition : frobNormRect A * rho <= kappaA) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (householder_paddedFinInput_R11 fp A)
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (12 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA
      (((3 * Theorem19_4.gamma_tilde fp (n + m) n) * kappaA) ^ 2) := by
  let k : Real :=
    ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real)
  have hkappaA : 0 <= kappaA := by
    exact le_trans (mul_nonneg (frobNormRect_nonneg A) hrho) hcondition
  exact
    mgs_qr_bounds_of_R11_det_ne_zero_compact_condition_radius_budget_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hnm hsmall
      (rho := rho) (c2 := 12 * k)
      (kappaA := kappaA)
      (higherOrder :=
        ((3 * Theorem19_4.gamma_tilde fp (n + m) n) * kappaA) ^ 2)
      hdet hRinv hrho hcondition hkappaA
      (by
        dsimp [k]
        exact le_rfl)
      (by exact le_rfl)

/-- Fully explicit small-unit-roundoff route using the Frobenius fallback
inverse budget for the extracted `R11` block.

This removes the visible `rectOpNorm2Le (nonsingInv R11) rho` and `0 <= rho`
premises from the explicit-radius wrapper by choosing
`rho = ||nonsingInv R11||_F`.  It is still weaker than the intended printed
source condition-number estimate, which should eventually prove the displayed
product bound from source-side nonbreakdown and conditioning facts. -/
theorem
    mgs_qr_bounds_of_R11_det_ne_zero_frob_condition_explicit_radius_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {kappaA : Real}
    (hdet :
      Ne
        (Matrix.det
        (householder_paddedFinInput_R11 fp A :
          Matrix (Fin n) (Fin n) Real))
        0)
    (hcondition :
      frobNormRect A *
          frobNorm (nonsingInv n (householder_paddedFinInput_R11 fp A)) <=
        kappaA) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (householder_paddedFinInput_R11 fp A)
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (12 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA
      (((3 * Theorem19_4.gamma_tilde fp (n + m) n) * kappaA) ^ 2) := by
  let R11 : Fin n -> Fin n -> Real := householder_paddedFinInput_R11 fp A
  let rho : Real := frobNorm (nonsingInv n R11)
  have hRinv : rectOpNorm2Le (nonsingInv n R11) rho := by
    dsimp [rho]
    exact rectOpNorm2Le_nonsingInv_frobNorm R11
  have hrho : 0 <= rho := by
    dsimp [rho]
    exact frobNorm_nonneg (nonsingInv n R11)
  exact
    mgs_qr_bounds_of_R11_det_ne_zero_compact_condition_explicit_radius_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hnm hsmall
      (rho := rho) (kappaA := kappaA)
      hdet
      (by simpa [R11] using hRinv)
      hrho
      (by simpa [R11, rho] using hcondition)

/-- Fully explicit Frobenius-self fallback route.

This specializes the fallback condition theorem to
`kappaA = ||A||_F * ||nonsingInv R11||_F`, removing the separate product-bound
premise.  The result is a checked determinant-only fallback after the standard
small-unit-roundoff guard, not the sharper printed condition-number theorem. -/
theorem
    mgs_qr_bounds_of_R11_det_ne_zero_frob_self_condition_explicit_radius_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    (hdet :
      Ne
        (Matrix.det
        (householder_paddedFinInput_R11 fp A :
          Matrix (Fin n) (Fin n) Real))
        0) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (householder_paddedFinInput_R11 fp A)
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (12 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A)
      (frobNormRect A *
        frobNorm (nonsingInv n (householder_paddedFinInput_R11 fp A)))
      (((3 * Theorem19_4.gamma_tilde fp (n + m) n) *
          (frobNormRect A *
            frobNorm
              (nonsingInv n (householder_paddedFinInput_R11 fp A)))) ^ 2) := by
  exact
    mgs_qr_bounds_of_R11_det_ne_zero_frob_condition_explicit_radius_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hnm hsmall
      (kappaA :=
        frobNormRect A *
          frobNorm (nonsingInv n (householder_paddedFinInput_R11 fp A)))
      hdet le_rfl

/-- Source-diagonal form of the fully explicit Frobenius-fallback condition
route.

This is the same checked fallback as
`mgs_qr_bounds_of_R11_det_ne_zero_frob_condition_explicit_radius_of_small_unit_roundoff`,
but the nonbreakdown premise is stated on the extracted `R11` diagonal, matching
the source-facing diagonal form used by the surrounding MGS route. -/
theorem
    mgs_qr_bounds_of_R11_diag_ne_zero_frob_condition_explicit_radius_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {kappaA : Real}
    (hdiag :
      forall i : Fin n,
        Ne (householder_paddedFinInput_R11 fp A i i) 0)
    (hcondition :
      frobNormRect A *
          frobNorm (nonsingInv n (householder_paddedFinInput_R11 fp A)) <=
        kappaA) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (householder_paddedFinInput_R11 fp A)
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (12 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA
      (((3 * Theorem19_4.gamma_tilde fp (n + m) n) * kappaA) ^ 2) := by
  have hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + m)) := by
    unfold gammaValid
    have hhalf_lt_one : (1 / 2 : Real) < 1 := by norm_num
    exact lt_of_le_of_lt hsmall hhalf_lt_one
  have hdet :
      Ne
        (Matrix.det
        (householder_paddedFinInput_R11 fp A :
          Matrix (Fin n) (Fin n) Real))
        0 :=
    (householder_paddedFinInput_R11_det_ne_zero_iff_diag_ne_zero
      fp A hn hvalid).2 hdiag
  exact
    mgs_qr_bounds_of_R11_det_ne_zero_frob_condition_explicit_radius_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hnm hsmall
      (kappaA := kappaA) hdet hcondition

/-- Stored-loop nonbreakdown form of the fully explicit Frobenius-condition
route for Theorem 19.13.

This combines the stored-panel uniform step-budget nonbreakdown theorem with
the source-diagonal MGS assembly.  The remaining algorithm bridge is explicit:
`hR11` must identify the concrete padded Householder `R11` block with the
stored-loop final top block.  The remaining source condition estimate is the
visible Frobenius product bound. -/
theorem
    mgs_qr_bounds_of_storedTrailingPanel_R11_uniform_step_budget_frob_condition_explicit_radius_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hrows : n <= n + m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    (A_hat : Nat -> Fin (n + m) -> Fin n -> Real)
    (b_hat : Nat -> Fin (n + m) -> Real)
    (alpha : Nat -> Real)
    (cStep : Real)
    (hm : gammaValid fp (n + m))
    (hStep : forall k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (n + m) n k
          (householderTrailingActiveVector (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (n + m)
            (householderTrailingActiveVector (n + m)
              (Fin.mk k (lt_of_lt_of_le hk hrows))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (halpha : forall k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq (n + m)
          (Fin.mk k (lt_of_lt_of_le hk hrows))
          (fun i => A_hat k i (Fin.mk k hk)))
    (hdetPrev : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat k)
            (le_trans (Nat.le_of_lt hk) hrows) hk :
            Matrix (Fin k) (Fin k) Real))
        0)
    (hdetLead : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrLeadingBlock (A_hat k)
            (le_trans (Nat.succ_le_of_lt hk) hrows) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) Real))
        0)
    (hlowerPrev :
      forall k (hk : k < n) (i : Fin (n + m)) (j : Fin k),
        k <= i.val -> A_hat k i (qrPreviousColumn n k hk j) = 0)
    (hsign : forall k (hk : k < n),
      alpha k *
          A_hat k (Fin.mk k (lt_of_lt_of_le hk hrows)) (Fin.mk k hk) <= 0)
    (hStepBudget : forall k : Fin n,
      storedQRCompactStepRelativeBudget hrows fp A_hat b_hat alpha k <= cStep)
    (huniformBudget : forall k (hk : k < n),
      ((n : Real) * cStep) *
          vecNorm2 (fun i : Fin (n + m) => A_hat k i (Fin.mk k hk)) <
        Real.sqrt
          (householderTrailingNorm2Sq (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun i => A_hat k i (Fin.mk k hk))))
    (hR11 : forall i j,
      householder_paddedFinInput_R11 fp A i j =
        A_hat n (Fin.mk i.val (lt_of_lt_of_le i.isLt hrows)) j)
    {kappaA : Real}
    (hcondition :
      frobNormRect A *
          frobNorm (nonsingInv n (householder_paddedFinInput_R11 fp A)) <=
        kappaA) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (householder_paddedFinInput_R11 fp A)
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (12 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA
      (((3 * Theorem19_4.gamma_tilde fp (n + m) n) * kappaA) ^ 2) := by
  have hdiag :
      forall i : Fin n,
        Ne (householder_paddedFinInput_R11 fp A i i) 0 :=
    householder_paddedFinInput_R11_diag_ne_zero_of_storedTrailingPanel_uniform_step_budget
      (fp := fp) (m := m) (n := n) A hrows A_hat b_hat alpha cStep
      hm hStep halpha hdetPrev hdetLead hlowerPrev hsign hStepBudget
      huniformBudget hR11
  exact
    mgs_qr_bounds_of_R11_diag_ne_zero_frob_condition_explicit_radius_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hnm hsmall
      (kappaA := kappaA) hdiag hcondition

/-- Stored-loop nonbreakdown form of the fully explicit Frobenius-self
fallback route for Theorem 19.13.

This specializes
`mgs_qr_bounds_of_storedTrailingPanel_R11_uniform_step_budget_frob_condition_explicit_radius_of_small_unit_roundoff`
to the fallback condition quantity
`kappaA = ||A||_F * ||nonsingInv R11||_F`.  It therefore removes the separate
Frobenius product-bound premise, while still keeping the real remaining
algorithm bridge `hR11` explicit. -/
theorem
    mgs_qr_bounds_of_storedTrailingPanel_R11_uniform_step_budget_frob_self_condition_explicit_radius_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hrows : n <= n + m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    (A_hat : Nat -> Fin (n + m) -> Fin n -> Real)
    (b_hat : Nat -> Fin (n + m) -> Real)
    (alpha : Nat -> Real)
    (cStep : Real)
    (hm : gammaValid fp (n + m))
    (hStep : forall k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (n + m) n k
          (householderTrailingActiveVector (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (n + m)
            (householderTrailingActiveVector (n + m)
              (Fin.mk k (lt_of_lt_of_le hk hrows))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (halpha : forall k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq (n + m)
          (Fin.mk k (lt_of_lt_of_le hk hrows))
          (fun i => A_hat k i (Fin.mk k hk)))
    (hdetPrev : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat k)
            (le_trans (Nat.le_of_lt hk) hrows) hk :
            Matrix (Fin k) (Fin k) Real))
        0)
    (hdetLead : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrLeadingBlock (A_hat k)
            (le_trans (Nat.succ_le_of_lt hk) hrows) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) Real))
        0)
    (hlowerPrev :
      forall k (hk : k < n) (i : Fin (n + m)) (j : Fin k),
        k <= i.val -> A_hat k i (qrPreviousColumn n k hk j) = 0)
    (hsign : forall k (hk : k < n),
      alpha k *
          A_hat k (Fin.mk k (lt_of_lt_of_le hk hrows)) (Fin.mk k hk) <= 0)
    (hStepBudget : forall k : Fin n,
      storedQRCompactStepRelativeBudget hrows fp A_hat b_hat alpha k <= cStep)
    (huniformBudget : forall k (hk : k < n),
      ((n : Real) * cStep) *
          vecNorm2 (fun i : Fin (n + m) => A_hat k i (Fin.mk k hk)) <
        Real.sqrt
          (householderTrailingNorm2Sq (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun i => A_hat k i (Fin.mk k hk))))
    (hR11 : forall i j,
      householder_paddedFinInput_R11 fp A i j =
        A_hat n (Fin.mk i.val (lt_of_lt_of_le i.isLt hrows)) j) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (householder_paddedFinInput_R11 fp A)
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (12 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A)
      (frobNormRect A *
        frobNorm (nonsingInv n (householder_paddedFinInput_R11 fp A)))
      (((3 * Theorem19_4.gamma_tilde fp (n + m) n) *
          (frobNormRect A *
            frobNorm
              (nonsingInv n (householder_paddedFinInput_R11 fp A)))) ^ 2) := by
  exact
    mgs_qr_bounds_of_storedTrailingPanel_R11_uniform_step_budget_frob_condition_explicit_radius_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hnm hrows hsmall
      A_hat b_hat alpha cStep hm hStep halpha hdetPrev hdetLead
      hlowerPrev hsign hStepBudget huniformBudget hR11
      (kappaA :=
        frobNormRect A *
          frobNorm (nonsingInv n (householder_paddedFinInput_R11 fp A)))
      le_rfl

/-- Stored-loop nonbreakdown form of the fully explicit Frobenius-condition
route, with the remaining algorithm bridge stated as a full final-panel
equality.

This is the downstream `MGSQRBounds` version of
`householder_paddedFinInput_R11_eq_top_block_of_final_panel_eq`: the final
recursive/stored QR bridge can now target `A_hat n = fl_householderQRPanel_R ...`
directly, and the top-block `R11` equality is supplied internally. -/
theorem
    mgs_qr_bounds_of_storedTrailingPanel_final_panel_eq_uniform_step_budget_frob_condition_explicit_radius_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hrows : n <= n + m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    (A_hat : Nat -> Fin (n + m) -> Fin n -> Real)
    (b_hat : Nat -> Fin (n + m) -> Real)
    (alpha : Nat -> Real)
    (cStep : Real)
    (hm : gammaValid fp (n + m))
    (hStep : forall k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (n + m) n k
          (householderTrailingActiveVector (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (n + m)
            (householderTrailingActiveVector (n + m)
              (Fin.mk k (lt_of_lt_of_le hk hrows))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (halpha : forall k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq (n + m)
          (Fin.mk k (lt_of_lt_of_le hk hrows))
          (fun i => A_hat k i (Fin.mk k hk)))
    (hdetPrev : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat k)
            (le_trans (Nat.le_of_lt hk) hrows) hk :
            Matrix (Fin k) (Fin k) Real))
        0)
    (hdetLead : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrLeadingBlock (A_hat k)
            (le_trans (Nat.succ_le_of_lt hk) hrows) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) Real))
        0)
    (hlowerPrev :
      forall k (hk : k < n) (i : Fin (n + m)) (j : Fin k),
        k <= i.val -> A_hat k i (qrPreviousColumn n k hk j) = 0)
    (hsign : forall k (hk : k < n),
      alpha k *
          A_hat k (Fin.mk k (lt_of_lt_of_le hk hrows)) (Fin.mk k hk) <= 0)
    (hStepBudget : forall k : Fin n,
      storedQRCompactStepRelativeBudget hrows fp A_hat b_hat alpha k <= cStep)
    (huniformBudget : forall k (hk : k < n),
      ((n : Real) * cStep) *
          vecNorm2 (fun i : Fin (n + m) => A_hat k i (Fin.mk k hk)) <
        Real.sqrt
          (householderTrailingNorm2Sq (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun i => A_hat k i (Fin.mk k hk))))
    (hFinal :
      A_hat n = fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
    {kappaA : Real}
    (hcondition :
      frobNormRect A *
          frobNorm (nonsingInv n (householder_paddedFinInput_R11 fp A)) <=
        kappaA) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (householder_paddedFinInput_R11 fp A)
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (12 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA
      (((3 * Theorem19_4.gamma_tilde fp (n + m) n) * kappaA) ^ 2) :=
  mgs_qr_bounds_of_storedTrailingPanel_R11_uniform_step_budget_frob_condition_explicit_radius_of_small_unit_roundoff
    (fp := fp) (m := m) (n := n) A hn hnm hrows hsmall
    A_hat b_hat alpha cStep hm hStep halpha hdetPrev hdetLead
    hlowerPrev hsign hStepBudget huniformBudget
    (householder_paddedFinInput_R11_eq_top_block_of_final_panel_eq
      fp A hrows A_hat hFinal)
    (kappaA := kappaA) hcondition

/-- Frobenius-self fallback version of
`mgs_qr_bounds_of_storedTrailingPanel_final_panel_eq_uniform_step_budget_frob_condition_explicit_radius_of_small_unit_roundoff`.

The only remaining recursive/stored bridge premise is the full final-panel
equality; the Frobenius condition quantity is chosen internally as
`||A||_F * ||nonsingInv R11||_F`. -/
theorem
    mgs_qr_bounds_of_storedTrailingPanel_final_panel_eq_uniform_step_budget_frob_self_condition_explicit_radius_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hrows : n <= n + m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    (A_hat : Nat -> Fin (n + m) -> Fin n -> Real)
    (b_hat : Nat -> Fin (n + m) -> Real)
    (alpha : Nat -> Real)
    (cStep : Real)
    (hm : gammaValid fp (n + m))
    (hStep : forall k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (n + m) n k
          (householderTrailingActiveVector (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (n + m)
            (householderTrailingActiveVector (n + m)
              (Fin.mk k (lt_of_lt_of_le hk hrows))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (halpha : forall k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq (n + m)
          (Fin.mk k (lt_of_lt_of_le hk hrows))
          (fun i => A_hat k i (Fin.mk k hk)))
    (hdetPrev : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat k)
            (le_trans (Nat.le_of_lt hk) hrows) hk :
            Matrix (Fin k) (Fin k) Real))
        0)
    (hdetLead : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrLeadingBlock (A_hat k)
            (le_trans (Nat.succ_le_of_lt hk) hrows) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) Real))
        0)
    (hlowerPrev :
      forall k (hk : k < n) (i : Fin (n + m)) (j : Fin k),
        k <= i.val -> A_hat k i (qrPreviousColumn n k hk j) = 0)
    (hsign : forall k (hk : k < n),
      alpha k *
          A_hat k (Fin.mk k (lt_of_lt_of_le hk hrows)) (Fin.mk k hk) <= 0)
    (hStepBudget : forall k : Fin n,
      storedQRCompactStepRelativeBudget hrows fp A_hat b_hat alpha k <= cStep)
    (huniformBudget : forall k (hk : k < n),
      ((n : Real) * cStep) *
          vecNorm2 (fun i : Fin (n + m) => A_hat k i (Fin.mk k hk)) <
        Real.sqrt
          (householderTrailingNorm2Sq (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun i => A_hat k i (Fin.mk k hk))))
    (hFinal :
      A_hat n = fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (householder_paddedFinInput_R11 fp A)
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (12 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A)
      (frobNormRect A *
        frobNorm (nonsingInv n (householder_paddedFinInput_R11 fp A)))
      (((3 * Theorem19_4.gamma_tilde fp (n + m) n) *
          (frobNormRect A *
            frobNorm
              (nonsingInv n (householder_paddedFinInput_R11 fp A)))) ^ 2) :=
  mgs_qr_bounds_of_storedTrailingPanel_final_panel_eq_uniform_step_budget_frob_condition_explicit_radius_of_small_unit_roundoff
    (fp := fp) (m := m) (n := n) A hn hnm hrows hsmall
    A_hat b_hat alpha cStep hm hStep halpha hdetPrev hdetLead
    hlowerPrev hsign hStepBudget huniformBudget hFinal
    (kappaA :=
      frobNormRect A *
        frobNorm (nonsingInv n (householder_paddedFinInput_R11 fp A)))
    le_rfl

/-- Stored-loop nonbreakdown form of the fully explicit Frobenius-condition
route, with previous-block information taken from the final stored panel.

This is the `MGSQRBounds` counterpart of
`householder_paddedFinInput_R11_diag_ne_zero_of_storedTrailingPanel_final_prevBlocks_uniform_step_budget`:
the stage-local previous-leading-block and lower-zero hypotheses are supplied
internally by the signed stored sequence.  The remaining source nonbreakdown
input is the current-leading-block condition at each active pivot. -/
theorem
    mgs_qr_bounds_of_storedTrailingPanel_R11_final_prevBlocks_uniform_step_budget_frob_condition_explicit_radius_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hrows : n <= n + m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    (A_hat : Nat -> Fin (n + m) -> Fin n -> Real)
    (b_hat : Nat -> Fin (n + m) -> Real)
    (alpha : Nat -> Real)
    (cStep : Real)
    (hm : gammaValid fp (n + m))
    (hStep : forall k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (n + m) n k
          (householderTrailingActiveVector (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (n + m)
            (householderTrailingActiveVector (n + m)
              (Fin.mk k (lt_of_lt_of_le hk hrows))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (halpha : forall k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq (n + m)
          (Fin.mk k (lt_of_lt_of_le hk hrows))
          (fun i => A_hat k i (Fin.mk k hk)))
    (hdetPrevFinal : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat n)
            (le_trans (Nat.le_of_lt hk) hrows) hk :
            Matrix (Fin k) (Fin k) Real))
        0)
    (hdetLead : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrLeadingBlock (A_hat k)
            (le_trans (Nat.succ_le_of_lt hk) hrows) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) Real))
        0)
    (hsign : forall k (hk : k < n),
      alpha k *
          A_hat k (Fin.mk k (lt_of_lt_of_le hk hrows)) (Fin.mk k hk) <= 0)
    (hStepBudget : forall k : Fin n,
      storedQRCompactStepRelativeBudget hrows fp A_hat b_hat alpha k <= cStep)
    (huniformBudget : forall k (hk : k < n),
      ((n : Real) * cStep) *
          vecNorm2 (fun i : Fin (n + m) => A_hat k i (Fin.mk k hk)) <
        Real.sqrt
          (householderTrailingNorm2Sq (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun i => A_hat k i (Fin.mk k hk))))
    (hR11 : forall i j,
      householder_paddedFinInput_R11 fp A i j =
        A_hat n (Fin.mk i.val (lt_of_lt_of_le i.isLt hrows)) j)
    {kappaA : Real}
    (hcondition :
      frobNormRect A *
          frobNorm (nonsingInv n (householder_paddedFinInput_R11 fp A)) <=
        kappaA) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (householder_paddedFinInput_R11 fp A)
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (12 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA
      (((3 * Theorem19_4.gamma_tilde fp (n + m) n) * kappaA) ^ 2) := by
  have hdiag :
      forall i : Fin n,
        Ne (householder_paddedFinInput_R11 fp A i i) 0 :=
    householder_paddedFinInput_R11_diag_ne_zero_of_storedTrailingPanel_final_prevBlocks_uniform_step_budget
      (fp := fp) (m := m) (n := n) A hrows A_hat b_hat alpha cStep
      hm hStep halpha hdetPrevFinal hdetLead hsign hStepBudget
      huniformBudget hR11
  exact
    mgs_qr_bounds_of_R11_diag_ne_zero_frob_condition_explicit_radius_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hnm hsmall
      (kappaA := kappaA) hdiag hcondition

/-- Frobenius-self fallback version of
`mgs_qr_bounds_of_storedTrailingPanel_R11_final_prevBlocks_uniform_step_budget_frob_condition_explicit_radius_of_small_unit_roundoff`.

The fallback conditioning quantity is chosen internally, and the previous-block
stage information is transported from the final stored panel. -/
theorem
    mgs_qr_bounds_of_storedTrailingPanel_R11_final_prevBlocks_uniform_step_budget_frob_self_condition_explicit_radius_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hrows : n <= n + m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    (A_hat : Nat -> Fin (n + m) -> Fin n -> Real)
    (b_hat : Nat -> Fin (n + m) -> Real)
    (alpha : Nat -> Real)
    (cStep : Real)
    (hm : gammaValid fp (n + m))
    (hStep : forall k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (n + m) n k
          (householderTrailingActiveVector (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (n + m)
            (householderTrailingActiveVector (n + m)
              (Fin.mk k (lt_of_lt_of_le hk hrows))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (halpha : forall k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq (n + m)
          (Fin.mk k (lt_of_lt_of_le hk hrows))
          (fun i => A_hat k i (Fin.mk k hk)))
    (hdetPrevFinal : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat n)
            (le_trans (Nat.le_of_lt hk) hrows) hk :
            Matrix (Fin k) (Fin k) Real))
        0)
    (hdetLead : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrLeadingBlock (A_hat k)
            (le_trans (Nat.succ_le_of_lt hk) hrows) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) Real))
        0)
    (hsign : forall k (hk : k < n),
      alpha k *
          A_hat k (Fin.mk k (lt_of_lt_of_le hk hrows)) (Fin.mk k hk) <= 0)
    (hStepBudget : forall k : Fin n,
      storedQRCompactStepRelativeBudget hrows fp A_hat b_hat alpha k <= cStep)
    (huniformBudget : forall k (hk : k < n),
      ((n : Real) * cStep) *
          vecNorm2 (fun i : Fin (n + m) => A_hat k i (Fin.mk k hk)) <
        Real.sqrt
          (householderTrailingNorm2Sq (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun i => A_hat k i (Fin.mk k hk))))
    (hR11 : forall i j,
      householder_paddedFinInput_R11 fp A i j =
        A_hat n (Fin.mk i.val (lt_of_lt_of_le i.isLt hrows)) j) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (householder_paddedFinInput_R11 fp A)
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (12 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A)
      (frobNormRect A *
        frobNorm (nonsingInv n (householder_paddedFinInput_R11 fp A)))
      (((3 * Theorem19_4.gamma_tilde fp (n + m) n) *
          (frobNormRect A *
            frobNorm
              (nonsingInv n (householder_paddedFinInput_R11 fp A)))) ^ 2) := by
  exact
    mgs_qr_bounds_of_storedTrailingPanel_R11_final_prevBlocks_uniform_step_budget_frob_condition_explicit_radius_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hnm hrows hsmall
      A_hat b_hat alpha cStep hm hStep halpha hdetPrevFinal hdetLead
      hsign hStepBudget huniformBudget hR11
      (kappaA :=
        frobNormRect A *
          frobNorm (nonsingInv n (householder_paddedFinInput_R11 fp A)))
      le_rfl

/-- Final-panel equality version of
`mgs_qr_bounds_of_storedTrailingPanel_R11_final_prevBlocks_uniform_step_budget_frob_condition_explicit_radius_of_small_unit_roundoff`.

The full recursive/stored final-panel equality supplies the concrete top-block
`R11` bridge, while final previous-leading-block hypotheses supply the
stage-local previous-block facts internally. -/
theorem
    mgs_qr_bounds_of_storedTrailingPanel_final_panel_eq_final_prevBlocks_uniform_step_budget_frob_condition_explicit_radius_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hrows : n <= n + m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    (A_hat : Nat -> Fin (n + m) -> Fin n -> Real)
    (b_hat : Nat -> Fin (n + m) -> Real)
    (alpha : Nat -> Real)
    (cStep : Real)
    (hm : gammaValid fp (n + m))
    (hStep : forall k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (n + m) n k
          (householderTrailingActiveVector (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (n + m)
            (householderTrailingActiveVector (n + m)
              (Fin.mk k (lt_of_lt_of_le hk hrows))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (halpha : forall k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq (n + m)
          (Fin.mk k (lt_of_lt_of_le hk hrows))
          (fun i => A_hat k i (Fin.mk k hk)))
    (hdetPrevFinal : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat n)
            (le_trans (Nat.le_of_lt hk) hrows) hk :
            Matrix (Fin k) (Fin k) Real))
        0)
    (hdetLead : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrLeadingBlock (A_hat k)
            (le_trans (Nat.succ_le_of_lt hk) hrows) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) Real))
        0)
    (hsign : forall k (hk : k < n),
      alpha k *
          A_hat k (Fin.mk k (lt_of_lt_of_le hk hrows)) (Fin.mk k hk) <= 0)
    (hStepBudget : forall k : Fin n,
      storedQRCompactStepRelativeBudget hrows fp A_hat b_hat alpha k <= cStep)
    (huniformBudget : forall k (hk : k < n),
      ((n : Real) * cStep) *
          vecNorm2 (fun i : Fin (n + m) => A_hat k i (Fin.mk k hk)) <
        Real.sqrt
          (householderTrailingNorm2Sq (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun i => A_hat k i (Fin.mk k hk))))
    (hFinal :
      A_hat n = fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
    {kappaA : Real}
    (hcondition :
      frobNormRect A *
          frobNorm (nonsingInv n (householder_paddedFinInput_R11 fp A)) <=
        kappaA) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (householder_paddedFinInput_R11 fp A)
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (12 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA
      (((3 * Theorem19_4.gamma_tilde fp (n + m) n) * kappaA) ^ 2) := by
  exact
    mgs_qr_bounds_of_storedTrailingPanel_R11_final_prevBlocks_uniform_step_budget_frob_condition_explicit_radius_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hnm hrows hsmall
      A_hat b_hat alpha cStep hm hStep halpha hdetPrevFinal hdetLead
      hsign hStepBudget huniformBudget
      (householder_paddedFinInput_R11_eq_top_block_of_final_panel_eq
        fp A hrows A_hat hFinal)
      (kappaA := kappaA) hcondition

/-- Frobenius-self fallback version of
`mgs_qr_bounds_of_storedTrailingPanel_final_panel_eq_final_prevBlocks_uniform_step_budget_frob_condition_explicit_radius_of_small_unit_roundoff`.

This is the most compact checked stored-loop fallback in this family: the
caller supplies final previous-leading-block determinants, current active
leading-block determinants, the signed stored recurrence, the uniform budget,
and the final-panel equality. -/
theorem
    mgs_qr_bounds_of_storedTrailingPanel_final_panel_eq_final_prevBlocks_uniform_step_budget_frob_self_condition_explicit_radius_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hrows : n <= n + m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    (A_hat : Nat -> Fin (n + m) -> Fin n -> Real)
    (b_hat : Nat -> Fin (n + m) -> Real)
    (alpha : Nat -> Real)
    (cStep : Real)
    (hm : gammaValid fp (n + m))
    (hStep : forall k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (n + m) n k
          (householderTrailingActiveVector (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (n + m)
            (householderTrailingActiveVector (n + m)
              (Fin.mk k (lt_of_lt_of_le hk hrows))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (halpha : forall k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq (n + m)
          (Fin.mk k (lt_of_lt_of_le hk hrows))
          (fun i => A_hat k i (Fin.mk k hk)))
    (hdetPrevFinal : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat n)
            (le_trans (Nat.le_of_lt hk) hrows) hk :
            Matrix (Fin k) (Fin k) Real))
        0)
    (hdetLead : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrLeadingBlock (A_hat k)
            (le_trans (Nat.succ_le_of_lt hk) hrows) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) Real))
        0)
    (hsign : forall k (hk : k < n),
      alpha k *
          A_hat k (Fin.mk k (lt_of_lt_of_le hk hrows)) (Fin.mk k hk) <= 0)
    (hStepBudget : forall k : Fin n,
      storedQRCompactStepRelativeBudget hrows fp A_hat b_hat alpha k <= cStep)
    (huniformBudget : forall k (hk : k < n),
      ((n : Real) * cStep) *
          vecNorm2 (fun i : Fin (n + m) => A_hat k i (Fin.mk k hk)) <
        Real.sqrt
          (householderTrailingNorm2Sq (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun i => A_hat k i (Fin.mk k hk))))
    (hFinal :
      A_hat n = fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (householder_paddedFinInput_R11 fp A)
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (12 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A)
      (frobNormRect A *
        frobNorm (nonsingInv n (householder_paddedFinInput_R11 fp A)))
      (((3 * Theorem19_4.gamma_tilde fp (n + m) n) *
          (frobNormRect A *
            frobNorm
              (nonsingInv n (householder_paddedFinInput_R11 fp A)))) ^ 2) := by
  exact
    mgs_qr_bounds_of_storedTrailingPanel_final_panel_eq_final_prevBlocks_uniform_step_budget_frob_condition_explicit_radius_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hnm hrows hsmall
      A_hat b_hat alpha cStep hm hStep halpha hdetPrevFinal hdetLead
      hsign hStepBudget huniformBudget hFinal
      (kappaA :=
        frobNormRect A *
          frobNorm (nonsingInv n (householder_paddedFinInput_R11 fp A)))
      le_rfl

/-- Determinant-routed pointwise-`R11` version of the stored-loop
Theorem 19.13 Frobenius-condition wrapper.

This consumes the final previous-leading-block determinant hypotheses together
with the explicit top-block `R11` bridge, then supplies the determinant
nonbreakdown certificate required by the existing condition-budget MGS route. -/
theorem
    mgs_qr_bounds_of_storedTrailingPanel_R11_final_prevBlocks_det_uniform_step_budget_frob_condition_explicit_radius_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hrows : n <= n + m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    (A_hat : Nat -> Fin (n + m) -> Fin n -> Real)
    (b_hat : Nat -> Fin (n + m) -> Real)
    (alpha : Nat -> Real)
    (cStep : Real)
    (hm : gammaValid fp (n + m))
    (hStep : forall k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (n + m) n k
          (householderTrailingActiveVector (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (n + m)
            (householderTrailingActiveVector (n + m)
              (Fin.mk k (lt_of_lt_of_le hk hrows))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (halpha : forall k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq (n + m)
          (Fin.mk k (lt_of_lt_of_le hk hrows))
          (fun i => A_hat k i (Fin.mk k hk)))
    (hdetPrevFinal : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat n)
            (le_trans (Nat.le_of_lt hk) hrows) hk :
            Matrix (Fin k) (Fin k) Real))
        0)
    (hdetLead : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrLeadingBlock (A_hat k)
            (le_trans (Nat.succ_le_of_lt hk) hrows) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) Real))
        0)
    (hsign : forall k (hk : k < n),
      alpha k *
          A_hat k (Fin.mk k (lt_of_lt_of_le hk hrows)) (Fin.mk k hk) <= 0)
    (hStepBudget : forall k : Fin n,
      storedQRCompactStepRelativeBudget hrows fp A_hat b_hat alpha k <= cStep)
    (huniformBudget : forall k (hk : k < n),
      ((n : Real) * cStep) *
          vecNorm2 (fun i : Fin (n + m) => A_hat k i (Fin.mk k hk)) <
        Real.sqrt
          (householderTrailingNorm2Sq (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun i => A_hat k i (Fin.mk k hk))))
    (hR11 : forall i j,
      householder_paddedFinInput_R11 fp A i j =
        A_hat n (Fin.mk i.val (lt_of_lt_of_le i.isLt hrows)) j)
    {kappaA : Real}
    (hcondition :
      frobNormRect A *
          frobNorm (nonsingInv n (householder_paddedFinInput_R11 fp A)) <=
        kappaA) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (householder_paddedFinInput_R11 fp A)
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (12 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA
      (((3 * Theorem19_4.gamma_tilde fp (n + m) n) * kappaA) ^ 2) := by
  have hdet :
      Ne
        (Matrix.det
          (householder_paddedFinInput_R11 fp A :
            Matrix (Fin n) (Fin n) Real))
        0 :=
    householder_paddedFinInput_R11_det_ne_zero_of_storedTrailingPanel_final_prevBlocks_uniform_step_budget
      (fp := fp) (m := m) (n := n) A hn hrows hsmall
      A_hat b_hat alpha cStep hm hStep halpha hdetPrevFinal hdetLead
      hsign hStepBudget huniformBudget hR11
  exact
    mgs_qr_bounds_of_R11_det_ne_zero_frob_condition_explicit_radius_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hnm hsmall
      (kappaA := kappaA) hdet hcondition

/-- Frobenius-self fallback version of
`mgs_qr_bounds_of_storedTrailingPanel_R11_final_prevBlocks_det_uniform_step_budget_frob_condition_explicit_radius_of_small_unit_roundoff`.

The pointwise `R11` bridge and stored-loop assumptions supply determinant
nonbreakdown; the fallback conditioning quantity is chosen internally. -/
theorem
    mgs_qr_bounds_of_storedTrailingPanel_R11_final_prevBlocks_det_uniform_step_budget_frob_self_condition_explicit_radius_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hrows : n <= n + m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    (A_hat : Nat -> Fin (n + m) -> Fin n -> Real)
    (b_hat : Nat -> Fin (n + m) -> Real)
    (alpha : Nat -> Real)
    (cStep : Real)
    (hm : gammaValid fp (n + m))
    (hStep : forall k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (n + m) n k
          (householderTrailingActiveVector (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (n + m)
            (householderTrailingActiveVector (n + m)
              (Fin.mk k (lt_of_lt_of_le hk hrows))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (halpha : forall k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq (n + m)
          (Fin.mk k (lt_of_lt_of_le hk hrows))
          (fun i => A_hat k i (Fin.mk k hk)))
    (hdetPrevFinal : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat n)
            (le_trans (Nat.le_of_lt hk) hrows) hk :
            Matrix (Fin k) (Fin k) Real))
        0)
    (hdetLead : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrLeadingBlock (A_hat k)
            (le_trans (Nat.succ_le_of_lt hk) hrows) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) Real))
        0)
    (hsign : forall k (hk : k < n),
      alpha k *
          A_hat k (Fin.mk k (lt_of_lt_of_le hk hrows)) (Fin.mk k hk) <= 0)
    (hStepBudget : forall k : Fin n,
      storedQRCompactStepRelativeBudget hrows fp A_hat b_hat alpha k <= cStep)
    (huniformBudget : forall k (hk : k < n),
      ((n : Real) * cStep) *
          vecNorm2 (fun i : Fin (n + m) => A_hat k i (Fin.mk k hk)) <
        Real.sqrt
          (householderTrailingNorm2Sq (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun i => A_hat k i (Fin.mk k hk))))
    (hR11 : forall i j,
      householder_paddedFinInput_R11 fp A i j =
        A_hat n (Fin.mk i.val (lt_of_lt_of_le i.isLt hrows)) j) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (householder_paddedFinInput_R11 fp A)
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (12 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A)
      (frobNormRect A *
        frobNorm (nonsingInv n (householder_paddedFinInput_R11 fp A)))
      (((3 * Theorem19_4.gamma_tilde fp (n + m) n) *
          (frobNormRect A *
            frobNorm
              (nonsingInv n (householder_paddedFinInput_R11 fp A)))) ^ 2) := by
  exact
    mgs_qr_bounds_of_storedTrailingPanel_R11_final_prevBlocks_det_uniform_step_budget_frob_condition_explicit_radius_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hnm hrows hsmall
      A_hat b_hat alpha cStep hm hStep halpha hdetPrevFinal hdetLead
      hsign hStepBudget huniformBudget hR11
      (kappaA :=
        frobNormRect A *
          frobNorm (nonsingInv n (householder_paddedFinInput_R11 fp A)))
      le_rfl

/-- Source-condition version of the determinant-routed pointwise-`R11`
stored-loop Theorem 19.13 wrapper.

Compared with the Frobenius fallback immediately above, this keeps the inverse
budget as the source-facing estimate `||A||_F * rho <= kappaA`, which is the
sharper condition-number gate still tracked for the final printed route. -/
theorem
    mgs_qr_bounds_of_storedTrailingPanel_R11_final_prevBlocks_det_uniform_step_budget_compact_condition_explicit_radius_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hrows : n <= n + m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    (A_hat : Nat -> Fin (n + m) -> Fin n -> Real)
    (b_hat : Nat -> Fin (n + m) -> Real)
    (alpha : Nat -> Real)
    (cStep : Real)
    (hm : gammaValid fp (n + m))
    (hStep : forall k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (n + m) n k
          (householderTrailingActiveVector (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (n + m)
            (householderTrailingActiveVector (n + m)
              (Fin.mk k (lt_of_lt_of_le hk hrows))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (halpha : forall k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq (n + m)
          (Fin.mk k (lt_of_lt_of_le hk hrows))
          (fun i => A_hat k i (Fin.mk k hk)))
    (hdetPrevFinal : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat n)
            (le_trans (Nat.le_of_lt hk) hrows) hk :
            Matrix (Fin k) (Fin k) Real))
        0)
    (hdetLead : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrLeadingBlock (A_hat k)
            (le_trans (Nat.succ_le_of_lt hk) hrows) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) Real))
        0)
    (hsign : forall k (hk : k < n),
      alpha k *
          A_hat k (Fin.mk k (lt_of_lt_of_le hk hrows)) (Fin.mk k hk) <= 0)
    (hStepBudget : forall k : Fin n,
      storedQRCompactStepRelativeBudget hrows fp A_hat b_hat alpha k <= cStep)
    (huniformBudget : forall k (hk : k < n),
      ((n : Real) * cStep) *
          vecNorm2 (fun i : Fin (n + m) => A_hat k i (Fin.mk k hk)) <
        Real.sqrt
          (householderTrailingNorm2Sq (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun i => A_hat k i (Fin.mk k hk))))
    (hR11 : forall i j,
      householder_paddedFinInput_R11 fp A i j =
        A_hat n (Fin.mk i.val (lt_of_lt_of_le i.isLt hrows)) j)
    {rho kappaA : Real}
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n (householder_paddedFinInput_R11 fp A))
        rho)
    (hrho : 0 <= rho)
    (hcondition : frobNormRect A * rho <= kappaA) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (householder_paddedFinInput_R11 fp A)
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (12 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA
      (((3 * Theorem19_4.gamma_tilde fp (n + m) n) * kappaA) ^ 2) := by
  have hdet :
      Ne
        (Matrix.det
          (householder_paddedFinInput_R11 fp A :
            Matrix (Fin n) (Fin n) Real))
        0 :=
    householder_paddedFinInput_R11_det_ne_zero_of_storedTrailingPanel_final_prevBlocks_uniform_step_budget
      (fp := fp) (m := m) (n := n) A hn hrows hsmall
      A_hat b_hat alpha cStep hm hStep halpha hdetPrevFinal hdetLead
      hsign hStepBudget huniformBudget hR11
  exact
    mgs_qr_bounds_of_R11_det_ne_zero_compact_condition_explicit_radius_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hnm hsmall
      (rho := rho) (kappaA := kappaA) hdet hRinv hrho hcondition

/-- Determinant-routed final-panel equality version of the stored-loop
Theorem 19.13 Frobenius-condition wrapper.

This consumes final previous-leading-block determinant hypotheses and the full
recursive/stored final-panel equality to produce the determinant nonbreakdown
certificate for the existing `R11` condition route. -/
theorem
    mgs_qr_bounds_of_storedTrailingPanel_final_panel_eq_final_prevBlocks_det_uniform_step_budget_frob_condition_explicit_radius_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hrows : n <= n + m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    (A_hat : Nat -> Fin (n + m) -> Fin n -> Real)
    (b_hat : Nat -> Fin (n + m) -> Real)
    (alpha : Nat -> Real)
    (cStep : Real)
    (hm : gammaValid fp (n + m))
    (hStep : forall k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (n + m) n k
          (householderTrailingActiveVector (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (n + m)
            (householderTrailingActiveVector (n + m)
              (Fin.mk k (lt_of_lt_of_le hk hrows))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (halpha : forall k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq (n + m)
          (Fin.mk k (lt_of_lt_of_le hk hrows))
          (fun i => A_hat k i (Fin.mk k hk)))
    (hdetPrevFinal : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat n)
            (le_trans (Nat.le_of_lt hk) hrows) hk :
            Matrix (Fin k) (Fin k) Real))
        0)
    (hdetLead : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrLeadingBlock (A_hat k)
            (le_trans (Nat.succ_le_of_lt hk) hrows) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) Real))
        0)
    (hsign : forall k (hk : k < n),
      alpha k *
          A_hat k (Fin.mk k (lt_of_lt_of_le hk hrows)) (Fin.mk k hk) <= 0)
    (hStepBudget : forall k : Fin n,
      storedQRCompactStepRelativeBudget hrows fp A_hat b_hat alpha k <= cStep)
    (huniformBudget : forall k (hk : k < n),
      ((n : Real) * cStep) *
          vecNorm2 (fun i : Fin (n + m) => A_hat k i (Fin.mk k hk)) <
        Real.sqrt
          (householderTrailingNorm2Sq (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun i => A_hat k i (Fin.mk k hk))))
    (hFinal :
      A_hat n = fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
    {kappaA : Real}
    (hcondition :
      frobNormRect A *
          frobNorm (nonsingInv n (householder_paddedFinInput_R11 fp A)) <=
        kappaA) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (householder_paddedFinInput_R11 fp A)
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (12 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA
      (((3 * Theorem19_4.gamma_tilde fp (n + m) n) * kappaA) ^ 2) := by
  have hdet :
      Ne
        (Matrix.det
          (householder_paddedFinInput_R11 fp A :
            Matrix (Fin n) (Fin n) Real))
        0 :=
    householder_paddedFinInput_R11_det_ne_zero_of_storedTrailingPanel_final_panel_eq_final_prevBlocks_uniform_step_budget
      (fp := fp) (m := m) (n := n) A hn hrows hsmall
      A_hat b_hat alpha cStep hm hStep halpha hdetPrevFinal hdetLead
      hsign hStepBudget huniformBudget hFinal
  exact
    mgs_qr_bounds_of_R11_det_ne_zero_frob_condition_explicit_radius_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hnm hsmall
      (kappaA := kappaA) hdet hcondition

/-- Frobenius-self fallback version of
`mgs_qr_bounds_of_storedTrailingPanel_final_panel_eq_final_prevBlocks_det_uniform_step_budget_frob_condition_explicit_radius_of_small_unit_roundoff`.

The stored-loop assumptions supply the determinant nonbreakdown certificate;
the fallback conditioning quantity is chosen internally. -/
theorem
    mgs_qr_bounds_of_storedTrailingPanel_final_panel_eq_final_prevBlocks_det_uniform_step_budget_frob_self_condition_explicit_radius_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hrows : n <= n + m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    (A_hat : Nat -> Fin (n + m) -> Fin n -> Real)
    (b_hat : Nat -> Fin (n + m) -> Real)
    (alpha : Nat -> Real)
    (cStep : Real)
    (hm : gammaValid fp (n + m))
    (hStep : forall k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (n + m) n k
          (householderTrailingActiveVector (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (n + m)
            (householderTrailingActiveVector (n + m)
              (Fin.mk k (lt_of_lt_of_le hk hrows))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (halpha : forall k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq (n + m)
          (Fin.mk k (lt_of_lt_of_le hk hrows))
          (fun i => A_hat k i (Fin.mk k hk)))
    (hdetPrevFinal : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat n)
            (le_trans (Nat.le_of_lt hk) hrows) hk :
            Matrix (Fin k) (Fin k) Real))
        0)
    (hdetLead : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrLeadingBlock (A_hat k)
            (le_trans (Nat.succ_le_of_lt hk) hrows) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) Real))
        0)
    (hsign : forall k (hk : k < n),
      alpha k *
          A_hat k (Fin.mk k (lt_of_lt_of_le hk hrows)) (Fin.mk k hk) <= 0)
    (hStepBudget : forall k : Fin n,
      storedQRCompactStepRelativeBudget hrows fp A_hat b_hat alpha k <= cStep)
    (huniformBudget : forall k (hk : k < n),
      ((n : Real) * cStep) *
          vecNorm2 (fun i : Fin (n + m) => A_hat k i (Fin.mk k hk)) <
        Real.sqrt
          (householderTrailingNorm2Sq (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun i => A_hat k i (Fin.mk k hk))))
    (hFinal :
      A_hat n = fl_householderQRPanel_R fp (n + m) n (paddedFinInput A)) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (householder_paddedFinInput_R11 fp A)
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (12 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A)
      (frobNormRect A *
        frobNorm (nonsingInv n (householder_paddedFinInput_R11 fp A)))
      (((3 * Theorem19_4.gamma_tilde fp (n + m) n) *
          (frobNormRect A *
            frobNorm
              (nonsingInv n (householder_paddedFinInput_R11 fp A)))) ^ 2) := by
  exact
    mgs_qr_bounds_of_storedTrailingPanel_final_panel_eq_final_prevBlocks_det_uniform_step_budget_frob_condition_explicit_radius_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hnm hrows hsmall
      A_hat b_hat alpha cStep hm hStep halpha hdetPrevFinal hdetLead
      hsign hStepBudget huniformBudget hFinal
      (kappaA :=
        frobNormRect A *
          frobNorm (nonsingInv n (householder_paddedFinInput_R11 fp A)))
      le_rfl

/-- Source-condition version of the determinant-routed final-panel equality
stored-loop Theorem 19.13 wrapper.

The full recursive/stored final-panel equality supplies the top-block `R11`
bridge internally, while the condition estimate remains visible as
`||A||_F * rho <= kappaA` for the final source-condition proof. -/
theorem
    mgs_qr_bounds_of_storedTrailingPanel_final_panel_eq_final_prevBlocks_det_uniform_step_budget_compact_condition_explicit_radius_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hrows : n <= n + m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    (A_hat : Nat -> Fin (n + m) -> Fin n -> Real)
    (b_hat : Nat -> Fin (n + m) -> Real)
    (alpha : Nat -> Real)
    (cStep : Real)
    (hm : gammaValid fp (n + m))
    (hStep : forall k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp (n + m) n k
          (householderTrailingActiveVector (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun a => A_hat k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec (n + m)
            (householderTrailingActiveVector (n + m)
              (Fin.mk k (lt_of_lt_of_le hk hrows))
              (fun a => A_hat k a (Fin.mk k hk)) (alpha k)))
          (A_hat k))
    (halpha : forall k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq (n + m)
          (Fin.mk k (lt_of_lt_of_le hk hrows))
          (fun i => A_hat k i (Fin.mk k hk)))
    (hdetPrevFinal : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrPreviousLeadingBlockTranspose (A_hat n)
            (le_trans (Nat.le_of_lt hk) hrows) hk :
            Matrix (Fin k) (Fin k) Real))
        0)
    (hdetLead : forall k (hk : k < n),
      Ne
        (Matrix.det
          (qrLeadingBlock (A_hat k)
            (le_trans (Nat.succ_le_of_lt hk) hrows) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) Real))
        0)
    (hsign : forall k (hk : k < n),
      alpha k *
          A_hat k (Fin.mk k (lt_of_lt_of_le hk hrows)) (Fin.mk k hk) <= 0)
    (hStepBudget : forall k : Fin n,
      storedQRCompactStepRelativeBudget hrows fp A_hat b_hat alpha k <= cStep)
    (huniformBudget : forall k (hk : k < n),
      ((n : Real) * cStep) *
          vecNorm2 (fun i : Fin (n + m) => A_hat k i (Fin.mk k hk)) <
        Real.sqrt
          (householderTrailingNorm2Sq (n + m)
            (Fin.mk k (lt_of_lt_of_le hk hrows))
            (fun i => A_hat k i (Fin.mk k hk))))
    (hFinal :
      A_hat n = fl_householderQRPanel_R fp (n + m) n (paddedFinInput A))
    {rho kappaA : Real}
    (hRinv :
      rectOpNorm2Le
        (nonsingInv n (householder_paddedFinInput_R11 fp A))
        rho)
    (hrho : 0 <= rho)
    (hcondition : frobNormRect A * rho <= kappaA) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (householder_paddedFinInput_R11 fp A)
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (12 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA
      (((3 * Theorem19_4.gamma_tilde fp (n + m) n) * kappaA) ^ 2) := by
  exact
    mgs_qr_bounds_of_storedTrailingPanel_R11_final_prevBlocks_det_uniform_step_budget_compact_condition_explicit_radius_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hnm hrows hsmall
      A_hat b_hat alpha cStep hm hStep halpha hdetPrevFinal hdetLead
      hsign hStepBudget huniformBudget
      (householder_paddedFinInput_R11_eq_top_block_of_final_panel_eq
        fp A hrows A_hat hFinal)
      (rho := rho) (kappaA := kappaA) hRinv hrho hcondition

/-- Source-diagonal Frobenius-self fallback route for the chapter-facing
Theorem 19.13 assembly.

This keeps the remaining source nonbreakdown input in diagonal form while
choosing the fallback condition quantity
`kappaA = ||A||_F * ||nonsingInv R11||_F`. -/
theorem
    mgs_qr_bounds_of_R11_diag_ne_zero_frob_self_condition_explicit_radius_of_small_unit_roundoff
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    (hdiag :
      forall i : Fin n,
        Ne (householder_paddedFinInput_R11 fp A i i) 0) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (householder_paddedFinInput_R11 fp A)
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (12 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A)
      (frobNormRect A *
        frobNorm (nonsingInv n (householder_paddedFinInput_R11 fp A)))
      (((3 * Theorem19_4.gamma_tilde fp (n + m) n) *
          (frobNormRect A *
            frobNorm
              (nonsingInv n (householder_paddedFinInput_R11 fp A)))) ^ 2) := by
  exact
    mgs_qr_bounds_of_R11_diag_ne_zero_frob_condition_explicit_radius_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hnm hsmall
      (kappaA :=
        frobNormRect A *
          frobNorm (nonsingInv n (householder_paddedFinInput_R11 fp A)))
      hdiag le_rfl

/-- Chapter-facing Theorem 19.13 assembly currently proved for the concrete
padded Householder route.

The CS/polar repair witness and the `nonsingInv` operator certificate are
constructed internally. The remaining source-strength obligations are explicit:
the actual extracted `R11` block must be nonsingular, and the final
Frobenius-inverse budget must match the advertised condition-number term. -/
theorem mgs_qr_bounds
    (fp : FPModel) {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hn : 0 < n)
    (hnm : n <= m)
    (hsmall :
      (((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real) *
        fp.u <= 1 / 2))
    {c2 kappaA higherOrder : Real}
    (hdet :
      Ne
        (Matrix.det
          (householder_paddedFinInput_R11 fp A :
            Matrix (Fin n) (Fin n) Real))
        0)
    (hbudget :
      2 *
          (((Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A) +
                2 *
                  (Theorem19_4.gamma_tilde fp (n + m) n *
                    frobNormRect A)) *
              frobNorm (nonsingInv n (householder_paddedFinInput_R11 fp A))) +
            (((Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A) +
                  2 *
                    (Theorem19_4.gamma_tilde fp (n + m) n *
                      frobNormRect A)) *
                frobNorm
                  (nonsingInv n (householder_paddedFinInput_R11 fp A))) ^ 2 <=
        c2 * fp.u * kappaA + higherOrder) :
    MGSQRBounds m n A
      (paddedEconomyQ
        (fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)))
      (householder_paddedFinInput_R11 fp A)
      (2 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      c2
      (4 * ((n * householderConstructApplyGammaIndex (n + m) : Nat) : Real))
      fp.u (frobNormRect A) kappaA higherOrder := by
  exact
    mgs_qr_bounds_of_householder_det_ne_zero_csPolarRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff
      (fp := fp) (m := m) (n := n) A hn hnm hsmall
      (eta1 := Theorem19_4.gamma_tilde fp (n + m) n * frobNormRect A)
      (c2 := c2) (kappaA := kappaA) (higherOrder := higherOrder)
      (by
        simpa [householder_paddedFinInput_R11] using hdet)
      (le_rfl)
      (by
        simpa [householder_paddedFinInput_R11] using hbudget)

end Theorem19_13

namespace Theorem19_10

/-- Formal coefficient used for the Higham 19.10 Givens QR bound.

The printed theorem writes a dimension-dependent modest multiple of the unit
roundoff.  The current implementation exposes the conservative coefficient
proved by the concrete staged Givens QR schedule. -/
noncomputable def gamma_tilde (fp : FPModel) (m n : Nat) : Real :=
  residualAccumBound
    (residualAccumBound (gamma fp 8 * Real.sqrt (m : Real))
      (givensQRStageTaskList m n (givensQRStageCount m n)).length)
    (givensQRStageCount m n)

/-- Equation `(19.25)` coefficient currently proved for the concrete staged
Givens QR schedule.

The printed source leaves this as a modest dimension-dependent `gamma_tilde`;
the implementation exposes the exact conservative accumulator generated by the
verified anti-diagonal Givens task schedule. -/
theorem eq19_25_gamma_tilde_eq_concrete_staged_coefficient
    (fp : FPModel) (m n : Nat) :
    gamma_tilde fp m n =
      residualAccumBound
        (residualAccumBound (gamma fp 8 * Real.sqrt (m : Real))
          (givensQRStageTaskList m n (givensQRStageCount m n)).length)
        (givensQRStageCount m n) := rfl

/-- Source-facing form of Higham, Theorem 19.10.

The contract records the computed upper-trapezoidal `R_hat`, an exact
orthogonal witness `Q`, the equation `A + dA = Q * R_hat`, and the advertised
columnwise perturbation shape for the Givens QR path. -/
structure GivensQRBackwardError (m n : Nat)
    (A : Fin m -> Fin n -> Real) (Q : Fin m -> Fin m -> Real)
    (R_hat : Fin m -> Fin n -> Real) (c : Real) : Prop where
  upper : IsUpperTrapezoidal m n R_hat
  orth : IsOrthogonal m Q
  result : Exists fun dA : Fin m -> Fin n -> Real =>
    (forall i j, A i j + dA i j = matMulRect m m n Q R_hat i j) /\
    (forall j, columnFrob dA j <= c * columnFrob A j)

/-- Higham, Theorem 19.10: Givens QR backward error for a tall rectangular
matrix, stated with the public Split 3B source-facing name.

For `A : R^(m x n)` with `0 < n` and `n <= m`, the concrete staged Givens QR
algorithm returns an upper-trapezoidal `R_hat` and an exact orthogonal witness
`Q` such that `A + dA = Q R_hat`, with each perturbation column bounded by the
repository's conservative `gamma_tilde fp m n` times the corresponding input
column norm. -/
theorem givens_qr_backward_error
    (fp : FPModel) (m n : Nat) (A : Fin m -> Fin n -> Real)
    (_hn : 0 < n) (_hnm : n <= m)
    (hvalid : gammaValid fp 8) :
    GivensQRBackwardError m n A
      (Classical.choose
        (fl_givensQRStageFold_sequence_columnFrob_backward_error_uniform
          fp m n A (givensQRStageCount m n) hvalid))
      (fl_givensQRStageFold fp m n (givensQRStageCount m n) A)
      (gamma_tilde fp m n) := by
  classical
  let hstage :=
    fl_givensQRStageFold_sequence_columnFrob_backward_error_uniform
      fp m n A (givensQRStageCount m n) hvalid
  let Q : Fin m -> Fin m -> Real := Classical.choose hstage
  let hstage_tail := Classical.choose_spec hstage
  let dA : Fin m -> Fin n -> Real := Classical.choose hstage_tail
  have hstage_spec := Classical.choose_spec hstage_tail
  have hQ : IsOrthogonal m Q := hstage_spec.1
  have hrepr :
      forall (i : Fin m) (j : Fin n),
        fl_givensQRStageFold fp m n (givensQRStageCount m n) A i j =
          matMulRect m m n (matTranspose Q)
            (fun a b => A a b + dA a b) i j :=
    hstage_spec.2.1
  have hbound :
      forall j,
        columnFrob dA j <=
          gamma_tilde fp m n * columnFrob A j := by
    intro j
    simpa [gamma_tilde, dA] using hstage_spec.2.2 j
  refine {
    upper := fl_givensQRStageFold_upper_trapezoidal
      fp m n A
    orth := hQ
    result := ?_
  }
  refine Exists.intro dA ?_
  refine And.intro ?_ hbound
  intro i j
  let R_hat : Fin m -> Fin n -> Real :=
    fl_givensQRStageFold fp m n (givensQRStageCount m n) A
  have hRmat :
      R_hat =
        matMulRect m m n (matTranspose Q)
          (fun a b => A a b + dA a b) := by
    ext a b
    exact hrepr a b
  have hQQT : matMul m Q (matTranspose Q) = idMatrix m := by
    ext a b
    exact hQ.right_inv a b
  calc
    A i j + dA i j =
        matMulRect m m n (idMatrix m)
          (fun a b => A a b + dA a b) i j := by
          rw [matMulRect_id_left]
    _ = matMulRect m m n (matMul m Q (matTranspose Q))
          (fun a b => A a b + dA a b) i j := by
          rw [hQQT]
    _ = matMulRect m m n Q
          (matMulRect m m n (matTranspose Q)
            (fun a b => A a b + dA a b)) i j := by
          rw [matMulRect_assoc_square_left]
    _ = matMulRect m m n Q R_hat i j := by
          rw [<- hRmat]

/-- Equation `(19.25)` source row for the concrete staged Givens QR path.

This packages the verified columnwise sequence perturbation bound under the
conservative coefficient `H19.Theorem19_10.gamma_tilde`.  The exact
printed-constant comparison remains a separate audit from this source-row
wrapper. -/
theorem eq19_25_columnwise_perturbation_bound
    (fp : FPModel) (m n : Nat) (A : Fin m -> Fin n -> Real)
    (hn : 0 < n) (hnm : n <= m)
    (hvalid : gammaValid fp 8) :
    Exists fun Q : Fin m -> Fin m -> Real =>
      GivensQRBackwardError m n A Q
        (fl_givensQRStageFold fp m n (givensQRStageCount m n) A)
        (gamma_tilde fp m n) := by
  classical
  let hstage :=
    fl_givensQRStageFold_sequence_columnFrob_backward_error_uniform
      fp m n A (givensQRStageCount m n) hvalid
  refine Exists.intro (Classical.choose hstage) ?_
  simpa [hstage] using givens_qr_backward_error fp m n A hn hnm hvalid

/-- Theorem 19.10 exposed through its equation `(19.25)` columnwise
perturbation row. -/
theorem eq19_25_givens_qr_backward_error
    (fp : FPModel) (m n : Nat) (A : Fin m -> Fin n -> Real)
    (hn : 0 < n) (hnm : n <= m)
    (hvalid : gammaValid fp 8) :
    GivensQRBackwardError m n A
      (Classical.choose
        (fl_givensQRStageFold_sequence_columnFrob_backward_error_uniform
          fp m n A (givensQRStageCount m n) hvalid))
      (fl_givensQRStageFold fp m n (givensQRStageCount m n) A)
      (gamma_tilde fp m n) :=
  givens_qr_backward_error fp m n A hn hnm hvalid

end Theorem19_10

end
end H19
