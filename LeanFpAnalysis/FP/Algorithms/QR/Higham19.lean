import LeanFpAnalysis.FP.Algorithms.QR.GivensQR
import LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt
import LeanFpAnalysis.FP.Algorithms.QR.GramSchmidtPolar
import LeanFpAnalysis.FP.Algorithms.QR.HouseholderQR

open LeanFpAnalysis.FP

namespace H19

noncomputable section

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

end Theorem19_10

end
end H19
