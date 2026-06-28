import LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt
import LeanFpAnalysis.FP.Algorithms.RandNLA.LowRankApprox

namespace LeanFpAnalysis.FP

open scoped BigOperators

noncomputable section

/-!
Polar/SVD adapters for the remaining Higham Problem 19.12 route.

The main Gram-Schmidt file keeps the downstream correction-map algebra.  This
file connects that algebra to the repository's existing exact right-Gram SVD
objects in the full-positive singular-value branch.
-/

/-- Full-positive right-Gram polar isometry `U * V^T` attached to a rectangular
matrix `A`.  This is an exact analysis object, not a computed factorization. -/
noncomputable def rectRightGramPolarQFull {m n : Nat}
    (A : Fin m -> Fin n -> Real) : Fin m -> Fin n -> Real :=
  matMulRect m n n
    (rectRightGramLeftSingularFromEigenbasis A)
    (finiteTranspose (rectRightGramEigenbasis A))

/-- Full-positive right-Gram polar positive factor `V * Sigma * V^T` attached
to a rectangular matrix `A`. -/
noncomputable def rectRightGramPolarH {m n : Nat}
    (A : Fin m -> Fin n -> Real) : Fin n -> Fin n -> Real :=
  matMul n (rectRightGramEigenbasis A)
    (matMul n (finiteDiagonal (rectRightGramBasisSingularValue A))
      (finiteTranspose (rectRightGramEigenbasis A)))

/-- In the full-positive branch, the right-Gram polar isometry has orthonormal
columns. -/
theorem rectRightGramPolarQFull_orthonormal_of_pos {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (hpos : forall a : Fin n, 0 < rectRightGramBasisSingularValue A a) :
    GramSchmidtOrthonormalColumns (rectRightGramPolarQFull A) := by
  intro j k
  unfold rectangularGram rectRightGramPolarQFull
  unfold matMulRect finiteTranspose
  calc
    (Finset.univ.sum fun i : Fin m =>
        (Finset.univ.sum fun a : Fin n =>
          rectRightGramLeftSingularFromEigenbasis A i a *
            rectRightGramEigenbasis A j a) *
        (Finset.univ.sum fun b : Fin n =>
          rectRightGramLeftSingularFromEigenbasis A i b *
            rectRightGramEigenbasis A k b))
        =
      Finset.univ.sum fun a : Fin n =>
        Finset.univ.sum fun b : Fin n =>
          (Finset.univ.sum fun i : Fin m =>
            rectRightGramLeftSingularFromEigenbasis A i a *
              rectRightGramLeftSingularFromEigenbasis A i b) *
            (rectRightGramEigenbasis A j a *
              rectRightGramEigenbasis A k b) := by
        calc
          (Finset.univ.sum fun i : Fin m =>
              (Finset.univ.sum fun a : Fin n =>
                rectRightGramLeftSingularFromEigenbasis A i a *
                  rectRightGramEigenbasis A j a) *
              (Finset.univ.sum fun b : Fin n =>
                rectRightGramLeftSingularFromEigenbasis A i b *
                  rectRightGramEigenbasis A k b))
              =
            Finset.univ.sum fun i : Fin m =>
              Finset.univ.sum fun a : Fin n =>
                Finset.univ.sum fun b : Fin n =>
                  (rectRightGramLeftSingularFromEigenbasis A i a *
                      rectRightGramEigenbasis A j a) *
                    (rectRightGramLeftSingularFromEigenbasis A i b *
                      rectRightGramEigenbasis A k b) := by
              apply Finset.sum_congr rfl
              intro i _hi
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro a _ha
              rw [Finset.mul_sum]
          _ =
            Finset.univ.sum fun a : Fin n =>
              Finset.univ.sum fun b : Fin n =>
                Finset.univ.sum fun i : Fin m =>
                  (rectRightGramLeftSingularFromEigenbasis A i a *
                      rectRightGramEigenbasis A j a) *
                    (rectRightGramLeftSingularFromEigenbasis A i b *
                      rectRightGramEigenbasis A k b) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro a _ha
              rw [Finset.sum_comm]
          _ =
            Finset.univ.sum fun a : Fin n =>
              Finset.univ.sum fun b : Fin n =>
                (Finset.univ.sum fun i : Fin m =>
                  rectRightGramLeftSingularFromEigenbasis A i a *
                    rectRightGramLeftSingularFromEigenbasis A i b) *
                  (rectRightGramEigenbasis A j a *
                    rectRightGramEigenbasis A k b) := by
              apply Finset.sum_congr rfl
              intro a _ha
              apply Finset.sum_congr rfl
              intro b _hb
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i _hi
              ring
    _ =
      Finset.univ.sum fun a : Fin n =>
        Finset.univ.sum fun b : Fin n =>
          idMatrix n a b *
            (rectRightGramEigenbasis A j a *
              rectRightGramEigenbasis A k b) := by
        apply Finset.sum_congr rfl
        intro a _ha
        apply Finset.sum_congr rfl
        intro b _hb
        rw [rectRightGramLeftSingularFromEigenbasis_col_orthonormal_of_pos
          A hpos a b]
    _ =
      Finset.univ.sum fun a : Fin n =>
        rectRightGramEigenbasis A j a *
          rectRightGramEigenbasis A k a := by
        simp [idMatrix]
    _ = idMatrix n j k := by
        simpa [idMatrix] using
          rectRightGramEigenbasis_row_orthonormal A j k

/-- Full-positive SVD reconstruction in matrix-product form. -/
theorem rectRightGramLeftSingularFromEigenbasis_mul_diagonal_transpose_eq
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hpos : forall a : Fin n, 0 < rectRightGramBasisSingularValue A a) :
    matMulRect m n n (rectRightGramLeftSingularFromEigenbasis A)
      (matMul n (finiteDiagonal (rectRightGramBasisSingularValue A))
        (finiteTranspose (rectRightGramEigenbasis A))) = A := by
  ext i j
  have h := rectRightGram_fullPositive_basisSVD_representation A hpos i j
  calc
    matMulRect m n n (rectRightGramLeftSingularFromEigenbasis A)
        (matMul n (finiteDiagonal (rectRightGramBasisSingularValue A))
          (finiteTranspose (rectRightGramEigenbasis A))) i j
        =
      Finset.univ.sum fun a : Fin n =>
        rectRightGramLeftSingularFromEigenbasis A i a *
          (rectRightGramBasisSingularValue A a *
            rectRightGramEigenbasis A j a) := by
        simp [matMulRect, matMul, finiteDiagonal, finiteTranspose]
    _ =
      Finset.univ.sum fun a : Fin n =>
        rectRightGramLeftSingularFromEigenbasis A i a *
          rectRightGramBasisSingularValue A a *
          rectRightGramEigenbasis A j a := by
        apply Finset.sum_congr rfl
        intro a _ha
        ring
    _ = A i j := h.symm

/-- In the full-positive branch, the exact right-Gram polar factors reconstruct
the original rectangular matrix. -/
theorem rectRightGramPolarQFull_mul_polarH_of_pos {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (hpos : forall a : Fin n, 0 < rectRightGramBasisSingularValue A a) :
    matMulRect m n n (rectRightGramPolarQFull A) (rectRightGramPolarH A) =
      A := by
  let U := rectRightGramLeftSingularFromEigenbasis A
  let V := rectRightGramEigenbasis A
  let D := finiteDiagonal (rectRightGramBasisSingularValue A)
  let Vt := finiteTranspose V
  have hVtV : matMul n Vt V = idMatrix n := by
    ext a b
    simpa [Vt, V, matMul, finiteTranspose] using
      rectRightGramEigenbasis_col_orthonormal A a b
  have hUDV : matMulRect m n n U (matMul n D Vt) = A := by
    simpa [U, V, D, Vt] using
      rectRightGramLeftSingularFromEigenbasis_mul_diagonal_transpose_eq
        A hpos
  calc
    matMulRect m n n (rectRightGramPolarQFull A) (rectRightGramPolarH A)
        =
      matMulRect m n n (matMulRect m n n U Vt)
        (matMul n V (matMul n D Vt)) := by
        rfl
    _ =
      matMulRect m n n U
        (matMul n Vt (matMul n V (matMul n D Vt))) := by
        rw [matMulRect_assoc_square_right]
    _ =
      matMulRect m n n U
        (matMul n (matMul n Vt V) (matMul n D Vt)) := by
        rw [<- matMul_assoc]
    _ =
      matMulRect m n n U
        (matMul n (idMatrix n) (matMul n D Vt)) := by
        rw [hVtV]
    _ = matMulRect m n n U (matMul n D Vt) := by
        rw [matMul_id_left]
    _ = A := hUDV

/-- The full-positive right-Gram polar positive factor is symmetric. -/
theorem rectRightGramPolarH_symmetric {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    finiteTranspose (rectRightGramPolarH A) = rectRightGramPolarH A := by
  let V := rectRightGramEigenbasis A
  let D := finiteDiagonal (rectRightGramBasisSingularValue A)
  let Vt := finiteTranspose V
  calc
    finiteTranspose (rectRightGramPolarH A)
        = finiteTranspose (matMul n V (matMul n D Vt)) := by
        rfl
    _ =
      matMul n (finiteTranspose (matMul n D Vt)) (finiteTranspose V) := by
        rw [finiteTranspose_matMul]
    _ =
      matMul n (matMul n (finiteTranspose Vt) (finiteTranspose D))
        (finiteTranspose V) := by
        rw [finiteTranspose_matMul]
    _ = matMul n (matMul n V D) Vt := by
        rw [finiteTranspose_finiteTranspose, finiteTranspose_finiteDiagonal]
    _ = matMul n V (matMul n D Vt) := by
        rw [matMul_assoc]
    _ = rectRightGramPolarH A := by
        rfl

/-- In the full-positive right-Gram polar branch, `H^2` is the rectangular
right Gram `A^T A`. -/
theorem rectRightGramPolarH_sq_eq_rectangularGram_of_pos {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (hpos : forall a : Fin n, 0 < rectRightGramBasisSingularValue A a) :
    matMul n (rectRightGramPolarH A) (rectRightGramPolarH A) =
      rectangularGram A := by
  have horth : GramSchmidtOrthonormalColumns (rectRightGramPolarQFull A) :=
    rectRightGramPolarQFull_orthonormal_of_pos A hpos
  have hfactor :
      matMulRect m n n (rectRightGramPolarQFull A)
          (rectRightGramPolarH A) = A :=
    rectRightGramPolarQFull_mul_polarH_of_pos A hpos
  have hgram :=
    rectangularGram_matMulRect_of_orthonormal_left horth
      (rectRightGramPolarH A)
  rw [hfactor] at hgram
  rw [rectRightGramPolarH_symmetric A] at hgram
  exact hgram.symm

/-- Full-positive polar rewrite of the top Gram in a corrected Problem 19.12
CS/polar input: `P11^T P11 = I - H^2`. -/
theorem MGSProblem1912CSPolarInput.p11_gram_eq_id_sub_polarH_sq
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : MGSProblem1912CSPolarInput m n P11 P21)
    (hpos : forall a : Fin n, 0 < rectRightGramBasisSingularValue P21 a) :
    rectangularGram P11 =
      fun i j =>
        idMatrix n i j -
          matMul n (rectRightGramPolarH P21) (rectRightGramPolarH P21) i j := by
  have hp21 :
      rectangularGram P21 =
        matMul n (rectRightGramPolarH P21) (rectRightGramPolarH P21) := by
    exact (rectRightGramPolarH_sq_eq_rectangularGram_of_pos P21 hpos).symm
  rw [hinput.p11_gram_eq_id_sub_p21_gram, hp21]

/-- Full-positive right-Gram polar factors give the bottom factor and
orthonormal part required by the Problem 19.12 polar payload.  The bridge
`T * P11 = I - H` and contraction bound remain explicit obligations. -/
def mgsProblem1912_polarFactorData_of_fullPositive_rightGram
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    {T : Fin n -> Fin n -> Real}
    (hpos : forall a : Fin n, 0 < rectRightGramBasisSingularValue P21 a)
    (hTP :
      matMul n T P11 =
        fun i j => idMatrix n i j - rectRightGramPolarH P21 i j)
    (hT : opNorm2Le T 1) :
    MGSProblem1912PolarFactorData m n P11 P21 where
  q := rectRightGramPolarQFull P21
  hMat := rectRightGramPolarH P21
  tMat := T
  bottom_factor :=
    (rectRightGramPolarQFull_mul_polarH_of_pos P21 hpos).symm
  bridge_factor := hTP
  q_orth := rectRightGramPolarQFull_orthonormal_of_pos P21 hpos
  t_bound := hT

/-- Full-positive right-Gram polar factors plus the remaining bridge produce
pure Problem 19.12 correction-map data. -/
theorem mgsProblem1912_correctionMapData_exists_of_fullPositive_rightGram
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    {T : Fin n -> Fin n -> Real}
    (hpos : forall a : Fin n, 0 < rectRightGramBasisSingularValue P21 a)
    (hTP :
      matMul n T P11 =
        fun i j => idMatrix n i j - rectRightGramPolarH P21 i j)
    (hT : opNorm2Le T 1) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      MGSProblem1912CorrectionMapData m n P11 P21 Q F := by
  exact
    mgsProblem1912_correctionMapData_exists_of_polarFactorData
      (mgsProblem1912_polarFactorData_of_fullPositive_rightGram
        hpos hTP hT)

/-- Full-positive right-Gram polar factors plus the remaining bridge produce
additive Problem 19.12 witnesses. -/
theorem mgsProblem1912_add_factor_exists_of_fullPositive_rightGram
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    {T : Fin n -> Fin n -> Real}
    (hpos : forall a : Fin n, 0 < rectRightGramBasisSingularValue P21 a)
    (hTP :
      matMul n T P11 =
        fun i j => idMatrix n i j - rectRightGramPolarH P21 i j)
    (hT : opNorm2Le T 1) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      (Q = fun i j => P21 i j + matMulRect m n n F P11 i j) /\
        GramSchmidtOrthonormalColumns Q /\
        rectOpNorm2Le F 1 := by
  exact
    mgsProblem1912_add_factor_exists_of_polarFactorData
      (mgsProblem1912_polarFactorData_of_fullPositive_rightGram
        hpos hTP hT)

end

end LeanFpAnalysis.FP
