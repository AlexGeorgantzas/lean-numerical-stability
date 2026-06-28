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

/-- Right distributivity for square matrix subtraction. -/
theorem matMul_sub_right_square (n : Nat)
    (A B C : Fin n -> Fin n -> Real) :
    matMul n A (fun i j => B i j - C i j) =
      fun i j => matMul n A B i j - matMul n A C i j := by
  ext i j
  unfold matMul
  rw [<- Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  ring

/-- Scalar estimate for the diagonal entries of `(I + H)^{-1}` when
`H` is positive semidefinite. -/
theorem inv_one_add_abs_le_one_of_nonneg {s : Real} (hs : 0 <= s) :
    |(1 : Real) / (1 + s)| <= 1 := by
  have hden_pos : 0 < 1 + s := by linarith
  have hden_ge_one : 1 <= 1 + s := by linarith
  calc
    |(1 : Real) / (1 + s)| = (1 : Real) / (1 + s) := by
      rw [abs_of_pos]
      positivity
    _ <= 1 := by
      exact (div_le_one hden_pos).2 hden_ge_one

/-- Scalar identity `(1+s)^{-1} * (1-s^2) = 1-s` for `s >= 0`. -/
theorem inv_one_add_mul_one_sub_sq {s : Real} (hs : 0 <= s) :
    (1 / (1 + s)) * (1 - s ^ 2) = (1 : Real) - s := by
  have hden_pos : 0 < 1 + s := by linarith
  have hden_ne : Ne (1 + s) 0 := ne_of_gt hden_pos
  field_simp [hden_ne]
  ring

/-- A finite diagonal matrix with entries `(1+s_i)^{-1}` is contractive when
all `s_i` are nonnegative. -/
theorem opNorm2Le_finiteDiagonal_inv_one_add_of_nonneg {n : Nat}
    (s : Fin n -> Real) (hs : forall i, 0 <= s i) :
    opNorm2Le (finiteDiagonal (fun i => 1 / (1 + s i))) 1 := by
  exact
    opNorm2Le_finiteDiagonal_of_abs_le_one
      (fun i => 1 / (1 + s i))
      (fun i => inv_one_add_abs_le_one_of_nonneg (hs i))

/-- Diagonal identity behind the polar bridge:
`diag((1+s)^{-1}) * (I - diag(s^2)) = I - diag(s)`. -/
theorem matMul_finiteDiagonal_inv_one_add_id_sub_square {n : Nat}
    (s : Fin n -> Real) (hs : forall i, 0 <= s i) :
    matMul n (finiteDiagonal (fun i => 1 / (1 + s i)))
      (fun i j => idMatrix n i j - finiteDiagonal (fun i => s i ^ 2) i j) =
      fun i j => idMatrix n i j - finiteDiagonal s i j := by
  ext i j
  by_cases hij : i = j
  case pos =>
    subst j
    simp [matMul, finiteDiagonal, idMatrix]
    simpa [one_div] using inv_one_add_mul_one_sub_sq (hs i)
  case neg =>
    simp [matMul, finiteDiagonal, idMatrix, hij]

/-- Square matrix products preserve operator-2 certificates. -/
theorem opNorm2Le_matMul_square_of_bounds {n : Nat}
    (A B : Fin n -> Fin n -> Real) {cA cB : Real}
    (hcA : 0 <= cA) (hA : opNorm2Le A cA) (hB : opNorm2Le B cB) :
    opNorm2Le (matMul n A B) (cA * cB) := by
  exact opNorm2Le_of_rectOpNorm2Le_square _
    (rectOpNorm2Le_matMul_square A B hcA hA hB)

/-- The spectral square of the full-positive polar `H` is obtained by
squaring its singular-value diagonal. -/
theorem rectRightGramPolarH_sq_eq_spectral_square {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    matMul n (rectRightGramPolarH A) (rectRightGramPolarH A) =
      matMul n (rectRightGramEigenbasis A)
        (matMul n (finiteDiagonal
            (fun i => rectRightGramBasisSingularValue A i ^ 2))
          (finiteTranspose (rectRightGramEigenbasis A))) := by
  let V := rectRightGramEigenbasis A
  let Vt := finiteTranspose V
  let D := finiteDiagonal (rectRightGramBasisSingularValue A)
  have hVtV : matMul n Vt V = idMatrix n := by
    ext i j
    have hcol := rectRightGramEigenbasis_col_orthonormal A i j
    simpa [Vt, V, matMul, finiteTranspose, idMatrix] using hcol
  calc
    matMul n (rectRightGramPolarH A) (rectRightGramPolarH A)
        = matMul n (matMul n V (matMul n D Vt))
            (matMul n V (matMul n D Vt)) := by
        rfl
    _ = matMul n V (matMul n (matMul n D Vt)
          (matMul n V (matMul n D Vt))) := by
        rw [matMul_assoc]
    _ = matMul n V (matMul n D
          (matMul n Vt (matMul n V (matMul n D Vt)))) := by
        congr 1
        rw [matMul_assoc]
    _ = matMul n V (matMul n D
          (matMul n (matMul n Vt V) (matMul n D Vt))) := by
        congr 2
        rw [<- matMul_assoc]
    _ = matMul n V (matMul n D
          (matMul n (idMatrix n) (matMul n D Vt))) := by
        rw [hVtV]
    _ = matMul n V (matMul n D (matMul n D Vt)) := by
        rw [matMul_id_left]
    _ = matMul n V (matMul n (matMul n D D) Vt) := by
        congr 1
        rw [<- matMul_assoc]
    _ =
      matMul n V
        (matMul n (finiteDiagonal
            (fun i => rectRightGramBasisSingularValue A i ^ 2)) Vt) := by
        rw [matMul_finiteDiagonal_self]

/-- Spectral `(I + H)^{-1}` for the right-Gram polar positive factor. -/
noncomputable def rectRightGramPolarResolvent {m n : Nat}
    (A : Fin m -> Fin n -> Real) : Fin n -> Fin n -> Real :=
  matMul n (rectRightGramEigenbasis A)
    (matMul n
      (finiteDiagonal
        (fun i => 1 / (1 + rectRightGramBasisSingularValue A i)))
      (finiteTranspose (rectRightGramEigenbasis A)))

/-- The spectral `(I + H)^{-1}` factor is an operator-2 contraction. -/
theorem rectRightGramPolarResolvent_opNorm2Le_one {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    opNorm2Le (rectRightGramPolarResolvent A) 1 := by
  let V := rectRightGramEigenbasis A
  let Vt := finiteTranspose V
  let Dinv :=
    finiteDiagonal
      (fun i => 1 / (1 + rectRightGramBasisSingularValue A i))
  have hVorth : IsOrthogonal n V :=
    rectRightGramEigenbasis_isOrthogonal A
  have hD : opNorm2Le Dinv 1 := by
    exact
      opNorm2Le_finiteDiagonal_inv_one_add_of_nonneg
        (rectRightGramBasisSingularValue A)
        (fun i => rectRightGramBasisSingularValue_nonneg A i)
  have hVt : opNorm2Le Vt 1 := by
    simpa [Vt, V, finiteTranspose, matTranspose] using
      hVorth.transpose_opNorm2Le_one
  have hDinvVt : opNorm2Le (matMul n Dinv Vt) 1 := by
    have hprod :
        opNorm2Le (matMul n Dinv Vt) (1 * 1) :=
      opNorm2Le_matMul_square_of_bounds Dinv Vt (by norm_num) hD hVt
    simpa using hprod
  have hV : opNorm2Le V 1 := hVorth.opNorm2Le_one
  have hprod :
      opNorm2Le (matMul n V (matMul n Dinv Vt)) (1 * 1) :=
    opNorm2Le_matMul_square_of_bounds V (matMul n Dinv Vt)
      (by norm_num) hV hDinvVt
  simpa [rectRightGramPolarResolvent, V, Vt, Dinv] using hprod

/-- The resolvent factor converts the polar top-Gram identity
`P11^T P11 = I - H^2` into the bridge matrix equation `T*P11 = I-H`. -/
theorem rectRightGramPolarResolvent_mul_id_sub_polarH_sq {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    matMul n (rectRightGramPolarResolvent A)
      (fun i j =>
        idMatrix n i j -
          matMul n (rectRightGramPolarH A) (rectRightGramPolarH A) i j) =
      fun i j => idMatrix n i j - rectRightGramPolarH A i j := by
  let V := rectRightGramEigenbasis A
  let Vt := finiteTranspose V
  let s := rectRightGramBasisSingularValue A
  let D := finiteDiagonal s
  let Dinv := finiteDiagonal (fun i => 1 / (1 + s i))
  let D2 := finiteDiagonal (fun i => s i ^ 2)
  have hVorth : IsOrthogonal n V :=
    rectRightGramEigenbasis_isOrthogonal A
  have hVtV : matMul n Vt V = idMatrix n := by
    ext i j
    have hcol := hVorth.col_orthonormal i j
    simpa [Vt, V, matMul, finiteTranspose, idMatrix] using hcol
  have hVVt : matMul n V Vt = idMatrix n := by
    ext i j
    have hrow := hVorth.row_orthonormal i j
    simpa [Vt, V, matMul, finiteTranspose, idMatrix] using hrow
  have hHsq :
      matMul n (rectRightGramPolarH A) (rectRightGramPolarH A) =
        matMul n V (matMul n D2 Vt) := by
    simpa [V, Vt, s, D2] using
      rectRightGramPolarH_sq_eq_spectral_square A
  have hHsq_expanded :
      matMul n (matMul n V (matMul n D Vt))
          (matMul n V (matMul n D Vt)) =
        matMul n V (matMul n D2 Vt) := by
    simpa [V, Vt, s, D, D2, rectRightGramPolarH] using hHsq
  have hdiag :
      matMul n Dinv (fun i j => idMatrix n i j - D2 i j) =
        fun i j => idMatrix n i j - D i j := by
    simpa [Dinv, D, D2, s] using
      matMul_finiteDiagonal_inv_one_add_id_sub_square s
        (fun i => rectRightGramBasisSingularValue_nonneg A i)
  calc
    matMul n (rectRightGramPolarResolvent A)
        (fun i j =>
          idMatrix n i j -
            matMul n (rectRightGramPolarH A) (rectRightGramPolarH A) i j)
        =
      matMul n (matMul n V (matMul n Dinv Vt))
        (fun i j =>
          idMatrix n i j -
            matMul n (matMul n V (matMul n D Vt))
              (matMul n V (matMul n D Vt)) i j) := by
        rfl
    _ =
      matMul n (matMul n V (matMul n Dinv Vt))
        (fun i j => idMatrix n i j - matMul n V (matMul n D2 Vt) i j) := by
        rw [hHsq_expanded]
    _ =
      matMul n (matMul n V (matMul n Dinv Vt))
        (fun i j => matMul n V Vt i j - matMul n V (matMul n D2 Vt) i j) := by
        rw [hVVt]
    _ =
      matMul n (matMul n V (matMul n Dinv Vt))
        (matMul n V (fun i j => Vt i j - matMul n D2 Vt i j)) := by
        congr 1
        symm
        rw [matMul_sub_right_square]
    _ =
      matMul n (matMul n V (matMul n Dinv Vt))
        (matMul n V (matMul n (fun i j => idMatrix n i j - D2 i j) Vt)) := by
        congr 1
        congr 1
        rw [matMul_sub_left]
        rw [matMul_id_left]
    _ =
      matMul n V (matMul n Dinv
        (matMul n Vt
          (matMul n V
            (matMul n (fun i j => idMatrix n i j - D2 i j) Vt)))) := by
        rw [matMul_assoc]
        congr 1
        rw [matMul_assoc]
    _ =
      matMul n V (matMul n Dinv
        (matMul n (matMul n Vt V)
          (matMul n (fun i j => idMatrix n i j - D2 i j) Vt))) := by
        congr 2
        rw [<- matMul_assoc]
    _ =
      matMul n V (matMul n Dinv
        (matMul n (idMatrix n)
          (matMul n (fun i j => idMatrix n i j - D2 i j) Vt))) := by
        rw [hVtV]
    _ =
      matMul n V (matMul n Dinv
        (matMul n (fun i j => idMatrix n i j - D2 i j) Vt)) := by
        rw [matMul_id_left]
    _ =
      matMul n V
        (matMul n (matMul n Dinv
          (fun i j => idMatrix n i j - D2 i j)) Vt) := by
        congr 1
        rw [<- matMul_assoc]
    _ = matMul n V (matMul n (fun i j => idMatrix n i j - D i j) Vt) := by
        rw [hdiag]
    _ = matMul n V (fun i j => Vt i j - matMul n D Vt i j) := by
        rw [matMul_sub_left]
        rw [matMul_id_left]
    _ = fun i j => matMul n V Vt i j - matMul n V (matMul n D Vt) i j := by
        rw [matMul_sub_right_square]
    _ = fun i j => idMatrix n i j - matMul n V (matMul n D Vt) i j := by
        rw [hVVt]
    _ = fun i j => idMatrix n i j - rectRightGramPolarH A i j := by
        rfl

/-- The concrete bridge matrix for the full-positive polar branch:
`T = (I+H)^{-1} * P11^T`. -/
noncomputable def mgsProblem1912_fullPositivePolarBridgeT
    {m n : Nat}
    (P11 : Fin n -> Fin n -> Real) (P21 : Fin m -> Fin n -> Real) :
    Fin n -> Fin n -> Real :=
  matMul n (rectRightGramPolarResolvent P21) (finiteTranspose P11)

/-- In the full-positive right-Gram polar branch, the concrete bridge matrix
satisfies `T*P11 = I-H`. -/
theorem mgsProblem1912_fullPositivePolarBridgeT_mul_p11
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : MGSProblem1912CSPolarInput m n P11 P21)
    (hpos : forall a : Fin n, 0 < rectRightGramBasisSingularValue P21 a) :
    matMul n (mgsProblem1912_fullPositivePolarBridgeT P11 P21) P11 =
      fun i j => idMatrix n i j - rectRightGramPolarH P21 i j := by
  have hgram :
      matMul n (finiteTranspose P11) P11 = rectangularGram P11 := by
    ext i j
    rfl
  have hp11 :
      rectangularGram P11 =
        fun i j =>
          idMatrix n i j -
            matMul n (rectRightGramPolarH P21)
              (rectRightGramPolarH P21) i j :=
    hinput.p11_gram_eq_id_sub_polarH_sq hpos
  calc
    matMul n (mgsProblem1912_fullPositivePolarBridgeT P11 P21) P11
        =
      matMul n (rectRightGramPolarResolvent P21)
        (matMul n (finiteTranspose P11) P11) := by
        rw [mgsProblem1912_fullPositivePolarBridgeT, matMul_assoc]
    _ = matMul n (rectRightGramPolarResolvent P21) (rectangularGram P11) := by
        rw [hgram]
    _ =
      matMul n (rectRightGramPolarResolvent P21)
        (fun i j =>
          idMatrix n i j -
            matMul n (rectRightGramPolarH P21)
              (rectRightGramPolarH P21) i j) := by
        rw [hp11]
    _ = fun i j => idMatrix n i j - rectRightGramPolarH P21 i j := by
        exact rectRightGramPolarResolvent_mul_id_sub_polarH_sq P21

/-- In the full-positive right-Gram polar branch, the concrete bridge matrix is
a contraction. -/
theorem mgsProblem1912_fullPositivePolarBridgeT_opNorm2Le_one
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : MGSProblem1912CSPolarInput m n P11 P21) :
    opNorm2Le (mgsProblem1912_fullPositivePolarBridgeT P11 P21) 1 := by
  have hres : opNorm2Le (rectRightGramPolarResolvent P21) 1 :=
    rectRightGramPolarResolvent_opNorm2Le_one P21
  have hP11 : opNorm2Le P11 1 := hinput.p11_opNorm2Le_one
  have hP11rect : rectOpNorm2Le P11 1 :=
    rectOpNorm2Le_of_opNorm2Le_square P11 hP11
  have hP11t_rect : rectOpNorm2Le (finiteTranspose P11) 1 :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le P11 (by norm_num)
      hP11rect
  have hP11t : opNorm2Le (finiteTranspose P11) 1 :=
    opNorm2Le_of_rectOpNorm2Le_square _ hP11t_rect
  have hprod :
      opNorm2Le
        (matMul n (rectRightGramPolarResolvent P21) (finiteTranspose P11))
        (1 * 1) :=
    opNorm2Le_matMul_square_of_bounds
      (rectRightGramPolarResolvent P21) (finiteTranspose P11)
      (by norm_num) hres hP11t
  simpa [mgsProblem1912_fullPositivePolarBridgeT] using hprod

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

/-- Full-positive right-Gram polar factors produce the complete polar payload
from the corrected CS/polar input.  This closes the former explicit bridge
obligations in this branch by taking `T = (I+H)^{-1} * P11^T`. -/
def mgsProblem1912_polarFactorData_of_csPolarInput_fullPositive_rightGram
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : MGSProblem1912CSPolarInput m n P11 P21)
    (hpos : forall a : Fin n, 0 < rectRightGramBasisSingularValue P21 a) :
    MGSProblem1912PolarFactorData m n P11 P21 :=
  mgsProblem1912_polarFactorData_of_fullPositive_rightGram hpos
    (mgsProblem1912_fullPositivePolarBridgeT_mul_p11 hinput hpos)
    (mgsProblem1912_fullPositivePolarBridgeT_opNorm2Le_one hinput)

/-- Full-positive right-Gram polar factors plus the corrected CS/polar input
produce pure Problem 19.12 correction-map data. -/
theorem mgsProblem1912_correctionMapData_exists_of_csPolarInput_fullPositive_rightGram
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : MGSProblem1912CSPolarInput m n P11 P21)
    (hpos : forall a : Fin n, 0 < rectRightGramBasisSingularValue P21 a) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      MGSProblem1912CorrectionMapData m n P11 P21 Q F := by
  exact
    mgsProblem1912_correctionMapData_exists_of_polarFactorData
      (mgsProblem1912_polarFactorData_of_csPolarInput_fullPositive_rightGram
        hinput hpos)

/-- Full-positive right-Gram polar factors plus the corrected CS/polar input
produce additive Problem 19.12 witnesses. -/
theorem mgsProblem1912_add_factor_exists_of_csPolarInput_fullPositive_rightGram
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : MGSProblem1912CSPolarInput m n P11 P21)
    (hpos : forall a : Fin n, 0 < rectRightGramBasisSingularValue P21 a) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      (Q = fun i j => P21 i j + matMulRect m n n F P11 i j) /\
        GramSchmidtOrthonormalColumns Q /\
        rectOpNorm2Le F 1 := by
  exact
    mgsProblem1912_add_factor_exists_of_polarFactorData
      (mgsProblem1912_polarFactorData_of_csPolarInput_fullPositive_rightGram
        hinput hpos)

/-- The two currently closed CS/polar branches for Problem 19.12: either the
top Gram vanishes, giving the zero-correction branch, or the lower right-Gram
singular values are all positive, giving the full-positive polar branch. -/
theorem mgsProblem1912_correctionMapData_exists_of_csPolarInput_zero_or_fullPositive_rightGram
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : MGSProblem1912CSPolarInput m n P11 P21)
    (hcase :
      rectangularGram P11 = (fun _ _ => 0) \/
        forall a : Fin n, 0 < rectRightGramBasisSingularValue P21 a) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      MGSProblem1912CorrectionMapData m n P11 P21 Q F := by
  cases hcase with
  | inl htop =>
      exact
        mgsProblem1912_correctionMapData_exists_of_csPolarInput_top_gram_zero
          hinput htop
  | inr hpos =>
      exact
        mgsProblem1912_correctionMapData_exists_of_csPolarInput_fullPositive_rightGram
          hinput hpos

/-- Additive-witness form of the closed zero/full-positive CS/polar branch
router for Problem 19.12.  The remaining general proof obligation is precisely
the rank-deficient mixed-singular-value branch not covered by this disjunction. -/
theorem mgsProblem1912_add_factor_exists_of_csPolarInput_zero_or_fullPositive_rightGram
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : MGSProblem1912CSPolarInput m n P11 P21)
    (hcase :
      rectangularGram P11 = (fun _ _ => 0) \/
        forall a : Fin n, 0 < rectRightGramBasisSingularValue P21 a) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      (Q = fun i j => P21 i j + matMulRect m n n F P11 i j) /\
        GramSchmidtOrthonormalColumns Q /\
        rectOpNorm2Le F 1 := by
  cases hcase with
  | inl htop =>
      exact
        mgsProblem1912_add_factor_exists_of_csPolarInput_top_gram_zero
          hinput htop
  | inr hpos =>
      exact
        mgsProblem1912_add_factor_exists_of_csPolarInput_fullPositive_rightGram
          hinput hpos

end

end LeanFpAnalysis.FP
