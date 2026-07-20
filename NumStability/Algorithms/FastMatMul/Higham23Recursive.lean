/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QED
-/
import NumStability.Algorithms.FastMatMul.Higham23

namespace NumStability

open scoped Topology
open Filter

/-!
# Literal recursive Strassen evaluators

This file supplies the recursively rounded source objects missing from the
initial Chapter 23 audit.  A value of `Higham23RecursiveMatrix r depth` is a
`2^depth` by `2^depth` block matrix whose leaves are `2^r` square real
matrices.  Thus its scalar order is `2^(r+depth)` and `depth = 0` is exactly
the conventional-multiplication threshold.
-/

instance {R : Type*} [Zero R] : Zero (Higham23Block2 (R := R)) :=
  ⟨⟨0, 0, 0, 0⟩⟩

instance {R : Type*} [Add R] : Add (Higham23Block2 (R := R)) :=
  ⟨fun A B ↦ ⟨A.c11 + B.c11, A.c12 + B.c12,
    A.c21 + B.c21, A.c22 + B.c22⟩⟩

instance {R : Type*} [Neg R] : Neg (Higham23Block2 (R := R)) :=
  ⟨fun A ↦ ⟨-A.c11, -A.c12, -A.c21, -A.c22⟩⟩

instance {R : Type*} [Sub R] : Sub (Higham23Block2 (R := R)) :=
  ⟨fun A B ↦ ⟨A.c11 - B.c11, A.c12 - B.c12,
    A.c21 - B.c21, A.c22 - B.c22⟩⟩

instance {S R : Type*} [SMul S R] : SMul S (Higham23Block2 (R := R)) :=
  ⟨fun s A ↦ ⟨s • A.c11, s • A.c12, s • A.c21, s • A.c22⟩⟩

@[simp] theorem higham23Block2_zero_c11 {R : Type*} [Zero R] :
    (0 : Higham23Block2 (R := R)).c11 = 0 := rfl
@[simp] theorem higham23Block2_zero_c12 {R : Type*} [Zero R] :
    (0 : Higham23Block2 (R := R)).c12 = 0 := rfl
@[simp] theorem higham23Block2_zero_c21 {R : Type*} [Zero R] :
    (0 : Higham23Block2 (R := R)).c21 = 0 := rfl
@[simp] theorem higham23Block2_zero_c22 {R : Type*} [Zero R] :
    (0 : Higham23Block2 (R := R)).c22 = 0 := rfl

@[simp] theorem higham23Block2_add_c11 {R : Type*} [Add R]
    (A B : Higham23Block2 (R := R)) : (A + B).c11 = A.c11 + B.c11 := rfl
@[simp] theorem higham23Block2_add_c12 {R : Type*} [Add R]
    (A B : Higham23Block2 (R := R)) : (A + B).c12 = A.c12 + B.c12 := rfl
@[simp] theorem higham23Block2_add_c21 {R : Type*} [Add R]
    (A B : Higham23Block2 (R := R)) : (A + B).c21 = A.c21 + B.c21 := rfl
@[simp] theorem higham23Block2_add_c22 {R : Type*} [Add R]
    (A B : Higham23Block2 (R := R)) : (A + B).c22 = A.c22 + B.c22 := rfl

private def higham23Block2EquivProd {R : Type*} :
    Higham23Block2 (R := R) ≃ R × R × R × R where
  toFun A := (A.c11, A.c12, A.c21, A.c22)
  invFun q := ⟨q.1, q.2.1, q.2.2.1, q.2.2.2⟩
  left_inv A := by cases A; rfl
  right_inv q := by rcases q with ⟨a, b, c, d⟩; rfl

instance {R : Type*} [AddCommGroup R] :
    AddCommGroup (Higham23Block2 (R := R)) := by
  apply higham23Block2EquivProd.injective.addCommGroup <;> intros <;> rfl

/-- Block multiplication equips `Higham23Block2 R` with the same distributive
nonassociative ring structure as its block entries. -/
instance higham23Block2NonUnitalNonAssocRing
    {R : Type*} [NonUnitalNonAssocRing R] :
    NonUnitalNonAssocRing (Higham23Block2 (R := R)) where
  mul := higham23BlockMul
  left_distrib := by
    intro A B C
    change higham23BlockMul A (B + C) =
      higham23BlockMul A B + higham23BlockMul A C
    cases A
    cases B
    cases C
    ext <;> dsimp [higham23BlockMul] <;> noncomm_ring
  right_distrib := by
    intro A B C
    change higham23BlockMul (A + B) C =
      higham23BlockMul A C + higham23BlockMul B C
    cases A
    cases B
    cases C
    ext <;> dsimp [higham23BlockMul] <;> noncomm_ring
  zero_mul := by
    intro A
    change higham23BlockMul 0 A = 0
    cases A
    ext <;> dsimp [higham23BlockMul] <;> simp
  mul_zero := by
    intro A
    change higham23BlockMul A 0 = 0
    cases A
    ext <;> dsimp [higham23BlockMul] <;> simp

@[simp] theorem higham23Block2_mul_c11 {R : Type*}
    [NonUnitalNonAssocRing R] (A B : Higham23Block2 (R := R)) :
    (A * B).c11 = A.c11 * B.c11 + A.c12 * B.c21 := rfl
@[simp] theorem higham23Block2_mul_c12 {R : Type*}
    [NonUnitalNonAssocRing R] (A B : Higham23Block2 (R := R)) :
    (A * B).c12 = A.c11 * B.c12 + A.c12 * B.c22 := rfl
@[simp] theorem higham23Block2_mul_c21 {R : Type*}
    [NonUnitalNonAssocRing R] (A B : Higham23Block2 (R := R)) :
    (A * B).c21 = A.c21 * B.c11 + A.c22 * B.c21 := rfl
@[simp] theorem higham23Block2_mul_c22 {R : Type*}
    [NonUnitalNonAssocRing R] (A B : Higham23Block2 (R := R)) :
    (A * B).c22 = A.c21 * B.c12 + A.c22 * B.c22 := rfl

@[simp] theorem higham23Block2_sub_c11 {R : Type*} [Sub R]
    (A B : Higham23Block2 (R := R)) : (A - B).c11 = A.c11 - B.c11 := rfl
@[simp] theorem higham23Block2_sub_c12 {R : Type*} [Sub R]
    (A B : Higham23Block2 (R := R)) : (A - B).c12 = A.c12 - B.c12 := rfl
@[simp] theorem higham23Block2_sub_c21 {R : Type*} [Sub R]
    (A B : Higham23Block2 (R := R)) : (A - B).c21 = A.c21 - B.c21 := rfl
@[simp] theorem higham23Block2_sub_c22 {R : Type*} [Sub R]
    (A B : Higham23Block2 (R := R)) : (A - B).c22 = A.c22 - B.c22 := rfl

/-- Recursive block presentation of a matrix of order `2^(r+depth)`. -/
def Higham23RecursiveMatrix (r : ℕ) : ℕ → Type
  | 0 => Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ
  | depth + 1 => Higham23Block2 (R := Higham23RecursiveMatrix r depth)

instance (r depth : ℕ) : NonUnitalNonAssocRing
    (Higham23RecursiveMatrix r depth) := by
  induction depth with
  | zero =>
      dsimp [Higham23RecursiveMatrix]
      infer_instance
  | succ depth ih =>
      dsimp [Higham23RecursiveMatrix]
      infer_instance

/-- Entrywise rounded addition at every scalar leaf. -/
noncomputable def higham23RecursiveFlAdd (fp : FPModel) (r : ℕ) :
    (depth : ℕ) → Higham23RecursiveMatrix r depth →
      Higham23RecursiveMatrix r depth → Higham23RecursiveMatrix r depth
  | 0, A, B => fun i j ↦ fp.fl_add (A i j) (B i j)
  | depth + 1, A, B =>
      { c11 := higham23RecursiveFlAdd fp r depth A.c11 B.c11
        c12 := higham23RecursiveFlAdd fp r depth A.c12 B.c12
        c21 := higham23RecursiveFlAdd fp r depth A.c21 B.c21
        c22 := higham23RecursiveFlAdd fp r depth A.c22 B.c22 }

/-- Entrywise rounded subtraction at every scalar leaf. -/
noncomputable def higham23RecursiveFlSub (fp : FPModel) (r : ℕ) :
    (depth : ℕ) → Higham23RecursiveMatrix r depth →
      Higham23RecursiveMatrix r depth → Higham23RecursiveMatrix r depth
  | 0, A, B => fun i j ↦ fp.fl_sub (A i j) (B i j)
  | depth + 1, A, B =>
      { c11 := higham23RecursiveFlSub fp r depth A.c11 B.c11
        c12 := higham23RecursiveFlSub fp r depth A.c12 B.c12
        c21 := higham23RecursiveFlSub fp r depth A.c21 B.c21
        c22 := higham23RecursiveFlSub fp r depth A.c22 B.c22 }

/-- Max-entry norm inequality on the recursive block presentation. -/
def Higham23RecursiveMaxNormLe (r : ℕ) :
    (depth : ℕ) → Higham23RecursiveMatrix r depth → ℝ → Prop
  | 0, A, bound => ∀ i j, |A i j| ≤ bound
  | depth + 1, A, bound =>
      Higham23RecursiveMaxNormLe r depth A.c11 bound ∧
      Higham23RecursiveMaxNormLe r depth A.c12 bound ∧
      Higham23RecursiveMaxNormLe r depth A.c21 bound ∧
      Higham23RecursiveMaxNormLe r depth A.c22 bound

/-- Entrywise error inequality on the recursive block presentation. -/
def Higham23RecursiveErrorLe (r : ℕ) :
    (depth : ℕ) → Higham23RecursiveMatrix r depth →
      Higham23RecursiveMatrix r depth → ℝ → Prop
  | 0, A, B, bound => ∀ i j, |A i j - B i j| ≤ bound
  | depth + 1, A, B, bound =>
      Higham23RecursiveErrorLe r depth A.c11 B.c11 bound ∧
      Higham23RecursiveErrorLe r depth A.c12 B.c12 bound ∧
      Higham23RecursiveErrorLe r depth A.c21 B.c21 bound ∧
      Higham23RecursiveErrorLe r depth A.c22 B.c22 bound

theorem higham23_recursiveMaxNormLe_mono (r : ℕ) :
    ∀ depth (A : Higham23RecursiveMatrix r depth) {a b : ℝ},
      Higham23RecursiveMaxNormLe r depth A a → a ≤ b →
        Higham23RecursiveMaxNormLe r depth A b
  | 0, A, a, b, hA, hab => by
      intro i j
      exact (hA i j).trans hab
  | depth + 1, A, a, b, hA, hab => by
      rcases hA with ⟨h11, h12, h21, h22⟩
      exact ⟨higham23_recursiveMaxNormLe_mono r depth A.c11 h11 hab,
        higham23_recursiveMaxNormLe_mono r depth A.c12 h12 hab,
        higham23_recursiveMaxNormLe_mono r depth A.c21 h21 hab,
        higham23_recursiveMaxNormLe_mono r depth A.c22 h22 hab⟩

theorem higham23_recursiveErrorLe_mono (r : ℕ) :
    ∀ depth (A B : Higham23RecursiveMatrix r depth) {a b : ℝ},
      Higham23RecursiveErrorLe r depth A B a → a ≤ b →
        Higham23RecursiveErrorLe r depth A B b
  | 0, A, B, a, b, h, hab => by
      intro i j
      exact (h i j).trans hab
  | depth + 1, A, B, a, b, h, hab => by
      rcases h with ⟨h11, h12, h21, h22⟩
      exact ⟨higham23_recursiveErrorLe_mono r depth A.c11 B.c11 h11 hab,
        higham23_recursiveErrorLe_mono r depth A.c12 B.c12 h12 hab,
        higham23_recursiveErrorLe_mono r depth A.c21 B.c21 h21 hab,
        higham23_recursiveErrorLe_mono r depth A.c22 B.c22 h22 hab⟩

theorem higham23_recursiveMaxNormLe_add (r : ℕ) :
    ∀ depth (A B : Higham23RecursiveMatrix r depth) {a b : ℝ},
      Higham23RecursiveMaxNormLe r depth A a →
      Higham23RecursiveMaxNormLe r depth B b →
      Higham23RecursiveMaxNormLe r depth (A + B) (a + b)
  | 0, A, B, a, b, hA, hB => by
      intro i j
      exact (abs_add_le (A i j) (B i j)).trans
        (add_le_add (hA i j) (hB i j))
  | depth + 1, A, B, a, b, hA, hB => by
      rcases hA with ⟨hA11, hA12, hA21, hA22⟩
      rcases hB with ⟨hB11, hB12, hB21, hB22⟩
      simpa only [higham23Block2_add_c11, higham23Block2_add_c12,
        higham23Block2_add_c21, higham23Block2_add_c22] using
        (show Higham23RecursiveMaxNormLe r depth (A.c11 + B.c11) (a + b) ∧
            Higham23RecursiveMaxNormLe r depth (A.c12 + B.c12) (a + b) ∧
            Higham23RecursiveMaxNormLe r depth (A.c21 + B.c21) (a + b) ∧
            Higham23RecursiveMaxNormLe r depth (A.c22 + B.c22) (a + b) from
          ⟨higham23_recursiveMaxNormLe_add r depth _ _ hA11 hB11,
        higham23_recursiveMaxNormLe_add r depth _ _ hA12 hB12,
        higham23_recursiveMaxNormLe_add r depth _ _ hA21 hB21,
        higham23_recursiveMaxNormLe_add r depth _ _ hA22 hB22⟩)

theorem higham23_recursiveMaxNormLe_sub (r : ℕ) :
    ∀ depth (A B : Higham23RecursiveMatrix r depth) {a b : ℝ},
      Higham23RecursiveMaxNormLe r depth A a →
      Higham23RecursiveMaxNormLe r depth B b →
      Higham23RecursiveMaxNormLe r depth (A - B) (a + b)
  | 0, A, B, a, b, hA, hB => by
      intro i j
      exact (abs_sub (A i j) (B i j)).trans
        (add_le_add (hA i j) (hB i j))
  | depth + 1, A, B, a, b, hA, hB => by
      rcases hA with ⟨hA11, hA12, hA21, hA22⟩
      rcases hB with ⟨hB11, hB12, hB21, hB22⟩
      simpa only [higham23Block2_sub_c11, higham23Block2_sub_c12,
        higham23Block2_sub_c21, higham23Block2_sub_c22] using
        (show Higham23RecursiveMaxNormLe r depth (A.c11 - B.c11) (a + b) ∧
            Higham23RecursiveMaxNormLe r depth (A.c12 - B.c12) (a + b) ∧
            Higham23RecursiveMaxNormLe r depth (A.c21 - B.c21) (a + b) ∧
            Higham23RecursiveMaxNormLe r depth (A.c22 - B.c22) (a + b) from
          ⟨higham23_recursiveMaxNormLe_sub r depth _ _ hA11 hB11,
        higham23_recursiveMaxNormLe_sub r depth _ _ hA12 hB12,
        higham23_recursiveMaxNormLe_sub r depth _ _ hA21 hB21,
        higham23_recursiveMaxNormLe_sub r depth _ _ hA22 hB22⟩)

theorem higham23_recursiveErrorLe_refl (r : ℕ) :
    ∀ depth (A : Higham23RecursiveMatrix r depth),
      Higham23RecursiveErrorLe r depth A A 0
  | 0, A => by simp [Higham23RecursiveErrorLe]
  | depth + 1, A => ⟨higham23_recursiveErrorLe_refl r depth A.c11,
      higham23_recursiveErrorLe_refl r depth A.c12,
      higham23_recursiveErrorLe_refl r depth A.c21,
      higham23_recursiveErrorLe_refl r depth A.c22⟩

theorem higham23_recursiveErrorLe_symm (r : ℕ) :
    ∀ depth (A B : Higham23RecursiveMatrix r depth) {e : ℝ},
      Higham23RecursiveErrorLe r depth A B e →
      Higham23RecursiveErrorLe r depth B A e
  | 0, A, B, e, h => by
      intro i j
      simpa [abs_sub_comm] using h i j
  | depth + 1, A, B, e, h => by
      rcases h with ⟨h11, h12, h21, h22⟩
      exact ⟨higham23_recursiveErrorLe_symm r depth _ _ h11,
        higham23_recursiveErrorLe_symm r depth _ _ h12,
        higham23_recursiveErrorLe_symm r depth _ _ h21,
        higham23_recursiveErrorLe_symm r depth _ _ h22⟩

theorem higham23_recursiveErrorLe_trans (r : ℕ) :
    ∀ depth (A B C : Higham23RecursiveMatrix r depth) {e f : ℝ},
      Higham23RecursiveErrorLe r depth A B e →
      Higham23RecursiveErrorLe r depth B C f →
      Higham23RecursiveErrorLe r depth A C (e + f)
  | 0, A, B, C, e, f, hAB, hBC => by
      intro i j
      calc
        |A i j - C i j| ≤ |A i j - B i j| + |B i j - C i j| := by
          have := abs_add_le (A i j - B i j) (B i j - C i j)
          convert this using 1 <;> ring
        _ ≤ e + f := add_le_add (hAB i j) (hBC i j)
  | depth + 1, A, B, C, e, f, hAB, hBC => by
      rcases hAB with ⟨hAB11, hAB12, hAB21, hAB22⟩
      rcases hBC with ⟨hBC11, hBC12, hBC21, hBC22⟩
      exact ⟨higham23_recursiveErrorLe_trans r depth _ _ _ hAB11 hBC11,
        higham23_recursiveErrorLe_trans r depth _ _ _ hAB12 hBC12,
        higham23_recursiveErrorLe_trans r depth _ _ _ hAB21 hBC21,
        higham23_recursiveErrorLe_trans r depth _ _ _ hAB22 hBC22⟩

theorem higham23_recursiveErrorLe_add (r : ℕ) :
    ∀ depth (A A' B B' : Higham23RecursiveMatrix r depth) {e f : ℝ},
      Higham23RecursiveErrorLe r depth A A' e →
      Higham23RecursiveErrorLe r depth B B' f →
      Higham23RecursiveErrorLe r depth (A + B) (A' + B') (e + f)
  | 0, A, A', B, B', e, f, hA, hB => by
      intro i j
      calc
        |(A + B) i j - (A' + B') i j| ≤
            |A i j - A' i j| + |B i j - B' i j| := by
          have := abs_add_le (A i j - A' i j) (B i j - B' i j)
          change |(A i j + B i j) - (A' i j + B' i j)| ≤ _
          convert this using 1 <;> ring
        _ ≤ e + f := add_le_add (hA i j) (hB i j)
  | depth + 1, A, A', B, B', e, f, hA, hB => by
      rcases hA with ⟨hA11, hA12, hA21, hA22⟩
      rcases hB with ⟨hB11, hB12, hB21, hB22⟩
      simpa only [higham23Block2_add_c11, higham23Block2_add_c12,
        higham23Block2_add_c21, higham23Block2_add_c22] using
        (show Higham23RecursiveErrorLe r depth (A.c11 + B.c11)
              (A'.c11 + B'.c11) (e + f) ∧
            Higham23RecursiveErrorLe r depth (A.c12 + B.c12)
              (A'.c12 + B'.c12) (e + f) ∧
            Higham23RecursiveErrorLe r depth (A.c21 + B.c21)
              (A'.c21 + B'.c21) (e + f) ∧
            Higham23RecursiveErrorLe r depth (A.c22 + B.c22)
              (A'.c22 + B'.c22) (e + f) from
          ⟨higham23_recursiveErrorLe_add r depth _ _ _ _ hA11 hB11,
        higham23_recursiveErrorLe_add r depth _ _ _ _ hA12 hB12,
        higham23_recursiveErrorLe_add r depth _ _ _ _ hA21 hB21,
        higham23_recursiveErrorLe_add r depth _ _ _ _ hA22 hB22⟩)

theorem higham23_recursiveErrorLe_sub (r : ℕ) :
    ∀ depth (A A' B B' : Higham23RecursiveMatrix r depth) {e f : ℝ},
      Higham23RecursiveErrorLe r depth A A' e →
      Higham23RecursiveErrorLe r depth B B' f →
      Higham23RecursiveErrorLe r depth (A - B) (A' - B') (e + f)
  | 0, A, A', B, B', e, f, hA, hB => by
      intro i j
      calc
        |(A - B) i j - (A' - B') i j| ≤
            |A i j - A' i j| + |B i j - B' i j| := by
          have := abs_sub (A i j - A' i j) (B i j - B' i j)
          change |(A i j - B i j) - (A' i j - B' i j)| ≤ _
          convert this using 1 <;> ring
        _ ≤ e + f := add_le_add (hA i j) (hB i j)
  | depth + 1, A, A', B, B', e, f, hA, hB => by
      rcases hA with ⟨hA11, hA12, hA21, hA22⟩
      rcases hB with ⟨hB11, hB12, hB21, hB22⟩
      simpa only [higham23Block2_sub_c11, higham23Block2_sub_c12,
        higham23Block2_sub_c21, higham23Block2_sub_c22] using
        (show Higham23RecursiveErrorLe r depth (A.c11 - B.c11)
              (A'.c11 - B'.c11) (e + f) ∧
            Higham23RecursiveErrorLe r depth (A.c12 - B.c12)
              (A'.c12 - B'.c12) (e + f) ∧
            Higham23RecursiveErrorLe r depth (A.c21 - B.c21)
              (A'.c21 - B'.c21) (e + f) ∧
            Higham23RecursiveErrorLe r depth (A.c22 - B.c22)
              (A'.c22 - B'.c22) (e + f) from
          ⟨higham23_recursiveErrorLe_sub r depth _ _ _ _ hA11 hB11,
        higham23_recursiveErrorLe_sub r depth _ _ _ _ hA12 hB12,
        higham23_recursiveErrorLe_sub r depth _ _ _ _ hA21 hB21,
        higham23_recursiveErrorLe_sub r depth _ _ _ _ hA22 hB22⟩)

/-- A norm bound and an error bound control the computed object. -/
theorem higham23_recursiveMaxNormLe_of_error (r : ℕ) :
    ∀ depth (A B : Higham23RecursiveMatrix r depth) {a e : ℝ},
      Higham23RecursiveMaxNormLe r depth A a →
      Higham23RecursiveErrorLe r depth A B e →
      Higham23RecursiveMaxNormLe r depth B (a + e)
  | 0, A, B, a, e, hA, hE => by
      intro i j
      calc
        |B i j| ≤ |A i j| + |A i j - B i j| := by
          have := abs_add_le (A i j) (B i j - A i j)
          rw [show A i j + (B i j - A i j) = B i j by ring] at this
          simpa [abs_sub_comm] using this
        _ ≤ a + e := add_le_add (hA i j) (hE i j)
  | depth + 1, A, B, a, e, hA, hE => by
      rcases hA with ⟨hA11, hA12, hA21, hA22⟩
      rcases hE with ⟨hE11, hE12, hE21, hE22⟩
      exact ⟨higham23_recursiveMaxNormLe_of_error r depth _ _ hA11 hE11,
        higham23_recursiveMaxNormLe_of_error r depth _ _ hA12 hE12,
        higham23_recursiveMaxNormLe_of_error r depth _ _ hA21 hE21,
        higham23_recursiveMaxNormLe_of_error r depth _ _ hA22 hE22⟩

/-- Exact matrix multiplication has the usual dimension factor in max-entry
norm, stated on the recursive block representation. -/
theorem higham23_recursiveMaxNormLe_mul (r : ℕ) :
    ∀ depth (A B : Higham23RecursiveMatrix r depth) (a b : ℝ),
      0 ≤ a → 0 ≤ b →
      Higham23RecursiveMaxNormLe r depth A a →
      Higham23RecursiveMaxNormLe r depth B b →
      Higham23RecursiveMaxNormLe r depth (A * B)
        ((2 ^ (r + depth) : ℕ) * a * b)
  | 0, A, B, a, b, ha, _hb, hA, hB => by
      intro i j
      change |∑ k : Fin (2 ^ r), A i k * B k j| ≤ _
      calc
        |∑ k : Fin (2 ^ r), A i k * B k j| ≤
            ∑ k : Fin (2 ^ r), |A i k * B k j| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin (2 ^ r), a * b := by
          apply Finset.sum_le_sum
          intro k _
          rw [abs_mul]
          exact mul_le_mul (hA i k) (hB k j) (abs_nonneg _) ha
        _ = ((2 ^ (r + 0) : ℕ) : ℝ) * a * b := by simp; ring
  | depth + 1, A, B, a, b, ha, hb, hA, hB => by
      rcases hA with ⟨hA11, hA12, hA21, hA22⟩
      rcases hB with ⟨hB11, hB12, hB21, hB22⟩
      let m : ℝ := (2 ^ (r + depth) : ℕ)
      have h11a := higham23_recursiveMaxNormLe_mul r depth
        A.c11 B.c11 a b ha hb hA11 hB11
      have h11b := higham23_recursiveMaxNormLe_mul r depth
        A.c12 B.c21 a b ha hb hA12 hB21
      have h12a := higham23_recursiveMaxNormLe_mul r depth
        A.c11 B.c12 a b ha hb hA11 hB12
      have h12b := higham23_recursiveMaxNormLe_mul r depth
        A.c12 B.c22 a b ha hb hA12 hB22
      have h21a := higham23_recursiveMaxNormLe_mul r depth
        A.c21 B.c11 a b ha hb hA21 hB11
      have h21b := higham23_recursiveMaxNormLe_mul r depth
        A.c22 B.c21 a b ha hb hA22 hB21
      have h22a := higham23_recursiveMaxNormLe_mul r depth
        A.c21 B.c12 a b ha hb hA21 hB12
      have h22b := higham23_recursiveMaxNormLe_mul r depth
        A.c22 B.c22 a b ha hb hA22 hB22
      have h11 := higham23_recursiveMaxNormLe_add r depth _ _ h11a h11b
      have h12 := higham23_recursiveMaxNormLe_add r depth _ _ h12a h12b
      have h21 := higham23_recursiveMaxNormLe_add r depth _ _ h21a h21b
      have h22 := higham23_recursiveMaxNormLe_add r depth _ _ h22a h22b
      have hpow : ((2 ^ (r + (depth + 1)) : ℕ) : ℝ) * a * b =
          (((2 ^ (r + depth) : ℕ) : ℝ) * a * b) +
            (((2 ^ (r + depth) : ℕ) : ℝ) * a * b) := by
        rw [show r + (depth + 1) = (r + depth) + 1 by omega, pow_succ]
        push_cast
        ring
      rw [hpow]
      simpa only [higham23Block2_mul_c11, higham23Block2_mul_c12,
        higham23Block2_mul_c21, higham23Block2_mul_c22] using
        (show Higham23RecursiveMaxNormLe r depth
              (A.c11 * B.c11 + A.c12 * B.c21) _ ∧
            Higham23RecursiveMaxNormLe r depth
              (A.c11 * B.c12 + A.c12 * B.c22) _ ∧
            Higham23RecursiveMaxNormLe r depth
              (A.c21 * B.c11 + A.c22 * B.c21) _ ∧
            Higham23RecursiveMaxNormLe r depth
              (A.c21 * B.c12 + A.c22 * B.c22) _ from
          ⟨h11, h12, h21, h22⟩)

theorem higham23_recursiveMaxNormLe_sub_of_error (r : ℕ) :
    ∀ depth (A B : Higham23RecursiveMatrix r depth) {e : ℝ},
      Higham23RecursiveErrorLe r depth A B e →
      Higham23RecursiveMaxNormLe r depth (A - B) e
  | 0, A, B, e, h => by simpa [Higham23RecursiveMaxNormLe] using h
  | depth + 1, A, B, e, h => by
      rcases h with ⟨h11, h12, h21, h22⟩
      exact ⟨higham23_recursiveMaxNormLe_sub_of_error r depth _ _ h11,
        higham23_recursiveMaxNormLe_sub_of_error r depth _ _ h12,
        higham23_recursiveMaxNormLe_sub_of_error r depth _ _ h21,
        higham23_recursiveMaxNormLe_sub_of_error r depth _ _ h22⟩

theorem higham23_recursiveErrorLe_of_maxNorm_sub (r : ℕ) :
    ∀ depth (A B : Higham23RecursiveMatrix r depth) {e : ℝ},
      Higham23RecursiveMaxNormLe r depth (A - B) e →
      Higham23RecursiveErrorLe r depth A B e
  | 0, A, B, e, h => by simpa [Higham23RecursiveMaxNormLe] using h
  | depth + 1, A, B, e, h => by
      rcases h with ⟨h11, h12, h21, h22⟩
      exact ⟨higham23_recursiveErrorLe_of_maxNorm_sub r depth _ _ h11,
        higham23_recursiveErrorLe_of_maxNorm_sub r depth _ _ h12,
        higham23_recursiveErrorLe_of_maxNorm_sub r depth _ _ h21,
        higham23_recursiveErrorLe_of_maxNorm_sub r depth _ _ h22⟩

/-- Perturbing both inputs of an exact product. -/
theorem higham23_recursiveErrorLe_mul (r depth : ℕ)
    (A Ahat B Bhat : Higham23RecursiveMatrix r depth)
    (aHat b dx dy : ℝ) (haHat : 0 ≤ aHat) (hb : 0 ≤ b)
    (hdx : 0 ≤ dx) (hdy : 0 ≤ dy)
    (hAhat : Higham23RecursiveMaxNormLe r depth Ahat aHat)
    (hB : Higham23RecursiveMaxNormLe r depth B b)
    (hAerr : Higham23RecursiveErrorLe r depth Ahat A dx)
    (hBerr : Higham23RecursiveErrorLe r depth Bhat B dy) :
    Higham23RecursiveErrorLe r depth (Ahat * Bhat) (A * B)
      (((2 ^ (r + depth) : ℕ) : ℝ) * dx * b +
        ((2 ^ (r + depth) : ℕ) : ℝ) * aHat * dy) := by
  have hDA := higham23_recursiveMaxNormLe_sub_of_error r depth Ahat A hAerr
  have hDB := higham23_recursiveMaxNormLe_sub_of_error r depth Bhat B hBerr
  have hfirst := higham23_recursiveMaxNormLe_mul r depth
    (Ahat - A) B dx b hdx hb hDA hB
  have hsecond := higham23_recursiveMaxNormLe_mul r depth
    Ahat (Bhat - B) aHat dy haHat hdy hAhat hDB
  have hsum := higham23_recursiveMaxNormLe_add r depth _ _ hfirst hsecond
  have hid : Ahat * Bhat - A * B =
      (Ahat - A) * B + Ahat * (Bhat - B) := by noncomm_ring
  rw [← hid] at hsum
  exact higham23_recursiveErrorLe_of_maxNorm_sub r depth _ _ hsum

/-- One rounded recursive addition introduces the standard local relative
error, uniformly across all scalar leaves. -/
theorem higham23_recursiveFlAdd_error (fp : FPModel) (r : ℕ) :
    ∀ depth (A B : Higham23RecursiveMatrix r depth) (a b : ℝ),
      0 ≤ a → 0 ≤ b →
      Higham23RecursiveMaxNormLe r depth A a →
      Higham23RecursiveMaxNormLe r depth B b →
      Higham23RecursiveErrorLe r depth (A + B)
        (higham23RecursiveFlAdd fp r depth A B) (fp.u * (a + b))
  | 0, A, B, a, b, ha, hb, hA, hB => by
      intro i j
      obtain ⟨delta, hdelta, hfl⟩ := fp.model_add (A i j) (B i j)
      change |A i j + B i j - fp.fl_add (A i j) (B i j)| ≤ _
      rw [hfl, show A i j + B i j - (A i j + B i j) * (1 + delta) =
        -(A i j + B i j) * delta by ring, abs_mul, abs_neg]
      calc
        |A i j + B i j| * |delta| ≤ (a + b) * fp.u := by
          exact mul_le_mul
            ((abs_add_le _ _).trans (add_le_add (hA i j) (hB i j)))
            hdelta (abs_nonneg _) (add_nonneg ha hb)
        _ = fp.u * (a + b) := by ring
  | depth + 1, A, B, a, b, ha, hb, hA, hB => by
      rcases hA with ⟨hA11, hA12, hA21, hA22⟩
      rcases hB with ⟨hB11, hB12, hB21, hB22⟩
      exact ⟨higham23_recursiveFlAdd_error fp r depth _ _ a b ha hb hA11 hB11,
        higham23_recursiveFlAdd_error fp r depth _ _ a b ha hb hA12 hB12,
        higham23_recursiveFlAdd_error fp r depth _ _ a b ha hb hA21 hB21,
        higham23_recursiveFlAdd_error fp r depth _ _ a b ha hb hA22 hB22⟩

theorem higham23_recursiveFlSub_error (fp : FPModel) (r : ℕ) :
    ∀ depth (A B : Higham23RecursiveMatrix r depth) (a b : ℝ),
      0 ≤ a → 0 ≤ b →
      Higham23RecursiveMaxNormLe r depth A a →
      Higham23RecursiveMaxNormLe r depth B b →
      Higham23RecursiveErrorLe r depth (A - B)
        (higham23RecursiveFlSub fp r depth A B) (fp.u * (a + b))
  | 0, A, B, a, b, ha, hb, hA, hB => by
      intro i j
      obtain ⟨delta, hdelta, hfl⟩ := fp.model_sub (A i j) (B i j)
      change |A i j - B i j - fp.fl_sub (A i j) (B i j)| ≤ _
      rw [hfl, show A i j - B i j - (A i j - B i j) * (1 + delta) =
        -(A i j - B i j) * delta by ring, abs_mul, abs_neg]
      calc
        |A i j - B i j| * |delta| ≤ (a + b) * fp.u := by
          exact mul_le_mul
            ((abs_sub _ _).trans (add_le_add (hA i j) (hB i j)))
            hdelta (abs_nonneg _) (add_nonneg ha hb)
        _ = fp.u * (a + b) := by ring
  | depth + 1, A, B, a, b, ha, hb, hA, hB => by
      rcases hA with ⟨hA11, hA12, hA21, hA22⟩
      rcases hB with ⟨hB11, hB12, hB21, hB22⟩
      exact ⟨higham23_recursiveFlSub_error fp r depth _ _ a b ha hb hA11 hB11,
        higham23_recursiveFlSub_error fp r depth _ _ a b ha hb hA12 hB12,
        higham23_recursiveFlSub_error fp r depth _ _ a b ha hb hA21 hB21,
        higham23_recursiveFlSub_error fp r depth _ _ a b ha hb hA22 hB22⟩

theorem higham23_recursiveFlAdd_norm (fp : FPModel) (r depth : ℕ)
    (A B : Higham23RecursiveMatrix r depth) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : Higham23RecursiveMaxNormLe r depth A a)
    (hB : Higham23RecursiveMaxNormLe r depth B b) :
    Higham23RecursiveMaxNormLe r depth
      (higham23RecursiveFlAdd fp r depth A B) ((1 + fp.u) * (a + b)) := by
  have hExact := higham23_recursiveMaxNormLe_add r depth A B hA hB
  have hErr := higham23_recursiveFlAdd_error fp r depth A B a b ha hb hA hB
  have h := higham23_recursiveMaxNormLe_of_error r depth _ _ hExact hErr
  convert h using 1 <;> ring

theorem higham23_recursiveFlSub_norm (fp : FPModel) (r depth : ℕ)
    (A B : Higham23RecursiveMatrix r depth) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : Higham23RecursiveMaxNormLe r depth A a)
    (hB : Higham23RecursiveMaxNormLe r depth B b) :
    Higham23RecursiveMaxNormLe r depth
      (higham23RecursiveFlSub fp r depth A B) ((1 + fp.u) * (a + b)) := by
  have hExact := higham23_recursiveMaxNormLe_sub r depth A B hA hB
  have hErr := higham23_recursiveFlSub_error fp r depth A B a b ha hb hA hB
  have h := higham23_recursiveMaxNormLe_of_error r depth _ _ hExact hErr
  convert h using 1 <;> ring

theorem higham23_recursiveFlAdd_pair (fp : FPModel) (r depth : ℕ)
    (A B : Higham23RecursiveMatrix r depth) (a : ℝ) (ha : 0 ≤ a)
    (hA : Higham23RecursiveMaxNormLe r depth A a)
    (hB : Higham23RecursiveMaxNormLe r depth B a) :
    Higham23RecursiveMaxNormLe r depth
        (higham23RecursiveFlAdd fp r depth A B) (2 * (1 + fp.u) * a) ∧
      Higham23RecursiveErrorLe r depth
        (higham23RecursiveFlAdd fp r depth A B) (A + B) (2 * fp.u * a) := by
  constructor
  · convert higham23_recursiveFlAdd_norm fp r depth A B a a ha ha hA hB using 1 <;>
      ring
  · apply higham23_recursiveErrorLe_symm r depth
    convert higham23_recursiveFlAdd_error fp r depth A B a a ha ha hA hB using 1 <;>
      ring

theorem higham23_recursiveFlSub_pair (fp : FPModel) (r depth : ℕ)
    (A B : Higham23RecursiveMatrix r depth) (a : ℝ) (ha : 0 ≤ a)
    (hA : Higham23RecursiveMaxNormLe r depth A a)
    (hB : Higham23RecursiveMaxNormLe r depth B a) :
    Higham23RecursiveMaxNormLe r depth
        (higham23RecursiveFlSub fp r depth A B) (2 * (1 + fp.u) * a) ∧
      Higham23RecursiveErrorLe r depth
        (higham23RecursiveFlSub fp r depth A B) (A - B) (2 * fp.u * a) := by
  constructor
  · convert higham23_recursiveFlSub_norm fp r depth A B a a ha ha hA hB using 1 <;>
      ring
  · apply higham23_recursiveErrorLe_symm r depth
    convert higham23_recursiveFlSub_error fp r depth A B a a ha ha hA hB using 1 <;>
      ring

/-- Transfer a recursive-product error theorem across rounded input
preparations.  This is the operation-level step used for each of the seven
Strassen products. -/
theorem higham23_recursiveProduct_transfer (r depth : ℕ)
    (X Xhat Y Yhat P : Higham23RecursiveMatrix r depth)
    (xHat y dx dy e : ℝ)
    (hxHat : 0 ≤ xHat) (hy : 0 ≤ y) (hdx : 0 ≤ dx)
    (hdy : 0 ≤ dy)
    (hXhat : Higham23RecursiveMaxNormLe r depth Xhat xHat)
    (hY : Higham23RecursiveMaxNormLe r depth Y y)
    (hYhat : Higham23RecursiveMaxNormLe r depth Yhat (y + dy))
    (hXerr : Higham23RecursiveErrorLe r depth Xhat X dx)
    (hYerr : Higham23RecursiveErrorLe r depth Yhat Y dy)
    (hRec : Higham23RecursiveErrorLe r depth (Xhat * Yhat) P
      (e * xHat * (y + dy))) :
    Higham23RecursiveErrorLe r depth (X * Y) P
        ((((2 ^ (r + depth) : ℕ) : ℝ) * dx * y +
          ((2 ^ (r + depth) : ℕ) : ℝ) * xHat * dy) +
            e * xHat * (y + dy)) ∧
      Higham23RecursiveMaxNormLe r depth P
        ((((2 ^ (r + depth) : ℕ) : ℝ) + e) * xHat * (y + dy)) := by
  have hyHat0 : 0 ≤ y + dy := add_nonneg hy hdy
  have hInput := higham23_recursiveErrorLe_mul r depth
    X Xhat Y Yhat xHat y dx dy hxHat hy hdx hdy hXhat hY hXerr hYerr
  have hInput' := higham23_recursiveErrorLe_symm r depth _ _ hInput
  have hErr := higham23_recursiveErrorLe_trans r depth _ _ _ hInput' hRec
  have hExact := higham23_recursiveMaxNormLe_mul r depth
    Xhat Yhat xHat (y + dy) hxHat hyHat0 hXhat hYhat
  have hNorm := higham23_recursiveMaxNormLe_of_error r depth _ _ hExact hRec
  refine ⟨hErr, ?_⟩
  convert hNorm using 1 <;> ring

/-- Rounding the three output operations in a four-term Strassen
recombination. -/
theorem higham23_recursiveFourTermRecombination_error
    (fp : FPModel) (r depth : ℕ)
    (P1 P2 P3 P4 : Higham23RecursiveMatrix r depth)
    (n1 n2 n3 n4 : ℝ)
    (hn1 : 0 ≤ n1) (hn2 : 0 ≤ n2) (hn3 : 0 ≤ n3) (hn4 : 0 ≤ n4)
    (hP1 : Higham23RecursiveMaxNormLe r depth P1 n1)
    (hP2 : Higham23RecursiveMaxNormLe r depth P2 n2)
    (hP3 : Higham23RecursiveMaxNormLe r depth P3 n3)
    (hP4 : Higham23RecursiveMaxNormLe r depth P4 n4) :
    let q1Norm := (1 + fp.u) * (n1 + n2)
    let q2Norm := (1 + fp.u) * (q1Norm + n3)
    Higham23RecursiveErrorLe r depth (P1 + P2 - P3 + P4)
      (higham23RecursiveFlAdd fp r depth
        (higham23RecursiveFlSub fp r depth
          (higham23RecursiveFlAdd fp r depth P1 P2) P3) P4)
      (fp.u * (n1 + n2) + fp.u * (q1Norm + n3) +
        fp.u * (q2Norm + n4)) := by
  dsimp only
  let Q1 := higham23RecursiveFlAdd fp r depth P1 P2
  let Q2 := higham23RecursiveFlSub fp r depth Q1 P3
  let q1Norm := (1 + fp.u) * (n1 + n2)
  let q2Norm := (1 + fp.u) * (q1Norm + n3)
  have hu1 : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
  have hq1n0 : 0 ≤ q1Norm :=
    mul_nonneg hu1 (add_nonneg hn1 hn2)
  have hq2n0 : 0 ≤ q2Norm :=
    mul_nonneg hu1 (add_nonneg hq1n0 hn3)
  have hE1 := higham23_recursiveFlAdd_error fp r depth
    P1 P2 n1 n2 hn1 hn2 hP1 hP2
  have hN1 := higham23_recursiveFlAdd_norm fp r depth
    P1 P2 n1 n2 hn1 hn2 hP1 hP2
  have hE2local := higham23_recursiveFlSub_error fp r depth
    Q1 P3 q1Norm n3 hq1n0 hn3 (by simpa [Q1, q1Norm] using hN1) hP3
  have hE1sub := higham23_recursiveErrorLe_sub r depth
    (P1 + P2) Q1 P3 P3 hE1 (higham23_recursiveErrorLe_refl r depth P3)
  have hE12raw := higham23_recursiveErrorLe_trans r depth
    (P1 + P2 - P3) (Q1 - P3) Q2 hE1sub hE2local
  have hE12 : Higham23RecursiveErrorLe r depth
      (P1 + P2 - P3) Q2
      (fp.u * (n1 + n2) + fp.u * (q1Norm + n3)) := by
    exact higham23_recursiveErrorLe_mono r depth _ _ hE12raw (by ring_nf; linarith)
  have hN2 := higham23_recursiveFlSub_norm fp r depth
    Q1 P3 q1Norm n3 hq1n0 hn3 (by simpa [Q1, q1Norm] using hN1) hP3
  have hE3local := higham23_recursiveFlAdd_error fp r depth
    Q2 P4 q2Norm n4 hq2n0 hn4 (by simpa [Q2, q2Norm] using hN2) hP4
  have hE12add := higham23_recursiveErrorLe_add r depth
    (P1 + P2 - P3) Q2 P4 P4 hE12
      (higham23_recursiveErrorLe_refl r depth P4)
  have hAll := higham23_recursiveErrorLe_trans r depth
    (P1 + P2 - P3 + P4) (Q2 + P4)
      (higham23RecursiveFlAdd fp r depth Q2 P4) hE12add hE3local
  exact higham23_recursiveErrorLe_mono r depth _ _ hAll (by ring_nf; linarith)

noncomputable def higham23StrassenHeavyError (m e u : ℝ) : ℝ :=
  m * (8 * u + 4 * u ^ 2) + 4 * (1 + u) ^ 2 * e

noncomputable def higham23StrassenLightError (m e u : ℝ) : ℝ :=
  m * (2 * u) + 2 * (1 + u) * e

noncomputable def higham23StrassenHeavyNorm (m e u : ℝ) : ℝ :=
  4 * (1 + u) ^ 2 * (m + e)

noncomputable def higham23StrassenLightNorm (m e u : ℝ) : ℝ :=
  2 * (1 + u) * (m + e)

/-- Two rounded input sums followed by a recursive product. -/
theorem higham23_strassenHeavyProduct_transfer
    (fp : FPModel) (r depth : ℕ)
    (X Xhat Y Yhat P : Higham23RecursiveMatrix r depth)
    (a b e : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hXhat : Higham23RecursiveMaxNormLe r depth Xhat
      (2 * (1 + fp.u) * a))
    (hY : Higham23RecursiveMaxNormLe r depth Y (2 * b))
    (hYhat : Higham23RecursiveMaxNormLe r depth Yhat
      (2 * (1 + fp.u) * b))
    (hXerr : Higham23RecursiveErrorLe r depth Xhat X (2 * fp.u * a))
    (hYerr : Higham23RecursiveErrorLe r depth Yhat Y (2 * fp.u * b))
    (hRec : Higham23RecursiveErrorLe r depth (Xhat * Yhat) P
      (e * (2 * (1 + fp.u) * a) * (2 * (1 + fp.u) * b))) :
    Higham23RecursiveErrorLe r depth (X * Y) P
        (higham23StrassenHeavyError
          ((2 ^ (r + depth) : ℕ) : ℝ) e fp.u * a * b) ∧
      Higham23RecursiveMaxNormLe r depth P
        (higham23StrassenHeavyNorm
          ((2 ^ (r + depth) : ℕ) : ℝ) e fp.u * a * b) := by
  have ht := higham23_recursiveProduct_transfer r depth X Xhat Y Yhat P
    (2 * (1 + fp.u) * a) (2 * b) (2 * fp.u * a) (2 * fp.u * b) e
    (mul_nonneg (mul_nonneg (by norm_num) (by linarith [fp.u_nonneg])) ha)
    (mul_nonneg (by norm_num) hb)
    (mul_nonneg (mul_nonneg (by norm_num) fp.u_nonneg) ha)
    (mul_nonneg (mul_nonneg (by norm_num) fp.u_nonneg) hb)
    hXhat hY (by convert hYhat using 1 <;> ring) hXerr hYerr
    (by convert hRec using 1 <;> ring)
  constructor
  · convert ht.1 using 1 <;> dsimp [higham23StrassenHeavyError] <;> ring
  · convert ht.2 using 1 <;> dsimp [higham23StrassenHeavyNorm] <;> ring

/-- One rounded left input sum followed by a recursive product. -/
theorem higham23_strassenLightLeftProduct_transfer
    (fp : FPModel) (r depth : ℕ)
    (X Xhat Y P : Higham23RecursiveMatrix r depth)
    (a b e : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hXhat : Higham23RecursiveMaxNormLe r depth Xhat
      (2 * (1 + fp.u) * a))
    (hY : Higham23RecursiveMaxNormLe r depth Y b)
    (hXerr : Higham23RecursiveErrorLe r depth Xhat X (2 * fp.u * a))
    (hRec : Higham23RecursiveErrorLe r depth (Xhat * Y) P
      (e * (2 * (1 + fp.u) * a) * b)) :
    Higham23RecursiveErrorLe r depth (X * Y) P
        (higham23StrassenLightError
          ((2 ^ (r + depth) : ℕ) : ℝ) e fp.u * a * b) ∧
      Higham23RecursiveMaxNormLe r depth P
        (higham23StrassenLightNorm
          ((2 ^ (r + depth) : ℕ) : ℝ) e fp.u * a * b) := by
  have ht := higham23_recursiveProduct_transfer r depth X Xhat Y Y P
    (2 * (1 + fp.u) * a) b (2 * fp.u * a) 0 e
    (mul_nonneg (mul_nonneg (by norm_num) (by linarith [fp.u_nonneg])) ha)
    hb (mul_nonneg (mul_nonneg (by norm_num) fp.u_nonneg) ha) (by norm_num)
    hXhat hY (by simpa using hY) hXerr
    (higham23_recursiveErrorLe_refl r depth Y)
    (by convert hRec using 1 <;> ring)
  constructor
  · convert ht.1 using 1 <;> dsimp [higham23StrassenLightError] <;> ring
  · convert ht.2 using 1 <;> dsimp [higham23StrassenLightNorm] <;> ring

/-- One rounded right input sum followed by a recursive product. -/
theorem higham23_strassenLightRightProduct_transfer
    (fp : FPModel) (r depth : ℕ)
    (X Y Yhat P : Higham23RecursiveMatrix r depth)
    (a b e : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hX : Higham23RecursiveMaxNormLe r depth X a)
    (hY : Higham23RecursiveMaxNormLe r depth Y (2 * b))
    (hYhat : Higham23RecursiveMaxNormLe r depth Yhat
      (2 * (1 + fp.u) * b))
    (hYerr : Higham23RecursiveErrorLe r depth Yhat Y (2 * fp.u * b))
    (hRec : Higham23RecursiveErrorLe r depth (X * Yhat) P
      (e * a * (2 * (1 + fp.u) * b))) :
    Higham23RecursiveErrorLe r depth (X * Y) P
        (higham23StrassenLightError
          ((2 ^ (r + depth) : ℕ) : ℝ) e fp.u * a * b) ∧
      Higham23RecursiveMaxNormLe r depth P
        (higham23StrassenLightNorm
          ((2 ^ (r + depth) : ℕ) : ℝ) e fp.u * a * b) := by
  have ht := higham23_recursiveProduct_transfer r depth X X Y Yhat P
    a (2 * b) 0 (2 * fp.u * b) e ha (mul_nonneg (by norm_num) hb)
    (by norm_num) (mul_nonneg (mul_nonneg (by norm_num) fp.u_nonneg) hb)
    hX hY (by convert hYhat using 1 <;> ring)
    (higham23_recursiveErrorLe_refl r depth X) hYerr
    (by convert hRec using 1 <;> ring)
  constructor
  · convert ht.1 using 1 <;> dsimp [higham23StrassenLightError] <;> ring
  · convert ht.2 using 1 <;> dsimp [higham23StrassenLightNorm] <;> ring

/-- Exact nonlinear coefficient proved for the literal recursive Strassen
evaluator.  Its linearization is the 12/46 recurrence in (23.16). -/
noncomputable def higham23StrassenExactMajorant
    (fp : FPModel) (r : ℕ) : ℕ → ℝ
  | 0 => ((2 ^ r : ℕ) : ℝ) * gamma fp (2 ^ r)
  | depth + 1 =>
      let u := fp.u
      let m : ℝ := (2 ^ (r + depth) : ℕ)
      let e := higham23StrassenExactMajorant fp r depth
      let heavyError := higham23StrassenHeavyError m e u
      let lightError := higham23StrassenLightError m e u
      let heavyNorm := higham23StrassenHeavyNorm m e u
      let lightNorm := higham23StrassenLightNorm m e u
      let q1Norm := (1 + u) * (heavyNorm + lightNorm)
      let q2Norm := (1 + u) * (q1Norm + lightNorm)
      2 * heavyError + 2 * lightError +
        u * (heavyNorm + lightNorm) + u * (q1Norm + lightNorm) +
          u * (q2Norm + heavyNorm)

theorem higham23_strassenExactMajorant_nonneg
    (fp : FPModel) (r depth : ℕ) (hvalid : gammaValid fp (2 ^ r)) :
    0 ≤ higham23StrassenExactMajorant fp r depth := by
  induction depth with
  | zero =>
      rw [higham23StrassenExactMajorant]
      exact mul_nonneg (Nat.cast_nonneg _) (gamma_nonneg fp hvalid)
  | succ depth ih =>
      dsimp only [higham23StrassenExactMajorant, higham23StrassenHeavyError,
        higham23StrassenLightError, higham23StrassenHeavyNorm,
        higham23StrassenLightNorm]
      have hu1 : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
      have hm : 0 ≤ ((2 ^ (r + depth) : ℕ) : ℝ) := Nat.cast_nonneg _
      have hpoly : 0 ≤ 8 * fp.u + 4 * fp.u ^ 2 := by
        nlinarith [fp.u_nonneg, sq_nonneg fp.u]
      have hHeavyError : 0 ≤
          ((2 ^ (r + depth) : ℕ) : ℝ) *
              (8 * fp.u + 4 * fp.u ^ 2) +
            4 * (1 + fp.u) ^ 2 * higham23StrassenExactMajorant fp r depth :=
        add_nonneg (mul_nonneg hm hpoly)
          (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) ih)
      have hLightError : 0 ≤
          ((2 ^ (r + depth) : ℕ) : ℝ) * (2 * fp.u) +
            2 * (1 + fp.u) * higham23StrassenExactMajorant fp r depth :=
        add_nonneg (mul_nonneg hm (mul_nonneg (by norm_num) fp.u_nonneg))
          (mul_nonneg (mul_nonneg (by norm_num) hu1) ih)
      have hHeavyNorm : 0 ≤ 4 * (1 + fp.u) ^ 2 *
          (((2 ^ (r + depth) : ℕ) : ℝ) +
            higham23StrassenExactMajorant fp r depth) := by positivity
      have hLightNorm : 0 ≤ 2 * (1 + fp.u) *
          (((2 ^ (r + depth) : ℕ) : ℝ) +
            higham23StrassenExactMajorant fp r depth) := by positivity
      have hq1 : 0 ≤ (1 + fp.u) *
          (4 * (1 + fp.u) ^ 2 *
              (((2 ^ (r + depth) : ℕ) : ℝ) +
                higham23StrassenExactMajorant fp r depth) +
            2 * (1 + fp.u) *
              (((2 ^ (r + depth) : ℕ) : ℝ) +
                higham23StrassenExactMajorant fp r depth)) := by positivity
      have hq2 : 0 ≤ (1 + fp.u) *
          ((1 + fp.u) *
              (4 * (1 + fp.u) ^ 2 *
                  (((2 ^ (r + depth) : ℕ) : ℝ) +
                    higham23StrassenExactMajorant fp r depth) +
                2 * (1 + fp.u) *
                  (((2 ^ (r + depth) : ℕ) : ℝ) +
                    higham23StrassenExactMajorant fp r depth)) +
            2 * (1 + fp.u) *
              (((2 ^ (r + depth) : ℕ) : ℝ) +
                higham23StrassenExactMajorant fp r depth)) := by positivity
      have ht1 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hHeavyError
      have ht2 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hLightError
      have ht3 := mul_nonneg fp.u_nonneg (add_nonneg hHeavyNorm hLightNorm)
      have ht4 := mul_nonneg fp.u_nonneg (add_nonneg hq1 hLightNorm)
      have ht5 := mul_nonneg fp.u_nonneg (add_nonneg hq2 hHeavyNorm)
      nlinarith

/-- Literal recursive Strassen evaluation.  The base case calls the actual
left-to-right rounded dot-product matrix multiplication; every block sum and
output recombination is rounded entrywise in the order printed in (23.4). -/
noncomputable def higham23FlStrassenRecursive (fp : FPModel) (r : ℕ) :
    (depth : ℕ) → Higham23RecursiveMatrix r depth →
      Higham23RecursiveMatrix r depth → Higham23RecursiveMatrix r depth
  | 0, A, B => higham23FlMatrixMul fp A B
  | depth + 1, A, B =>
      let p1 := higham23FlStrassenRecursive fp r depth
        (higham23RecursiveFlAdd fp r depth A.c11 A.c22)
        (higham23RecursiveFlAdd fp r depth B.c11 B.c22)
      let p2 := higham23FlStrassenRecursive fp r depth
        (higham23RecursiveFlAdd fp r depth A.c21 A.c22) B.c11
      let p3 := higham23FlStrassenRecursive fp r depth A.c11
        (higham23RecursiveFlSub fp r depth B.c12 B.c22)
      let p4 := higham23FlStrassenRecursive fp r depth A.c22
        (higham23RecursiveFlSub fp r depth B.c21 B.c11)
      let p5 := higham23FlStrassenRecursive fp r depth
        (higham23RecursiveFlAdd fp r depth A.c11 A.c12) B.c22
      let p6 := higham23FlStrassenRecursive fp r depth
        (higham23RecursiveFlSub fp r depth A.c21 A.c11)
        (higham23RecursiveFlAdd fp r depth B.c11 B.c12)
      let p7 := higham23FlStrassenRecursive fp r depth
        (higham23RecursiveFlSub fp r depth A.c12 A.c22)
        (higham23RecursiveFlAdd fp r depth B.c21 B.c22)
      { c11 := higham23RecursiveFlAdd fp r depth
          (higham23RecursiveFlSub fp r depth
            (higham23RecursiveFlAdd fp r depth p1 p4) p5) p7
        c12 := higham23RecursiveFlAdd fp r depth p3 p5
        c21 := higham23RecursiveFlAdd fp r depth p2 p4
        c22 := higham23RecursiveFlAdd fp r depth
          (higham23RecursiveFlSub fp r depth
            (higham23RecursiveFlAdd fp r depth p1 p3) p2) p6 }

/-- Literal recursive Winograd--Strassen evaluation, with all 15 additions
rounded in the dependency order of (23.6). -/
noncomputable def higham23FlWinogradStrassenRecursive
    (fp : FPModel) (r : ℕ) :
    (depth : ℕ) → Higham23RecursiveMatrix r depth →
      Higham23RecursiveMatrix r depth → Higham23RecursiveMatrix r depth
  | 0, A, B => higham23FlMatrixMul fp A B
  | depth + 1, A, B =>
      let s1 := higham23RecursiveFlAdd fp r depth A.c21 A.c22
      let s2 := higham23RecursiveFlSub fp r depth s1 A.c11
      let s3 := higham23RecursiveFlSub fp r depth A.c11 A.c21
      let s4 := higham23RecursiveFlSub fp r depth A.c12 s2
      let s5 := higham23RecursiveFlSub fp r depth B.c12 B.c11
      let s6 := higham23RecursiveFlSub fp r depth B.c22 s5
      let s7 := higham23RecursiveFlSub fp r depth B.c22 B.c12
      let s8 := higham23RecursiveFlSub fp r depth s6 B.c21
      let m1 := higham23FlWinogradStrassenRecursive fp r depth s2 s6
      let m2 := higham23FlWinogradStrassenRecursive fp r depth A.c11 B.c11
      let m3 := higham23FlWinogradStrassenRecursive fp r depth A.c12 B.c21
      let m4 := higham23FlWinogradStrassenRecursive fp r depth s3 s7
      let m5 := higham23FlWinogradStrassenRecursive fp r depth s1 s5
      let m6 := higham23FlWinogradStrassenRecursive fp r depth s4 B.c22
      let m7 := higham23FlWinogradStrassenRecursive fp r depth A.c22 s8
      let t1 := higham23RecursiveFlAdd fp r depth m1 m2
      let t2 := higham23RecursiveFlAdd fp r depth t1 m4
      { c11 := higham23RecursiveFlAdd fp r depth m2 m3
        c12 := higham23RecursiveFlAdd fp r depth
          (higham23RecursiveFlAdd fp r depth t1 m5) m6
        c21 := higham23RecursiveFlSub fp r depth t2 m7
        c22 := higham23RecursiveFlAdd fp r depth t2 m5 }

/-- Theorem 23.2 at exact nonlinear radius.  Unlike the scalar recurrence
surface, this theorem is proved by induction over the actual recursively
rounded Strassen evaluator. -/
theorem higham23_theorem23_2_strassen_exactMajorant
    (fp : FPModel) (r : ℕ) (hvalid : gammaValid fp (2 ^ r)) :
    ∀ depth (A B : Higham23RecursiveMatrix r depth) (a b : ℝ),
      0 ≤ a → 0 ≤ b →
      Higham23RecursiveMaxNormLe r depth A a →
      Higham23RecursiveMaxNormLe r depth B b →
      Higham23RecursiveErrorLe r depth (A * B)
        (higham23FlStrassenRecursive fp r depth A B)
        (higham23StrassenExactMajorant fp r depth * a * b) := by
  intro depth
  induction depth with
  | zero =>
      intro A B a b ha _hb hA hB
      intro i j
      have hcomp := higham23_eq23_10_conventional_componentwise
        fp A B hvalid i j
      have hsum : (∑ k : Fin (2 ^ r), |A i k| * |B k j|) ≤
          ((2 ^ r : ℕ) : ℝ) * a * b := by
        calc
          (∑ k : Fin (2 ^ r), |A i k| * |B k j|) ≤
              ∑ _k : Fin (2 ^ r), a * b := by
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul (hA i k) (hB k j) (abs_nonneg _) ha
          _ = ((2 ^ r : ℕ) : ℝ) * a * b := by simp; ring
      change |(A * B) i j - higham23FlMatrixMul fp A B i j| ≤ _
      calc
        |(A * B) i j - higham23FlMatrixMul fp A B i j| ≤
            gamma fp (2 ^ r) *
              ∑ k : Fin (2 ^ r), |A i k| * |B k j| := hcomp
        _ ≤ gamma fp (2 ^ r) *
            (((2 ^ r : ℕ) : ℝ) * a * b) :=
          mul_le_mul_of_nonneg_left hsum (gamma_nonneg fp hvalid)
        _ = higham23StrassenExactMajorant fp r 0 * a * b := by
          simp [higham23StrassenExactMajorant]
          ring
  | succ depth ih =>
      intro A B a b ha hb hA hB
      rcases hA with ⟨hA11, hA12, hA21, hA22⟩
      rcases hB with ⟨hB11, hB12, hB21, hB22⟩
      let u := fp.u
      let m : ℝ := (2 ^ (r + depth) : ℕ)
      let e := higham23StrassenExactMajorant fp r depth
      let HE := higham23StrassenHeavyError m e u
      let LE := higham23StrassenLightError m e u
      let HN := higham23StrassenHeavyNorm m e u
      let LN := higham23StrassenLightNorm m e u
      let q1N := (1 + u) * (HN + LN)
      let q2N := (1 + u) * (q1N + LN)
      let roundN := u * (HN + LN) + u * (q1N + LN) + u * (q2N + HN)
      have he0 : 0 ≤ e := higham23_strassenExactMajorant_nonneg fp r depth hvalid
      have hm0 : 0 ≤ m := by dsimp [m]; positivity
      have hu1 : 0 ≤ 1 + u := by dsimp [u]; linarith [fp.u_nonneg]
      have haHat : 0 ≤ 2 * (1 + u) * a := by positivity
      have hbHat : 0 ≤ 2 * (1 + u) * b := by positivity
      have hHE0 : 0 ≤ HE := by
        dsimp [HE, higham23StrassenHeavyError, u]
        have hp : 0 ≤ 8 * fp.u + 4 * fp.u ^ 2 := by
          nlinarith [fp.u_nonneg, sq_nonneg fp.u]
        positivity
      have hLE0 : 0 ≤ LE := by
        dsimp [LE, higham23StrassenLightError, u]
        exact add_nonneg
          (mul_nonneg hm0 (mul_nonneg (by norm_num) fp.u_nonneg))
          (mul_nonneg (mul_nonneg (by norm_num) hu1) he0)
      have hHN0 : 0 ≤ HN := by
        dsimp [HN, higham23StrassenHeavyNorm]
        positivity
      have hLN0 : 0 ≤ LN := by
        dsimp [LN, higham23StrassenLightNorm]
        positivity
      have hq1N0 : 0 ≤ q1N := by dsimp [q1N]; positivity
      have hq2N0 : 0 ≤ q2N := by dsimp [q2N]; positivity
      have hroundN0 : 0 ≤ roundN := by
        dsimp [roundN]
        exact add_nonneg
          (add_nonneg
            (mul_nonneg fp.u_nonneg (add_nonneg hHN0 hLN0))
            (mul_nonneg fp.u_nonneg (add_nonneg hq1N0 hLN0)))
          (mul_nonneg fp.u_nonneg (add_nonneg hq2N0 hHN0))
      have hstepRadius :
          (2 * HE + 2 * LE) * a * b + roundN * a * b =
            higham23StrassenExactMajorant fp r (depth + 1) * a * b := by
        dsimp [higham23StrassenExactMajorant, roundN, q1N, q2N,
          HE, LE, HN, LN, u, m, e]
        ring

      let x1 := higham23RecursiveFlAdd fp r depth A.c11 A.c22
      let y1 := higham23RecursiveFlAdd fp r depth B.c11 B.c22
      let x2 := higham23RecursiveFlAdd fp r depth A.c21 A.c22
      let y3 := higham23RecursiveFlSub fp r depth B.c12 B.c22
      let y4 := higham23RecursiveFlSub fp r depth B.c21 B.c11
      let x5 := higham23RecursiveFlAdd fp r depth A.c11 A.c12
      let x6 := higham23RecursiveFlSub fp r depth A.c21 A.c11
      let y6 := higham23RecursiveFlAdd fp r depth B.c11 B.c12
      let x7 := higham23RecursiveFlSub fp r depth A.c12 A.c22
      let y7 := higham23RecursiveFlAdd fp r depth B.c21 B.c22
      let p1 := higham23FlStrassenRecursive fp r depth x1 y1
      let p2 := higham23FlStrassenRecursive fp r depth x2 B.c11
      let p3 := higham23FlStrassenRecursive fp r depth A.c11 y3
      let p4 := higham23FlStrassenRecursive fp r depth A.c22 y4
      let p5 := higham23FlStrassenRecursive fp r depth x5 B.c22
      let p6 := higham23FlStrassenRecursive fp r depth x6 y6
      let p7 := higham23FlStrassenRecursive fp r depth x7 y7

      have hx1 := higham23_recursiveFlAdd_pair fp r depth
        A.c11 A.c22 a ha hA11 hA22
      have hy1 := higham23_recursiveFlAdd_pair fp r depth
        B.c11 B.c22 b hb hB11 hB22
      have hx2 := higham23_recursiveFlAdd_pair fp r depth
        A.c21 A.c22 a ha hA21 hA22
      have hy3 := higham23_recursiveFlSub_pair fp r depth
        B.c12 B.c22 b hb hB12 hB22
      have hy4 := higham23_recursiveFlSub_pair fp r depth
        B.c21 B.c11 b hb hB21 hB11
      have hx5 := higham23_recursiveFlAdd_pair fp r depth
        A.c11 A.c12 a ha hA11 hA12
      have hx6 := higham23_recursiveFlSub_pair fp r depth
        A.c21 A.c11 a ha hA21 hA11
      have hy6 := higham23_recursiveFlAdd_pair fp r depth
        B.c11 B.c12 b hb hB11 hB12
      have hx7 := higham23_recursiveFlSub_pair fp r depth
        A.c12 A.c22 a ha hA12 hA22
      have hy7 := higham23_recursiveFlAdd_pair fp r depth
        B.c21 B.c22 b hb hB21 hB22
      have hBsum11_22 := higham23_recursiveMaxNormLe_add r depth
        B.c11 B.c22 hB11 hB22
      have hBsub12_22 := higham23_recursiveMaxNormLe_sub r depth
        B.c12 B.c22 hB12 hB22
      have hBsub21_11 := higham23_recursiveMaxNormLe_sub r depth
        B.c21 B.c11 hB21 hB11
      have hBsum11_12 := higham23_recursiveMaxNormLe_add r depth
        B.c11 B.c12 hB11 hB12
      have hBsum21_22 := higham23_recursiveMaxNormLe_add r depth
        B.c21 B.c22 hB21 hB22

      have hp1Rec := ih x1 y1 (2 * (1 + u) * a) (2 * (1 + u) * b)
        haHat hbHat (by simpa [x1, u] using hx1.1) (by simpa [y1, u] using hy1.1)
      have hp1 := higham23_strassenHeavyProduct_transfer fp r depth
        (A.c11 + A.c22) x1 (B.c11 + B.c22) y1 p1 a b e ha hb
        (by simpa [x1, u] using hx1.1)
        (by convert hBsum11_22 using 1 <;> ring)
        (by simpa [y1, u] using hy1.1)
        (by simpa [x1, u] using hx1.2)
        (by simpa [y1, u] using hy1.2)
        (by simpa [p1, e] using hp1Rec)

      have hp2Rec := ih x2 B.c11 (2 * (1 + u) * a) b
        haHat hb (by simpa [x2, u] using hx2.1) hB11
      have hp2 := higham23_strassenLightLeftProduct_transfer fp r depth
        (A.c21 + A.c22) x2 B.c11 p2 a b e ha hb
        (by simpa [x2, u] using hx2.1) hB11
        (by simpa [x2, u] using hx2.2)
        (by simpa [p2, e] using hp2Rec)

      have hp3Rec := ih A.c11 y3 a (2 * (1 + u) * b)
        ha hbHat hA11 (by simpa [y3, u] using hy3.1)
      have hp3 := higham23_strassenLightRightProduct_transfer fp r depth
        A.c11 (B.c12 - B.c22) y3 p3 a b e ha hb hA11
        (by convert hBsub12_22 using 1 <;> ring)
        (by simpa [y3, u] using hy3.1)
        (by simpa [y3, u] using hy3.2)
        (by simpa [p3, e] using hp3Rec)

      have hp4Rec := ih A.c22 y4 a (2 * (1 + u) * b)
        ha hbHat hA22 (by simpa [y4, u] using hy4.1)
      have hp4 := higham23_strassenLightRightProduct_transfer fp r depth
        A.c22 (B.c21 - B.c11) y4 p4 a b e ha hb hA22
        (by convert hBsub21_11 using 1 <;> ring)
        (by simpa [y4, u] using hy4.1)
        (by simpa [y4, u] using hy4.2)
        (by simpa [p4, e] using hp4Rec)

      have hp5Rec := ih x5 B.c22 (2 * (1 + u) * a) b
        haHat hb (by simpa [x5, u] using hx5.1) hB22
      have hp5 := higham23_strassenLightLeftProduct_transfer fp r depth
        (A.c11 + A.c12) x5 B.c22 p5 a b e ha hb
        (by simpa [x5, u] using hx5.1) hB22
        (by simpa [x5, u] using hx5.2)
        (by simpa [p5, e] using hp5Rec)

      have hp6Rec := ih x6 y6 (2 * (1 + u) * a) (2 * (1 + u) * b)
        haHat hbHat (by simpa [x6, u] using hx6.1) (by simpa [y6, u] using hy6.1)
      have hp6 := higham23_strassenHeavyProduct_transfer fp r depth
        (A.c21 - A.c11) x6 (B.c11 + B.c12) y6 p6 a b e ha hb
        (by simpa [x6, u] using hx6.1)
        (by convert hBsum11_12 using 1 <;> ring)
        (by simpa [y6, u] using hy6.1)
        (by simpa [x6, u] using hx6.2)
        (by simpa [y6, u] using hy6.2)
        (by simpa [p6, e] using hp6Rec)

      have hp7Rec := ih x7 y7 (2 * (1 + u) * a) (2 * (1 + u) * b)
        haHat hbHat (by simpa [x7, u] using hx7.1) (by simpa [y7, u] using hy7.1)
      have hp7 := higham23_strassenHeavyProduct_transfer fp r depth
        (A.c12 - A.c22) x7 (B.c21 + B.c22) y7 p7 a b e ha hb
        (by simpa [x7, u] using hx7.1)
        (by convert hBsum21_22 using 1 <;> ring)
        (by simpa [y7, u] using hy7.1)
        (by simpa [x7, u] using hx7.2)
        (by simpa [y7, u] using hy7.2)
        (by simpa [p7, e] using hp7Rec)

      have hnH0 : 0 ≤ HN * a * b := by positivity
      have hnL0 : 0 ≤ LN * a * b := by positivity
      have hRound11raw := higham23_recursiveFourTermRecombination_error
        fp r depth p1 p4 p5 p7 (HN * a * b) (LN * a * b)
          (LN * a * b) (HN * a * b) hnH0 hnL0 hnL0 hnH0
          hp1.2 hp4.2 hp5.2 hp7.2
      have hRound11 : Higham23RecursiveErrorLe r depth
          (p1 + p4 - p5 + p7)
          (higham23RecursiveFlAdd fp r depth
            (higham23RecursiveFlSub fp r depth
              (higham23RecursiveFlAdd fp r depth p1 p4) p5) p7)
          (roundN * a * b) := by
        convert hRound11raw using 1 <;> dsimp [roundN, q1N, q2N, u] <;> ring
      have hProducts11a := higham23_recursiveErrorLe_add r depth
        ((A.c11 + A.c22) * (B.c11 + B.c22)) p1
        (A.c22 * (B.c21 - B.c11)) p4 hp1.1 hp4.1
      have hProducts11b := higham23_recursiveErrorLe_sub r depth
        ((A.c11 + A.c22) * (B.c11 + B.c22) + A.c22 * (B.c21 - B.c11))
        (p1 + p4) ((A.c11 + A.c12) * B.c22) p5 hProducts11a hp5.1
      have hProducts11c := higham23_recursiveErrorLe_add r depth
        ((A.c11 + A.c22) * (B.c11 + B.c22) + A.c22 * (B.c21 - B.c11) -
          (A.c11 + A.c12) * B.c22) (p1 + p4 - p5)
        ((A.c12 - A.c22) * (B.c21 + B.c22)) p7 hProducts11b hp7.1
      have hProducts11 : Higham23RecursiveErrorLe r depth
          ((A.c11 + A.c22) * (B.c11 + B.c22) + A.c22 * (B.c21 - B.c11) -
            (A.c11 + A.c12) * B.c22 + (A.c12 - A.c22) * (B.c21 + B.c22))
          (p1 + p4 - p5 + p7) ((2 * HE + 2 * LE) * a * b) := by
        convert hProducts11c using 1 <;> dsimp [HE, LE] <;> ring
      have h11raw := higham23_recursiveErrorLe_trans r depth _ _ _
        hProducts11 hRound11
      have h11 : Higham23RecursiveErrorLe r depth (A * B).c11
          (higham23FlStrassenRecursive fp r (depth + 1) A B).c11
          (higham23StrassenExactMajorant fp r (depth + 1) * a * b) := by
        have hc := congrArg (fun X : Higham23Block2
            (R := Higham23RecursiveMatrix r depth) ↦ X.c11)
          (higham23_eq23_4_strassen_correct A B)
        change (higham23Strassen2 A B).c11 = (A * B).c11 at hc
        rw [← hc, ← hstepRadius]
        simpa [higham23Strassen2, higham23FlStrassenRecursive, p1, p4, p5, p7,
          x1, y1, y4, x5, x7, y7] using h11raw

      have hProducts22a := higham23_recursiveErrorLe_add r depth
        ((A.c11 + A.c22) * (B.c11 + B.c22)) p1
        (A.c11 * (B.c12 - B.c22)) p3 hp1.1 hp3.1
      have hProducts22b := higham23_recursiveErrorLe_sub r depth
        ((A.c11 + A.c22) * (B.c11 + B.c22) + A.c11 * (B.c12 - B.c22))
        (p1 + p3) ((A.c21 + A.c22) * B.c11) p2 hProducts22a hp2.1
      have hProducts22c := higham23_recursiveErrorLe_add r depth
        ((A.c11 + A.c22) * (B.c11 + B.c22) + A.c11 * (B.c12 - B.c22) -
          (A.c21 + A.c22) * B.c11) (p1 + p3 - p2)
        ((A.c21 - A.c11) * (B.c11 + B.c12)) p6 hProducts22b hp6.1
      have hProducts22 : Higham23RecursiveErrorLe r depth
          ((A.c11 + A.c22) * (B.c11 + B.c22) + A.c11 * (B.c12 - B.c22) -
            (A.c21 + A.c22) * B.c11 +
              (A.c21 - A.c11) * (B.c11 + B.c12))
          (p1 + p3 - p2 + p6)
          ((2 * HE + 2 * LE) * a * b) := by
        convert hProducts22c using 1 <;> dsimp [HE, LE] <;> ring
      have hRound22raw := higham23_recursiveFourTermRecombination_error
        fp r depth p1 p3 p2 p6 (HN * a * b) (LN * a * b)
          (LN * a * b) (HN * a * b) hnH0 hnL0 hnL0 hnH0
          hp1.2 hp3.2 hp2.2 hp6.2
      have hRound22 : Higham23RecursiveErrorLe r depth
          (p1 + p3 - p2 + p6)
          (higham23RecursiveFlAdd fp r depth
            (higham23RecursiveFlSub fp r depth
              (higham23RecursiveFlAdd fp r depth p1 p3) p2) p6)
          (roundN * a * b) := by
        convert hRound22raw using 1 <;> dsimp [roundN, q1N, q2N, u] <;> ring
      have h22raw := higham23_recursiveErrorLe_trans r depth _ _ _
        hProducts22 hRound22
      have h22 : Higham23RecursiveErrorLe r depth (A * B).c22
          (higham23FlStrassenRecursive fp r (depth + 1) A B).c22
          (higham23StrassenExactMajorant fp r (depth + 1) * a * b) := by
        have hc := congrArg (fun X : Higham23Block2
            (R := Higham23RecursiveMatrix r depth) ↦ X.c22)
          (higham23_eq23_4_strassen_correct A B)
        change (higham23Strassen2 A B).c22 = (A * B).c22 at hc
        rw [← hc, ← hstepRadius]
        simpa [higham23Strassen2, higham23FlStrassenRecursive, p1, p2, p3, p6,
          x1, y1, x2, y3, x6, y6] using h22raw

      have hHNgeLN : LN ≤ HN := by
        dsimp [LN, HN, higham23StrassenLightNorm,
          higham23StrassenHeavyNorm]
        have hs : 0 ≤ 2 * (1 + u) * (m + e) := by positivity
        have hfac : 0 ≤ 2 * (1 + u) - 1 := by
          dsimp [u]
          linarith [fp.u_nonneg]
        nlinarith [mul_nonneg hs hfac]
      have hSmallRadius :
          (2 * LE * a * b + u * (2 * LN * a * b)) ≤
            higham23StrassenExactMajorant fp r (depth + 1) * a * b := by
        have hab0 : 0 ≤ a * b := mul_nonneg ha hb
        have hu0 : 0 ≤ u := by exact fp.u_nonneg
        have hfirst : u * (2 * LN) ≤ u * (HN + LN) := by
          exact mul_le_mul_of_nonneg_left (by linarith) hu0
        have hroundLower : u * (2 * LN) ≤ roundN := by
          have ht2 : 0 ≤ u * (q1N + LN) :=
            mul_nonneg hu0 (add_nonneg hq1N0 hLN0)
          have ht3 : 0 ≤ u * (q2N + HN) :=
            mul_nonneg hu0 (add_nonneg hq2N0 hHN0)
          dsimp [roundN]
          linarith
        have hcoef :
            2 * LE + u * (2 * LN) ≤ 2 * HE + 2 * LE + roundN := by
          linarith
        calc
          2 * LE * a * b + u * (2 * LN * a * b) =
              (2 * LE + u * (2 * LN)) * (a * b) := by ring
          _ ≤ (2 * HE + 2 * LE + roundN) * (a * b) :=
            mul_le_mul_of_nonneg_right hcoef hab0
          _ = (2 * HE + 2 * LE) * a * b + roundN * a * b := by ring
          _ = _ := hstepRadius
      have h12prod := higham23_recursiveErrorLe_add r depth
        (A.c11 * (B.c12 - B.c22)) p3 ((A.c11 + A.c12) * B.c22) p5
        hp3.1 hp5.1
      have h12round := higham23_recursiveFlAdd_error fp r depth p3 p5
        (LN * a * b) (LN * a * b) hnL0 hnL0 hp3.2 hp5.2
      have h12raw := higham23_recursiveErrorLe_trans r depth _ _ _ h12prod h12round
      have h12 : Higham23RecursiveErrorLe r depth (A * B).c12
          (higham23FlStrassenRecursive fp r (depth + 1) A B).c12
          (higham23StrassenExactMajorant fp r (depth + 1) * a * b) := by
        have hc := congrArg (fun X : Higham23Block2
            (R := Higham23RecursiveMatrix r depth) ↦ X.c12)
          (higham23_eq23_4_strassen_correct A B)
        change (higham23Strassen2 A B).c12 = (A * B).c12 at hc
        have hm := higham23_recursiveErrorLe_mono r depth _ _ h12raw
          (by
            calc
              LE * a * b + LE * a * b + fp.u * (LN * a * b + LN * a * b) =
                  2 * LE * a * b + u * (2 * LN * a * b) := by dsimp [u]; ring
              _ ≤ _ := hSmallRadius)
        rw [← hc]
        simpa [higham23Strassen2, higham23FlStrassenRecursive, p3, p5,
          y3, x5] using hm
      have h21prod := higham23_recursiveErrorLe_add r depth
        ((A.c21 + A.c22) * B.c11) p2 (A.c22 * (B.c21 - B.c11)) p4
        hp2.1 hp4.1
      have h21round := higham23_recursiveFlAdd_error fp r depth p2 p4
        (LN * a * b) (LN * a * b) hnL0 hnL0 hp2.2 hp4.2
      have h21raw := higham23_recursiveErrorLe_trans r depth _ _ _ h21prod h21round
      have h21 : Higham23RecursiveErrorLe r depth (A * B).c21
          (higham23FlStrassenRecursive fp r (depth + 1) A B).c21
          (higham23StrassenExactMajorant fp r (depth + 1) * a * b) := by
        have hc := congrArg (fun X : Higham23Block2
            (R := Higham23RecursiveMatrix r depth) ↦ X.c21)
          (higham23_eq23_4_strassen_correct A B)
        change (higham23Strassen2 A B).c21 = (A * B).c21 at hc
        have hm := higham23_recursiveErrorLe_mono r depth _ _ h21raw
          (by
            calc
              LE * a * b + LE * a * b + fp.u * (LN * a * b + LN * a * b) =
                  2 * LE * a * b + u * (2 * LN * a * b) := by dsimp [u]; ring
              _ ≤ _ := hSmallRadius)
        rw [← hc]
        simpa [higham23Strassen2, higham23FlStrassenRecursive, p2, p4,
          x2, y4] using hm
      exact ⟨h11, h12, h21, h22⟩

/-! ## First-order source coefficient and genuine quadratic remainder -/

/-- The exact one-level scalar majorant generated by the literal Strassen
dataflow. -/
noncomputable def higham23StrassenStepMajorant (m e u : ℝ) : ℝ :=
  let heavyError := higham23StrassenHeavyError m e u
  let lightError := higham23StrassenLightError m e u
  let heavyNorm := higham23StrassenHeavyNorm m e u
  let lightNorm := higham23StrassenLightNorm m e u
  let q1Norm := (1 + u) * (heavyNorm + lightNorm)
  let q2Norm := (1 + u) * (q1Norm + lightNorm)
  2 * heavyError + 2 * lightError +
    u * (heavyNorm + lightNorm) + u * (q1Norm + lightNorm) +
      u * (q2Norm + heavyNorm)

/-- Nonlinear part left after removing the source's one-level linearization
`46*m*u + 12*e`. -/
noncomputable def higham23StrassenStepResidual (m e u : ℝ) : ℝ :=
  higham23StrassenStepMajorant m e u - (46 * m * u + 12 * e)

private noncomputable def higham23StrassenStepMQuadratic (u : ℝ) : ℝ :=
  70 + 54 * u + 22 * u ^ 2 + 4 * u ^ 3

private noncomputable def higham23StrassenStepEQuadratic (u : ℝ) : ℝ :=
  46 + 70 * u + 54 * u ^ 2 + 22 * u ^ 3 + 4 * u ^ 4

/-- Exact factorization showing that every term discarded by the 12/46
linearization has total order at least two when `e = O(u)`. -/
theorem higham23_strassenStepResidual_factor (m e u : ℝ) :
    higham23StrassenStepResidual m e u =
      m * u ^ 2 * higham23StrassenStepMQuadratic u +
        e * u * higham23StrassenStepEQuadratic u := by
  unfold higham23StrassenStepResidual higham23StrassenStepMajorant
    higham23StrassenStepMQuadratic higham23StrassenStepEQuadratic
    higham23StrassenHeavyError higham23StrassenLightError
    higham23StrassenHeavyNorm higham23StrassenLightNorm
  ring

private theorem higham23_strassenStepMQuadratic_continuousAt :
    ContinuousAt higham23StrassenStepMQuadratic 0 := by
  unfold higham23StrassenStepMQuadratic
  fun_prop

private theorem higham23_strassenStepEQuadratic_continuousAt :
    ContinuousAt higham23StrassenStepEQuadratic 0 := by
  unfold higham23StrassenStepEQuadratic
  fun_prop

/-- A one-level Strassen residual preserves quadratic order whenever the
recursive error entering that level is first order. -/
theorem higham23_strassenStepResidual_isBigO_u_sq
    (m : ℝ) (e : ℝ → ℝ)
    (he : e =O[𝓝 0] (fun u : ℝ ↦ u)) :
    (fun u : ℝ ↦ higham23StrassenStepResidual m (e u) u)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
  have huSq : (fun u : ℝ ↦ u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) :=
    Asymptotics.isBigO_refl _ _
  have hMCoeff :
      (fun u : ℝ ↦ m * higham23StrassenStepMQuadratic u)
        =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    (continuousAt_const.mul higham23_strassenStepMQuadratic_continuousAt).isBigO_one ℝ
  have hMTerm :
      (fun u : ℝ ↦ m * u ^ 2 * higham23StrassenStepMQuadratic u)
        =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    have h := huSq.mul hMCoeff
    simpa only [mul_one, mul_assoc, mul_comm, mul_left_comm] using h
  have hu : (fun u : ℝ ↦ u) =O[𝓝 0] (fun u : ℝ ↦ u) :=
    Asymptotics.isBigO_refl _ _
  have hECoeff :
      (fun u : ℝ ↦ higham23StrassenStepEQuadratic u)
        =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    higham23_strassenStepEQuadratic_continuousAt.isBigO_one ℝ
  have hETerm :
      (fun u : ℝ ↦ e u * u * higham23StrassenStepEQuadratic u)
        =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    have h := (he.mul hu).mul hECoeff
    simpa only [pow_two, mul_one, mul_assoc] using h
  have h := hMTerm.add hETerm
  apply h.congr'
  · exact Filter.Eventually.of_forall fun u ↦ by
      exact (higham23_strassenStepResidual_factor m (e u) u).symm
  · exact Filter.EventuallyEq.rfl

/-- The exact nonlinear Strassen majorant as a function of a variable unit
roundoff.  At depth zero it is the exact gamma split; recursive levels use
the literal one-level majorant. -/
noncomputable def higham23StrassenMajorantFamily (r : ℕ) : ℕ → ℝ → ℝ
  | 0, u =>
      (4 : ℝ) ^ r * u +
        ((2 ^ r : ℕ) : ℝ) * higham23GammaRemainder (2 ^ r) u
  | depth + 1, u =>
      higham23StrassenStepMajorant ((2 ^ (r + depth) : ℕ) : ℝ)
        (higham23StrassenMajorantFamily r depth u) u

/-- The remainder after removing the canonical 12/46 first-order
coefficient from the exact nonlinear majorant family. -/
noncomputable def higham23StrassenMajorantRemainder
    (r depth : ℕ) (u : ℝ) : ℝ :=
  higham23StrassenMajorantFamily r depth u -
    higham23StrassenErrorCoefficient r depth * u

/-- The fixed-`FPModel` exact majorant is the variable-roundoff family
evaluated at `fp.u`. -/
theorem higham23_strassenExactMajorant_eq_family
    (fp : FPModel) (r depth : ℕ) (hvalid : gammaValid fp (2 ^ r)) :
    higham23StrassenExactMajorant fp r depth =
      higham23StrassenMajorantFamily r depth fp.u := by
  induction depth with
  | zero =>
      rw [higham23StrassenExactMajorant, higham23StrassenMajorantFamily,
        higham23_gamma_split fp (2 ^ r) hvalid]
      norm_num [Nat.cast_pow]
      have hp : (2 : ℝ) ^ r * (2 : ℝ) ^ r = (4 : ℝ) ^ r := by
        rw [← mul_pow]
        norm_num
      calc
        (2 : ℝ) ^ r *
              ((2 : ℝ) ^ r * fp.u + higham23GammaRemainder (2 ^ r) fp.u) =
            ((2 : ℝ) ^ r * (2 : ℝ) ^ r) * fp.u +
              (2 : ℝ) ^ r * higham23GammaRemainder (2 ^ r) fp.u := by ring
        _ = _ := by rw [hp]
  | succ depth ih =>
      rw [higham23StrassenExactMajorant, higham23StrassenMajorantFamily]
      unfold higham23StrassenStepMajorant
      rw [ih]

/-- The source's second-order term is genuinely `O(u²)` for every fixed
threshold and recursion depth. -/
theorem higham23_strassenMajorantRemainder_isBigO_u_sq (r depth : ℕ) :
    (fun u : ℝ ↦ higham23StrassenMajorantRemainder r depth u)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
  induction depth with
  | zero =>
      have h := (higham23_gammaRemainder_isBigO_u_sq (2 ^ r)).const_mul_left
        (((2 ^ r : ℕ) : ℝ))
      simpa only [higham23StrassenMajorantRemainder,
        higham23StrassenMajorantFamily,
        higham23_strassenErrorCoefficient_zero, add_sub_cancel_left] using h
  | succ depth ih =>
      let e : ℝ → ℝ := higham23StrassenMajorantFamily r depth
      let c := higham23StrassenErrorCoefficient r depth
      let m : ℝ := ((2 ^ (r + depth) : ℕ) : ℝ)
      have hu : (fun u : ℝ ↦ u) =O[𝓝 0] (fun u : ℝ ↦ u) :=
        Asymptotics.isBigO_refl _ _
      have huOne : (fun u : ℝ ↦ u) =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
        continuousAt_id.isBigO_one ℝ
      have huSqOu : (fun u : ℝ ↦ u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u) := by
        simpa only [pow_two, mul_one] using hu.mul huOne
      have hLinear : (fun u : ℝ ↦ c * u) =O[𝓝 0] (fun u : ℝ ↦ u) :=
        hu.const_mul_left c
      have he : e =O[𝓝 0] (fun u : ℝ ↦ u) := by
        have hsum := hLinear.add (ih.trans huSqOu)
        apply hsum.congr'
        · exact Filter.Eventually.of_forall fun u ↦ by
            dsimp [e, c, higham23StrassenMajorantRemainder]
            ring
        · exact Filter.EventuallyEq.rfl
      have hStep := higham23_strassenStepResidual_isBigO_u_sq m e he
      have hPrevious := ih.const_mul_left (12 : ℝ)
      have h := hStep.add hPrevious
      apply h.congr'
      · exact Filter.Eventually.of_forall fun u ↦ by
          dsimp [higham23StrassenMajorantRemainder,
            higham23StrassenMajorantFamily, e, c, m]
          rw [higham23_eq23_16_strassen_coefficient]
          unfold higham23StrassenStepResidual
          norm_num [Nat.cast_pow, pow_add]
          ring
      · exact Filter.EventuallyEq.rfl

/-- Theorem 23.2 with the exact 12/46 recurrence coefficient and its
explicit remainder family. -/
theorem higham23_theorem23_2_strassen_firstOrder
    (fp : FPModel) (r depth : ℕ) (hvalid : gammaValid fp (2 ^ r))
    (A B : Higham23RecursiveMatrix r depth) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : Higham23RecursiveMaxNormLe r depth A a)
    (hB : Higham23RecursiveMaxNormLe r depth B b) :
    Higham23RecursiveErrorLe r depth (A * B)
      (higham23FlStrassenRecursive fp r depth A B)
      ((higham23StrassenErrorCoefficient r depth * fp.u +
          higham23StrassenMajorantRemainder r depth fp.u) * a * b) := by
  have h := higham23_theorem23_2_strassen_exactMajorant fp r hvalid
    depth A B a b ha hb hA hB
  rw [higham23_strassenExactMajorant_eq_family fp r depth hvalid] at h
  have hsplit :
      higham23StrassenMajorantFamily r depth fp.u =
        higham23StrassenErrorCoefficient r depth * fp.u +
          higham23StrassenMajorantRemainder r depth fp.u := by
    unfold higham23StrassenMajorantRemainder
    ring
  rwa [hsplit] at h

/-- Theorem 23.2 with the closed coefficient printed in (23.14); the same
quadratic remainder is retained explicitly. -/
theorem higham23_theorem23_2_strassen_closedCoefficient_firstOrder
    (fp : FPModel) (r depth : ℕ) (hvalid : gammaValid fp (2 ^ r))
    (A B : Higham23RecursiveMatrix r depth) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : Higham23RecursiveMaxNormLe r depth A a)
    (hB : Higham23RecursiveMaxNormLe r depth B b) :
    Higham23RecursiveErrorLe r depth (A * B)
      (higham23FlStrassenRecursive fp r depth A B)
      ((higham23StrassenClosedCoefficient r depth * fp.u +
          higham23StrassenMajorantRemainder r depth fp.u) * a * b) := by
  have h := higham23_theorem23_2_strassen_firstOrder fp r depth hvalid
    A B a b ha hb hA hB
  apply higham23_recursiveErrorLe_mono r depth _ _ h
  have hc := higham23_strassenErrorCoefficient_le r depth
  have hs : 0 ≤ fp.u * a * b :=
    mul_nonneg (mul_nonneg fp.u_nonneg ha) hb
  have hm := mul_le_mul_of_nonneg_right hc hs
  dsimp [higham23StrassenClosedCoefficient] at hm ⊢
  nlinarith

end NumStability
