-- FloatingPointArithmetic.lean

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Analysis.Error

namespace LeanFpAnalysis.FP

/-!
# Higham Chapter 2 Floating-Point Arithmetic

This file records source-facing algebra from Higham, *Accuracy and Stability of
Numerical Algorithms*, Chapter 2.  It starts the finite-format vocabulary for
§2.1 and records algebra around the standard model of §2.2.  The repository's
primitive `FPModel` is the abstract standard model (2.4); it is not yet derived
from the finite format below.

The lemmas here also expose the inverse relative-error form used in Theorem
2.3 and equation (2.5):

`computed = exact / (1 + δ)`.

This is intentionally a source-facing foundation, not a complete IEEE machine
model with exceptions, signaling NaNs, full signed-zero operation behavior,
directed rounding, or underflow.
-/

noncomputable section

/-- IEEE rounding-direction vocabulary from Chapter 2's IEEE discussion.  The
source-facing finite selectors below currently implement only nearest/even as a
real-valued finite policy; the other modes are named so future IEEE semantics
do not hide a directed-rounding assumption. -/
inductive IeeeRoundingMode where
  | nearestEven
  | towardZero
  | towardPositive
  | towardNegative
  deriving DecidableEq, Repr

/-- IEEE exception-flag vocabulary from Chapter 2. -/
inductive IeeeExceptionFlag where
  | invalidOperation
  | divisionByZero
  | overflow
  | underflow
  | inexact
  deriving DecidableEq, Repr

/-- IEEE-facing scalar result vocabulary.  This separates real finite results
from infinities and NaNs, unlike the source-facing finite selectors that always
return real numbers. -/
inductive IeeeValue where
  | finite (x : ℝ)
  | posZero
  | negZero
  | posInf
  | negInf
  | nan

namespace IeeeValue

/-- Predicate that an IEEE-facing value is an ordinary finite real. -/
def isFinite : IeeeValue → Prop
  | finite _ => True
  | posZero => True
  | negZero => True
  | posInf => False
  | negInf => False
  | nan => False

/-- Predicate for the IEEE NaN value.  This does not distinguish quiet from
signaling NaNs or preserve payloads. -/
def isNaN : IeeeValue → Prop
  | nan => True
  | _ => False

/-- Predicate for IEEE infinities. -/
def isInfinite : IeeeValue → Prop
  | posInf => True
  | negInf => True
  | _ => False

/-- Predicate for IEEE zero values.  The ordinary finite value `0` and the
signed zero values all count as zero for invalid-operation examples such as
`0/0` and `0 * infinity`. -/
def isZero : IeeeValue → Prop
  | finite x => x = 0
  | posZero => True
  | negZero => True
  | _ => False

/-- Two IEEE-facing values are the same signed infinity. -/
def sameSignedInfinities (x y : IeeeValue) : Prop :=
  (x = IeeeValue.posInf ∧ y = IeeeValue.posInf) ∨
    (x = IeeeValue.negInf ∧ y = IeeeValue.negInf)

/-- Two IEEE-facing values are opposite signed infinities. -/
def oppositeSignedInfinities (x y : IeeeValue) : Prop :=
  (x = IeeeValue.posInf ∧ y = IeeeValue.negInf) ∨
    (x = IeeeValue.negInf ∧ y = IeeeValue.posInf)

/-- IEEE unordered comparison predicate.  In the modeled quiet/default layer,
unordered means that at least one operand is the modeled NaN value. -/
def ieeeUnordered (x y : IeeeValue) : Prop :=
  x.isNaN ∨ y.isNaN

/-- IEEE equality predicate for the modeled value layer.  NaNs are unequal to
everything, including themselves; signed zeros compare equal. -/
def ieeeEq : IeeeValue → IeeeValue → Prop
  | nan, _ => False
  | _, nan => False
  | finite x, finite y => x = y
  | finite x, posZero => x = 0
  | finite x, negZero => x = 0
  | posZero, finite y => y = 0
  | negZero, finite y => y = 0
  | posZero, posZero => True
  | posZero, negZero => True
  | negZero, posZero => True
  | negZero, negZero => True
  | posInf, posInf => True
  | negInf, negInf => True
  | _, _ => False

/-- IEEE less-than predicate for the modeled value layer.  NaNs are unordered
and hence not less than anything; signed zeros compare equal. -/
def ieeeLt : IeeeValue → IeeeValue → Prop
  | nan, _ => False
  | _, nan => False
  | negInf, negInf => False
  | negInf, _ => True
  | _, negInf => False
  | posInf, _ => False
  | _, posInf => True
  | finite x, finite y => x < y
  | finite x, posZero => x < 0
  | finite x, negZero => x < 0
  | posZero, finite y => 0 < y
  | negZero, finite y => 0 < y
  | posZero, posZero => False
  | posZero, negZero => False
  | negZero, posZero => False
  | negZero, negZero => False

/-- IEEE greater-than predicate, defined by reversing less-than. -/
def ieeeGt (x y : IeeeValue) : Prop :=
  ieeeLt y x

/-- Extract the real payload of a finite IEEE-facing value. -/
def toReal? : IeeeValue → Option ℝ
  | finite x => some x
  | posZero => some 0
  | negZero => some 0
  | posInf => none
  | negInf => none
  | nan => none

theorem finite_isFinite (x : ℝ) :
    (IeeeValue.finite x).isFinite := by
  simp [isFinite]

theorem posZero_isFinite :
    IeeeValue.posZero.isFinite := by
  simp [isFinite]

theorem negZero_isFinite :
    IeeeValue.negZero.isFinite := by
  simp [isFinite]

theorem nan_isNaN :
    IeeeValue.nan.isNaN := by
  simp [isNaN]

theorem posInf_isInfinite :
    IeeeValue.posInf.isInfinite := by
  simp [isInfinite]

theorem negInf_isInfinite :
    IeeeValue.negInf.isInfinite := by
  simp [isInfinite]

theorem finite_zero_isZero :
    (IeeeValue.finite 0).isZero := by
  simp [isZero]

theorem posZero_isZero :
    IeeeValue.posZero.isZero := by
  simp [isZero]

theorem negZero_isZero :
    IeeeValue.negZero.isZero := by
  simp [isZero]

theorem ieeeUnordered_left_nan
    (y : IeeeValue) :
    IeeeValue.ieeeUnordered IeeeValue.nan y := by
  exact Or.inl IeeeValue.nan_isNaN

theorem ieeeUnordered_right_nan
    (x : IeeeValue) :
    IeeeValue.ieeeUnordered x IeeeValue.nan := by
  exact Or.inr IeeeValue.nan_isNaN

theorem ieeeUnordered_nan_self :
    IeeeValue.ieeeUnordered IeeeValue.nan IeeeValue.nan := by
  exact ieeeUnordered_left_nan IeeeValue.nan

theorem not_ieeeEq_left_nan
    (y : IeeeValue) :
    ¬ IeeeValue.ieeeEq IeeeValue.nan y := by
  cases y <;> simp [ieeeEq]

theorem not_ieeeEq_right_nan
    (x : IeeeValue) :
    ¬ IeeeValue.ieeeEq x IeeeValue.nan := by
  cases x <;> simp [ieeeEq]

theorem not_ieeeEq_nan_self :
    ¬ IeeeValue.ieeeEq IeeeValue.nan IeeeValue.nan := by
  simp [ieeeEq]

theorem not_ieeeEq_self_iff_isNaN
    (x : IeeeValue) :
    ¬ IeeeValue.ieeeEq x x ↔ x.isNaN := by
  cases x <;> simp [ieeeEq, isNaN]

theorem not_ieeeLt_left_nan
    (y : IeeeValue) :
    ¬ IeeeValue.ieeeLt IeeeValue.nan y := by
  cases y <;> simp [ieeeLt]

theorem not_ieeeLt_right_nan
    (x : IeeeValue) :
    ¬ IeeeValue.ieeeLt x IeeeValue.nan := by
  cases x <;> simp [ieeeLt]

theorem not_ieeeGt_left_nan
    (y : IeeeValue) :
    ¬ IeeeValue.ieeeGt IeeeValue.nan y :=
  not_ieeeLt_right_nan y

theorem not_ieeeGt_right_nan
    (x : IeeeValue) :
    ¬ IeeeValue.ieeeGt x IeeeValue.nan :=
  not_ieeeLt_left_nan x

theorem ieeeEq_posZero_negZero :
    IeeeValue.ieeeEq IeeeValue.posZero IeeeValue.negZero := by
  simp [ieeeEq]

theorem ieeeEq_negZero_posZero :
    IeeeValue.ieeeEq IeeeValue.negZero IeeeValue.posZero := by
  simp [ieeeEq]

theorem ieeeEq_self_of_not_isNaN
    {x : IeeeValue} (hx : ¬ x.isNaN) :
    x.ieeeEq x := by
  cases x <;> simp [ieeeEq, isNaN] at hx ⊢

theorem not_ieeeLt_self
    (x : IeeeValue) :
    ¬ x.ieeeLt x := by
  cases x <;> simp [ieeeLt]

theorem not_ieeeGt_self
    (x : IeeeValue) :
    ¬ x.ieeeGt x := by
  simpa [ieeeGt] using not_ieeeLt_self x

theorem ieeeComparison_complete
    (x y : IeeeValue) :
    x.ieeeUnordered y ∨ x.ieeeLt y ∨ x.ieeeEq y ∨ x.ieeeGt y := by
  cases x with
  | finite a =>
      cases y with
      | finite b =>
          simpa [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
            using (lt_trichotomy a b)
      | posZero =>
          simpa [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
            using (lt_trichotomy a (0 : ℝ))
      | negZero =>
          simpa [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
            using (lt_trichotomy a (0 : ℝ))
      | posInf => simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
      | negInf => simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
      | nan => simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
  | posZero =>
      cases y with
      | finite b =>
          simpa [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt, eq_comm]
            using (lt_trichotomy (0 : ℝ) b)
      | posZero => simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
      | negZero => simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
      | posInf => simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
      | negInf => simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
      | nan => simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
  | negZero =>
      cases y with
      | finite b =>
          simpa [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt, eq_comm]
            using (lt_trichotomy (0 : ℝ) b)
      | posZero => simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
      | negZero => simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
      | posInf => simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
      | negInf => simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
      | nan => simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
  | posInf =>
      cases y <;> simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
  | negInf =>
      cases y <;> simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]
  | nan =>
      cases y <;> simp [ieeeUnordered, isNaN, ieeeLt, ieeeEq, ieeeGt]

theorem ieeeComparison_ordered_of_not_unordered
    {x y : IeeeValue} (h : ¬ x.ieeeUnordered y) :
    x.ieeeLt y ∨ x.ieeeEq y ∨ x.ieeeGt y := by
  rcases ieeeComparison_complete x y with hunordered | hordered
  · exact False.elim (h hunordered)
  · exact hordered

theorem toReal?_finite (x : ℝ) :
    (IeeeValue.finite x).toReal? = some x := rfl

theorem toReal?_posZero :
    IeeeValue.posZero.toReal? = some 0 := rfl

theorem toReal?_negZero :
    IeeeValue.negZero.toReal? = some 0 := rfl

theorem isFinite_iff_exists {v : IeeeValue} :
    v.isFinite ↔
      (∃ x : ℝ, v = IeeeValue.finite x) ∨
        v = IeeeValue.posZero ∨ v = IeeeValue.negZero := by
  cases v <;> simp [isFinite]

end IeeeValue

/-- IEEE-facing operation result: a value together with the exception flags
raised by the operation.  Flags are a predicate so later semantics can state
sets of flags without committing now to a bit-vector representation. -/
structure IeeeOperationResult where
  value : IeeeValue
  flag : IeeeExceptionFlag → Prop

namespace IeeeOperationResult

/-- The finite, no-exception result associated with a real-valued source
selector. -/
def finiteNoFlags (x : ℝ) : IeeeOperationResult where
  value := IeeeValue.finite x
  flag := fun _ => False

/-- A general no-exception result associated with an IEEE-facing value.  This
is used for non-finite special-value branches that do not raise a flag. -/
def valueNoFlags (value : IeeeValue) : IeeeOperationResult where
  value := value
  flag := fun _ => False

def hasFlag (r : IeeeOperationResult) (flag : IeeeExceptionFlag) : Prop :=
  r.flag flag

def noFlags (r : IeeeOperationResult) : Prop :=
  ∀ flag, ¬ r.hasFlag flag

def isFinite (r : IeeeOperationResult) : Prop :=
  r.value.isFinite

theorem finiteNoFlags_value (x : ℝ) :
    (finiteNoFlags x).value = IeeeValue.finite x := rfl

theorem valueNoFlags_value (value : IeeeValue) :
    (valueNoFlags value).value = value := rfl

theorem finiteNoFlags_noFlags (x : ℝ) :
    (finiteNoFlags x).noFlags := by
  intro flag
  simp [finiteNoFlags, hasFlag]

theorem valueNoFlags_noFlags (value : IeeeValue) :
    (valueNoFlags value).noFlags := by
  intro flag
  simp [valueNoFlags, hasFlag]

theorem not_hasFlag_of_noFlags {r : IeeeOperationResult}
    {flag : IeeeExceptionFlag} (h : r.noFlags) :
    ¬ r.hasFlag flag :=
  h flag

theorem finiteNoFlags_not_hasFlag (x : ℝ) (flag : IeeeExceptionFlag) :
    ¬ (finiteNoFlags x).hasFlag flag :=
  not_hasFlag_of_noFlags (finiteNoFlags_noFlags x)

theorem valueNoFlags_not_hasFlag (value : IeeeValue)
    (flag : IeeeExceptionFlag) :
    ¬ (valueNoFlags value).hasFlag flag :=
  not_hasFlag_of_noFlags (valueNoFlags_noFlags value)

theorem finiteNoFlags_isFinite (x : ℝ) :
    (finiteNoFlags x).isFinite := by
  simp [finiteNoFlags, isFinite, IeeeValue.isFinite]

theorem valueNoFlags_isFinite_iff (value : IeeeValue) :
    (valueNoFlags value).isFinite ↔ value.isFinite := by
  rfl

theorem finiteNoFlags_toReal? (x : ℝ) :
    (finiteNoFlags x).value.toReal? = some x := rfl

theorem valueNoFlags_toReal? (value : IeeeValue) :
    (valueNoFlags value).value.toReal? = value.toReal? := rfl

end IeeeOperationResult

/-- Generic IEEE-facing invalid-operation result: the value is NaN and the
invalid-operation flag is set.  This is the common result predicate used by
operation-specific invalid branches. -/
def ieeeInvalidOperationResult (r : IeeeOperationResult) : Prop :=
  r.value = IeeeValue.nan ∧
    r.hasFlag IeeeExceptionFlag.invalidOperation

/-- Default invalid-operation result, returning NaN and setting exactly the
invalid-operation flag. -/
def ieeeInvalidOperationDefaultResult : IeeeOperationResult where
  value := IeeeValue.nan
  flag := fun flag => flag = IeeeExceptionFlag.invalidOperation

theorem ieeeInvalidOperationDefaultResult_value :
    ieeeInvalidOperationDefaultResult.value = IeeeValue.nan := rfl

theorem ieeeInvalidOperationDefaultResult_hasFlag_iff
    (flag : IeeeExceptionFlag) :
    ieeeInvalidOperationDefaultResult.hasFlag flag ↔
      flag = IeeeExceptionFlag.invalidOperation := by
  rfl

theorem ieeeInvalidOperationDefaultResult_hasInvalidOperationFlag :
    ieeeInvalidOperationDefaultResult.hasFlag
      IeeeExceptionFlag.invalidOperation := by
  simp [ieeeInvalidOperationDefaultResult, IeeeOperationResult.hasFlag]

theorem ieeeInvalidOperationDefaultResult_ieeeInvalidOperationResult :
    ieeeInvalidOperationResult ieeeInvalidOperationDefaultResult := by
  exact ⟨rfl, ieeeInvalidOperationDefaultResult_hasInvalidOperationFlag⟩

theorem ieeeInvalidOperationResult_value
    {r : IeeeOperationResult} (h : ieeeInvalidOperationResult r) :
    r.value = IeeeValue.nan :=
  h.1

theorem ieeeInvalidOperationResult_hasInvalidOperationFlag
    {r : IeeeOperationResult} (h : ieeeInvalidOperationResult r) :
    r.hasFlag IeeeExceptionFlag.invalidOperation :=
  h.2

theorem ieeeInvalidOperationResult_not_noFlags
    {r : IeeeOperationResult} (h : ieeeInvalidOperationResult r) :
    ¬ r.noFlags := by
  intro hno
  exact hno IeeeExceptionFlag.invalidOperation
    (ieeeInvalidOperationResult_hasInvalidOperationFlag h)

theorem ieeeInvalidOperationResult_not_finiteNoFlags {x : ℝ} :
    ¬ ieeeInvalidOperationResult (IeeeOperationResult.finiteNoFlags x) := by
  intro h
  exact IeeeOperationResult.finiteNoFlags_not_hasFlag x
    IeeeExceptionFlag.invalidOperation
    (ieeeInvalidOperationResult_hasInvalidOperationFlag h)

/-- IEEE division-by-zero input predicate for Table 2.2's `finite nonzero/0`
case.  The zero denominator may be either signed zero or the ordinary modeled
finite zero. -/
def ieeeDivisionByZeroInput (x y : IeeeValue) : Prop :=
  x.isFinite ∧ ¬ x.isZero ∧ y.isZero

/-- IEEE division-by-zero result predicate: a finite nonzero value divided by
zero returns an infinity and raises the division-by-zero flag.  The sign of the
infinity is intentionally left to a later full IEEE operation semantics. -/
def ieeeDivisionByZeroResult
    (x y : IeeeValue) (r : IeeeOperationResult) : Prop :=
  ieeeDivisionByZeroInput x y ∧
    r.value.isInfinite ∧ r.hasFlag IeeeExceptionFlag.divisionByZero

/-- Default division-by-zero result with a supplied infinity value and exactly
the division-by-zero flag.  The supplied value lets this predicate layer avoid
committing to a sign-selection rule before full signed-zero operation semantics
is available. -/
def ieeeDivisionByZeroDefaultResult (value : IeeeValue) : IeeeOperationResult where
  value := value
  flag := fun flag => flag = IeeeExceptionFlag.divisionByZero

/-- Signed default infinity for the finite-nonzero divided by signed-zero
cases.  A denominator represented only as `finite 0` has no IEEE sign bit in
this local value model, so the selector returns `none` there. -/
def ieeeDivisionByZeroSignedValue : IeeeValue → IeeeValue → Option IeeeValue
  | IeeeValue.finite x, IeeeValue.posZero =>
      if 0 < x then some IeeeValue.posInf
      else if x < 0 then some IeeeValue.negInf
      else none
  | IeeeValue.finite x, IeeeValue.negZero =>
      if 0 < x then some IeeeValue.negInf
      else if x < 0 then some IeeeValue.posInf
      else none
  | _, _ => none

theorem ieeeDivisionByZeroInput_finite_nonzero
    {x : ℝ} {y : IeeeValue} (hx : x ≠ 0) (hy : y.isZero) :
    ieeeDivisionByZeroInput (IeeeValue.finite x) y := by
  exact ⟨IeeeValue.finite_isFinite x, by simpa [IeeeValue.isZero] using hx, hy⟩

theorem ieeeDivisionByZeroInput_finite_nonzero_posZero
    {x : ℝ} (hx : x ≠ 0) :
    ieeeDivisionByZeroInput (IeeeValue.finite x) IeeeValue.posZero :=
  ieeeDivisionByZeroInput_finite_nonzero hx IeeeValue.posZero_isZero

theorem ieeeDivisionByZeroInput_finite_nonzero_negZero
    {x : ℝ} (hx : x ≠ 0) :
    ieeeDivisionByZeroInput (IeeeValue.finite x) IeeeValue.negZero :=
  ieeeDivisionByZeroInput_finite_nonzero hx IeeeValue.negZero_isZero

theorem ieeeDivisionByZeroInput_finite_nonzero_finite_zero
    {x : ℝ} (hx : x ≠ 0) :
    ieeeDivisionByZeroInput (IeeeValue.finite x) (IeeeValue.finite 0) :=
  ieeeDivisionByZeroInput_finite_nonzero hx IeeeValue.finite_zero_isZero

theorem ieeeDivisionByZeroSignedValue_pos_over_posZero
    {x : ℝ} (hx : 0 < x) :
    ieeeDivisionByZeroSignedValue (IeeeValue.finite x) IeeeValue.posZero =
      some IeeeValue.posInf := by
  simp [ieeeDivisionByZeroSignedValue, hx]

theorem ieeeDivisionByZeroSignedValue_neg_over_posZero
    {x : ℝ} (hx : x < 0) :
    ieeeDivisionByZeroSignedValue (IeeeValue.finite x) IeeeValue.posZero =
      some IeeeValue.negInf := by
  have hnot : ¬ 0 < x := not_lt.mpr (le_of_lt hx)
  simp [ieeeDivisionByZeroSignedValue, hnot, hx]

theorem ieeeDivisionByZeroSignedValue_pos_over_negZero
    {x : ℝ} (hx : 0 < x) :
    ieeeDivisionByZeroSignedValue (IeeeValue.finite x) IeeeValue.negZero =
      some IeeeValue.negInf := by
  simp [ieeeDivisionByZeroSignedValue, hx]

theorem ieeeDivisionByZeroSignedValue_neg_over_negZero
    {x : ℝ} (hx : x < 0) :
    ieeeDivisionByZeroSignedValue (IeeeValue.finite x) IeeeValue.negZero =
      some IeeeValue.posInf := by
  have hnot : ¬ 0 < x := not_lt.mpr (le_of_lt hx)
  simp [ieeeDivisionByZeroSignedValue, hnot, hx]

theorem ieeeDivisionByZeroSignedValue_none_finite_zero
    (x : ℝ) :
    ieeeDivisionByZeroSignedValue (IeeeValue.finite x) (IeeeValue.finite 0) =
      none := by
  simp [ieeeDivisionByZeroSignedValue]

/-- Repository default infinity selector for the ordinary modeled `finite 0`
denominator branch.  Since `finite 0` carries no signed-zero bit in
`IeeeValue`, this records the signless finite-zero convention separately from
the true signed-zero selectors above. -/
def ieeeDivisionByZeroFiniteZeroDefaultValue (x : ℝ) : IeeeValue :=
  if 0 < x then IeeeValue.posInf else IeeeValue.negInf

theorem ieeeDivisionByZeroFiniteZeroDefaultValue_pos
    {x : ℝ} (hx : 0 < x) :
    ieeeDivisionByZeroFiniteZeroDefaultValue x = IeeeValue.posInf := by
  simp [ieeeDivisionByZeroFiniteZeroDefaultValue, hx]

theorem ieeeDivisionByZeroFiniteZeroDefaultValue_neg
    {x : ℝ} (hx : x < 0) :
    ieeeDivisionByZeroFiniteZeroDefaultValue x = IeeeValue.negInf := by
  have hnot : ¬ 0 < x := not_lt.mpr (le_of_lt hx)
  simp [ieeeDivisionByZeroFiniteZeroDefaultValue, hnot]

theorem ieeeDivisionByZeroFiniteZeroDefaultValue_isInfinite
    (x : ℝ) :
    (ieeeDivisionByZeroFiniteZeroDefaultValue x).isInfinite := by
  by_cases hpos : 0 < x
  · simp [ieeeDivisionByZeroFiniteZeroDefaultValue, hpos, IeeeValue.isInfinite]
  · simp [ieeeDivisionByZeroFiniteZeroDefaultValue, hpos, IeeeValue.isInfinite]

theorem ieeeDivisionByZeroDefaultResult_value
    (value : IeeeValue) :
    (ieeeDivisionByZeroDefaultResult value).value = value := rfl

theorem ieeeDivisionByZeroDefaultResult_hasFlag_iff
    (value : IeeeValue) (flag : IeeeExceptionFlag) :
    (ieeeDivisionByZeroDefaultResult value).hasFlag flag ↔
      flag = IeeeExceptionFlag.divisionByZero := by
  rfl

theorem ieeeDivisionByZeroDefaultResult_hasDivisionByZeroFlag
    (value : IeeeValue) :
    (ieeeDivisionByZeroDefaultResult value).hasFlag
      IeeeExceptionFlag.divisionByZero := by
  simp [ieeeDivisionByZeroDefaultResult, IeeeOperationResult.hasFlag]

theorem ieeeDivisionByZeroDefaultResult_ieeeDivisionByZeroResult
    {x y value : IeeeValue}
    (hinput : ieeeDivisionByZeroInput x y) (hvalue : value.isInfinite) :
    ieeeDivisionByZeroResult x y
      (ieeeDivisionByZeroDefaultResult value) := by
  exact
    ⟨hinput, by simpa [ieeeDivisionByZeroDefaultResult] using hvalue,
      ieeeDivisionByZeroDefaultResult_hasDivisionByZeroFlag value⟩

theorem ieeeDivisionByZeroDefaultResult_posInf_ieeeDivisionByZeroResult
    {x y : IeeeValue} (hinput : ieeeDivisionByZeroInput x y) :
    ieeeDivisionByZeroResult x y
      (ieeeDivisionByZeroDefaultResult IeeeValue.posInf) :=
  ieeeDivisionByZeroDefaultResult_ieeeDivisionByZeroResult
    hinput IeeeValue.posInf_isInfinite

theorem ieeeDivisionByZeroDefaultResult_negInf_ieeeDivisionByZeroResult
    {x y : IeeeValue} (hinput : ieeeDivisionByZeroInput x y) :
    ieeeDivisionByZeroResult x y
      (ieeeDivisionByZeroDefaultResult IeeeValue.negInf) :=
  ieeeDivisionByZeroDefaultResult_ieeeDivisionByZeroResult
    hinput IeeeValue.negInf_isInfinite

theorem ieeeDivisionByZeroDefaultResult_pos_over_posZero
    {x : ℝ} (hx : 0 < x) :
    ieeeDivisionByZeroResult (IeeeValue.finite x) IeeeValue.posZero
      (ieeeDivisionByZeroDefaultResult IeeeValue.posInf) :=
  ieeeDivisionByZeroDefaultResult_posInf_ieeeDivisionByZeroResult
    (ieeeDivisionByZeroInput_finite_nonzero_posZero (ne_of_gt hx))

theorem ieeeDivisionByZeroDefaultResult_neg_over_posZero
    {x : ℝ} (hx : x < 0) :
    ieeeDivisionByZeroResult (IeeeValue.finite x) IeeeValue.posZero
      (ieeeDivisionByZeroDefaultResult IeeeValue.negInf) :=
  ieeeDivisionByZeroDefaultResult_negInf_ieeeDivisionByZeroResult
    (ieeeDivisionByZeroInput_finite_nonzero_posZero (ne_of_lt hx))

theorem ieeeDivisionByZeroDefaultResult_pos_over_negZero
    {x : ℝ} (hx : 0 < x) :
    ieeeDivisionByZeroResult (IeeeValue.finite x) IeeeValue.negZero
      (ieeeDivisionByZeroDefaultResult IeeeValue.negInf) :=
  ieeeDivisionByZeroDefaultResult_negInf_ieeeDivisionByZeroResult
    (ieeeDivisionByZeroInput_finite_nonzero_negZero (ne_of_gt hx))

theorem ieeeDivisionByZeroDefaultResult_neg_over_negZero
    {x : ℝ} (hx : x < 0) :
    ieeeDivisionByZeroResult (IeeeValue.finite x) IeeeValue.negZero
      (ieeeDivisionByZeroDefaultResult IeeeValue.posInf) :=
  ieeeDivisionByZeroDefaultResult_posInf_ieeeDivisionByZeroResult
    (ieeeDivisionByZeroInput_finite_nonzero_negZero (ne_of_lt hx))

theorem ieeeDivisionByZeroDefaultResult_finite_zero
    {x : ℝ} (hx : x ≠ 0) :
    ieeeDivisionByZeroResult (IeeeValue.finite x) (IeeeValue.finite 0)
      (ieeeDivisionByZeroDefaultResult
        (ieeeDivisionByZeroFiniteZeroDefaultValue x)) :=
  ieeeDivisionByZeroDefaultResult_ieeeDivisionByZeroResult
    (ieeeDivisionByZeroInput_finite_nonzero_finite_zero hx)
    (ieeeDivisionByZeroFiniteZeroDefaultValue_isInfinite x)

theorem ieeeDivisionByZeroDefaultResult_pos_over_finite_zero
    {x : ℝ} (hx : 0 < x) :
    ieeeDivisionByZeroResult (IeeeValue.finite x) (IeeeValue.finite 0)
      (ieeeDivisionByZeroDefaultResult IeeeValue.posInf) := by
  rw [← ieeeDivisionByZeroFiniteZeroDefaultValue_pos hx]
  exact ieeeDivisionByZeroDefaultResult_finite_zero (ne_of_gt hx)

theorem ieeeDivisionByZeroDefaultResult_neg_over_finite_zero
    {x : ℝ} (hx : x < 0) :
    ieeeDivisionByZeroResult (IeeeValue.finite x) (IeeeValue.finite 0)
      (ieeeDivisionByZeroDefaultResult IeeeValue.negInf) := by
  rw [← ieeeDivisionByZeroFiniteZeroDefaultValue_neg hx]
  exact ieeeDivisionByZeroDefaultResult_finite_zero (ne_of_lt hx)

theorem ieeeDivisionByZeroResult_input
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeeDivisionByZeroResult x y r) :
    ieeeDivisionByZeroInput x y :=
  h.1

theorem ieeeDivisionByZeroResult_value_isInfinite
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeeDivisionByZeroResult x y r) :
    r.value.isInfinite :=
  h.2.1

theorem ieeeDivisionByZeroResult_hasDivisionByZeroFlag
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeeDivisionByZeroResult x y r) :
    r.hasFlag IeeeExceptionFlag.divisionByZero :=
  h.2.2

theorem ieeeDivisionByZeroResult_not_noFlags
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeeDivisionByZeroResult x y r) :
    ¬ r.noFlags := by
  intro hno
  exact hno IeeeExceptionFlag.divisionByZero
    (ieeeDivisionByZeroResult_hasDivisionByZeroFlag h)

theorem ieeeDivisionByZeroResult_not_finiteNoFlags
    {x y : IeeeValue} {z : ℝ} :
    ¬ ieeeDivisionByZeroResult x y (IeeeOperationResult.finiteNoFlags z) := by
  intro h
  exact IeeeOperationResult.finiteNoFlags_not_hasFlag z
    IeeeExceptionFlag.divisionByZero
    (ieeeDivisionByZeroResult_hasDivisionByZeroFlag h)

/-- IEEE square-root invalid-operation branch for negative real inputs. -/
def ieeeSqrtInvalidResult (x : ℝ) (r : IeeeOperationResult) : Prop :=
  x < 0 ∧ ieeeInvalidOperationResult r

/-- Default square-root invalid-operation result.  The input is retained in the
API so the constructor lines up with `ieeeSqrtInvalidResult`. -/
def ieeeSqrtInvalidDefaultResult (_x : ℝ) : IeeeOperationResult :=
  ieeeInvalidOperationDefaultResult

theorem ieeeSqrtInvalidDefaultResult_ieeeSqrtInvalidResult
    {x : ℝ} (hx : x < 0) :
    ieeeSqrtInvalidResult x (ieeeSqrtInvalidDefaultResult x) := by
  exact ⟨hx, ieeeInvalidOperationDefaultResult_ieeeInvalidOperationResult⟩

theorem ieeeSqrtInvalidResult_input_neg
    {x : ℝ} {r : IeeeOperationResult}
    (h : ieeeSqrtInvalidResult x r) :
    x < 0 :=
  h.1

theorem ieeeSqrtInvalidResult_ieeeInvalidOperationResult
    {x : ℝ} {r : IeeeOperationResult}
    (h : ieeeSqrtInvalidResult x r) :
    ieeeInvalidOperationResult r :=
  h.2

theorem ieeeSqrtInvalidResult_value
    {x : ℝ} {r : IeeeOperationResult}
    (h : ieeeSqrtInvalidResult x r) :
    r.value = IeeeValue.nan :=
  ieeeInvalidOperationResult_value h.2

theorem ieeeSqrtInvalidResult_hasInvalidOperationFlag
    {x : ℝ} {r : IeeeOperationResult}
    (h : ieeeSqrtInvalidResult x r) :
    r.hasFlag IeeeExceptionFlag.invalidOperation :=
  ieeeInvalidOperationResult_hasInvalidOperationFlag h.2

/-- IEEE-facing square-root special-value predicate for non-finite inputs.
This records the quiet/default branches modeled here: NaN propagates to NaN
with no flags, positive infinity maps to positive infinity with no flags, and
negative infinity raises invalid operation and returns NaN.  Signaling NaNs,
payloads, traps, and signed-zero behavior remain outside this predicate. -/
def ieeeSqrtSpecialValueResult
    (v : IeeeValue) (r : IeeeOperationResult) : Prop :=
  match v with
  | IeeeValue.finite _ => False
  | IeeeValue.posZero => False
  | IeeeValue.negZero => False
  | IeeeValue.posInf => r.value = IeeeValue.posInf ∧ r.noFlags
  | IeeeValue.negInf => ieeeInvalidOperationResult r
  | IeeeValue.nan => r.value = IeeeValue.nan ∧ r.noFlags

theorem ieeeSqrtSpecialValueResult_nan_valueNoFlags :
    ieeeSqrtSpecialValueResult IeeeValue.nan
      (IeeeOperationResult.valueNoFlags IeeeValue.nan) := by
  exact ⟨rfl, IeeeOperationResult.valueNoFlags_noFlags IeeeValue.nan⟩

theorem ieeeSqrtSpecialValueResult_posInf_valueNoFlags :
    ieeeSqrtSpecialValueResult IeeeValue.posInf
      (IeeeOperationResult.valueNoFlags IeeeValue.posInf) := by
  exact ⟨rfl, IeeeOperationResult.valueNoFlags_noFlags IeeeValue.posInf⟩

theorem ieeeSqrtSpecialValueResult_negInf_invalid :
    ieeeSqrtSpecialValueResult IeeeValue.negInf
      ieeeInvalidOperationDefaultResult :=
  ieeeInvalidOperationDefaultResult_ieeeInvalidOperationResult

theorem ieeeSqrtSpecialValueResult_value_nan
    {r : IeeeOperationResult}
    (h : ieeeSqrtSpecialValueResult IeeeValue.nan r) :
    r.value = IeeeValue.nan :=
  h.1

theorem ieeeSqrtSpecialValueResult_noFlags_nan
    {r : IeeeOperationResult}
    (h : ieeeSqrtSpecialValueResult IeeeValue.nan r) :
    r.noFlags :=
  h.2

theorem ieeeSqrtSpecialValueResult_value_posInf
    {r : IeeeOperationResult}
    (h : ieeeSqrtSpecialValueResult IeeeValue.posInf r) :
    r.value = IeeeValue.posInf :=
  h.1

theorem ieeeSqrtSpecialValueResult_noFlags_posInf
    {r : IeeeOperationResult}
    (h : ieeeSqrtSpecialValueResult IeeeValue.posInf r) :
    r.noFlags :=
  h.2

theorem ieeeSqrtSpecialValueResult_negInf_ieeeInvalidOperationResult
    {r : IeeeOperationResult}
    (h : ieeeSqrtSpecialValueResult IeeeValue.negInf r) :
    ieeeInvalidOperationResult r :=
  h

/-- IEEE square-root signed-zero predicate: square root preserves the sign of
zero and raises no flags.  The ordinary real payload `finite 0` remains the
source-facing real zero; IEEE signed zeros use `posZero` and `negZero`. -/
def ieeeSqrtSignedZeroResult
    (v : IeeeValue) (r : IeeeOperationResult) : Prop :=
  match v with
  | IeeeValue.posZero => r.value = IeeeValue.posZero ∧ r.noFlags
  | IeeeValue.negZero => r.value = IeeeValue.negZero ∧ r.noFlags
  | _ => False

theorem ieeeSqrtSignedZeroResult_posZero_valueNoFlags :
    ieeeSqrtSignedZeroResult IeeeValue.posZero
      (IeeeOperationResult.valueNoFlags IeeeValue.posZero) := by
  exact ⟨rfl, IeeeOperationResult.valueNoFlags_noFlags IeeeValue.posZero⟩

theorem ieeeSqrtSignedZeroResult_negZero_valueNoFlags :
    ieeeSqrtSignedZeroResult IeeeValue.negZero
      (IeeeOperationResult.valueNoFlags IeeeValue.negZero) := by
  exact ⟨rfl, IeeeOperationResult.valueNoFlags_noFlags IeeeValue.negZero⟩

theorem ieeeSqrtSignedZeroResult_value_posZero
    {r : IeeeOperationResult}
    (h : ieeeSqrtSignedZeroResult IeeeValue.posZero r) :
    r.value = IeeeValue.posZero :=
  h.1

theorem ieeeSqrtSignedZeroResult_noFlags_posZero
    {r : IeeeOperationResult}
    (h : ieeeSqrtSignedZeroResult IeeeValue.posZero r) :
    r.noFlags :=
  h.2

theorem ieeeSqrtSignedZeroResult_value_negZero
    {r : IeeeOperationResult}
    (h : ieeeSqrtSignedZeroResult IeeeValue.negZero r) :
    r.value = IeeeValue.negZero :=
  h.1

theorem ieeeSqrtSignedZeroResult_noFlags_negZero
    {r : IeeeOperationResult}
    (h : ieeeSqrtSignedZeroResult IeeeValue.negZero r) :
    r.noFlags :=
  h.2

/-- IEEE quiet/default NaN propagation for primitive binary operations:
if either input is the modeled NaN value, the result is NaN with no flags.
Signaling NaNs and payload propagation are intentionally not modeled here. -/
def ieeeQuietNaNPropagationResult
    (x y : IeeeValue) (r : IeeeOperationResult) : Prop :=
  (x.isNaN ∨ y.isNaN) ∧ r.value = IeeeValue.nan ∧ r.noFlags

theorem ieeeQuietNaNPropagationResult_left_nan
    (y : IeeeValue) :
    ieeeQuietNaNPropagationResult IeeeValue.nan y
      (IeeeOperationResult.valueNoFlags IeeeValue.nan) := by
  exact
    ⟨Or.inl IeeeValue.nan_isNaN, rfl,
      IeeeOperationResult.valueNoFlags_noFlags IeeeValue.nan⟩

theorem ieeeQuietNaNPropagationResult_right_nan
    (x : IeeeValue) :
    ieeeQuietNaNPropagationResult x IeeeValue.nan
      (IeeeOperationResult.valueNoFlags IeeeValue.nan) := by
  exact
    ⟨Or.inr IeeeValue.nan_isNaN, rfl,
      IeeeOperationResult.valueNoFlags_noFlags IeeeValue.nan⟩

theorem ieeeQuietNaNPropagationResult_value
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeeQuietNaNPropagationResult x y r) :
    r.value = IeeeValue.nan :=
  h.2.1

theorem ieeeQuietNaNPropagationResult_noFlags
    {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeeQuietNaNPropagationResult x y r) :
    r.noFlags :=
  h.2.2

/-- Source-facing predicate for the first primitive IEEE invalid-operation
special-value inputs described in Chapter 2: `0/0`, `0 * infinity`,
`infinity * 0`, `infinity / infinity`, and the usual indeterminate
infinity-plus/minus-infinity cases. -/
def ieeePrimitiveInvalidOperationInput
    (op : BasicOp) (x y : IeeeValue) : Prop :=
  match op with
  | BasicOp.add => IeeeValue.oppositeSignedInfinities x y
  | BasicOp.sub => IeeeValue.sameSignedInfinities x y
  | BasicOp.mul =>
      (x.isZero ∧ y.isInfinite) ∨ (x.isInfinite ∧ y.isZero)
  | BasicOp.div =>
      (x.isZero ∧ y.isZero) ∨ (x.isInfinite ∧ y.isInfinite)

/-- IEEE primitive-operation invalid-operation branch: the input pair is one
of the modeled invalid special-value combinations and the result is a NaN with
the invalid-operation flag. -/
def ieeePrimitiveInvalidOperationResult
    (op : BasicOp) (x y : IeeeValue)
    (r : IeeeOperationResult) : Prop :=
  ieeePrimitiveInvalidOperationInput op x y ∧ ieeeInvalidOperationResult r

theorem ieeePrimitiveInvalidOperationInput_div_zero_zero
    {x y : IeeeValue} (hx : x.isZero) (hy : y.isZero) :
    ieeePrimitiveInvalidOperationInput BasicOp.div x y := by
  change (x.isZero ∧ y.isZero) ∨ (x.isInfinite ∧ y.isInfinite)
  exact Or.inl ⟨hx, hy⟩

theorem ieeePrimitiveInvalidOperationInput_div_inf_inf
    {x y : IeeeValue} (hx : x.isInfinite) (hy : y.isInfinite) :
    ieeePrimitiveInvalidOperationInput BasicOp.div x y := by
  change (x.isZero ∧ y.isZero) ∨ (x.isInfinite ∧ y.isInfinite)
  exact Or.inr ⟨hx, hy⟩

theorem ieeePrimitiveInvalidOperationInput_mul_zero_inf
    {x y : IeeeValue} (hx : x.isZero) (hy : y.isInfinite) :
    ieeePrimitiveInvalidOperationInput BasicOp.mul x y := by
  change (x.isZero ∧ y.isInfinite) ∨ (x.isInfinite ∧ y.isZero)
  exact Or.inl ⟨hx, hy⟩

theorem ieeePrimitiveInvalidOperationInput_mul_inf_zero
    {x y : IeeeValue} (hx : x.isInfinite) (hy : y.isZero) :
    ieeePrimitiveInvalidOperationInput BasicOp.mul x y := by
  change (x.isZero ∧ y.isInfinite) ∨ (x.isInfinite ∧ y.isZero)
  exact Or.inr ⟨hx, hy⟩

theorem ieeePrimitiveInvalidOperationInput_add_posInf_negInf :
    ieeePrimitiveInvalidOperationInput BasicOp.add
      IeeeValue.posInf IeeeValue.negInf := by
  change IeeeValue.oppositeSignedInfinities IeeeValue.posInf IeeeValue.negInf
  exact Or.inl ⟨rfl, rfl⟩

theorem ieeePrimitiveInvalidOperationInput_add_negInf_posInf :
    ieeePrimitiveInvalidOperationInput BasicOp.add
      IeeeValue.negInf IeeeValue.posInf := by
  change IeeeValue.oppositeSignedInfinities IeeeValue.negInf IeeeValue.posInf
  exact Or.inr ⟨rfl, rfl⟩

theorem ieeePrimitiveInvalidOperationInput_sub_posInf_posInf :
    ieeePrimitiveInvalidOperationInput BasicOp.sub
      IeeeValue.posInf IeeeValue.posInf := by
  change IeeeValue.sameSignedInfinities IeeeValue.posInf IeeeValue.posInf
  exact Or.inl ⟨rfl, rfl⟩

theorem ieeePrimitiveInvalidOperationInput_sub_negInf_negInf :
    ieeePrimitiveInvalidOperationInput BasicOp.sub
      IeeeValue.negInf IeeeValue.negInf := by
  change IeeeValue.sameSignedInfinities IeeeValue.negInf IeeeValue.negInf
  exact Or.inr ⟨rfl, rfl⟩

theorem ieeePrimitiveInvalidOperationDefaultResult_ieeePrimitiveInvalidOperationResult
    {op : BasicOp} {x y : IeeeValue}
    (hinput : ieeePrimitiveInvalidOperationInput op x y) :
    ieeePrimitiveInvalidOperationResult op x y
      ieeeInvalidOperationDefaultResult := by
  exact ⟨hinput, ieeeInvalidOperationDefaultResult_ieeeInvalidOperationResult⟩

theorem ieeePrimitiveInvalidOperationResult_input
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveInvalidOperationResult op x y r) :
    ieeePrimitiveInvalidOperationInput op x y :=
  h.1

theorem ieeePrimitiveInvalidOperationResult_ieeeInvalidOperationResult
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveInvalidOperationResult op x y r) :
    ieeeInvalidOperationResult r :=
  h.2

theorem ieeePrimitiveInvalidOperationResult_value
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveInvalidOperationResult op x y r) :
    r.value = IeeeValue.nan :=
  ieeeInvalidOperationResult_value h.2

theorem ieeePrimitiveInvalidOperationResult_hasInvalidOperationFlag
    {op : BasicOp} {x y : IeeeValue} {r : IeeeOperationResult}
    (h : ieeePrimitiveInvalidOperationResult op x y r) :
    r.hasFlag IeeeExceptionFlag.invalidOperation :=
  ieeeInvalidOperationResult_hasInvalidOperationFlag h.2

/-- Combined primitive-operation special-value result predicate for the first
IEEE branches modeled here: quiet NaN propagation and invalid-operation
special-value inputs. -/
def ieeePrimitiveSpecialValueResult
    (op : BasicOp) (x y : IeeeValue)
    (r : IeeeOperationResult) : Prop :=
  ieeeQuietNaNPropagationResult x y r ∨
    ieeePrimitiveInvalidOperationResult op x y r

theorem ieeePrimitiveSpecialValueResult_left_nan
    (op : BasicOp) (y : IeeeValue) :
    ieeePrimitiveSpecialValueResult op IeeeValue.nan y
      (IeeeOperationResult.valueNoFlags IeeeValue.nan) := by
  exact Or.inl (ieeeQuietNaNPropagationResult_left_nan y)

theorem ieeePrimitiveSpecialValueResult_right_nan
    (op : BasicOp) (x : IeeeValue) :
    ieeePrimitiveSpecialValueResult op x IeeeValue.nan
      (IeeeOperationResult.valueNoFlags IeeeValue.nan) := by
  exact Or.inl (ieeeQuietNaNPropagationResult_right_nan x)

theorem ieeePrimitiveSpecialValueResult_invalid_default
    {op : BasicOp} {x y : IeeeValue}
    (hinput : ieeePrimitiveInvalidOperationInput op x y) :
    ieeePrimitiveSpecialValueResult op x y
      ieeeInvalidOperationDefaultResult := by
  exact Or.inr
    (ieeePrimitiveInvalidOperationDefaultResult_ieeePrimitiveInvalidOperationResult
      hinput)

/-- Higham Chapter 2 finite floating-point format parameters.  We use inclusive
exponent endpoints, matching the displayed source line `emin <= e <= emax`. -/
structure FloatingPointFormat where
  /-- Base, or radix. -/
  beta : ℕ
  /-- Precision, in base-`beta` digits. -/
  t : ℕ
  /-- Minimum normalized exponent. -/
  emin : ℤ
  /-- Maximum normalized exponent. -/
  emax : ℤ
  beta_ge_two : 2 ≤ beta
  t_pos : 0 < t
  emin_le_emax : emin ≤ emax

namespace FloatingPointFormat

/-- The base as a real number. -/
def betaR (fmt : FloatingPointFormat) : ℝ :=
  (fmt.beta : ℝ)

/-- Higham's machine epsilon: the gap from `1.0` to the next larger normalized
number, `beta^(1-t)`. -/
def machineEpsilon (fmt : FloatingPointFormat) : ℝ :=
  fmt.betaR ^ (1 - (fmt.t : ℤ))

/-- Higham's unit roundoff `u = (1/2) beta^(1-t)`. -/
def unitRoundoff (fmt : FloatingPointFormat) : ℝ :=
  (1 / 2 : ℝ) * fmt.machineEpsilon

/-- Higham's unit in the last place for a normalized value with exponent `e`:
`ulp(+- beta^e * .d_1...d_t) = beta^(e-t)`. -/
def ulpAtExponent (fmt : FloatingPointFormat) (e : ℤ) : ℝ :=
  fmt.betaR ^ (e - (fmt.t : ℤ))

/-- Higham's IEEE single-precision parameter tuple: `beta = 2`, `t = 24`,
`emin = -125`, `emax = 128`.  This records the finite-format parameters only;
it is not a full IEEE semantics with signed zeros, infinities, NaNs, exception
flags, or a concrete tie rule. -/
def ieeeSingleFormat : FloatingPointFormat where
  beta := 2
  t := 24
  emin := -125
  emax := 128
  beta_ge_two := by norm_num
  t_pos := by norm_num
  emin_le_emax := by norm_num

/-- Higham's IEEE double-precision parameter tuple: `beta = 2`, `t = 53`,
`emin = -1021`, `emax = 1024`.  This records the finite-format parameters only;
it is not a full IEEE semantics with signed zeros, infinities, NaNs, exception
flags, or a concrete tie rule. -/
def ieeeDoubleFormat : FloatingPointFormat where
  beta := 2
  t := 53
  emin := -1021
  emax := 1024
  beta_ge_two := by norm_num
  t_pos := by norm_num
  emin_le_emax := by norm_num

theorem ieeeSingleFormat_params :
    ieeeSingleFormat.beta = 2 ∧ ieeeSingleFormat.t = 24 ∧
      ieeeSingleFormat.emin = -125 ∧ ieeeSingleFormat.emax = 128 := by
  norm_num [ieeeSingleFormat]

theorem ieeeDoubleFormat_params :
    ieeeDoubleFormat.beta = 2 ∧ ieeeDoubleFormat.t = 53 ∧
      ieeeDoubleFormat.emin = -1021 ∧ ieeeDoubleFormat.emax = 1024 := by
  norm_num [ieeeDoubleFormat]

theorem ieeeSingleFormat_machineEpsilon :
    ieeeSingleFormat.machineEpsilon = (2 : ℝ) ^ (-23 : ℤ) := by
  norm_num [ieeeSingleFormat, machineEpsilon, betaR]

theorem ieeeSingleFormat_unitRoundoff :
    ieeeSingleFormat.unitRoundoff = (2 : ℝ) ^ (-24 : ℤ) := by
  rw [unitRoundoff, ieeeSingleFormat_machineEpsilon]
  norm_num [zpow_neg]

theorem ieeeDoubleFormat_machineEpsilon :
    ieeeDoubleFormat.machineEpsilon = (2 : ℝ) ^ (-52 : ℤ) := by
  norm_num [ieeeDoubleFormat, machineEpsilon, betaR]

theorem ieeeDoubleFormat_unitRoundoff :
    ieeeDoubleFormat.unitRoundoff = (2 : ℝ) ^ (-53 : ℤ) := by
  rw [unitRoundoff, ieeeDoubleFormat_machineEpsilon]
  norm_num [zpow_neg]

theorem ieeeSingleFormat_ulpAtExponent (e : ℤ) :
    ieeeSingleFormat.ulpAtExponent e = (2 : ℝ) ^ (e - 24) := by
  norm_num [ulpAtExponent, ieeeSingleFormat, betaR]

theorem ieeeDoubleFormat_ulpAtExponent (e : ℤ) :
    ieeeDoubleFormat.ulpAtExponent e = (2 : ℝ) ^ (e - 53) := by
  norm_num [ulpAtExponent, ieeeDoubleFormat, betaR]

/-- Higham's note on MATLAB's permanent variable `eps` for IEEE double
arithmetic: it is the machine epsilon, not the unit roundoff. -/
def matlabIeeeDoubleEps : ℝ :=
  ieeeDoubleFormat.machineEpsilon

/-- Higham's Fortran `EPSILON` convention for a real kind represented by
`fmt`: it returns the kind's machine epsilon. -/
def fortranEpsilon (fmt : FloatingPointFormat) : ℝ :=
  fmt.machineEpsilon

theorem matlabIeeeDoubleEps_eq_ieeeDoubleFormat_machineEpsilon :
    matlabIeeeDoubleEps = ieeeDoubleFormat.machineEpsilon :=
  rfl

theorem matlabIeeeDoubleEps_eq_two_zpow_neg52 :
    matlabIeeeDoubleEps = (2 : ℝ) ^ (-52 : ℤ) := by
  simpa [matlabIeeeDoubleEps] using ieeeDoubleFormat_machineEpsilon

theorem matlabIeeeDoubleEps_eq_two_mul_ieeeDoubleFormat_unitRoundoff :
    matlabIeeeDoubleEps = 2 * ieeeDoubleFormat.unitRoundoff := by
  rw [matlabIeeeDoubleEps, unitRoundoff]
  ring

theorem fortranEpsilon_eq_machineEpsilon (fmt : FloatingPointFormat) :
    fmt.fortranEpsilon = fmt.machineEpsilon :=
  rfl

theorem fortranEpsilon_eq_two_mul_unitRoundoff
    (fmt : FloatingPointFormat) :
    fmt.fortranEpsilon = 2 * fmt.unitRoundoff := by
  rw [fortranEpsilon, unitRoundoff]
  ring

theorem ieeeSingleFormat_fortranEpsilon :
    ieeeSingleFormat.fortranEpsilon = (2 : ℝ) ^ (-23 : ℤ) := by
  simpa [fortranEpsilon] using ieeeSingleFormat_machineEpsilon

theorem ieeeDoubleFormat_fortranEpsilon :
    ieeeDoubleFormat.fortranEpsilon = (2 : ℝ) ^ (-52 : ℤ) := by
  simpa [fortranEpsilon] using ieeeDoubleFormat_machineEpsilon

theorem matlabIeeeDoubleEps_eq_ieeeDoubleFormat_fortranEpsilon :
    matlabIeeeDoubleEps = ieeeDoubleFormat.fortranEpsilon :=
  rfl

/-- The smallest positive normalized magnitude, `beta^(emin-1)`. -/
def minNormalMagnitude (fmt : FloatingPointFormat) : ℝ :=
  fmt.betaR ^ (fmt.emin - 1)

/-- The smallest positive subnormal magnitude, `beta^(emin-t)`. -/
def minSubnormalMagnitude (fmt : FloatingPointFormat) : ℝ :=
  fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))

/-- Higham Chapter 2 equation (2.8), gradual-underflow additive-error bound
`u * alpha`, where `alpha = beta^(emin-1)` is the smallest positive normalized
floating-point magnitude. -/
def gradualUnderflowEtaBound (fmt : FloatingPointFormat) : ℝ :=
  fmt.unitRoundoff * fmt.minNormalMagnitude

/-- Higham Chapter 2 equation (2.8), flush-to-zero additive-error bound
`alpha`, the smallest positive normalized floating-point magnitude. -/
def flushToZeroEtaBound (fmt : FloatingPointFormat) : ℝ :=
  fmt.minNormalMagnitude

/-- The largest finite normalized magnitude,
`beta^emax * (1 - beta^(-t))`. -/
def maxFiniteMagnitude (fmt : FloatingPointFormat) : ℝ :=
  fmt.betaR ^ fmt.emax * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))

/-- Source-facing finite normal range, excluding the subnormal/zero region but
including both finite normalized endpoints by magnitude. -/
def finiteNormalRange (fmt : FloatingPointFormat) (x : ℝ) : Prop :=
  fmt.minNormalMagnitude ≤ |x| ∧ |x| ≤ fmt.maxFiniteMagnitude

/-- Source-facing underflow range: magnitudes below the smallest positive
normalized value.  This includes zero and subnormal magnitudes; arithmetic
semantics and exception behavior are modeled separately. -/
def finiteUnderflowRange (fmt : FloatingPointFormat) (x : ℝ) : Prop :=
  |x| < fmt.minNormalMagnitude

/-- Source-facing overflow range: magnitudes above the largest finite normalized
value.  This is a range predicate, not yet an operational overflow semantics. -/
def finiteOverflowRange (fmt : FloatingPointFormat) (x : ℝ) : Prop :=
  fmt.maxFiniteMagnitude < |x|

theorem finiteNormalRange_neg_iff (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.finiteNormalRange (-x) ↔ fmt.finiteNormalRange x := by
  simp [finiteNormalRange]

theorem finiteUnderflowRange_neg_iff (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.finiteUnderflowRange (-x) ↔ fmt.finiteUnderflowRange x := by
  simp [finiteUnderflowRange]

theorem finiteOverflowRange_neg_iff (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.finiteOverflowRange (-x) ↔ fmt.finiteOverflowRange x := by
  simp [finiteOverflowRange]

/-- A finite-normal value is not in the source-facing underflow range. -/
theorem finiteNormalRange_not_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ} (hx : fmt.finiteNormalRange x) :
    ¬ fmt.finiteUnderflowRange x :=
  not_lt_of_ge hx.1

/-- A finite-normal value is not in the source-facing overflow range. -/
theorem finiteNormalRange_not_finiteOverflowRange
    {fmt : FloatingPointFormat} {x : ℝ} (hx : fmt.finiteNormalRange x) :
    ¬ fmt.finiteOverflowRange x :=
  not_lt_of_ge hx.2

/-- IEEE-facing default overflow value for a finite exact real result that is
outside the finite range.  Nearest/even overflows to the signed infinity; the
directed modes choose either the signed infinity or the signed largest finite
endpoint according to the direction.  This is only the value component of the
overflow semantics; flags are recorded by `ieeeOverflowResult`. -/
def ieeeOverflowValue
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    IeeeValue :=
  if x < 0 then
    match mode with
    | IeeeRoundingMode.nearestEven => IeeeValue.negInf
    | IeeeRoundingMode.towardZero => IeeeValue.finite (-fmt.maxFiniteMagnitude)
    | IeeeRoundingMode.towardPositive =>
        IeeeValue.finite (-fmt.maxFiniteMagnitude)
    | IeeeRoundingMode.towardNegative => IeeeValue.negInf
  else
    match mode with
    | IeeeRoundingMode.nearestEven => IeeeValue.posInf
    | IeeeRoundingMode.towardZero => IeeeValue.finite fmt.maxFiniteMagnitude
    | IeeeRoundingMode.towardPositive => IeeeValue.posInf
    | IeeeRoundingMode.towardNegative =>
        IeeeValue.finite fmt.maxFiniteMagnitude

/-- First IEEE-facing overflow-result predicate for Chapter 2: the exact real
input is in the source-facing overflow range, the value is the mode-dependent
overflow value, and the overflow and inexact flags are set.  This is a semantic
predicate, not yet a full arithmetic operation. -/
def ieeeOverflowResult
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ)
    (r : IeeeOperationResult) : Prop :=
  fmt.finiteOverflowRange x ∧
    r.value = fmt.ieeeOverflowValue mode x ∧
    r.hasFlag IeeeExceptionFlag.overflow ∧
    r.hasFlag IeeeExceptionFlag.inexact

/-- Default IEEE-facing overflow result for an exact finite real result outside
the finite range.  It records the mode-dependent overflow value and sets
exactly the overflow and inexact flags. -/
def ieeeOverflowDefaultResult
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    IeeeOperationResult where
  value := fmt.ieeeOverflowValue mode x
  flag := fun flag =>
    flag = IeeeExceptionFlag.overflow ∨ flag = IeeeExceptionFlag.inexact

theorem ieeeOverflowDefaultResult_value
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    (fmt.ieeeOverflowDefaultResult mode x).value =
      fmt.ieeeOverflowValue mode x := rfl

theorem ieeeOverflowDefaultResult_hasFlag_iff
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ)
    (flag : IeeeExceptionFlag) :
    (fmt.ieeeOverflowDefaultResult mode x).hasFlag flag ↔
      flag = IeeeExceptionFlag.overflow ∨
        flag = IeeeExceptionFlag.inexact := by
  rfl

theorem ieeeOverflowDefaultResult_hasOverflowFlag
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    (fmt.ieeeOverflowDefaultResult mode x).hasFlag
      IeeeExceptionFlag.overflow := by
  simp [ieeeOverflowDefaultResult, IeeeOperationResult.hasFlag]

theorem ieeeOverflowDefaultResult_hasInexactFlag
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    (fmt.ieeeOverflowDefaultResult mode x).hasFlag
      IeeeExceptionFlag.inexact := by
  simp [ieeeOverflowDefaultResult, IeeeOperationResult.hasFlag]

theorem ieeeOverflowDefaultResult_ieeeOverflowResult_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx : fmt.finiteOverflowRange x) :
    fmt.ieeeOverflowResult mode x
      (fmt.ieeeOverflowDefaultResult mode x) := by
  exact ⟨hx, rfl,
    fmt.ieeeOverflowDefaultResult_hasOverflowFlag mode x,
    fmt.ieeeOverflowDefaultResult_hasInexactFlag mode x⟩

theorem ieeeOverflowValue_nearestEven_of_neg
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x < 0) :
    fmt.ieeeOverflowValue IeeeRoundingMode.nearestEven x =
      IeeeValue.negInf := by
  simp [ieeeOverflowValue, hx]

theorem ieeeOverflowValue_nearestEven_of_nonneg
    {fmt : FloatingPointFormat} {x : ℝ} (hx : 0 ≤ x) :
    fmt.ieeeOverflowValue IeeeRoundingMode.nearestEven x =
      IeeeValue.posInf := by
  have hnot : ¬ x < 0 := not_lt.mpr hx
  simp [ieeeOverflowValue, hnot]

theorem ieeeOverflowValue_towardZero_of_neg
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x < 0) :
    fmt.ieeeOverflowValue IeeeRoundingMode.towardZero x =
      IeeeValue.finite (-fmt.maxFiniteMagnitude) := by
  simp [ieeeOverflowValue, hx]

theorem ieeeOverflowValue_towardZero_of_nonneg
    {fmt : FloatingPointFormat} {x : ℝ} (hx : 0 ≤ x) :
    fmt.ieeeOverflowValue IeeeRoundingMode.towardZero x =
      IeeeValue.finite fmt.maxFiniteMagnitude := by
  have hnot : ¬ x < 0 := not_lt.mpr hx
  simp [ieeeOverflowValue, hnot]

theorem ieeeOverflowValue_towardPositive_of_neg
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x < 0) :
    fmt.ieeeOverflowValue IeeeRoundingMode.towardPositive x =
      IeeeValue.finite (-fmt.maxFiniteMagnitude) := by
  simp [ieeeOverflowValue, hx]

theorem ieeeOverflowValue_towardPositive_of_nonneg
    {fmt : FloatingPointFormat} {x : ℝ} (hx : 0 ≤ x) :
    fmt.ieeeOverflowValue IeeeRoundingMode.towardPositive x =
      IeeeValue.posInf := by
  have hnot : ¬ x < 0 := not_lt.mpr hx
  simp [ieeeOverflowValue, hnot]

theorem ieeeOverflowValue_towardNegative_of_neg
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x < 0) :
    fmt.ieeeOverflowValue IeeeRoundingMode.towardNegative x =
      IeeeValue.negInf := by
  simp [ieeeOverflowValue, hx]

theorem ieeeOverflowValue_towardNegative_of_nonneg
    {fmt : FloatingPointFormat} {x : ℝ} (hx : 0 ≤ x) :
    fmt.ieeeOverflowValue IeeeRoundingMode.towardNegative x =
      IeeeValue.finite fmt.maxFiniteMagnitude := by
  have hnot : ¬ x < 0 := not_lt.mpr hx
  simp [ieeeOverflowValue, hnot]

theorem ieeeOverflowResult_finiteOverflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    {r : IeeeOperationResult} (h : fmt.ieeeOverflowResult mode x r) :
    fmt.finiteOverflowRange x :=
  h.1

theorem ieeeOverflowResult_value
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    {r : IeeeOperationResult} (h : fmt.ieeeOverflowResult mode x r) :
    r.value = fmt.ieeeOverflowValue mode x :=
  h.2.1

theorem ieeeOverflowResult_hasOverflowFlag
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    {r : IeeeOperationResult} (h : fmt.ieeeOverflowResult mode x r) :
    r.hasFlag IeeeExceptionFlag.overflow :=
  h.2.2.1

theorem ieeeOverflowResult_hasInexactFlag
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    {r : IeeeOperationResult} (h : fmt.ieeeOverflowResult mode x r) :
    r.hasFlag IeeeExceptionFlag.inexact :=
  h.2.2.2

theorem ieeeOverflowResult_not_noFlags
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    {r : IeeeOperationResult} (h : fmt.ieeeOverflowResult mode x r) :
    ¬ r.noFlags := by
  intro hno
  exact hno IeeeExceptionFlag.overflow
    (fmt.ieeeOverflowResult_hasOverflowFlag h)

theorem ieeeOverflowResult_not_finiteNoFlags
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x y : ℝ} :
    ¬ fmt.ieeeOverflowResult mode x (IeeeOperationResult.finiteNoFlags y) := by
  intro h
  exact IeeeOperationResult.finiteNoFlags_not_hasFlag y
    IeeeExceptionFlag.overflow (fmt.ieeeOverflowResult_hasOverflowFlag h)

/-- Mantissas in the finite `t`-digit range `0 <= m <= beta^t - 1`, represented
over natural numbers as `m < beta^t`. -/
def mantissaInRange (fmt : FloatingPointFormat) (m : ℕ) : Prop :=
  m < fmt.beta ^ fmt.t

/-- The smallest normalized mantissa, `beta^(t-1)`. -/
def minNormalMantissa (fmt : FloatingPointFormat) : ℕ :=
  fmt.beta ^ (fmt.t - 1)

/-- The largest normalized mantissa, `beta^t - 1`. -/
def maxNormalMantissa (fmt : FloatingPointFormat) : ℕ :=
  fmt.beta ^ fmt.t - 1

/-- Higham's normalized nonzero mantissa condition:
`beta^(t-1) <= m <= beta^t - 1`. -/
def normalizedMantissa (fmt : FloatingPointFormat) (m : ℕ) : Prop :=
  fmt.minNormalMantissa ≤ m ∧ fmt.mantissaInRange m

/-- Higham's subnormal nonzero mantissa condition:
`0 < m < beta^(t-1)`. -/
def subnormalMantissa (fmt : FloatingPointFormat) (m : ℕ) : Prop :=
  0 < m ∧ m < fmt.minNormalMantissa

/-- Inclusive exponent range for normalized numbers. -/
def exponentInRange (fmt : FloatingPointFormat) (e : ℤ) : Prop :=
  fmt.emin ≤ e ∧ e ≤ fmt.emax

/-- Sign choice in the `+- m beta^(e-t)` representation. -/
def signValue (_fmt : FloatingPointFormat) (negative : Bool) : ℝ :=
  if negative then -1 else 1

/-- Higham equation (2.1), `+- m * beta^(e-t)`.  The mantissa and exponent
predicates are kept separate so the same value expression can be used for the
bounded system `F` and the unbounded-exponent system `G`. -/
def normalizedValue (fmt : FloatingPointFormat) (negative : Bool) (m : ℕ)
    (e : ℤ) : ℝ :=
  fmt.signValue negative * (m : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))

/-- Subnormal value form `+- m * beta^(emin-t)`. -/
def subnormalValue (fmt : FloatingPointFormat) (negative : Bool) (m : ℕ) : ℝ :=
  fmt.signValue negative * (m : ℝ) * fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))

/-- The normalized finite system `F`, excluding zero and subnormals. -/
def normalizedSystem (fmt : FloatingPointFormat) (y : ℝ) : Prop :=
  ∃ negative m e,
    fmt.normalizedMantissa m ∧
    fmt.exponentInRange e ∧
    y = fmt.normalizedValue negative m e

/-- A normalized finite representation of a value with an explicit exponent.
This is the local version of Higham's `e(x)` surface used in the guard-digit
theorems: the exponent is carried as data rather than chosen by a function. -/
def normalizedExponentRepresentation
    (fmt : FloatingPointFormat) (y : ℝ) (e : ℤ) : Prop :=
  ∃ negative m,
    fmt.normalizedMantissa m ∧
    fmt.exponentInRange e ∧
    y = fmt.normalizedValue negative m e

theorem normalizedExponentRepresentation_normalizedSystem
    {fmt : FloatingPointFormat} {y : ℝ} {e : ℤ}
    (h : fmt.normalizedExponentRepresentation y e) :
    fmt.normalizedSystem y := by
  rcases h with ⟨negative, m, hm, he, hy⟩
  exact ⟨negative, m, e, hm, he, hy⟩

theorem normalizedSystem_exists_normalizedExponentRepresentation
    {fmt : FloatingPointFormat} {y : ℝ}
    (h : fmt.normalizedSystem y) :
    ∃ e : ℤ, fmt.normalizedExponentRepresentation y e := by
  rcases h with ⟨negative, m, e, hm, he, hy⟩
  exact ⟨e, negative, m, hm, he, hy⟩

theorem normalizedSystem_iff_exists_normalizedExponentRepresentation
    {fmt : FloatingPointFormat} {y : ℝ} :
    fmt.normalizedSystem y ↔
      ∃ e : ℤ, fmt.normalizedExponentRepresentation y e := by
  constructor
  · exact normalizedSystem_exists_normalizedExponentRepresentation
  · intro h
    rcases h with ⟨e, he⟩
    exact fmt.normalizedExponentRepresentation_normalizedSystem he

/-- Higham Theorem 2.4's exponent side condition for Ferguson exact
subtraction, expressed with explicit normalized exponent representations for
`x`, `y`, and `x-y`.  The representation of `x-y` also records the
"does not underflow or overflow" side condition at the finite-format level. -/
def fergusonExponentCondition
    (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  ∃ ex ey ez : ℤ,
    fmt.normalizedExponentRepresentation x ex ∧
    fmt.normalizedExponentRepresentation y ey ∧
    fmt.normalizedExponentRepresentation (x - y) ez ∧
    ez < min ex ey

theorem fergusonExponentCondition_left_normalized
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.fergusonExponentCondition x y) :
    fmt.normalizedSystem x := by
  rcases h with ⟨_ex, _ey, _ez, hx, _hy, _hz, _hcond⟩
  exact fmt.normalizedExponentRepresentation_normalizedSystem hx

theorem fergusonExponentCondition_right_normalized
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.fergusonExponentCondition x y) :
    fmt.normalizedSystem y := by
  rcases h with ⟨_ex, _ey, _ez, _hx, hy, _hz, _hcond⟩
  exact fmt.normalizedExponentRepresentation_normalizedSystem hy

theorem fergusonExponentCondition_sub_normalized
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.fergusonExponentCondition x y) :
    fmt.normalizedSystem (x - y) := by
  rcases h with ⟨_ex, _ey, _ez, _hx, _hy, hz, _hcond⟩
  exact fmt.normalizedExponentRepresentation_normalizedSystem hz

/-- Guard-digit exact-subtraction model for Higham Theorem 2.4.  This is an
interface, not yet a constructive digit algorithm: any subtraction routine
satisfying it computes `x-y` exactly under the Ferguson exponent condition. -/
def guardDigitSubtractionModel
    (fmt : FloatingPointFormat) (flSub : ℝ → ℝ → ℝ) : Prop :=
  ∀ {x y : ℝ}, fmt.fergusonExponentCondition x y → flSub x y = x - y

theorem guardDigitSubtractionModel_exact_of_fergusonCondition
    {fmt : FloatingPointFormat} {flSub : ℝ → ℝ → ℝ} {x y : ℝ}
    (hmodel : fmt.guardDigitSubtractionModel flSub)
    (hcond : fmt.fergusonExponentCondition x y) :
    flSub x y = x - y :=
  hmodel hcond

/-- Higham Theorem 2.5's Sterbenz ratio condition. -/
def sterbenzRatioCondition (_fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  y / 2 < x ∧ x < 2 * y

theorem sterbenzRatioCondition_y_pos
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sterbenzRatioCondition x y) :
    0 < y := by
  rcases h with ⟨hlo, hhi⟩
  linarith

theorem sterbenzRatioCondition_x_pos
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sterbenzRatioCondition x y) :
    0 < x := by
  rcases h with ⟨hlo, hhi⟩
  have hy : 0 < y := by
    linarith
  linarith

theorem sterbenzRatioCondition_symm
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sterbenzRatioCondition x y) :
    fmt.sterbenzRatioCondition y x := by
  rcases h with ⟨hlo, hhi⟩
  constructor <;> linarith

theorem sterbenzRatioCondition_abs_sub_lt_left
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sterbenzRatioCondition x y) :
    |x - y| < x := by
  rcases h with ⟨hlo, hhi⟩
  have hy : 0 < y := by
    linarith
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem sterbenzRatioCondition_abs_sub_lt_right
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sterbenzRatioCondition x y) :
    |x - y| < y := by
  rcases h with ⟨hlo, hhi⟩
  have hx : 0 < x := by
    linarith
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem sterbenzRatioCondition_abs_sub_lt_min
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sterbenzRatioCondition x y) :
    |x - y| < min x y :=
  lt_min (fmt.sterbenzRatioCondition_abs_sub_lt_left h)
    (fmt.sterbenzRatioCondition_abs_sub_lt_right h)

/-- A one-digit decimal format used to keep the Sterbenz/Ferguson bridge honest:
Sterbenz's ratio hypothesis is not, in general bases, the same thing as
Ferguson's cancellation exponent hypothesis. -/
def decimalSingleDigitFormat : FloatingPointFormat where
  beta := 10
  t := 1
  emin := 1
  emax := 1
  beta_ge_two := by norm_num
  t_pos := by norm_num
  emin_le_emax := by norm_num

theorem decimalSingleDigitFormat_normalizedExponentRepresentation_four :
    decimalSingleDigitFormat.normalizedExponentRepresentation (4 : ℝ) 1 := by
  refine ⟨false, 4, ?_, ?_, ?_⟩
  · norm_num [decimalSingleDigitFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  · norm_num [decimalSingleDigitFormat, exponentInRange]
  · norm_num [decimalSingleDigitFormat, normalizedValue, signValue, betaR]

theorem decimalSingleDigitFormat_normalizedExponentRepresentation_five :
    decimalSingleDigitFormat.normalizedExponentRepresentation (5 : ℝ) 1 := by
  refine ⟨false, 5, ?_, ?_, ?_⟩
  · norm_num [decimalSingleDigitFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  · norm_num [decimalSingleDigitFormat, exponentInRange]
  · norm_num [decimalSingleDigitFormat, normalizedValue, signValue, betaR]

theorem decimalSingleDigitFormat_normalizedExponentRepresentation_nine :
    decimalSingleDigitFormat.normalizedExponentRepresentation (9 : ℝ) 1 := by
  refine ⟨false, 9, ?_, ?_, ?_⟩
  · norm_num [decimalSingleDigitFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  · norm_num [decimalSingleDigitFormat, exponentInRange]
  · norm_num [decimalSingleDigitFormat, normalizedValue, signValue, betaR]

theorem decimalSingleDigitFormat_sterbenzRatioCondition_nine_five :
    decimalSingleDigitFormat.sterbenzRatioCondition (9 : ℝ) 5 := by
  norm_num [sterbenzRatioCondition]

theorem decimalSingleDigitFormat_not_fergusonExponentCondition_nine_five :
    ¬ decimalSingleDigitFormat.fergusonExponentCondition (9 : ℝ) 5 := by
  intro h
  rcases h with ⟨ex, ey, ez, hx, hy, hz, hcond⟩
  rcases hx with ⟨_negX, _mx, _hmx, hex, _hx⟩
  rcases hy with ⟨_negY, _my, _hmy, hey, _hy⟩
  rcases hz with ⟨_negZ, _mz, _hmz, hez, _hz⟩
  norm_num [decimalSingleDigitFormat, exponentInRange] at hex hey hez
  omega

theorem decimalSingleDigitFormat_sterbenzRatio_not_ferguson :
    decimalSingleDigitFormat.sterbenzRatioCondition (9 : ℝ) 5 ∧
      decimalSingleDigitFormat.normalizedSystem (9 : ℝ) ∧
      decimalSingleDigitFormat.normalizedSystem (5 : ℝ) ∧
      decimalSingleDigitFormat.normalizedSystem ((9 : ℝ) - 5) ∧
      ¬ decimalSingleDigitFormat.fergusonExponentCondition (9 : ℝ) 5 := by
  refine ⟨decimalSingleDigitFormat_sterbenzRatioCondition_nine_five, ?_, ?_, ?_, ?_⟩
  · exact decimalSingleDigitFormat.normalizedExponentRepresentation_normalizedSystem
      decimalSingleDigitFormat_normalizedExponentRepresentation_nine
  · exact decimalSingleDigitFormat.normalizedExponentRepresentation_normalizedSystem
      decimalSingleDigitFormat_normalizedExponentRepresentation_five
  · norm_num
    exact decimalSingleDigitFormat.normalizedExponentRepresentation_normalizedSystem
      decimalSingleDigitFormat_normalizedExponentRepresentation_four
  · exact decimalSingleDigitFormat_not_fergusonExponentCondition_nine_five

/-- Current bridge surface for Sterbenz: the ratio condition plus an explicit
Ferguson exponent condition.  The decimal counterexample above shows that
Sterbenz cannot be closed by proving the ratio condition implies Ferguson's
exponent condition in general bases; the remaining finite-format theorem work is
a direct Sterbenz representability/exact-subtraction proof. -/
def sterbenzFergusonBridgeCondition
    (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  fmt.sterbenzRatioCondition x y ∧ fmt.fergusonExponentCondition x y

theorem sterbenzFergusonBridgeCondition_ratio
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sterbenzFergusonBridgeCondition x y) :
    fmt.sterbenzRatioCondition x y :=
  h.1

theorem sterbenzFergusonBridgeCondition_ferguson
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sterbenzFergusonBridgeCondition x y) :
    fmt.fergusonExponentCondition x y :=
  h.2

theorem guardDigitSubtractionModel_exact_of_sterbenzBridge
    {fmt : FloatingPointFormat} {flSub : ℝ → ℝ → ℝ} {x y : ℝ}
    (hmodel : fmt.guardDigitSubtractionModel flSub)
    (hbridge : fmt.sterbenzFergusonBridgeCondition x y) :
    flSub x y = x - y :=
  hmodel hbridge.2

/-- Higham's unbounded-exponent set `G`, with the same normalized mantissas but
without the finite exponent-range restriction. -/
def unboundedNormalizedSystem (fmt : FloatingPointFormat) (y : ℝ) : Prop :=
  ∃ negative m e,
    fmt.normalizedMantissa m ∧
    y = fmt.normalizedValue negative m e

/-- The subnormal part of the finite system. -/
def subnormalSystem (fmt : FloatingPointFormat) (y : ℝ) : Prop :=
  ∃ negative m,
    fmt.subnormalMantissa m ∧
    y = fmt.subnormalValue negative m

/-- The finite floating-point values: zero, normalized numbers, and subnormals. -/
def finiteSystem (fmt : FloatingPointFormat) (y : ℝ) : Prop :=
  y = 0 ∨ fmt.normalizedSystem y ∨ fmt.subnormalSystem y

/-- Every bounded normalized finite value is also a member of Higham's
unbounded normalized system `G`. -/
theorem normalizedSystem_unboundedNormalizedSystem
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.normalizedSystem y) :
    fmt.unboundedNormalizedSystem y := by
  rcases hy with ⟨negative, m, e, hm, _he, hy⟩
  exact ⟨negative, m, e, hm, hy⟩

/-- A base-`beta`, length-`t` digit string, written in Higham's big-endian
order `d_1, ..., d_t`. -/
def digitStringInRange (fmt : FloatingPointFormat) (digits : List ℕ) : Prop :=
  digits.length = fmt.t ∧ ∀ d ∈ digits, d < fmt.beta

/-- A normalized base-`beta`, length-`t` digit string: all digits are in range
and the most significant digit is nonzero. -/
def normalizedDigitString (fmt : FloatingPointFormat) (digits : List ℕ) : Prop :=
  fmt.digitStringInRange digits ∧ ∃ d rest, digits = d :: rest ∧ 0 < d

/-- The integer mantissa encoded by a big-endian digit string.  Mathlib's
`Nat.ofDigits` uses little-endian order, hence the reverse. -/
def positionalMantissa (fmt : FloatingPointFormat) (digits : List ℕ) : ℕ :=
  Nat.ofDigits fmt.beta digits.reverse

/-- Higham equation (2.2), represented through the equivalent integer mantissa
used in (2.1). -/
def positionalValue (fmt : FloatingPointFormat) (negative : Bool)
    (digits : List ℕ) (e : ℤ) : ℝ :=
  fmt.normalizedValue negative (fmt.positionalMantissa digits) e

/-- Same-exponent structural adjacency between normalized values.  The relation
is unordered; it records the two immediate mantissas `m` and `m+1` at a fixed
exponent before proving they are adjacent in the ordered real set. -/
def sameExponentAdjacentNormalized (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  ∃ negative m e,
    fmt.normalizedMantissa m ∧
    fmt.normalizedMantissa (m + 1) ∧
    ((x = fmt.normalizedValue negative m e ∧
        y = fmt.normalizedValue negative (m + 1) e) ∨
      (x = fmt.normalizedValue negative (m + 1) e ∧
        y = fmt.normalizedValue negative m e))

/-- Exponent-boundary structural adjacency: the largest mantissa at exponent
`e` next to the smallest mantissa at exponent `e+1`.  The relation is unordered
and does not yet assert there is no representable value between them. -/
def boundaryAdjacentNormalized (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  ∃ negative e,
    ((x = fmt.normalizedValue negative fmt.maxNormalMantissa e ∧
        y = fmt.normalizedValue negative fmt.minNormalMantissa (e + 1)) ∨
      (x = fmt.normalizedValue negative fmt.minNormalMantissa (e + 1) ∧
        y = fmt.normalizedValue negative fmt.maxNormalMantissa e))

/-- Structural adjacency for normalized values in Higham's unbounded-exponent
system: either adjacent mantissas at one exponent or the exponent-boundary
case.  Later lemmas must still prove this structural relation matches real-order
adjacency in the representable set. -/
def adjacentNormalized (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  fmt.sameExponentAdjacentNormalized x y ∨ fmt.boundaryAdjacentNormalized x y

/-- Real-order adjacency in Higham's unbounded normalized system `G`: both
endpoints are normalized representable values, they are distinct, and no
normalized representable value lies strictly between them in either order. -/
def realOrderAdjacentNormalized (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  fmt.unboundedNormalizedSystem x ∧
    fmt.unboundedNormalizedSystem y ∧
      x ≠ y ∧
        ∀ z, fmt.unboundedNormalizedSystem z →
          ¬ ((x < z ∧ z < y) ∨ (y < z ∧ z < x))

/-- Nearest-rounding relation into an arbitrary set of representable values.
This deliberately leaves tie-breaking as a relation rather than a function. -/
def nearestRoundingIn (S : ℝ → Prop) (x y : ℝ) : Prop :=
  S y ∧ ∀ z, S z → |x - y| ≤ |x - z|

/-- Nearest rounding into Higham's unbounded-exponent set `G`. -/
def nearestRoundingToUnbounded (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  nearestRoundingIn fmt.unboundedNormalizedSystem x y

/-- Nearest rounding into the finite system including zero and subnormals. -/
def nearestRoundingToFinite (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  nearestRoundingIn fmt.finiteSystem x y

/-- First IEEE-facing underflow-result predicate for Chapter 2: the exact real
input is in the source-facing underflow range, the returned value is a finite
nearest-rounded value, the underflow flag is set, and an inexact flag is set
whenever the rounded value differs from the exact real input.  This is the
finite gradual-underflow branch, not a complete IEEE special-value semantics. -/
def ieeeUnderflowResult
    (fmt : FloatingPointFormat) (x rounded : ℝ)
    (r : IeeeOperationResult) : Prop :=
  fmt.finiteUnderflowRange x ∧
    fmt.nearestRoundingToFinite x rounded ∧
    r.value = IeeeValue.finite rounded ∧
    r.hasFlag IeeeExceptionFlag.underflow ∧
    (rounded ≠ x → r.hasFlag IeeeExceptionFlag.inexact)

/-- Mode-dependent finite evidence for an IEEE-facing underflow result.  The
nearest/even mode keeps the nearest-finite requirement used by
`ieeeUnderflowResult`; directed modes record the finite one-sided/toward-zero
property appropriate for the mode. -/
def ieeeUnderflowModeRoundingEvidence
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (x rounded : ℝ) : Prop :=
  match mode with
  | IeeeRoundingMode.nearestEven =>
      fmt.nearestRoundingToFinite x rounded
  | IeeeRoundingMode.towardZero =>
      fmt.finiteSystem rounded ∧ |rounded| ≤ |x|
  | IeeeRoundingMode.towardPositive =>
      fmt.finiteSystem rounded ∧ x ≤ rounded
  | IeeeRoundingMode.towardNegative =>
      fmt.finiteSystem rounded ∧ rounded ≤ x

/-- Mode-aware IEEE-facing underflow-result predicate.  It generalizes
`ieeeUnderflowResult` from nearest/even to directed modes by separating the
rounding-policy evidence from the common result value and flag behavior. -/
def ieeeUnderflowModeResult
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (x rounded : ℝ) (r : IeeeOperationResult) : Prop :=
  fmt.finiteUnderflowRange x ∧
    fmt.ieeeUnderflowModeRoundingEvidence mode x rounded ∧
    r.value = IeeeValue.finite rounded ∧
    r.hasFlag IeeeExceptionFlag.underflow ∧
    (rounded ≠ x → r.hasFlag IeeeExceptionFlag.inexact)

/-- Default IEEE-facing underflow result for a finite exact real result in the
underflow range.  It returns the supplied finite rounded value, always sets the
underflow flag, and sets the inexact flag exactly when the rounded value is not
the exact real input. -/
def ieeeUnderflowDefaultResult
    (_fmt : FloatingPointFormat) (x rounded : ℝ) :
    IeeeOperationResult where
  value := IeeeValue.finite rounded
  flag := fun flag =>
    flag = IeeeExceptionFlag.underflow ∨
      (rounded ≠ x ∧ flag = IeeeExceptionFlag.inexact)

theorem ieeeUnderflowDefaultResult_value
    (fmt : FloatingPointFormat) (x rounded : ℝ) :
    (fmt.ieeeUnderflowDefaultResult x rounded).value =
      IeeeValue.finite rounded := rfl

theorem ieeeUnderflowDefaultResult_toReal?
    (fmt : FloatingPointFormat) (x rounded : ℝ) :
    (fmt.ieeeUnderflowDefaultResult x rounded).value.toReal? =
      some rounded := rfl

theorem ieeeUnderflowDefaultResult_hasFlag_iff
    (fmt : FloatingPointFormat) (x rounded : ℝ)
    (flag : IeeeExceptionFlag) :
    (fmt.ieeeUnderflowDefaultResult x rounded).hasFlag flag ↔
      flag = IeeeExceptionFlag.underflow ∨
        (rounded ≠ x ∧ flag = IeeeExceptionFlag.inexact) := by
  rfl

theorem ieeeUnderflowDefaultResult_hasUnderflowFlag
    (fmt : FloatingPointFormat) (x rounded : ℝ) :
    (fmt.ieeeUnderflowDefaultResult x rounded).hasFlag
      IeeeExceptionFlag.underflow := by
  simp [ieeeUnderflowDefaultResult, IeeeOperationResult.hasFlag]

theorem ieeeUnderflowDefaultResult_hasInexactFlag_of_ne
    (fmt : FloatingPointFormat) {x rounded : ℝ} (hne : rounded ≠ x) :
    (fmt.ieeeUnderflowDefaultResult x rounded).hasFlag
      IeeeExceptionFlag.inexact := by
  simp [ieeeUnderflowDefaultResult, IeeeOperationResult.hasFlag, hne]

theorem ieeeUnderflowDefaultResult_ieeeUnderflowResult
    {fmt : FloatingPointFormat} {x rounded : ℝ}
    (hx : fmt.finiteUnderflowRange x)
    (hround : fmt.nearestRoundingToFinite x rounded) :
    fmt.ieeeUnderflowResult x rounded
      (fmt.ieeeUnderflowDefaultResult x rounded) := by
  exact ⟨hx, hround, rfl,
    fmt.ieeeUnderflowDefaultResult_hasUnderflowFlag x rounded,
    fun hne => fmt.ieeeUnderflowDefaultResult_hasInexactFlag_of_ne hne⟩

theorem ieeeUnderflowDefaultResult_ieeeUnderflowModeResult
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x rounded : ℝ}
    (hx : fmt.finiteUnderflowRange x)
    (hround : fmt.ieeeUnderflowModeRoundingEvidence mode x rounded) :
    fmt.ieeeUnderflowModeResult mode x rounded
      (fmt.ieeeUnderflowDefaultResult x rounded) := by
  exact ⟨hx, hround, rfl,
    fmt.ieeeUnderflowDefaultResult_hasUnderflowFlag x rounded,
    fun hne => fmt.ieeeUnderflowDefaultResult_hasInexactFlag_of_ne hne⟩

/-- Explicit local round-away selector for an ordered adjacent bracket.  It
chooses the nearer endpoint, and in an exact distance tie chooses the endpoint
with larger magnitude.  This is a local policy for a supplied adjacent pair,
not yet a total finite-format rounding function. -/
def nearestAdjacentRoundAway (x a b : ℝ) : ℝ :=
  if |x - a| < |x - b| then a
  else if |x - b| < |x - a| then b
  else if |a| ≤ |b| then b else a

/-- Mantissa parity used by the local round-to-even tie policy.  For binary and
decimal-style formats this matches Higham's "even last digit" rule on adjacent
same-exponent mantissas. -/
def evenMantissa (m : ℕ) : Prop :=
  m % 2 = 0

instance decidableEvenMantissa (m : ℕ) : Decidable (evenMantissa m) := by
  unfold evenMantissa
  infer_instance

theorem evenMantissa_succ_iff_not_evenMantissa (m : ℕ) :
    evenMantissa (m + 1) ↔ ¬ evenMantissa m := by
  unfold evenMantissa
  omega

theorem evenMantissa_iff_not_evenMantissa_succ (m : ℕ) :
    evenMantissa m ↔ ¬ evenMantissa (m + 1) := by
  constructor
  · intro hm hm_succ
    exact (evenMantissa_succ_iff_not_evenMantissa m).mp hm_succ hm
  · intro hnot_succ
    by_contra hm
    exact hnot_succ ((evenMantissa_succ_iff_not_evenMantissa m).mpr hm)

/-- Explicit local round-to-even selector for an ordered adjacent bracket.  It
chooses the nearer endpoint, and in an exact distance tie chooses the endpoint
whose supplied left mantissa is even; otherwise it chooses the right endpoint.
This is a local policy for a supplied adjacent pair, not a total IEEE rounding
operation. -/
def nearestAdjacentRoundToEven (x a b : ℝ) (leftMantissa : ℕ) : ℝ :=
  if |x - a| < |x - b| then a
  else if |x - b| < |x - a| then b
  else if evenMantissa leftMantissa then a else b

/-- Local directed selector for rounding toward negative infinity on a supplied
ordered adjacent bracket `a <= x <= b`.  Exact endpoints are fixed; otherwise it
chooses the left endpoint. -/
def adjacentRoundTowardNegative (x a b : ℝ) : ℝ :=
  if x = b then b else a

/-- Local directed selector for rounding toward positive infinity on a supplied
ordered adjacent bracket `a <= x <= b`.  Exact endpoints are fixed; otherwise it
chooses the right endpoint. -/
def adjacentRoundTowardPositive (x a b : ℝ) : ℝ :=
  if x = a then a else b

/-- Local directed selector for rounding toward zero on a supplied adjacent
bracket.  On a nonnegative bracket it uses the toward-negative selector, and on
a negative bracket it uses the toward-positive selector, so exact endpoints are
fixed by the directed endpoint selectors. -/
def adjacentRoundTowardZero (x a b : ℝ) : ℝ :=
  if x < 0 then adjacentRoundTowardPositive x a b
  else adjacentRoundTowardNegative x a b

theorem minNormalMantissa_pos (fmt : FloatingPointFormat) :
    0 < fmt.minNormalMantissa := by
  unfold minNormalMantissa
  exact Nat.pow_pos (lt_of_lt_of_le (by decide : 0 < 2) fmt.beta_ge_two)

theorem mantissaBound_pos (fmt : FloatingPointFormat) :
    0 < fmt.beta ^ fmt.t :=
  Nat.pow_pos (lt_of_lt_of_le (by decide : 0 < 2) fmt.beta_ge_two)

theorem one_lt_beta (fmt : FloatingPointFormat) :
    1 < fmt.beta :=
  lt_of_lt_of_le (by decide : 1 < 2) fmt.beta_ge_two

theorem minNormalMantissa_lt_mantissaBound (fmt : FloatingPointFormat) :
    fmt.minNormalMantissa < fmt.beta ^ fmt.t := by
  unfold minNormalMantissa
  exact Nat.pow_lt_pow_right fmt.one_lt_beta (Nat.sub_lt fmt.t_pos Nat.one_pos)

theorem minNormalMantissa_mul_beta_eq_mantissaBound
    (fmt : FloatingPointFormat) :
    fmt.minNormalMantissa * fmt.beta = fmt.beta ^ fmt.t := by
  unfold minNormalMantissa
  rw [← pow_succ]
  congr 1
  exact Nat.sub_one_add_one_eq_of_pos fmt.t_pos

theorem normalizedMantissa_pos {fmt : FloatingPointFormat} {m : ℕ}
    (hm : fmt.normalizedMantissa m) :
    0 < m :=
  lt_of_lt_of_le fmt.minNormalMantissa_pos hm.1

theorem minNormalMantissa_le_mantissaBound (fmt : FloatingPointFormat) :
    fmt.minNormalMantissa ≤ fmt.beta ^ fmt.t := by
  unfold minNormalMantissa
  exact Nat.pow_le_pow_right
    (Nat.succ_le_of_lt (lt_of_lt_of_le (by decide : 0 < 2) fmt.beta_ge_two))
    (Nat.sub_le _ _)

theorem minNormalMantissa_normalized (fmt : FloatingPointFormat) :
    fmt.normalizedMantissa fmt.minNormalMantissa :=
  ⟨le_rfl, fmt.minNormalMantissa_lt_mantissaBound⟩

theorem maxNormalMantissa_add_one (fmt : FloatingPointFormat) :
    fmt.maxNormalMantissa + 1 = fmt.beta ^ fmt.t := by
  unfold maxNormalMantissa
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt fmt.mantissaBound_pos)

theorem maxNormalMantissa_lt_mantissaBound (fmt : FloatingPointFormat) :
    fmt.maxNormalMantissa < fmt.beta ^ fmt.t := by
  rw [← fmt.maxNormalMantissa_add_one]
  exact Nat.lt_succ_self fmt.maxNormalMantissa

theorem minNormalMantissa_le_maxNormalMantissa (fmt : FloatingPointFormat) :
    fmt.minNormalMantissa ≤ fmt.maxNormalMantissa := by
  have hlt : fmt.minNormalMantissa < fmt.maxNormalMantissa + 1 := by
    rw [fmt.maxNormalMantissa_add_one]
    exact fmt.minNormalMantissa_lt_mantissaBound
  exact Nat.le_of_lt_succ hlt

theorem maxNormalMantissa_normalized (fmt : FloatingPointFormat) :
    fmt.normalizedMantissa fmt.maxNormalMantissa :=
  ⟨fmt.minNormalMantissa_le_maxNormalMantissa,
    fmt.maxNormalMantissa_lt_mantissaBound⟩

theorem evenMantissa_minNormalMantissa_of_even_beta
    (fmt : FloatingPointFormat)
    (hbeta : evenMantissa fmt.beta) (ht : 1 < fmt.t) :
    evenMantissa fmt.minNormalMantissa := by
  unfold evenMantissa at *
  apply Nat.mod_eq_zero_of_dvd
  have hbeta_dvd : 2 ∣ fmt.beta := Nat.dvd_of_mod_eq_zero hbeta
  have hpow : fmt.beta ∣ fmt.beta ^ (fmt.t - 1) := by
    simpa using
      (Nat.pow_dvd_pow fmt.beta (by omega : 1 ≤ fmt.t - 1))
  exact dvd_trans hbeta_dvd hpow

theorem not_evenMantissa_maxNormalMantissa_of_even_beta
    (fmt : FloatingPointFormat)
    (hbeta : evenMantissa fmt.beta) :
    ¬ evenMantissa fmt.maxNormalMantissa := by
  unfold evenMantissa at *
  intro hmax
  have hbeta_dvd : 2 ∣ fmt.beta := Nat.dvd_of_mod_eq_zero hbeta
  have hpow : 2 ∣ fmt.beta ^ fmt.t := by
    have hbeta_pow : fmt.beta ∣ fmt.beta ^ fmt.t := by
      simpa using
        (Nat.pow_dvd_pow fmt.beta (Nat.succ_le_of_lt fmt.t_pos))
    exact dvd_trans hbeta_dvd hbeta_pow
  have hbound_mod : (fmt.beta ^ fmt.t) % 2 = 0 :=
    Nat.mod_eq_zero_of_dvd hpow
  have hmax_add := fmt.maxNormalMantissa_add_one
  omega

theorem evenMantissa_minNormalMantissa_iff_not_evenMantissa_maxNormalMantissa_of_even_beta
    (fmt : FloatingPointFormat)
    (hbeta : evenMantissa fmt.beta) (ht : 1 < fmt.t) :
    evenMantissa fmt.minNormalMantissa ↔
      ¬ evenMantissa fmt.maxNormalMantissa := by
  constructor
  · intro _hmin
    exact fmt.not_evenMantissa_maxNormalMantissa_of_even_beta hbeta
  · intro _hmax
    exact fmt.evenMantissa_minNormalMantissa_of_even_beta hbeta ht

theorem evenMantissa_maxNormalMantissa_iff_not_evenMantissa_minNormalMantissa_of_even_beta
    (fmt : FloatingPointFormat)
    (hbeta : evenMantissa fmt.beta) (ht : 1 < fmt.t) :
    evenMantissa fmt.maxNormalMantissa ↔
      ¬ evenMantissa fmt.minNormalMantissa := by
  constructor
  · intro hmax
    exact False.elim
      ((fmt.not_evenMantissa_maxNormalMantissa_of_even_beta hbeta) hmax)
  · intro hnot_min
    exact False.elim
      (hnot_min (fmt.evenMantissa_minNormalMantissa_of_even_beta hbeta ht))

theorem minNormalMantissa_mem_normalizedSystem (fmt : FloatingPointFormat)
    (negative : Bool) :
    fmt.normalizedSystem
      (fmt.normalizedValue negative fmt.minNormalMantissa fmt.emin) :=
  ⟨negative, fmt.minNormalMantissa, fmt.emin,
    fmt.minNormalMantissa_normalized, ⟨le_rfl, fmt.emin_le_emax⟩, rfl⟩

theorem maxNormalMantissa_mem_normalizedSystem (fmt : FloatingPointFormat)
    (negative : Bool) :
    fmt.normalizedSystem
      (fmt.normalizedValue negative fmt.maxNormalMantissa fmt.emax) :=
  ⟨negative, fmt.maxNormalMantissa, fmt.emax,
    fmt.maxNormalMantissa_normalized, ⟨fmt.emin_le_emax, le_rfl⟩, rfl⟩

theorem subnormalMantissa_inRange {fmt : FloatingPointFormat} {m : ℕ}
    (hm : fmt.subnormalMantissa m) :
    fmt.mantissaInRange m := by
  unfold mantissaInRange
  exact lt_of_lt_of_le hm.2 fmt.minNormalMantissa_le_mantissaBound

theorem one_subnormalMantissa_of_subnormalMantissa
    {fmt : FloatingPointFormat} {m : ℕ} (hm : fmt.subnormalMantissa m) :
    fmt.subnormalMantissa 1 :=
  ⟨by norm_num, lt_of_le_of_lt (Nat.succ_le_of_lt hm.1) hm.2⟩

theorem digitStringInRange_reverse {fmt : FloatingPointFormat}
    {digits : List ℕ} (hdigits : fmt.digitStringInRange digits) :
    fmt.digitStringInRange digits.reverse := by
  rcases hdigits with ⟨hlen, hdigit_lt⟩
  constructor
  · rw [List.length_reverse]
    exact hlen
  · intro d hd
    exact hdigit_lt d (by simpa using List.mem_reverse.mp hd)

theorem positionalMantissa_lt_mantissaBound {fmt : FloatingPointFormat}
    {digits : List ℕ} (hdigits : fmt.digitStringInRange digits) :
    fmt.positionalMantissa digits < fmt.beta ^ fmt.t := by
  have hrev := fmt.digitStringInRange_reverse hdigits
  have hlt :=
    Nat.ofDigits_lt_base_pow_length fmt.one_lt_beta hrev.2
  simpa [positionalMantissa, hrev.1] using hlt

theorem minNormalMantissa_le_positionalMantissa
    {fmt : FloatingPointFormat} {digits : List ℕ}
    (hdigits : fmt.normalizedDigitString digits) :
    fmt.minNormalMantissa ≤ fmt.positionalMantissa digits := by
  rcases hdigits with ⟨hrange, d, rest, rfl, hdpos⟩
  have hlen : rest.length + 1 = fmt.t := by
    simpa using hrange.1
  unfold minNormalMantissa positionalMantissa
  rw [Nat.ofDigits_reverse_cons]
  have hrest : rest.length = fmt.t - 1 := by
    omega
  have hpow :
      fmt.beta ^ (fmt.t - 1) ≤ fmt.beta ^ rest.length * d := by
    rw [hrest]
    calc
      fmt.beta ^ (fmt.t - 1) = fmt.beta ^ (fmt.t - 1) * 1 := by
        rw [mul_one]
      _ ≤ fmt.beta ^ (fmt.t - 1) * d :=
        Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hdpos)
  exact le_trans hpow (Nat.le_add_left _ _)

theorem positionalMantissa_normalized {fmt : FloatingPointFormat}
    {digits : List ℕ} (hdigits : fmt.normalizedDigitString digits) :
    fmt.normalizedMantissa (fmt.positionalMantissa digits) :=
  ⟨fmt.minNormalMantissa_le_positionalMantissa hdigits,
    fmt.positionalMantissa_lt_mantissaBound hdigits.1⟩

theorem positionalValue_eq_normalizedValue_positionalMantissa
    (fmt : FloatingPointFormat) (negative : Bool)
    (digits : List ℕ) (e : ℤ) :
    fmt.positionalValue negative digits e =
      fmt.normalizedValue negative (fmt.positionalMantissa digits) e := rfl

theorem positionalValue_mem_normalizedSystem
    {fmt : FloatingPointFormat} {negative : Bool}
    {digits : List ℕ} {e : ℤ}
    (hdigits : fmt.normalizedDigitString digits)
    (he : fmt.exponentInRange e) :
    fmt.normalizedSystem (fmt.positionalValue negative digits e) :=
  ⟨negative, fmt.positionalMantissa digits, e,
    fmt.positionalMantissa_normalized hdigits, he, rfl⟩

theorem exists_digitStringInRange_positionalMantissa_eq
    {fmt : FloatingPointFormat} {m : ℕ} (hm : fmt.mantissaInRange m) :
    ∃ digits : List ℕ,
      fmt.digitStringInRange digits ∧
        fmt.positionalMantissa digits = m := by
  let little := Nat.digitsAppend fmt.beta fmt.t m
  refine ⟨little.reverse, ?_, ?_⟩
  · have hlittle := Nat.mapsTo_digitsAppend fmt.one_lt_beta fmt.t hm
    constructor
    · rw [List.length_reverse]
      exact hlittle.1
    · intro d hd
      exact hlittle.2 d (by simpa using List.mem_reverse.mp hd)
  · unfold positionalMantissa
    simp [little]
    exact (Nat.setInvOn_digitsAppend_ofDigits fmt.one_lt_beta fmt.t).2 hm

theorem exists_normalizedDigitString_positionalMantissa_eq
    {fmt : FloatingPointFormat} {m : ℕ}
    (hm : fmt.normalizedMantissa m) :
    ∃ digits : List ℕ,
      fmt.normalizedDigitString digits ∧
        fmt.positionalMantissa digits = m := by
  let little := fmt.beta.digits m
  have hmpos : 0 < m := fmt.normalizedMantissa_pos hm
  have hmne : m ≠ 0 := ne_of_gt hmpos
  have hmin : fmt.beta ^ (fmt.t - 1) ≤ m := by
    simpa [minNormalMantissa] using hm.1
  have hlen_le : little.length ≤ fmt.t := by
    exact (Nat.digits_length_le_iff fmt.one_lt_beta m).2 hm.2
  have hlen_gt : fmt.t - 1 < little.length := by
    exact (Nat.lt_digits_length_iff fmt.one_lt_beta m).2 hmin
  have hlen : little.length = fmt.t := by
    omega
  have hlittle_ne : little ≠ [] := by
    exact Nat.digits_ne_nil_iff_ne_zero.mpr hmne
  refine ⟨little.reverse, ?_, ?_⟩
  · constructor
    · constructor
      · rw [List.length_reverse]
        exact hlen
      · intro d hd
        exact Nat.digits_lt_base fmt.one_lt_beta
          (by simpa [little] using List.mem_reverse.mp hd)
    · refine ⟨little.getLast hlittle_ne, little.dropLast.reverse, ?_, ?_⟩
      · calc
          little.reverse =
              (little.dropLast ++ [little.getLast hlittle_ne]).reverse := by
            rw [List.dropLast_append_getLast hlittle_ne]
          _ = little.getLast hlittle_ne :: little.dropLast.reverse := by
            simp
      · exact Nat.pos_of_ne_zero
          (by
            simpa [little] using Nat.getLast_digit_ne_zero fmt.beta hmne)
  · unfold positionalMantissa
    simp [little, Nat.ofDigits_digits]

theorem digitStringInRange_eq_of_positionalMantissa_eq
    {fmt : FloatingPointFormat} {digits₁ digits₂ : List ℕ}
    (h₁ : fmt.digitStringInRange digits₁)
    (h₂ : fmt.digitStringInRange digits₂)
    (h : fmt.positionalMantissa digits₁ = fmt.positionalMantissa digits₂) :
    digits₁ = digits₂ := by
  have h₁rev := fmt.digitStringInRange_reverse h₁
  have h₂rev := fmt.digitStringInRange_reverse h₂
  have hrev :
      digits₁.reverse = digits₂.reverse :=
    Nat.injOn_ofDigits fmt.one_lt_beta fmt.t
      h₁rev h₂rev (by simpa [positionalMantissa] using h)
  have := congrArg List.reverse hrev
  simpa using this

theorem betaR_pos (fmt : FloatingPointFormat) :
    0 < fmt.betaR := by
  unfold betaR
  exact Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : 0 < 2) fmt.beta_ge_two)

theorem betaR_nonneg (fmt : FloatingPointFormat) :
    0 ≤ fmt.betaR :=
  (fmt.betaR_pos).le

theorem betaR_zpow_pos (fmt : FloatingPointFormat) (e : ℤ) :
    0 < fmt.betaR ^ e :=
  zpow_pos fmt.betaR_pos e

theorem betaR_zpow_nonneg (fmt : FloatingPointFormat) (e : ℤ) :
    0 ≤ fmt.betaR ^ e :=
  (fmt.betaR_zpow_pos e).le

theorem betaR_zpow_le_zpow_of_le (fmt : FloatingPointFormat)
    {e e' : ℤ} (h : e ≤ e') :
    fmt.betaR ^ e ≤ fmt.betaR ^ e' := by
  have hone : (1 : ℝ) ≤ fmt.betaR := by
    unfold betaR
    exact_mod_cast (le_trans (by decide : 1 ≤ 2) fmt.beta_ge_two)
  exact zpow_le_zpow_right₀ hone h

theorem machineEpsilon_nonneg (fmt : FloatingPointFormat) :
    0 ≤ fmt.machineEpsilon := by
  unfold machineEpsilon
  exact fmt.betaR_zpow_nonneg (1 - (fmt.t : ℤ))

theorem machineEpsilon_pos (fmt : FloatingPointFormat) :
    0 < fmt.machineEpsilon := by
  unfold machineEpsilon
  exact fmt.betaR_zpow_pos (1 - (fmt.t : ℤ))

theorem unitRoundoff_nonneg (fmt : FloatingPointFormat) :
    0 ≤ fmt.unitRoundoff := by
  unfold unitRoundoff
  exact mul_nonneg (by norm_num) fmt.machineEpsilon_nonneg

theorem unitRoundoff_pos (fmt : FloatingPointFormat) :
    0 < fmt.unitRoundoff := by
  unfold unitRoundoff
  exact mul_pos (by norm_num) fmt.machineEpsilon_pos

theorem fortranEpsilon_pos (fmt : FloatingPointFormat) :
    0 < fmt.fortranEpsilon := by
  rw [fortranEpsilon]
  exact fmt.machineEpsilon_pos

theorem ulpAtExponent_nonneg (fmt : FloatingPointFormat) (e : ℤ) :
    0 ≤ fmt.ulpAtExponent e := by
  unfold ulpAtExponent
  exact fmt.betaR_zpow_nonneg (e - (fmt.t : ℤ))

theorem ulpAtExponent_pos (fmt : FloatingPointFormat) (e : ℤ) :
    0 < fmt.ulpAtExponent e := by
  unfold ulpAtExponent
  exact fmt.betaR_zpow_pos (e - (fmt.t : ℤ))

theorem ulpAtExponent_one (fmt : FloatingPointFormat) :
    fmt.ulpAtExponent 1 = fmt.machineEpsilon :=
  rfl

theorem signValue_abs (fmt : FloatingPointFormat) (negative : Bool) :
    |fmt.signValue negative| = 1 := by
  unfold signValue
  cases negative <;> simp

theorem normalizedValue_abs (fmt : FloatingPointFormat) (negative : Bool)
    (m : ℕ) (e : ℤ) :
    |fmt.normalizedValue negative m e| =
      (m : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  unfold normalizedValue
  rw [abs_mul, abs_mul, fmt.signValue_abs negative,
    abs_of_nonneg (Nat.cast_nonneg m),
    abs_of_pos (fmt.betaR_zpow_pos (e - (fmt.t : ℤ)))]
  ring

theorem subnormalValue_abs (fmt : FloatingPointFormat) (negative : Bool)
    (m : ℕ) :
    |fmt.subnormalValue negative m| =
      (m : ℝ) * fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
  unfold subnormalValue
  rw [abs_mul, abs_mul, fmt.signValue_abs negative,
    abs_of_nonneg (Nat.cast_nonneg m),
    abs_of_pos (fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ)))]
  ring

theorem normalizedValue_ne_zero {fmt : FloatingPointFormat}
    {negative : Bool} {m : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) :
    fmt.normalizedValue negative m e ≠ 0 := by
  have hpos :
      0 < |fmt.normalizedValue negative m e| := by
    rw [fmt.normalizedValue_abs negative m e]
    exact mul_pos
      (Nat.cast_pos.mpr (fmt.normalizedMantissa_pos hm))
      (fmt.betaR_zpow_pos (e - (fmt.t : ℤ)))
  exact abs_pos.mp hpos

theorem unboundedNormalizedSystem_ne_zero {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.unboundedNormalizedSystem y) :
    y ≠ 0 := by
  rcases hy with ⟨negative, m, e, hm, rfl⟩
  exact fmt.normalizedValue_ne_zero hm

theorem subnormalValue_ne_zero {fmt : FloatingPointFormat}
    {negative : Bool} {m : ℕ} (hm : fmt.subnormalMantissa m) :
    fmt.subnormalValue negative m ≠ 0 := by
  have hpos :
      0 < |fmt.subnormalValue negative m| := by
    rw [fmt.subnormalValue_abs negative m]
    exact mul_pos
      (Nat.cast_pos.mpr hm.1)
      (fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ)))
  exact abs_pos.mp hpos

theorem subnormalValue_false_pos {fmt : FloatingPointFormat} {m : ℕ}
    (hm : fmt.subnormalMantissa m) :
    0 < fmt.subnormalValue false m := by
  simpa [subnormalValue, signValue] using
    mul_pos (Nat.cast_pos.mpr hm.1)
      (fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ)))

theorem subnormalValue_true_neg {fmt : FloatingPointFormat} {m : ℕ}
    (hm : fmt.subnormalMantissa m) :
    fmt.subnormalValue true m < 0 := by
  have hpos :
      0 < (m : ℝ) * fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) :=
    mul_pos (Nat.cast_pos.mpr hm.1)
      (fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ)))
  have hneg :
      -((m : ℝ) * fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) < 0 := by
    linarith
  simpa [subnormalValue, signValue] using hneg

theorem subnormalSystem_ne_zero {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.subnormalSystem y) :
    y ≠ 0 := by
  rcases hy with ⟨negative, m, hm, rfl⟩
  exact fmt.subnormalValue_ne_zero hm

theorem normalizedValue_true_eq_neg_false (fmt : FloatingPointFormat)
    (m : ℕ) (e : ℤ) :
    fmt.normalizedValue true m e = -fmt.normalizedValue false m e := by
  unfold normalizedValue signValue
  simp

theorem normalizedValue_not_eq_neg (fmt : FloatingPointFormat)
    (negative : Bool) (m : ℕ) (e : ℤ) :
    fmt.normalizedValue (!negative) m e =
      -fmt.normalizedValue negative m e := by
  cases negative
  · simp [normalizedValue, signValue]
  · simp [normalizedValue, signValue]

/-- Flipping the sign bit negates a subnormal value with the same mantissa. -/
theorem subnormalValue_not_eq_neg (fmt : FloatingPointFormat)
    (negative : Bool) (m : ℕ) :
    fmt.subnormalValue (!negative) m =
      -fmt.subnormalValue negative m := by
  cases negative
  · simp [subnormalValue, signValue]
  · simp [subnormalValue, signValue]

/-- The normalized finite system is closed under negation. -/
theorem normalizedSystem_neg
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.normalizedSystem y) :
    fmt.normalizedSystem (-y) := by
  rcases hy with ⟨negative, m, e, hm, he, rfl⟩
  refine ⟨!negative, m, e, hm, he, ?_⟩
  exact Eq.symm (fmt.normalizedValue_not_eq_neg negative m e)

/-- Higham's unbounded normalized system `G` is closed under negation. -/
theorem unboundedNormalizedSystem_neg
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.unboundedNormalizedSystem y) :
    fmt.unboundedNormalizedSystem (-y) := by
  rcases hy with ⟨negative, m, e, hm, rfl⟩
  refine ⟨!negative, m, e, hm, ?_⟩
  exact Eq.symm (fmt.normalizedValue_not_eq_neg negative m e)

/-- The subnormal finite system is closed under negation. -/
theorem subnormalSystem_neg
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.subnormalSystem y) :
    fmt.subnormalSystem (-y) := by
  rcases hy with ⟨negative, m, hm, rfl⟩
  refine ⟨!negative, m, hm, ?_⟩
  exact Eq.symm (fmt.subnormalValue_not_eq_neg negative m)

/-- The finite floating-point system is closed under negation. -/
theorem finiteSystem_neg
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.finiteSystem y) :
    fmt.finiteSystem (-y) := by
  rcases hy with hzero | hnorm | hsub
  · subst y
    simp [finiteSystem]
  · exact Or.inr (Or.inl (fmt.normalizedSystem_neg hnorm))
  · exact Or.inr (Or.inr (fmt.subnormalSystem_neg hsub))

theorem normalizedValue_sameExponent_lt_iff_false
    (fmt : FloatingPointFormat) (m n : ℕ) (e : ℤ) :
    fmt.normalizedValue false m e < fmt.normalizedValue false n e ↔
      m < n := by
  constructor
  · intro h
    have hscale_nonneg : 0 ≤ fmt.betaR ^ (e - (fmt.t : ℤ)) :=
      fmt.betaR_zpow_nonneg (e - (fmt.t : ℤ))
    have hmul :
        (m : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) <
          (n : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) := by
      simpa [normalizedValue, signValue] using h
    exact Nat.cast_lt.mp (lt_of_mul_lt_mul_right hmul hscale_nonneg)
  · intro hmn
    have hscale_pos : 0 < fmt.betaR ^ (e - (fmt.t : ℤ)) :=
      fmt.betaR_zpow_pos (e - (fmt.t : ℤ))
    have hcast : (m : ℝ) < n := Nat.cast_lt.mpr hmn
    have hmul :
        (m : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) <
          (n : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) :=
      mul_lt_mul_of_pos_right hcast hscale_pos
    simpa [normalizedValue, signValue] using hmul

theorem normalizedValue_sameExponent_lt_iff_true
    (fmt : FloatingPointFormat) (m n : ℕ) (e : ℤ) :
    fmt.normalizedValue true m e < fmt.normalizedValue true n e ↔
      n < m := by
  rw [fmt.normalizedValue_true_eq_neg_false m e,
    fmt.normalizedValue_true_eq_neg_false n e, neg_lt_neg_iff]
  exact fmt.normalizedValue_sameExponent_lt_iff_false n m e

theorem normalizedValue_sameExponent_no_between_succ
    (fmt : FloatingPointFormat) (negative : Bool) (m k : ℕ) (e : ℤ) :
    ¬ ((fmt.normalizedValue negative m e <
          fmt.normalizedValue negative k e ∧
        fmt.normalizedValue negative k e <
          fmt.normalizedValue negative (m + 1) e) ∨
      (fmt.normalizedValue negative (m + 1) e <
          fmt.normalizedValue negative k e ∧
        fmt.normalizedValue negative k e <
          fmt.normalizedValue negative m e)) := by
  cases negative
  · intro h
    rcases h with hbetween | hbetween
    · rcases hbetween with ⟨hmk_val, hkm1_val⟩
      have hmk : m < k :=
        (fmt.normalizedValue_sameExponent_lt_iff_false m k e).mp hmk_val
      have hkm1 : k < m + 1 :=
        (fmt.normalizedValue_sameExponent_lt_iff_false k (m + 1) e).mp hkm1_val
      exact (not_lt_of_ge (Nat.lt_succ_iff.mp hkm1)) hmk
    · rcases hbetween with ⟨hm1k_val, hkm_val⟩
      have hm1k : m + 1 < k :=
        (fmt.normalizedValue_sameExponent_lt_iff_false (m + 1) k e).mp hm1k_val
      have hkm : k < m :=
        (fmt.normalizedValue_sameExponent_lt_iff_false k m e).mp hkm_val
      have hm_lt_k : m < k := lt_trans (Nat.lt_succ_self m) hm1k
      exact (not_lt_of_ge (le_of_lt hkm)) hm_lt_k
  · intro h
    rcases h with hbetween | hbetween
    · rcases hbetween with ⟨hmk_val, hkm1_val⟩
      have hkm : k < m :=
        (fmt.normalizedValue_sameExponent_lt_iff_true m k e).mp hmk_val
      have hm1k : m + 1 < k :=
        (fmt.normalizedValue_sameExponent_lt_iff_true k (m + 1) e).mp hkm1_val
      have hm_lt_k : m < k := lt_trans (Nat.lt_succ_self m) hm1k
      exact (not_lt_of_ge (le_of_lt hkm)) hm_lt_k
    · rcases hbetween with ⟨hm1k_val, hkm_val⟩
      have hkm1 : k < m + 1 :=
        (fmt.normalizedValue_sameExponent_lt_iff_true (m + 1) k e).mp hm1k_val
      have hmk : m < k :=
        (fmt.normalizedValue_sameExponent_lt_iff_true k m e).mp hkm_val
      exact (not_lt_of_ge (Nat.lt_succ_iff.mp hkm1)) hmk

theorem normalizedValue_false_pos {fmt : FloatingPointFormat} {m : ℕ}
    {e : ℤ} (hm : fmt.normalizedMantissa m) :
    0 < fmt.normalizedValue false m e := by
  simpa [normalizedValue, signValue] using
    mul_pos (Nat.cast_pos.mpr (fmt.normalizedMantissa_pos hm))
      (fmt.betaR_zpow_pos (e - (fmt.t : ℤ)))

theorem normalizedValue_true_neg {fmt : FloatingPointFormat} {m : ℕ}
    {e : ℤ} (hm : fmt.normalizedMantissa m) :
    fmt.normalizedValue true m e < 0 := by
  have hpos := fmt.normalizedValue_false_pos (m := m) (e := e) hm
  simpa [fmt.normalizedValue_true_eq_neg_false m e] using
    (neg_lt_zero.mpr hpos : -fmt.normalizedValue false m e < 0)

theorem normalizedValue_abs_lower_mantissa {fmt : FloatingPointFormat}
    {negative : Bool} {m : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) :
    (fmt.minNormalMantissa : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) ≤
      |fmt.normalizedValue negative m e| := by
  rw [fmt.normalizedValue_abs negative m e]
  exact mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr hm.1)
    (fmt.betaR_zpow_nonneg (e - (fmt.t : ℤ)))

theorem minNormalMantissa_scale_eq (fmt : FloatingPointFormat) (e : ℤ) :
    (fmt.minNormalMantissa : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) =
      fmt.betaR ^ (e - 1) := by
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  have htcast : ((fmt.t - 1 : ℕ) : ℤ) = (fmt.t : ℤ) - 1 := by
    rw [Nat.cast_sub (Nat.succ_le_of_lt fmt.t_pos), Nat.cast_one]
  calc
    (fmt.minNormalMantissa : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) =
        fmt.betaR ^ (((fmt.t - 1 : ℕ) : ℤ)) *
          fmt.betaR ^ (e - (fmt.t : ℤ)) := by
      congr 1
      unfold minNormalMantissa betaR
      rw [zpow_natCast, Nat.cast_pow]
    _ = fmt.betaR ^ (((fmt.t - 1 : ℕ) : ℤ) + (e - (fmt.t : ℤ))) := by
      rw [← zpow_add₀ hbase]
    _ = fmt.betaR ^ (e - 1) := by
      congr 1
      rw [htcast]
      ring

theorem normalizedValue_minNormalMantissa_abs_eq
    (fmt : FloatingPointFormat) (negative : Bool) (e : ℤ) :
    |fmt.normalizedValue negative fmt.minNormalMantissa e| =
      fmt.betaR ^ (e - 1) := by
  rw [fmt.normalizedValue_abs negative fmt.minNormalMantissa e,
    fmt.minNormalMantissa_scale_eq e]

/-- The positive smallest normalized value at exponent `e` is the lower power
endpoint `beta^(e-1)`. -/
theorem normalizedValue_false_minNormalMantissa_eq
    (fmt : FloatingPointFormat) (e : ℤ) :
    fmt.normalizedValue false fmt.minNormalMantissa e =
      fmt.betaR ^ (e - 1) := by
  simpa [normalizedValue, signValue] using fmt.minNormalMantissa_scale_eq e

/-- Shifting one base digit from the exponent into the mantissa preserves the
represented normalized value.  This is the one-step renormalization identity
used by the direct Sterbenz same-exponent branch. -/
theorem normalizedValue_mul_beta_predExponent_eq
    (fmt : FloatingPointFormat) (negative : Bool) (m : ℕ) (e : ℤ) :
    fmt.normalizedValue negative (m * fmt.beta) (e - 1) =
      fmt.normalizedValue negative m e := by
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  have hpow :
      fmt.betaR * fmt.betaR ^ ((e - 1) - (fmt.t : ℤ)) =
        fmt.betaR ^ (e - (fmt.t : ℤ)) := by
    calc
      fmt.betaR * fmt.betaR ^ ((e - 1) - (fmt.t : ℤ)) =
          fmt.betaR ^ (1 : ℤ) *
            fmt.betaR ^ ((e - 1) - (fmt.t : ℤ)) := by
        rw [zpow_one]
      _ = fmt.betaR ^ ((1 : ℤ) + ((e - 1) - (fmt.t : ℤ))) := by
        rw [← zpow_add₀ hbase]
      _ = fmt.betaR ^ (e - (fmt.t : ℤ)) := by
        congr 1
        ring
  have hpow_cast :
      (fmt.beta : ℝ) * fmt.betaR ^ ((e - 1) - (fmt.t : ℤ)) =
        fmt.betaR ^ (e - (fmt.t : ℤ)) := by
    simpa [betaR] using hpow
  cases negative <;>
    simp [normalizedValue, signValue, Nat.cast_mul, mul_assoc, hpow_cast]

/-- Shifting any finite number of base digits from the exponent into the
mantissa preserves the represented normalized value. -/
theorem normalizedValue_mul_beta_pow_subExponent_eq
    (fmt : FloatingPointFormat) (negative : Bool) (m shift : ℕ) (e : ℤ) :
    fmt.normalizedValue negative (m * fmt.beta ^ shift)
        (e - (shift : ℤ)) =
      fmt.normalizedValue negative m e := by
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  have hpow :
      fmt.betaR ^ (shift : ℤ) *
          fmt.betaR ^ ((e - (shift : ℤ)) - (fmt.t : ℤ)) =
        fmt.betaR ^ (e - (fmt.t : ℤ)) := by
    calc
      fmt.betaR ^ (shift : ℤ) *
          fmt.betaR ^ ((e - (shift : ℤ)) - (fmt.t : ℤ)) =
        fmt.betaR ^ ((shift : ℤ) +
          ((e - (shift : ℤ)) - (fmt.t : ℤ))) := by
          rw [← zpow_add₀ hbase]
      _ = fmt.betaR ^ (e - (fmt.t : ℤ)) := by
        congr 1
        ring
  have hpow_cast :
      (fmt.beta : ℝ) ^ shift *
          fmt.betaR ^ ((e - (shift : ℤ)) - (fmt.t : ℤ)) =
        fmt.betaR ^ (e - (fmt.t : ℤ)) := by
    simpa [betaR, zpow_natCast] using hpow
  cases negative <;>
    simp [normalizedValue, signValue, Nat.cast_mul, Nat.cast_pow,
      hpow_cast, mul_assoc]

/-- If a normalized-style value is shifted down exactly to `emin`, then the
same real value is represented by the corresponding subnormal endpoint
coefficient.  No normalized-mantissa hypothesis is needed: this is just the
radix-shift identity used by the shifted Sterbenz endpoint branch. -/
theorem normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
    (fmt : FloatingPointFormat) (negative : Bool) (m shift : ℕ) (e : ℤ)
    (he : e - (shift : ℤ) = fmt.emin) :
    fmt.normalizedValue negative m e =
      fmt.subnormalValue negative (m * fmt.beta ^ shift) := by
  rw [← fmt.normalizedValue_mul_beta_pow_subExponent_eq
    (negative := negative) (m := m) (shift := shift) (e := e)]
  rw [he]
  rfl

theorem normalizedValue_abs_lower_power {fmt : FloatingPointFormat}
    {negative : Bool} {m : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) :
    fmt.betaR ^ (e - 1) ≤ |fmt.normalizedValue negative m e| := by
  rw [← fmt.minNormalMantissa_scale_eq e]
  exact fmt.normalizedValue_abs_lower_mantissa hm

theorem normalizedValue_abs_lt_mantissaBound {fmt : FloatingPointFormat}
    {negative : Bool} {m : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) :
    |fmt.normalizedValue negative m e| <
      fmt.betaR ^ fmt.t * fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  rw [fmt.normalizedValue_abs negative m e]
  have hmant : (m : ℝ) < fmt.betaR ^ fmt.t := by
    simpa [betaR, Nat.cast_pow] using (Nat.cast_lt.mpr hm.2 : (m : ℝ) < (fmt.beta ^ fmt.t : ℕ))
  exact mul_lt_mul_of_pos_right hmant
    (fmt.betaR_zpow_pos (e - (fmt.t : ℤ)))

theorem mantissaBound_scale_eq (fmt : FloatingPointFormat) (e : ℤ) :
    fmt.betaR ^ fmt.t * fmt.betaR ^ (e - (fmt.t : ℤ)) =
      fmt.betaR ^ e := by
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  calc
    fmt.betaR ^ fmt.t * fmt.betaR ^ (e - (fmt.t : ℤ)) =
        fmt.betaR ^ ((fmt.t : ℤ)) * fmt.betaR ^ (e - (fmt.t : ℤ)) := by
      rw [zpow_natCast]
    _ = fmt.betaR ^ ((fmt.t : ℤ) + (e - (fmt.t : ℤ))) := by
      rw [← zpow_add₀ hbase]
    _ = fmt.betaR ^ e := by
      congr 1
      ring

theorem maxNormalMantissa_cast (fmt : FloatingPointFormat) :
    (fmt.maxNormalMantissa : ℝ) = fmt.betaR ^ fmt.t - 1 := by
  unfold maxNormalMantissa betaR
  rw [Nat.cast_sub (Nat.succ_le_of_lt fmt.mantissaBound_pos), Nat.cast_one,
    Nat.cast_pow]

theorem maxNormalMantissa_scale_eq (fmt : FloatingPointFormat) (e : ℤ) :
    (fmt.maxNormalMantissa : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) =
      fmt.betaR ^ e - fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  rw [fmt.maxNormalMantissa_cast]
  calc
    (fmt.betaR ^ fmt.t - 1) * fmt.betaR ^ (e - (fmt.t : ℤ)) =
        fmt.betaR ^ fmt.t * fmt.betaR ^ (e - (fmt.t : ℤ)) -
          fmt.betaR ^ (e - (fmt.t : ℤ)) := by
      ring
    _ = fmt.betaR ^ e - fmt.betaR ^ (e - (fmt.t : ℤ)) := by
      rw [fmt.mantissaBound_scale_eq e]

theorem normalizedValue_maxNormalMantissa_abs_eq_sub
    (fmt : FloatingPointFormat) (negative : Bool) (e : ℤ) :
    |fmt.normalizedValue negative fmt.maxNormalMantissa e| =
      fmt.betaR ^ e - fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  rw [fmt.normalizedValue_abs negative fmt.maxNormalMantissa e,
    fmt.maxNormalMantissa_scale_eq e]

theorem normalizedValue_maxNormalMantissa_abs_eq
    (fmt : FloatingPointFormat) (negative : Bool) (e : ℤ) :
    |fmt.normalizedValue negative fmt.maxNormalMantissa e| =
      fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))) := by
  rw [fmt.normalizedValue_maxNormalMantissa_abs_eq_sub negative e]
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  have hsplit :
      fmt.betaR ^ (e - (fmt.t : ℤ)) =
        fmt.betaR ^ e * fmt.betaR ^ (-(fmt.t : ℤ)) := by
    rw [← zpow_add₀ hbase]
    congr 1
  rw [hsplit]
  ring

/-- The positive largest normalized value at exponent `e` is the upper source
endpoint `beta^e * (1 - beta^(-t))`. -/
theorem normalizedValue_false_maxNormalMantissa_eq
    (fmt : FloatingPointFormat) (e : ℤ) :
    fmt.normalizedValue false fmt.maxNormalMantissa e =
      fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))) := by
  have hsub := fmt.maxNormalMantissa_scale_eq e
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  have hsplit :
      fmt.betaR ^ (e - (fmt.t : ℤ)) =
        fmt.betaR ^ e * fmt.betaR ^ (-(fmt.t : ℤ)) := by
    rw [← zpow_add₀ hbase]
    congr 1
  calc
    fmt.normalizedValue false fmt.maxNormalMantissa e =
        (fmt.maxNormalMantissa : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) := by
      simp [normalizedValue, signValue]
    _ = fmt.betaR ^ e - fmt.betaR ^ (e - (fmt.t : ℤ)) := hsub
    _ = fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))) := by
      rw [hsplit]
      ring

theorem normalizedValue_abs_lt_beta_pow {fmt : FloatingPointFormat}
    {negative : Bool} {m : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) :
    |fmt.normalizedValue negative m e| < fmt.betaR ^ e := by
  rw [← fmt.mantissaBound_scale_eq e]
  exact fmt.normalizedValue_abs_lt_mantissaBound hm

theorem normalizedValue_abs_between_beta_powers {fmt : FloatingPointFormat}
    {negative : Bool} {m : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) :
    fmt.betaR ^ (e - 1) ≤ |fmt.normalizedValue negative m e| ∧
      |fmt.normalizedValue negative m e| < fmt.betaR ^ e :=
  ⟨fmt.normalizedValue_abs_lower_power hm, fmt.normalizedValue_abs_lt_beta_pow hm⟩

theorem normalizedValue_abs_lower_of_exp_ge {fmt : FloatingPointFormat}
    {negative : Bool} {m : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) (he : fmt.emin ≤ e) :
    fmt.betaR ^ (fmt.emin - 1) ≤
      |fmt.normalizedValue negative m e| := by
  exact le_trans
    (fmt.betaR_zpow_le_zpow_of_le (by omega : fmt.emin - 1 ≤ e - 1))
    (fmt.normalizedValue_abs_lower_power hm)

theorem normalizedValue_abs_le_maxNormalMantissa_same_exp
    {fmt : FloatingPointFormat} {negative : Bool} {m : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) :
    |fmt.normalizedValue negative m e| ≤
      |fmt.normalizedValue false fmt.maxNormalMantissa e| := by
  have hle : m ≤ fmt.maxNormalMantissa := by
    unfold maxNormalMantissa
    exact Nat.le_sub_one_of_lt hm.2
  rw [fmt.normalizedValue_abs negative m e,
    fmt.normalizedValue_abs false fmt.maxNormalMantissa e]
  exact mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr hle)
    (fmt.betaR_zpow_nonneg (e - (fmt.t : ℤ)))

theorem normalizedValue_abs_le_maxNormalMantissa_of_exp_le
    {fmt : FloatingPointFormat} {negative : Bool} {m : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) (he : e ≤ fmt.emax) :
    |fmt.normalizedValue negative m e| ≤
      |fmt.normalizedValue false fmt.maxNormalMantissa fmt.emax| := by
  by_cases heq : e = fmt.emax
  · subst e
    exact fmt.normalizedValue_abs_le_maxNormalMantissa_same_exp hm
  · have hlt : e < fmt.emax := lt_of_le_of_ne he heq
    calc
      |fmt.normalizedValue negative m e| ≤ fmt.betaR ^ e :=
        le_of_lt (fmt.normalizedValue_abs_lt_beta_pow hm)
      _ ≤ fmt.betaR ^ (fmt.emax - 1) :=
        fmt.betaR_zpow_le_zpow_of_le (by omega)
      _ = |fmt.normalizedValue false fmt.minNormalMantissa fmt.emax| := by
        rw [fmt.normalizedValue_minNormalMantissa_abs_eq false fmt.emax]
      _ ≤ |fmt.normalizedValue false fmt.maxNormalMantissa fmt.emax| :=
        fmt.normalizedValue_abs_le_maxNormalMantissa_same_exp
          (negative := false) (m := fmt.minNormalMantissa)
          (e := fmt.emax) fmt.minNormalMantissa_normalized

theorem normalizedSystem_abs_lower_bound {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.normalizedSystem y) :
    fmt.betaR ^ (fmt.emin - 1) ≤ |y| := by
  rcases hy with ⟨negative, m, e, hm, he, rfl⟩
  exact fmt.normalizedValue_abs_lower_of_exp_ge hm he.1

theorem normalizedSystem_abs_le_maxNormalMantissa
    {fmt : FloatingPointFormat} {y : ℝ} (hy : fmt.normalizedSystem y) :
    |y| ≤ |fmt.normalizedValue false fmt.maxNormalMantissa fmt.emax| := by
  rcases hy with ⟨negative, m, e, hm, he, rfl⟩
  exact fmt.normalizedValue_abs_le_maxNormalMantissa_of_exp_le hm he.2

theorem normalizedSystem_abs_le_maxFinite_bound
    {fmt : FloatingPointFormat} {y : ℝ} (hy : fmt.normalizedSystem y) :
    |y| ≤ fmt.betaR ^ fmt.emax *
      (1 - fmt.betaR ^ (-(fmt.t : ℤ))) := by
  calc
    |y| ≤ |fmt.normalizedValue false fmt.maxNormalMantissa fmt.emax| :=
      fmt.normalizedSystem_abs_le_maxNormalMantissa hy
    _ = fmt.betaR ^ fmt.emax * (1 - fmt.betaR ^ (-(fmt.t : ℤ))) := by
      rw [fmt.normalizedValue_maxNormalMantissa_abs_eq false fmt.emax]

theorem normalizedSystem_abs_bounds {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.normalizedSystem y) :
    fmt.betaR ^ (fmt.emin - 1) ≤ |y| ∧
      |y| ≤ fmt.betaR ^ fmt.emax *
        (1 - fmt.betaR ^ (-(fmt.t : ℤ))) :=
  ⟨fmt.normalizedSystem_abs_lower_bound hy,
    fmt.normalizedSystem_abs_le_maxFinite_bound hy⟩

/-- The smallest positive normalized magnitude is positive. -/
theorem minNormalMagnitude_pos (fmt : FloatingPointFormat) :
    0 < fmt.minNormalMagnitude := by
  simpa [minNormalMagnitude] using fmt.betaR_zpow_pos (fmt.emin - 1)

/-- The smallest positive subnormal magnitude is positive. -/
theorem minSubnormalMagnitude_pos (fmt : FloatingPointFormat) :
    0 < fmt.minSubnormalMagnitude := by
  simpa [minSubnormalMagnitude] using
    fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ))

/-- The gradual-underflow additive-error bound `u * alpha` is half the
subnormal spacing. -/
theorem unitRoundoff_mul_minNormalMagnitude_eq_half_minSubnormalMagnitude
    (fmt : FloatingPointFormat) :
    fmt.unitRoundoff * fmt.minNormalMagnitude =
      (1 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  unfold unitRoundoff machineEpsilon minNormalMagnitude minSubnormalMagnitude
  calc
    ((1 / 2 : ℝ) * fmt.betaR ^ (1 - (fmt.t : ℤ))) *
        fmt.betaR ^ (fmt.emin - 1) =
        (1 / 2 : ℝ) *
          (fmt.betaR ^ (1 - (fmt.t : ℤ)) *
            fmt.betaR ^ (fmt.emin - 1)) := by
      ring
    _ = (1 / 2 : ℝ) *
          fmt.betaR ^ ((1 - (fmt.t : ℤ)) + (fmt.emin - 1)) := by
      rw [← zpow_add₀ hbase]
    _ = (1 / 2 : ℝ) * fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
      congr 1
      ring_nf

/-- Higham's gradual-underflow `eta` bound is half the subnormal spacing. -/
theorem gradualUnderflowEtaBound_eq_half_minSubnormalMagnitude
    (fmt : FloatingPointFormat) :
    fmt.gradualUnderflowEtaBound =
      (1 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
  simpa [gradualUnderflowEtaBound] using
    fmt.unitRoundoff_mul_minNormalMagnitude_eq_half_minSubnormalMagnitude

/-- The gradual-underflow additive-error bound is positive. -/
theorem gradualUnderflowEtaBound_pos (fmt : FloatingPointFormat) :
    0 < fmt.gradualUnderflowEtaBound := by
  rw [fmt.gradualUnderflowEtaBound_eq_half_minSubnormalMagnitude]
  exact mul_pos (by norm_num) fmt.minSubnormalMagnitude_pos

/-- The gradual-underflow additive-error bound is nonnegative. -/
theorem gradualUnderflowEtaBound_nonneg (fmt : FloatingPointFormat) :
    0 ≤ fmt.gradualUnderflowEtaBound :=
  le_of_lt fmt.gradualUnderflowEtaBound_pos

/-- The flush-to-zero additive-error bound is positive. -/
theorem flushToZeroEtaBound_pos (fmt : FloatingPointFormat) :
    0 < fmt.flushToZeroEtaBound := by
  simpa [flushToZeroEtaBound] using fmt.minNormalMagnitude_pos

/-- The flush-to-zero additive-error bound is nonnegative. -/
theorem flushToZeroEtaBound_nonneg (fmt : FloatingPointFormat) :
    0 ≤ fmt.flushToZeroEtaBound :=
  le_of_lt fmt.flushToZeroEtaBound_pos

/-- The smallest subnormal magnitude is no larger than the smallest normal
magnitude. -/
theorem minSubnormalMagnitude_le_minNormalMagnitude
    (fmt : FloatingPointFormat) :
    fmt.minSubnormalMagnitude ≤ fmt.minNormalMagnitude := by
  have ht : (1 : ℤ) ≤ (fmt.t : ℤ) := by
    exact_mod_cast fmt.t_pos
  simpa [minSubnormalMagnitude, minNormalMagnitude] using
    fmt.betaR_zpow_le_zpow_of_le (by omega : fmt.emin - (fmt.t : ℤ) ≤ fmt.emin - 1)

/-- The largest finite magnitude is at least the smallest normal magnitude. -/
theorem minNormalMagnitude_le_maxFiniteMagnitude
    (fmt : FloatingPointFormat) :
    fmt.minNormalMagnitude ≤ fmt.maxFiniteMagnitude := by
  have h :=
    fmt.normalizedSystem_abs_le_maxFinite_bound
      (fmt.minNormalMantissa_mem_normalizedSystem false)
  simpa [minNormalMagnitude, maxFiniteMagnitude,
    fmt.normalizedValue_minNormalMantissa_abs_eq false fmt.emin] using h

/-- The largest finite magnitude is nonnegative. -/
theorem maxFiniteMagnitude_nonneg (fmt : FloatingPointFormat) :
    0 ≤ fmt.maxFiniteMagnitude :=
  le_trans (le_of_lt fmt.minNormalMagnitude_pos)
    fmt.minNormalMagnitude_le_maxFiniteMagnitude

/-- The smallest subnormal magnitude is nonnegative. -/
theorem minSubnormalMagnitude_nonneg (fmt : FloatingPointFormat) :
    0 ≤ fmt.minSubnormalMagnitude :=
  le_of_lt fmt.minSubnormalMagnitude_pos

/-- The positive smallest normal magnitude is a normalized finite value. -/
theorem minNormalMagnitude_mem_normalizedSystem
    (fmt : FloatingPointFormat) :
    fmt.normalizedSystem fmt.minNormalMagnitude := by
  simpa [minNormalMagnitude,
    fmt.normalizedValue_false_minNormalMantissa_eq fmt.emin] using
    fmt.minNormalMantissa_mem_normalizedSystem false

/-- The positive largest finite magnitude is a normalized finite value. -/
theorem maxFiniteMagnitude_mem_normalizedSystem
    (fmt : FloatingPointFormat) :
    fmt.normalizedSystem fmt.maxFiniteMagnitude := by
  simpa [maxFiniteMagnitude,
    fmt.normalizedValue_false_maxNormalMantissa_eq fmt.emax] using
    fmt.maxNormalMantissa_mem_normalizedSystem false

/-- The largest finite magnitude is strictly below the next power
`beta^emax`. -/
theorem maxFiniteMagnitude_lt_beta_pow_emax
    (fmt : FloatingPointFormat) :
    fmt.maxFiniteMagnitude < fmt.betaR ^ fmt.emax := by
  have h :=
    fmt.normalizedValue_abs_lt_beta_pow
      (negative := false)
      (m := fmt.maxNormalMantissa) (e := fmt.emax)
      fmt.maxNormalMantissa_normalized
  have hpos :=
    fmt.normalizedValue_false_pos
      (m := fmt.maxNormalMantissa) (e := fmt.emax)
      fmt.maxNormalMantissa_normalized
  rw [abs_of_pos hpos] at h
  simpa [maxFiniteMagnitude,
    fmt.normalizedValue_false_maxNormalMantissa_eq fmt.emax] using h

/-- The negative smallest normal endpoint is a normalized finite value. -/
theorem neg_minNormalMagnitude_mem_normalizedSystem
    (fmt : FloatingPointFormat) :
    fmt.normalizedSystem (-fmt.minNormalMagnitude) := by
  have h := fmt.minNormalMantissa_mem_normalizedSystem true
  rw [fmt.normalizedValue_true_eq_neg_false] at h
  simpa [minNormalMagnitude,
    fmt.normalizedValue_false_minNormalMantissa_eq fmt.emin] using h

/-- The negative largest finite endpoint is a normalized finite value. -/
theorem neg_maxFiniteMagnitude_mem_normalizedSystem
    (fmt : FloatingPointFormat) :
    fmt.normalizedSystem (-fmt.maxFiniteMagnitude) := by
  have h := fmt.maxNormalMantissa_mem_normalizedSystem true
  rw [fmt.normalizedValue_true_eq_neg_false] at h
  simpa [maxFiniteMagnitude,
    fmt.normalizedValue_false_maxNormalMantissa_eq fmt.emax] using h

/-- The positive smallest normal magnitude is finite representable. -/
theorem minNormalMagnitude_mem_finiteSystem
    (fmt : FloatingPointFormat) :
    fmt.finiteSystem fmt.minNormalMagnitude :=
  Or.inr (Or.inl fmt.minNormalMagnitude_mem_normalizedSystem)

/-- The positive smallest normal magnitude is in Higham's unbounded normalized
system `G`. -/
theorem minNormalMagnitude_mem_unboundedNormalizedSystem
    (fmt : FloatingPointFormat) :
    fmt.unboundedNormalizedSystem fmt.minNormalMagnitude :=
  fmt.normalizedSystem_unboundedNormalizedSystem
    fmt.minNormalMagnitude_mem_normalizedSystem

/-- The positive largest finite magnitude is finite representable. -/
theorem maxFiniteMagnitude_mem_finiteSystem
    (fmt : FloatingPointFormat) :
    fmt.finiteSystem fmt.maxFiniteMagnitude :=
  Or.inr (Or.inl fmt.maxFiniteMagnitude_mem_normalizedSystem)

/-- The positive largest finite magnitude is in Higham's unbounded normalized
system `G`. -/
theorem maxFiniteMagnitude_mem_unboundedNormalizedSystem
    (fmt : FloatingPointFormat) :
    fmt.unboundedNormalizedSystem fmt.maxFiniteMagnitude :=
  fmt.normalizedSystem_unboundedNormalizedSystem
    fmt.maxFiniteMagnitude_mem_normalizedSystem

/-- The negative smallest normal endpoint is finite representable. -/
theorem neg_minNormalMagnitude_mem_finiteSystem
    (fmt : FloatingPointFormat) :
    fmt.finiteSystem (-fmt.minNormalMagnitude) :=
  Or.inr (Or.inl fmt.neg_minNormalMagnitude_mem_normalizedSystem)

/-- The negative smallest normal endpoint is in Higham's unbounded normalized
system `G`. -/
theorem neg_minNormalMagnitude_mem_unboundedNormalizedSystem
    (fmt : FloatingPointFormat) :
    fmt.unboundedNormalizedSystem (-fmt.minNormalMagnitude) :=
  fmt.normalizedSystem_unboundedNormalizedSystem
    fmt.neg_minNormalMagnitude_mem_normalizedSystem

/-- The negative largest finite endpoint is finite representable. -/
theorem neg_maxFiniteMagnitude_mem_finiteSystem
    (fmt : FloatingPointFormat) :
    fmt.finiteSystem (-fmt.maxFiniteMagnitude) :=
  Or.inr (Or.inl fmt.neg_maxFiniteMagnitude_mem_normalizedSystem)

/-- The negative largest finite endpoint is in Higham's unbounded normalized
system `G`. -/
theorem neg_maxFiniteMagnitude_mem_unboundedNormalizedSystem
    (fmt : FloatingPointFormat) :
    fmt.unboundedNormalizedSystem (-fmt.maxFiniteMagnitude) :=
  fmt.normalizedSystem_unboundedNormalizedSystem
    fmt.neg_maxFiniteMagnitude_mem_normalizedSystem

/-- Normalized finite values lie in the source-facing finite normal range. -/
theorem normalizedSystem_finiteNormalRange
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.normalizedSystem y) :
    fmt.finiteNormalRange y := by
  rcases fmt.normalizedSystem_abs_bounds hy with ⟨hlo, hhi⟩
  exact ⟨by simpa [minNormalMagnitude] using hlo,
    by simpa [maxFiniteMagnitude] using hhi⟩

/-- An unbounded normalized value whose magnitude lies in the finite normal
range is actually a bounded normalized finite value. -/
theorem unboundedNormalizedSystem_normalizedSystem_of_finiteNormalRange
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.unboundedNormalizedSystem y)
    (hrange : fmt.finiteNormalRange y) :
    fmt.normalizedSystem y := by
  rcases hy with ⟨negative, m, e, hm, rfl⟩
  have hemin : fmt.emin ≤ e := by
    by_contra hnot
    have he_lt : e < fmt.emin := lt_of_not_ge hnot
    have hpow_le :
        fmt.betaR ^ e ≤ fmt.betaR ^ (fmt.emin - 1) :=
      fmt.betaR_zpow_le_zpow_of_le (by omega : e ≤ fmt.emin - 1)
    have hlt :
        |fmt.normalizedValue negative m e| < fmt.minNormalMagnitude := by
      calc
        |fmt.normalizedValue negative m e| < fmt.betaR ^ e :=
          fmt.normalizedValue_abs_lt_beta_pow hm
        _ ≤ fmt.betaR ^ (fmt.emin - 1) := hpow_le
        _ = fmt.minNormalMagnitude := by rfl
    exact not_lt_of_ge hrange.1 hlt
  have hemax : e ≤ fmt.emax := by
    by_contra hnot
    have hlt : fmt.emax < e := lt_of_not_ge hnot
    have hpow_le :
        fmt.betaR ^ fmt.emax ≤ fmt.betaR ^ (e - 1) :=
      fmt.betaR_zpow_le_zpow_of_le (by omega : fmt.emax ≤ e - 1)
    have hmax_lt :
        fmt.maxFiniteMagnitude <
          |fmt.normalizedValue negative m e| := by
      exact lt_of_lt_of_le
        (lt_of_lt_of_le fmt.maxFiniteMagnitude_lt_beta_pow_emax hpow_le)
        (fmt.normalizedValue_abs_lower_power hm)
    exact not_lt_of_ge hrange.2 hmax_lt
  exact ⟨negative, m, e, hm, ⟨hemin, hemax⟩, rfl⟩

/-- Normalized finite values are not in the source-facing underflow range. -/
theorem normalizedSystem_not_finiteUnderflowRange
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.normalizedSystem y) :
    ¬ fmt.finiteUnderflowRange y :=
  not_lt_of_ge (fmt.normalizedSystem_finiteNormalRange hy).1

/-- Normalized finite values are not in the source-facing overflow range. -/
theorem normalizedSystem_not_finiteOverflowRange
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.normalizedSystem y) :
    ¬ fmt.finiteOverflowRange y :=
  not_lt_of_ge (fmt.normalizedSystem_finiteNormalRange hy).2

/-- Normalized finite values have magnitude at least the smallest subnormal. -/
theorem normalizedSystem_abs_ge_minSubnormalMagnitude
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.normalizedSystem y) :
    fmt.minSubnormalMagnitude ≤ |y| :=
  le_trans fmt.minSubnormalMagnitude_le_minNormalMagnitude
    (fmt.normalizedSystem_finiteNormalRange hy).1

theorem normalizedExponentRepresentation_abs_lower_power
    {fmt : FloatingPointFormat} {y : ℝ} {e : ℤ}
    (h : fmt.normalizedExponentRepresentation y e) :
    fmt.betaR ^ (e - 1) ≤ |y| := by
  rcases h with ⟨negative, m, hm, _he, rfl⟩
  exact fmt.normalizedValue_abs_lower_power hm

theorem normalizedExponentRepresentation_abs_lt_beta_pow
    {fmt : FloatingPointFormat} {y : ℝ} {e : ℤ}
    (h : fmt.normalizedExponentRepresentation y e) :
    |y| < fmt.betaR ^ e := by
  rcases h with ⟨negative, m, hm, _he, rfl⟩
  exact fmt.normalizedValue_abs_lt_beta_pow hm

theorem fergusonExponentCondition_sub_not_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.fergusonExponentCondition x y) :
    ¬ fmt.finiteUnderflowRange (x - y) :=
  fmt.normalizedSystem_not_finiteUnderflowRange
    (fmt.fergusonExponentCondition_sub_normalized h)

theorem fergusonExponentCondition_sub_not_finiteOverflowRange
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.fergusonExponentCondition x y) :
    ¬ fmt.finiteOverflowRange (x - y) :=
  fmt.normalizedSystem_not_finiteOverflowRange
    (fmt.fergusonExponentCondition_sub_normalized h)

theorem betaR_zpow_add_one_le_of_two_mul
    (fmt : FloatingPointFormat) (e : ℤ) :
    2 * fmt.betaR ^ e ≤ fmt.betaR ^ (e + 1) := by
  have hb : (2 : ℝ) ≤ fmt.betaR := by
    unfold betaR
    exact_mod_cast fmt.beta_ge_two
  have hpow_nonneg : 0 ≤ fmt.betaR ^ e :=
    fmt.betaR_zpow_nonneg e
  have hmul : 2 * fmt.betaR ^ e ≤ fmt.betaR * fmt.betaR ^ e :=
    mul_le_mul_of_nonneg_right hb hpow_nonneg
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  calc
    2 * fmt.betaR ^ e ≤ fmt.betaR * fmt.betaR ^ e := hmul
    _ = fmt.betaR ^ (1 : ℤ) * fmt.betaR ^ e := by
      rw [zpow_one]
    _ = fmt.betaR ^ ((1 : ℤ) + e) := by
      rw [← zpow_add₀ hbase]
    _ = fmt.betaR ^ (e + 1) := by
      congr 1
      omega

theorem normalizedExponentRepresentation_sub_exponent_gap_le_one
    {fmt : FloatingPointFormat} {x y : ℝ} {ex ey ez : ℤ}
    (hx : fmt.normalizedExponentRepresentation x ex)
    (hy : fmt.normalizedExponentRepresentation y ey)
    (hz : fmt.normalizedExponentRepresentation (x - y) ez)
    (hcond : ez < min ex ey) :
    ex ≤ ey + 1 ∧ ey ≤ ex + 1 := by
  have hx_upper : |x| < fmt.betaR ^ ex :=
    fmt.normalizedExponentRepresentation_abs_lt_beta_pow hx
  have hy_upper : |y| < fmt.betaR ^ ey :=
    fmt.normalizedExponentRepresentation_abs_lt_beta_pow hy
  have hx_lower : fmt.betaR ^ (ex - 1) ≤ |x| :=
    fmt.normalizedExponentRepresentation_abs_lower_power hx
  have hy_lower : fmt.betaR ^ (ey - 1) ≤ |y| :=
    fmt.normalizedExponentRepresentation_abs_lower_power hy
  have hz_upper : |x - y| < fmt.betaR ^ ez :=
    fmt.normalizedExponentRepresentation_abs_lt_beta_pow hz
  have hlt_ex : ez < ex := lt_of_lt_of_le hcond (min_le_left ex ey)
  have hlt_ey : ez < ey := lt_of_lt_of_le hcond (min_le_right ex ey)
  have hz_lt_ex : |x - y| < fmt.betaR ^ ex :=
    lt_of_lt_of_le hz_upper
      (fmt.betaR_zpow_le_zpow_of_le (le_of_lt hlt_ex))
  have hz_lt_ey : |x - y| < fmt.betaR ^ ey :=
    lt_of_lt_of_le hz_upper
      (fmt.betaR_zpow_le_zpow_of_le (le_of_lt hlt_ey))
  constructor
  · by_contra hnot
    have hgap : ey + 1 < ex := by omega
    have hx_big : fmt.betaR ^ (ey + 1) ≤ |x| := by
      exact le_trans
        (fmt.betaR_zpow_le_zpow_of_le (by omega : ey + 1 ≤ ex - 1))
        hx_lower
    have hx_two : 2 * fmt.betaR ^ ey ≤ |x| :=
      le_trans (fmt.betaR_zpow_add_one_le_of_two_mul ey) hx_big
    have hsum_lt :
        fmt.betaR ^ ey + |y| < fmt.betaR ^ ey + fmt.betaR ^ ey := by
      simpa [add_comm] using add_lt_add_right hy_upper (fmt.betaR ^ ey)
    have htwo_eq : 2 * fmt.betaR ^ ey = fmt.betaR ^ ey + fmt.betaR ^ ey := by
      ring
    have hsum_le_x : fmt.betaR ^ ey + fmt.betaR ^ ey ≤ |x| := by
      simpa [htwo_eq] using hx_two
    have hdiff_lt : fmt.betaR ^ ey < |x| - |y| := by
      linarith
    have htriangle : |x| - |y| ≤ |x - y| := by
      exact abs_sub_abs_le_abs_sub x y
    have hlarge : fmt.betaR ^ ey < |x - y| := lt_of_lt_of_le hdiff_lt htriangle
    exact not_lt_of_ge (le_of_lt hlarge) hz_lt_ey
  · by_contra hnot
    have hgap : ex + 1 < ey := by omega
    have hy_big : fmt.betaR ^ (ex + 1) ≤ |y| := by
      exact le_trans
        (fmt.betaR_zpow_le_zpow_of_le (by omega : ex + 1 ≤ ey - 1))
        hy_lower
    have hy_two : 2 * fmt.betaR ^ ex ≤ |y| :=
      le_trans (fmt.betaR_zpow_add_one_le_of_two_mul ex) hy_big
    have hsum_lt :
        fmt.betaR ^ ex + |x| < fmt.betaR ^ ex + fmt.betaR ^ ex := by
      simpa [add_comm] using add_lt_add_right hx_upper (fmt.betaR ^ ex)
    have htwo_eq : 2 * fmt.betaR ^ ex = fmt.betaR ^ ex + fmt.betaR ^ ex := by
      ring
    have hsum_le_y : fmt.betaR ^ ex + fmt.betaR ^ ex ≤ |y| := by
      simpa [htwo_eq] using hy_two
    have hdiff_lt : fmt.betaR ^ ex < |y| - |x| := by
      linarith
    have htriangle : |y| - |x| ≤ |x - y| := by
      have htri_yx : |y| - |x| ≤ |y - x| := abs_sub_abs_le_abs_sub y x
      have htri_xy : |y| - |x| ≤ |x - y| := by
        simpa [abs_sub_comm] using htri_yx
      exact htri_xy
    have hlarge : fmt.betaR ^ ex < |x - y| := lt_of_lt_of_le hdiff_lt htriangle
    exact not_lt_of_ge (le_of_lt hlarge) hz_lt_ex

theorem normalizedValue_sub_fergusonCondition_sign_eq
    {fmt : FloatingPointFormat} {negativeX negativeY : Bool}
    {mx my : ℕ} {ex ey ez : ℤ}
    (hmx : fmt.normalizedMantissa mx)
    (hmy : fmt.normalizedMantissa my)
    (hz : fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negativeX mx ex -
        fmt.normalizedValue negativeY my ey) ez)
    (hcond : ez < min ex ey) :
    negativeX = negativeY := by
  let z :=
    fmt.normalizedValue negativeX mx ex -
      fmt.normalizedValue negativeY my ey
  have hz_upper : |z| < fmt.betaR ^ ez := by
    simpa [z] using fmt.normalizedExponentRepresentation_abs_lt_beta_pow hz
  have hlt_ex : ez < ex := lt_of_lt_of_le hcond (min_le_left ex ey)
  have hz_lt_ex_lower : |z| < fmt.betaR ^ (ex - 1) :=
    lt_of_lt_of_le hz_upper
      (fmt.betaR_zpow_le_zpow_of_le (by omega : ez ≤ ex - 1))
  cases negativeX <;> cases negativeY
  · rfl
  · exfalso
    have hxpos := fmt.normalizedValue_false_pos (m := mx) (e := ex) hmx
    have hyneg := fmt.normalizedValue_true_neg (m := my) (e := ey) hmy
    have hle : |fmt.normalizedValue false mx ex| ≤
        |fmt.normalizedValue false mx ex -
          fmt.normalizedValue true my ey| := by
      rw [abs_of_pos hxpos]
      have hdiff_nonneg :
          0 ≤ fmt.normalizedValue false mx ex -
            fmt.normalizedValue true my ey := by
        linarith
      rw [abs_of_nonneg hdiff_nonneg]
      linarith
    have hx_lower :
        fmt.betaR ^ (ex - 1) ≤ |fmt.normalizedValue false mx ex| :=
      fmt.normalizedValue_abs_lower_power hmx
    have hbig :
        fmt.betaR ^ (ex - 1) ≤
          |fmt.normalizedValue false mx ex -
            fmt.normalizedValue true my ey| :=
      le_trans hx_lower hle
    exact (not_lt_of_ge hbig) (by simpa [z] using hz_lt_ex_lower)
  · exfalso
    have hxneg := fmt.normalizedValue_true_neg (m := mx) (e := ex) hmx
    have hypos := fmt.normalizedValue_false_pos (m := my) (e := ey) hmy
    have hle : |fmt.normalizedValue true mx ex| ≤
        |fmt.normalizedValue true mx ex -
          fmt.normalizedValue false my ey| := by
      rw [abs_of_neg hxneg]
      have hdiff_nonpos :
          fmt.normalizedValue true mx ex -
            fmt.normalizedValue false my ey ≤ 0 := by
        linarith
      rw [abs_of_nonpos hdiff_nonpos]
      linarith
    have hx_lower :
        fmt.betaR ^ (ex - 1) ≤ |fmt.normalizedValue true mx ex| :=
      fmt.normalizedValue_abs_lower_power hmx
    have hbig :
        fmt.betaR ^ (ex - 1) ≤
          |fmt.normalizedValue true mx ex -
            fmt.normalizedValue false my ey| :=
      le_trans hx_lower hle
    exact (not_lt_of_ge hbig) (by simpa [z] using hz_lt_ex_lower)
  · rfl

theorem fergusonExponentCondition_exponent_gap_le_one
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.fergusonExponentCondition x y) :
    ∃ ex ey : ℤ,
      fmt.normalizedExponentRepresentation x ex ∧
      fmt.normalizedExponentRepresentation y ey ∧
      ex ≤ ey + 1 ∧ ey ≤ ex + 1 := by
  rcases h with ⟨ex, ey, ez, hx, hy, hz, hcond⟩
  rcases fmt.normalizedExponentRepresentation_sub_exponent_gap_le_one
      hx hy hz hcond with ⟨hxy, hyx⟩
  exact ⟨ex, ey, hx, hy, hxy, hyx⟩

theorem fergusonExponentCondition_same_sign_and_exponent_gap
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.fergusonExponentCondition x y) :
    ∃ negative mx my ex ey,
      fmt.normalizedMantissa mx ∧
      fmt.exponentInRange ex ∧
      x = fmt.normalizedValue negative mx ex ∧
      fmt.normalizedMantissa my ∧
      fmt.exponentInRange ey ∧
      y = fmt.normalizedValue negative my ey ∧
      ex ≤ ey + 1 ∧ ey ≤ ex + 1 := by
  rcases h with ⟨ex, ey, ez, hx, hy, hz, hcond⟩
  rcases hx with ⟨negativeX, mx, hmx, hex, hx_eq⟩
  rcases hy with ⟨negativeY, my, hmy, hey, hy_eq⟩
  subst x
  subst y
  have hsign : negativeX = negativeY :=
    fmt.normalizedValue_sub_fergusonCondition_sign_eq
      (negativeX := negativeX) (negativeY := negativeY)
      (mx := mx) (my := my) (ex := ex) (ey := ey) (ez := ez)
      hmx hmy hz hcond
  subst negativeY
  have hx_repr :
      fmt.normalizedExponentRepresentation
        (fmt.normalizedValue negativeX mx ex) ex :=
    ⟨negativeX, mx, hmx, hex, rfl⟩
  have hy_repr :
      fmt.normalizedExponentRepresentation
        (fmt.normalizedValue negativeX my ey) ey :=
    ⟨negativeX, my, hmy, hey, rfl⟩
  rcases fmt.normalizedExponentRepresentation_sub_exponent_gap_le_one
      hx_repr hy_repr hz hcond with ⟨hxy, hyx⟩
  exact ⟨negativeX, mx, my, ex, ey, hmx, hex, rfl, hmy, hey, rfl, hxy, hyx⟩

theorem fergusonExponentCondition_same_sign_exponent_cases
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.fergusonExponentCondition x y) :
    ∃ negative mx my ex ey,
      fmt.normalizedMantissa mx ∧
      fmt.exponentInRange ex ∧
      x = fmt.normalizedValue negative mx ex ∧
      fmt.normalizedMantissa my ∧
      fmt.exponentInRange ey ∧
      y = fmt.normalizedValue negative my ey ∧
      (ex = ey ∨ ex = ey + 1 ∨ ey = ex + 1) := by
  rcases fmt.fergusonExponentCondition_same_sign_and_exponent_gap h with
    ⟨negative, mx, my, ex, ey, hmx, hex, hx, hmy, hey, hy, hxy, hyx⟩
  have hcases : ex = ey ∨ ex = ey + 1 ∨ ey = ex + 1 := by
    omega
  exact ⟨negative, mx, my, ex, ey, hmx, hex, hx, hmy, hey, hy, hcases⟩

/-- Raw aligned subtraction value when two normalized mantissas have the same
exponent and sign.  This is the exact arithmetic identity before any
renormalization or rounding decision. -/
def alignedSameExponentSubtractionValue
    (fmt : FloatingPointFormat) (negative : Bool) (m n : ℕ) (e : ℤ) : ℝ :=
  fmt.signValue negative * ((m : ℝ) - (n : ℝ)) *
    fmt.betaR ^ (e - (fmt.t : ℤ))

theorem normalizedValue_sub_sameSign_sameExponent_eq_aligned
    (fmt : FloatingPointFormat) (negative : Bool) (m n : ℕ) (e : ℤ) :
    fmt.normalizedValue negative m e - fmt.normalizedValue negative n e =
      fmt.alignedSameExponentSubtractionValue negative m n e := by
  cases negative <;>
    simp [alignedSameExponentSubtractionValue, normalizedValue, signValue] <;>
    ring

/-- Integer coefficient for same-exponent aligned subtraction. -/
def sameExponentMantissaDiffInt
    (_fmt : FloatingPointFormat) (m n : ℕ) : ℤ :=
  (m : ℤ) - (n : ℤ)

theorem sameExponentMantissaDiffInt_cast
    (fmt : FloatingPointFormat) (m n : ℕ) :
    ((fmt.sameExponentMantissaDiffInt m n : ℤ) : ℝ) =
      (m : ℝ) - (n : ℝ) := by
  simp [sameExponentMantissaDiffInt]

theorem sameExponentMantissaDiffInt_natAbs_lt_mantissaBound
    {fmt : FloatingPointFormat} {m n : ℕ}
    (hm : fmt.mantissaInRange m) (hn : fmt.mantissaInRange n) :
    (fmt.sameExponentMantissaDiffInt m n).natAbs < fmt.beta ^ fmt.t := by
  have hmInt : (m : ℤ) < (fmt.beta ^ fmt.t : ℤ) := by
    exact_mod_cast hm
  have hnInt : (n : ℤ) < (fmt.beta ^ fmt.t : ℤ) := by
    exact_mod_cast hn
  have habs :
      |(m : ℤ) - (n : ℤ)| < (fmt.beta ^ fmt.t : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have hnatInt :
      (((((m : ℤ) - (n : ℤ)).natAbs : ℕ) : ℤ) <
        (fmt.beta ^ fmt.t : ℤ)) := by
    simpa [Int.natCast_natAbs] using habs
  have hnat : (((m : ℤ) - (n : ℤ)).natAbs < fmt.beta ^ fmt.t) := by
    exact_mod_cast hnatInt
  simpa [sameExponentMantissaDiffInt] using hnat

/-- Raw aligned subtraction value when the first normalized mantissa has
exponent `e + 1`, the second has exponent `e`, and the signs agree.  The
factor `beta*mHigh - mLow` is the t+1 digit guard-aligned mantissa difference
from the Ferguson proof. -/
def guardAlignedMantissaDiff
    (fmt : FloatingPointFormat) (mHigh mLow : ℕ) : ℝ :=
  fmt.betaR * (mHigh : ℝ) - (mLow : ℝ)

/-- Integer form of the guard-aligned coefficient `beta*mHigh - mLow`.
This is the coefficient whose base-`beta` digits are formed before the final
t-digit rounding step in Ferguson's proof. -/
def guardAlignedMantissaDiffInt
    (fmt : FloatingPointFormat) (mHigh mLow : ℕ) : ℤ :=
  ((fmt.beta * mHigh : ℕ) : ℤ) - (mLow : ℤ)

theorem guardAlignedMantissaDiffInt_cast
    (fmt : FloatingPointFormat) (mHigh mLow : ℕ) :
    ((fmt.guardAlignedMantissaDiffInt mHigh mLow : ℤ) : ℝ) =
      fmt.guardAlignedMantissaDiff mHigh mLow := by
  simp [guardAlignedMantissaDiffInt, guardAlignedMantissaDiff, betaR]

def alignedAdjacentExponentSubtractionValue
    (fmt : FloatingPointFormat) (negative : Bool) (mHigh mLow : ℕ)
    (e : ℤ) : ℝ :=
  fmt.signValue negative *
    (fmt.guardAlignedMantissaDiff mHigh mLow *
      fmt.betaR ^ (e - (fmt.t : ℤ)))

theorem normalizedValue_sub_sameSign_adjacentExponent_eq_aligned
    (fmt : FloatingPointFormat) (negative : Bool) (mHigh mLow : ℕ)
    (e : ℤ) :
    fmt.normalizedValue negative mHigh (e + 1) -
        fmt.normalizedValue negative mLow e =
      fmt.alignedAdjacentExponentSubtractionValue negative mHigh mLow e := by
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  have hpow :
      fmt.betaR ^ ((e + 1) - (fmt.t : ℤ)) =
        fmt.betaR * fmt.betaR ^ (e - (fmt.t : ℤ)) := by
    calc
      fmt.betaR ^ ((e + 1) - (fmt.t : ℤ)) =
          fmt.betaR ^ ((e - (fmt.t : ℤ)) + 1) := by
        congr 1
        ring
      _ = fmt.betaR ^ (e - (fmt.t : ℤ)) * fmt.betaR ^ (1 : ℤ) := by
        rw [zpow_add₀ hbase]
      _ = fmt.betaR * fmt.betaR ^ (e - (fmt.t : ℤ)) := by
        rw [zpow_one]
        ring
  cases negative <;>
    simp [alignedAdjacentExponentSubtractionValue, normalizedValue, signValue,
      guardAlignedMantissaDiff, hpow] <;>
    ring

theorem alignedAdjacentExponentSubtractionValue_abs
    (fmt : FloatingPointFormat) (negative : Bool) (mHigh mLow : ℕ)
    (e : ℤ) :
    |fmt.alignedAdjacentExponentSubtractionValue negative mHigh mLow e| =
      |fmt.guardAlignedMantissaDiff mHigh mLow| *
        fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  rw [alignedAdjacentExponentSubtractionValue, abs_mul, abs_mul,
    fmt.signValue_abs negative,
    abs_of_pos (fmt.betaR_zpow_pos (e - (fmt.t : ℤ)))]
  ring

theorem guardAlignedMantissaDiff_abs_lt_minNormalMantissa_of_fergusonAdjacent
    {fmt : FloatingPointFormat} {negative : Bool} {mHigh mLow : ℕ}
    {e ez : ℤ}
    (hz : fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negative mHigh (e + 1) -
        fmt.normalizedValue negative mLow e) ez)
    (hcond : ez < e) :
    |fmt.guardAlignedMantissaDiff mHigh mLow| <
      (fmt.minNormalMantissa : ℝ) := by
  have hz_upper :
      |fmt.normalizedValue negative mHigh (e + 1) -
        fmt.normalizedValue negative mLow e| < fmt.betaR ^ ez :=
    fmt.normalizedExponentRepresentation_abs_lt_beta_pow hz
  have hz_lt_lower :
      |fmt.normalizedValue negative mHigh (e + 1) -
        fmt.normalizedValue negative mLow e| < fmt.betaR ^ (e - 1) :=
    lt_of_lt_of_le hz_upper
      (fmt.betaR_zpow_le_zpow_of_le (by omega : ez ≤ e - 1))
  have hvalue :=
    fmt.normalizedValue_sub_sameSign_adjacentExponent_eq_aligned
      negative mHigh mLow e
  have hscale_pos : 0 < fmt.betaR ^ (e - (fmt.t : ℤ)) :=
    fmt.betaR_zpow_pos (e - (fmt.t : ℤ))
  have hscaled :
      |fmt.guardAlignedMantissaDiff mHigh mLow| *
          fmt.betaR ^ (e - (fmt.t : ℤ)) <
        (fmt.minNormalMantissa : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)) := by
    rw [← fmt.alignedAdjacentExponentSubtractionValue_abs negative mHigh mLow e]
    rw [← hvalue]
    simpa [fmt.minNormalMantissa_scale_eq e] using hz_lt_lower
  exact lt_of_mul_lt_mul_right hscaled (le_of_lt hscale_pos)

theorem guardAlignedMantissaDiffInt_abs_lt_minNormalMantissa_of_fergusonAdjacent
    {fmt : FloatingPointFormat} {negative : Bool} {mHigh mLow : ℕ}
    {e ez : ℤ}
    (hz : fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negative mHigh (e + 1) -
        fmt.normalizedValue negative mLow e) ez)
    (hcond : ez < e) :
    |fmt.guardAlignedMantissaDiffInt mHigh mLow| <
      (fmt.minNormalMantissa : ℤ) := by
  have hreal :
      |((fmt.guardAlignedMantissaDiffInt mHigh mLow : ℤ) : ℝ)| <
        (fmt.minNormalMantissa : ℝ) := by
    simpa [fmt.guardAlignedMantissaDiffInt_cast mHigh mLow] using
      fmt.guardAlignedMantissaDiff_abs_lt_minNormalMantissa_of_fergusonAdjacent
        (negative := negative) (mHigh := mHigh) (mLow := mLow)
        (e := e) (ez := ez) hz hcond
  exact_mod_cast hreal

theorem guardAlignedMantissaDiffInt_natAbs_lt_minNormalMantissa_of_fergusonAdjacent
    {fmt : FloatingPointFormat} {negative : Bool} {mHigh mLow : ℕ}
    {e ez : ℤ}
    (hz : fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negative mHigh (e + 1) -
        fmt.normalizedValue negative mLow e) ez)
    (hcond : ez < e) :
    (fmt.guardAlignedMantissaDiffInt mHigh mLow).natAbs <
      fmt.minNormalMantissa := by
  have hint :
      |fmt.guardAlignedMantissaDiffInt mHigh mLow| <
        (fmt.minNormalMantissa : ℤ) :=
    fmt.guardAlignedMantissaDiffInt_abs_lt_minNormalMantissa_of_fergusonAdjacent
      (negative := negative) (mHigh := mHigh) (mLow := mLow)
      (e := e) (ez := ez) hz hcond
  have hnatInt :
      (((fmt.guardAlignedMantissaDiffInt mHigh mLow).natAbs : ℕ) : ℤ) <
        (fmt.minNormalMantissa : ℤ) := by
    simpa using hint
  exact_mod_cast hnatInt

/-- In the positive adjacent-exponent Sterbenz branch, the guard-aligned
coefficient is positive: the higher-exponent normalized operand is already
larger than the lower-exponent one. -/
theorem guardAlignedMantissaDiffInt_pos_of_adjacentNormalizedMantissas
    {fmt : FloatingPointFormat} {mHigh mLow : ℕ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow) :
    0 < fmt.guardAlignedMantissaDiffInt mHigh mLow := by
  have hlow_lt_coeff : mLow < fmt.beta * mHigh := by
    calc
      mLow < fmt.beta ^ fmt.t := hmLow.2
      _ = fmt.minNormalMantissa * fmt.beta :=
          fmt.minNormalMantissa_mul_beta_eq_mantissaBound.symm
      _ = fmt.beta * fmt.minNormalMantissa := by rw [Nat.mul_comm]
      _ ≤ fmt.beta * mHigh := Nat.mul_le_mul_left fmt.beta hmHigh.1
  dsimp [guardAlignedMantissaDiffInt]
  omega

/-- Direct Sterbenz adjacent-branch coefficient bound.  If positive
same-sign operands have adjacent exponents and satisfy the Sterbenz ratio
condition, then the guard-aligned integer coefficient `beta*mHigh - mLow` has
at most `t` base-`beta` digits. -/
theorem guardAlignedMantissaDiffInt_natAbs_lt_mantissaBound_of_sterbenzAdjacent
    {fmt : FloatingPointFormat} {mHigh mLow : ℕ} {e : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (hsterbenz : fmt.sterbenzRatioCondition
      (fmt.normalizedValue false mHigh (e + 1))
      (fmt.normalizedValue false mLow e)) :
    (fmt.guardAlignedMantissaDiffInt mHigh mLow).natAbs <
      fmt.beta ^ fmt.t := by
  let s := fmt.betaR ^ (e - (fmt.t : ℤ))
  have hs_pos : 0 < s := fmt.betaR_zpow_pos (e - (fmt.t : ℤ))
  have hx_expr :
      fmt.normalizedValue false mHigh (e + 1) =
        ((fmt.beta : ℝ) * (mHigh : ℝ)) * s := by
    have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
    have hpow :
        fmt.betaR ^ ((e + 1) - (fmt.t : ℤ)) =
          fmt.betaR * s := by
      calc
        fmt.betaR ^ ((e + 1) - (fmt.t : ℤ)) =
            fmt.betaR ^ ((e - (fmt.t : ℤ)) + 1) := by
              congr 1
              ring
        _ = fmt.betaR ^ (e - (fmt.t : ℤ)) * fmt.betaR ^ (1 : ℤ) := by
              rw [zpow_add₀ hbase]
        _ = fmt.betaR * s := by
              rw [zpow_one]
              ring
    calc
      fmt.normalizedValue false mHigh (e + 1) =
          (mHigh : ℝ) *
            fmt.betaR ^ ((e + 1) - (fmt.t : ℤ)) := by
            simp [normalizedValue, signValue]
      _ = (mHigh : ℝ) * (fmt.betaR * s) := by rw [hpow]
      _ = ((fmt.beta : ℝ) * (mHigh : ℝ)) * s := by
            simp [betaR]
            ring
  have hy_expr :
      fmt.normalizedValue false mLow e = (mLow : ℝ) * s := by
    simp [normalizedValue, signValue, s]
  have hcoeff_real :
      (fmt.beta : ℝ) * (mHigh : ℝ) < 2 * (mLow : ℝ) := by
    have hxlt := hsterbenz.2
    rw [hx_expr, hy_expr] at hxlt
    have hxlt' :
        ((fmt.beta : ℝ) * (mHigh : ℝ)) * s <
          (2 * (mLow : ℝ)) * s := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hxlt
    exact lt_of_mul_lt_mul_right hxlt' (le_of_lt hs_pos)
  have hcoeff_nat : fmt.beta * mHigh < 2 * mLow := by
    exact_mod_cast hcoeff_real
  have hlow_lt_coeff : mLow < fmt.beta * mHigh := by
    calc
      mLow < fmt.beta ^ fmt.t := hmLow.2
      _ = fmt.minNormalMantissa * fmt.beta :=
          fmt.minNormalMantissa_mul_beta_eq_mantissaBound.symm
      _ = fmt.beta * fmt.minNormalMantissa := by rw [Nat.mul_comm]
      _ ≤ fmt.beta * mHigh := Nat.mul_le_mul_left fmt.beta hmHigh.1
  have hdiff_lt_low : fmt.beta * mHigh - mLow < mLow := by
    omega
  have hdiff_lt_bound :
      fmt.beta * mHigh - mLow < fmt.beta ^ fmt.t :=
    lt_trans hdiff_lt_low hmLow.2
  have hguard_eq :
      ((fmt.beta * mHigh - mLow : ℕ) : ℝ) =
        fmt.guardAlignedMantissaDiff mHigh mLow := by
    rw [Nat.cast_sub (le_of_lt hlow_lt_coeff)]
    simp [guardAlignedMantissaDiff, betaR, Nat.cast_mul]
  have hguard_pos :
      0 < fmt.guardAlignedMantissaDiff mHigh mLow := by
    rw [← hguard_eq]
    exact_mod_cast Nat.sub_pos_of_lt hlow_lt_coeff
  have hguard_lt_bound :
      fmt.guardAlignedMantissaDiff mHigh mLow <
        (fmt.beta ^ fmt.t : ℝ) := by
    rw [← hguard_eq]
    exact_mod_cast hdiff_lt_bound
  have hreal :
      |((fmt.guardAlignedMantissaDiffInt mHigh mLow : ℤ) : ℝ)| <
        (fmt.beta ^ fmt.t : ℝ) := by
    rw [fmt.guardAlignedMantissaDiffInt_cast mHigh mLow]
    rw [abs_of_pos hguard_pos]
    exact hguard_lt_bound
  have hint :
      |fmt.guardAlignedMantissaDiffInt mHigh mLow| <
        (fmt.beta ^ fmt.t : ℤ) := by
    exact_mod_cast hreal
  have hnatInt :
      (((fmt.guardAlignedMantissaDiffInt mHigh mLow).natAbs : ℕ) : ℤ) <
        (fmt.beta ^ fmt.t : ℤ) := by
    simpa using hint
  exact_mod_cast hnatInt

/-- The leading digit of the `t+1`-digit guard word associated to an integer
coefficient.  For the one-exponent-shift Ferguson branch this is the source
proof's `z₁` digit in `z₁.z₂...zₜzₜ₊₁`. -/
def guardDigitLeadingDigit (fmt : FloatingPointFormat) (k : ℤ) : ℕ :=
  k.natAbs / fmt.beta ^ fmt.t

/-- The trailing `t`-digit coefficient after removing the leading guard-word
digit.  When the leading digit is zero this is the original absolute
coefficient. -/
def guardDigitTailMantissa (fmt : FloatingPointFormat) (k : ℤ) : ℕ :=
  k.natAbs % fmt.beta ^ fmt.t

theorem guardDigitTailMantissa_eq_natAbs_of_natAbs_lt_mantissaBound
    {fmt : FloatingPointFormat} {k : ℤ}
    (h : k.natAbs < fmt.beta ^ fmt.t) :
    fmt.guardDigitTailMantissa k = k.natAbs := by
  exact Nat.mod_eq_of_lt h

theorem guardDigitLeadingDigit_eq_zero_of_natAbs_lt_minNormalMantissa
    {fmt : FloatingPointFormat} {k : ℤ}
    (h : k.natAbs < fmt.minNormalMantissa) :
    fmt.guardDigitLeadingDigit k = 0 := by
  exact Nat.div_eq_of_lt
    (lt_trans h fmt.minNormalMantissa_lt_mantissaBound)

theorem guardDigitTailMantissa_eq_natAbs_of_natAbs_lt_minNormalMantissa
    {fmt : FloatingPointFormat} {k : ℤ}
    (h : k.natAbs < fmt.minNormalMantissa) :
    fmt.guardDigitTailMantissa k = k.natAbs := by
  exact fmt.guardDigitTailMantissa_eq_natAbs_of_natAbs_lt_mantissaBound
    (lt_trans h fmt.minNormalMantissa_lt_mantissaBound)

/-- The signed coefficient obtained by dropping the leading guard digit and
reattaching the original sign.  Under the Ferguson one-shift condition this is
the source proof's "round to t digits" coefficient. -/
def guardDigitRoundedCoeff (fmt : FloatingPointFormat) (k : ℤ) : ℤ :=
  if k < 0 then -((fmt.guardDigitTailMantissa k : ℕ) : ℤ)
  else ((fmt.guardDigitTailMantissa k : ℕ) : ℤ)

theorem guardDigitRoundedCoeff_eq_self_of_natAbs_lt_mantissaBound
    {fmt : FloatingPointFormat} {k : ℤ}
    (h : k.natAbs < fmt.beta ^ fmt.t) :
    fmt.guardDigitRoundedCoeff k = k := by
  have htail := fmt.guardDigitTailMantissa_eq_natAbs_of_natAbs_lt_mantissaBound h
  unfold guardDigitRoundedCoeff
  by_cases hk : k < 0
  · rw [if_pos hk, htail, Int.natCast_natAbs, abs_of_neg hk]
    ring
  · have hk_nonneg : 0 ≤ k := le_of_not_gt hk
    rw [if_neg hk, htail, Int.natCast_natAbs, abs_of_nonneg hk_nonneg]

theorem guardDigitRoundedCoeff_eq_self_of_natAbs_lt_minNormalMantissa
    {fmt : FloatingPointFormat} {k : ℤ}
    (h : k.natAbs < fmt.minNormalMantissa) :
    fmt.guardDigitRoundedCoeff k = k :=
  fmt.guardDigitRoundedCoeff_eq_self_of_natAbs_lt_mantissaBound
    (lt_trans h fmt.minNormalMantissa_lt_mantissaBound)

/-- Same-exponent subtraction value after the t-digit subtraction coefficient
is kept exactly. -/
def guardDigitRoundedSameExponentSubtractionValue
    (fmt : FloatingPointFormat) (negative : Bool) (m n : ℕ)
    (e : ℤ) : ℝ :=
  fmt.signValue negative *
    (((fmt.guardDigitRoundedCoeff
      (fmt.sameExponentMantissaDiffInt m n) : ℤ) : ℝ) *
      fmt.betaR ^ (e - (fmt.t : ℤ)))

theorem normalizedValue_sub_sameSign_sameExponent_eq_guardDigitRounded
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ}
    {e : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n) :
    fmt.normalizedValue negative m e - fmt.normalizedValue negative n e =
      fmt.guardDigitRoundedSameExponentSubtractionValue negative m n e := by
  have hround :
      fmt.guardDigitRoundedCoeff (fmt.sameExponentMantissaDiffInt m n) =
        fmt.sameExponentMantissaDiffInt m n :=
    fmt.guardDigitRoundedCoeff_eq_self_of_natAbs_lt_mantissaBound
      (fmt.sameExponentMantissaDiffInt_natAbs_lt_mantissaBound hm.2 hn.2)
  have hcast :
      (((fmt.guardDigitRoundedCoeff
        (fmt.sameExponentMantissaDiffInt m n) : ℤ) : ℝ)) =
        (m : ℝ) - (n : ℝ) := by
    rw [hround]
    exact fmt.sameExponentMantissaDiffInt_cast m n
  rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
  simp [guardDigitRoundedSameExponentSubtractionValue,
    alignedSameExponentSubtractionValue, hcast]
  ring

/-- A selector witness for direct same-exponent renormalization: after shifting
some finite number of base digits from the exponent into the exact integer
mantissa difference, the shifted mantissa is normalized and the shifted exponent
remains inside the finite exponent range. -/
def sameExponentRenormalizationWitness
    (fmt : FloatingPointFormat) (m n : ℕ) (e : ℤ) : Prop :=
  ∃ shift : ℕ,
    fmt.exponentInRange (e - (shift : ℤ)) ∧
      fmt.normalizedMantissa
        ((fmt.sameExponentMantissaDiffInt m n).natAbs * fmt.beta ^ shift)

/-- A selector witness for the same-exponent branch whose exact difference
shifts all the way down to `emin` and lands in the subnormal interval. -/
def sameExponentSubnormalEndpointWitness
    (fmt : FloatingPointFormat) (m n : ℕ) (e : ℤ) : Prop :=
  ∃ shift : ℕ,
    e - (shift : ℤ) = fmt.emin ∧
      (fmt.sameExponentMantissaDiffInt m n).natAbs * fmt.beta ^ shift <
        fmt.minNormalMantissa

/-- Finite radix-shift search for a same-exponent integer coefficient.  Within
`q` shifts, a `t`-digit coefficient is either zero, becomes normalized, or is
still below the normalized leading-digit threshold at the endpoint. -/
theorem sameExponent_shift_search
    {fmt : FloatingPointFormat} {a q : ℕ}
    (ha : a < fmt.beta ^ fmt.t) :
    a = 0 ∨
      (∃ shift : ℕ, shift ≤ q ∧
        fmt.normalizedMantissa (a * fmt.beta ^ shift)) ∨
      a * fmt.beta ^ q < fmt.minNormalMantissa := by
  induction q with
  | zero =>
      by_cases ha0 : a = 0
      · exact Or.inl ha0
      · by_cases hmin : fmt.minNormalMantissa ≤ a
        · exact Or.inr (Or.inl ⟨0, le_rfl, by
            simpa [normalizedMantissa] using
              (⟨hmin, ha⟩ : fmt.normalizedMantissa a)⟩)
        · exact Or.inr (Or.inr (by
            simpa using (Nat.lt_of_not_ge hmin)))
  | succ q ih =>
      rcases ih with hzero | hrest
      · exact Or.inl hzero
      rcases hrest with hnorm | hprev_lt
      · rcases hnorm with ⟨shift, hle, hnorm⟩
        exact Or.inr (Or.inl ⟨shift, Nat.le_succ_of_le hle, hnorm⟩)
      · by_cases hnext_lt :
          a * fmt.beta ^ (q + 1) < fmt.minNormalMantissa
        · exact Or.inr (Or.inr hnext_lt)
        · have hnext_ge :
            fmt.minNormalMantissa ≤ a * fmt.beta ^ (q + 1) :=
            Nat.le_of_not_gt hnext_lt
          have hstep :
              a * fmt.beta ^ (q + 1) =
                (a * fmt.beta ^ q) * fmt.beta := by
            rw [pow_succ]
            ring
          have hnext_lt_bound :
              a * fmt.beta ^ (q + 1) < fmt.beta ^ fmt.t := by
            calc
              a * fmt.beta ^ (q + 1) =
                  (a * fmt.beta ^ q) * fmt.beta := hstep
              _ < fmt.minNormalMantissa * fmt.beta :=
                  Nat.mul_lt_mul_of_pos_right hprev_lt
                    (lt_of_lt_of_le (by decide : 0 < 2) fmt.beta_ge_two)
              _ = fmt.beta ^ fmt.t :=
                  fmt.minNormalMantissa_mul_beta_eq_mantissaBound
          exact Or.inr (Or.inl
            ⟨q + 1, le_rfl, ⟨hnext_ge, hnext_lt_bound⟩⟩)

/-- Generic finite-system theorem for an exact signed integer coefficient with
fewer than `t` radix digits at exponent `e`.  The coefficient either is zero,
renormalizes before leaving the exponent interval, or lands in the shifted
`emin` subnormal endpoint. -/
theorem scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool} {k : ℤ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hk : k.natAbs < fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      (fmt.signValue negative * (k : ℝ) *
        fmt.betaR ^ (e - (fmt.t : ℤ))) := by
  by_cases hkzero : k = 0
  · left
    simp [hkzero]
  let a := k.natAbs
  let q := Int.toNat (e - fmt.emin)
  have ha_pos : 0 < a := by
    exact Nat.pos_of_ne_zero (mt Int.natAbs_eq_zero.mp hkzero)
  have hq_cast : ((q : ℕ) : ℤ) = e - fmt.emin := by
    have hnonneg : 0 ≤ e - fmt.emin := sub_nonneg.mpr he.1
    simpa [q] using Int.toNat_of_nonneg hnonneg
  have hq_endpoint : e - (q : ℤ) = fmt.emin := by
    omega
  have ha_lt : a < fmt.beta ^ fmt.t := by
    simpa [a] using hk
  rcases fmt.sameExponent_shift_search (a := a) (q := q) ha_lt with
    hazero | hrest
  · exact False.elim (by
      have : k.natAbs = 0 := by simpa [a] using hazero
      exact hkzero (Int.natAbs_eq_zero.mp this))
  rcases hrest with hnorm | hend
  · rcases hnorm with ⟨shift, hle, hnorm⟩
    have hle_int : (shift : ℤ) ≤ (q : ℤ) := by
      exact_mod_cast hle
    have hex : fmt.exponentInRange (e - (shift : ℤ)) := by
      constructor
      · omega
      · have hshift_nonneg : (0 : ℤ) ≤ (shift : ℤ) := by
          exact_mod_cast Nat.zero_le shift
        have hle_e : e - (shift : ℤ) ≤ e := by omega
        exact le_trans hle_e he.2
    by_cases hkneg : k < 0
    · have hk_abs_int : (((k.natAbs : ℕ) : ℤ)) = -k := by
        simp [abs_of_neg hkneg]
      have hk_abs_real : ((k.natAbs : ℕ) : ℝ) = -(k : ℝ) := by
        have hcast :
            ((((k.natAbs : ℕ) : ℤ) : ℝ)) = (((-k : ℤ) : ℝ)) :=
          congrArg (fun z : ℤ => (z : ℝ)) hk_abs_int
        simpa using hcast
      cases negative
      · exact Or.inr (Or.inl
          ⟨true, k.natAbs * fmt.beta ^ shift, e - (shift : ℤ),
            by simpa [a] using hnorm, hex, by
            rw [fmt.normalizedValue_mul_beta_pow_subExponent_eq]
            simp [normalizedValue, signValue, hk_abs_real]⟩)
      · exact Or.inr (Or.inl
          ⟨false, k.natAbs * fmt.beta ^ shift, e - (shift : ℤ),
            by simpa [a] using hnorm, hex, by
            rw [fmt.normalizedValue_mul_beta_pow_subExponent_eq]
            simp [normalizedValue, signValue, hk_abs_real]⟩)
    · have hknonneg : 0 ≤ k := le_of_not_gt hkneg
      have hk_abs_int : (((k.natAbs : ℕ) : ℤ)) = k := by
        simp [abs_of_nonneg hknonneg]
      have hk_abs_real : ((k.natAbs : ℕ) : ℝ) = (k : ℝ) := by
        have hcast :
            ((((k.natAbs : ℕ) : ℤ) : ℝ)) = ((k : ℤ) : ℝ) :=
          congrArg (fun z : ℤ => (z : ℝ)) hk_abs_int
        simpa using hcast
      cases negative
      · exact Or.inr (Or.inl
          ⟨false, k.natAbs * fmt.beta ^ shift, e - (shift : ℤ),
            by simpa [a] using hnorm, hex, by
            rw [fmt.normalizedValue_mul_beta_pow_subExponent_eq]
            simp [normalizedValue, signValue, hk_abs_real]⟩)
      · exact Or.inr (Or.inl
          ⟨true, k.natAbs * fmt.beta ^ shift, e - (shift : ℤ),
            by simpa [a] using hnorm, hex, by
            rw [fmt.normalizedValue_mul_beta_pow_subExponent_eq]
            simp [normalizedValue, signValue, hk_abs_real]⟩)
  · have hscale_pos :
        0 < k.natAbs * fmt.beta ^ q := by
      exact Nat.mul_pos ha_pos
        (Nat.pow_pos (lt_of_lt_of_le (by decide : 0 < 2) fmt.beta_ge_two))
    have hsub :
        fmt.subnormalMantissa (k.natAbs * fmt.beta ^ q) :=
      ⟨hscale_pos, by simpa [a] using hend⟩
    by_cases hkneg : k < 0
    · have hk_abs_int : (((k.natAbs : ℕ) : ℤ)) = -k := by
        simp [abs_of_neg hkneg]
      have hk_abs_real : ((k.natAbs : ℕ) : ℝ) = -(k : ℝ) := by
        have hcast :
            ((((k.natAbs : ℕ) : ℤ) : ℝ)) = (((-k : ℤ) : ℝ)) :=
          congrArg (fun z : ℤ => (z : ℝ)) hk_abs_int
        simpa using hcast
      cases negative
      · exact Or.inr (Or.inr
          ⟨true, k.natAbs * fmt.beta ^ q, hsub, by
            rw [← fmt.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
              (negative := true) (m := k.natAbs) (shift := q)
              (e := e) hq_endpoint]
            simp [normalizedValue, signValue, hk_abs_real]⟩)
      · exact Or.inr (Or.inr
          ⟨false, k.natAbs * fmt.beta ^ q, hsub, by
            rw [← fmt.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
              (negative := false) (m := k.natAbs) (shift := q)
              (e := e) hq_endpoint]
            simp [normalizedValue, signValue, hk_abs_real]⟩)
    · have hknonneg : 0 ≤ k := le_of_not_gt hkneg
      have hk_abs_int : (((k.natAbs : ℕ) : ℤ)) = k := by
        simp [abs_of_nonneg hknonneg]
      have hk_abs_real : ((k.natAbs : ℕ) : ℝ) = (k : ℝ) := by
        have hcast :
            ((((k.natAbs : ℕ) : ℤ) : ℝ)) = ((k : ℤ) : ℝ) :=
          congrArg (fun z : ℤ => (z : ℝ)) hk_abs_int
        simpa using hcast
      cases negative
      · exact Or.inr (Or.inr
          ⟨false, k.natAbs * fmt.beta ^ q, hsub, by
            rw [← fmt.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
              (negative := false) (m := k.natAbs) (shift := q)
              (e := e) hq_endpoint]
            simp [normalizedValue, signValue, hk_abs_real]⟩)
      · exact Or.inr (Or.inr
          ⟨true, k.natAbs * fmt.beta ^ q, hsub, by
            rw [← fmt.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
              (negative := true) (m := k.natAbs) (shift := q)
              (e := e) hq_endpoint]
            simp [normalizedValue, signValue, hk_abs_real]⟩)

/-- Same-lattice signed scaled-integer subtraction is finite when the integer
coefficient difference has fewer than `t` radix digits.

This is the coefficient-level bridge needed by binary addition roundoff-error
representability proofs: once an exact source value and its rounded endpoint
are represented on the same exponent lattice, the real difference is finite
provided the coefficient gap fits in the finite mantissa range. -/
theorem signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool} {k l : ℤ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hdiff : (k - l).natAbs < fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      (fmt.signValue negative * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)) -
        fmt.signValue negative * (l : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) := by
  have hfin :
      fmt.finiteSystem
        (fmt.signValue negative * ((k - l : ℤ) : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) :=
    fmt.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
      (negative := negative) (k := k - l) (e := e) he hdiff
  convert hfin using 1
  norm_num
  ring

/-- Same-sign, same-exponent normalized addition stays on the same scaled
integer lattice with coefficient `m+n`.

This is the source-side operand-grid representation needed by the C4.4
roundoff-error proof: before the rounded endpoint is compared to `a+b`, the
exact sum of two aligned same-sign normalized operands has an explicit integer
coefficient on the common exponent lattice. -/
theorem normalizedValue_add_sameSign_sameExponent_eq_scaledInteger
    (fmt : FloatingPointFormat) (negative : Bool) (m n : ℕ) (e : ℤ) :
    fmt.normalizedValue negative m e +
        fmt.normalizedValue negative n e =
      fmt.signValue negative * ((m + n : ℕ) : ℝ) *
        fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  cases negative <;>
    simp [normalizedValue, signValue, Nat.cast_add] <;> ring

/-- The same-sign, same-exponent normalized addition coefficient has at most
one guard digit: `m+n < 2*beta^t`. -/
theorem normalizedMantissa_add_lt_two_mul_mantissaBound
    {fmt : FloatingPointFormat} {m n : ℕ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n) :
    m + n < 2 * fmt.beta ^ fmt.t := by
  have hsum : m + n < fmt.beta ^ fmt.t + fmt.beta ^ fmt.t :=
    Nat.add_lt_add hm.2 hn.2
  simpa [two_mul] using hsum

/-- Packaged source-grid form for aligned same-sign normalized addition: the
exact source sum has an explicit signed integer coefficient on the same exponent
lattice, and that coefficient is bounded by the two-operand guard word
`2*beta^t`. -/
theorem normalizedValue_add_sameSign_sameExponent_exists_scaledIntegerCoeff
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n) :
    ∃ k : ℤ,
      k.natAbs < 2 * fmt.beta ^ fmt.t ∧
        fmt.normalizedValue negative m e +
            fmt.normalizedValue negative n e =
          fmt.signValue negative * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  refine ⟨((m + n : ℕ) : ℤ), ?_, ?_⟩
  · simpa using
      normalizedMantissa_add_lt_two_mul_mantissaBound
        (fmt := fmt) hm hn
  · exact fmt.normalizedValue_add_sameSign_sameExponent_eq_scaledInteger
      negative m n e

/-- If the aligned same-sign normalized addition coefficient already fits in
`t` digits, the exact source sum is finite representable. -/
theorem normalizedValue_add_sameSign_sameExponent_finiteSystem_of_add_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hadd : m + n < fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      (fmt.normalizedValue negative m e +
        fmt.normalizedValue negative n e) := by
  rw [fmt.normalizedValue_add_sameSign_sameExponent_eq_scaledInteger]
  exact
    fmt.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
      (negative := negative) (k := ((m + n : ℕ) : ℤ)) (e := e) he
      (by simpa using hadd)

/-- Same-sign normalized operands with ordered exponents add exactly when the
higher-exponent operand is shifted onto the lower exponent lattice and the
resulting coefficient still fits in `t` radix digits. -/
theorem normalizedValue_add_sameSign_orderedExponent_finiteSystem_of_alignedCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (_hmHigh : fmt.normalizedMantissa mHigh)
    (_hmLow : fmt.normalizedMantissa mLow)
    (_heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      (fmt.normalizedValue negative mHigh eHigh +
        fmt.normalizedValue negative mLow eLow) := by
  let q := Int.toNat (eHigh - eLow)
  have hq_cast : ((q : ℕ) : ℤ) = eHigh - eLow := by
    have hnonneg : 0 ≤ eHigh - eLow := sub_nonneg.mpr hle
    simpa [q] using Int.toNat_of_nonneg hnonneg
  have hq_endpoint : eHigh - (q : ℤ) = eLow := by
    omega
  have hshift :
      fmt.normalizedValue negative (mHigh * fmt.beta ^ q) eLow =
        fmt.normalizedValue negative mHigh eHigh := by
    have h :=
      fmt.normalizedValue_mul_beta_pow_subExponent_eq
        (negative := negative) (m := mHigh) (shift := q) (e := eHigh)
    rw [hq_endpoint] at h
    exact h
  have hfin :
      fmt.finiteSystem
        (fmt.signValue negative *
          ((((mHigh * fmt.beta ^ q + mLow : ℕ) : ℤ) : ℝ)) *
          fmt.betaR ^ (eLow - (fmt.t : ℤ))) :=
    fmt.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
      (negative := negative)
      (k := ((mHigh * fmt.beta ^ q + mLow : ℕ) : ℤ))
      (e := eLow)
      heLow
      (by simpa [q] using hcoeff)
  convert hfin using 1
  rw [← hshift]
  simp [normalizedValue, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  ring

/-- Raising the normalized exponent by one shifts one base digit into the
integer coefficient on the original exponent lattice. -/
theorem normalizedValue_succExponent_eq_beta_scaledInteger
    (fmt : FloatingPointFormat) (negative : Bool) (m : ℕ) (e : ℤ) :
    fmt.normalizedValue negative m (e + 1) =
      fmt.signValue negative * (((fmt.beta * m : ℕ) : ℝ)) *
        fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  have hpow :
      fmt.betaR ^ ((e + 1) - (fmt.t : ℤ)) =
        fmt.betaR * fmt.betaR ^ (e - (fmt.t : ℤ)) := by
    calc
      fmt.betaR ^ ((e + 1) - (fmt.t : ℤ)) =
          fmt.betaR ^ ((e - (fmt.t : ℤ)) + 1) := by
        congr 1
        ring
      _ = fmt.betaR ^ (e - (fmt.t : ℤ)) * fmt.betaR ^ (1 : ℤ) := by
        rw [zpow_add₀ hbase]
      _ = fmt.betaR * fmt.betaR ^ (e - (fmt.t : ℤ)) := by
        rw [zpow_one]
        ring
  cases negative <;>
    simp [normalizedValue, signValue, Nat.cast_mul, hpow] <;>
    rw [show ((fmt.beta : ℝ) = fmt.betaR) by rfl] <;> ring

/-- Raising the normalized exponent by two shifts two base digits into the
integer coefficient on the original exponent lattice. -/
theorem normalizedValue_add_twoExponent_eq_beta_sq_scaledInteger
    (fmt : FloatingPointFormat) (negative : Bool) (m : ℕ) (e : ℤ) :
    fmt.normalizedValue negative m (e + 2) =
      fmt.signValue negative * (((m * fmt.beta ^ 2 : ℕ) : ℝ)) *
        fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  have h := fmt.normalizedValue_mul_beta_pow_subExponent_eq
    (negative := negative) (m := m) (shift := 2) (e := e + 2)
  have hexp : (e + 2 - (2 : ℤ)) = e := by ring
  have hleft :
      fmt.normalizedValue negative (m * fmt.beta ^ 2) e =
        fmt.normalizedValue negative m (e + 2) := by
    simpa [hexp] using h
  rw [← hleft]
  rfl

/-- Positive binary guard-word source coefficients lie between the quotient
endpoints at the next exponent.

If `k = beta*q+r` with `r < beta`, then the source value
`k*beta^(e-t)` is between the normalized values with mantissas `q` and
`q+1` at exponent `e+1`.  This is the concrete bracket-construction step for
the aligned positive C4.4 guard-word branch. -/
theorem binaryGuardSource_between_sameExponentEndpoints_positive
    {fmt : FloatingPointFormat} {k q r : ℕ} {e : ℤ}
    (hk : k = fmt.beta * q + r)
    (hr : r < fmt.beta) :
    fmt.normalizedValue false q (e + 1) ≤
        (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) ∧
      (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) ≤
        fmt.normalizedValue false (q + 1) (e + 1) := by
  have hs_nonneg : 0 ≤ fmt.betaR ^ (e - (fmt.t : ℤ)) :=
    fmt.betaR_zpow_nonneg (e - (fmt.t : ℤ))
  have hk_lower_nat : fmt.beta * q ≤ k := by
    rw [hk]
    exact Nat.le_add_right _ _
  have hk_upper_nat : k ≤ fmt.beta * (q + 1) := by
    rw [hk, Nat.mul_succ]
    exact Nat.add_le_add_left (Nat.le_of_lt hr) (fmt.beta * q)
  have hk_lower_real : (((fmt.beta * q : ℕ) : ℝ)) ≤ (k : ℝ) :=
    Nat.cast_le.mpr hk_lower_nat
  have hk_upper_real : (k : ℝ) ≤ (((fmt.beta * (q + 1) : ℕ) : ℝ)) :=
    Nat.cast_le.mpr hk_upper_nat
  have hk_lower_real' : (fmt.beta : ℝ) * (q : ℝ) ≤ (k : ℝ) := by
    simpa [Nat.cast_mul] using hk_lower_real
  have hk_upper_real' : (k : ℝ) ≤ (fmt.beta : ℝ) * ((q : ℝ) + 1) := by
    simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hk_upper_real
  constructor
  · rw [fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
    simp [signValue]
    exact mul_le_mul_of_nonneg_right hk_lower_real' hs_nonneg
  · rw [fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
    simp [signValue]
    exact mul_le_mul_of_nonneg_right hk_upper_real' hs_nonneg

/-- Negative binary guard-word source coefficients lie between the reversed
quotient endpoints at the next exponent.

For negative values the real-order bracket is reversed: the left endpoint has
mantissa `q+1`, and the right endpoint has mantissa `q`. -/
theorem binaryGuardSource_between_sameExponentEndpoints_negative
    {fmt : FloatingPointFormat} {k q r : ℕ} {e : ℤ}
    (hk : k = fmt.beta * q + r)
    (hr : r < fmt.beta) :
    fmt.normalizedValue true (q + 1) (e + 1) ≤
        fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)) ∧
      fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)) ≤
        fmt.normalizedValue true q (e + 1) := by
  have hs_nonneg : 0 ≤ fmt.betaR ^ (e - (fmt.t : ℤ)) :=
    fmt.betaR_zpow_nonneg (e - (fmt.t : ℤ))
  have hk_lower_nat : fmt.beta * q ≤ k := by
    rw [hk]
    exact Nat.le_add_right _ _
  have hk_upper_nat : k ≤ fmt.beta * (q + 1) := by
    rw [hk, Nat.mul_succ]
    exact Nat.add_le_add_left (Nat.le_of_lt hr) (fmt.beta * q)
  have hk_lower_real : (((fmt.beta * q : ℕ) : ℝ)) ≤ (k : ℝ) :=
    Nat.cast_le.mpr hk_lower_nat
  have hk_upper_real : (k : ℝ) ≤ (((fmt.beta * (q + 1) : ℕ) : ℝ)) :=
    Nat.cast_le.mpr hk_upper_nat
  have hk_lower_real' : (fmt.beta : ℝ) * (q : ℝ) ≤ (k : ℝ) := by
    simpa [Nat.cast_mul] using hk_lower_real
  have hk_upper_real' : (k : ℝ) ≤ (fmt.beta : ℝ) * ((q : ℝ) + 1) := by
    simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hk_upper_real
  constructor
  · rw [fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
    simp [signValue]
    exact mul_le_mul_of_nonneg_right hk_upper_real' hs_nonneg
  · rw [fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
    simp [signValue]
    exact mul_le_mul_of_nonneg_right hk_lower_real' hs_nonneg

/-- Positive binary guard-word source coefficients at the mantissa ceiling lie
between the exponent-boundary endpoints.

This is the boundary counterpart of
`binaryGuardSource_between_sameExponentEndpoints_positive`: when the lower
quotient is `maxNormalMantissa`, the upper endpoint is the smallest mantissa at
the next exponent. -/
theorem binaryGuardSource_between_boundaryEndpoints_positive
    {fmt : FloatingPointFormat} {k r : ℕ} {e : ℤ}
    (hk : k = fmt.beta * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta) :
    fmt.normalizedValue false fmt.maxNormalMantissa (e + 1) ≤
        (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) ∧
      (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) ≤
        fmt.normalizedValue false fmt.minNormalMantissa (e + 2) := by
  have hs_nonneg : 0 ≤ fmt.betaR ^ (e - (fmt.t : ℤ)) :=
    fmt.betaR_zpow_nonneg (e - (fmt.t : ℤ))
  have hk_lower_nat : fmt.beta * fmt.maxNormalMantissa ≤ k := by
    rw [hk]
    exact Nat.le_add_right _ _
  have hmaxsucc_eq :
      fmt.maxNormalMantissa + 1 = fmt.minNormalMantissa * fmt.beta := by
    rw [fmt.maxNormalMantissa_add_one,
      fmt.minNormalMantissa_mul_beta_eq_mantissaBound]
  have hupper_coeff :
      fmt.beta * (fmt.maxNormalMantissa + 1) =
        fmt.minNormalMantissa * fmt.beta ^ 2 := by
    rw [hmaxsucc_eq]
    ring
  have hk_upper_lt : k < fmt.beta * (fmt.maxNormalMantissa + 1) := by
    rw [hk, Nat.mul_succ]
    exact Nat.add_lt_add_left hr (fmt.beta * fmt.maxNormalMantissa)
  have hk_upper_nat : k ≤ fmt.minNormalMantissa * fmt.beta ^ 2 := by
    rw [← hupper_coeff]
    exact Nat.le_of_lt hk_upper_lt
  have hk_lower_real : (((fmt.beta * fmt.maxNormalMantissa : ℕ) : ℝ)) ≤
      (k : ℝ) :=
    Nat.cast_le.mpr hk_lower_nat
  have hk_upper_real : (k : ℝ) ≤
      (((fmt.minNormalMantissa * fmt.beta ^ 2 : ℕ) : ℝ)) :=
    Nat.cast_le.mpr hk_upper_nat
  have hk_lower_real' :
      (fmt.beta : ℝ) * (fmt.maxNormalMantissa : ℝ) ≤ (k : ℝ) := by
    simpa [Nat.cast_mul] using hk_lower_real
  have hk_upper_real' :
      (k : ℝ) ≤ (fmt.minNormalMantissa : ℝ) * (fmt.beta : ℝ) ^ 2 := by
    simpa [Nat.cast_mul, Nat.cast_pow] using hk_upper_real
  constructor
  · rw [fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
    simp [signValue]
    exact mul_le_mul_of_nonneg_right hk_lower_real' hs_nonneg
  · rw [fmt.normalizedValue_add_twoExponent_eq_beta_sq_scaledInteger]
    simp [signValue]
    exact mul_le_mul_of_nonneg_right hk_upper_real' hs_nonneg

/-- Negative binary guard-word source coefficients at the mantissa ceiling lie
between the reversed exponent-boundary endpoints. -/
theorem binaryGuardSource_between_boundaryEndpoints_negative
    {fmt : FloatingPointFormat} {k r : ℕ} {e : ℤ}
    (hk : k = fmt.beta * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta) :
    fmt.normalizedValue true fmt.minNormalMantissa (e + 2) ≤
        fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)) ∧
      fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)) ≤
        fmt.normalizedValue true fmt.maxNormalMantissa (e + 1) := by
  have hs_nonneg : 0 ≤ fmt.betaR ^ (e - (fmt.t : ℤ)) :=
    fmt.betaR_zpow_nonneg (e - (fmt.t : ℤ))
  have hk_lower_nat : fmt.beta * fmt.maxNormalMantissa ≤ k := by
    rw [hk]
    exact Nat.le_add_right _ _
  have hmaxsucc_eq :
      fmt.maxNormalMantissa + 1 = fmt.minNormalMantissa * fmt.beta := by
    rw [fmt.maxNormalMantissa_add_one,
      fmt.minNormalMantissa_mul_beta_eq_mantissaBound]
  have hupper_coeff :
      fmt.beta * (fmt.maxNormalMantissa + 1) =
        fmt.minNormalMantissa * fmt.beta ^ 2 := by
    rw [hmaxsucc_eq]
    ring
  have hk_upper_lt : k < fmt.beta * (fmt.maxNormalMantissa + 1) := by
    rw [hk, Nat.mul_succ]
    exact Nat.add_lt_add_left hr (fmt.beta * fmt.maxNormalMantissa)
  have hk_upper_nat : k ≤ fmt.minNormalMantissa * fmt.beta ^ 2 := by
    rw [← hupper_coeff]
    exact Nat.le_of_lt hk_upper_lt
  have hk_lower_real : (((fmt.beta * fmt.maxNormalMantissa : ℕ) : ℝ)) ≤
      (k : ℝ) :=
    Nat.cast_le.mpr hk_lower_nat
  have hk_upper_real : (k : ℝ) ≤
      (((fmt.minNormalMantissa * fmt.beta ^ 2 : ℕ) : ℝ)) :=
    Nat.cast_le.mpr hk_upper_nat
  have hk_lower_real' :
      (fmt.beta : ℝ) * (fmt.maxNormalMantissa : ℝ) ≤ (k : ℝ) := by
    simpa [Nat.cast_mul] using hk_lower_real
  have hk_upper_real' :
      (k : ℝ) ≤ (fmt.minNormalMantissa : ℝ) * (fmt.beta : ℝ) ^ 2 := by
    simpa [Nat.cast_mul, Nat.cast_pow] using hk_upper_real
  constructor
  · rw [fmt.normalizedValue_add_twoExponent_eq_beta_sq_scaledInteger]
    simp [signValue]
    exact mul_le_mul_of_nonneg_right hk_upper_real' hs_nonneg
  · rw [fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
    simp [signValue]
    exact mul_le_mul_of_nonneg_right hk_lower_real' hs_nonneg

/-- Binary guard-word quotient dispatcher for aligned addition.

If a one-guard-digit source coefficient `k` lies in
`[beta^t, 2*beta^t)` and is decomposed as `k = 2*q+r`, then the quotient
endpoint is either an ordinary normalized same-exponent bracket (`q` and
`q+1` are both normalized mantissas) or the lower endpoint is exactly
`maxNormalMantissa`, which is the exponent-boundary guard-word case. -/
theorem binaryGuardQuotient_normalized_or_max_of_mantissaBound_le_of_lt_two_mul
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2) {k q r : ℕ}
    (hk : k = fmt.beta * q + r)
    (hr : r < fmt.beta)
    (hlo : fmt.beta ^ fmt.t ≤ k)
    (hhi : k < 2 * fmt.beta ^ fmt.t) :
    (fmt.normalizedMantissa q ∧ fmt.normalizedMantissa (q + 1)) ∨
      q = fmt.maxNormalMantissa := by
  have hk2 : k = 2 * q + r := by
    simpa [hbeta] using hk
  have hr2 : r < 2 := by
    simpa [hbeta] using hr
  have hB_eq : fmt.beta ^ fmt.t = 2 * fmt.minNormalMantissa := by
    rw [← fmt.minNormalMantissa_mul_beta_eq_mantissaBound, hbeta]
    ring
  have hq_ge_min : fmt.minNormalMantissa ≤ q := by
    omega
  have hq_lt_B : q < fmt.beta ^ fmt.t := by
    omega
  by_cases hqsucc_lt_B : q + 1 < fmt.beta ^ fmt.t
  · exact Or.inl
      ⟨⟨hq_ge_min, hq_lt_B⟩,
        ⟨Nat.le_trans hq_ge_min (Nat.le_succ q), hqsucc_lt_B⟩⟩
  · have hqsucc_eq_B : q + 1 = fmt.beta ^ fmt.t := by
      omega
    have hqmax : q = fmt.maxNormalMantissa := by
      rw [← fmt.maxNormalMantissa_add_one] at hqsucc_eq_B
      omega
    exact Or.inr hqmax

/-- Binary one-guard-digit endpoint comparison for aligned addition.

If a source coefficient `k` is decomposed as `k = beta*q + r` in base two, and
the rounded endpoint coefficient is either `q` or the non-exact upper endpoint
`q+1`, then the scaled coefficient difference `k - beta*l` has fewer than `t`
base-`beta` digits.  This is the integer arithmetic core of the aligned
inexact-add branch for C4.4/FastTwoSum. -/
theorem binaryGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2) {k q r l : ℕ}
    (hk : k = fmt.beta * q + r)
    (hr : r < fmt.beta)
    (hl : l = q ∨ (l = q + 1 ∧ r ≠ 0)) :
    (((k : ℤ) - ((fmt.beta * l : ℕ) : ℤ)).natAbs <
      fmt.beta ^ fmt.t) := by
  have hbeta_le_B : fmt.beta ≤ fmt.beta ^ fmt.t :=
    Nat.le_self_pow (Nat.ne_of_gt fmt.t_pos) fmt.beta
  have hBgt1 : 1 < fmt.beta ^ fmt.t :=
    Nat.one_lt_pow (Nat.ne_of_gt fmt.t_pos) fmt.one_lt_beta
  have hk2 : k = 2 * q + r := by
    simpa [hbeta] using hk
  have hr2 : r < 2 := by
    simpa [hbeta] using hr
  rcases hl with hl | hceil
  · subst l
    have hdiff : ((k : ℤ) - ((fmt.beta * q : ℕ) : ℤ)) = (r : ℤ) := by
      rw [hbeta]
      omega
    rw [hdiff]
    have habs : ((r : ℤ).natAbs) = r := by
      simp
    rw [habs]
    exact lt_of_lt_of_le hr hbeta_le_B
  · rcases hceil with ⟨hl, hrne⟩
    subst l
    have hr_eq : r = 1 := by
      omega
    have hdiff :
        ((k : ℤ) - ((fmt.beta * (q + 1) : ℕ) : ℤ)) = (-1 : ℤ) := by
      rw [hbeta]
      omega
    rw [hdiff]
    norm_num
    exact hBgt1

/-- Binary one-guard-digit coefficient comparison at the exponent boundary.

The lower endpoint is `beta * maxNormalMantissa` on the original exponent
lattice.  The upper boundary endpoint is `minNormalMantissa * beta^2` on that
same lattice, and it can only be selected in the non-exact remainder case. -/
theorem binaryGuardBoundaryCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_boundary
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2) {k r c : ℕ}
    (hk : k = fmt.beta * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta)
    (hc : c = fmt.beta * fmt.maxNormalMantissa ∨
      (c = fmt.minNormalMantissa * fmt.beta ^ 2 ∧ r ≠ 0)) :
    (((k : ℤ) - (c : ℤ)).natAbs < fmt.beta ^ fmt.t) := by
  have hbeta_le_B : fmt.beta ≤ fmt.beta ^ fmt.t :=
    Nat.le_self_pow (Nat.ne_of_gt fmt.t_pos) fmt.beta
  have hBgt1 : 1 < fmt.beta ^ fmt.t :=
    Nat.one_lt_pow (Nat.ne_of_gt fmt.t_pos) fmt.one_lt_beta
  have hmaxsucc_eq :
      fmt.maxNormalMantissa + 1 = fmt.minNormalMantissa * fmt.beta := by
    rw [fmt.maxNormalMantissa_add_one,
      fmt.minNormalMantissa_mul_beta_eq_mantissaBound]
  have hupper_coeff :
      fmt.beta * (fmt.maxNormalMantissa + 1) =
        fmt.minNormalMantissa * fmt.beta ^ 2 := by
    rw [hmaxsucc_eq]
    ring
  rcases hc with hc | hc
  · subst c
    have hdiff :
        ((k : ℤ) - ((fmt.beta * fmt.maxNormalMantissa : ℕ) : ℤ)) =
          (r : ℤ) := by
      rw [hk]
      omega
    rw [hdiff]
    have habs : ((r : ℤ).natAbs) = r := by simp
    rw [habs]
    exact lt_of_lt_of_le hr hbeta_le_B
  · rcases hc with ⟨hc, hrne⟩
    subst c
    have hr_eq : r = 1 := by
      omega
    have hdiff :
        ((k : ℤ) - ((fmt.minNormalMantissa * fmt.beta ^ 2 : ℕ) : ℤ)) =
          (-1 : ℤ) := by
      rw [hk, ← hupper_coeff, hbeta, hr_eq]
      omega
    rw [hdiff]
    simpa using hBgt1

/-- The guard-aligned adjacent-exponent subtraction value is finite whenever
its exact signed integer coefficient has fewer than `t` radix digits. -/
theorem alignedAdjacentExponentSubtractionValue_finiteSystem_of_natAbs_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool} {mHigh mLow : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hcoeff :
      (fmt.guardAlignedMantissaDiffInt mHigh mLow).natAbs < fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      (fmt.alignedAdjacentExponentSubtractionValue negative mHigh mLow e) := by
  have h :=
    fmt.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
      (negative := negative)
      (k := fmt.guardAlignedMantissaDiffInt mHigh mLow)
      (e := e) he hcoeff
  convert h using 1
  rw [alignedAdjacentExponentSubtractionValue,
    fmt.guardAlignedMantissaDiffInt_cast mHigh mLow]
  ring

/-- Same-sign adjacent-exponent subtraction is finite when the guard-aligned
coefficient has fewer than `t` radix digits. -/
theorem normalizedValue_sub_sameSign_adjacentExponent_finiteSystem_of_natAbs_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool} {mHigh mLow : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hcoeff :
      (fmt.guardAlignedMantissaDiffInt mHigh mLow).natAbs < fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      (fmt.normalizedValue negative mHigh (e + 1) -
        fmt.normalizedValue negative mLow e) := by
  rw [fmt.normalizedValue_sub_sameSign_adjacentExponent_eq_aligned]
  exact
    fmt.alignedAdjacentExponentSubtractionValue_finiteSystem_of_natAbs_lt_mantissaBound
      (negative := negative) (mHigh := mHigh) (mLow := mLow) (e := e)
      he hcoeff

/-- Positive adjacent-exponent Sterbenz branch: if the two normalized operands
satisfy the Sterbenz ratio condition, their exact subtraction is finite
representable. -/
theorem normalizedValue_sub_positive_adjacentExponent_finiteSystem_of_sterbenzAdjacent
    {fmt : FloatingPointFormat} {mHigh mLow : ℕ} {e : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (he : fmt.exponentInRange e)
    (hsterbenz : fmt.sterbenzRatioCondition
      (fmt.normalizedValue false mHigh (e + 1))
      (fmt.normalizedValue false mLow e)) :
    fmt.finiteSystem
      (fmt.normalizedValue false mHigh (e + 1) -
        fmt.normalizedValue false mLow e) := by
  exact
    fmt.normalizedValue_sub_sameSign_adjacentExponent_finiteSystem_of_natAbs_lt_mantissaBound
      (negative := false) (mHigh := mHigh) (mLow := mLow) (e := e) he
      (fmt.guardAlignedMantissaDiffInt_natAbs_lt_mantissaBound_of_sterbenzAdjacent
        (mHigh := mHigh) (mLow := mLow) (e := e)
        hmHigh hmLow hsterbenz)

/-- Sterbenz's ratio condition forces two positive normalized operands to have
exponents that differ by at most one. -/
theorem sterbenzRatioCondition_positive_normalized_exponent_gap_le_one
    {fmt : FloatingPointFormat} {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (hsterbenz : fmt.sterbenzRatioCondition
      (fmt.normalizedValue false m e)
      (fmt.normalizedValue false n e')) :
    e ≤ e' + 1 ∧ e' ≤ e + 1 := by
  constructor
  · by_contra hnot
    have hgap : e' + 1 < e := by omega
    have hx_lower :
        fmt.betaR ^ (e - 1) ≤ fmt.normalizedValue false m e :=
      by
        have hxpos := fmt.normalizedValue_false_pos (m := m) (e := e) hm
        simpa [abs_of_pos hxpos] using
          (fmt.normalizedValue_abs_lower_power
            (negative := false) (m := m) (e := e) hm)
    have hy_upper :
        fmt.normalizedValue false n e' < fmt.betaR ^ e' :=
      by
        have hypos := fmt.normalizedValue_false_pos (m := n) (e := e') hn
        simpa [abs_of_pos hypos] using
          (fmt.normalizedValue_abs_lt_beta_pow
            (negative := false) (m := n) (e := e') hn)
    have htwo_y_lt_x :
        2 * fmt.normalizedValue false n e' <
          fmt.normalizedValue false m e := by
      calc
        2 * fmt.normalizedValue false n e' <
            2 * fmt.betaR ^ e' :=
          mul_lt_mul_of_pos_left hy_upper (by norm_num)
        _ ≤ fmt.betaR ^ (e' + 1) :=
          fmt.betaR_zpow_add_one_le_of_two_mul e'
        _ ≤ fmt.betaR ^ (e - 1) :=
          fmt.betaR_zpow_le_zpow_of_le (by omega)
        _ ≤ fmt.normalizedValue false m e := hx_lower
    exact (not_lt_of_ge (le_of_lt htwo_y_lt_x)) hsterbenz.2
  · by_contra hnot
    have hgap : e + 1 < e' := by omega
    have hy_lower :
        fmt.betaR ^ (e' - 1) ≤ fmt.normalizedValue false n e' :=
      by
        have hypos := fmt.normalizedValue_false_pos (m := n) (e := e') hn
        simpa [abs_of_pos hypos] using
          (fmt.normalizedValue_abs_lower_power
            (negative := false) (m := n) (e := e') hn)
    have hx_upper :
        fmt.normalizedValue false m e < fmt.betaR ^ e :=
      by
        have hxpos := fmt.normalizedValue_false_pos (m := m) (e := e) hm
        simpa [abs_of_pos hxpos] using
          (fmt.normalizedValue_abs_lt_beta_pow
            (negative := false) (m := m) (e := e) hm)
    have htwo_x_lt_y :
        2 * fmt.normalizedValue false m e <
          fmt.normalizedValue false n e' := by
      calc
        2 * fmt.normalizedValue false m e <
            2 * fmt.betaR ^ e :=
          mul_lt_mul_of_pos_left hx_upper (by norm_num)
        _ ≤ fmt.betaR ^ (e + 1) :=
          fmt.betaR_zpow_add_one_le_of_two_mul e
        _ ≤ fmt.betaR ^ (e' - 1) :=
          fmt.betaR_zpow_le_zpow_of_le (by omega)
        _ ≤ fmt.normalizedValue false n e' := hy_lower
    have hy_lt_two_x :
        fmt.normalizedValue false n e' <
          2 * fmt.normalizedValue false m e := by
      rcases hsterbenz with ⟨hlo, _hhi⟩
      linarith
    exact (not_lt_of_ge (le_of_lt htwo_x_lt_y)) hy_lt_two_x

/-- The currently closed same-exponent finite-difference cases for direct
Sterbenz-style representability: exact zero, a normalized finite shift, or the
shifted `emin` subnormal endpoint.  Proving this witness from Sterbenz's source
hypotheses is the remaining direct same-exponent selector obligation. -/
def sameExponentFiniteDifferenceWitness
    (fmt : FloatingPointFormat) (m n : ℕ) (e : ℤ) : Prop :=
  (fmt.sameExponentMantissaDiffInt m n).natAbs = 0 ∨
    fmt.sameExponentRenormalizationWitness m n e ∨
      fmt.sameExponentSubnormalEndpointWitness m n e

/-- Same-exponent finite-difference selector derived from ordinary finite
same-exponent operand facts.  The exact integer mantissa difference has fewer
than `t` digits; shifting it down from exponent `e` either normalizes before
leaving the finite exponent interval or reaches the shifted `emin` subnormal
endpoint. -/
theorem sameExponentFiniteDifferenceWitness_of_normalizedMantissas
    {fmt : FloatingPointFormat} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (he : fmt.exponentInRange e) :
    fmt.sameExponentFiniteDifferenceWitness m n e := by
  let a := (fmt.sameExponentMantissaDiffInt m n).natAbs
  let q := Int.toNat (e - fmt.emin)
  have hq_cast : ((q : ℕ) : ℤ) = e - fmt.emin := by
    have hnonneg : 0 ≤ e - fmt.emin := sub_nonneg.mpr he.1
    simpa [q] using Int.toNat_of_nonneg hnonneg
  have hq_endpoint : e - (q : ℤ) = fmt.emin := by
    omega
  have ha_lt : a < fmt.beta ^ fmt.t := by
    simpa [a] using
      fmt.sameExponentMantissaDiffInt_natAbs_lt_mantissaBound hm.2 hn.2
  rcases fmt.sameExponent_shift_search (a := a) (q := q) ha_lt with
    hzero | hrest
  · exact Or.inl (by simpa [a] using hzero)
  rcases hrest with hnorm | hend
  · rcases hnorm with ⟨shift, hle, hnorm⟩
    have hle_int : (shift : ℤ) ≤ (q : ℤ) := by
      exact_mod_cast hle
    have hex : fmt.exponentInRange (e - (shift : ℤ)) := by
      constructor
      · omega
      · have hshift_nonneg : (0 : ℤ) ≤ (shift : ℤ) := by
          exact_mod_cast Nat.zero_le shift
        have hle_e : e - (shift : ℤ) ≤ e := by omega
        exact le_trans hle_e he.2
    exact Or.inr (Or.inl ⟨shift, hex, by simpa [a] using hnorm⟩)
  · exact Or.inr (Or.inr ⟨q, hq_endpoint, by simpa [a] using hend⟩)

/-- Exact zero same-exponent subtraction is finite for every exponent. -/
theorem normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_natAbs_eq_zero
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hdiff : (fmt.sameExponentMantissaDiffInt m n).natAbs = 0) :
    fmt.finiteSystem
      (fmt.normalizedValue negative m e -
        fmt.normalizedValue negative n e) := by
  let k := fmt.sameExponentMantissaDiffInt m n
  have hk_cast : (k : ℝ) = (m : ℝ) - (n : ℝ) := by
    simpa [k] using fmt.sameExponentMantissaDiffInt_cast m n
  have hkzero : k = 0 := by
    exact Int.natAbs_eq_zero.mp (by simpa [k] using hdiff)
  left
  rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
  simp [alignedSameExponentSubtractionValue, signValue, hk_cast.symm, hkzero]

/-- Direct representability subcase for Sterbenz-style exact subtraction:
when the same-exponent mantissa difference is already a normalized mantissa, the
exact subtraction result is a finite normalized floating-point value.  The
remaining direct Sterbenz work is the non-`emin` renormalization case when this
coefficient has too few leading digits. -/
theorem normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_normalizedDiff
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hex : fmt.exponentInRange e)
    (hdiff : fmt.normalizedMantissa
      (fmt.sameExponentMantissaDiffInt m n).natAbs) :
    fmt.finiteSystem
      (fmt.normalizedValue negative m e -
        fmt.normalizedValue negative n e) := by
  let k := fmt.sameExponentMantissaDiffInt m n
  have hk_cast : (k : ℝ) = (m : ℝ) - (n : ℝ) := by
    simpa [k] using fmt.sameExponentMantissaDiffInt_cast m n
  by_cases hkneg : k < 0
  · have hk_abs_int : (((k.natAbs : ℕ) : ℤ)) = -k := by
      simp [abs_of_neg hkneg]
    have hk_abs_real : ((k.natAbs : ℕ) : ℝ) = -(k : ℝ) := by
      have hcast :
          ((((k.natAbs : ℕ) : ℤ) : ℝ)) = (((-k : ℤ) : ℝ)) :=
        congrArg (fun z : ℤ => (z : ℝ)) hk_abs_int
      simpa using hcast
    cases negative
    · exact Or.inr (Or.inl
        ⟨true, k.natAbs, e, by simpa [k] using hdiff, hex, by
          rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
          simp [alignedSameExponentSubtractionValue, normalizedValue,
            signValue, hk_cast.symm, hk_abs_real]⟩)
    · exact Or.inr (Or.inl
        ⟨false, k.natAbs, e, by simpa [k] using hdiff, hex, by
          rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
          simp [alignedSameExponentSubtractionValue, normalizedValue,
            signValue, hk_cast.symm, hk_abs_real]⟩)
  · have hknonneg : 0 ≤ k := le_of_not_gt hkneg
    have hk_abs_int : (((k.natAbs : ℕ) : ℤ)) = k := by
      simp [abs_of_nonneg hknonneg]
    have hk_abs_real : ((k.natAbs : ℕ) : ℝ) = (k : ℝ) := by
      have hcast :
          ((((k.natAbs : ℕ) : ℤ) : ℝ)) = ((k : ℤ) : ℝ) :=
        congrArg (fun z : ℤ => (z : ℝ)) hk_abs_int
      simpa using hcast
    cases negative
    · exact Or.inr (Or.inl
        ⟨false, k.natAbs, e, by simpa [k] using hdiff, hex, by
          rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
          simp [alignedSameExponentSubtractionValue, normalizedValue,
            signValue, hk_cast.symm, hk_abs_real]⟩)
    · exact Or.inr (Or.inl
        ⟨true, k.natAbs, e, by simpa [k] using hdiff, hex, by
          rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
          simp [alignedSameExponentSubtractionValue, normalizedValue,
            signValue, hk_cast.symm, hk_abs_real]⟩)

/-- Direct one-step renormalization subcase for Sterbenz-style exact
subtraction: if shifting one base digit from the exponent into the exact
same-exponent mantissa difference gives a normalized mantissa, then the exact
subtraction result is a finite normalized floating-point value at exponent
`e - 1`. -/
theorem normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_beta_mul_normalizedDiff
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hex : fmt.exponentInRange (e - 1))
    (hdiff : fmt.normalizedMantissa
      ((fmt.sameExponentMantissaDiffInt m n).natAbs * fmt.beta)) :
    fmt.finiteSystem
      (fmt.normalizedValue negative m e -
        fmt.normalizedValue negative n e) := by
  let k := fmt.sameExponentMantissaDiffInt m n
  have hk_cast : (k : ℝ) = (m : ℝ) - (n : ℝ) := by
    simpa [k] using fmt.sameExponentMantissaDiffInt_cast m n
  by_cases hkneg : k < 0
  · have hk_abs_int : (((k.natAbs : ℕ) : ℤ)) = -k := by
      simp [abs_of_neg hkneg]
    have hk_abs_real : ((k.natAbs : ℕ) : ℝ) = -(k : ℝ) := by
      have hcast :
          ((((k.natAbs : ℕ) : ℤ) : ℝ)) = (((-k : ℤ) : ℝ)) :=
        congrArg (fun z : ℤ => (z : ℝ)) hk_abs_int
      simpa using hcast
    cases negative
    · exact Or.inr (Or.inl
        ⟨true, k.natAbs * fmt.beta, e - 1, by simpa [k] using hdiff, hex, by
          rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
          rw [fmt.normalizedValue_mul_beta_predExponent_eq]
          simp [alignedSameExponentSubtractionValue, normalizedValue,
            signValue, hk_cast.symm, hk_abs_real]⟩)
    · exact Or.inr (Or.inl
        ⟨false, k.natAbs * fmt.beta, e - 1, by simpa [k] using hdiff, hex, by
          rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
          rw [fmt.normalizedValue_mul_beta_predExponent_eq]
          simp [alignedSameExponentSubtractionValue, normalizedValue,
            signValue, hk_cast.symm, hk_abs_real]⟩)
  · have hknonneg : 0 ≤ k := le_of_not_gt hkneg
    have hk_abs_int : (((k.natAbs : ℕ) : ℤ)) = k := by
      simp [abs_of_nonneg hknonneg]
    have hk_abs_real : ((k.natAbs : ℕ) : ℝ) = (k : ℝ) := by
      have hcast :
          ((((k.natAbs : ℕ) : ℤ) : ℝ)) = ((k : ℤ) : ℝ) :=
        congrArg (fun z : ℤ => (z : ℝ)) hk_abs_int
      simpa using hcast
    cases negative
    · exact Or.inr (Or.inl
        ⟨false, k.natAbs * fmt.beta, e - 1, by simpa [k] using hdiff, hex, by
          rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
          rw [fmt.normalizedValue_mul_beta_predExponent_eq]
          simp [alignedSameExponentSubtractionValue, normalizedValue,
            signValue, hk_cast.symm, hk_abs_real]⟩)
    · exact Or.inr (Or.inl
        ⟨true, k.natAbs * fmt.beta, e - 1, by simpa [k] using hdiff, hex, by
          rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
          rw [fmt.normalizedValue_mul_beta_predExponent_eq]
          simp [alignedSameExponentSubtractionValue, normalizedValue,
            signValue, hk_cast.symm, hk_abs_real]⟩)

/-- Direct arbitrary-shift renormalization subcase for Sterbenz-style exact
subtraction: if shifting any finite number of base digits from the exponent
into the exact same-exponent mantissa difference gives a normalized mantissa,
then the exact subtraction result is a finite normalized floating-point value
at the shifted exponent. -/
theorem normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_beta_pow_mul_normalizedDiff
    {fmt : FloatingPointFormat} {negative : Bool} {m n shift : ℕ} {e : ℤ}
    (hex : fmt.exponentInRange (e - (shift : ℤ)))
    (hdiff : fmt.normalizedMantissa
      ((fmt.sameExponentMantissaDiffInt m n).natAbs * fmt.beta ^ shift)) :
    fmt.finiteSystem
      (fmt.normalizedValue negative m e -
        fmt.normalizedValue negative n e) := by
  let k := fmt.sameExponentMantissaDiffInt m n
  have hk_cast : (k : ℝ) = (m : ℝ) - (n : ℝ) := by
    simpa [k] using fmt.sameExponentMantissaDiffInt_cast m n
  by_cases hkneg : k < 0
  · have hk_abs_int : (((k.natAbs : ℕ) : ℤ)) = -k := by
      simp [abs_of_neg hkneg]
    have hk_abs_real : ((k.natAbs : ℕ) : ℝ) = -(k : ℝ) := by
      have hcast :
          ((((k.natAbs : ℕ) : ℤ) : ℝ)) = (((-k : ℤ) : ℝ)) :=
        congrArg (fun z : ℤ => (z : ℝ)) hk_abs_int
      simpa using hcast
    cases negative
    · exact Or.inr (Or.inl
        ⟨true, k.natAbs * fmt.beta ^ shift, e - (shift : ℤ),
          by simpa [k] using hdiff, hex, by
          rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
          rw [fmt.normalizedValue_mul_beta_pow_subExponent_eq]
          simp [alignedSameExponentSubtractionValue, normalizedValue,
            signValue, hk_cast.symm, hk_abs_real]⟩)
    · exact Or.inr (Or.inl
        ⟨false, k.natAbs * fmt.beta ^ shift, e - (shift : ℤ),
          by simpa [k] using hdiff, hex, by
          rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
          rw [fmt.normalizedValue_mul_beta_pow_subExponent_eq]
          simp [alignedSameExponentSubtractionValue, normalizedValue,
            signValue, hk_cast.symm, hk_abs_real]⟩)
  · have hknonneg : 0 ≤ k := le_of_not_gt hkneg
    have hk_abs_int : (((k.natAbs : ℕ) : ℤ)) = k := by
      simp [abs_of_nonneg hknonneg]
    have hk_abs_real : ((k.natAbs : ℕ) : ℝ) = (k : ℝ) := by
      have hcast :
          ((((k.natAbs : ℕ) : ℤ) : ℝ)) = ((k : ℤ) : ℝ) :=
        congrArg (fun z : ℤ => (z : ℝ)) hk_abs_int
      simpa using hcast
    cases negative
    · exact Or.inr (Or.inl
        ⟨false, k.natAbs * fmt.beta ^ shift, e - (shift : ℤ),
          by simpa [k] using hdiff, hex, by
          rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
          rw [fmt.normalizedValue_mul_beta_pow_subExponent_eq]
          simp [alignedSameExponentSubtractionValue, normalizedValue,
            signValue, hk_cast.symm, hk_abs_real]⟩)
    · exact Or.inr (Or.inl
        ⟨true, k.natAbs * fmt.beta ^ shift, e - (shift : ℤ),
          by simpa [k] using hdiff, hex, by
          rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
          rw [fmt.normalizedValue_mul_beta_pow_subExponent_eq]
          simp [alignedSameExponentSubtractionValue, normalizedValue,
            signValue, hk_cast.symm, hk_abs_real]⟩)

/-- A renormalization selector witness is enough to prove same-exponent exact
subtraction is finite. -/
theorem normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_renormalizationWitness
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hw : fmt.sameExponentRenormalizationWitness m n e) :
    fmt.finiteSystem
      (fmt.normalizedValue negative m e -
        fmt.normalizedValue negative n e) := by
  rcases hw with ⟨shift, hex, hdiff⟩
  exact
    fmt.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_beta_pow_mul_normalizedDiff
      (negative := negative) (m := m) (n := n) (e := e)
      (shift := shift) hex hdiff

/-- Direct subnormal endpoint for Sterbenz-style exact subtraction: at the
smallest normal exponent, a same-exponent exact mantissa difference below the
normal leading-digit threshold is either zero or a finite subnormal value. -/
theorem normalizedValue_sub_sameSign_sameExponent_finiteSystem_at_emin_of_natAbs_lt_minNormalMantissa
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ}
    (hdiff :
      (fmt.sameExponentMantissaDiffInt m n).natAbs < fmt.minNormalMantissa) :
    fmt.finiteSystem
      (fmt.normalizedValue negative m fmt.emin -
        fmt.normalizedValue negative n fmt.emin) := by
  let k := fmt.sameExponentMantissaDiffInt m n
  have hk_cast : (k : ℝ) = (m : ℝ) - (n : ℝ) := by
    simpa [k] using fmt.sameExponentMantissaDiffInt_cast m n
  by_cases hkzero : k = 0
  · left
    rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
    simp [alignedSameExponentSubtractionValue, signValue, hk_cast.symm, hkzero]
  · by_cases hkneg : k < 0
    · have hk_abs_int : (((k.natAbs : ℕ) : ℤ)) = -k := by
        simp [abs_of_neg hkneg]
      have hk_abs_real : ((k.natAbs : ℕ) : ℝ) = -(k : ℝ) := by
        have hcast :
            ((((k.natAbs : ℕ) : ℤ) : ℝ)) = (((-k : ℤ) : ℝ)) :=
          congrArg (fun z : ℤ => (z : ℝ)) hk_abs_int
        simpa using hcast
      have hpos_int : (0 : ℤ) < ((k.natAbs : ℕ) : ℤ) := by
        rw [hk_abs_int]
        exact neg_pos.mpr hkneg
      have hpos : 0 < k.natAbs := by
        exact_mod_cast hpos_int
      have hsub : fmt.subnormalMantissa k.natAbs :=
        ⟨hpos, by simpa [k] using hdiff⟩
      cases negative
      · exact Or.inr (Or.inr
          ⟨true, k.natAbs, hsub, by
            rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
            simp [alignedSameExponentSubtractionValue, subnormalValue,
              signValue, hk_cast.symm, hk_abs_real]⟩)
      · exact Or.inr (Or.inr
          ⟨false, k.natAbs, hsub, by
            rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
            simp [alignedSameExponentSubtractionValue, subnormalValue,
              signValue, hk_cast.symm, hk_abs_real]⟩)
    · have hknonneg : 0 ≤ k := le_of_not_gt hkneg
      have hkpos_int : (0 : ℤ) < k := by
        exact lt_of_le_of_ne hknonneg (fun h => hkzero h.symm)
      have hk_abs_int : (((k.natAbs : ℕ) : ℤ)) = k := by
        simp [abs_of_nonneg hknonneg]
      have hk_abs_real : ((k.natAbs : ℕ) : ℝ) = (k : ℝ) := by
        have hcast :
            ((((k.natAbs : ℕ) : ℤ) : ℝ)) = ((k : ℤ) : ℝ) :=
          congrArg (fun z : ℤ => (z : ℝ)) hk_abs_int
        simpa using hcast
      have hpos_int : (0 : ℤ) < ((k.natAbs : ℕ) : ℤ) := by
        rw [hk_abs_int]
        exact hkpos_int
      have hpos : 0 < k.natAbs := by
        exact_mod_cast hpos_int
      have hsub : fmt.subnormalMantissa k.natAbs :=
        ⟨hpos, by simpa [k] using hdiff⟩
      cases negative
      · exact Or.inr (Or.inr
          ⟨false, k.natAbs, hsub, by
            rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
            simp [alignedSameExponentSubtractionValue, subnormalValue,
              signValue, hk_cast.symm, hk_abs_real]⟩)
      · exact Or.inr (Or.inr
          ⟨true, k.natAbs, hsub, by
            rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
            simp [alignedSameExponentSubtractionValue, subnormalValue,
              signValue, hk_cast.symm, hk_abs_real]⟩)

/-- Shifted direct subnormal endpoint for Sterbenz-style exact subtraction:
after shifting some finite number of base digits from the exponent into the
same-exponent exact mantissa difference, if the shifted exponent is `emin` and
the shifted coefficient is below the normalized leading-digit threshold, then
the exact subtraction result is finite. -/
theorem normalizedValue_sub_sameSign_sameExponent_finiteSystem_at_shifted_emin_of_natAbs_mul_beta_pow_lt_minNormalMantissa
    {fmt : FloatingPointFormat} {negative : Bool} {m n shift : ℕ} {e : ℤ}
    (he : e - (shift : ℤ) = fmt.emin)
    (hdiff :
      (fmt.sameExponentMantissaDiffInt m n).natAbs * fmt.beta ^ shift <
        fmt.minNormalMantissa) :
    fmt.finiteSystem
      (fmt.normalizedValue negative m e -
        fmt.normalizedValue negative n e) := by
  let k := fmt.sameExponentMantissaDiffInt m n
  have hk_cast : (k : ℝ) = (m : ℝ) - (n : ℝ) := by
    simpa [k] using fmt.sameExponentMantissaDiffInt_cast m n
  by_cases hkzero : k = 0
  · exact
      fmt.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_natAbs_eq_zero
        (negative := negative) (m := m) (n := n) (e := e)
        (by simp [k, hkzero])
  · have hkabs_pos : 0 < k.natAbs := by
      exact Nat.pos_of_ne_zero (mt Int.natAbs_eq_zero.mp hkzero)
    have hscale_pos :
        0 < k.natAbs * fmt.beta ^ shift := by
      exact Nat.mul_pos hkabs_pos
        (Nat.pow_pos (lt_of_lt_of_le (by decide : 0 < 2) fmt.beta_ge_two))
    have hsub :
        fmt.subnormalMantissa (k.natAbs * fmt.beta ^ shift) :=
      ⟨hscale_pos, by simpa [k] using hdiff⟩
    by_cases hkneg : k < 0
    · have hk_abs_int : (((k.natAbs : ℕ) : ℤ)) = -k := by
        simp [abs_of_neg hkneg]
      have hk_abs_real : ((k.natAbs : ℕ) : ℝ) = -(k : ℝ) := by
        have hcast :
            ((((k.natAbs : ℕ) : ℤ) : ℝ)) = (((-k : ℤ) : ℝ)) :=
          congrArg (fun z : ℤ => (z : ℝ)) hk_abs_int
        simpa using hcast
      cases negative
      · exact Or.inr (Or.inr
          ⟨true, k.natAbs * fmt.beta ^ shift, hsub, by
            rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
            rw [← fmt.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
              (negative := true) (m := k.natAbs) (shift := shift)
              (e := e) he]
            simp [alignedSameExponentSubtractionValue, normalizedValue,
              signValue, hk_cast.symm, hk_abs_real]⟩)
      · exact Or.inr (Or.inr
          ⟨false, k.natAbs * fmt.beta ^ shift, hsub, by
            rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
            rw [← fmt.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
              (negative := false) (m := k.natAbs) (shift := shift)
              (e := e) he]
            simp [alignedSameExponentSubtractionValue, normalizedValue,
              signValue, hk_cast.symm, hk_abs_real]⟩)
    · have hknonneg : 0 ≤ k := le_of_not_gt hkneg
      have hk_abs_int : (((k.natAbs : ℕ) : ℤ)) = k := by
        simp [abs_of_nonneg hknonneg]
      have hk_abs_real : ((k.natAbs : ℕ) : ℝ) = (k : ℝ) := by
        have hcast :
            ((((k.natAbs : ℕ) : ℤ) : ℝ)) = ((k : ℤ) : ℝ) :=
          congrArg (fun z : ℤ => (z : ℝ)) hk_abs_int
        simpa using hcast
      cases negative
      · exact Or.inr (Or.inr
          ⟨false, k.natAbs * fmt.beta ^ shift, hsub, by
            rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
            rw [← fmt.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
              (negative := false) (m := k.natAbs) (shift := shift)
              (e := e) he]
            simp [alignedSameExponentSubtractionValue, normalizedValue,
              signValue, hk_cast.symm, hk_abs_real]⟩)
      · exact Or.inr (Or.inr
          ⟨true, k.natAbs * fmt.beta ^ shift, hsub, by
            rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
            rw [← fmt.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
              (negative := true) (m := k.natAbs) (shift := shift)
              (e := e) he]
            simp [alignedSameExponentSubtractionValue, normalizedValue,
              signValue, hk_cast.symm, hk_abs_real]⟩)

/-- A shifted subnormal endpoint selector witness is enough to prove
same-exponent exact subtraction is finite. -/
theorem normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_subnormalEndpointWitness
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hw : fmt.sameExponentSubnormalEndpointWitness m n e) :
    fmt.finiteSystem
      (fmt.normalizedValue negative m e -
        fmt.normalizedValue negative n e) := by
  rcases hw with ⟨shift, he, hdiff⟩
  exact
    fmt.normalizedValue_sub_sameSign_sameExponent_finiteSystem_at_shifted_emin_of_natAbs_mul_beta_pow_lt_minNormalMantissa
      (negative := negative) (m := m) (n := n) (e := e)
      (shift := shift) he hdiff

/-- The closed same-exponent finite-difference witness packages the direct
Sterbenz-style finite representability cases currently proved in Lean: exact
zero, normalized finite renormalization shift, or the shifted `emin` subnormal
endpoint. -/
theorem normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_finiteDifferenceWitness
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hw : fmt.sameExponentFiniteDifferenceWitness m n e) :
    fmt.finiteSystem
      (fmt.normalizedValue negative m e -
        fmt.normalizedValue negative n e) := by
  rcases hw with hzero | hrenorm | hemin
  · exact
      fmt.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_natAbs_eq_zero
        (negative := negative) (m := m) (n := n) (e := e) hzero
  · exact
      fmt.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_renormalizationWitness
        (negative := negative) (m := m) (n := n) (e := e) hrenorm
  · exact
      fmt.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_subnormalEndpointWitness
        (negative := negative) (m := m) (n := n) (e := e) hemin

/-- Source-facing same-exponent finite-subtraction theorem: for two finite
normalized operands with the same exponent and sign, the exact difference is a
finite floating-point number.  The proof derives the finite-difference selector
from the operand mantissas and exponent range. -/
theorem normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_normalizedMantissas
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (he : fmt.exponentInRange e) :
    fmt.finiteSystem
      (fmt.normalizedValue negative m e -
        fmt.normalizedValue negative n e) :=
  fmt.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_finiteDifferenceWitness
    (negative := negative) (m := m) (n := n) (e := e)
    (fmt.sameExponentFiniteDifferenceWitness_of_normalizedMantissas hm hn he)

/-- Positive normalized Sterbenz finite-representability theorem.  For any two
positive normalized finite operands whose exponents are in range, the exact
subtraction is finite whenever Sterbenz's ratio condition holds. -/
theorem normalizedValue_sub_positive_finiteSystem_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (he : fmt.exponentInRange e) (he' : fmt.exponentInRange e')
    (hsterbenz : fmt.sterbenzRatioCondition
      (fmt.normalizedValue false m e)
      (fmt.normalizedValue false n e')) :
    fmt.finiteSystem
      (fmt.normalizedValue false m e -
        fmt.normalizedValue false n e') := by
  have hgap :=
    fmt.sterbenzRatioCondition_positive_normalized_exponent_gap_le_one
      (m := m) (n := n) (e := e) (e' := e') hm hn hsterbenz
  have hcases : e = e' ∨ e = e' + 1 ∨ e' = e + 1 := by
    omega
  rcases hcases with heq | hcases
  · subst e'
    exact
      fmt.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_normalizedMantissas
        (negative := false) (m := m) (n := n) (e := e) hm hn he
  · rcases hcases with hsucc | hpred
    · subst e
      exact
        fmt.normalizedValue_sub_positive_adjacentExponent_finiteSystem_of_sterbenzAdjacent
          (mHigh := m) (mLow := n) (e := e') hm hn he' hsterbenz
    · subst e'
      have hsymm :
          fmt.sterbenzRatioCondition
            (fmt.normalizedValue false n (e + 1))
            (fmt.normalizedValue false m e) :=
        fmt.sterbenzRatioCondition_symm hsterbenz
      have hfin_yx :
          fmt.finiteSystem
            (fmt.normalizedValue false n (e + 1) -
              fmt.normalizedValue false m e) :=
        fmt.normalizedValue_sub_positive_adjacentExponent_finiteSystem_of_sterbenzAdjacent
          (mHigh := n) (mLow := m) (e := e) hn hm he hsymm
      have hneg := fmt.finiteSystem_neg hfin_yx
      convert hneg using 1
      ring

/-- Source-shaped normalized Sterbenz finite-representability theorem.  The
ratio condition forces normalized finite operands to be positive, so their sign
bits reduce to the positive-normalized theorem above. -/
theorem normalizedSystem_sub_finiteSystem_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.normalizedSystem x)
    (hy : fmt.normalizedSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteSystem (x - y) := by
  rcases hx with ⟨negativeX, m, e, hm, he, rfl⟩
  rcases hy with ⟨negativeY, n, e', hn, he', rfl⟩
  cases negativeX
  · cases negativeY
    · exact
        fmt.normalizedValue_sub_positive_finiteSystem_of_sterbenzRatioCondition
          (m := m) (n := n) (e := e) (e' := e')
          hm hn he he' hsterbenz
    · have hypos := fmt.sterbenzRatioCondition_y_pos hsterbenz
      have hyneg := fmt.normalizedValue_true_neg (m := n) (e := e') hn
      linarith
  · have hxpos := fmt.sterbenzRatioCondition_x_pos hsterbenz
    have hxneg := fmt.normalizedValue_true_neg (m := m) (e := e) hm
    linarith

/-- Same-sign subnormal subtraction is finite: both operands lie on the common
subnormal lattice, so the exact integer coefficient still has fewer than `t`
radix digits. -/
theorem subnormalValue_sub_sameSign_finiteSystem_of_subnormalMantissas
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ}
    (hm : fmt.subnormalMantissa m)
    (hn : fmt.subnormalMantissa n) :
    fmt.finiteSystem
      (fmt.subnormalValue negative m -
        fmt.subnormalValue negative n) := by
  have hmrange : fmt.mantissaInRange m :=
    fmt.subnormalMantissa_inRange hm
  have hnrange : fmt.mantissaInRange n :=
    fmt.subnormalMantissa_inRange hn
  have hcoeff :
      (fmt.sameExponentMantissaDiffInt m n).natAbs < fmt.beta ^ fmt.t :=
    fmt.sameExponentMantissaDiffInt_natAbs_lt_mantissaBound hmrange hnrange
  have hfin :
      fmt.finiteSystem
        (fmt.signValue negative *
          ((fmt.sameExponentMantissaDiffInt m n : ℤ) : ℝ) *
          fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) :=
    fmt.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
      (negative := negative)
      (k := fmt.sameExponentMantissaDiffInt m n)
      (e := fmt.emin) ⟨le_rfl, fmt.emin_le_emax⟩ hcoeff
  convert hfin using 1
  rw [fmt.sameExponentMantissaDiffInt_cast m n]
  simp [subnormalValue]
  ring

/-- Same-sign subnormal addition is finite: both operands share the minimum
subnormal lattice spacing, and the sum coefficient stays below the normalized
mantissa bound. -/
theorem subnormalValue_add_sameSign_finiteSystem_of_subnormalMantissas
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ}
    (hm : fmt.subnormalMantissa m)
    (hn : fmt.subnormalMantissa n) :
    fmt.finiteSystem
      (fmt.subnormalValue negative m + fmt.subnormalValue negative n) := by
  have hsum_lt_min_sum :
      m + n < fmt.minNormalMantissa + fmt.minNormalMantissa :=
    Nat.add_lt_add hm.2 hn.2
  have hsum_lt_bound : m + n < fmt.beta ^ fmt.t := by
    have hle_two :
        fmt.minNormalMantissa + fmt.minNormalMantissa ≤
          fmt.minNormalMantissa * fmt.beta := by
      calc
        fmt.minNormalMantissa + fmt.minNormalMantissa =
            fmt.minNormalMantissa * 2 := by omega
        _ ≤ fmt.minNormalMantissa * fmt.beta :=
            Nat.mul_le_mul_left fmt.minNormalMantissa fmt.beta_ge_two
    exact lt_of_lt_of_le hsum_lt_min_sum
      (by simpa [fmt.minNormalMantissa_mul_beta_eq_mantissaBound] using hle_two)
  have hfin :
      fmt.finiteSystem
        (fmt.signValue negative * (((m + n : ℕ) : ℤ) : ℝ) *
          fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) :=
    fmt.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
      (negative := negative)
      (k := ((m + n : ℕ) : ℤ))
      (e := fmt.emin)
      ⟨le_rfl, fmt.emin_le_emax⟩
      (by simpa using hsum_lt_bound)
  convert hfin using 1
  simp [subnormalValue, Nat.cast_add]
  ring

/-- Same-sign mixed normal/subnormal addition is finite when the normalized
operand, shifted onto the subnormal lattice, plus the subnormal coefficient
still fits in `t` radix digits. -/
theorem normalizedValue_add_sameSign_subnormal_finiteSystem_of_alignedCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (_hm : fmt.normalizedMantissa m)
    (_hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hcoeff :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n < fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      (fmt.normalizedValue negative m e + fmt.subnormalValue negative n) := by
  let q := Int.toNat (e - fmt.emin)
  have hq_cast : ((q : ℕ) : ℤ) = e - fmt.emin := by
    have hnonneg : 0 ≤ e - fmt.emin := sub_nonneg.mpr he.1
    simpa [q] using Int.toNat_of_nonneg hnonneg
  have hq_endpoint : e - (q : ℤ) = fmt.emin := by
    omega
  have hshift :
      fmt.normalizedValue negative m e =
        fmt.subnormalValue negative (m * fmt.beta ^ q) :=
    fmt.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
      (negative := negative) (m := m) (shift := q) (e := e) hq_endpoint
  have hfin :
      fmt.finiteSystem
        (fmt.signValue negative *
          ((((m * fmt.beta ^ q + n : ℕ) : ℤ) : ℝ)) *
          fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) :=
    fmt.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
      (negative := negative)
      (k := ((m * fmt.beta ^ q + n : ℕ) : ℤ))
      (e := fmt.emin)
      ⟨le_rfl, fmt.emin_le_emax⟩
      (by simpa [q] using hcoeff)
  convert hfin using 1
  rw [hshift]
  simp [subnormalValue, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  ring

/-- Source-shaped subnormal Sterbenz finite-representability theorem.  The
ratio condition forces both subnormal finite operands to be positive, reducing
the proof to the same-sign subnormal lattice theorem. -/
theorem subnormalSystem_sub_finiteSystem_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.subnormalSystem x)
    (hy : fmt.subnormalSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteSystem (x - y) := by
  rcases hx with ⟨negativeX, m, hm, rfl⟩
  rcases hy with ⟨negativeY, n, hn, rfl⟩
  cases negativeX
  · cases negativeY
    · exact
        fmt.subnormalValue_sub_sameSign_finiteSystem_of_subnormalMantissas
          (negative := false) (m := m) (n := n) hm hn
    · have hypos := fmt.sterbenzRatioCondition_y_pos hsterbenz
      have hyneg := fmt.subnormalValue_true_neg (m := n) hn
      linarith
  · have hxpos := fmt.sterbenzRatioCondition_x_pos hsterbenz
    have hxneg := fmt.subnormalValue_true_neg (m := m) hm
    linarith

/-- Positive mixed normal/subnormal Sterbenz finite-representability theorem.
The normalized operand is rewritten on the subnormal lattice with integer
coefficient `m * beta^(e - emin)`, and the Sterbenz upper ratio bounds that
coefficient below twice the subnormal mantissa. -/
theorem normalizedValue_sub_subnormalValue_positive_finiteSystem_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hsterbenz : fmt.sterbenzRatioCondition
      (fmt.normalizedValue false m e)
      (fmt.subnormalValue false n)) :
    fmt.finiteSystem
      (fmt.normalizedValue false m e -
        fmt.subnormalValue false n) := by
  let q := Int.toNat (e - fmt.emin)
  let a := m * fmt.beta ^ q
  have _hm_range : fmt.mantissaInRange m := hm.2
  have hq_cast : ((q : ℕ) : ℤ) = e - fmt.emin := by
    have hnonneg : 0 ≤ e - fmt.emin := sub_nonneg.mpr he.1
    simpa [q] using Int.toNat_of_nonneg hnonneg
  have hq_endpoint : e - (q : ℤ) = fmt.emin := by
    omega
  have hshift :
      fmt.normalizedValue false a fmt.emin =
        fmt.normalizedValue false m e := by
    have h :=
      fmt.normalizedValue_mul_beta_pow_subExponent_eq
        (negative := false) (m := m) (shift := q) (e := e)
    rw [hq_endpoint] at h
    simpa [a] using h
  let s := fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))
  have hs_pos : 0 < s := fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ))
  have hx_expr :
      fmt.normalizedValue false m e = (a : ℝ) * s := by
    rw [← hshift]
    simp [a, s, normalizedValue, signValue]
  have hy_expr :
      fmt.subnormalValue false n = (n : ℝ) * s := by
    simp [s, subnormalValue, signValue]
  have ha_lt_two_n_real : (a : ℝ) < 2 * (n : ℝ) := by
    have hxlt := hsterbenz.2
    rw [hx_expr, hy_expr] at hxlt
    have hxlt' :
        (a : ℝ) * s < (2 * (n : ℝ)) * s := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hxlt
    exact lt_of_mul_lt_mul_right hxlt' (le_of_lt hs_pos)
  have ha_lt_two_n : a < 2 * n := by
    exact_mod_cast ha_lt_two_n_real
  have ha_range : fmt.mantissaInRange a := by
    have htwo_n_lt :
        2 * n < 2 * fmt.minNormalMantissa :=
      Nat.mul_lt_mul_of_pos_left hn.2 (by decide)
    have htwo_min_le :
        2 * fmt.minNormalMantissa ≤ fmt.beta * fmt.minNormalMantissa :=
      Nat.mul_le_mul_right fmt.minNormalMantissa fmt.beta_ge_two
    have hbound :
        fmt.beta * fmt.minNormalMantissa = fmt.beta ^ fmt.t := by
      rw [Nat.mul_comm]
      exact fmt.minNormalMantissa_mul_beta_eq_mantissaBound
    exact lt_of_lt_of_le (lt_trans ha_lt_two_n htwo_n_lt)
      (by simpa [hbound] using htwo_min_le)
  have hn_range : fmt.mantissaInRange n :=
    fmt.subnormalMantissa_inRange hn
  have hcoeff :
      (fmt.sameExponentMantissaDiffInt a n).natAbs < fmt.beta ^ fmt.t :=
    fmt.sameExponentMantissaDiffInt_natAbs_lt_mantissaBound
      (m := a) (n := n) ha_range hn_range
  have hfin :
      fmt.finiteSystem
        (fmt.signValue false *
          ((fmt.sameExponentMantissaDiffInt a n : ℤ) : ℝ) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) :=
    fmt.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
      (negative := false)
      (k := fmt.sameExponentMantissaDiffInt a n)
      (e := fmt.emin) ⟨le_rfl, fmt.emin_le_emax⟩ hcoeff
  convert hfin using 1
  rw [← hshift, fmt.sameExponentMantissaDiffInt_cast a n]
  simp [normalizedValue, subnormalValue, signValue]
  ring

/-- Source-shaped mixed normal/subnormal Sterbenz finite-representability
theorem.  The ratio condition forces both operands to be positive, reducing the
proof to the positive mixed lattice theorem. -/
theorem normalizedSystem_sub_subnormalSystem_finiteSystem_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.normalizedSystem x)
    (hy : fmt.subnormalSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteSystem (x - y) := by
  rcases hx with ⟨negativeX, m, e, hm, he, rfl⟩
  rcases hy with ⟨negativeY, n, hn, rfl⟩
  cases negativeX
  · cases negativeY
    · exact
        fmt.normalizedValue_sub_subnormalValue_positive_finiteSystem_of_sterbenzRatioCondition
          (m := m) (n := n) (e := e) hm hn he hsterbenz
    · have hypos := fmt.sterbenzRatioCondition_y_pos hsterbenz
      have hyneg := fmt.subnormalValue_true_neg (m := n) hn
      linarith
  · have hxpos := fmt.sterbenzRatioCondition_x_pos hsterbenz
    have hxneg := fmt.normalizedValue_true_neg (m := m) (e := e) hm
    linarith

/-- Source-shaped mixed subnormal/normal Sterbenz finite-representability
theorem, obtained by symmetry and finite-system closure under negation. -/
theorem subnormalSystem_sub_normalizedSystem_finiteSystem_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.subnormalSystem x)
    (hy : fmt.normalizedSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteSystem (x - y) := by
  have hsymm : fmt.sterbenzRatioCondition y x :=
    fmt.sterbenzRatioCondition_symm hsterbenz
  have hfin_yx : fmt.finiteSystem (y - x) :=
    fmt.normalizedSystem_sub_subnormalSystem_finiteSystem_of_sterbenzRatioCondition
      hy hx hsymm
  have hneg := fmt.finiteSystem_neg hfin_yx
  convert hneg using 1
  ring

/-- Full finite-system Sterbenz finite-representability theorem for the
source-facing real finite format.  Zero cases are impossible under Sterbenz's
strict positive ratio condition; the remaining normal/subnormal cases dispatch
to the closed branch theorems. -/
theorem finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystem x)
    (hy : fmt.finiteSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteSystem (x - y) := by
  rcases hx with hxzero | hxnorm | hxsub
  · subst x
    have hxpos := fmt.sterbenzRatioCondition_x_pos hsterbenz
    linarith
  rcases hy with hyzero | hynorm | hysub
  · subst y
    have hypos := fmt.sterbenzRatioCondition_y_pos hsterbenz
    linarith
  · exact
      fmt.normalizedSystem_sub_finiteSystem_of_sterbenzRatioCondition
        hxnorm hynorm hsterbenz
  · exact
      fmt.normalizedSystem_sub_subnormalSystem_finiteSystem_of_sterbenzRatioCondition
        hxnorm hysub hsterbenz
  rcases hy with hyzero | hynorm | hysub
  · subst y
    have hypos := fmt.sterbenzRatioCondition_y_pos hsterbenz
    linarith
  · exact
      fmt.subnormalSystem_sub_normalizedSystem_finiteSystem_of_sterbenzRatioCondition
        hxsub hynorm hsterbenz
  · exact
      fmt.subnormalSystem_sub_finiteSystem_of_sterbenzRatioCondition
        hxsub hysub hsterbenz

/-- The unshifted `emin` endpoint remains available as a constructor for the
new shifted subnormal endpoint witness. -/
theorem sameExponentSubnormalEndpointWitness_of_emin_natAbs_lt_minNormalMantissa
    {fmt : FloatingPointFormat} {m n : ℕ} {e : ℤ}
    (he : e = fmt.emin)
    (hdiff :
      (fmt.sameExponentMantissaDiffInt m n).natAbs <
        fmt.minNormalMantissa) :
    fmt.sameExponentSubnormalEndpointWitness m n e := by
  refine ⟨0, ?_, ?_⟩
  · simp [he]
  · simpa using hdiff

/-- The old unshifted `emin` endpoint is a special case of the packaged
finite-difference witness. -/
theorem sameExponentFiniteDifferenceWitness_of_emin_natAbs_lt_minNormalMantissa
    {fmt : FloatingPointFormat} {m n : ℕ} {e : ℤ}
    (he : e = fmt.emin)
    (hdiff :
      (fmt.sameExponentMantissaDiffInt m n).natAbs <
        fmt.minNormalMantissa) :
    fmt.sameExponentFiniteDifferenceWitness m n e := by
    exact
      Or.inr (Or.inr
        (fmt.sameExponentSubnormalEndpointWitness_of_emin_natAbs_lt_minNormalMantissa
          (m := m) (n := n) (e := e) he hdiff))

theorem guardDigitLeadingDigit_eq_zero_of_fergusonAdjacent
    {fmt : FloatingPointFormat} {negative : Bool} {mHigh mLow : ℕ}
    {e ez : ℤ}
    (hz : fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negative mHigh (e + 1) -
        fmt.normalizedValue negative mLow e) ez)
    (hcond : ez < e) :
    fmt.guardDigitLeadingDigit
      (fmt.guardAlignedMantissaDiffInt mHigh mLow) = 0 := by
  apply fmt.guardDigitLeadingDigit_eq_zero_of_natAbs_lt_minNormalMantissa
  exact fmt.guardAlignedMantissaDiffInt_natAbs_lt_minNormalMantissa_of_fergusonAdjacent
    (negative := negative) (mHigh := mHigh) (mLow := mLow)
    (e := e) (ez := ez) hz hcond

theorem guardDigitTailMantissa_eq_natAbs_of_fergusonAdjacent
    {fmt : FloatingPointFormat} {negative : Bool} {mHigh mLow : ℕ}
    {e ez : ℤ}
    (hz : fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negative mHigh (e + 1) -
        fmt.normalizedValue negative mLow e) ez)
    (hcond : ez < e) :
    fmt.guardDigitTailMantissa
      (fmt.guardAlignedMantissaDiffInt mHigh mLow) =
        (fmt.guardAlignedMantissaDiffInt mHigh mLow).natAbs := by
  apply fmt.guardDigitTailMantissa_eq_natAbs_of_natAbs_lt_minNormalMantissa
  exact fmt.guardAlignedMantissaDiffInt_natAbs_lt_minNormalMantissa_of_fergusonAdjacent
    (negative := negative) (mHigh := mHigh) (mLow := mLow)
    (e := e) (ez := ez) hz hcond

theorem guardDigitRoundedCoeff_eq_self_of_fergusonAdjacent
    {fmt : FloatingPointFormat} {negative : Bool} {mHigh mLow : ℕ}
    {e ez : ℤ}
    (hz : fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negative mHigh (e + 1) -
        fmt.normalizedValue negative mLow e) ez)
    (hcond : ez < e) :
    fmt.guardDigitRoundedCoeff
      (fmt.guardAlignedMantissaDiffInt mHigh mLow) =
        fmt.guardAlignedMantissaDiffInt mHigh mLow := by
  apply fmt.guardDigitRoundedCoeff_eq_self_of_natAbs_lt_minNormalMantissa
  exact fmt.guardAlignedMantissaDiffInt_natAbs_lt_minNormalMantissa_of_fergusonAdjacent
    (negative := negative) (mHigh := mHigh) (mLow := mLow)
    (e := e) (ez := ez) hz hcond

/-- Adjacent-exponent subtraction value after the guard word is rounded to t
digits by dropping the zero leading guard digit. -/
def guardDigitRoundedAdjacentExponentSubtractionValue
    (fmt : FloatingPointFormat) (negative : Bool) (mHigh mLow : ℕ)
    (e : ℤ) : ℝ :=
  fmt.signValue negative *
    (((fmt.guardDigitRoundedCoeff
      (fmt.guardAlignedMantissaDiffInt mHigh mLow) : ℤ) : ℝ) *
      fmt.betaR ^ (e - (fmt.t : ℤ)))

theorem normalizedValue_sub_sameSign_adjacentExponent_eq_guardDigitRounded_of_fergusonAdjacent
    {fmt : FloatingPointFormat} {negative : Bool} {mHigh mLow : ℕ}
    {e ez : ℤ}
    (hz : fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negative mHigh (e + 1) -
        fmt.normalizedValue negative mLow e) ez)
    (hcond : ez < e) :
    fmt.normalizedValue negative mHigh (e + 1) -
        fmt.normalizedValue negative mLow e =
      fmt.guardDigitRoundedAdjacentExponentSubtractionValue
        negative mHigh mLow e := by
  have hround :
      fmt.guardDigitRoundedCoeff
        (fmt.guardAlignedMantissaDiffInt mHigh mLow) =
          fmt.guardAlignedMantissaDiffInt mHigh mLow :=
    fmt.guardDigitRoundedCoeff_eq_self_of_fergusonAdjacent
      (negative := negative) (mHigh := mHigh) (mLow := mLow)
      (e := e) (ez := ez) hz hcond
  have hcast :
      (((fmt.guardDigitRoundedCoeff
        (fmt.guardAlignedMantissaDiffInt mHigh mLow) : ℤ) : ℝ)) =
        fmt.guardAlignedMantissaDiff mHigh mLow := by
    rw [hround]
    exact fmt.guardAlignedMantissaDiffInt_cast mHigh mLow
  rw [fmt.normalizedValue_sub_sameSign_adjacentExponent_eq_aligned]
  simp [guardDigitRoundedAdjacentExponentSubtractionValue,
    alignedAdjacentExponentSubtractionValue, hcast]

theorem guardAlignedMantissaDiff_abs_lt_minNormalMantissa_of_fergusonAdjacent_reversed
    {fmt : FloatingPointFormat} {negative : Bool} {mHigh mLow : ℕ}
    {e ez : ℤ}
    (hz : fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negative mLow e -
        fmt.normalizedValue negative mHigh (e + 1)) ez)
    (hcond : ez < e) :
    |fmt.guardAlignedMantissaDiff mHigh mLow| <
      (fmt.minNormalMantissa : ℝ) := by
  have hz_upper :
      |fmt.normalizedValue negative mLow e -
        fmt.normalizedValue negative mHigh (e + 1)| < fmt.betaR ^ ez :=
    fmt.normalizedExponentRepresentation_abs_lt_beta_pow hz
  have hz_lt_lower :
      |fmt.normalizedValue negative mLow e -
        fmt.normalizedValue negative mHigh (e + 1)| < fmt.betaR ^ (e - 1) :=
    lt_of_lt_of_le hz_upper
      (fmt.betaR_zpow_le_zpow_of_le (by omega : ez ≤ e - 1))
  have hvalue :=
    fmt.normalizedValue_sub_sameSign_adjacentExponent_eq_aligned
      negative mHigh mLow e
  have hscale_pos : 0 < fmt.betaR ^ (e - (fmt.t : ℤ)) :=
    fmt.betaR_zpow_pos (e - (fmt.t : ℤ))
  have hscaled :
      |fmt.guardAlignedMantissaDiff mHigh mLow| *
          fmt.betaR ^ (e - (fmt.t : ℤ)) <
        (fmt.minNormalMantissa : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)) := by
    rw [← fmt.alignedAdjacentExponentSubtractionValue_abs negative mHigh mLow e]
    rw [← hvalue]
    rw [abs_sub_comm]
    simpa [fmt.minNormalMantissa_scale_eq e] using hz_lt_lower
  exact lt_of_mul_lt_mul_right hscaled (le_of_lt hscale_pos)

theorem guardAlignedMantissaDiffInt_abs_lt_minNormalMantissa_of_fergusonAdjacent_reversed
    {fmt : FloatingPointFormat} {negative : Bool} {mHigh mLow : ℕ}
    {e ez : ℤ}
    (hz : fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negative mLow e -
        fmt.normalizedValue negative mHigh (e + 1)) ez)
    (hcond : ez < e) :
    |fmt.guardAlignedMantissaDiffInt mHigh mLow| <
      (fmt.minNormalMantissa : ℤ) := by
  have hreal :
      |((fmt.guardAlignedMantissaDiffInt mHigh mLow : ℤ) : ℝ)| <
        (fmt.minNormalMantissa : ℝ) := by
    simpa [fmt.guardAlignedMantissaDiffInt_cast mHigh mLow] using
      fmt.guardAlignedMantissaDiff_abs_lt_minNormalMantissa_of_fergusonAdjacent_reversed
        (negative := negative) (mHigh := mHigh) (mLow := mLow)
        (e := e) (ez := ez) hz hcond
  exact_mod_cast hreal

theorem guardAlignedMantissaDiffInt_natAbs_lt_minNormalMantissa_of_fergusonAdjacent_reversed
    {fmt : FloatingPointFormat} {negative : Bool} {mHigh mLow : ℕ}
    {e ez : ℤ}
    (hz : fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negative mLow e -
        fmt.normalizedValue negative mHigh (e + 1)) ez)
    (hcond : ez < e) :
    (fmt.guardAlignedMantissaDiffInt mHigh mLow).natAbs <
      fmt.minNormalMantissa := by
  have hint :
      |fmt.guardAlignedMantissaDiffInt mHigh mLow| <
        (fmt.minNormalMantissa : ℤ) :=
    fmt.guardAlignedMantissaDiffInt_abs_lt_minNormalMantissa_of_fergusonAdjacent_reversed
      (negative := negative) (mHigh := mHigh) (mLow := mLow)
      (e := e) (ez := ez) hz hcond
  have hnatInt :
      (((fmt.guardAlignedMantissaDiffInt mHigh mLow).natAbs : ℕ) : ℤ) <
        (fmt.minNormalMantissa : ℤ) := by
    simpa using hint
  exact_mod_cast hnatInt

theorem normalizedValue_sub_sameSign_reversedAdjacentExponent_eq_neg_guardDigitRounded_of_fergusonAdjacent
    {fmt : FloatingPointFormat} {negative : Bool} {mHigh mLow : ℕ}
    {e ez : ℤ}
    (hz : fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negative mLow e -
        fmt.normalizedValue negative mHigh (e + 1)) ez)
    (hcond : ez < e) :
    fmt.normalizedValue negative mLow e -
        fmt.normalizedValue negative mHigh (e + 1) =
      -fmt.guardDigitRoundedAdjacentExponentSubtractionValue
        negative mHigh mLow e := by
  have hround :
      fmt.guardDigitRoundedCoeff
        (fmt.guardAlignedMantissaDiffInt mHigh mLow) =
          fmt.guardAlignedMantissaDiffInt mHigh mLow :=
    fmt.guardDigitRoundedCoeff_eq_self_of_natAbs_lt_minNormalMantissa
      (fmt.guardAlignedMantissaDiffInt_natAbs_lt_minNormalMantissa_of_fergusonAdjacent_reversed
        (negative := negative) (mHigh := mHigh) (mLow := mLow)
        (e := e) (ez := ez) hz hcond)
  have hcast :
      (((fmt.guardDigitRoundedCoeff
        (fmt.guardAlignedMantissaDiffInt mHigh mLow) : ℤ) : ℝ)) =
        fmt.guardAlignedMantissaDiff mHigh mLow := by
    rw [hround]
    exact fmt.guardAlignedMantissaDiffInt_cast mHigh mLow
  have hforward :
      fmt.normalizedValue negative mHigh (e + 1) -
          fmt.normalizedValue negative mLow e =
        fmt.guardDigitRoundedAdjacentExponentSubtractionValue
          negative mHigh mLow e := by
    rw [fmt.normalizedValue_sub_sameSign_adjacentExponent_eq_aligned]
    simp [guardDigitRoundedAdjacentExponentSubtractionValue,
      alignedAdjacentExponentSubtractionValue, hcast]
  calc
    fmt.normalizedValue negative mLow e -
        fmt.normalizedValue negative mHigh (e + 1) =
        -(fmt.normalizedValue negative mHigh (e + 1) -
          fmt.normalizedValue negative mLow e) := by
          ring
    _ = -fmt.guardDigitRoundedAdjacentExponentSubtractionValue
        negative mHigh mLow e := by
          rw [hforward]

/-- The branch-level guard-digit subtraction value in Ferguson's proof.
It keeps the same-exponent `t`-digit difference exactly, uses the `t+1`
guard word in the high-minus-low adjacent-exponent branch, and negates that
adjacent branch when the requested subtraction has the lower exponent first. -/
def guardDigitRoundedBranchSubtractionValue
    (fmt : FloatingPointFormat) (negative : Bool) (mx my : ℕ)
    (ex ey : ℤ) : ℝ :=
  if _hsame : ex = ey then
    fmt.guardDigitRoundedSameExponentSubtractionValue negative mx my ey
  else if _hx : ex = ey + 1 then
    fmt.guardDigitRoundedAdjacentExponentSubtractionValue negative mx my ey
  else if _hy : ey = ex + 1 then
    -fmt.guardDigitRoundedAdjacentExponentSubtractionValue negative my mx ex
  else
    fmt.normalizedValue negative mx ex -
      fmt.normalizedValue negative my ey

theorem guardDigitRoundedBranchSubtractionValue_eq_sub_of_ferguson
    {fmt : FloatingPointFormat} {negative : Bool} {mx my : ℕ}
    {ex ey ez : ℤ}
    (hmx : fmt.normalizedMantissa mx)
    (hmy : fmt.normalizedMantissa my)
    (hz : fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negative mx ex -
        fmt.normalizedValue negative my ey) ez)
    (hcond : ez < min ex ey)
    (hcases : ex = ey ∨ ex = ey + 1 ∨ ey = ex + 1) :
    fmt.guardDigitRoundedBranchSubtractionValue negative mx my ex ey =
      fmt.normalizedValue negative mx ex -
        fmt.normalizedValue negative my ey := by
  unfold guardDigitRoundedBranchSubtractionValue
  by_cases hsame : ex = ey
  · rw [dif_pos hsame]
    subst ex
    exact (fmt.normalizedValue_sub_sameSign_sameExponent_eq_guardDigitRounded
      (negative := negative) (m := mx) (n := my) (e := ey) hmx hmy).symm
  · rw [dif_neg hsame]
    by_cases hx : ex = ey + 1
    · rw [dif_pos hx]
      subst ex
      have hcondEy : ez < ey :=
        lt_of_lt_of_le hcond (min_le_right (ey + 1) ey)
      exact
        (fmt.normalizedValue_sub_sameSign_adjacentExponent_eq_guardDigitRounded_of_fergusonAdjacent
          (negative := negative) (mHigh := mx) (mLow := my)
          (e := ey) (ez := ez) hz hcondEy).symm
    · rw [dif_neg hx]
      by_cases hy : ey = ex + 1
      · rw [dif_pos hy]
        subst ey
        have hcondEx : ez < ex :=
          lt_of_lt_of_le hcond (min_le_left ex (ex + 1))
        exact
          (fmt.normalizedValue_sub_sameSign_reversedAdjacentExponent_eq_neg_guardDigitRounded_of_fergusonAdjacent
            (negative := negative) (mHigh := my) (mLow := mx)
            (e := ex) (ez := ez) hz hcondEx).symm
      · rw [dif_neg hy]

/-- A concrete branch implementation contract for Ferguson subtraction.  It
does not assume exactness directly; it requires the routine to return the
rounded branch value dictated by the same-sign exponent case split. -/
def guardDigitBranchSubtractionModel
    (fmt : FloatingPointFormat) (flSub : ℝ → ℝ → ℝ) : Prop :=
  ∀ {negative : Bool} {mx my : ℕ} {ex ey ez : ℤ},
    fmt.normalizedMantissa mx →
    fmt.exponentInRange ex →
    fmt.normalizedMantissa my →
    fmt.exponentInRange ey →
    fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negative mx ex -
        fmt.normalizedValue negative my ey) ez →
    ez < min ex ey →
    flSub (fmt.normalizedValue negative mx ex)
      (fmt.normalizedValue negative my ey) =
        fmt.guardDigitRoundedBranchSubtractionValue negative mx my ex ey

theorem guardDigitBranchSubtractionModel_guardDigitSubtractionModel
    {fmt : FloatingPointFormat} {flSub : ℝ → ℝ → ℝ}
    (hbranch : fmt.guardDigitBranchSubtractionModel flSub) :
    fmt.guardDigitSubtractionModel flSub := by
  intro x y hferg
  rcases hferg with ⟨ex, ey, ez, hx, hy, hz, hcond⟩
  rcases hx with ⟨negativeX, mx, hmx, hex, hx_eq⟩
  rcases hy with ⟨negativeY, my, hmy, hey, hy_eq⟩
  subst x
  subst y
  have hsign : negativeX = negativeY :=
    fmt.normalizedValue_sub_fergusonCondition_sign_eq
      (negativeX := negativeX) (negativeY := negativeY)
      (mx := mx) (my := my) (ex := ex) (ey := ey) (ez := ez)
      hmx hmy hz hcond
  subst negativeY
  have hx_repr :
      fmt.normalizedExponentRepresentation
        (fmt.normalizedValue negativeX mx ex) ex :=
    ⟨negativeX, mx, hmx, hex, rfl⟩
  have hy_repr :
      fmt.normalizedExponentRepresentation
        (fmt.normalizedValue negativeX my ey) ey :=
    ⟨negativeX, my, hmy, hey, rfl⟩
  have hgap :
      ex ≤ ey + 1 ∧ ey ≤ ex + 1 :=
    fmt.normalizedExponentRepresentation_sub_exponent_gap_le_one
      hx_repr hy_repr hz hcond
  have hcases : ex = ey ∨ ex = ey + 1 ∨ ey = ex + 1 := by
    omega
  have hfl :=
    hbranch hmx hex hmy hey hz hcond
  rw [hfl]
  exact fmt.guardDigitRoundedBranchSubtractionValue_eq_sub_of_ferguson
    (negative := negativeX) (mx := mx) (my := my)
    (ex := ex) (ey := ey) (ez := ez) hmx hmy hz hcond hcases

theorem guardDigitBranchSubtractionModel_exact_of_fergusonCondition
    {fmt : FloatingPointFormat} {flSub : ℝ → ℝ → ℝ} {x y : ℝ}
    (hbranch : fmt.guardDigitBranchSubtractionModel flSub)
    (hcond : fmt.fergusonExponentCondition x y) :
    flSub x y = x - y :=
  fmt.guardDigitBranchSubtractionModel_guardDigitSubtractionModel hbranch hcond

/-- Normalized branch data for the Ferguson guard-digit subtraction proof.
This is the representation-selection evidence needed by the branch-level
routine below. -/
structure GuardDigitBranchSubtractionData
    (fmt : FloatingPointFormat) (x y : ℝ) where
  negative : Bool
  mx : ℕ
  my : ℕ
  ex : ℤ
  ey : ℤ
  ez : ℤ
  hmx : fmt.normalizedMantissa mx
  hex : fmt.exponentInRange ex
  hx : x = fmt.normalizedValue negative mx ex
  hmy : fmt.normalizedMantissa my
  hey : fmt.exponentInRange ey
  hy : y = fmt.normalizedValue negative my ey
  hz : fmt.normalizedExponentRepresentation (x - y) ez
  hcond : ez < min ex ey

theorem GuardDigitBranchSubtractionData.exponent_cases
    {fmt : FloatingPointFormat} {x y : ℝ}
    (d : GuardDigitBranchSubtractionData fmt x y) :
    d.ex = d.ey ∨ d.ex = d.ey + 1 ∨ d.ey = d.ex + 1 := by
  have hx_repr : fmt.normalizedExponentRepresentation x d.ex :=
    ⟨d.negative, d.mx, d.hmx, d.hex, d.hx⟩
  have hy_repr : fmt.normalizedExponentRepresentation y d.ey :=
    ⟨d.negative, d.my, d.hmy, d.hey, d.hy⟩
  have hgap :
      d.ex ≤ d.ey + 1 ∧ d.ey ≤ d.ex + 1 :=
    fmt.normalizedExponentRepresentation_sub_exponent_gap_le_one
      hx_repr hy_repr d.hz d.hcond
  omega

theorem GuardDigitBranchSubtractionData.branchValue_eq_sub
    {fmt : FloatingPointFormat} {x y : ℝ}
    (d : GuardDigitBranchSubtractionData fmt x y) :
    fmt.guardDigitRoundedBranchSubtractionValue
        d.negative d.mx d.my d.ex d.ey =
      x - y := by
  have hbranch :=
    fmt.guardDigitRoundedBranchSubtractionValue_eq_sub_of_ferguson
      (negative := d.negative) (mx := d.mx) (my := d.my)
      (ex := d.ex) (ey := d.ey) (ez := d.ez)
      d.hmx d.hmy
      (by
        simpa [d.hx, d.hy] using d.hz)
      d.hcond d.exponent_cases
  simpa [d.hx, d.hy] using hbranch

/-- The branch-selected guard-digit value is a finite floating-point value.
The same-exponent branch uses the finite-difference selector derived from the
operand mantissas; the adjacent branches use Ferguson's normalized
representation of the exact difference. -/
theorem guardDigitRoundedBranchSubtractionValue_finiteSystem_of_ferguson
    {fmt : FloatingPointFormat} {negative : Bool} {mx my : ℕ}
    {ex ey ez : ℤ}
    (hmx : fmt.normalizedMantissa mx) (hex : fmt.exponentInRange ex)
    (hmy : fmt.normalizedMantissa my) (hey : fmt.exponentInRange ey)
    (hz : fmt.normalizedExponentRepresentation
      (fmt.normalizedValue negative mx ex -
        fmt.normalizedValue negative my ey) ez)
    (hcond : ez < min ex ey) :
    fmt.finiteSystem
      (fmt.guardDigitRoundedBranchSubtractionValue negative mx my ex ey) := by
  unfold guardDigitRoundedBranchSubtractionValue
  by_cases hsame : ex = ey
  · rw [dif_pos hsame]
    subst ex
    have hfinite :
        fmt.finiteSystem
          (fmt.normalizedValue negative mx ey -
            fmt.normalizedValue negative my ey) :=
      fmt.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_normalizedMantissas
        (negative := negative) (m := mx) (n := my) (e := ey) hmx hmy hey
    have hvalue :
        fmt.normalizedValue negative mx ey -
            fmt.normalizedValue negative my ey =
          fmt.guardDigitRoundedSameExponentSubtractionValue
            negative mx my ey :=
      fmt.normalizedValue_sub_sameSign_sameExponent_eq_guardDigitRounded
        (negative := negative) (m := mx) (n := my) (e := ey) hmx hmy
    rwa [← hvalue]
  · rw [dif_neg hsame]
    by_cases hx : ex = ey + 1
    · rw [dif_pos hx]
      subst ex
      have hcondEy : ez < ey :=
        lt_of_lt_of_le hcond (min_le_right (ey + 1) ey)
      have hvalue :
          fmt.normalizedValue negative mx (ey + 1) -
              fmt.normalizedValue negative my ey =
            fmt.guardDigitRoundedAdjacentExponentSubtractionValue
              negative mx my ey :=
        fmt.normalizedValue_sub_sameSign_adjacentExponent_eq_guardDigitRounded_of_fergusonAdjacent
          (negative := negative) (mHigh := mx) (mLow := my)
          (e := ey) (ez := ez) hz hcondEy
      have hfinite :
          fmt.finiteSystem
            (fmt.normalizedValue negative mx (ey + 1) -
              fmt.normalizedValue negative my ey) :=
        Or.inr (Or.inl
          (fmt.normalizedExponentRepresentation_normalizedSystem hz))
      rwa [← hvalue]
    · rw [dif_neg hx]
      by_cases hy : ey = ex + 1
      · rw [dif_pos hy]
        subst ey
        have hcondEx : ez < ex :=
          lt_of_lt_of_le hcond (min_le_left ex (ex + 1))
        have hvalue :
            fmt.normalizedValue negative mx ex -
                fmt.normalizedValue negative my (ex + 1) =
              -fmt.guardDigitRoundedAdjacentExponentSubtractionValue
                negative my mx ex :=
          fmt.normalizedValue_sub_sameSign_reversedAdjacentExponent_eq_neg_guardDigitRounded_of_fergusonAdjacent
            (negative := negative) (mHigh := my) (mLow := mx)
            (e := ex) (ez := ez) hz hcondEx
        have hfinite :
            fmt.finiteSystem
              (fmt.normalizedValue negative mx ex -
                fmt.normalizedValue negative my (ex + 1)) :=
          Or.inr (Or.inl
            (fmt.normalizedExponentRepresentation_normalizedSystem hz))
        rwa [← hvalue]
      · rw [dif_neg hy]
        exact Or.inr (Or.inl
          (fmt.normalizedExponentRepresentation_normalizedSystem hz))

theorem GuardDigitBranchSubtractionData.branchValue_finiteSystem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (d : GuardDigitBranchSubtractionData fmt x y) :
    fmt.finiteSystem
      (fmt.guardDigitRoundedBranchSubtractionValue
        d.negative d.mx d.my d.ex d.ey) := by
  exact
    fmt.guardDigitRoundedBranchSubtractionValue_finiteSystem_of_ferguson
      d.hmx d.hex d.hmy d.hey
      (by simpa [d.hx, d.hy] using d.hz) d.hcond

/-- Noncomputable branch selector for Ferguson subtraction.  If normalized
Ferguson branch data are available, it returns the branch-rounded value from
that data; otherwise it falls back to exact subtraction.  The fallback is only a
totality device and is not used in the Ferguson theorem. -/
noncomputable def guardDigitBranchSubtractionRoutine
    (fmt : FloatingPointFormat) (x y : ℝ) : ℝ := by
  classical
  exact
    if h : Nonempty (GuardDigitBranchSubtractionData fmt x y) then
      let d := Classical.choice h
      fmt.guardDigitRoundedBranchSubtractionValue
        d.negative d.mx d.my d.ex d.ey
    else
      x - y

theorem guardDigitBranchSubtractionRoutine_eq_sub_of_data
    {fmt : FloatingPointFormat} {x y : ℝ}
    (d : GuardDigitBranchSubtractionData fmt x y) :
    fmt.guardDigitBranchSubtractionRoutine x y = x - y := by
  classical
  unfold guardDigitBranchSubtractionRoutine
  rw [dif_pos ⟨d⟩]
  exact (Classical.choice ⟨d⟩).branchValue_eq_sub

theorem guardDigitBranchSubtractionRoutine_branchModel
    {fmt : FloatingPointFormat} :
    fmt.guardDigitBranchSubtractionModel
      (fmt.guardDigitBranchSubtractionRoutine) := by
  intro negative mx my ex ey ez hmx hex hmy hey hz hcond
  let x := fmt.normalizedValue negative mx ex
  let y := fmt.normalizedValue negative my ey
  let d : GuardDigitBranchSubtractionData fmt x y :=
    { negative := negative
      mx := mx
      my := my
      ex := ex
      ey := ey
      ez := ez
      hmx := hmx
      hex := hex
      hx := rfl
      hmy := hmy
      hey := hey
      hy := rfl
      hz := hz
      hcond := hcond }
  have hroutine :
      fmt.guardDigitBranchSubtractionRoutine x y = x - y :=
    fmt.guardDigitBranchSubtractionRoutine_eq_sub_of_data d
  have hbranch :
      fmt.guardDigitRoundedBranchSubtractionValue negative mx my ex ey =
        x - y := by
    exact d.branchValue_eq_sub
  simpa [x, y] using hroutine.trans hbranch.symm

theorem guardDigitBranchSubtractionRoutine_guardDigitSubtractionModel
    {fmt : FloatingPointFormat} :
    fmt.guardDigitSubtractionModel
      (fmt.guardDigitBranchSubtractionRoutine) :=
  fmt.guardDigitBranchSubtractionModel_guardDigitSubtractionModel
    fmt.guardDigitBranchSubtractionRoutine_branchModel

theorem guardDigitBranchSubtractionRoutine_exact_of_fergusonCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hcond : fmt.fergusonExponentCondition x y) :
    fmt.guardDigitBranchSubtractionRoutine x y = x - y :=
  fmt.guardDigitBranchSubtractionRoutine_guardDigitSubtractionModel hcond

theorem guardDigitBranchSubtractionRoutine_finiteSystem_of_data
    {fmt : FloatingPointFormat} {x y : ℝ}
    (d : GuardDigitBranchSubtractionData fmt x y) :
    fmt.finiteSystem (fmt.guardDigitBranchSubtractionRoutine x y) := by
  rw [fmt.guardDigitBranchSubtractionRoutine_eq_sub_of_data d]
  exact Or.inr (Or.inl
    (fmt.normalizedExponentRepresentation_normalizedSystem d.hz))

theorem guardDigitBranchSubtractionRoutine_finiteSystem_of_fergusonCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hcond : fmt.fergusonExponentCondition x y) :
    fmt.finiteSystem (fmt.guardDigitBranchSubtractionRoutine x y) := by
  rw [fmt.guardDigitBranchSubtractionRoutine_exact_of_fergusonCondition hcond]
  exact Or.inr (Or.inl (fmt.fergusonExponentCondition_sub_normalized hcond))

theorem subnormalValue_abs_lt_min_normal {fmt : FloatingPointFormat}
    {negative : Bool} {m : ℕ} (hm : fmt.subnormalMantissa m) :
    |fmt.subnormalValue negative m| < fmt.betaR ^ (fmt.emin - 1) := by
  rw [fmt.subnormalValue_abs negative m,
    ← fmt.minNormalMantissa_scale_eq fmt.emin]
  exact mul_lt_mul_of_pos_right
    (Nat.cast_lt.mpr hm.2)
    (fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ)))

/-- Subnormal finite values lie below the smallest positive normal magnitude. -/
theorem subnormalSystem_finiteUnderflowRange
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.subnormalSystem y) :
    fmt.finiteUnderflowRange y := by
  rcases hy with ⟨negative, m, hm, rfl⟩
  simpa [finiteUnderflowRange, minNormalMagnitude] using
    fmt.subnormalValue_abs_lt_min_normal (negative := negative) hm

/-- Subnormal values are no larger than the positive smallest normal
magnitude. -/
theorem subnormalSystem_le_minNormalMagnitude
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.subnormalSystem y) :
    y ≤ fmt.minNormalMagnitude := by
  have hunder := fmt.subnormalSystem_finiteUnderflowRange hy
  exact le_trans (le_abs_self y) (le_of_lt hunder)

/-- Subnormal values are no smaller than the negative smallest normal
endpoint. -/
theorem neg_minNormalMagnitude_le_subnormalSystem
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.subnormalSystem y) :
    -fmt.minNormalMagnitude ≤ y := by
  have hunder := fmt.subnormalSystem_finiteUnderflowRange hy
  have hneg : -fmt.minNormalMagnitude < -|y| := neg_lt_neg hunder
  exact le_of_lt (lt_of_lt_of_le hneg (neg_abs_le y))

/-- Subnormal finite values have magnitude at least the smallest subnormal. -/
theorem subnormalSystem_abs_ge_minSubnormalMagnitude
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.subnormalSystem y) :
    fmt.minSubnormalMagnitude ≤ |y| := by
  rcases hy with ⟨negative, m, hm, rfl⟩
  have hm_one : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hm.1)
  rw [fmt.subnormalValue_abs negative m]
  simpa [minSubnormalMagnitude] using
    mul_le_mul_of_nonneg_right hm_one
      (fmt.betaR_zpow_nonneg (fmt.emin - (fmt.t : ℤ)))

/-- Subnormal finite values are not in the source-facing overflow range. -/
theorem subnormalSystem_not_finiteOverflowRange
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.subnormalSystem y) :
    ¬ fmt.finiteOverflowRange y := by
  have hunder := fmt.subnormalSystem_finiteUnderflowRange hy
  exact not_lt_of_ge
    (le_trans (le_of_lt hunder)
      fmt.minNormalMagnitude_le_maxFiniteMagnitude)

/-- Every finite-system value is either zero, in the finite normal range, or in
the source-facing underflow range. -/
theorem finiteSystem_zero_or_finiteNormalRange_or_finiteUnderflowRange
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.finiteSystem y) :
    y = 0 ∨ fmt.finiteNormalRange y ∨ fmt.finiteUnderflowRange y := by
  rcases hy with hzero | hnorm | hsub
  · exact Or.inl hzero
  · exact Or.inr (Or.inl (fmt.normalizedSystem_finiteNormalRange hnorm))
  · exact Or.inr (Or.inr (fmt.subnormalSystem_finiteUnderflowRange hsub))

/-- Inside the finite system, the source-facing underflow range contains only
zero and subnormal values. -/
theorem finiteSystem_finiteUnderflowRange_iff_zero_or_subnormalSystem
    {fmt : FloatingPointFormat} {y : ℝ} :
    (fmt.finiteSystem y ∧ fmt.finiteUnderflowRange y) ↔
      y = 0 ∨ fmt.subnormalSystem y := by
  constructor
  · rintro ⟨hy, hunder⟩
    rcases hy with hzero | hnorm | hsub
    · exact Or.inl hzero
    · exact False.elim
        ((fmt.normalizedSystem_not_finiteUnderflowRange hnorm) hunder)
    · exact Or.inr hsub
  · intro h
    rcases h with hzero | hsub
    · subst y
      constructor
      · exact Or.inl rfl
      · simpa [finiteUnderflowRange] using fmt.minNormalMagnitude_pos
    · exact ⟨Or.inr (Or.inr hsub),
        fmt.subnormalSystem_finiteUnderflowRange hsub⟩

/-- A finite value is a nonzero underflow-range value exactly when it is
subnormal. -/
theorem finiteSystem_finiteUnderflowRange_ne_zero_iff_subnormalSystem
    {fmt : FloatingPointFormat} {y : ℝ} :
    (fmt.finiteSystem y ∧ fmt.finiteUnderflowRange y ∧ y ≠ 0) ↔
      fmt.subnormalSystem y := by
  constructor
  · rintro ⟨hy, hunder, hy_ne⟩
    rcases
      (fmt.finiteSystem_finiteUnderflowRange_iff_zero_or_subnormalSystem).mp
        ⟨hy, hunder⟩ with hzero | hsub
    · exact False.elim (hy_ne hzero)
    · exact hsub
  · intro hsub
    exact
      ⟨Or.inr (Or.inr hsub),
        fmt.subnormalSystem_finiteUnderflowRange hsub,
        fmt.subnormalSystem_ne_zero hsub⟩

/-- No finite-system value lies in the source-facing overflow range. -/
theorem finiteSystem_not_finiteOverflowRange
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.finiteSystem y) :
    ¬ fmt.finiteOverflowRange y := by
  rcases hy with hzero | hnorm | hsub
  · subst y
    rw [finiteOverflowRange, abs_zero]
    exact not_lt_of_ge fmt.maxFiniteMagnitude_nonneg
  · exact fmt.normalizedSystem_not_finiteOverflowRange hnorm
  · exact fmt.subnormalSystem_not_finiteOverflowRange hsub

/-- Every finite-system value has magnitude at most the largest finite
normalized magnitude. -/
theorem finiteSystem_abs_le_maxFiniteMagnitude
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.finiteSystem y) :
    |y| ≤ fmt.maxFiniteMagnitude := by
  have hnot := fmt.finiteSystem_not_finiteOverflowRange hy
  rw [finiteOverflowRange] at hnot
  exact le_of_not_gt hnot

/-- Every nonzero finite-system value has magnitude at least the smallest
positive subnormal magnitude. -/
theorem finiteSystem_ne_zero_abs_ge_minSubnormalMagnitude
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.finiteSystem y) (hzero : y ≠ 0) :
    fmt.minSubnormalMagnitude ≤ |y| := by
  rcases hy with hzero' | hnorm | hsub
  · exact False.elim (hzero hzero')
  · exact fmt.normalizedSystem_abs_ge_minSubnormalMagnitude hnorm
  · exact fmt.subnormalSystem_abs_ge_minSubnormalMagnitude hsub

theorem subnormalValue_false_one_eq (fmt : FloatingPointFormat) :
    fmt.subnormalValue false 1 =
      fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
  simp [subnormalValue, signValue]

theorem subnormalValue_one_abs_eq
    (fmt : FloatingPointFormat) (negative : Bool) :
    |fmt.subnormalValue negative 1| =
      fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
  rw [fmt.subnormalValue_abs negative 1]
  ring

/-- If mantissa `1` is an admissible subnormal mantissa, then the smallest
positive subnormal magnitude is a finite subnormal value. -/
theorem minSubnormalMagnitude_mem_subnormalSystem_of_subnormalMantissa_one
    {fmt : FloatingPointFormat} (h : fmt.subnormalMantissa 1) :
    fmt.subnormalSystem fmt.minSubnormalMagnitude := by
  refine ⟨false, 1, h, ?_⟩
  exact Eq.symm (fmt.subnormalValue_false_one_eq)

/-- If the first subnormal mantissa exists, the smallest normal is at least two
subnormal spacings from zero. -/
theorem two_mul_minSubnormalMagnitude_le_minNormalMagnitude_of_subnormalMantissa_one
    {fmt : FloatingPointFormat} (h : fmt.subnormalMantissa 1) :
    2 * fmt.minSubnormalMagnitude ≤ fmt.minNormalMagnitude := by
  have htwo_le_mantissa : (2 : ℝ) ≤ (fmt.minNormalMantissa : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt h.2)
  have hscale :
      2 * fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) ≤
        (fmt.minNormalMantissa : ℝ) *
          fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) :=
    mul_le_mul_of_nonneg_right htwo_le_mantissa
      (fmt.betaR_zpow_nonneg (fmt.emin - (fmt.t : ℤ)))
  rw [fmt.minNormalMantissa_scale_eq fmt.emin] at hscale
  simpa [minSubnormalMagnitude, minNormalMagnitude] using hscale

theorem subnormalValue_false_one_le_of_subnormalMantissa
    {fmt : FloatingPointFormat} {m : ℕ} (hm : fmt.subnormalMantissa m) :
    fmt.subnormalValue false 1 ≤ fmt.subnormalValue false m := by
  have hle : (1 : ℕ) ≤ m := Nat.succ_le_of_lt hm.1
  have hleR : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hle
  simpa [subnormalValue, signValue] using
    mul_le_mul_of_nonneg_right
      hleR
      (fmt.betaR_zpow_nonneg (fmt.emin - (fmt.t : ℤ)))

theorem subnormalValue_succ_sub
    (fmt : FloatingPointFormat) (m : ℕ) :
    fmt.subnormalValue false (m + 1) - fmt.subnormalValue false m =
      fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
  simp [subnormalValue, signValue]
  ring

theorem subnormalValue_succ_spacing
    (fmt : FloatingPointFormat) (negative : Bool) (m : ℕ) :
    |fmt.subnormalValue negative (m + 1) -
        fmt.subnormalValue negative m| =
      fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
  cases negative
  · rw [fmt.subnormalValue_succ_sub m]
    exact abs_of_pos (fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ)))
  · have hsub :
        fmt.subnormalValue true (m + 1) - fmt.subnormalValue true m =
          -fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
      simp [subnormalValue, signValue]
      ring
    rw [hsub, abs_neg]
    exact abs_of_pos (fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ)))

theorem subnormalValue_boundary_sub
    (fmt : FloatingPointFormat) :
    fmt.normalizedValue false fmt.minNormalMantissa fmt.emin -
        fmt.subnormalValue false (fmt.minNormalMantissa - 1) =
      fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
  have hcast :
      ((fmt.minNormalMantissa - 1 : ℕ) : ℝ) =
        (fmt.minNormalMantissa : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.succ_le_of_lt fmt.minNormalMantissa_pos),
      Nat.cast_one]
  simp [normalizedValue, subnormalValue, signValue, hcast]
  ring

theorem subnormalValue_boundary_spacing
    (fmt : FloatingPointFormat) :
    |fmt.normalizedValue false fmt.minNormalMantissa fmt.emin -
        fmt.subnormalValue false (fmt.minNormalMantissa - 1)| =
      fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
  rw [fmt.subnormalValue_boundary_sub]
  exact abs_of_pos (fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ)))

theorem normalizedValue_false_lower_power {fmt : FloatingPointFormat}
    {m : ℕ} {e : ℤ} (hm : fmt.normalizedMantissa m) :
    fmt.betaR ^ (e - 1) ≤ fmt.normalizedValue false m e := by
  have hpos := fmt.normalizedValue_false_pos (m := m) (e := e) hm
  simpa [abs_of_pos hpos] using
    (fmt.normalizedValue_abs_lower_power (negative := false) (m := m) (e := e) hm)

theorem normalizedValue_false_lt_beta_pow {fmt : FloatingPointFormat}
    {m : ℕ} {e : ℤ} (hm : fmt.normalizedMantissa m) :
    fmt.normalizedValue false m e < fmt.betaR ^ e := by
  have hpos := fmt.normalizedValue_false_pos (m := m) (e := e) hm
  simpa [abs_of_pos hpos] using
    (fmt.normalizedValue_abs_lt_beta_pow (negative := false) (m := m) (e := e) hm)

theorem normalizedValue_false_lt_of_exp_lt {fmt : FloatingPointFormat}
    {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (he : e < e') :
    fmt.normalizedValue false m e < fmt.normalizedValue false n e' := by
  have hone : (1 : ℝ) ≤ fmt.betaR := by
    unfold betaR
    exact_mod_cast (le_trans (by decide : 1 ≤ 2) fmt.beta_ge_two)
  have hexp_le : e ≤ e' - 1 := by
    omega
  calc
    fmt.normalizedValue false m e < fmt.betaR ^ e :=
      fmt.normalizedValue_false_lt_beta_pow hm
    _ ≤ fmt.betaR ^ (e' - 1) :=
      zpow_le_zpow_right₀ hone hexp_le
    _ ≤ fmt.normalizedValue false n e' :=
      fmt.normalizedValue_false_lower_power hn

theorem normalizedValue_true_lt_of_exp_lt {fmt : FloatingPointFormat}
    {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (he : e < e') :
    fmt.normalizedValue true n e' < fmt.normalizedValue true m e := by
  have hpos :=
    fmt.normalizedValue_false_lt_of_exp_lt
      (m := m) (n := n) (e := e) (e' := e') hm hn he
  rw [fmt.normalizedValue_true_eq_neg_false n e',
    fmt.normalizedValue_true_eq_neg_false m e]
  exact neg_lt_neg hpos

theorem normalizedValue_false_eq_iff
    {fmt : FloatingPointFormat} {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n) :
    fmt.normalizedValue false m e = fmt.normalizedValue false n e' ↔
      e = e' ∧ m = n := by
  constructor
  · intro h
    have heq : e = e' := by
      rcases lt_trichotomy e e' with hlt | heq | hgt
      · exact False.elim
          ((ne_of_lt (fmt.normalizedValue_false_lt_of_exp_lt hm hn hlt)) h)
      · exact heq
      · exact False.elim
          ((ne_of_gt (fmt.normalizedValue_false_lt_of_exp_lt hn hm hgt)) h)
    subst e'
    have hmn : m = n := by
      rcases lt_trichotomy m n with hlt | heq | hgt
      · exact False.elim
          ((ne_of_lt
            ((fmt.normalizedValue_sameExponent_lt_iff_false m n e).2 hlt)) h)
      · exact heq
      · exact False.elim
          ((ne_of_gt
            ((fmt.normalizedValue_sameExponent_lt_iff_false n m e).2 hgt)) h)
    exact ⟨rfl, hmn⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem normalizedValue_true_eq_iff
    {fmt : FloatingPointFormat} {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n) :
    fmt.normalizedValue true m e = fmt.normalizedValue true n e' ↔
      e = e' ∧ m = n := by
  constructor
  · intro h
    have hfalse :
        fmt.normalizedValue false m e =
          fmt.normalizedValue false n e' := by
      rw [fmt.normalizedValue_true_eq_neg_false m e,
        fmt.normalizedValue_true_eq_neg_false n e'] at h
      exact neg_inj.mp h
    exact (fmt.normalizedValue_false_eq_iff hm hn).1 hfalse
  · rintro ⟨rfl, rfl⟩
    rfl

theorem normalizedValue_false_ne_true
    {fmt : FloatingPointFormat} {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n) :
    fmt.normalizedValue false m e ≠ fmt.normalizedValue true n e' := by
  intro h
  have hpos : 0 < fmt.normalizedValue true n e' := by
    simpa [h] using fmt.normalizedValue_false_pos (m := m) (e := e) hm
  exact (not_lt_of_ge (le_of_lt (fmt.normalizedValue_true_neg hn))) hpos

theorem normalizedValue_eq_sign_exp_mantissa
    {fmt : FloatingPointFormat} {negative negative' : Bool}
    {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (h :
      fmt.normalizedValue negative m e =
        fmt.normalizedValue negative' n e') :
    negative = negative' ∧ e = e' ∧ m = n := by
  cases negative <;> cases negative'
  · rcases (fmt.normalizedValue_false_eq_iff hm hn).1 h with ⟨he, hmne⟩
    exact ⟨rfl, he, hmne⟩
  · exact False.elim ((fmt.normalizedValue_false_ne_true hm hn) h)
  · exact False.elim ((fmt.normalizedValue_false_ne_true hn hm) h.symm)
  · rcases (fmt.normalizedValue_true_eq_iff hm hn).1 h with ⟨he, hmne⟩
    exact ⟨rfl, he, hmne⟩

theorem normalizedValue_eq_iff_sign_exp_mantissa
    {fmt : FloatingPointFormat} {negative negative' : Bool}
    {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n) :
    fmt.normalizedValue negative m e =
        fmt.normalizedValue negative' n e' ↔
      negative = negative' ∧ e = e' ∧ m = n := by
  constructor
  · exact fmt.normalizedValue_eq_sign_exp_mantissa hm hn
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem normalizedValue_false_le_of_mantissa_le
    (fmt : FloatingPointFormat) {m n : ℕ} (e : ℤ) (hmn : m ≤ n) :
    fmt.normalizedValue false m e ≤ fmt.normalizedValue false n e := by
  rcases lt_or_eq_of_le hmn with hlt | heq
  · exact le_of_lt ((fmt.normalizedValue_sameExponent_lt_iff_false m n e).2 hlt)
  · subst n
    rfl

theorem normalizedValue_false_le_maxNormalMantissa
    {fmt : FloatingPointFormat} {m : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) :
    fmt.normalizedValue false m e ≤
      fmt.normalizedValue false fmt.maxNormalMantissa e := by
  have hle : m ≤ fmt.maxNormalMantissa := by
    unfold maxNormalMantissa
    exact Nat.le_sub_one_of_lt hm.2
  exact fmt.normalizedValue_false_le_of_mantissa_le e hle

theorem normalizedValue_false_minNormalMantissa_le
    {fmt : FloatingPointFormat} {m : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) :
    fmt.normalizedValue false fmt.minNormalMantissa e ≤
      fmt.normalizedValue false m e :=
  fmt.normalizedValue_false_le_of_mantissa_le e hm.1

theorem normalizedValue_false_minNormalMantissa_succ_eq_beta_pow
    (fmt : FloatingPointFormat) (e : ℤ) :
    fmt.normalizedValue false fmt.minNormalMantissa (e + 1) =
      fmt.betaR ^ e := by
  calc
    fmt.normalizedValue false fmt.minNormalMantissa (e + 1) =
        (fmt.minNormalMantissa : ℝ) *
          fmt.betaR ^ ((e + 1) - (fmt.t : ℤ)) := by
      simp [normalizedValue, signValue]
    _ = fmt.betaR ^ ((e + 1) - 1) :=
      fmt.minNormalMantissa_scale_eq (e + 1)
    _ = fmt.betaR ^ e := by
      congr 1
      ring

theorem normalizedValue_false_le_maxNormalMantissa_of_exp_le
    {fmt : FloatingPointFormat} {m : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (he : e' ≤ e) :
    fmt.normalizedValue false m e' ≤
      fmt.normalizedValue false fmt.maxNormalMantissa e := by
  by_cases hlt : e' < e
  · exact le_of_lt
      (fmt.normalizedValue_false_lt_of_exp_lt
        hm fmt.maxNormalMantissa_normalized hlt)
  · have heq : e' = e := by
      omega
    subst e'
    exact fmt.normalizedValue_false_le_maxNormalMantissa hm

theorem normalizedValue_false_minNormalMantissa_le_of_exp_le
    {fmt : FloatingPointFormat} {m : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (he : e + 1 ≤ e') :
    fmt.normalizedValue false fmt.minNormalMantissa (e + 1) ≤
      fmt.normalizedValue false m e' := by
  by_cases hlt : e + 1 < e'
  · exact le_of_lt
      (fmt.normalizedValue_false_lt_of_exp_lt
        fmt.minNormalMantissa_normalized hm hlt)
  · have heq : e' = e + 1 := by
      omega
    subst e'
    exact fmt.normalizedValue_false_minNormalMantissa_le hm

theorem normalizedValue_sameSign_no_between_succ
    (fmt : FloatingPointFormat) (negative : Bool) {m k : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hmnext : fmt.normalizedMantissa (m + 1))
    (hk : fmt.normalizedMantissa k) :
    ¬ ((fmt.normalizedValue negative m e <
          fmt.normalizedValue negative k e' ∧
        fmt.normalizedValue negative k e' <
          fmt.normalizedValue negative (m + 1) e) ∨
      (fmt.normalizedValue negative (m + 1) e <
          fmt.normalizedValue negative k e' ∧
        fmt.normalizedValue negative k e' <
          fmt.normalizedValue negative m e)) := by
  by_cases heq : e' = e
  · subst e'
    exact fmt.normalizedValue_sameExponent_no_between_succ negative m k e
  · have horder : e' < e ∨ e < e' := lt_or_gt_of_ne heq
    cases negative
    · intro hbetween
      rcases horder with hlt | hlt
      · have hk_lt_m :
            fmt.normalizedValue false k e' <
              fmt.normalizedValue false m e :=
          fmt.normalizedValue_false_lt_of_exp_lt hk hm hlt
        have hk_lt_mnext :
            fmt.normalizedValue false k e' <
              fmt.normalizedValue false (m + 1) e :=
          fmt.normalizedValue_false_lt_of_exp_lt hk hmnext hlt
        rcases hbetween with hbetween | hbetween
        · exact (not_lt_of_ge (le_of_lt hk_lt_m)) hbetween.1
        · exact (not_lt_of_ge (le_of_lt hk_lt_mnext)) hbetween.1
      · have hm_lt_k :
            fmt.normalizedValue false m e <
              fmt.normalizedValue false k e' :=
          fmt.normalizedValue_false_lt_of_exp_lt hm hk hlt
        have hmnext_lt_k :
            fmt.normalizedValue false (m + 1) e <
              fmt.normalizedValue false k e' :=
          fmt.normalizedValue_false_lt_of_exp_lt hmnext hk hlt
        rcases hbetween with hbetween | hbetween
        · exact (not_lt_of_ge (le_of_lt hmnext_lt_k)) hbetween.2
        · exact (not_lt_of_ge (le_of_lt hm_lt_k)) hbetween.2
    · intro hbetween
      rcases horder with hlt | hlt
      · have hm_lt_k :
            fmt.normalizedValue true m e <
              fmt.normalizedValue true k e' :=
          fmt.normalizedValue_true_lt_of_exp_lt hk hm hlt
        have hmnext_lt_k :
            fmt.normalizedValue true (m + 1) e <
              fmt.normalizedValue true k e' :=
          fmt.normalizedValue_true_lt_of_exp_lt hk hmnext hlt
        rcases hbetween with hbetween | hbetween
        · exact (not_lt_of_ge (le_of_lt hmnext_lt_k)) hbetween.2
        · exact (not_lt_of_ge (le_of_lt hm_lt_k)) hbetween.2
      · have hk_lt_m :
            fmt.normalizedValue true k e' <
              fmt.normalizedValue true m e :=
          fmt.normalizedValue_true_lt_of_exp_lt hm hk hlt
        have hk_lt_mnext :
            fmt.normalizedValue true k e' <
              fmt.normalizedValue true (m + 1) e :=
          fmt.normalizedValue_true_lt_of_exp_lt hmnext hk hlt
        rcases hbetween with hbetween | hbetween
        · exact (not_lt_of_ge (le_of_lt hk_lt_m)) hbetween.1
        · exact (not_lt_of_ge (le_of_lt hk_lt_mnext)) hbetween.1

theorem normalizedValue_oppositeSign_no_between_succ
    (fmt : FloatingPointFormat) (negative : Bool) {m k : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hmnext : fmt.normalizedMantissa (m + 1))
    (hk : fmt.normalizedMantissa k) :
    ¬ ((fmt.normalizedValue negative m e <
          fmt.normalizedValue (!negative) k e' ∧
        fmt.normalizedValue (!negative) k e' <
          fmt.normalizedValue negative (m + 1) e) ∨
      (fmt.normalizedValue negative (m + 1) e <
          fmt.normalizedValue (!negative) k e' ∧
        fmt.normalizedValue (!negative) k e' <
          fmt.normalizedValue negative m e)) := by
  cases negative
  · have hm_pos := fmt.normalizedValue_false_pos (m := m) (e := e) hm
    have hmnext_pos :=
      fmt.normalizedValue_false_pos (m := m + 1) (e := e) hmnext
    have hk_neg := fmt.normalizedValue_true_neg (m := k) (e := e') hk
    have hk_lt_m :
        fmt.normalizedValue true k e' < fmt.normalizedValue false m e :=
      lt_trans hk_neg hm_pos
    have hk_lt_mnext :
        fmt.normalizedValue true k e' <
          fmt.normalizedValue false (m + 1) e :=
      lt_trans hk_neg hmnext_pos
    intro hbetween
    rcases hbetween with hbetween | hbetween
    · exact (not_lt_of_ge (le_of_lt hk_lt_m)) hbetween.1
    · exact (not_lt_of_ge (le_of_lt hk_lt_mnext)) hbetween.1
  · have hm_neg := fmt.normalizedValue_true_neg (m := m) (e := e) hm
    have hmnext_neg :=
      fmt.normalizedValue_true_neg (m := m + 1) (e := e) hmnext
    have hk_pos := fmt.normalizedValue_false_pos (m := k) (e := e') hk
    have hm_lt_k :
        fmt.normalizedValue true m e < fmt.normalizedValue false k e' :=
      lt_trans hm_neg hk_pos
    have hmnext_lt_k :
        fmt.normalizedValue true (m + 1) e <
          fmt.normalizedValue false k e' :=
      lt_trans hmnext_neg hk_pos
    intro hbetween
    rcases hbetween with hbetween | hbetween
    · exact (not_lt_of_ge (le_of_lt hmnext_lt_k)) hbetween.2
    · exact (not_lt_of_ge (le_of_lt hm_lt_k)) hbetween.2

theorem normalizedValue_no_between_succ
    (fmt : FloatingPointFormat) (negative znegative : Bool)
    {m k : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hmnext : fmt.normalizedMantissa (m + 1))
    (hk : fmt.normalizedMantissa k) :
    ¬ ((fmt.normalizedValue negative m e <
          fmt.normalizedValue znegative k e' ∧
        fmt.normalizedValue znegative k e' <
          fmt.normalizedValue negative (m + 1) e) ∨
      (fmt.normalizedValue negative (m + 1) e <
          fmt.normalizedValue znegative k e' ∧
        fmt.normalizedValue znegative k e' <
          fmt.normalizedValue negative m e)) := by
  cases negative <;> cases znegative
  · exact fmt.normalizedValue_sameSign_no_between_succ false hm hmnext hk
  · exact fmt.normalizedValue_oppositeSign_no_between_succ false hm hmnext hk
  · exact fmt.normalizedValue_oppositeSign_no_between_succ true hm hmnext hk
  · exact fmt.normalizedValue_sameSign_no_between_succ true hm hmnext hk

theorem normalizedValue_boundary_no_between
    (fmt : FloatingPointFormat) (negative znegative : Bool)
    {k : ℕ} {e e' : ℤ}
    (hk : fmt.normalizedMantissa k) :
    ¬ ((fmt.normalizedValue negative fmt.maxNormalMantissa e <
          fmt.normalizedValue znegative k e' ∧
        fmt.normalizedValue znegative k e' <
          fmt.normalizedValue negative fmt.minNormalMantissa (e + 1)) ∨
      (fmt.normalizedValue negative fmt.minNormalMantissa (e + 1) <
          fmt.normalizedValue znegative k e' ∧
        fmt.normalizedValue znegative k e' <
          fmt.normalizedValue negative fmt.maxNormalMantissa e)) := by
  have hmax_lt_min_false :
      fmt.normalizedValue false fmt.maxNormalMantissa e <
        fmt.normalizedValue false fmt.minNormalMantissa (e + 1) :=
    fmt.normalizedValue_false_lt_of_exp_lt
      fmt.maxNormalMantissa_normalized fmt.minNormalMantissa_normalized
      (by omega)
  cases negative <;> cases znegative
  · by_cases hle : e' ≤ e
    · have hz_le_max :
          fmt.normalizedValue false k e' ≤
            fmt.normalizedValue false fmt.maxNormalMantissa e :=
        fmt.normalizedValue_false_le_maxNormalMantissa_of_exp_le hk hle
      have hz_lt_min :
          fmt.normalizedValue false k e' <
            fmt.normalizedValue false fmt.minNormalMantissa (e + 1) :=
        lt_of_le_of_lt hz_le_max hmax_lt_min_false
      intro hbetween
      rcases hbetween with hbetween | hbetween
      · exact (not_lt_of_ge hz_le_max) hbetween.1
      · exact (not_lt_of_ge (le_of_lt hz_lt_min)) hbetween.1
    · have he_ge : e + 1 ≤ e' := by
        omega
      have hmin_le_z :
          fmt.normalizedValue false fmt.minNormalMantissa (e + 1) ≤
            fmt.normalizedValue false k e' :=
        fmt.normalizedValue_false_minNormalMantissa_le_of_exp_le hk he_ge
      have hmax_lt_z :
          fmt.normalizedValue false fmt.maxNormalMantissa e <
            fmt.normalizedValue false k e' :=
        lt_of_lt_of_le hmax_lt_min_false hmin_le_z
      intro hbetween
      rcases hbetween with hbetween | hbetween
      · exact (not_lt_of_ge hmin_le_z) hbetween.2
      · exact (not_lt_of_ge (le_of_lt hmax_lt_z)) hbetween.2
  · have hz_neg := fmt.normalizedValue_true_neg (m := k) (e := e') hk
    have hmax_pos :=
      fmt.normalizedValue_false_pos
        (m := fmt.maxNormalMantissa) (e := e) fmt.maxNormalMantissa_normalized
    have hmin_pos :=
      fmt.normalizedValue_false_pos
        (m := fmt.minNormalMantissa) (e := e + 1) fmt.minNormalMantissa_normalized
    have hz_lt_max :
        fmt.normalizedValue true k e' <
          fmt.normalizedValue false fmt.maxNormalMantissa e :=
      lt_trans hz_neg hmax_pos
    have hz_lt_min :
        fmt.normalizedValue true k e' <
          fmt.normalizedValue false fmt.minNormalMantissa (e + 1) :=
      lt_trans hz_neg hmin_pos
    intro hbetween
    rcases hbetween with hbetween | hbetween
    · exact (not_lt_of_ge (le_of_lt hz_lt_max)) hbetween.1
    · exact (not_lt_of_ge (le_of_lt hz_lt_min)) hbetween.1
  · have hmax_neg :=
      fmt.normalizedValue_true_neg
        (m := fmt.maxNormalMantissa) (e := e) fmt.maxNormalMantissa_normalized
    have hmin_neg :=
      fmt.normalizedValue_true_neg
        (m := fmt.minNormalMantissa) (e := e + 1) fmt.minNormalMantissa_normalized
    have hz_pos := fmt.normalizedValue_false_pos (m := k) (e := e') hk
    have hmax_lt_z :
        fmt.normalizedValue true fmt.maxNormalMantissa e <
          fmt.normalizedValue false k e' :=
      lt_trans hmax_neg hz_pos
    have hmin_lt_z :
        fmt.normalizedValue true fmt.minNormalMantissa (e + 1) <
          fmt.normalizedValue false k e' :=
      lt_trans hmin_neg hz_pos
    intro hbetween
    rcases hbetween with hbetween | hbetween
    · exact (not_lt_of_ge (le_of_lt hmin_lt_z)) hbetween.2
    · exact (not_lt_of_ge (le_of_lt hmax_lt_z)) hbetween.2
  · have hmin_true_lt_max_true :
        fmt.normalizedValue true fmt.minNormalMantissa (e + 1) <
          fmt.normalizedValue true fmt.maxNormalMantissa e := by
      rw [fmt.normalizedValue_true_eq_neg_false fmt.minNormalMantissa (e + 1),
        fmt.normalizedValue_true_eq_neg_false fmt.maxNormalMantissa e]
      exact neg_lt_neg hmax_lt_min_false
    by_cases hle : e' ≤ e
    · have hz_le_max_false :
          fmt.normalizedValue false k e' ≤
            fmt.normalizedValue false fmt.maxNormalMantissa e :=
        fmt.normalizedValue_false_le_maxNormalMantissa_of_exp_le hk hle
      have hmax_true_le_z :
          fmt.normalizedValue true fmt.maxNormalMantissa e ≤
            fmt.normalizedValue true k e' := by
        rw [fmt.normalizedValue_true_eq_neg_false fmt.maxNormalMantissa e,
          fmt.normalizedValue_true_eq_neg_false k e']
        exact neg_le_neg hz_le_max_false
      have hmin_true_lt_z :
          fmt.normalizedValue true fmt.minNormalMantissa (e + 1) <
            fmt.normalizedValue true k e' :=
        lt_of_lt_of_le hmin_true_lt_max_true hmax_true_le_z
      intro hbetween
      rcases hbetween with hbetween | hbetween
      · exact (not_lt_of_ge (le_of_lt hmin_true_lt_z)) hbetween.2
      · exact (not_lt_of_ge hmax_true_le_z) hbetween.2
    · have he_ge : e + 1 ≤ e' := by
        omega
      have hmin_le_z_false :
          fmt.normalizedValue false fmt.minNormalMantissa (e + 1) ≤
            fmt.normalizedValue false k e' :=
        fmt.normalizedValue_false_minNormalMantissa_le_of_exp_le hk he_ge
      have hz_true_le_min :
          fmt.normalizedValue true k e' ≤
            fmt.normalizedValue true fmt.minNormalMantissa (e + 1) := by
        rw [fmt.normalizedValue_true_eq_neg_false k e',
          fmt.normalizedValue_true_eq_neg_false fmt.minNormalMantissa (e + 1)]
        exact neg_le_neg hmin_le_z_false
      have hz_true_lt_max :
          fmt.normalizedValue true k e' <
            fmt.normalizedValue true fmt.maxNormalMantissa e :=
        lt_of_le_of_lt hz_true_le_min hmin_true_lt_max_true
      intro hbetween
      rcases hbetween with hbetween | hbetween
      · exact (not_lt_of_ge (le_of_lt hz_true_lt_max)) hbetween.1
      · exact (not_lt_of_ge hz_true_le_min) hbetween.1

theorem machineEpsilon_mul_lower_power_eq (fmt : FloatingPointFormat) (e : ℤ) :
    fmt.machineEpsilon * fmt.betaR ^ (e - 1) =
      fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  unfold machineEpsilon
  calc
    fmt.betaR ^ (1 - (fmt.t : ℤ)) * fmt.betaR ^ (e - 1) =
        fmt.betaR ^ ((1 - (fmt.t : ℤ)) + (e - 1)) := by
      rw [← zpow_add₀ hbase]
    _ = fmt.betaR ^ (e - (fmt.t : ℤ)) := by
      congr 1
      ring

theorem beta_inv_machineEpsilon_mul_upper_power_eq
    (fmt : FloatingPointFormat) (e : ℤ) :
    (fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon) * fmt.betaR ^ e =
      fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  unfold machineEpsilon
  calc
    (fmt.betaR ^ (-1 : ℤ) * fmt.betaR ^ (1 - (fmt.t : ℤ))) *
        fmt.betaR ^ e =
        fmt.betaR ^ ((-1 : ℤ) + (1 - (fmt.t : ℤ))) * fmt.betaR ^ e := by
      rw [← zpow_add₀ hbase]
    _ = fmt.betaR ^ (((-1 : ℤ) + (1 - (fmt.t : ℤ))) + e) := by
      rw [← zpow_add₀ hbase]
    _ = fmt.betaR ^ (e - (fmt.t : ℤ)) := by
      congr 1
      ring

theorem ulpAtExponent_eq_machineEpsilon_mul_lower_power
    (fmt : FloatingPointFormat) (e : ℤ) :
    fmt.ulpAtExponent e = fmt.machineEpsilon * fmt.betaR ^ (e - 1) := by
  simpa [ulpAtExponent] using
    (fmt.machineEpsilon_mul_lower_power_eq e).symm

theorem ulpAtExponent_eq_beta_inv_machineEpsilon_mul_upper_power
    (fmt : FloatingPointFormat) (e : ℤ) :
    fmt.ulpAtExponent e =
      (fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon) * fmt.betaR ^ e := by
  simpa [ulpAtExponent] using
    (fmt.beta_inv_machineEpsilon_mul_upper_power_eq e).symm

theorem normalizedValue_spacing_bounds
    {fmt : FloatingPointFormat} {negative : Bool} {m : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) :
    fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon *
        |fmt.normalizedValue negative m e| ≤
      fmt.betaR ^ (e - (fmt.t : ℤ)) ∧
    fmt.betaR ^ (e - (fmt.t : ℤ)) ≤
      fmt.machineEpsilon * |fmt.normalizedValue negative m e| := by
  have hmag :=
    fmt.normalizedValue_abs_between_beta_powers
      (negative := negative) (m := m) (e := e) hm
  constructor
  · have hfactor_pos :
        0 < fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon := by
      unfold machineEpsilon
      exact mul_pos (fmt.betaR_zpow_pos (-1 : ℤ))
        (fmt.betaR_zpow_pos (1 - (fmt.t : ℤ)))
    have hlt :
        (fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon) *
            |fmt.normalizedValue negative m e| <
          (fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon) *
            fmt.betaR ^ e :=
      mul_lt_mul_of_pos_left hmag.2 hfactor_pos
    have hscale :
        fmt.betaR⁻¹ * fmt.machineEpsilon * fmt.betaR ^ e =
          fmt.betaR ^ (e - (fmt.t : ℤ)) := by
      simpa using fmt.beta_inv_machineEpsilon_mul_upper_power_eq e
    exact le_of_lt (by simpa [hscale] using hlt)
  · have heps_nonneg : 0 ≤ fmt.machineEpsilon := by
      unfold machineEpsilon
      exact fmt.betaR_zpow_nonneg (1 - (fmt.t : ℤ))
    have hle :
        fmt.machineEpsilon * fmt.betaR ^ (e - 1) ≤
          fmt.machineEpsilon * |fmt.normalizedValue negative m e| :=
      mul_le_mul_of_nonneg_left hmag.1 heps_nonneg
    have hscale := fmt.machineEpsilon_mul_lower_power_eq e
    simpa [hscale] using hle

theorem normalizedValue_wobblingPrecision_bounds
    {fmt : FloatingPointFormat} {negative : Bool} {m : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) :
    fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon *
        |fmt.normalizedValue negative m e| ≤ fmt.ulpAtExponent e ∧
    fmt.ulpAtExponent e ≤
      fmt.machineEpsilon * |fmt.normalizedValue negative m e| := by
  simpa [ulpAtExponent] using
    (fmt.normalizedValue_spacing_bounds (negative := negative) (m := m)
      (e := e) hm)

theorem normalizedValue_succ_sub_sameExponent (fmt : FloatingPointFormat)
    (negative : Bool) (m : ℕ) (e : ℤ) :
    fmt.normalizedValue negative (m + 1) e -
      fmt.normalizedValue negative m e =
        fmt.signValue negative * fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  unfold normalizedValue
  norm_num
  ring

theorem normalizedValue_succ_spacing (fmt : FloatingPointFormat)
    (negative : Bool) (m : ℕ) (e : ℤ) :
    |fmt.normalizedValue negative (m + 1) e -
      fmt.normalizedValue negative m e| =
        fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  rw [fmt.normalizedValue_succ_sub_sameExponent negative m e, abs_mul,
    fmt.signValue_abs negative,
    abs_of_pos (fmt.betaR_zpow_pos (e - (fmt.t : ℤ)))]
  ring

theorem normalizedValue_succ_spacing_eq_ulpAtExponent
    (fmt : FloatingPointFormat) (negative : Bool) (m : ℕ) (e : ℤ) :
    |fmt.normalizedValue negative (m + 1) e -
      fmt.normalizedValue negative m e| = fmt.ulpAtExponent e := by
  simpa [ulpAtExponent] using
    fmt.normalizedValue_succ_spacing negative m e

theorem normalizedValue_boundary_sub (fmt : FloatingPointFormat)
    (negative : Bool) (e : ℤ) :
    fmt.normalizedValue negative fmt.minNormalMantissa (e + 1) -
      fmt.normalizedValue negative fmt.maxNormalMantissa e =
        fmt.signValue negative * fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  have hmin :
      (fmt.minNormalMantissa : ℝ) *
          fmt.betaR ^ ((e + 1) - (fmt.t : ℤ)) = fmt.betaR ^ e := by
    calc
      (fmt.minNormalMantissa : ℝ) *
          fmt.betaR ^ ((e + 1) - (fmt.t : ℤ)) =
            fmt.betaR ^ ((e + 1) - 1) := by
        exact fmt.minNormalMantissa_scale_eq (e + 1)
      _ = fmt.betaR ^ e := by
        congr 1
        ring
  have hmax := fmt.maxNormalMantissa_scale_eq e
  unfold normalizedValue
  calc
    fmt.signValue negative * ↑fmt.minNormalMantissa *
          fmt.betaR ^ ((e + 1) - ↑fmt.t) -
        fmt.signValue negative * ↑fmt.maxNormalMantissa *
          fmt.betaR ^ (e - ↑fmt.t) =
        fmt.signValue negative *
          (↑fmt.minNormalMantissa * fmt.betaR ^ ((e + 1) - ↑fmt.t) -
            ↑fmt.maxNormalMantissa * fmt.betaR ^ (e - ↑fmt.t)) := by
      ring
    _ = fmt.signValue negative *
        (fmt.betaR ^ e - (fmt.betaR ^ e - fmt.betaR ^ (e - ↑fmt.t))) := by
      rw [hmin, hmax]
    _ = fmt.signValue negative * fmt.betaR ^ (e - ↑fmt.t) := by
      ring

theorem normalizedValue_boundary_spacing (fmt : FloatingPointFormat)
    (negative : Bool) (e : ℤ) :
    |fmt.normalizedValue negative fmt.minNormalMantissa (e + 1) -
      fmt.normalizedValue negative fmt.maxNormalMantissa e| =
        fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  rw [fmt.normalizedValue_boundary_sub negative e, abs_mul,
    fmt.signValue_abs negative,
    abs_of_pos (fmt.betaR_zpow_pos (e - (fmt.t : ℤ)))]
  ring

theorem normalizedValue_boundary_spacing_eq_ulpAtExponent
    (fmt : FloatingPointFormat) (negative : Bool) (e : ℤ) :
    |fmt.normalizedValue negative fmt.minNormalMantissa (e + 1) -
      fmt.normalizedValue negative fmt.maxNormalMantissa e| =
        fmt.ulpAtExponent e := by
  simpa [ulpAtExponent] using
    fmt.normalizedValue_boundary_spacing negative e

theorem normalizedValue_boundary_min_spacing_bounds
    (fmt : FloatingPointFormat) (negative : Bool) (e : ℤ) :
    fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon *
        |fmt.normalizedValue negative fmt.minNormalMantissa (e + 1)| ≤
      fmt.betaR ^ (e - (fmt.t : ℤ)) ∧
    fmt.betaR ^ (e - (fmt.t : ℤ)) ≤
      fmt.machineEpsilon *
        |fmt.normalizedValue negative fmt.minNormalMantissa (e + 1)| := by
  have habs :
      |fmt.normalizedValue negative fmt.minNormalMantissa (e + 1)| =
        fmt.betaR ^ e := by
    rw [fmt.normalizedValue_abs negative fmt.minNormalMantissa (e + 1)]
    calc
      (fmt.minNormalMantissa : ℝ) *
          fmt.betaR ^ ((e + 1) - (fmt.t : ℤ)) =
          fmt.betaR ^ ((e + 1) - 1) := by
        exact fmt.minNormalMantissa_scale_eq (e + 1)
      _ = fmt.betaR ^ e := by
        congr 1
        ring
  constructor
  · have hscale :
        fmt.betaR⁻¹ * fmt.machineEpsilon * fmt.betaR ^ e =
          fmt.betaR ^ (e - (fmt.t : ℤ)) := by
      simpa using fmt.beta_inv_machineEpsilon_mul_upper_power_eq e
    simp [habs, hscale]
  · have hone : (1 : ℝ) ≤ fmt.betaR := by
      unfold betaR
      exact_mod_cast (le_trans (by decide : 1 ≤ 2) fmt.beta_ge_two)
    have hexp_le : e - (fmt.t : ℤ) ≤ e + 1 - (fmt.t : ℤ) := by
      exact sub_le_sub_right
        (le_add_of_nonneg_right (by decide : (0 : ℤ) ≤ 1)) (fmt.t : ℤ)
    have hpow_le :
        fmt.betaR ^ (e - (fmt.t : ℤ)) ≤
          fmt.betaR ^ (e + 1 - (fmt.t : ℤ)) :=
      zpow_le_zpow_right₀ hone hexp_le
    have hscale :
        fmt.machineEpsilon *
            |fmt.normalizedValue negative fmt.minNormalMantissa (e + 1)| =
          fmt.betaR ^ (e + 1 - (fmt.t : ℤ)) := by
      calc
        fmt.machineEpsilon *
            |fmt.normalizedValue negative fmt.minNormalMantissa (e + 1)| =
            fmt.machineEpsilon * fmt.betaR ^ e := by
          rw [habs]
        _ = fmt.machineEpsilon * fmt.betaR ^ ((e + 1) - 1) := by
          congr 1
          congr 1
          ring
        _ = fmt.betaR ^ ((e + 1) - (fmt.t : ℤ)) := by
          exact fmt.machineEpsilon_mul_lower_power_eq (e + 1)
    simpa [hscale] using hpow_le

theorem sameExponentAdjacentNormalized_abs_sub
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sameExponentAdjacentNormalized x y) :
    ∃ e : ℤ, |x - y| = fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  rcases h with ⟨negative, m, e, _hm, _hmnext, hxy⟩
  refine ⟨e, ?_⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨rfl, rfl⟩
    rw [abs_sub_comm]
    exact fmt.normalizedValue_succ_spacing negative m e
  · rcases hxy with ⟨rfl, rfl⟩
    exact fmt.normalizedValue_succ_spacing negative m e

theorem sameExponentAdjacentNormalized_abs_sub_eq_ulpAtExponent
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sameExponentAdjacentNormalized x y) :
    ∃ e : ℤ, |x - y| = fmt.ulpAtExponent e := by
  rcases fmt.sameExponentAdjacentNormalized_abs_sub h with ⟨e, hspace⟩
  exact ⟨e, by simpa [ulpAtExponent] using hspace⟩

theorem boundaryAdjacentNormalized_abs_sub
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.boundaryAdjacentNormalized x y) :
    ∃ e : ℤ, |x - y| = fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  rcases h with ⟨negative, e, hxy⟩
  refine ⟨e, ?_⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨rfl, rfl⟩
    rw [abs_sub_comm]
    exact fmt.normalizedValue_boundary_spacing negative e
  · rcases hxy with ⟨rfl, rfl⟩
    exact fmt.normalizedValue_boundary_spacing negative e

theorem boundaryAdjacentNormalized_abs_sub_eq_ulpAtExponent
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.boundaryAdjacentNormalized x y) :
    ∃ e : ℤ, |x - y| = fmt.ulpAtExponent e := by
  rcases fmt.boundaryAdjacentNormalized_abs_sub h with ⟨e, hspace⟩
  exact ⟨e, by simpa [ulpAtExponent] using hspace⟩

theorem adjacentNormalized_abs_sub
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.adjacentNormalized x y) :
    ∃ e : ℤ, |x - y| = fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  rcases h with hsame | hboundary
  · exact sameExponentAdjacentNormalized_abs_sub hsame
  · exact boundaryAdjacentNormalized_abs_sub hboundary

theorem adjacentNormalized_abs_sub_eq_ulpAtExponent
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.adjacentNormalized x y) :
    ∃ e : ℤ, |x - y| = fmt.ulpAtExponent e := by
  rcases h with hsame | hboundary
  · exact fmt.sameExponentAdjacentNormalized_abs_sub_eq_ulpAtExponent hsame
  · exact fmt.boundaryAdjacentNormalized_abs_sub_eq_ulpAtExponent hboundary

theorem sameExponentAdjacentNormalized_left_mem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sameExponentAdjacentNormalized x y) :
    fmt.unboundedNormalizedSystem x := by
  rcases h with ⟨negative, m, e, hm, hmnext, hxy⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨rfl, _⟩
    exact ⟨negative, m, e, hm, rfl⟩
  · rcases hxy with ⟨rfl, _⟩
    exact ⟨negative, m + 1, e, hmnext, rfl⟩

theorem sameExponentAdjacentNormalized_right_mem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sameExponentAdjacentNormalized x y) :
    fmt.unboundedNormalizedSystem y := by
  rcases h with ⟨negative, m, e, hm, hmnext, hxy⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨_, rfl⟩
    exact ⟨negative, m + 1, e, hmnext, rfl⟩
  · rcases hxy with ⟨_, rfl⟩
    exact ⟨negative, m, e, hm, rfl⟩

theorem boundaryAdjacentNormalized_left_mem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.boundaryAdjacentNormalized x y) :
    fmt.unboundedNormalizedSystem x := by
  rcases h with ⟨negative, e, hxy⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨rfl, _⟩
    exact ⟨negative, fmt.maxNormalMantissa, e,
      fmt.maxNormalMantissa_normalized, rfl⟩
  · rcases hxy with ⟨rfl, _⟩
    exact ⟨negative, fmt.minNormalMantissa, e + 1,
      fmt.minNormalMantissa_normalized, rfl⟩

theorem boundaryAdjacentNormalized_right_mem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.boundaryAdjacentNormalized x y) :
    fmt.unboundedNormalizedSystem y := by
  rcases h with ⟨negative, e, hxy⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨_, rfl⟩
    exact ⟨negative, fmt.minNormalMantissa, e + 1,
      fmt.minNormalMantissa_normalized, rfl⟩
  · rcases hxy with ⟨_, rfl⟩
    exact ⟨negative, fmt.maxNormalMantissa, e,
      fmt.maxNormalMantissa_normalized, rfl⟩

theorem adjacentNormalized_left_mem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.adjacentNormalized x y) :
    fmt.unboundedNormalizedSystem x := by
  rcases h with hsame | hboundary
  · exact sameExponentAdjacentNormalized_left_mem hsame
  · exact boundaryAdjacentNormalized_left_mem hboundary

theorem adjacentNormalized_right_mem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.adjacentNormalized x y) :
    fmt.unboundedNormalizedSystem y := by
  rcases h with hsame | hboundary
  · exact sameExponentAdjacentNormalized_right_mem hsame
  · exact boundaryAdjacentNormalized_right_mem hboundary

theorem adjacentNormalized_ne
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.adjacentNormalized x y) :
    x ≠ y := by
  intro hxy
  rcases adjacentNormalized_abs_sub h with ⟨e, hspace⟩
  have hzero : (0 : ℝ) = fmt.betaR ^ (e - (fmt.t : ℤ)) := by
    simpa [hxy] using hspace
  exact (ne_of_gt (fmt.betaR_zpow_pos (e - (fmt.t : ℤ)))) hzero.symm

theorem adjacentNormalized_endpoint_data
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.adjacentNormalized x y) :
    fmt.unboundedNormalizedSystem x ∧
      fmt.unboundedNormalizedSystem y ∧ x ≠ y :=
  ⟨adjacentNormalized_left_mem h,
    adjacentNormalized_right_mem h,
    adjacentNormalized_ne h⟩

theorem realOrderAdjacentNormalized_of_adjacentNormalized_no_between
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.adjacentNormalized x y)
    (hbetween : ∀ z, fmt.unboundedNormalizedSystem z →
      ¬ ((x < z ∧ z < y) ∨ (y < z ∧ z < x))) :
    fmt.realOrderAdjacentNormalized x y := by
  exact ⟨adjacentNormalized_left_mem h,
    adjacentNormalized_right_mem h,
    adjacentNormalized_ne h,
    hbetween⟩

theorem realOrderAdjacentNormalized_symm
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y) :
    fmt.realOrderAdjacentNormalized y x := by
  refine ⟨h.2.1, h.1, h.2.2.1.symm, ?_⟩
  intro z hz hbetween
  apply h.2.2.2 z hz
  rcases hbetween with hbetween | hbetween
  · exact Or.inr hbetween
  · exact Or.inl hbetween

theorem realOrderAdjacentNormalized_neg_ordered
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y) :
    fmt.realOrderAdjacentNormalized (-y) (-x) := by
  refine
    ⟨fmt.unboundedNormalizedSystem_neg h.2.1,
      fmt.unboundedNormalizedSystem_neg h.1, ?_, ?_⟩
  · intro hneg_eq
    apply h.2.2.1
    linarith
  · intro z hz hbetween
    have hzneg : fmt.unboundedNormalizedSystem (-z) :=
      fmt.unboundedNormalizedSystem_neg hz
    apply h.2.2.2 (-z) hzneg
    rcases hbetween with hbetween | hbetween
    · rcases hbetween with ⟨hyz, hzx⟩
      exact Or.inl ⟨by linarith, by linarith⟩
    · rcases hbetween with ⟨hxz, hzy⟩
      exact Or.inr ⟨by linarith, by linarith⟩

theorem sameExponentAdjacentNormalized_symm
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sameExponentAdjacentNormalized x y) :
    fmt.sameExponentAdjacentNormalized y x := by
  rcases h with ⟨negative, m, e, hm, hmnext, hxy⟩
  refine ⟨negative, m, e, hm, hmnext, ?_⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨rfl, rfl⟩
    exact Or.inr ⟨rfl, rfl⟩
  · rcases hxy with ⟨rfl, rfl⟩
    exact Or.inl ⟨rfl, rfl⟩

theorem boundaryAdjacentNormalized_symm
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.boundaryAdjacentNormalized x y) :
    fmt.boundaryAdjacentNormalized y x := by
  rcases h with ⟨negative, e, hxy⟩
  refine ⟨negative, e, ?_⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨rfl, rfl⟩
    exact Or.inr ⟨rfl, rfl⟩
  · rcases hxy with ⟨rfl, rfl⟩
    exact Or.inl ⟨rfl, rfl⟩

theorem adjacentNormalized_symm
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.adjacentNormalized x y) :
    fmt.adjacentNormalized y x := by
  rcases h with hsame | hboundary
  · exact Or.inl (fmt.sameExponentAdjacentNormalized_symm hsame)
  · exact Or.inr (fmt.boundaryAdjacentNormalized_symm hboundary)

theorem sameExponentAdjacentNormalized_neg
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sameExponentAdjacentNormalized x y) :
    fmt.sameExponentAdjacentNormalized (-x) (-y) := by
  rcases h with ⟨negative, m, e, hm, hmnext, hxy⟩
  refine ⟨!negative, m, e, hm, hmnext, ?_⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨hx, hy⟩
    have hxneg :
        -x = fmt.normalizedValue (!negative) m e := by
      rw [hx, ← fmt.normalizedValue_not_eq_neg negative m e]
    have hyneg :
        -y = fmt.normalizedValue (!negative) (m + 1) e := by
      rw [hy, ← fmt.normalizedValue_not_eq_neg negative (m + 1) e]
    exact Or.inl ⟨hxneg, hyneg⟩
  · rcases hxy with ⟨hx, hy⟩
    have hxneg :
        -x = fmt.normalizedValue (!negative) (m + 1) e := by
      rw [hx, ← fmt.normalizedValue_not_eq_neg negative (m + 1) e]
    have hyneg :
        -y = fmt.normalizedValue (!negative) m e := by
      rw [hy, ← fmt.normalizedValue_not_eq_neg negative m e]
    exact Or.inr ⟨hxneg, hyneg⟩

theorem boundaryAdjacentNormalized_neg
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.boundaryAdjacentNormalized x y) :
    fmt.boundaryAdjacentNormalized (-x) (-y) := by
  rcases h with ⟨negative, e, hxy⟩
  refine ⟨!negative, e, ?_⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨hx, hy⟩
    have hxneg :
        -x = fmt.normalizedValue (!negative) fmt.maxNormalMantissa e := by
      rw [hx, ← fmt.normalizedValue_not_eq_neg negative fmt.maxNormalMantissa e]
    have hyneg :
        -y = fmt.normalizedValue (!negative) fmt.minNormalMantissa (e + 1) := by
      rw [hy, ← fmt.normalizedValue_not_eq_neg negative fmt.minNormalMantissa (e + 1)]
    exact Or.inl ⟨hxneg, hyneg⟩
  · rcases hxy with ⟨hx, hy⟩
    have hxneg :
        -x = fmt.normalizedValue (!negative) fmt.minNormalMantissa (e + 1) := by
      rw [hx, ← fmt.normalizedValue_not_eq_neg negative fmt.minNormalMantissa (e + 1)]
    have hyneg :
        -y = fmt.normalizedValue (!negative) fmt.maxNormalMantissa e := by
      rw [hy, ← fmt.normalizedValue_not_eq_neg negative fmt.maxNormalMantissa e]
    exact Or.inr ⟨hxneg, hyneg⟩

theorem adjacentNormalized_neg
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.adjacentNormalized x y) :
    fmt.adjacentNormalized (-x) (-y) := by
  rcases h with hsame | hboundary
  · exact Or.inl (fmt.sameExponentAdjacentNormalized_neg hsame)
  · exact Or.inr (fmt.boundaryAdjacentNormalized_neg hboundary)

theorem sameExponentAdjacentNormalized_no_between
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sameExponentAdjacentNormalized x y) :
    ∀ z, fmt.unboundedNormalizedSystem z →
      ¬ ((x < z ∧ z < y) ∨ (y < z ∧ z < x)) := by
  intro z hz
  rcases h with ⟨negative, m, e, hm, hmnext, hxy⟩
  rcases hz with ⟨znegative, k, e', hk, rfl⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨rfl, rfl⟩
    exact fmt.normalizedValue_no_between_succ negative znegative hm hmnext hk
  · rcases hxy with ⟨rfl, rfl⟩
    have hnb :=
      fmt.normalizedValue_no_between_succ
        negative znegative (e := e) (e' := e') hm hmnext hk
    intro hbetween
    apply hnb
    rcases hbetween with hbetween | hbetween
    · exact Or.inr hbetween
    · exact Or.inl hbetween

theorem realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sameExponentAdjacentNormalized x y) :
    fmt.realOrderAdjacentNormalized x y :=
  fmt.realOrderAdjacentNormalized_of_adjacentNormalized_no_between
    (Or.inl h) (fmt.sameExponentAdjacentNormalized_no_between h)

theorem boundaryAdjacentNormalized_no_between
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.boundaryAdjacentNormalized x y) :
    ∀ z, fmt.unboundedNormalizedSystem z →
      ¬ ((x < z ∧ z < y) ∨ (y < z ∧ z < x)) := by
  intro z hz
  rcases h with ⟨negative, e, hxy⟩
  rcases hz with ⟨znegative, k, e', hk, rfl⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨rfl, rfl⟩
    exact fmt.normalizedValue_boundary_no_between negative znegative hk
  · rcases hxy with ⟨rfl, rfl⟩
    have hnb :=
      fmt.normalizedValue_boundary_no_between
        negative znegative (e := e) (e' := e') hk
    intro hbetween
    apply hnb
    rcases hbetween with hbetween | hbetween
    · exact Or.inr hbetween
    · exact Or.inl hbetween

theorem realOrderAdjacentNormalized_of_boundaryAdjacentNormalized
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.boundaryAdjacentNormalized x y) :
    fmt.realOrderAdjacentNormalized x y :=
  fmt.realOrderAdjacentNormalized_of_adjacentNormalized_no_between
    (Or.inr h) (fmt.boundaryAdjacentNormalized_no_between h)

theorem adjacentNormalized_no_between
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.adjacentNormalized x y) :
    ∀ z, fmt.unboundedNormalizedSystem z →
      ¬ ((x < z ∧ z < y) ∨ (y < z ∧ z < x)) := by
  rcases h with hsame | hboundary
  · exact fmt.sameExponentAdjacentNormalized_no_between hsame
  · exact fmt.boundaryAdjacentNormalized_no_between hboundary

theorem realOrderAdjacentNormalized_of_adjacentNormalized
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.adjacentNormalized x y) :
    fmt.realOrderAdjacentNormalized x y :=
  fmt.realOrderAdjacentNormalized_of_adjacentNormalized_no_between
    h (fmt.adjacentNormalized_no_between h)

theorem realOrderAdjacentNormalized_same_sign_of_representations
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y)
    {negative znegative : Bool} {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (hx : x = fmt.normalizedValue negative m e)
    (hy : y = fmt.normalizedValue znegative n e') :
    negative = znegative := by
  cases negative <;> cases znegative
  · rfl
  · exfalso
    let z := fmt.normalizedValue false fmt.maxNormalMantissa (e - 1)
    have hz_mem : fmt.unboundedNormalizedSystem z :=
      ⟨false, fmt.maxNormalMantissa, e - 1,
        fmt.maxNormalMantissa_normalized, rfl⟩
    have hz_pos :
        0 < z :=
      fmt.normalizedValue_false_pos
        (m := fmt.maxNormalMantissa) (e := e - 1)
        fmt.maxNormalMantissa_normalized
    have hy_neg : y < 0 := by
      rw [hy]
      exact fmt.normalizedValue_true_neg (m := n) (e := e') hn
    have hz_lt_x : z < x := by
      rw [hx]
      exact fmt.normalizedValue_false_lt_of_exp_lt
        fmt.maxNormalMantissa_normalized hm (by omega)
    exact (h.2.2.2 z hz_mem) (Or.inr ⟨lt_trans hy_neg hz_pos, hz_lt_x⟩)
  · exfalso
    let z := fmt.normalizedValue false fmt.maxNormalMantissa (e' - 1)
    have hz_mem : fmt.unboundedNormalizedSystem z :=
      ⟨false, fmt.maxNormalMantissa, e' - 1,
        fmt.maxNormalMantissa_normalized, rfl⟩
    have hz_pos :
        0 < z :=
      fmt.normalizedValue_false_pos
        (m := fmt.maxNormalMantissa) (e := e' - 1)
        fmt.maxNormalMantissa_normalized
    have hx_neg : x < 0 := by
      rw [hx]
      exact fmt.normalizedValue_true_neg (m := m) (e := e) hm
    have hz_lt_y : z < y := by
      rw [hy]
      exact fmt.normalizedValue_false_lt_of_exp_lt
        fmt.maxNormalMantissa_normalized hn (by omega)
    exact (h.2.2.2 z hz_mem) (Or.inl ⟨lt_trans hx_neg hz_pos, hz_lt_y⟩)
  · rfl

theorem realOrderAdjacentNormalized_false_ordered_exp_ge
    {fmt : FloatingPointFormat} {x y : ℝ}
    (_h : fmt.realOrderAdjacentNormalized x y)
    {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (hx : x = fmt.normalizedValue false m e)
    (hy : y = fmt.normalizedValue false n e')
    (hxy : x < y) :
    e ≤ e' := by
  by_contra hnot
  have hlt : e' < e := by
    omega
  have hy_lt_x : y < x := by
    rw [hx, hy]
    exact fmt.normalizedValue_false_lt_of_exp_lt hn hm hlt
  exact (not_lt_of_ge (le_of_lt hy_lt_x)) hxy

theorem realOrderAdjacentNormalized_false_ordered_exp_le_succ
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y)
    {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (hx : x = fmt.normalizedValue false m e)
    (hy : y = fmt.normalizedValue false n e')
    (_hxy : x < y) :
    e' ≤ e + 1 := by
  by_contra hnot
  have hgap : e + 1 < e' := by
    omega
  let z := fmt.normalizedValue false fmt.minNormalMantissa (e + 1)
  have hz_mem : fmt.unboundedNormalizedSystem z :=
    ⟨false, fmt.minNormalMantissa, e + 1,
      fmt.minNormalMantissa_normalized, rfl⟩
  have hx_lt_z : x < z := by
    rw [hx]
    change fmt.normalizedValue false m e <
      fmt.normalizedValue false fmt.minNormalMantissa (e + 1)
    rw [fmt.normalizedValue_false_minNormalMantissa_succ_eq_beta_pow e]
    exact fmt.normalizedValue_false_lt_beta_pow hm
  have hz_lt_y : z < y := by
    rw [hy]
    exact fmt.normalizedValue_false_lt_of_exp_lt
      fmt.minNormalMantissa_normalized hn hgap
  exact (h.2.2.2 z hz_mem) (Or.inl ⟨hx_lt_z, hz_lt_y⟩)

theorem realOrderAdjacentNormalized_false_ordered_exp_eq_or_succ
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y)
    {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (hx : x = fmt.normalizedValue false m e)
    (hy : y = fmt.normalizedValue false n e')
    (hxy : x < y) :
    e' = e ∨ e' = e + 1 := by
  have hge :=
    fmt.realOrderAdjacentNormalized_false_ordered_exp_ge h hm hn hx hy hxy
  have hle :=
    fmt.realOrderAdjacentNormalized_false_ordered_exp_le_succ h hm hn hx hy hxy
  omega

theorem realOrderAdjacentNormalized_false_ordered_same_exp_mantissa_succ
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y)
    {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (hx : x = fmt.normalizedValue false m e)
    (hy : y = fmt.normalizedValue false n e')
    (hxy : x < y) (he : e' = e) :
    n = m + 1 := by
  subst e'
  have hval : fmt.normalizedValue false m e <
      fmt.normalizedValue false n e := by
    simpa [hx, hy] using hxy
  have hmn : m < n :=
    (fmt.normalizedValue_sameExponent_lt_iff_false m n e).mp hval
  by_contra hne
  have hgap : m + 1 < n := by
    omega
  have hmnext : fmt.normalizedMantissa (m + 1) :=
    ⟨le_trans hm.1 (Nat.le_succ m), lt_trans hgap hn.2⟩
  let z := fmt.normalizedValue false (m + 1) e
  have hz_mem : fmt.unboundedNormalizedSystem z :=
    ⟨false, m + 1, e, hmnext, rfl⟩
  have hx_lt_z : x < z := by
    rw [hx]
    exact (fmt.normalizedValue_sameExponent_lt_iff_false m (m + 1) e).2
      (Nat.lt_succ_self m)
  have hz_lt_y : z < y := by
    rw [hy]
    exact (fmt.normalizedValue_sameExponent_lt_iff_false (m + 1) n e).2 hgap
  exact (h.2.2.2 z hz_mem) (Or.inl ⟨hx_lt_z, hz_lt_y⟩)

theorem realOrderAdjacentNormalized_false_ordered_succ_exp_mantissa_boundary
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y)
    {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (hx : x = fmt.normalizedValue false m e)
    (hy : y = fmt.normalizedValue false n e')
    (he : e' = e + 1) :
    m = fmt.maxNormalMantissa ∧ n = fmt.minNormalMantissa := by
  subst e'
  constructor
  · by_contra hmmax
    have hm_le_max : m ≤ fmt.maxNormalMantissa := by
      unfold maxNormalMantissa
      exact Nat.le_sub_one_of_lt hm.2
    have hm_lt_max : m < fmt.maxNormalMantissa :=
      lt_of_le_of_ne hm_le_max hmmax
    have hmnext : fmt.normalizedMantissa (m + 1) :=
      ⟨le_trans hm.1 (Nat.le_succ m),
        lt_of_le_of_lt (Nat.succ_le_of_lt hm_lt_max)
          fmt.maxNormalMantissa_lt_mantissaBound⟩
    let z := fmt.normalizedValue false (m + 1) e
    have hz_mem : fmt.unboundedNormalizedSystem z :=
      ⟨false, m + 1, e, hmnext, rfl⟩
    have hx_lt_z : x < z := by
      rw [hx]
      exact (fmt.normalizedValue_sameExponent_lt_iff_false m (m + 1) e).2
        (Nat.lt_succ_self m)
    have hz_lt_y : z < y := by
      rw [hy]
      exact fmt.normalizedValue_false_lt_of_exp_lt hmnext hn (by omega)
    exact (h.2.2.2 z hz_mem) (Or.inl ⟨hx_lt_z, hz_lt_y⟩)
  · by_contra hnmin
    have hmin_ne_n : fmt.minNormalMantissa ≠ n := by
      intro hmin_eq_n
      exact hnmin hmin_eq_n.symm
    have hmin_lt_n : fmt.minNormalMantissa < n :=
      lt_of_le_of_ne hn.1 hmin_ne_n
    let z := fmt.normalizedValue false fmt.minNormalMantissa (e + 1)
    have hz_mem : fmt.unboundedNormalizedSystem z :=
      ⟨false, fmt.minNormalMantissa, e + 1,
        fmt.minNormalMantissa_normalized, rfl⟩
    have hx_lt_z : x < z := by
      rw [hx]
      exact fmt.normalizedValue_false_lt_of_exp_lt
        hm fmt.minNormalMantissa_normalized (by omega)
    have hz_lt_y : z < y := by
      rw [hy]
      exact (fmt.normalizedValue_sameExponent_lt_iff_false
        fmt.minNormalMantissa n (e + 1)).2 hmin_lt_n
    exact (h.2.2.2 z hz_mem) (Or.inl ⟨hx_lt_z, hz_lt_y⟩)

theorem realOrderAdjacentNormalized_false_ordered_adjacentNormalized
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y)
    {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (hx : x = fmt.normalizedValue false m e)
    (hy : y = fmt.normalizedValue false n e')
    (hxy : x < y) :
    fmt.adjacentNormalized x y := by
  rcases fmt.realOrderAdjacentNormalized_false_ordered_exp_eq_or_succ
      h hm hn hx hy hxy with he | hsucc
  · have hn_succ :=
      fmt.realOrderAdjacentNormalized_false_ordered_same_exp_mantissa_succ
        h hm hn hx hy hxy he
    have hmnext : fmt.normalizedMantissa (m + 1) := by
      simpa [hn_succ] using hn
    have hy_succ : y = fmt.normalizedValue false (m + 1) e := by
      simpa [hn_succ, he] using hy
    exact Or.inl
      ⟨false, m, e, hm, hmnext, Or.inl ⟨hx, hy_succ⟩⟩
  · have hboundary :=
      fmt.realOrderAdjacentNormalized_false_ordered_succ_exp_mantissa_boundary
        h hm hn hx hy hsucc
    rcases hboundary with ⟨hmmax, hnmin⟩
    have hx_max : x = fmt.normalizedValue false fmt.maxNormalMantissa e := by
      simpa [hmmax] using hx
    have hy_min :
        y = fmt.normalizedValue false fmt.minNormalMantissa (e + 1) := by
      simpa [hnmin, hsucc] using hy
    exact Or.inr ⟨false, e, Or.inl ⟨hx_max, hy_min⟩⟩

theorem realOrderAdjacentNormalized_false_representations_adjacentNormalized
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y)
    {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (hx : x = fmt.normalizedValue false m e)
    (hy : y = fmt.normalizedValue false n e') :
    fmt.adjacentNormalized x y := by
  rcases lt_or_gt_of_ne h.2.2.1 with hxy | hyx
  · exact fmt.realOrderAdjacentNormalized_false_ordered_adjacentNormalized
      h hm hn hx hy hxy
  · exact fmt.adjacentNormalized_symm
      (fmt.realOrderAdjacentNormalized_false_ordered_adjacentNormalized
        (fmt.realOrderAdjacentNormalized_symm h) hn hm hy hx hyx)

theorem realOrderAdjacentNormalized_false_of_true_representations
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y)
    {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (hx : x = fmt.normalizedValue true m e)
    (hy : y = fmt.normalizedValue true n e') :
    fmt.realOrderAdjacentNormalized
      (fmt.normalizedValue false m e)
      (fmt.normalizedValue false n e') := by
  let a := fmt.normalizedValue false m e
  let b := fmt.normalizedValue false n e'
  have hx_neg : x = -a := by
    dsimp [a]
    rw [hx, fmt.normalizedValue_true_eq_neg_false m e]
  have hy_neg : y = -b := by
    dsimp [b]
    rw [hy, fmt.normalizedValue_true_eq_neg_false n e']
  refine ⟨⟨false, m, e, hm, rfl⟩, ⟨false, n, e', hn, rfl⟩, ?_, ?_⟩
  · intro hab
    have hab_ab : a = b := by
      simpa [a, b] using hab
    apply h.2.2.1
    rw [hx_neg, hy_neg, hab_ab]
  · intro z hz hbetween
    rcases hz with ⟨negative, k, ez, hk, rfl⟩
    let zneg := fmt.normalizedValue (!negative) k ez
    have hzneg_mem : fmt.unboundedNormalizedSystem zneg :=
      ⟨!negative, k, ez, hk, rfl⟩
    have hzneg_eq :
        zneg = -fmt.normalizedValue negative k ez :=
      fmt.normalizedValue_not_eq_neg negative k ez
    apply h.2.2.2 zneg hzneg_mem
    rcases hbetween with hbetween | hbetween
    · rcases hbetween with ⟨haz, hzb⟩
      have hy_lt_zneg : y < zneg := by
        rw [hy_neg, hzneg_eq]
        exact neg_lt_neg hzb
      have zneg_lt_x : zneg < x := by
        rw [hx_neg, hzneg_eq]
        exact neg_lt_neg haz
      exact Or.inr ⟨hy_lt_zneg, zneg_lt_x⟩
    · rcases hbetween with ⟨hbz, hza⟩
      have hx_lt_zneg : x < zneg := by
        rw [hx_neg, hzneg_eq]
        exact neg_lt_neg hza
      have zneg_lt_y : zneg < y := by
        rw [hy_neg, hzneg_eq]
        exact neg_lt_neg hbz
      exact Or.inl ⟨hx_lt_zneg, zneg_lt_y⟩

theorem realOrderAdjacentNormalized_true_representations_adjacentNormalized
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y)
    {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (hx : x = fmt.normalizedValue true m e)
    (hy : y = fmt.normalizedValue true n e') :
    fmt.adjacentNormalized x y := by
  let a := fmt.normalizedValue false m e
  let b := fmt.normalizedValue false n e'
  have hx_neg : x = -a := by
    dsimp [a]
    rw [hx, fmt.normalizedValue_true_eq_neg_false m e]
  have hy_neg : y = -b := by
    dsimp [b]
    rw [hy, fmt.normalizedValue_true_eq_neg_false n e']
  have hpos :=
    fmt.realOrderAdjacentNormalized_false_of_true_representations h hm hn hx hy
  have hpos_adj :
      fmt.adjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_false_representations_adjacentNormalized
      hpos hm hn rfl rfl
  have hneg_adj : fmt.adjacentNormalized (-a) (-b) :=
    fmt.adjacentNormalized_neg hpos_adj
  rw [hx_neg, hy_neg]
  exact hneg_adj

theorem adjacentNormalized_of_realOrderAdjacentNormalized
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y) :
    fmt.adjacentNormalized x y := by
  rcases h.1 with ⟨negative, m, e, hm, hx⟩
  rcases h.2.1 with ⟨znegative, n, e', hn, hy⟩
  have hsign :=
    fmt.realOrderAdjacentNormalized_same_sign_of_representations
      h hm hn hx hy
  subst znegative
  cases negative
  · exact fmt.realOrderAdjacentNormalized_false_representations_adjacentNormalized
      h hm hn hx hy
  · exact fmt.realOrderAdjacentNormalized_true_representations_adjacentNormalized
      h hm hn hx hy

theorem sameExponentAdjacentNormalized_spacing_bounds_left
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sameExponentAdjacentNormalized x y) :
    fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon * |x| ≤ |x - y| ∧
      |x - y| ≤ fmt.machineEpsilon * |x| := by
  rcases h with ⟨negative, m, e, hm, hmnext, hxy⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨rfl, rfl⟩
    have hb :=
      fmt.normalizedValue_spacing_bounds
        (negative := negative) (m := m) (e := e) hm
    have hspace :
        |fmt.normalizedValue negative m e -
          fmt.normalizedValue negative (m + 1) e| =
            fmt.betaR ^ (e - (fmt.t : ℤ)) := by
      rw [abs_sub_comm]
      exact fmt.normalizedValue_succ_spacing negative m e
    constructor
    · simpa [hspace] using hb.1
    · simpa [hspace] using hb.2
  · rcases hxy with ⟨rfl, rfl⟩
    have hb :=
      fmt.normalizedValue_spacing_bounds
        (negative := negative) (m := m + 1) (e := e) hmnext
    constructor
    · simpa [fmt.normalizedValue_succ_spacing negative m e] using hb.1
    · simpa [fmt.normalizedValue_succ_spacing negative m e] using hb.2

theorem boundaryAdjacentNormalized_spacing_bounds_left
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.boundaryAdjacentNormalized x y) :
    fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon * |x| ≤ |x - y| ∧
      |x - y| ≤ fmt.machineEpsilon * |x| := by
  rcases h with ⟨negative, e, hxy⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨rfl, rfl⟩
    have hb :=
      fmt.normalizedValue_spacing_bounds
        (negative := negative) (m := fmt.maxNormalMantissa) (e := e)
        fmt.maxNormalMantissa_normalized
    have hspace :
        |fmt.normalizedValue negative fmt.maxNormalMantissa e -
          fmt.normalizedValue negative fmt.minNormalMantissa (e + 1)| =
            fmt.betaR ^ (e - (fmt.t : ℤ)) := by
      rw [abs_sub_comm]
      exact fmt.normalizedValue_boundary_spacing negative e
    constructor
    · simpa [hspace] using hb.1
    · simpa [hspace] using hb.2
  · rcases hxy with ⟨rfl, rfl⟩
    have hb := fmt.normalizedValue_boundary_min_spacing_bounds negative e
    constructor
    · simpa [fmt.normalizedValue_boundary_spacing negative e] using hb.1
    · simpa [fmt.normalizedValue_boundary_spacing negative e] using hb.2

theorem adjacentNormalized_spacing_bounds_left
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.adjacentNormalized x y) :
    fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon * |x| ≤ |x - y| ∧
      |x - y| ≤ fmt.machineEpsilon * |x| := by
  rcases h with hsame | hboundary
  · exact sameExponentAdjacentNormalized_spacing_bounds_left hsame
  · exact boundaryAdjacentNormalized_spacing_bounds_left hboundary

theorem realOrderAdjacentNormalized_spacing_bounds_left
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y) :
    fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon * |x| ≤ |x - y| ∧
      |x - y| ≤ fmt.machineEpsilon * |x| :=
  fmt.adjacentNormalized_spacing_bounds_left
    (fmt.adjacentNormalized_of_realOrderAdjacentNormalized h)

theorem realOrderAdjacentNormalized_relativeSpacing_bounds_left
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y) :
    fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon ≤ |x - y| / |x| ∧
      |x - y| / |x| ≤ fmt.machineEpsilon := by
  have hb := fmt.realOrderAdjacentNormalized_spacing_bounds_left h
  have hxpos : 0 < |x| :=
    abs_pos.mpr (fmt.unboundedNormalizedSystem_ne_zero h.1)
  constructor
  · have hdiv := div_le_div_of_nonneg_right hb.1 hxpos.le
    have hcancel :
        fmt.betaR⁻¹ * fmt.machineEpsilon * |x| / |x| =
          fmt.betaR⁻¹ * fmt.machineEpsilon := by
      field_simp [ne_of_gt hxpos]
    simpa [hcancel] using hdiv
  · have hdiv := div_le_div_of_nonneg_right hb.2 hxpos.le
    have hcancel :
        (fmt.machineEpsilon * |x|) / |x| = fmt.machineEpsilon := by
      field_simp [ne_of_gt hxpos]
    simpa [hcancel] using hdiv

theorem ieeeSingleFormat_realOrderAdjacentNormalized_relativeSpacing_bounds_left
    {x y : ℝ}
    (h : ieeeSingleFormat.realOrderAdjacentNormalized x y) :
    (2 : ℝ) ^ (-24 : ℤ) ≤ |x - y| / |x| ∧
      |x - y| / |x| ≤ (2 : ℝ) ^ (-23 : ℤ) := by
  have hb := ieeeSingleFormat.realOrderAdjacentNormalized_relativeSpacing_bounds_left h
  have hleft :
      ieeeSingleFormat.betaR⁻¹ *
          ieeeSingleFormat.machineEpsilon =
        (2 : ℝ) ^ (-24 : ℤ) := by
    rw [ieeeSingleFormat_machineEpsilon]
    norm_num [ieeeSingleFormat, betaR, zpow_neg]
  constructor
  · simpa [hleft, zpow_neg] using hb.1
  · simpa [ieeeSingleFormat_machineEpsilon] using hb.2

theorem adjacentNormalized_realOrder_spacing_bounds_left
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.adjacentNormalized x y) :
    fmt.realOrderAdjacentNormalized x y ∧
      fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon * |x| ≤ |x - y| ∧
        |x - y| ≤ fmt.machineEpsilon * |x| :=
  ⟨fmt.realOrderAdjacentNormalized_of_adjacentNormalized h,
    fmt.adjacentNormalized_spacing_bounds_left h⟩

theorem unitRoundoff_eq_half_machineEpsilon (fmt : FloatingPointFormat) :
    fmt.unitRoundoff = (1 / 2 : ℝ) * fmt.machineEpsilon :=
  rfl

theorem nearestRoundingIn_mem {S : ℝ → Prop} {x y : ℝ}
    (h : nearestRoundingIn S x y) :
    S y :=
  h.1

theorem nearestRoundingIn_minimal {S : ℝ → Prop} {x y z : ℝ}
    (h : nearestRoundingIn S x y) (hz : S z) :
    |x - y| ≤ |x - z| :=
  h.2 z hz

/-- Nearest rounding is symmetric under negation when the target set is closed
under negation. -/
theorem nearestRoundingIn_neg {S : ℝ → Prop} {x y : ℝ}
    (hSneg : ∀ {z : ℝ}, S z → S (-z))
    (h : nearestRoundingIn S x y) :
    nearestRoundingIn S (-x) (-y) := by
  refine ⟨hSneg (nearestRoundingIn_mem h), ?_⟩
  intro z hz
  have hmin := nearestRoundingIn_minimal h (hSneg hz)
  rw [show (-x) - (-y) = -(x - y) by ring,
    show (-x) - z = -(x - (-z)) by ring, abs_neg, abs_neg]
  exact hmin

/-- Finite nearest rounding is symmetric under negation. -/
theorem nearestRoundingToFinite_neg
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.nearestRoundingToFinite x y) :
    fmt.nearestRoundingToFinite (-x) (-y) :=
  nearestRoundingIn_neg (fun hz => fmt.finiteSystem_neg hz) h

/-- Floor-based mantissa bracketing.  If a nonnegative real mantissa coordinate
lies in a natural interval, it is either exactly an integer mantissa or lies
strictly between two consecutive mantissas still inside the interval. -/
theorem nat_floor_exact_or_successor_bracket
    {lo hi : ℕ} {q : ℝ}
    (hloq : (lo : ℝ) ≤ q) (hqhi : q ≤ (hi : ℝ)) :
    ∃ m : ℕ,
      lo ≤ m ∧ m ≤ hi ∧
        (q = (m : ℝ) ∨
          (m + 1 ≤ hi ∧ (m : ℝ) < q ∧ q < (m + 1 : ℝ))) := by
  let m := Nat.floor q
  have hq_nonneg : 0 ≤ q := le_trans (Nat.cast_nonneg lo) hloq
  have hlo_m : lo ≤ m := Nat.le_floor hloq
  have hm_hi : m ≤ hi := Nat.floor_le_of_le hqhi
  refine ⟨m, hlo_m, hm_hi, ?_⟩
  by_cases hq_eq : q = (m : ℝ)
  · exact Or.inl hq_eq
  · have hm_le_q : (m : ℝ) ≤ q := Nat.floor_le hq_nonneg
    have hm_lt_q : (m : ℝ) < q :=
      lt_of_le_of_ne hm_le_q (by
        intro hmq
        exact hq_eq hmq.symm)
    have hq_lt_msucc : q < (m + 1 : ℝ) := by
      simpa using Nat.lt_floor_add_one q
    have hm_lt_hi : m < hi :=
      Nat.cast_lt.mp (lt_of_lt_of_le hm_lt_q hqhi)
    exact Or.inr ⟨Nat.succ_le_iff.mpr hm_lt_hi, hm_lt_q, hq_lt_msucc⟩

/-- Half-cell natural index selection.  If a real coordinate lies strictly
between the zero/first-cell boundary and the last-subnormal/normal boundary,
then some natural index `m` with `0 < m < M` is within half a unit of it. -/
theorem exists_nat_half_cell_of_half_lt_of_lt_sub_half
    {M : ℕ} {q : ℝ}
    (hlo : (1 / 2 : ℝ) < q)
    (hhi : q < (M : ℝ) - (1 / 2 : ℝ)) :
    ∃ m : ℕ,
      0 < m ∧ m < M ∧
        (m : ℝ) - (1 / 2 : ℝ) ≤ q ∧
          q ≤ (m : ℝ) + (1 / 2 : ℝ) := by
  let r : ℝ := q + (1 / 2 : ℝ)
  let m : ℕ := Nat.floor r
  have hr_ge_one : (1 : ℝ) ≤ r := by
    dsimp [r]
    linarith
  have hr_nonneg : 0 ≤ r := by linarith
  have hm_ge_one : 1 ≤ m :=
    Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ r by simpa using hr_ge_one)
  have hm_pos : 0 < m := hm_ge_one
  have hfloor_le : (m : ℝ) ≤ r := Nat.floor_le hr_nonneg
  have hr_lt_M : r < (M : ℝ) := by
    dsimp [r]
    linarith
  have hm_lt_M : m < M :=
    Nat.cast_lt.mp (lt_of_le_of_lt hfloor_le hr_lt_M)
  have hr_lt_msucc : r < (m + 1 : ℝ) := by
    simpa [m, r] using Nat.lt_floor_add_one r
  refine ⟨m, hm_pos, hm_lt_M, ?_, ?_⟩
  · dsimp [r] at hfloor_le
    linarith
  · dsimp [r] at hr_lt_msucc
    linarith

/-- Same-exponent positive bracketing from a scaled mantissa interval.  For a
positive real input between the smallest and largest normalized values at a
fixed exponent, `Nat.floor (x / beta^(e-t))` either gives an exact normalized
representation or two adjacent normalized endpoints bracketing `x`. -/
theorem exists_unboundedNormalized_or_realOrderAdjacent_bracket_sameExponent
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hmin : fmt.normalizedValue false fmt.minNormalMantissa e ≤ x)
    (hmax : x ≤ fmt.normalizedValue false fmt.maxNormalMantissa e) :
    (∃ m : ℕ,
      fmt.normalizedMantissa m ∧ x = fmt.normalizedValue false m e) ∨
      ∃ a b : ℝ,
        fmt.realOrderAdjacentNormalized a b ∧
          0 ≤ a ∧ a ≤ x ∧ x ≤ b := by
  let s : ℝ := fmt.betaR ^ (e - (fmt.t : ℤ))
  have hs_pos : 0 < s := by
    dsimp [s]
    exact fmt.betaR_zpow_pos (e - (fmt.t : ℤ))
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hmin_scaled : (fmt.minNormalMantissa : ℝ) * s ≤ x := by
    simpa [normalizedValue, signValue, s] using hmin
  have hmax_scaled : x ≤ (fmt.maxNormalMantissa : ℝ) * s := by
    simpa [normalizedValue, signValue, s] using hmax
  have hq_min : (fmt.minNormalMantissa : ℝ) ≤ x / s :=
    (le_div_iff₀ hs_pos).2 hmin_scaled
  have hq_max : x / s ≤ (fmt.maxNormalMantissa : ℝ) :=
    (div_le_iff₀ hs_pos).2 hmax_scaled
  rcases nat_floor_exact_or_successor_bracket hq_min hq_max with
    ⟨m, hm_min, hm_max, hcase⟩
  have hm_range : fmt.mantissaInRange m :=
    lt_of_le_of_lt hm_max fmt.maxNormalMantissa_lt_mantissaBound
  have hm_norm : fmt.normalizedMantissa m := ⟨hm_min, hm_range⟩
  rcases hcase with hq_eq | hbetween
  · have hx_eq_scaled : x = (m : ℝ) * s :=
      (div_eq_iff hs_ne).mp hq_eq
    exact Or.inl
      ⟨m, hm_norm, by
        simpa [normalizedValue, signValue, s] using hx_eq_scaled⟩
  · rcases hbetween with ⟨hm_succ_max, hm_lt_q, hq_lt_succ⟩
    have hm_succ_min : fmt.minNormalMantissa ≤ m + 1 :=
      le_trans hm_min (Nat.le_succ m)
    have hm_succ_range : fmt.mantissaInRange (m + 1) :=
      lt_of_le_of_lt hm_succ_max fmt.maxNormalMantissa_lt_mantissaBound
    have hm_succ_norm : fmt.normalizedMantissa (m + 1) :=
      ⟨hm_succ_min, hm_succ_range⟩
    let a := fmt.normalizedValue false m e
    let b := fmt.normalizedValue false (m + 1) e
    have hstruct : fmt.sameExponentAdjacentNormalized a b := by
      refine ⟨false, m, e, hm_norm, hm_succ_norm, Or.inl ?_⟩
      exact ⟨rfl, rfl⟩
    have hadj : fmt.realOrderAdjacentNormalized a b :=
      fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
    have ha_nonneg : 0 ≤ a :=
      le_of_lt (fmt.normalizedValue_false_pos hm_norm)
    have ha_le_x : a ≤ x := by
      have hlt : (m : ℝ) * s < x := by
        have hmul := mul_lt_mul_of_pos_right hm_lt_q hs_pos
        simpa [s, div_mul_cancel₀ x hs_ne] using hmul
      exact le_of_lt (by
        simpa [a, normalizedValue, signValue, s] using hlt)
    have hx_le_b : x ≤ b := by
      have hlt : x < ((m + 1 : ℕ) : ℝ) * s := by
        have hmul := mul_lt_mul_of_pos_right hq_lt_succ hs_pos
        simpa [s, div_mul_cancel₀ x hs_ne] using hmul
      exact le_of_lt (by
        simpa [b, normalizedValue, signValue, s] using hlt)
    exact Or.inr ⟨a, b, hadj, ha_nonneg, ha_le_x, hx_le_b⟩

/-- Same-exponent negative bracketing, obtained from the positive floor
construction by sign symmetry.  If a negative input lies in one exponent bin,
it is either exactly represented by a negative normalized mantissa or bracketed
by adjacent negative normalized endpoints. -/
theorem exists_unboundedNormalized_or_realOrderAdjacent_bracket_sameExponent_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : fmt.normalizedValue true fmt.maxNormalMantissa e ≤ x)
    (hhi : x ≤ fmt.normalizedValue true fmt.minNormalMantissa e) :
    (∃ m : ℕ,
      fmt.normalizedMantissa m ∧ x = fmt.normalizedValue true m e) ∨
      ∃ a b : ℝ,
        fmt.realOrderAdjacentNormalized a b ∧
          b ≤ 0 ∧ a ≤ x ∧ x ≤ b := by
  have hpos_min : fmt.normalizedValue false fmt.minNormalMantissa e ≤ -x := by
    have h := neg_le_neg hhi
    simpa [fmt.normalizedValue_true_eq_neg_false] using h
  have hpos_max : -x ≤ fmt.normalizedValue false fmt.maxNormalMantissa e := by
    have h := neg_le_neg hlo
    simpa [fmt.normalizedValue_true_eq_neg_false] using h
  rcases fmt.exists_unboundedNormalized_or_realOrderAdjacent_bracket_sameExponent
      hpos_min hpos_max with hrepr | hbracket
  · rcases hrepr with ⟨m, hm, hxneg_eq⟩
    have hx_eq : x = fmt.normalizedValue true m e := by
      calc
        x = -(-x) := by simp
        _ = -fmt.normalizedValue false m e := by rw [hxneg_eq]
        _ = fmt.normalizedValue true m e := by
          rw [fmt.normalizedValue_true_eq_neg_false]
    exact Or.inl ⟨m, hm, hx_eq⟩
  · rcases hbracket with ⟨a, b, hadj, ha_nonneg, ha_le_negx, hnegx_le_b⟩
    have hneg_adj_ab : fmt.realOrderAdjacentNormalized (-a) (-b) :=
      fmt.realOrderAdjacentNormalized_of_adjacentNormalized
        (fmt.adjacentNormalized_neg
          (fmt.adjacentNormalized_of_realOrderAdjacentNormalized hadj))
    have hneg_adj : fmt.realOrderAdjacentNormalized (-b) (-a) :=
      fmt.realOrderAdjacentNormalized_symm hneg_adj_ab
    have hleft : -b ≤ x := by
      have h := neg_le_neg hnegx_le_b
      simpa using h
    have hright : x ≤ -a := by
      have h := neg_le_neg ha_le_negx
      simpa using h
    have hright_nonpos : -a ≤ 0 := by
      simpa using (neg_nonpos.mpr ha_nonneg)
    exact Or.inr ⟨-b, -a, hneg_adj, hright_nonpos, hleft, hright⟩

theorem nearestRoundingIn_self {S : ℝ → Prop} {x : ℝ}
    (hx : S x) :
    nearestRoundingIn S x x := by
  refine ⟨hx, ?_⟩
  intro z _hz
  simp

/-- If the source value is already in the target set, every nearest-rounded
output is equal to the source value. -/
theorem nearestRoundingIn_eq_self_of_mem {S : ℝ → Prop} {x y : ℝ}
    (hx : S x) (h : nearestRoundingIn S x y) :
    y = x := by
  have hdist : |x - y| ≤ 0 := by
    simpa using nearestRoundingIn_minimal h hx
  have hdist_nonneg : 0 ≤ |x - y| := abs_nonneg _
  have habs : |x - y| = 0 := le_antisymm hdist hdist_nonneg
  have hsub : x - y = 0 := abs_eq_zero.mp habs
  linarith

theorem nearestRoundingToUnbounded_self
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.unboundedNormalizedSystem x) :
    fmt.nearestRoundingToUnbounded x x :=
  nearestRoundingIn_self hx

theorem nearestRoundingToUnbounded_eq_self_of_mem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.unboundedNormalizedSystem x)
    (h : fmt.nearestRoundingToUnbounded x y) :
    y = x :=
  nearestRoundingIn_eq_self_of_mem hx h

theorem nearestRoundingToFinite_self
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteSystem x) :
    fmt.nearestRoundingToFinite x x :=
  nearestRoundingIn_self hx

theorem nearestRoundingToFinite_eq_self_of_finiteSystem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystem x)
    (h : fmt.nearestRoundingToFinite x y) :
    y = x :=
  nearestRoundingIn_eq_self_of_mem hx h

/-- Zero is part of the finite floating-point system. -/
theorem finiteSystem_zero (fmt : FloatingPointFormat) :
    fmt.finiteSystem 0 :=
  Or.inl rfl

/-- Finite-format nearest rounding sends zero to itself under the relation. -/
theorem nearestRoundingToFinite_zero (fmt : FloatingPointFormat) :
    fmt.nearestRoundingToFinite 0 0 :=
  fmt.nearestRoundingToFinite_self fmt.finiteSystem_zero

/-- Positive normal-range bridge from the unbounded nearest-rounding relation
to the finite nearest-rounding relation.  If `x` is at or above the smallest
normal magnitude and an unbounded nearest-rounded value `y` is finite, then
zero and subnormal finite candidates are no closer than the smallest normal,
while normalized finite candidates are already candidates in `G`. -/
theorem nearestRoundingToFinite_of_nearestRoundingToUnbounded_of_finite_of_minNormalMagnitude_le
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hyfin : fmt.finiteSystem y)
    (hxlo : fmt.minNormalMagnitude ≤ x) :
    fmt.nearestRoundingToFinite x y := by
  refine ⟨hyfin, ?_⟩
  intro z hz
  rcases hz with hz0 | hznorm | hzsub
  · subst z
    have hmin :=
      nearestRoundingIn_minimal hround
        fmt.minNormalMagnitude_mem_unboundedNormalizedSystem
    have hmin_nonneg : 0 ≤ fmt.minNormalMagnitude :=
      le_of_lt fmt.minNormalMagnitude_pos
    have hx_min_nonneg : 0 ≤ x - fmt.minNormalMagnitude :=
      sub_nonneg.mpr hxlo
    have hx_zero_nonneg : 0 ≤ x - 0 := by
      linarith
    have hdist : |x - fmt.minNormalMagnitude| ≤ |x - 0| := by
      rw [abs_of_nonneg hx_min_nonneg, abs_of_nonneg hx_zero_nonneg]
      linarith
    exact le_trans hmin hdist
  · exact
      nearestRoundingIn_minimal hround
        (fmt.normalizedSystem_unboundedNormalizedSystem hznorm)
  · have hmin :=
      nearestRoundingIn_minimal hround
        fmt.minNormalMagnitude_mem_unboundedNormalizedSystem
    have hz_le_min : z ≤ fmt.minNormalMagnitude :=
      fmt.subnormalSystem_le_minNormalMagnitude hzsub
    have hx_min_nonneg : 0 ≤ x - fmt.minNormalMagnitude :=
      sub_nonneg.mpr hxlo
    have hx_z_nonneg : 0 ≤ x - z :=
      sub_nonneg.mpr (le_trans hz_le_min hxlo)
    have hdist : |x - fmt.minNormalMagnitude| ≤ |x - z| := by
      rw [abs_of_nonneg hx_min_nonneg, abs_of_nonneg hx_z_nonneg]
      linarith
    exact le_trans hmin hdist

/-- Negative normal-range bridge from the unbounded nearest-rounding relation
to the finite nearest-rounding relation.  This is the sign mirror of
`nearestRoundingToFinite_of_nearestRoundingToUnbounded_of_finite_of_minNormalMagnitude_le`. -/
theorem nearestRoundingToFinite_of_nearestRoundingToUnbounded_of_finite_of_le_neg_minNormalMagnitude
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hyfin : fmt.finiteSystem y)
    (hxhi : x ≤ -fmt.minNormalMagnitude) :
    fmt.nearestRoundingToFinite x y := by
  refine ⟨hyfin, ?_⟩
  intro z hz
  rcases hz with hz0 | hznorm | hzsub
  · subst z
    have hmin :=
      nearestRoundingIn_minimal hround
        fmt.neg_minNormalMagnitude_mem_unboundedNormalizedSystem
    have hmin_nonneg : 0 ≤ fmt.minNormalMagnitude :=
      le_of_lt fmt.minNormalMagnitude_pos
    have hx_min_nonpos : x - -fmt.minNormalMagnitude ≤ 0 :=
      sub_nonpos.mpr hxhi
    have hx_zero_nonpos : x - 0 ≤ 0 := by
      linarith
    have hdist : |x - -fmt.minNormalMagnitude| ≤ |x - 0| := by
      rw [abs_of_nonpos hx_min_nonpos, abs_of_nonpos hx_zero_nonpos]
      linarith
    exact le_trans hmin hdist
  · exact
      nearestRoundingIn_minimal hround
        (fmt.normalizedSystem_unboundedNormalizedSystem hznorm)
  · have hmin :=
      nearestRoundingIn_minimal hround
        fmt.neg_minNormalMagnitude_mem_unboundedNormalizedSystem
    have hneg_min_le_z : -fmt.minNormalMagnitude ≤ z :=
      fmt.neg_minNormalMagnitude_le_subnormalSystem hzsub
    have hx_min_nonpos : x - -fmt.minNormalMagnitude ≤ 0 :=
      sub_nonpos.mpr hxhi
    have hx_z_nonpos : x - z ≤ 0 :=
      sub_nonpos.mpr (le_trans hxhi hneg_min_le_z)
    have hdist : |x - -fmt.minNormalMagnitude| ≤ |x - z| := by
      rw [abs_of_nonpos hx_min_nonpos, abs_of_nonpos hx_z_nonpos]
      linarith
    exact le_trans hmin hdist

/-- A nearest-rounded value in the unbounded system is finite whenever the
positive input lies in the finite normal interval. -/
theorem nearestRoundingToUnbounded_output_finite_of_minNormalMagnitude_le_of_le_maxFiniteMagnitude
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hxlo : fmt.minNormalMagnitude ≤ x)
    (hxhi : x ≤ fmt.maxFiniteMagnitude) :
    fmt.finiteSystem y := by
  have hmin_le_y : fmt.minNormalMagnitude ≤ y := by
    by_contra hnot
    have hy_lt : y < fmt.minNormalMagnitude := lt_of_not_ge hnot
    have hmin :=
      nearestRoundingIn_minimal hround
        fmt.minNormalMagnitude_mem_unboundedNormalizedSystem
    have hx_min_nonneg : 0 ≤ x - fmt.minNormalMagnitude :=
      sub_nonneg.mpr hxlo
    have hx_y_nonneg : 0 ≤ x - y :=
      sub_nonneg.mpr (le_trans (le_of_lt hy_lt) hxlo)
    have hdist : |x - fmt.minNormalMagnitude| < |x - y| := by
      rw [abs_of_nonneg hx_min_nonneg, abs_of_nonneg hx_y_nonneg]
      linarith
    exact not_lt_of_ge hmin hdist
  have hy_le_max : y ≤ fmt.maxFiniteMagnitude := by
    by_contra hnot
    have hmax_lt : fmt.maxFiniteMagnitude < y := lt_of_not_ge hnot
    have hmax :=
      nearestRoundingIn_minimal hround
        fmt.maxFiniteMagnitude_mem_unboundedNormalizedSystem
    have hx_max_nonpos : x - fmt.maxFiniteMagnitude ≤ 0 :=
      sub_nonpos.mpr hxhi
    have hx_y_nonpos : x - y ≤ 0 :=
      sub_nonpos.mpr (le_trans hxhi (le_of_lt hmax_lt))
    have hdist : |x - fmt.maxFiniteMagnitude| < |x - y| := by
      rw [abs_of_nonpos hx_max_nonpos, abs_of_nonpos hx_y_nonpos]
      linarith
    exact not_lt_of_ge hmax hdist
  have hy_nonneg : 0 ≤ y :=
    le_trans (le_of_lt fmt.minNormalMagnitude_pos) hmin_le_y
  have hyrange : fmt.finiteNormalRange y := by
    constructor
    · simpa [abs_of_nonneg hy_nonneg] using hmin_le_y
    · simpa [abs_of_nonneg hy_nonneg] using hy_le_max
  exact Or.inr (Or.inl
    (fmt.unboundedNormalizedSystem_normalizedSystem_of_finiteNormalRange
      (nearestRoundingIn_mem hround) hyrange))

/-- A nearest-rounded value in the unbounded system is finite whenever the
negative input lies in the finite normal interval. -/
theorem nearestRoundingToUnbounded_output_finite_of_neg_maxFiniteMagnitude_le_of_le_neg_minNormalMagnitude
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hxlo : -fmt.maxFiniteMagnitude ≤ x)
    (hxhi : x ≤ -fmt.minNormalMagnitude) :
    fmt.finiteSystem y := by
  have hnegmax_le_y : -fmt.maxFiniteMagnitude ≤ y := by
    by_contra hnot
    have hy_lt : y < -fmt.maxFiniteMagnitude := lt_of_not_ge hnot
    have hmax :=
      nearestRoundingIn_minimal hround
        fmt.neg_maxFiniteMagnitude_mem_unboundedNormalizedSystem
    have hx_max_nonneg : 0 ≤ x - -fmt.maxFiniteMagnitude :=
      sub_nonneg.mpr hxlo
    have hx_y_nonneg : 0 ≤ x - y :=
      sub_nonneg.mpr (le_trans (le_of_lt hy_lt) hxlo)
    have hdist : |x - -fmt.maxFiniteMagnitude| < |x - y| := by
      rw [abs_of_nonneg hx_max_nonneg, abs_of_nonneg hx_y_nonneg]
      linarith
    exact not_lt_of_ge hmax hdist
  have hy_le_negmin : y ≤ -fmt.minNormalMagnitude := by
    by_contra hnot
    have hmin_lt : -fmt.minNormalMagnitude < y := lt_of_not_ge hnot
    have hmin :=
      nearestRoundingIn_minimal hround
        fmt.neg_minNormalMagnitude_mem_unboundedNormalizedSystem
    have hx_min_nonpos : x - -fmt.minNormalMagnitude ≤ 0 :=
      sub_nonpos.mpr hxhi
    have hx_y_nonpos : x - y ≤ 0 :=
      sub_nonpos.mpr (le_trans hxhi (le_of_lt hmin_lt))
    have hdist : |x - -fmt.minNormalMagnitude| < |x - y| := by
      rw [abs_of_nonpos hx_min_nonpos, abs_of_nonpos hx_y_nonpos]
      linarith
    exact not_lt_of_ge hmin hdist
  have hy_nonpos : y ≤ 0 := by
    have hmin_pos := fmt.minNormalMagnitude_pos
    linarith
  have hyrange : fmt.finiteNormalRange y := by
    constructor
    · rw [abs_of_nonpos hy_nonpos]
      linarith
    · rw [abs_of_nonpos hy_nonpos]
      linarith
  exact Or.inr (Or.inl
    (fmt.unboundedNormalizedSystem_normalizedSystem_of_finiteNormalRange
      (nearestRoundingIn_mem hround) hyrange))

/-- Outputs of the finite nearest-rounding relation are finite values, hence
zero, finite-normal by magnitude, or in the source-facing underflow range. -/
theorem nearestRoundingToFinite_output_zero_or_finiteNormalRange_or_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.nearestRoundingToFinite x y) :
    y = 0 ∨ fmt.finiteNormalRange y ∨ fmt.finiteUnderflowRange y :=
  fmt.finiteSystem_zero_or_finiteNormalRange_or_finiteUnderflowRange
    (nearestRoundingIn_mem h)

/-- A finite nearest-rounded output that lies in the source-facing underflow
range is either zero or subnormal. -/
theorem nearestRoundingToFinite_output_underflow_zero_or_subnormalSystem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.nearestRoundingToFinite x y)
    (hunder : fmt.finiteUnderflowRange y) :
    y = 0 ∨ fmt.subnormalSystem y :=
  (fmt.finiteSystem_finiteUnderflowRange_iff_zero_or_subnormalSystem).mp
    ⟨nearestRoundingIn_mem h, hunder⟩

/-- A nonzero finite nearest-rounded output in the source-facing underflow
range is subnormal. -/
theorem nearestRoundingToFinite_output_underflow_ne_zero_subnormalSystem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.nearestRoundingToFinite x y)
    (hunder : fmt.finiteUnderflowRange y)
    (hy_ne : y ≠ 0) :
    fmt.subnormalSystem y :=
  (fmt.finiteSystem_finiteUnderflowRange_ne_zero_iff_subnormalSystem).mp
    ⟨nearestRoundingIn_mem h, hunder, hy_ne⟩

/-- Outputs of the finite nearest-rounding relation cannot be in the
source-facing overflow range. -/
theorem nearestRoundingToFinite_output_not_finiteOverflowRange
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.nearestRoundingToFinite x y) :
    ¬ fmt.finiteOverflowRange y :=
  fmt.finiteSystem_not_finiteOverflowRange (nearestRoundingIn_mem h)

/-- Outputs of the finite nearest-rounding relation have magnitude bounded by
the largest finite normalized magnitude. -/
theorem nearestRoundingToFinite_output_abs_le_maxFiniteMagnitude
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.nearestRoundingToFinite x y) :
    |y| ≤ fmt.maxFiniteMagnitude :=
  fmt.finiteSystem_abs_le_maxFiniteMagnitude (nearestRoundingIn_mem h)

/-- Positive overflow-range inputs round, under the finite nearest-rounding
relation, to the positive largest finite endpoint.  This is the constructive
existence direction for relation-level saturation. -/
theorem nearestRoundingToFinite_maxFiniteMagnitude_of_gt_maxFiniteMagnitude
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.maxFiniteMagnitude < x) :
    fmt.nearestRoundingToFinite x fmt.maxFiniteMagnitude := by
  refine ⟨fmt.maxFiniteMagnitude_mem_finiteSystem, ?_⟩
  intro z hz
  have hz_abs_le := fmt.finiteSystem_abs_le_maxFiniteMagnitude hz
  have hz_le : z ≤ fmt.maxFiniteMagnitude :=
    le_trans (le_abs_self z) hz_abs_le
  have hx_z : z ≤ x := le_trans hz_le (le_of_lt hx)
  have hxz_nonneg : 0 ≤ x - z := sub_nonneg.mpr hx_z
  have hxM_nonneg : 0 ≤ x - fmt.maxFiniteMagnitude :=
    sub_nonneg.mpr (le_of_lt hx)
  rw [abs_of_nonneg hxM_nonneg, abs_of_nonneg hxz_nonneg]
  linarith

/-- Negative overflow-range inputs round, under the finite nearest-rounding
relation, to the negative largest finite endpoint.  This is the constructive
existence direction for relation-level saturation. -/
theorem nearestRoundingToFinite_neg_maxFiniteMagnitude_of_lt_neg_maxFiniteMagnitude
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : x < -fmt.maxFiniteMagnitude) :
    fmt.nearestRoundingToFinite x (-fmt.maxFiniteMagnitude) := by
  refine ⟨fmt.neg_maxFiniteMagnitude_mem_finiteSystem, ?_⟩
  intro z hz
  have hz_abs_le := fmt.finiteSystem_abs_le_maxFiniteMagnitude hz
  have hnegM_le_z : -fmt.maxFiniteMagnitude ≤ z :=
    le_trans (neg_le_neg hz_abs_le) (neg_abs_le z)
  have hx_z : x ≤ z := le_trans (le_of_lt hx) hnegM_le_z
  have hxz_nonpos : x - z ≤ 0 := sub_nonpos.mpr hx_z
  have hxM_nonpos : x - -fmt.maxFiniteMagnitude ≤ 0 :=
    sub_nonpos.mpr (le_of_lt hx)
  rw [abs_of_nonpos hxM_nonpos, abs_of_nonpos hxz_nonpos]
  linarith

/-- Source-facing finite overflow saturation map.  It picks the signed largest
finite endpoint for inputs whose magnitude exceeds the finite range.  This is
not an IEEE exception model. -/
def finiteOverflowSaturation (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  if x < 0 then -fmt.maxFiniteMagnitude else fmt.maxFiniteMagnitude

/-- IEEE-facing wrapper for the source-facing finite saturation map.  The
result is explicitly finite and flag-free, so this bridge records the current
finite real-valued policy rather than IEEE overflow exception/infinity
semantics. -/
def finiteOverflowSaturationIeeeFiniteResult
    (fmt : FloatingPointFormat) (x : ℝ) : IeeeOperationResult :=
  IeeeOperationResult.finiteNoFlags (fmt.finiteOverflowSaturation x)

theorem finiteOverflowSaturationIeeeFiniteResult_isFinite
    (fmt : FloatingPointFormat) (x : ℝ) :
    (fmt.finiteOverflowSaturationIeeeFiniteResult x).isFinite :=
  IeeeOperationResult.finiteNoFlags_isFinite _

theorem finiteOverflowSaturationIeeeFiniteResult_noFlags
    (fmt : FloatingPointFormat) (x : ℝ) :
    (fmt.finiteOverflowSaturationIeeeFiniteResult x).noFlags :=
  IeeeOperationResult.finiteNoFlags_noFlags _

theorem finiteOverflowSaturationIeeeFiniteResult_not_ieeeOverflowResult
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    ¬ fmt.ieeeOverflowResult mode x
      (fmt.finiteOverflowSaturationIeeeFiniteResult x) := by
  simpa [finiteOverflowSaturationIeeeFiniteResult] using
    (ieeeOverflowResult_not_finiteNoFlags
      (fmt := fmt) (mode := mode) (x := x)
      (y := fmt.finiteOverflowSaturation x))

theorem finiteOverflowSaturationIeeeFiniteResult_toReal?
    (fmt : FloatingPointFormat) (x : ℝ) :
    (fmt.finiteOverflowSaturationIeeeFiniteResult x).value.toReal? =
      some (fmt.finiteOverflowSaturation x) :=
  IeeeOperationResult.finiteNoFlags_toReal? _

/-- Positive overflow inputs saturate to the positive largest finite endpoint
under the source-facing saturation map. -/
theorem finiteOverflowSaturation_eq_maxFiniteMagnitude_of_gt_maxFiniteMagnitude
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.maxFiniteMagnitude < x) :
    fmt.finiteOverflowSaturation x = fmt.maxFiniteMagnitude := by
  have hx_nonneg : ¬ x < 0 := by
    have hM_nonneg := fmt.maxFiniteMagnitude_nonneg
    linarith
  simp [finiteOverflowSaturation, hx_nonneg]

/-- Negative overflow inputs saturate to the negative largest finite endpoint
under the source-facing saturation map. -/
theorem finiteOverflowSaturation_eq_neg_maxFiniteMagnitude_of_lt_neg_maxFiniteMagnitude
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : x < -fmt.maxFiniteMagnitude) :
    fmt.finiteOverflowSaturation x = -fmt.maxFiniteMagnitude := by
  have hx_neg : x < 0 := by
    have hM_nonneg := fmt.maxFiniteMagnitude_nonneg
    linarith
  simp [finiteOverflowSaturation, hx_neg]

/-- For every source-facing overflow-range input, the saturation map is a
finite nearest-rounded value. -/
theorem finiteOverflowSaturation_nearestRoundingToFinite_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteOverflowRange x) :
    fmt.nearestRoundingToFinite x (fmt.finiteOverflowSaturation x) := by
  rcases lt_or_ge x 0 with hneg | hnonneg
  · have hxneg : x < -fmt.maxFiniteMagnitude := by
      rw [finiteOverflowRange, abs_of_neg hneg] at hx
      linarith
    simpa [finiteOverflowSaturation, hneg] using
      fmt.nearestRoundingToFinite_neg_maxFiniteMagnitude_of_lt_neg_maxFiniteMagnitude
        hxneg
  · have hxpos : fmt.maxFiniteMagnitude < x := by
      rw [finiteOverflowRange, abs_of_nonneg hnonneg] at hx
      exact hx
    have hx_not_neg : ¬ x < 0 := not_lt.mpr hnonneg
    simpa [finiteOverflowSaturation, hx_not_neg] using
      fmt.nearestRoundingToFinite_maxFiniteMagnitude_of_gt_maxFiniteMagnitude
        hxpos

/-- Source-facing overflow saturation never increases magnitude on overflow
inputs.  This is the finite-value counterpart of directed toward-zero overflow:
IEEE directed modes that overflow toward infinity are modeled separately by
`ieeeOverflowValue`. -/
theorem finiteOverflowSaturation_abs_le_abs_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteOverflowRange x) :
    |fmt.finiteOverflowSaturation x| ≤ |x| := by
  rcases lt_or_ge x 0 with hneg | hnonneg
  · have hxneg : x < -fmt.maxFiniteMagnitude := by
      rw [finiteOverflowRange, abs_of_neg hneg] at hx
      linarith
    have hMnonneg := fmt.maxFiniteMagnitude_nonneg
    simp [finiteOverflowSaturation, hneg, abs_of_nonneg hMnonneg,
      abs_of_neg hneg]
    linarith
  · have hxpos : fmt.maxFiniteMagnitude < x := by
      rw [finiteOverflowRange, abs_of_nonneg hnonneg] at hx
      exact hx
    have hx_not_neg : ¬ x < 0 := not_lt.mpr hnonneg
    have hMnonneg := fmt.maxFiniteMagnitude_nonneg
    simp [finiteOverflowSaturation, hx_not_neg, abs_of_nonneg hMnonneg,
      abs_of_nonneg hnonneg]
    exact le_of_lt hxpos

theorem finiteOverflowSaturation_neg_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteOverflowRange x) :
    fmt.finiteOverflowSaturation (-x) =
      -fmt.finiteOverflowSaturation x := by
  unfold finiteOverflowSaturation
  by_cases hxneg : x < 0
  · have hnegx_nonneg : ¬ -x < 0 := by linarith
    simp [hxneg, hnegx_nonneg]
  · have hxnonneg : 0 ≤ x := le_of_not_gt hxneg
    have hxpos : 0 < x := by
      have hMnonneg := fmt.maxFiniteMagnitude_nonneg
      have hx' := hx
      rw [finiteOverflowRange, abs_of_nonneg hxnonneg] at hx'
      linarith
    have hnegx_neg : -x < 0 := by linarith
    simp [hxneg, hnegx_neg]

/-- Positive overflow-range inputs round, under the finite nearest-rounding
relation, to the positive largest finite endpoint.  This is relation-level
saturation behavior, not yet a total `fl` function or IEEE exception model. -/
theorem nearestRoundingToFinite_eq_maxFiniteMagnitude_of_gt_maxFiniteMagnitude
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.nearestRoundingToFinite x y)
    (hx : fmt.maxFiniteMagnitude < x) :
    y = fmt.maxFiniteMagnitude := by
  have hy_abs_le :=
    fmt.nearestRoundingToFinite_output_abs_le_maxFiniteMagnitude h
  have hy_le : y ≤ fmt.maxFiniteMagnitude :=
    le_trans (le_abs_self y) hy_abs_le
  have hx_y : y ≤ x := le_trans hy_le (le_of_lt hx)
  have hxy_nonneg : 0 ≤ x - y := sub_nonneg.mpr hx_y
  have hxM_nonneg : 0 ≤ x - fmt.maxFiniteMagnitude :=
    sub_nonneg.mpr (le_of_lt hx)
  have hmin :=
    nearestRoundingIn_minimal h fmt.maxFiniteMagnitude_mem_finiteSystem
  rw [abs_of_nonneg hxy_nonneg, abs_of_nonneg hxM_nonneg] at hmin
  have hM_le_y : fmt.maxFiniteMagnitude ≤ y := by
    linarith
  exact le_antisymm hy_le hM_le_y

/-- Negative overflow-range inputs round, under the finite nearest-rounding
relation, to the negative largest finite endpoint.  This is relation-level
saturation behavior, not yet a total `fl` function or IEEE exception model. -/
theorem nearestRoundingToFinite_eq_neg_maxFiniteMagnitude_of_lt_neg_maxFiniteMagnitude
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.nearestRoundingToFinite x y)
    (hx : x < -fmt.maxFiniteMagnitude) :
    y = -fmt.maxFiniteMagnitude := by
  have hy_abs_le :=
    fmt.nearestRoundingToFinite_output_abs_le_maxFiniteMagnitude h
  have hnegM_le_y : -fmt.maxFiniteMagnitude ≤ y := by
    exact le_trans (neg_le_neg hy_abs_le) (neg_abs_le y)
  have hx_y : x ≤ y := le_trans (le_of_lt hx) hnegM_le_y
  have hxy_nonpos : x - y ≤ 0 := sub_nonpos.mpr hx_y
  have hxM_nonpos : x - -fmt.maxFiniteMagnitude ≤ 0 :=
    sub_nonpos.mpr (le_of_lt hx)
  have hmin :=
    nearestRoundingIn_minimal h fmt.neg_maxFiniteMagnitude_mem_finiteSystem
  rw [abs_of_nonpos hxy_nonpos, abs_of_nonpos hxM_nonpos] at hmin
  have hy_le_negM : y ≤ -fmt.maxFiniteMagnitude := by
    linarith
  exact le_antisymm hy_le_negM hnegM_le_y

/-- In the source-facing overflow range, every finite nearest-rounded value is
the saturation-map value.  Ties do not matter outside the finite interval. -/
theorem nearestRoundingToFinite_eq_finiteOverflowSaturation_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.nearestRoundingToFinite x y)
    (hx : fmt.finiteOverflowRange x) :
    y = fmt.finiteOverflowSaturation x := by
  rcases lt_or_ge x 0 with hneg | hnonneg
  · have hxneg : x < -fmt.maxFiniteMagnitude := by
      rw [finiteOverflowRange, abs_of_neg hneg] at hx
      linarith
    rw [fmt.nearestRoundingToFinite_eq_neg_maxFiniteMagnitude_of_lt_neg_maxFiniteMagnitude
      h hxneg]
    exact Eq.symm
      (fmt.finiteOverflowSaturation_eq_neg_maxFiniteMagnitude_of_lt_neg_maxFiniteMagnitude
        hxneg)
  · have hxpos : fmt.maxFiniteMagnitude < x := by
      rw [finiteOverflowRange, abs_of_nonneg hnonneg] at hx
      exact hx
    rw [fmt.nearestRoundingToFinite_eq_maxFiniteMagnitude_of_gt_maxFiniteMagnitude
      h hxpos]
    exact Eq.symm
      (fmt.finiteOverflowSaturation_eq_maxFiniteMagnitude_of_gt_maxFiniteMagnitude
        hxpos)

/-- If the input is within half the smallest subnormal magnitude of zero, then
zero is a finite nearest-rounded value.  Ties at exactly half spacing remain
relation-valued. -/
theorem nearestRoundingToFinite_zero_of_abs_le_half_minSubnormalMagnitude
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : |x| ≤ (1 / 2 : ℝ) * fmt.minSubnormalMagnitude) :
    fmt.nearestRoundingToFinite x 0 := by
  refine ⟨fmt.finiteSystem_zero, ?_⟩
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    simp
  · have hz_lb :=
      fmt.finiteSystem_ne_zero_abs_ge_minSubnormalMagnitude hz hz0
    have htri0 : |z| ≤ |z - x| + |x| := by
      have h := abs_add_le (z - x) x
      have hzx : z - x + x = z := by ring
      simpa [hzx] using h
    have htri : |z| ≤ |x - z| + |x| := by
      simpa [abs_sub_comm] using htri0
    have hdist : |x| ≤ |x - z| := by
      nlinarith
    simpa using hdist

/-- If the input is strictly within half the smallest subnormal magnitude of
zero, every finite nearest-rounded value is zero. -/
theorem nearestRoundingToFinite_eq_zero_of_abs_lt_half_minSubnormalMagnitude
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.nearestRoundingToFinite x y)
    (hx : |x| < (1 / 2 : ℝ) * fmt.minSubnormalMagnitude) :
    y = 0 := by
  by_contra hy0
  have hy_lb :=
    fmt.finiteSystem_ne_zero_abs_ge_minSubnormalMagnitude
      (nearestRoundingIn_mem h) hy0
  have htri0 : |y| ≤ |y - x| + |x| := by
    have htri := abs_add_le (y - x) x
    have hyx : y - x + x = y := by ring
    simpa [hyx] using htri
  have htri : |y| ≤ |x - y| + |x| := by
    simpa [abs_sub_comm] using htri0
  have hdist_gt : |x| < |x - y| := by
    nlinarith
  have hzero_min :=
    nearestRoundingIn_minimal h fmt.finiteSystem_zero
  have hdist_le : |x - y| ≤ |x| := by
    simpa using hzero_min
  exact not_lt_of_ge hdist_le hdist_gt

/-- First positive subnormal cell: if the first subnormal mantissa exists and
`x` lies between one half and three halves of the smallest subnormal spacing,
then the smallest positive subnormal magnitude is a finite nearest-rounded
value.  This is the first local piece of the remaining underflow selector. -/
theorem nearestRoundingToFinite_minSubnormalMagnitude_of_half_le_of_le_three_halves
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hxlo : (1 / 2 : ℝ) * fmt.minSubnormalMagnitude ≤ x)
    (hxhi : x ≤ (3 / 2 : ℝ) * fmt.minSubnormalMagnitude) :
    fmt.nearestRoundingToFinite x fmt.minSubnormalMagnitude := by
  have hηpos := fmt.minSubnormalMagnitude_pos
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude := le_of_lt hηpos
  have hx_nonneg : 0 ≤ x := by nlinarith
  have hdist_le_x : |x - fmt.minSubnormalMagnitude| ≤ x := by
    rw [abs_le]
    constructor <;> nlinarith
  have hdist_le_half :
      |x - fmt.minSubnormalMagnitude| ≤
        (1 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
    rw [abs_le]
    constructor <;> nlinarith
  have htwo_normal :=
    fmt.two_mul_minSubnormalMagnitude_le_minNormalMagnitude_of_subnormalMantissa_one
      hsub
  refine
    ⟨Or.inr (Or.inr
        (fmt.minSubnormalMagnitude_mem_subnormalSystem_of_subnormalMantissa_one
          hsub)), ?_⟩
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    simpa [abs_of_nonneg hx_nonneg] using hdist_le_x
  rcases hz with hzero | hnorm | hsubz
  · exact False.elim (hz0 hzero)
  · rcases hnorm with ⟨negative, m, e, hm, he, rfl⟩
    cases negative
    · have hz_abs_ge_min :
          fmt.minNormalMagnitude ≤
            |fmt.normalizedValue false m e| :=
        (fmt.normalizedSystem_finiteNormalRange
          ⟨false, m, e, hm, he, rfl⟩).1
      have hz_ge_two :
          2 * fmt.minSubnormalMagnitude ≤
            fmt.normalizedValue false m e := by
        have hpos := fmt.normalizedValue_false_pos (m := m) (e := e) hm
        rw [abs_of_pos hpos] at hz_abs_ge_min
        exact le_trans htwo_normal hz_abs_ge_min
      have hxz_nonpos : x - fmt.normalizedValue false m e ≤ 0 := by
        nlinarith
      rw [abs_of_nonpos hxz_nonpos]
      nlinarith
    · have hz_neg := fmt.normalizedValue_true_neg (m := m) (e := e) hm
      have hxz_nonneg : 0 ≤ x - fmt.normalizedValue true m e := by
        nlinarith
      rw [abs_of_nonneg hxz_nonneg]
      nlinarith
  · rcases hsubz with ⟨negative, m, hm, rfl⟩
    cases negative
    · by_cases hm_one : m = 1
      · subst m
        rw [fmt.subnormalValue_false_one_eq]
        rfl
      · have hm_gt_one : 1 < m :=
          lt_of_le_of_ne (Nat.succ_le_of_lt hm.1) (Ne.symm hm_one)
        have htwo_le_m : (2 : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt hm_gt_one)
        have hz_ge_two :
            2 * fmt.minSubnormalMagnitude ≤ fmt.subnormalValue false m := by
          have hmul :
              2 * fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) ≤
                (m : ℝ) * fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) :=
            mul_le_mul_of_nonneg_right htwo_le_m
              (fmt.betaR_zpow_nonneg (fmt.emin - (fmt.t : ℤ)))
          simpa [subnormalValue, signValue, minSubnormalMagnitude] using hmul
        have hxz_nonpos : x - fmt.subnormalValue false m ≤ 0 := by
          nlinarith
        rw [abs_of_nonpos hxz_nonpos]
        nlinarith
    · have hz_nonpos : fmt.subnormalValue true m ≤ 0 := by
        have hpos :
            0 < (m : ℝ) * fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) :=
          mul_pos (Nat.cast_pos.mpr hm.1)
            (fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ)))
        have hle :
            -((m : ℝ) * fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) ≤ 0 := by
          nlinarith
        simpa [subnormalValue, signValue] using hle
      have hxz_nonneg : 0 ≤ x - fmt.subnormalValue true m := by
        nlinarith
      rw [abs_of_nonneg hxz_nonneg]
      nlinarith

/-- First negative subnormal cell: by sign symmetry, inputs between negative
three halves and negative one half of the smallest subnormal spacing have the
negative smallest subnormal magnitude as a finite nearest-rounded value. -/
theorem nearestRoundingToFinite_neg_minSubnormalMagnitude_of_neg_three_halves_le_of_le_neg_half
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hxlo : -(3 / 2 : ℝ) * fmt.minSubnormalMagnitude ≤ x)
    (hxhi : x ≤ -(1 / 2 : ℝ) * fmt.minSubnormalMagnitude) :
    fmt.nearestRoundingToFinite x (-fmt.minSubnormalMagnitude) := by
  have hposlo : (1 / 2 : ℝ) * fmt.minSubnormalMagnitude ≤ -x := by
    nlinarith
  have hposhi : -x ≤ (3 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
    nlinarith
  have hround :=
    fmt.nearestRoundingToFinite_minSubnormalMagnitude_of_half_le_of_le_three_halves
      hsub hposlo hposhi
  simpa using fmt.nearestRoundingToFinite_neg hround

/-- Positive subnormal grid cell: if `x` lies within half a subnormal spacing
of a positive subnormal value, then that subnormal value is a finite
nearest-rounded value.  Ties at the cell endpoints remain relation-valued. -/
theorem nearestRoundingToFinite_subnormalValue_false_of_half_cell
    {fmt : FloatingPointFormat} {m : ℕ} {x : ℝ}
    (hm : fmt.subnormalMantissa m)
    (hxlo : ((m : ℝ) - (1 / 2 : ℝ)) *
        fmt.minSubnormalMagnitude ≤ x)
    (hxhi : x ≤ ((m : ℝ) + (1 / 2 : ℝ)) *
        fmt.minSubnormalMagnitude) :
    fmt.nearestRoundingToFinite x (fmt.subnormalValue false m) := by
  have hηpos := fmt.minSubnormalMagnitude_pos
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude := le_of_lt hηpos
  have hm_ge_one_nat : 1 ≤ m := Nat.succ_le_of_lt hm.1
  have hm_ge_one : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_ge_one_nat
  have htarget :
      fmt.subnormalValue false m =
        (m : ℝ) * fmt.minSubnormalMagnitude := by
    simp [subnormalValue, signValue, minSubnormalMagnitude]
  have hdist_le_half :
      |x - fmt.subnormalValue false m| ≤
        (1 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
    rw [htarget, abs_le]
    constructor <;> nlinarith
  have hhalf_le_x : (1 / 2 : ℝ) * fmt.minSubnormalMagnitude ≤ x := by
    nlinarith
  have hx_nonneg : 0 ≤ x := by nlinarith
  refine ⟨Or.inr (Or.inr ⟨false, m, hm, rfl⟩), ?_⟩
  intro z hz
  rcases hz with hzero | hnorm | hsubz
  · subst z
    rw [sub_zero, abs_of_nonneg hx_nonneg]
    exact le_trans hdist_le_half hhalf_le_x
  · rcases hnorm with ⟨negative, n, e, hn, he, rfl⟩
    cases negative
    · have hz_abs_ge_min :
          fmt.minNormalMagnitude ≤ |fmt.normalizedValue false n e| :=
        (fmt.normalizedSystem_finiteNormalRange
          ⟨false, n, e, hn, he, rfl⟩).1
      have hz_ge_min :
          fmt.minNormalMagnitude ≤ fmt.normalizedValue false n e := by
        have hpos := fmt.normalizedValue_false_pos (m := n) (e := e) hn
        simpa [abs_of_pos hpos] using hz_abs_ge_min
      have hm_succ_le_min : m + 1 ≤ fmt.minNormalMantissa :=
        Nat.succ_le_of_lt hm.2
      have hm_succ_le_min_real :
          ((m + 1 : ℕ) : ℝ) ≤ (fmt.minNormalMantissa : ℝ) := by
        exact_mod_cast hm_succ_le_min
      have hm_succ_cast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by
        norm_num
      have hnormal_ge_next :
          ((m + 1 : ℕ) : ℝ) *
              fmt.minSubnormalMagnitude ≤ fmt.minNormalMagnitude := by
        have hmul :
            ((m + 1 : ℕ) : ℝ) *
                fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) ≤
              (fmt.minNormalMantissa : ℝ) *
                fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) :=
          mul_le_mul_of_nonneg_right hm_succ_le_min_real
            (fmt.betaR_zpow_nonneg (fmt.emin - (fmt.t : ℤ)))
        rw [fmt.minNormalMantissa_scale_eq fmt.emin] at hmul
        simpa [minSubnormalMagnitude, minNormalMagnitude] using hmul
      have hcell_le_next :
          ((m : ℝ) + (1 / 2 : ℝ)) * fmt.minSubnormalMagnitude ≤
            ((m + 1 : ℕ) : ℝ) * fmt.minSubnormalMagnitude := by
        nlinarith
      have hxz_nonpos : x - fmt.normalizedValue false n e ≤ 0 := by
        nlinarith
      rw [abs_of_nonpos hxz_nonpos]
      have hgap :
          (1 / 2 : ℝ) * fmt.minSubnormalMagnitude ≤
            -(x - fmt.normalizedValue false n e) := by
        nlinarith
      exact le_trans hdist_le_half hgap
    · have hz_neg := fmt.normalizedValue_true_neg (m := n) (e := e) hn
      have hxz_nonneg : 0 ≤ x - fmt.normalizedValue true n e := by
        nlinarith
      rw [abs_of_nonneg hxz_nonneg]
      nlinarith
  · rcases hsubz with ⟨negative, n, hn, rfl⟩
    cases negative
    · by_cases hnm : n = m
      · subst n
        rfl
      · have hlt_or_gt : n < m ∨ m < n := Nat.lt_or_gt_of_ne hnm
        rcases hlt_or_gt with hnm_lt | hm_lt_n
        · have hn_succ_le_m : n + 1 ≤ m := Nat.succ_le_of_lt hnm_lt
          have hn_succ_le_m_real :
              ((n + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
            exact_mod_cast hn_succ_le_m
          have hn_succ_cast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
            norm_num
          have hgap :
              (1 / 2 : ℝ) * fmt.minSubnormalMagnitude ≤
                x - fmt.subnormalValue false n := by
            have hval_n :
                fmt.subnormalValue false n =
                  (n : ℝ) * fmt.minSubnormalMagnitude := by
              simp [subnormalValue, signValue, minSubnormalMagnitude]
            rw [hval_n]
            nlinarith
          have hxz_nonneg : 0 ≤ x - fmt.subnormalValue false n := by
            nlinarith
          rw [abs_of_nonneg hxz_nonneg]
          exact le_trans hdist_le_half hgap
        · have hm_succ_le_n : m + 1 ≤ n := Nat.succ_le_of_lt hm_lt_n
          have hm_succ_le_n_real :
              ((m + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast hm_succ_le_n
          have hm_succ_cast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by
            norm_num
          have hgap :
              (1 / 2 : ℝ) * fmt.minSubnormalMagnitude ≤
                fmt.subnormalValue false n - x := by
            have hval_n :
                fmt.subnormalValue false n =
                  (n : ℝ) * fmt.minSubnormalMagnitude := by
              simp [subnormalValue, signValue, minSubnormalMagnitude]
            rw [hval_n]
            nlinarith
          have hxz_nonpos : x - fmt.subnormalValue false n ≤ 0 := by
            nlinarith
          rw [abs_of_nonpos hxz_nonpos]
          have hgap' :
              (1 / 2 : ℝ) * fmt.minSubnormalMagnitude ≤
                -(x - fmt.subnormalValue false n) := by
            nlinarith
          exact le_trans hdist_le_half hgap'
    · have hz_nonpos : fmt.subnormalValue true n ≤ 0 := by
        have hpos :
            0 < (n : ℝ) * fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) :=
          mul_pos (Nat.cast_pos.mpr hn.1)
            (fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ)))
        have hle :
            -((n : ℝ) * fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) ≤ 0 := by
          nlinarith
        simpa [subnormalValue, signValue] using hle
      have hxz_nonneg : 0 ≤ x - fmt.subnormalValue true n := by
        nlinarith
      rw [abs_of_nonneg hxz_nonneg]
      nlinarith

/-- Positive subnormal half-cell absolute-error bound: if `x` lies within
half a subnormal spacing of a positive subnormal value, the absolute error to
that value is at most half a subnormal spacing. -/
theorem absError_subnormalValue_false_le_half_minSubnormalMagnitude_of_half_cell
    {fmt : FloatingPointFormat} {m : ℕ} {x : ℝ}
    (_hm : fmt.subnormalMantissa m)
    (hxlo : ((m : ℝ) - (1 / 2 : ℝ)) *
        fmt.minSubnormalMagnitude ≤ x)
    (hxhi : x ≤ ((m : ℝ) + (1 / 2 : ℝ)) *
        fmt.minSubnormalMagnitude) :
    absError (fmt.subnormalValue false m) x ≤
      (1 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude :=
    le_of_lt fmt.minSubnormalMagnitude_pos
  have htarget :
      fmt.subnormalValue false m =
        (m : ℝ) * fmt.minSubnormalMagnitude := by
    simp [subnormalValue, signValue, minSubnormalMagnitude]
  rw [absError, htarget]
  rw [abs_le]
  constructor <;> nlinarith

/-- Negative subnormal grid cell, obtained from the positive cell by finite
nearest-rounding sign symmetry. -/
theorem nearestRoundingToFinite_subnormalValue_true_of_half_cell
    {fmt : FloatingPointFormat} {m : ℕ} {x : ℝ}
    (hm : fmt.subnormalMantissa m)
    (hxlo : -(((m : ℝ) + (1 / 2 : ℝ)) *
        fmt.minSubnormalMagnitude) ≤ x)
    (hxhi : x ≤ -(((m : ℝ) - (1 / 2 : ℝ)) *
        fmt.minSubnormalMagnitude)) :
    fmt.nearestRoundingToFinite x (fmt.subnormalValue true m) := by
  have hposlo :
      ((m : ℝ) - (1 / 2 : ℝ)) *
          fmt.minSubnormalMagnitude ≤ -x := by
    nlinarith
  have hposhi :
      -x ≤ ((m : ℝ) + (1 / 2 : ℝ)) *
          fmt.minSubnormalMagnitude := by
    nlinarith
  have hround :=
    fmt.nearestRoundingToFinite_subnormalValue_false_of_half_cell
      hm hposlo hposhi
  have hneg := fmt.nearestRoundingToFinite_neg hround
  have hsign := fmt.subnormalValue_not_eq_neg false m
  rw [← hsign] at hneg
  simpa using hneg

/-- The smallest normal magnitude is exactly `minNormalMantissa` subnormal
spacings from zero. -/
theorem minNormalMagnitude_eq_minNormalMantissa_mul_minSubnormalMagnitude
    (fmt : FloatingPointFormat) :
    fmt.minNormalMagnitude =
      (fmt.minNormalMantissa : ℝ) * fmt.minSubnormalMagnitude := by
  simpa [minNormalMagnitude, minSubnormalMagnitude] using
    (fmt.minNormalMantissa_scale_eq fmt.emin).symm

/-- Positive subnormal/normal boundary cell: inputs in the top half subnormal
spacing below the smallest normal magnitude have the smallest normal magnitude
as a finite nearest-rounded value.  The endpoint tie remains relation-valued. -/
theorem nearestRoundingToFinite_minNormalMagnitude_of_subnormal_boundary_half_le
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxlo : ((fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ)) *
        fmt.minSubnormalMagnitude ≤ x)
    (hxhi : x ≤ fmt.minNormalMagnitude) :
    fmt.nearestRoundingToFinite x fmt.minNormalMagnitude := by
  have hηpos := fmt.minSubnormalMagnitude_pos
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude := le_of_lt hηpos
  have hMpos_nat : 0 < fmt.minNormalMantissa := fmt.minNormalMantissa_pos
  have hMge_one_nat : 1 ≤ fmt.minNormalMantissa :=
    Nat.succ_le_of_lt hMpos_nat
  have hMge_one : (1 : ℝ) ≤ (fmt.minNormalMantissa : ℝ) := by
    exact_mod_cast hMge_one_nat
  have htarget :
      fmt.minNormalMagnitude =
        (fmt.minNormalMantissa : ℝ) * fmt.minSubnormalMagnitude :=
    fmt.minNormalMagnitude_eq_minNormalMantissa_mul_minSubnormalMagnitude
  have hhalf_le_x : (1 / 2 : ℝ) * fmt.minSubnormalMagnitude ≤ x := by
    rw [htarget] at hxhi
    nlinarith
  have hx_nonneg : 0 ≤ x := by nlinarith
  have hdist_le_half :
      |x - fmt.minNormalMagnitude| ≤
        (1 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
    rw [htarget, abs_le]
    constructor <;> nlinarith
  refine ⟨fmt.minNormalMagnitude_mem_finiteSystem, ?_⟩
  intro z hz
  rcases hz with hzero | hnorm | hsubz
  · subst z
    rw [sub_zero, abs_of_nonneg hx_nonneg]
    exact le_trans hdist_le_half hhalf_le_x
  · rcases hnorm with ⟨negative, m, e, hm, he, rfl⟩
    cases negative
    · have hz_abs_ge_min :
          fmt.minNormalMagnitude ≤
            |fmt.normalizedValue false m e| :=
        (fmt.normalizedSystem_finiteNormalRange
          ⟨false, m, e, hm, he, rfl⟩).1
      have hz_ge_min :
          fmt.minNormalMagnitude ≤ fmt.normalizedValue false m e := by
        have hpos := fmt.normalizedValue_false_pos (m := m) (e := e) hm
        simpa [abs_of_pos hpos] using hz_abs_ge_min
      have hxz_nonpos : x - fmt.normalizedValue false m e ≤ 0 := by
        nlinarith
      rw [abs_of_nonpos hxz_nonpos]
      have hx_target_nonpos : x - fmt.minNormalMagnitude ≤ 0 :=
        sub_nonpos.mpr hxhi
      rw [abs_of_nonpos hx_target_nonpos]
      nlinarith
    · have hz_neg := fmt.normalizedValue_true_neg (m := m) (e := e) hm
      have hxz_nonneg : 0 ≤ x - fmt.normalizedValue true m e := by
        nlinarith
      rw [abs_of_nonneg hxz_nonneg]
      exact le_trans hdist_le_half (le_trans hhalf_le_x (by nlinarith))
  · rcases hsubz with ⟨negative, m, hm, rfl⟩
    cases negative
    · have hm_le_last : m ≤ fmt.minNormalMantissa - 1 :=
        Nat.le_sub_one_of_lt hm.2
      have hm_le_last_real :
          (m : ℝ) ≤ (fmt.minNormalMantissa - 1 : ℕ) := by
        exact_mod_cast hm_le_last
      have hlast_cast :
          ((fmt.minNormalMantissa - 1 : ℕ) : ℝ) =
            (fmt.minNormalMantissa : ℝ) - 1 := by
        rw [Nat.cast_sub hMge_one_nat, Nat.cast_one]
      have hz_le_last :
          fmt.subnormalValue false m ≤
            ((fmt.minNormalMantissa : ℝ) - 1) *
              fmt.minSubnormalMagnitude := by
        have hmul :
            (m : ℝ) * fmt.minSubnormalMagnitude ≤
              ((fmt.minNormalMantissa - 1 : ℕ) : ℝ) *
                fmt.minSubnormalMagnitude :=
          mul_le_mul_of_nonneg_right hm_le_last_real hηnonneg
        simpa [subnormalValue, signValue, minSubnormalMagnitude, hlast_cast]
          using hmul
      have hxz_nonneg : 0 ≤ x - fmt.subnormalValue false m := by
        nlinarith
      rw [abs_of_nonneg hxz_nonneg]
      have hgap :
          (1 / 2 : ℝ) * fmt.minSubnormalMagnitude ≤
            x - fmt.subnormalValue false m := by
        nlinarith
      exact le_trans hdist_le_half hgap
    · have hz_nonpos : fmt.subnormalValue true m ≤ 0 := by
        have hpos :
            0 < (m : ℝ) * fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) :=
          mul_pos (Nat.cast_pos.mpr hm.1)
            (fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ)))
        have hle :
            -((m : ℝ) * fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) ≤ 0 := by
          nlinarith
        simpa [subnormalValue, signValue] using hle
      have hxz_nonneg : 0 ≤ x - fmt.subnormalValue true m := by
        nlinarith
      rw [abs_of_nonneg hxz_nonneg]
      exact le_trans hdist_le_half (le_trans hhalf_le_x (by nlinarith))

/-- Positive subnormal/normal boundary-cell absolute-error bound: if `x` is in
the top half subnormal spacing below the smallest normal value, the absolute
error to the smallest normal value is at most half a subnormal spacing. -/
theorem absError_minNormalMagnitude_le_half_minSubnormalMagnitude_of_boundary_half_cell
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxlo : ((fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ)) *
        fmt.minSubnormalMagnitude ≤ x)
    (hxhi : x ≤ fmt.minNormalMagnitude) :
    absError fmt.minNormalMagnitude x ≤
      (1 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude :=
    le_of_lt fmt.minSubnormalMagnitude_pos
  have htarget :=
    fmt.minNormalMagnitude_eq_minNormalMantissa_mul_minSubnormalMagnitude
  rw [absError, htarget]
  rw [abs_le]
  constructor <;> nlinarith

/-- Negative subnormal/normal boundary cell, obtained from the positive
boundary cell by finite nearest-rounding sign symmetry. -/
theorem nearestRoundingToFinite_neg_minNormalMagnitude_of_subnormal_boundary_half_le
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxlo : -fmt.minNormalMagnitude ≤ x)
    (hxhi : x ≤ -(((fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ)) *
        fmt.minSubnormalMagnitude)) :
    fmt.nearestRoundingToFinite x (-fmt.minNormalMagnitude) := by
  have hposlo :
      ((fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ)) *
          fmt.minSubnormalMagnitude ≤ -x := by
    nlinarith
  have hposhi : -x ≤ fmt.minNormalMagnitude := by
    nlinarith
  have hround :=
    fmt.nearestRoundingToFinite_minNormalMagnitude_of_subnormal_boundary_half_le
      hposlo hposhi
  simpa using fmt.nearestRoundingToFinite_neg hround

/-- Positive middle subnormal underflow existence: away from the zero cell and
the smallest-normal boundary cell, a positive underflow input lies in one of
the proved positive subnormal half-cells. -/
theorem exists_nearestRoundingToFinite_positive_subnormal_middle
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxlo : (1 / 2 : ℝ) * fmt.minSubnormalMagnitude < x)
    (hxhi : x < ((fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ)) *
        fmt.minSubnormalMagnitude) :
    ∃ y : ℝ, fmt.nearestRoundingToFinite x y := by
  have hηpos := fmt.minSubnormalMagnitude_pos
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude := le_of_lt hηpos
  let q : ℝ := x / fmt.minSubnormalMagnitude
  have hqlo : (1 / 2 : ℝ) < q := by
    dsimp [q]
    rw [lt_div_iff₀ hηpos]
    simpa [mul_comm] using hxlo
  have hqhi : q < (fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ) := by
    dsimp [q]
    rw [div_lt_iff₀ hηpos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hxhi
  rcases exists_nat_half_cell_of_half_lt_of_lt_sub_half
      (M := fmt.minNormalMantissa) hqlo hqhi with
    ⟨m, hmpos, hmlt, hcelllo, hcellhi⟩
  have hq_mul : q * fmt.minSubnormalMagnitude = x := by
    dsimp [q]
    exact div_mul_cancel₀ x (ne_of_gt hηpos)
  have hxlo_cell :
      ((m : ℝ) - (1 / 2 : ℝ)) *
          fmt.minSubnormalMagnitude ≤ x := by
    have hmul :=
      mul_le_mul_of_nonneg_right hcelllo hηnonneg
    rw [hq_mul] at hmul
    exact hmul
  have hxhi_cell :
      x ≤ ((m : ℝ) + (1 / 2 : ℝ)) *
          fmt.minSubnormalMagnitude := by
    have hmul :=
      mul_le_mul_of_nonneg_right hcellhi hηnonneg
    rw [hq_mul] at hmul
    exact hmul
  exact
    ⟨fmt.subnormalValue false m,
      fmt.nearestRoundingToFinite_subnormalValue_false_of_half_cell
        ⟨hmpos, hmlt⟩ hxlo_cell hxhi_cell⟩

/-- Nonnegative finite-underflow inputs have at least one finite nearest-rounded
value.  The proof splits the underflow band into the zero cell, subnormal
half-cells, and the smallest-normal boundary cell. -/
theorem exists_nearestRoundingToFinite_nonneg_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxnonneg : 0 ≤ x)
    (hunder : fmt.finiteUnderflowRange x) :
    ∃ y : ℝ, fmt.nearestRoundingToFinite x y := by
  have hx_lt_min : x < fmt.minNormalMagnitude := by
    simpa [finiteUnderflowRange, abs_of_nonneg hxnonneg] using hunder
  have hx_le_min : x ≤ fmt.minNormalMagnitude := le_of_lt hx_lt_min
  by_cases hzero :
      x ≤ (1 / 2 : ℝ) * fmt.minSubnormalMagnitude
  · exact
      ⟨0, fmt.nearestRoundingToFinite_zero_of_abs_le_half_minSubnormalMagnitude
        (by simpa [abs_of_nonneg hxnonneg] using hzero)⟩
  · have hx_gt_half :
        (1 / 2 : ℝ) * fmt.minSubnormalMagnitude < x :=
      lt_of_not_ge hzero
    by_cases hboundary :
        ((fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ)) *
            fmt.minSubnormalMagnitude ≤ x
    · exact
        ⟨fmt.minNormalMagnitude,
          fmt.nearestRoundingToFinite_minNormalMagnitude_of_subnormal_boundary_half_le
            hboundary hx_le_min⟩
    · have hx_lt_boundary :
          x < ((fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ)) *
              fmt.minSubnormalMagnitude :=
        lt_of_not_ge hboundary
      exact
        fmt.exists_nearestRoundingToFinite_positive_subnormal_middle
          hx_gt_half hx_lt_boundary

/-- Nonnegative finite-underflow inputs have a finite candidate within half a
subnormal spacing.  This is the absolute-error substrate for Higham's gradual
underflow additive term. -/
theorem exists_finiteSystem_absError_le_half_minSubnormalMagnitude_nonneg_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxnonneg : 0 ≤ x)
    (hunder : fmt.finiteUnderflowRange x) :
    ∃ y : ℝ,
      fmt.finiteSystem y ∧
        absError y x ≤ (1 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
  have hx_lt_min : x < fmt.minNormalMagnitude := by
    simpa [finiteUnderflowRange, abs_of_nonneg hxnonneg] using hunder
  have hx_le_min : x ≤ fmt.minNormalMagnitude := le_of_lt hx_lt_min
  by_cases hzero :
      x ≤ (1 / 2 : ℝ) * fmt.minSubnormalMagnitude
  · exact
      ⟨0, fmt.finiteSystem_zero,
        by simpa [absError, abs_of_nonneg hxnonneg] using hzero⟩
  · have hx_gt_half :
        (1 / 2 : ℝ) * fmt.minSubnormalMagnitude < x :=
      lt_of_not_ge hzero
    by_cases hboundary :
        ((fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ)) *
            fmt.minSubnormalMagnitude ≤ x
    · exact
        ⟨fmt.minNormalMagnitude, fmt.minNormalMagnitude_mem_finiteSystem,
          fmt.absError_minNormalMagnitude_le_half_minSubnormalMagnitude_of_boundary_half_cell
            hboundary hx_le_min⟩
    · have hx_lt_boundary :
          x < ((fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ)) *
              fmt.minSubnormalMagnitude :=
        lt_of_not_ge hboundary
      have hηpos := fmt.minSubnormalMagnitude_pos
      have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude := le_of_lt hηpos
      let q : ℝ := x / fmt.minSubnormalMagnitude
      have hqlo : (1 / 2 : ℝ) < q := by
        dsimp [q]
        rw [lt_div_iff₀ hηpos]
        simpa [mul_comm] using hx_gt_half
      have hqhi : q < (fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ) := by
        dsimp [q]
        rw [div_lt_iff₀ hηpos]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hx_lt_boundary
      rcases exists_nat_half_cell_of_half_lt_of_lt_sub_half
          (M := fmt.minNormalMantissa) hqlo hqhi with
        ⟨m, hmpos, hmlt, hcelllo, hcellhi⟩
      have hq_mul : q * fmt.minSubnormalMagnitude = x := by
        dsimp [q]
        exact div_mul_cancel₀ x (ne_of_gt hηpos)
      have hxlo_cell :
          ((m : ℝ) - (1 / 2 : ℝ)) *
              fmt.minSubnormalMagnitude ≤ x := by
        have hmul :=
          mul_le_mul_of_nonneg_right hcelllo hηnonneg
        rw [hq_mul] at hmul
        exact hmul
      have hxhi_cell :
          x ≤ ((m : ℝ) + (1 / 2 : ℝ)) *
              fmt.minSubnormalMagnitude := by
        have hmul :=
          mul_le_mul_of_nonneg_right hcellhi hηnonneg
        rw [hq_mul] at hmul
        exact hmul
      exact
        ⟨fmt.subnormalValue false m,
          Or.inr (Or.inr ⟨false, m, ⟨hmpos, hmlt⟩, rfl⟩),
          fmt.absError_subnormalValue_false_le_half_minSubnormalMagnitude_of_half_cell
            ⟨hmpos, hmlt⟩ hxlo_cell hxhi_cell⟩

/-- Nonpositive finite-underflow inputs have at least one finite nearest-rounded
value, by sign symmetry from the nonnegative underflow theorem. -/
theorem exists_nearestRoundingToFinite_nonpos_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxnonpos : x ≤ 0)
    (hunder : fmt.finiteUnderflowRange x) :
    ∃ y : ℝ, fmt.nearestRoundingToFinite x y := by
  have hneg_nonneg : 0 ≤ -x := by linarith
  have hunder_neg : fmt.finiteUnderflowRange (-x) := by
    simpa [finiteUnderflowRange, abs_neg] using hunder
  rcases fmt.exists_nearestRoundingToFinite_nonneg_finiteUnderflowRange
      hneg_nonneg hunder_neg with ⟨y, hround⟩
  exact ⟨-y, by simpa using fmt.nearestRoundingToFinite_neg hround⟩

/-- Every source-facing finite-underflow input has at least one finite
nearest-rounded value.  This is relation-level gradual-underflow existence; it
does not choose a unique tie result or model IEEE underflow exceptions. -/
theorem exists_nearestRoundingToFinite_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    ∃ y : ℝ, fmt.nearestRoundingToFinite x y := by
  by_cases hxnonneg : 0 ≤ x
  · exact
      fmt.exists_nearestRoundingToFinite_nonneg_finiteUnderflowRange
        hxnonneg hunder
  · have hxnonpos : x ≤ 0 := le_of_lt (lt_of_not_ge hxnonneg)
    exact
      fmt.exists_nearestRoundingToFinite_nonpos_finiteUnderflowRange
        hxnonpos hunder

/-- Every finite-underflow input has a finite candidate within half a subnormal
spacing. -/
theorem exists_finiteSystem_absError_le_half_minSubnormalMagnitude_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    ∃ y : ℝ,
      fmt.finiteSystem y ∧
        absError y x ≤ (1 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
  by_cases hxnonneg : 0 ≤ x
  · exact
      fmt.exists_finiteSystem_absError_le_half_minSubnormalMagnitude_nonneg_finiteUnderflowRange
        hxnonneg hunder
  · have hxnonpos : x ≤ 0 := le_of_lt (lt_of_not_ge hxnonneg)
    have hneg_nonneg : 0 ≤ -x := by linarith
    have hunder_neg : fmt.finiteUnderflowRange (-x) := by
      simpa [finiteUnderflowRange, abs_neg] using hunder
    rcases
      fmt.exists_finiteSystem_absError_le_half_minSubnormalMagnitude_nonneg_finiteUnderflowRange
        hneg_nonneg hunder_neg with
      ⟨y, hy, hdist⟩
    refine ⟨-y, fmt.finiteSystem_neg hy, ?_⟩
    have heq : absError (-y) x = absError y (-x) := by
      unfold absError
      have harg : -y - x = -(y - -x) := by ring
      rw [harg, abs_neg]
    simpa [heq] using hdist

/-- No finite candidate is exactly half a subnormal spacing from the source.
This is the visible side condition needed to upgrade Higham's gradual-underflow
additive bound from non-strict `≤` to strict `<`; exact half-cell ties are
intentionally not hidden. -/
def finiteUnderflowNoHalfTie (fmt : FloatingPointFormat) (x : ℝ) : Prop :=
  ∀ y : ℝ, fmt.finiteSystem y →
    absError y x ≠ fmt.gradualUnderflowEtaBound

/-- Any finite nearest-rounded output for a finite-underflow input is within
Higham's gradual-underflow additive-error bound `u * alpha`, equivalently half
a subnormal spacing. -/
theorem nearestRoundingToFinite_absError_le_gradualUnderflowEtaBound_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hround : fmt.nearestRoundingToFinite x y)
    (hunder : fmt.finiteUnderflowRange x) :
    absError y x ≤ fmt.gradualUnderflowEtaBound := by
  rcases
    fmt.exists_finiteSystem_absError_le_half_minSubnormalMagnitude_finiteUnderflowRange
      hunder with
    ⟨z, hz, hdist_z⟩
  have hmin : |x - y| ≤ |x - z| :=
    nearestRoundingIn_minimal hround hz
  have hdist_y : absError y x ≤ absError z x := by
    simpa [absError, abs_sub_comm] using hmin
  exact le_trans hdist_y
    (by
      simpa [fmt.gradualUnderflowEtaBound_eq_half_minSubnormalMagnitude]
        using hdist_z)

/-- Strict variant of the gradual-underflow additive-error bound away from
exact half-cell ties. -/
theorem nearestRoundingToFinite_absError_lt_gradualUnderflowEtaBound_of_finiteUnderflowRange_of_noHalfTie
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hround : fmt.nearestRoundingToFinite x y)
    (hunder : fmt.finiteUnderflowRange x)
    (hnotie : fmt.finiteUnderflowNoHalfTie x) :
    absError y x < fmt.gradualUnderflowEtaBound := by
  have hle :=
    fmt.nearestRoundingToFinite_absError_le_gradualUnderflowEtaBound_of_finiteUnderflowRange
      hround hunder
  exact lt_of_le_of_ne hle (hnotie y (nearestRoundingIn_mem hround))

/-- Source-style round-away selector for nonnegative finite-underflow inputs.
It rounds by the subnormal lattice coordinate `x / eta`, where
`eta = minSubnormalMagnitude`, choosing the larger-magnitude endpoint at exact
halfway ties.  This is still only a finite-value selector, not an IEEE
underflow/exception semantics. -/
def finiteUnderflowRoundAwayNonneg (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  let q : ℝ := x / fmt.minSubnormalMagnitude
  let m : ℕ := Nat.floor (q + (1 / 2 : ℝ))
  if m = 0 then
    0
  else if fmt.minNormalMantissa ≤ m then
    fmt.minNormalMagnitude
  else
    fmt.subnormalValue false m

theorem finiteUnderflowRoundAwayNonneg_nearestRoundingToFinite
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxnonneg : 0 ≤ x)
    (hunder : fmt.finiteUnderflowRange x) :
    fmt.nearestRoundingToFinite x
      (fmt.finiteUnderflowRoundAwayNonneg x) := by
  let q : ℝ := x / fmt.minSubnormalMagnitude
  let m : ℕ := Nat.floor (q + (1 / 2 : ℝ))
  have hηpos := fmt.minSubnormalMagnitude_pos
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude := le_of_lt hηpos
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hxnonneg hηnonneg
  have hr_nonneg : 0 ≤ q + (1 / 2 : ℝ) := by
    nlinarith
  have hx_lt_min : x < fmt.minNormalMagnitude := by
    simpa [finiteUnderflowRange, abs_of_nonneg hxnonneg] using hunder
  have hx_le_min : x ≤ fmt.minNormalMagnitude := le_of_lt hx_lt_min
  have hq_lt_M : q < (fmt.minNormalMantissa : ℝ) := by
    have htarget :=
      fmt.minNormalMagnitude_eq_minNormalMantissa_mul_minSubnormalMagnitude
    dsimp [q]
    rw [div_lt_iff₀ hηpos]
    simpa [htarget, mul_comm] using hx_lt_min
  have hfloor_le : (m : ℝ) ≤ q + (1 / 2 : ℝ) :=
    Nat.floor_le hr_nonneg
  have hfloor_succ : q + (1 / 2 : ℝ) < (m + 1 : ℕ) := by
    simpa [m] using Nat.lt_floor_add_one (q + (1 / 2 : ℝ))
  change
    fmt.nearestRoundingToFinite x
      (if m = 0 then 0
        else if fmt.minNormalMantissa ≤ m then fmt.minNormalMagnitude
        else fmt.subnormalValue false m)
  by_cases hm0 : m = 0
  · simp [hm0]
    have hq_lt_half : q < (1 / 2 : ℝ) := by
      have hs : q + (1 / 2 : ℝ) < (1 : ℝ) := by
        simpa [hm0] using hfloor_succ
      linarith
    have hx_lt_half : x < (1 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
      dsimp [q] at hq_lt_half
      rw [div_lt_iff₀ hηpos] at hq_lt_half
      simpa [mul_comm] using hq_lt_half
    exact
      fmt.nearestRoundingToFinite_zero_of_abs_le_half_minSubnormalMagnitude
        (by
          rw [abs_of_nonneg hxnonneg]
          exact le_of_lt hx_lt_half)
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    by_cases htop : fmt.minNormalMantissa ≤ m
    · simp [hm0, htop]
      have hM_le_r :
          (fmt.minNormalMantissa : ℝ) ≤ q + (1 / 2 : ℝ) := by
        exact le_trans (by exact_mod_cast htop) hfloor_le
      have hqlo :
          (fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ) ≤ q := by
        linarith
      have hxlo :
          ((fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ)) *
              fmt.minSubnormalMagnitude ≤ x := by
        have hmul := mul_le_mul_of_nonneg_right hqlo hηnonneg
        dsimp [q] at hmul
        rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
        exact hmul
      exact
        fmt.nearestRoundingToFinite_minNormalMagnitude_of_subnormal_boundary_half_le
          hxlo hx_le_min
    · simp [hm0, htop]
      have hmlt : m < fmt.minNormalMantissa := lt_of_not_ge htop
      have hm : fmt.subnormalMantissa m := ⟨hmpos, hmlt⟩
      have hqlo : (m : ℝ) - (1 / 2 : ℝ) ≤ q := by
        linarith
      have hfloor_succ' : q + (1 / 2 : ℝ) < (m : ℝ) + 1 := by
        simpa [Nat.cast_add, Nat.cast_one] using hfloor_succ
      have hqhi : q ≤ (m : ℝ) + (1 / 2 : ℝ) := by
        linarith
      have hxlo :
          ((m : ℝ) - (1 / 2 : ℝ)) *
              fmt.minSubnormalMagnitude ≤ x := by
        have hmul := mul_le_mul_of_nonneg_right hqlo hηnonneg
        dsimp [q] at hmul
        rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
        exact hmul
      have hxhi :
          x ≤ ((m : ℝ) + (1 / 2 : ℝ)) *
              fmt.minSubnormalMagnitude := by
        have hmul := mul_le_mul_of_nonneg_right hqhi hηnonneg
        dsimp [q] at hmul
        rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
        exact hmul
      exact
        fmt.nearestRoundingToFinite_subnormalValue_false_of_half_cell
          hm hxlo hxhi

/-- Source-style round-away selector for finite-underflow inputs, obtained from
the nonnegative selector by sign symmetry. -/
def finiteUnderflowRoundAway (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  if 0 ≤ x then
    fmt.finiteUnderflowRoundAwayNonneg x
  else
    -fmt.finiteUnderflowRoundAwayNonneg (-x)

theorem finiteUnderflowRoundAway_nearestRoundingToFinite
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    fmt.nearestRoundingToFinite x (fmt.finiteUnderflowRoundAway x) := by
  unfold finiteUnderflowRoundAway
  by_cases hxnonneg : 0 ≤ x
  · simp [hxnonneg]
    exact
      fmt.finiteUnderflowRoundAwayNonneg_nearestRoundingToFinite
        hxnonneg hunder
  · simp [hxnonneg]
    have hxneg_nonneg : 0 ≤ -x := by linarith
    have hunder_neg : fmt.finiteUnderflowRange (-x) := by
      simpa [finiteUnderflowRange, abs_neg] using hunder
    have hround :=
      fmt.finiteUnderflowRoundAwayNonneg_nearestRoundingToFinite
        hxneg_nonneg hunder_neg
    simpa using fmt.nearestRoundingToFinite_neg hround

/-- Source-style round-to-even selector for nonnegative finite-underflow
inputs.  It rounds by the subnormal lattice coordinate `x / eta`, where
`eta = minSubnormalMagnitude`, and breaks exact half-spacing ties by the lower
lattice index parity.  The index `0` denotes zero, positive indices below
`minNormalMantissa` denote subnormals, and `minNormalMantissa` denotes the
smallest normal value. -/
def finiteUnderflowRoundToEvenNonneg (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  let q : ℝ := x / fmt.minSubnormalMagnitude
  let m : ℕ := Nat.floor q
  let midpoint : ℝ := (m : ℝ) + (1 / 2 : ℝ)
  if q < midpoint then
    if m = 0 then 0 else fmt.subnormalValue false m
  else if midpoint < q then
    if fmt.minNormalMantissa ≤ m + 1 then
      fmt.minNormalMagnitude
    else
      fmt.subnormalValue false (m + 1)
  else if evenMantissa m then
    if m = 0 then 0 else fmt.subnormalValue false m
  else if fmt.minNormalMantissa ≤ m + 1 then
    fmt.minNormalMagnitude
  else
    fmt.subnormalValue false (m + 1)

theorem finiteUnderflowRoundToEvenNonneg_zero
    (fmt : FloatingPointFormat) :
    fmt.finiteUnderflowRoundToEvenNonneg 0 = 0 := by
  unfold finiteUnderflowRoundToEvenNonneg
  simp

theorem finiteUnderflowRoundToEvenNonneg_nearestRoundingToFinite
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxnonneg : 0 ≤ x)
    (hunder : fmt.finiteUnderflowRange x) :
    fmt.nearestRoundingToFinite x
      (fmt.finiteUnderflowRoundToEvenNonneg x) := by
  let q : ℝ := x / fmt.minSubnormalMagnitude
  let m : ℕ := Nat.floor q
  let midpoint : ℝ := (m : ℝ) + (1 / 2 : ℝ)
  have hηpos := fmt.minSubnormalMagnitude_pos
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude := le_of_lt hηpos
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hxnonneg hηnonneg
  have hx_lt_min : x < fmt.minNormalMagnitude := by
    simpa [finiteUnderflowRange, abs_of_nonneg hxnonneg] using hunder
  have hx_le_min : x ≤ fmt.minNormalMagnitude := le_of_lt hx_lt_min
  have hq_lt_M : q < (fmt.minNormalMantissa : ℝ) := by
    have htarget :=
      fmt.minNormalMagnitude_eq_minNormalMantissa_mul_minSubnormalMagnitude
    dsimp [q]
    rw [div_lt_iff₀ hηpos]
    simpa [htarget, mul_comm] using hx_lt_min
  have hfloor_le : (m : ℝ) ≤ q := Nat.floor_le hq_nonneg
  have hfloor_succ : q < (m + 1 : ℕ) := by
    simpa [m] using Nat.lt_floor_add_one q
  have hm_lt_M : m < fmt.minNormalMantissa :=
    Nat.cast_lt.mp (lt_of_le_of_lt hfloor_le hq_lt_M)
  have hsucc_le_M : m + 1 ≤ fmt.minNormalMantissa :=
    Nat.succ_le_iff.mpr hm_lt_M
  change
    fmt.nearestRoundingToFinite x
      (if q < midpoint then
        if m = 0 then 0 else fmt.subnormalValue false m
      else if midpoint < q then
        if fmt.minNormalMantissa ≤ m + 1 then
          fmt.minNormalMagnitude
        else
          fmt.subnormalValue false (m + 1)
      else if evenMantissa m then
        if m = 0 then 0 else fmt.subnormalValue false m
      else if fmt.minNormalMantissa ≤ m + 1 then
        fmt.minNormalMagnitude
      else
        fmt.subnormalValue false (m + 1))
  by_cases hleft : q < midpoint
  · simp [hleft]
    by_cases hm0 : m = 0
    · simp [hm0]
      have hq_lt_half : q < (1 / 2 : ℝ) := by
        simpa [midpoint, hm0] using hleft
      have hx_lt_half : x < (1 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
        dsimp [q] at hq_lt_half
        rw [div_lt_iff₀ hηpos] at hq_lt_half
        simpa [mul_comm] using hq_lt_half
      exact
        fmt.nearestRoundingToFinite_zero_of_abs_le_half_minSubnormalMagnitude
          (by
            rw [abs_of_nonneg hxnonneg]
            exact le_of_lt hx_lt_half)
    · simp [hm0]
      have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      have hm : fmt.subnormalMantissa m := ⟨hmpos, hm_lt_M⟩
      have hqlo : (m : ℝ) - (1 / 2 : ℝ) ≤ q := by
        linarith
      have hqhi : q ≤ (m : ℝ) + (1 / 2 : ℝ) := le_of_lt hleft
      have hxlo :
          ((m : ℝ) - (1 / 2 : ℝ)) *
              fmt.minSubnormalMagnitude ≤ x := by
        have hmul := mul_le_mul_of_nonneg_right hqlo hηnonneg
        dsimp [q] at hmul
        rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
        exact hmul
      have hxhi :
          x ≤ ((m : ℝ) + (1 / 2 : ℝ)) *
              fmt.minSubnormalMagnitude := by
        have hmul := mul_le_mul_of_nonneg_right hqhi hηnonneg
        dsimp [q] at hmul
        rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
        exact hmul
      exact
        fmt.nearestRoundingToFinite_subnormalValue_false_of_half_cell
          hm hxlo hxhi
  · simp [hleft]
    by_cases hright : midpoint < q
    · simp [hright]
      by_cases htop : fmt.minNormalMantissa ≤ m + 1
      · simp [htop]
        have hM_le_succ :
            (fmt.minNormalMantissa : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
          exact_mod_cast htop
        have hmid_eq : midpoint = ((m + 1 : ℕ) : ℝ) - (1 / 2 : ℝ) := by
          dsimp [midpoint]
          rw [Nat.cast_add, Nat.cast_one]
          ring
        have hqlo :
            (fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ) ≤ q := by
          rw [hmid_eq] at hright
          linarith
        have hxlo :
            ((fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ)) *
                fmt.minSubnormalMagnitude ≤ x := by
          have hmul := mul_le_mul_of_nonneg_right hqlo hηnonneg
          dsimp [q] at hmul
          rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
          exact hmul
        exact
          fmt.nearestRoundingToFinite_minNormalMagnitude_of_subnormal_boundary_half_le
            hxlo hx_le_min
      · simp [htop]
        have hsucc_lt_M : m + 1 < fmt.minNormalMantissa :=
          lt_of_not_ge htop
        have hm : fmt.subnormalMantissa (m + 1) :=
          ⟨Nat.succ_pos m, hsucc_lt_M⟩
        have hmid_eq : midpoint = ((m + 1 : ℕ) : ℝ) - (1 / 2 : ℝ) := by
          dsimp [midpoint]
          rw [Nat.cast_add, Nat.cast_one]
          ring
        have hqlo : ((m + 1 : ℕ) : ℝ) - (1 / 2 : ℝ) ≤ q := by
          rw [← hmid_eq]
          exact le_of_lt hright
        have hqhi : q ≤ ((m + 1 : ℕ) : ℝ) + (1 / 2 : ℝ) := by
          have hsucc' : q < ((m + 1 : ℕ) : ℝ) := by
            simpa using hfloor_succ
          linarith
        have hxlo :
            (((m + 1 : ℕ) : ℝ) - (1 / 2 : ℝ)) *
                fmt.minSubnormalMagnitude ≤ x := by
          have hmul := mul_le_mul_of_nonneg_right hqlo hηnonneg
          dsimp [q] at hmul
          rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
          exact hmul
        have hxhi :
            x ≤ (((m + 1 : ℕ) : ℝ) + (1 / 2 : ℝ)) *
                fmt.minSubnormalMagnitude := by
          have hmul := mul_le_mul_of_nonneg_right hqhi hηnonneg
          dsimp [q] at hmul
          rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
          exact hmul
        exact
          fmt.nearestRoundingToFinite_subnormalValue_false_of_half_cell
            hm hxlo hxhi
    · simp [hright]
      have htie : q = midpoint :=
        le_antisymm (le_of_not_gt hright) (le_of_not_gt hleft)
      by_cases heven : evenMantissa m
      · simp [heven]
        by_cases hm0 : m = 0
        · simp [hm0]
          have hq_le_half : q ≤ (1 / 2 : ℝ) := by
            rw [htie]
            simp [midpoint, hm0]
          have hx_le_half : x ≤ (1 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
            dsimp [q] at hq_le_half
            rw [div_le_iff₀ hηpos] at hq_le_half
            simpa [mul_comm] using hq_le_half
          exact
            fmt.nearestRoundingToFinite_zero_of_abs_le_half_minSubnormalMagnitude
              (by
                rw [abs_of_nonneg hxnonneg]
                exact hx_le_half)
        · simp [hm0]
          have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
          have hm : fmt.subnormalMantissa m := ⟨hmpos, hm_lt_M⟩
          have hqlo : (m : ℝ) - (1 / 2 : ℝ) ≤ q := by
            linarith
          have hqhi : q ≤ (m : ℝ) + (1 / 2 : ℝ) := by
            simpa [midpoint] using le_of_eq htie
          have hxlo :
              ((m : ℝ) - (1 / 2 : ℝ)) *
                  fmt.minSubnormalMagnitude ≤ x := by
            have hmul := mul_le_mul_of_nonneg_right hqlo hηnonneg
            dsimp [q] at hmul
            rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
            exact hmul
          have hxhi :
              x ≤ ((m : ℝ) + (1 / 2 : ℝ)) *
                  fmt.minSubnormalMagnitude := by
            have hmul := mul_le_mul_of_nonneg_right hqhi hηnonneg
            dsimp [q] at hmul
            rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
            exact hmul
          exact
            fmt.nearestRoundingToFinite_subnormalValue_false_of_half_cell
              hm hxlo hxhi
      · simp [heven]
        by_cases htop : fmt.minNormalMantissa ≤ m + 1
        · simp [htop]
          have hM_le_succ :
              (fmt.minNormalMantissa : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
            exact_mod_cast htop
          have hmid_eq : midpoint = ((m + 1 : ℕ) : ℝ) - (1 / 2 : ℝ) := by
            dsimp [midpoint]
            rw [Nat.cast_add, Nat.cast_one]
            ring
          have hqlo :
              (fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ) ≤ q := by
            rw [htie, hmid_eq]
            linarith
          have hxlo :
              ((fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ)) *
                  fmt.minSubnormalMagnitude ≤ x := by
            have hmul := mul_le_mul_of_nonneg_right hqlo hηnonneg
            dsimp [q] at hmul
            rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
            exact hmul
          exact
            fmt.nearestRoundingToFinite_minNormalMagnitude_of_subnormal_boundary_half_le
              hxlo hx_le_min
        · simp [htop]
          have hsucc_lt_M : m + 1 < fmt.minNormalMantissa :=
            lt_of_not_ge htop
          have hm : fmt.subnormalMantissa (m + 1) :=
            ⟨Nat.succ_pos m, hsucc_lt_M⟩
          have hmid_eq : midpoint = ((m + 1 : ℕ) : ℝ) - (1 / 2 : ℝ) := by
            dsimp [midpoint]
            rw [Nat.cast_add, Nat.cast_one]
            ring
          have hqlo : ((m + 1 : ℕ) : ℝ) - (1 / 2 : ℝ) ≤ q := by
            rw [htie, hmid_eq]
          have hqhi : q ≤ ((m + 1 : ℕ) : ℝ) + (1 / 2 : ℝ) := by
            have hsucc' : q < ((m + 1 : ℕ) : ℝ) := by
              simpa using hfloor_succ
            linarith
          have hxlo :
              (((m + 1 : ℕ) : ℝ) - (1 / 2 : ℝ)) *
                  fmt.minSubnormalMagnitude ≤ x := by
            have hmul := mul_le_mul_of_nonneg_right hqlo hηnonneg
            dsimp [q] at hmul
            rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
            exact hmul
          have hxhi :
              x ≤ (((m + 1 : ℕ) : ℝ) + (1 / 2 : ℝ)) *
                  fmt.minSubnormalMagnitude := by
            have hmul := mul_le_mul_of_nonneg_right hqhi hηnonneg
            dsimp [q] at hmul
            rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
            exact hmul
          exact
            fmt.nearestRoundingToFinite_subnormalValue_false_of_half_cell
              hm hxlo hxhi

/-- Source-style round-to-even selector for finite-underflow inputs, obtained
from the nonnegative selector by sign symmetry. -/
def finiteUnderflowRoundToEven (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  if 0 ≤ x then
    fmt.finiteUnderflowRoundToEvenNonneg x
  else
    -fmt.finiteUnderflowRoundToEvenNonneg (-x)

theorem finiteUnderflowRoundToEven_neg
    (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.finiteUnderflowRoundToEven (-x) =
      -fmt.finiteUnderflowRoundToEven x := by
  rcases lt_trichotomy x 0 with hxneg | hxzero | hxpos
  · have hx_nonneg : ¬ 0 ≤ x := by linarith
    have hnegx_nonneg : 0 ≤ -x := by linarith
    simp [finiteUnderflowRoundToEven, hx_nonneg, hnegx_nonneg]
  · subst x
    simp [finiteUnderflowRoundToEven, finiteUnderflowRoundToEvenNonneg_zero]
  · have hx_nonneg : 0 ≤ x := le_of_lt hxpos
    have hnegx_nonneg : ¬ 0 ≤ -x := by linarith
    simp [finiteUnderflowRoundToEven, hx_nonneg, hnegx_nonneg]

theorem finiteUnderflowRoundToEven_nearestRoundingToFinite
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    fmt.nearestRoundingToFinite x (fmt.finiteUnderflowRoundToEven x) := by
  unfold finiteUnderflowRoundToEven
  by_cases hxnonneg : 0 ≤ x
  · simp [hxnonneg]
    exact
      fmt.finiteUnderflowRoundToEvenNonneg_nearestRoundingToFinite
        hxnonneg hunder
  · simp [hxnonneg]
    have hxneg_nonneg : 0 ≤ -x := by linarith
    have hunder_neg : fmt.finiteUnderflowRange (-x) := by
      simpa [finiteUnderflowRange, abs_neg] using hunder
    have hround :=
      fmt.finiteUnderflowRoundToEvenNonneg_nearestRoundingToFinite
        hxneg_nonneg hunder_neg
    simpa using fmt.nearestRoundingToFinite_neg hround

/-- The source-facing underflow round-to-even branch satisfies Higham's
gradual-underflow additive absolute-error bound. -/
theorem finiteUnderflowRoundToEven_absError_le_gradualUnderflowEtaBound
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    absError (fmt.finiteUnderflowRoundToEven x) x ≤
      fmt.gradualUnderflowEtaBound :=
  fmt.nearestRoundingToFinite_absError_le_gradualUnderflowEtaBound_of_finiteUnderflowRange
    (fmt.finiteUnderflowRoundToEven_nearestRoundingToFinite hunder) hunder

/-- Strict gradual-underflow additive absolute-error bound for the source-facing
underflow round-to-even branch, away from exact half-cell ties. -/
theorem finiteUnderflowRoundToEven_absError_lt_gradualUnderflowEtaBound_of_noHalfTie
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x)
    (hnotie : fmt.finiteUnderflowNoHalfTie x) :
    absError (fmt.finiteUnderflowRoundToEven x) x <
      fmt.gradualUnderflowEtaBound :=
  fmt.nearestRoundingToFinite_absError_lt_gradualUnderflowEtaBound_of_finiteUnderflowRange_of_noHalfTie
    (fmt.finiteUnderflowRoundToEven_nearestRoundingToFinite hunder)
    hunder hnotie

/-- Source-style directed round-down selector for nonnegative finite-underflow
inputs.  It truncates the subnormal lattice coordinate `x / eta`, where
`eta = minSubnormalMagnitude`; index `0` denotes zero and positive indices below
`minNormalMantissa` denote positive subnormals. -/
def finiteUnderflowRoundTowardZeroNonneg
    (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  let q : ℝ := x / fmt.minSubnormalMagnitude
  let m : ℕ := Nat.floor q
  if m = 0 then 0 else fmt.subnormalValue false m

/-- Source-style directed round-up selector for nonnegative finite-underflow
inputs.  It uses the same subnormal lattice coordinate as
`finiteUnderflowRoundTowardZeroNonneg`, choosing the next lattice value unless
the coordinate is already exact.  The top lattice endpoint is the smallest
normal magnitude. -/
def finiteUnderflowRoundTowardPositiveNonneg
    (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  let q : ℝ := x / fmt.minSubnormalMagnitude
  let m : ℕ := Nat.floor q
  if q = (m : ℝ) then
    if m = 0 then 0 else fmt.subnormalValue false m
  else if fmt.minNormalMantissa ≤ m + 1 then
    fmt.minNormalMagnitude
  else
    fmt.subnormalValue false (m + 1)

theorem finiteUnderflowRoundTowardZeroNonneg_finiteSystem
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxnonneg : 0 ≤ x) (hunder : fmt.finiteUnderflowRange x) :
    fmt.finiteSystem (fmt.finiteUnderflowRoundTowardZeroNonneg x) := by
  let q : ℝ := x / fmt.minSubnormalMagnitude
  let m : ℕ := Nat.floor q
  have hηpos := fmt.minSubnormalMagnitude_pos
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude := le_of_lt hηpos
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hxnonneg hηnonneg
  have hx_lt_min : x < fmt.minNormalMagnitude := by
    simpa [finiteUnderflowRange, abs_of_nonneg hxnonneg] using hunder
  have hq_lt_M : q < (fmt.minNormalMantissa : ℝ) := by
    have htarget :=
      fmt.minNormalMagnitude_eq_minNormalMantissa_mul_minSubnormalMagnitude
    dsimp [q]
    rw [div_lt_iff₀ hηpos]
    simpa [htarget, mul_comm] using hx_lt_min
  have hfloor_le : (m : ℝ) ≤ q := Nat.floor_le hq_nonneg
  have hm_lt_M : m < fmt.minNormalMantissa :=
    Nat.cast_lt.mp (lt_of_le_of_lt hfloor_le hq_lt_M)
  change fmt.finiteSystem (if m = 0 then 0 else fmt.subnormalValue false m)
  by_cases hm0 : m = 0
  · simp [hm0, fmt.finiteSystem_zero]
  · simp [hm0]
    exact Or.inr (Or.inr
      ⟨false, m, ⟨Nat.pos_of_ne_zero hm0, hm_lt_M⟩, rfl⟩)

theorem finiteUnderflowRoundTowardPositiveNonneg_finiteSystem
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxnonneg : 0 ≤ x) (hunder : fmt.finiteUnderflowRange x) :
    fmt.finiteSystem (fmt.finiteUnderflowRoundTowardPositiveNonneg x) := by
  let q : ℝ := x / fmt.minSubnormalMagnitude
  let m : ℕ := Nat.floor q
  have hηpos := fmt.minSubnormalMagnitude_pos
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude := le_of_lt hηpos
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hxnonneg hηnonneg
  have hx_lt_min : x < fmt.minNormalMagnitude := by
    simpa [finiteUnderflowRange, abs_of_nonneg hxnonneg] using hunder
  have hq_lt_M : q < (fmt.minNormalMantissa : ℝ) := by
    have htarget :=
      fmt.minNormalMagnitude_eq_minNormalMantissa_mul_minSubnormalMagnitude
    dsimp [q]
    rw [div_lt_iff₀ hηpos]
    simpa [htarget, mul_comm] using hx_lt_min
  have hfloor_le : (m : ℝ) ≤ q := Nat.floor_le hq_nonneg
  have hm_lt_M : m < fmt.minNormalMantissa :=
    Nat.cast_lt.mp (lt_of_le_of_lt hfloor_le hq_lt_M)
  change
    fmt.finiteSystem
      (if q = (m : ℝ) then
        if m = 0 then 0 else fmt.subnormalValue false m
      else if fmt.minNormalMantissa ≤ m + 1 then
        fmt.minNormalMagnitude
      else
        fmt.subnormalValue false (m + 1))
  by_cases hqeq : q = (m : ℝ)
  · simp [hqeq]
    by_cases hm0 : m = 0
    · simp [hm0, fmt.finiteSystem_zero]
    · simp [hm0]
      exact Or.inr (Or.inr
        ⟨false, m, ⟨Nat.pos_of_ne_zero hm0, hm_lt_M⟩, rfl⟩)
  · simp [hqeq]
    by_cases htop : fmt.minNormalMantissa ≤ m + 1
    · simp [htop]
      exact fmt.minNormalMagnitude_mem_finiteSystem
    · simp [htop]
      have hsucc_lt_M : m + 1 < fmt.minNormalMantissa := lt_of_not_ge htop
      exact Or.inr (Or.inr
        ⟨false, m + 1, ⟨Nat.succ_pos m, hsucc_lt_M⟩, rfl⟩)

theorem finiteUnderflowRoundTowardZeroNonneg_nonneg
    (fmt : FloatingPointFormat) (x : ℝ) :
    0 ≤ fmt.finiteUnderflowRoundTowardZeroNonneg x := by
  let q : ℝ := x / fmt.minSubnormalMagnitude
  let m : ℕ := Nat.floor q
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude :=
    le_of_lt fmt.minSubnormalMagnitude_pos
  change 0 ≤ if m = 0 then 0 else fmt.subnormalValue false m
  by_cases hm0 : m = 0
  · simp [hm0]
  · simp [hm0, subnormalValue, signValue]
    exact mul_nonneg (Nat.cast_nonneg m) hηnonneg

theorem finiteUnderflowRoundTowardPositiveNonneg_nonneg
    (fmt : FloatingPointFormat) (x : ℝ) :
    0 ≤ fmt.finiteUnderflowRoundTowardPositiveNonneg x := by
  let q : ℝ := x / fmt.minSubnormalMagnitude
  let m : ℕ := Nat.floor q
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude :=
    le_of_lt fmt.minSubnormalMagnitude_pos
  have hmin_nonneg : 0 ≤ fmt.minNormalMagnitude :=
    le_of_lt fmt.minNormalMagnitude_pos
  change
    0 ≤
      if q = (m : ℝ) then
        if m = 0 then 0 else fmt.subnormalValue false m
      else if fmt.minNormalMantissa ≤ m + 1 then
        fmt.minNormalMagnitude
      else
        fmt.subnormalValue false (m + 1)
  by_cases hqeq : q = (m : ℝ)
  · simp [hqeq]
    by_cases hm0 : m = 0
    · simp [hm0]
    · simp [hm0, subnormalValue, signValue]
      exact mul_nonneg (Nat.cast_nonneg m) hηnonneg
  · simp [hqeq]
    by_cases htop : fmt.minNormalMantissa ≤ m + 1
    · simp [htop, hmin_nonneg]
    · simp [htop, subnormalValue, signValue]
      have hsucc_nonneg : 0 ≤ (m : ℝ) + 1 := by positivity
      exact mul_nonneg hsucc_nonneg hηnonneg

theorem finiteUnderflowRoundTowardZeroNonneg_le
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxnonneg : 0 ≤ x) :
    fmt.finiteUnderflowRoundTowardZeroNonneg x ≤ x := by
  let q : ℝ := x / fmt.minSubnormalMagnitude
  let m : ℕ := Nat.floor q
  have hηpos := fmt.minSubnormalMagnitude_pos
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude := le_of_lt hηpos
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hxnonneg hηnonneg
  have hfloor_le : (m : ℝ) ≤ q := Nat.floor_le hq_nonneg
  change (if m = 0 then 0 else fmt.subnormalValue false m) ≤ x
  by_cases hm0 : m = 0
  · simp [hm0, hxnonneg]
  · simp [hm0, subnormalValue, signValue]
    have hmul := mul_le_mul_of_nonneg_right hfloor_le hηnonneg
    dsimp [q] at hmul
    rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
    simpa [mul_assoc] using hmul

theorem le_finiteUnderflowRoundTowardPositiveNonneg
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxnonneg : 0 ≤ x) (hunder : fmt.finiteUnderflowRange x) :
    x ≤ fmt.finiteUnderflowRoundTowardPositiveNonneg x := by
  let q : ℝ := x / fmt.minSubnormalMagnitude
  let m : ℕ := Nat.floor q
  have hηpos := fmt.minSubnormalMagnitude_pos
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude := le_of_lt hηpos
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hxnonneg hηnonneg
  have hfloor_le : (m : ℝ) ≤ q := Nat.floor_le hq_nonneg
  have hfloor_succ : q < (m + 1 : ℕ) := by
    simpa [m] using Nat.lt_floor_add_one q
  have hx_lt_min : x < fmt.minNormalMagnitude := by
    simpa [finiteUnderflowRange, abs_of_nonneg hxnonneg] using hunder
  change
    x ≤
      if q = (m : ℝ) then
        if m = 0 then 0 else fmt.subnormalValue false m
      else if fmt.minNormalMantissa ≤ m + 1 then
        fmt.minNormalMagnitude
      else
        fmt.subnormalValue false (m + 1)
  by_cases hqeq : q = (m : ℝ)
  · simp [hqeq]
    have hx_div : x / fmt.minSubnormalMagnitude = (m : ℝ) := by
      simpa [q] using hqeq
    have hx_eq : x = (m : ℝ) * fmt.minSubnormalMagnitude := by
      calc
        x = x / fmt.minSubnormalMagnitude *
            fmt.minSubnormalMagnitude := by
          rw [div_mul_cancel₀ x (ne_of_gt hηpos)]
        _ = (m : ℝ) * fmt.minSubnormalMagnitude := by
          rw [hx_div]
    by_cases hm0 : m = 0
    · simp [hm0] at hx_eq
      simp [hm0, hx_eq]
    · simp [hm0, subnormalValue, signValue, minSubnormalMagnitude, hx_eq]
  · simp [hqeq]
    by_cases htop : fmt.minNormalMantissa ≤ m + 1
    · simp [htop]
      exact le_of_lt hx_lt_min
    · simp [htop, subnormalValue, signValue]
      have hqhi : q ≤ ((m + 1 : ℕ) : ℝ) := le_of_lt hfloor_succ
      have hmul := mul_le_mul_of_nonneg_right hqhi hηnonneg
      dsimp [q] at hmul
      rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
      simpa [Nat.cast_add, Nat.cast_one, mul_assoc] using hmul

/-- Source-style finite-underflow selector for rounding toward zero, obtained
from the nonnegative round-down selector by sign symmetry. -/
def finiteUnderflowRoundTowardZero
    (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  if 0 ≤ x then
    fmt.finiteUnderflowRoundTowardZeroNonneg x
  else
    -fmt.finiteUnderflowRoundTowardZeroNonneg (-x)

/-- Source-style finite-underflow selector for rounding toward positive
infinity, using round-up on nonnegative inputs and round-down after sign
symmetry on negative inputs. -/
def finiteUnderflowRoundTowardPositive
    (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  if 0 ≤ x then
    fmt.finiteUnderflowRoundTowardPositiveNonneg x
  else
    -fmt.finiteUnderflowRoundTowardZeroNonneg (-x)

/-- Source-style finite-underflow selector for rounding toward negative
infinity, using round-down on nonnegative inputs and round-up after sign
symmetry on negative inputs. -/
def finiteUnderflowRoundTowardNegative
    (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  if 0 ≤ x then
    fmt.finiteUnderflowRoundTowardZeroNonneg x
  else
    -fmt.finiteUnderflowRoundTowardPositiveNonneg (-x)

theorem finiteUnderflowRoundTowardZero_finiteSystem
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    fmt.finiteSystem (fmt.finiteUnderflowRoundTowardZero x) := by
  unfold finiteUnderflowRoundTowardZero
  by_cases hxnonneg : 0 ≤ x
  · simp [hxnonneg]
    exact
      fmt.finiteUnderflowRoundTowardZeroNonneg_finiteSystem
        hxnonneg hunder
  · simp [hxnonneg]
    have hxneg_nonneg : 0 ≤ -x := by linarith
    have hunder_neg : fmt.finiteUnderflowRange (-x) := by
      simpa [finiteUnderflowRange, abs_neg] using hunder
    exact fmt.finiteSystem_neg
      (fmt.finiteUnderflowRoundTowardZeroNonneg_finiteSystem
        hxneg_nonneg hunder_neg)

theorem finiteUnderflowRoundTowardPositive_finiteSystem
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    fmt.finiteSystem (fmt.finiteUnderflowRoundTowardPositive x) := by
  unfold finiteUnderflowRoundTowardPositive
  by_cases hxnonneg : 0 ≤ x
  · simp [hxnonneg]
    exact
      fmt.finiteUnderflowRoundTowardPositiveNonneg_finiteSystem
        hxnonneg hunder
  · simp [hxnonneg]
    have hxneg_nonneg : 0 ≤ -x := by linarith
    have hunder_neg : fmt.finiteUnderflowRange (-x) := by
      simpa [finiteUnderflowRange, abs_neg] using hunder
    exact fmt.finiteSystem_neg
      (fmt.finiteUnderflowRoundTowardZeroNonneg_finiteSystem
        hxneg_nonneg hunder_neg)

theorem finiteUnderflowRoundTowardNegative_finiteSystem
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    fmt.finiteSystem (fmt.finiteUnderflowRoundTowardNegative x) := by
  unfold finiteUnderflowRoundTowardNegative
  by_cases hxnonneg : 0 ≤ x
  · simp [hxnonneg]
    exact
      fmt.finiteUnderflowRoundTowardZeroNonneg_finiteSystem
        hxnonneg hunder
  · simp [hxnonneg]
    have hxneg_nonneg : 0 ≤ -x := by linarith
    have hunder_neg : fmt.finiteUnderflowRange (-x) := by
      simpa [finiteUnderflowRange, abs_neg] using hunder
    exact fmt.finiteSystem_neg
      (fmt.finiteUnderflowRoundTowardPositiveNonneg_finiteSystem
        hxneg_nonneg hunder_neg)

theorem finiteUnderflowRoundTowardZero_abs_le_abs
    {fmt : FloatingPointFormat} {x : ℝ}
    (_hunder : fmt.finiteUnderflowRange x) :
    |fmt.finiteUnderflowRoundTowardZero x| ≤ |x| := by
  unfold finiteUnderflowRoundTowardZero
  by_cases hxnonneg : 0 ≤ x
  · simp [hxnonneg]
    have hout_nonneg :=
      fmt.finiteUnderflowRoundTowardZeroNonneg_nonneg x
    have hout_le :=
      fmt.finiteUnderflowRoundTowardZeroNonneg_le hxnonneg
    rw [abs_of_nonneg hxnonneg, abs_of_nonneg hout_nonneg]
    exact hout_le
  · simp [hxnonneg]
    have hxneg_nonneg : 0 ≤ -x := by linarith
    have hout_nonneg :=
      fmt.finiteUnderflowRoundTowardZeroNonneg_nonneg (-x)
    have hout_le :=
      fmt.finiteUnderflowRoundTowardZeroNonneg_le hxneg_nonneg
    have hxneg : x < 0 := lt_of_not_ge hxnonneg
    rw [abs_of_neg hxneg, abs_of_nonneg hout_nonneg]
    exact hout_le

theorem le_finiteUnderflowRoundTowardPositive
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    x ≤ fmt.finiteUnderflowRoundTowardPositive x := by
  unfold finiteUnderflowRoundTowardPositive
  by_cases hxnonneg : 0 ≤ x
  · simp [hxnonneg]
    exact
      fmt.le_finiteUnderflowRoundTowardPositiveNonneg hxnonneg hunder
  · simp [hxnonneg]
    have hxneg_nonneg : 0 ≤ -x := by linarith
    have hout_le :=
      fmt.finiteUnderflowRoundTowardZeroNonneg_le hxneg_nonneg
    linarith

theorem finiteUnderflowRoundTowardNegative_le
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    fmt.finiteUnderflowRoundTowardNegative x ≤ x := by
  unfold finiteUnderflowRoundTowardNegative
  by_cases hxnonneg : 0 ≤ x
  · simp [hxnonneg]
    exact fmt.finiteUnderflowRoundTowardZeroNonneg_le hxnonneg
  · simp [hxnonneg]
    have hxneg_nonneg : 0 ≤ -x := by linarith
    have hunder_neg : fmt.finiteUnderflowRange (-x) := by
      simpa [finiteUnderflowRange, abs_neg] using hunder
    have hle :=
      fmt.le_finiteUnderflowRoundTowardPositiveNonneg
        hxneg_nonneg hunder_neg
    linarith

/-- Exact finite representable inputs round to themselves with signed relative
error witness `delta = 0`.  This includes zero, normalized values, and
subnormals. -/
theorem nearestRoundingToFinite_exact_signedRelErrorWitness
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteSystem x) :
    ∃ δ : ℝ,
      |δ| ≤ fmt.unitRoundoff ∧
        signedRelErrorWitness x x δ ∧
          fmt.nearestRoundingToFinite x x := by
  refine ⟨0, ?_, ?_, fmt.nearestRoundingToFinite_self hx⟩
  · simpa using fmt.unitRoundoff_nonneg
  · unfold signedRelErrorWitness
    ring

/-- Strict source-style variant of exact finite rounding: the zero witness
satisfies `|delta| < u` because `u` is positive. -/
theorem nearestRoundingToFinite_exact_signedRelErrorWitness_lt
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteSystem x) :
    ∃ δ : ℝ,
      |δ| < fmt.unitRoundoff ∧
        signedRelErrorWitness x x δ ∧
          fmt.nearestRoundingToFinite x x := by
  refine ⟨0, ?_, ?_, fmt.nearestRoundingToFinite_self hx⟩
  · simpa using fmt.unitRoundoff_pos
  · unfold signedRelErrorWitness
    ring

/-- Source-facing zero case for the finite-format relation: nearest rounding
has output zero and the signed relative-error witness holds with `delta = 0`. -/
theorem exists_nearestRoundingToFinite_signedRelErrorWitness_zero
    (fmt : FloatingPointFormat) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite 0 y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y 0 δ := by
  rcases fmt.nearestRoundingToFinite_exact_signedRelErrorWitness
      (x := 0) fmt.finiteSystem_zero with ⟨δ, hδ, hwit, hround⟩
  exact ⟨0, δ, hround, hδ, hwit⟩

theorem nearestRoundingToUnbounded_exact_signedRelErrorWitness
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.unboundedNormalizedSystem x) :
    ∃ δ : ℝ,
      |δ| ≤ fmt.unitRoundoff ∧
        signedRelErrorWitness x x δ ∧
          fmt.nearestRoundingToUnbounded x x := by
  refine ⟨0, ?_, ?_, fmt.nearestRoundingToUnbounded_self hx⟩
  · simpa using fmt.unitRoundoff_nonneg
  · unfold signedRelErrorWitness
    ring

theorem nearestRoundingToUnbounded_exact_signedRelErrorWitness_lt
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.unboundedNormalizedSystem x) :
    ∃ δ : ℝ,
      |δ| < fmt.unitRoundoff ∧
        signedRelErrorWitness x x δ ∧
          fmt.nearestRoundingToUnbounded x x := by
  refine ⟨0, ?_, ?_, fmt.nearestRoundingToUnbounded_self hx⟩
  · simpa using fmt.unitRoundoff_pos
  · unfold signedRelErrorWitness
    ring

theorem nearestRoundingIn_abs_sub_le_half_abs_sub_of_between
    {S : ℝ → Prop} {x y z : ℝ}
    (h : nearestRoundingIn S x y) (hz : S z)
    (hbetween : (y ≤ x ∧ x ≤ z) ∨ (z ≤ x ∧ x ≤ y)) :
    |x - y| ≤ (1 / 2 : ℝ) * |y - z| := by
  have hmin : |x - y| ≤ |x - z| :=
    nearestRoundingIn_minimal h hz
  rcases hbetween with hbetween | hbetween
  · rcases hbetween with ⟨hyx, hxz⟩
    have hyz : y ≤ z := le_trans hyx hxz
    have hxy_nonneg : 0 ≤ x - y := sub_nonneg.mpr hyx
    have hxz_nonpos : x - z ≤ 0 := sub_nonpos.mpr hxz
    have hyz_nonpos : y - z ≤ 0 := sub_nonpos.mpr hyz
    have hsum : |y - z| = |x - y| + |x - z| := by
      rw [abs_of_nonpos hyz_nonpos, abs_of_nonneg hxy_nonneg,
        abs_of_nonpos hxz_nonpos]
      ring
    have htwice : 2 * |x - y| ≤ |y - z| := by
      rw [hsum]
      nlinarith
    nlinarith
  · rcases hbetween with ⟨hzx, hxy⟩
    have hzy : z ≤ y := le_trans hzx hxy
    have hxy_nonpos : x - y ≤ 0 := sub_nonpos.mpr hxy
    have hxz_nonneg : 0 ≤ x - z := sub_nonneg.mpr hzx
    have hyz_nonneg : 0 ≤ y - z := sub_nonneg.mpr hzy
    have hsum : |y - z| = |x - y| + |x - z| := by
      rw [abs_of_nonneg hyz_nonneg, abs_of_nonpos hxy_nonpos,
        abs_of_nonneg hxz_nonneg]
      ring
    have htwice : 2 * |x - y| ≤ |y - z| := by
      rw [hsum]
      nlinarith
    nlinarith

theorem nearestRoundingToUnbounded_eq_left_or_right_of_realOrderAdjacent_ordered_between
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : a ≤ x ∧ x ≤ b) :
    y = a ∨ y = b := by
  by_cases hya : y = a
  · exact Or.inl hya
  by_cases hyb : y = b
  · exact Or.inr hyb
  have hy_mem : fmt.unboundedNormalizedSystem y := hround.1
  have ha_mem : fmt.unboundedNormalizedSystem a := hadj.1
  have hb_mem : fmt.unboundedNormalizedSystem b := hadj.2.1
  have hmin_a : |x - y| ≤ |x - a| := hround.2 a ha_mem
  have hmin_b : |x - y| ≤ |x - b| := hround.2 b hb_mem
  rcases lt_or_ge y a with hy_lt_a | ha_le_y
  · have hdist : |x - a| < |x - y| := by
      have hxa_nonneg : 0 ≤ x - a := sub_nonneg.mpr hbetween.1
      have hxy_nonneg : 0 ≤ x - y :=
        sub_nonneg.mpr (le_trans (le_of_lt hy_lt_a) hbetween.1)
      rw [abs_of_nonneg hxa_nonneg, abs_of_nonneg hxy_nonneg]
      linarith
    exact False.elim ((not_lt_of_ge hmin_a) hdist)
  · have ha_lt_y : a < y := by
      exact lt_of_le_of_ne ha_le_y (by
        intro hay
        exact hya hay.symm)
    rcases lt_or_ge y b with hy_lt_b | hb_le_y
    · exact False.elim
        ((hadj.2.2.2 y hy_mem) (Or.inl ⟨ha_lt_y, hy_lt_b⟩))
    · have hb_lt_y : b < y := by
        exact lt_of_le_of_ne hb_le_y (by
          intro hby
          exact hyb hby.symm)
      have hdist : |x - b| < |x - y| := by
        have hxb_nonpos : x - b ≤ 0 := sub_nonpos.mpr hbetween.2
        have hxy_nonpos : x - y ≤ 0 :=
          sub_nonpos.mpr (le_trans hbetween.2 (le_of_lt hb_lt_y))
        rw [abs_of_nonpos hxb_nonpos, abs_of_nonpos hxy_nonpos]
        linarith
      exact False.elim ((not_lt_of_ge hmin_b) hdist)

theorem nearestRoundingToUnbounded_eq_left_or_right_of_realOrderAdjacent_between
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : (a ≤ x ∧ x ≤ b) ∨ (b ≤ x ∧ x ≤ a)) :
    y = a ∨ y = b := by
  rcases hbetween with hbetween | hbetween
  · exact
      fmt.nearestRoundingToUnbounded_eq_left_or_right_of_realOrderAdjacent_ordered_between
        hround hadj hbetween
  · have hsel :=
      fmt.nearestRoundingToUnbounded_eq_left_or_right_of_realOrderAdjacent_ordered_between
        hround (fmt.realOrderAdjacentNormalized_symm hadj) hbetween
    rcases hsel with hyb | hya
    · exact Or.inr hyb
    · exact Or.inl hya

theorem nearestRoundingToUnbounded_left_of_realOrderAdjacent_ordered_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : a ≤ x ∧ x ≤ b)
    (hleft : |x - a| ≤ |x - b|) :
    fmt.nearestRoundingToUnbounded x a := by
  refine ⟨hadj.1, ?_⟩
  intro z hz
  by_cases hza_lt : z < a
  · have hxa_nonneg : 0 ≤ x - a := sub_nonneg.mpr hbetween.1
    have hxz_nonneg : 0 ≤ x - z :=
      sub_nonneg.mpr (le_trans (le_of_lt hza_lt) hbetween.1)
    rw [abs_of_nonneg hxa_nonneg, abs_of_nonneg hxz_nonneg]
    linarith
  · have ha_le_z : a ≤ z := le_of_not_gt hza_lt
    by_cases hza : z = a
    · simp [hza]
    · have haz : a < z := lt_of_le_of_ne ha_le_z (by
        intro haz_eq
        exact hza haz_eq.symm)
      by_cases hzb_lt : z < b
      · exact False.elim ((hadj.2.2.2 z hz) (Or.inl ⟨haz, hzb_lt⟩))
      · have hb_le_z : b ≤ z := le_of_not_gt hzb_lt
        by_cases hzb : z = b
        · simpa [hzb] using hleft
        · have hbz : b < z := lt_of_le_of_ne hb_le_z (by
            intro hbz_eq
            exact hzb hbz_eq.symm)
          have hdist_right : |x - b| ≤ |x - z| := by
            have hxb_nonpos : x - b ≤ 0 := sub_nonpos.mpr hbetween.2
            have hxz_nonpos : x - z ≤ 0 :=
              sub_nonpos.mpr (le_trans hbetween.2 (le_of_lt hbz))
            rw [abs_of_nonpos hxb_nonpos, abs_of_nonpos hxz_nonpos]
            linarith
          exact le_trans hleft hdist_right

theorem nearestRoundingToUnbounded_right_of_realOrderAdjacent_ordered_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : a ≤ x ∧ x ≤ b)
    (hright : |x - b| ≤ |x - a|) :
    fmt.nearestRoundingToUnbounded x b := by
  refine ⟨hadj.2.1, ?_⟩
  intro z hz
  by_cases hza_lt : z < a
  · have hdist_left : |x - a| ≤ |x - z| := by
      have hxa_nonneg : 0 ≤ x - a := sub_nonneg.mpr hbetween.1
      have hxz_nonneg : 0 ≤ x - z :=
        sub_nonneg.mpr (le_trans (le_of_lt hza_lt) hbetween.1)
      rw [abs_of_nonneg hxa_nonneg, abs_of_nonneg hxz_nonneg]
      linarith
    exact le_trans hright hdist_left
  · have ha_le_z : a ≤ z := le_of_not_gt hza_lt
    by_cases hza : z = a
    · simpa [hza] using hright
    · have haz : a < z := lt_of_le_of_ne ha_le_z (by
        intro haz_eq
        exact hza haz_eq.symm)
      by_cases hzb_lt : z < b
      · exact False.elim ((hadj.2.2.2 z hz) (Or.inl ⟨haz, hzb_lt⟩))
      · have hb_le_z : b ≤ z := le_of_not_gt hzb_lt
        by_cases hzb : z = b
        · simp [hzb]
        · have hbz : b < z := lt_of_le_of_ne hb_le_z (by
            intro hbz_eq
            exact hzb hbz_eq.symm)
          have hdist_right : |x - b| ≤ |x - z| := by
            have hxb_nonpos : x - b ≤ 0 := sub_nonpos.mpr hbetween.2
            have hxz_nonpos : x - z ≤ 0 :=
              sub_nonpos.mpr (le_trans hbetween.2 (le_of_lt hbz))
            rw [abs_of_nonpos hxb_nonpos, abs_of_nonpos hxz_nonpos]
            linarith
          exact hdist_right

/-- The local round-away selector is a valid nearest-rounding choice for a
supplied ordered adjacent normalized bracket. -/
theorem nearestAdjacentRoundAway_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : a ≤ x ∧ x ≤ b) :
    fmt.nearestRoundingToUnbounded x (nearestAdjacentRoundAway x a b) := by
  unfold nearestAdjacentRoundAway
  by_cases hleft_lt : |x - a| < |x - b|
  · simp [hleft_lt]
    exact
      fmt.nearestRoundingToUnbounded_left_of_realOrderAdjacent_ordered_between
        hadj hbetween (le_of_lt hleft_lt)
  · simp [hleft_lt]
    by_cases hright_lt : |x - b| < |x - a|
    · simp [hright_lt]
      exact
        fmt.nearestRoundingToUnbounded_right_of_realOrderAdjacent_ordered_between
          hadj hbetween (le_of_lt hright_lt)
    · simp [hright_lt]
      by_cases haway : |a| ≤ |b|
      · simp [haway]
        exact
          fmt.nearestRoundingToUnbounded_right_of_realOrderAdjacent_ordered_between
            hadj hbetween (le_of_not_gt hleft_lt)
      · simp [haway]
        exact
          fmt.nearestRoundingToUnbounded_left_of_realOrderAdjacent_ordered_between
            hadj hbetween (le_of_not_gt hright_lt)

theorem nearestAdjacentRoundToEven_eq_left_of_left_closer
    {x a b : ℝ} {leftMantissa : ℕ}
    (hleft : |x - a| < |x - b|) :
    nearestAdjacentRoundToEven x a b leftMantissa = a := by
  unfold nearestAdjacentRoundToEven
  simp [hleft]

theorem nearestAdjacentRoundToEven_eq_right_of_right_closer
    {x a b : ℝ} {leftMantissa : ℕ}
    (hright : |x - b| < |x - a|) :
    nearestAdjacentRoundToEven x a b leftMantissa = b := by
  unfold nearestAdjacentRoundToEven
  have hnot_left : ¬ |x - a| < |x - b| := not_lt_of_gt hright
  simp [hnot_left, hright]

theorem nearestAdjacentRoundToEven_eq_left_of_tie_even
    {x a b : ℝ} {leftMantissa : ℕ}
    (htie : |x - a| = |x - b|)
    (heven : evenMantissa leftMantissa) :
    nearestAdjacentRoundToEven x a b leftMantissa = a := by
  unfold nearestAdjacentRoundToEven
  have hnot_left : ¬ |x - a| < |x - b| := by
    rw [htie]
    exact lt_irrefl _
  have hnot_right : ¬ |x - b| < |x - a| := by
    rw [htie]
    exact lt_irrefl _
  simp [hnot_left, hnot_right, heven]

theorem nearestAdjacentRoundToEven_eq_right_of_tie_odd
    {x a b : ℝ} {leftMantissa : ℕ}
    (htie : |x - a| = |x - b|)
    (hodd : ¬ evenMantissa leftMantissa) :
    nearestAdjacentRoundToEven x a b leftMantissa = b := by
  unfold nearestAdjacentRoundToEven
  have hnot_left : ¬ |x - a| < |x - b| := by
    rw [htie]
    exact lt_irrefl _
  have hnot_right : ¬ |x - b| < |x - a| := by
    rw [htie]
    exact lt_irrefl _
  simp [hnot_left, hnot_right, hodd]

theorem nearestAdjacentRoundToEven_eq_left_endpoint
    (a b : ℝ) (leftMantissa : ℕ) :
    nearestAdjacentRoundToEven a a b leftMantissa = a := by
  by_cases hab : a = b
  · subst b
    simp [nearestAdjacentRoundToEven]
  · have hleft : |a - a| < |a - b| := by
      have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
      have hpos : 0 < |a - b| := abs_pos.mpr hne
      simpa using hpos
    exact nearestAdjacentRoundToEven_eq_left_of_left_closer hleft

theorem nearestAdjacentRoundToEven_eq_right_endpoint
    (a b : ℝ) (leftMantissa : ℕ) :
    nearestAdjacentRoundToEven b a b leftMantissa = b := by
  by_cases hab : a = b
  · subst b
    simp [nearestAdjacentRoundToEven]
  · have hright : |b - b| < |b - a| := by
      have hne : b - a ≠ 0 := by
        exact sub_ne_zero.mpr (fun hba => hab hba.symm)
      have hpos : 0 < |b - a| := abs_pos.mpr hne
      simpa using hpos
    exact nearestAdjacentRoundToEven_eq_right_of_right_closer hright

theorem nearestAdjacentRoundToEven_neg_of_even_right_iff_not_even_left
    {x a b : ℝ} {leftMantissa rightMantissa : ℕ}
    (hparity : evenMantissa rightMantissa ↔ ¬ evenMantissa leftMantissa) :
    nearestAdjacentRoundToEven (-x) (-b) (-a) rightMantissa =
      -nearestAdjacentRoundToEven x a b leftMantissa := by
  unfold nearestAdjacentRoundToEven
  have hdist_right : |-x - -b| = |x - b| := by
    have h : -x - -b = -(x - b) := by ring
    rw [h, abs_neg]
  have hdist_left : |-x - -a| = |x - a| := by
    have h : -x - -a = -(x - a) := by ring
    rw [h, abs_neg]
  rw [hdist_right, hdist_left]
  by_cases hleft : |x - a| < |x - b|
  · have hnot_right : ¬ |x - b| < |x - a| := not_lt_of_gt hleft
    simp [hleft, hnot_right]
  · by_cases hright : |x - b| < |x - a|
    · have hnot_left : ¬ |x - a| < |x - b| := not_lt_of_gt hright
      simp [hright, hnot_left]
    · have htie_left : ¬ |x - a| < |x - b| := hleft
      have htie_right : ¬ |x - b| < |x - a| := hright
      by_cases heven_left : evenMantissa leftMantissa
      · have hodd_right : ¬ evenMantissa rightMantissa := by
          intro heven_right
          exact (hparity.mp heven_right) heven_left
        simp [htie_left, htie_right, heven_left, hodd_right]
      · have heven_right : evenMantissa rightMantissa :=
          hparity.mpr heven_left
        simp [htie_left, htie_right, heven_left, heven_right]

/-- The local round-to-even selector is a valid nearest-rounding choice for a
supplied ordered adjacent normalized bracket.  This proves the source-level
nearest-rounding property of the tie policy, but not a total finite or IEEE
operation. -/
theorem nearestAdjacentRoundToEven_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
    {fmt : FloatingPointFormat} {x a b : ℝ} (leftMantissa : ℕ)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : a ≤ x ∧ x ≤ b) :
    fmt.nearestRoundingToUnbounded x
      (nearestAdjacentRoundToEven x a b leftMantissa) := by
  unfold nearestAdjacentRoundToEven
  by_cases hleft_lt : |x - a| < |x - b|
  · simp [hleft_lt]
    exact
      fmt.nearestRoundingToUnbounded_left_of_realOrderAdjacent_ordered_between
        hadj hbetween (le_of_lt hleft_lt)
  · simp [hleft_lt]
    by_cases hright_lt : |x - b| < |x - a|
    · simp [hright_lt]
      exact
        fmt.nearestRoundingToUnbounded_right_of_realOrderAdjacent_ordered_between
          hadj hbetween (le_of_lt hright_lt)
    · simp [hright_lt]
      by_cases heven : evenMantissa leftMantissa
      · simp [heven]
        exact
          fmt.nearestRoundingToUnbounded_left_of_realOrderAdjacent_ordered_between
            hadj hbetween (le_of_not_gt hright_lt)
      · simp [heven]
        exact
          fmt.nearestRoundingToUnbounded_right_of_realOrderAdjacent_ordered_between
            hadj hbetween (le_of_not_gt hleft_lt)

theorem nearestAdjacentRoundToEven_nearestRoundingToUnbounded_of_sameExponentAdjacentNormalized_ordered_between
    {fmt : FloatingPointFormat} {x a b : ℝ} {leftMantissa : ℕ}
    (hadj : fmt.sameExponentAdjacentNormalized a b)
    (hbetween : a ≤ x ∧ x ≤ b) :
    fmt.nearestRoundingToUnbounded x
      (nearestAdjacentRoundToEven x a b leftMantissa) := by
  exact
    fmt.nearestAdjacentRoundToEven_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
      leftMantissa
      (fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hadj)
      hbetween

theorem nearestRoundingToUnbounded_eq_left_of_realOrderAdjacent_ordered_between_of_left_closer
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : a ≤ x ∧ x ≤ b)
    (hleft : |x - a| < |x - b|) :
    y = a := by
  rcases
      fmt.nearestRoundingToUnbounded_eq_left_or_right_of_realOrderAdjacent_ordered_between
        hround hadj hbetween with hy | hy
  · exact hy
  · subst y
    have hmin : |x - b| ≤ |x - a| :=
      nearestRoundingIn_minimal hround hadj.1
    exact False.elim ((not_lt_of_ge hmin) hleft)

theorem nearestRoundingToUnbounded_eq_right_of_realOrderAdjacent_ordered_between_of_right_closer
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : a ≤ x ∧ x ≤ b)
    (hright : |x - b| < |x - a|) :
    y = b := by
  rcases
      fmt.nearestRoundingToUnbounded_eq_left_or_right_of_realOrderAdjacent_ordered_between
        hround hadj hbetween with hy | hy
  · subst y
    have hmin : |x - a| ≤ |x - b| :=
      nearestRoundingIn_minimal hround hadj.2.1
    exact False.elim ((not_lt_of_ge hmin) hright)
  · exact hy

theorem realOrderAdjacentNormalized_bracket_unique_of_strict_between
    {fmt : FloatingPointFormat} {x a b c d : ℝ}
    (hab : fmt.realOrderAdjacentNormalized a b)
    (hcd : fmt.realOrderAdjacentNormalized c d)
    (habx : a < x ∧ x < b)
    (hcdx : c ≤ x ∧ x ≤ d) :
    c = a ∧ d = b := by
  have hc_lt_x : c < x := by
    have hc_ne_x : c ≠ x := by
      intro hcx
      apply hab.2.2.2 c hcd.1
      exact Or.inl
        ⟨by simpa [hcx] using habx.1, by simpa [hcx] using habx.2⟩
    exact lt_of_le_of_ne hcdx.1 hc_ne_x
  have hx_lt_d : x < d := by
    have hd_ne_x : d ≠ x := by
      intro hdx
      apply hab.2.2.2 d hcd.2.1
      exact Or.inl
        ⟨by simpa [hdx] using habx.1, by simpa [hdx] using habx.2⟩
    exact lt_of_le_of_ne hcdx.2 hd_ne_x.symm
  have hc_eq_a : c = a := by
    rcases lt_trichotomy c a with hca | hca | hac
    · exfalso
      apply hcd.2.2.2 a hab.1
      exact Or.inl ⟨hca, lt_trans habx.1 hx_lt_d⟩
    · exact hca
    · exfalso
      apply hab.2.2.2 c hcd.1
      exact Or.inl ⟨hac, lt_trans hc_lt_x habx.2⟩
  subst c
  have hd_eq_b : d = b := by
    rcases lt_trichotomy d b with hdb | hdb | hbd
    · exfalso
      apply hab.2.2.2 d hcd.2.1
      exact Or.inl ⟨lt_trans habx.1 hx_lt_d, hdb⟩
    · exact hdb
    · exfalso
      apply hcd.2.2.2 b hab.2.1
      exact Or.inl ⟨lt_trans habx.1 habx.2, hbd⟩
  exact ⟨rfl, hd_eq_b⟩

theorem adjacentRoundTowardNegative_eq_right_of_eq_right
    {x a b : ℝ} (hxb : x = b) :
    adjacentRoundTowardNegative x a b = b := by
  simp [adjacentRoundTowardNegative, hxb]

theorem adjacentRoundTowardNegative_eq_left_of_ne_right
    {x a b : ℝ} (hxb : x ≠ b) :
    adjacentRoundTowardNegative x a b = a := by
  simp [adjacentRoundTowardNegative, hxb]

theorem adjacentRoundTowardPositive_eq_left_of_eq_left
    {x a b : ℝ} (hxa : x = a) :
    adjacentRoundTowardPositive x a b = a := by
  simp [adjacentRoundTowardPositive, hxa]

theorem adjacentRoundTowardPositive_eq_right_of_ne_left
    {x a b : ℝ} (hxa : x ≠ a) :
    adjacentRoundTowardPositive x a b = b := by
  simp [adjacentRoundTowardPositive, hxa]

theorem adjacentRoundTowardZero_eq_towardPositive_of_neg
    {x a b : ℝ} (hx : x < 0) :
    adjacentRoundTowardZero x a b = adjacentRoundTowardPositive x a b := by
  simp [adjacentRoundTowardZero, hx]

theorem adjacentRoundTowardZero_eq_towardNegative_of_nonneg
    {x a b : ℝ} (hx : 0 ≤ x) :
    adjacentRoundTowardZero x a b = adjacentRoundTowardNegative x a b := by
  simp [adjacentRoundTowardZero, not_lt.mpr hx]

theorem adjacentRoundTowardNegative_mem_unboundedNormalized
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b) :
    fmt.unboundedNormalizedSystem (adjacentRoundTowardNegative x a b) := by
  by_cases hxb : x = b
  · simpa [adjacentRoundTowardNegative, hxb] using hadj.2.1
  · simpa [adjacentRoundTowardNegative, hxb] using hadj.1

theorem adjacentRoundTowardPositive_mem_unboundedNormalized
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b) :
    fmt.unboundedNormalizedSystem (adjacentRoundTowardPositive x a b) := by
  by_cases hxa : x = a
  · simpa [adjacentRoundTowardPositive, hxa] using hadj.1
  · simpa [adjacentRoundTowardPositive, hxa] using hadj.2.1

theorem adjacentRoundTowardZero_mem_unboundedNormalized_of_nonneg_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (ha_nonneg : 0 ≤ a) (hbetween : a ≤ x ∧ x ≤ b) :
    fmt.unboundedNormalizedSystem (adjacentRoundTowardZero x a b) := by
  have hx_nonneg : 0 ≤ x := le_trans ha_nonneg hbetween.1
  by_cases hxb : x = b
  · have hb_nonneg : 0 ≤ b := by simpa [hxb] using hx_nonneg
    simpa [adjacentRoundTowardZero, adjacentRoundTowardNegative,
      not_lt.mpr hb_nonneg, hxb] using hadj.2.1
  · simpa [adjacentRoundTowardZero, adjacentRoundTowardNegative,
      not_lt.mpr hx_nonneg, hxb] using hadj.1

theorem adjacentRoundTowardZero_mem_unboundedNormalized_of_nonpos_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hb_nonpos : b ≤ 0) (hbetween : a ≤ x ∧ x ≤ b) :
    fmt.unboundedNormalizedSystem (adjacentRoundTowardZero x a b) := by
  have hb_ne : b ≠ 0 :=
    fmt.unboundedNormalizedSystem_ne_zero hadj.2.1
  have hb_neg : b < 0 := lt_of_le_of_ne hb_nonpos hb_ne
  have hx_neg : x < 0 := lt_of_le_of_lt hbetween.2 hb_neg
  by_cases hxa : x = a
  · have ha_neg : a < 0 := by simpa [hxa] using hx_neg
    simpa [adjacentRoundTowardZero, adjacentRoundTowardPositive, ha_neg,
      hxa] using hadj.1
  · simpa [adjacentRoundTowardZero, adjacentRoundTowardPositive, hx_neg,
      hxa] using hadj.2.1

theorem adjacentRoundTowardNegative_le_of_ordered_between
    {x a b : ℝ} (hbetween : a ≤ x ∧ x ≤ b) :
    adjacentRoundTowardNegative x a b ≤ x := by
  by_cases hxb : x = b
  · simp [adjacentRoundTowardNegative, hxb]
  · simpa [adjacentRoundTowardNegative, hxb] using hbetween.1

theorem le_adjacentRoundTowardPositive_of_ordered_between
    {x a b : ℝ} (hbetween : a ≤ x ∧ x ≤ b) :
    x ≤ adjacentRoundTowardPositive x a b := by
  by_cases hxa : x = a
  · simp [adjacentRoundTowardPositive, hxa]
  · simpa [adjacentRoundTowardPositive, hxa] using hbetween.2

theorem adjacentRoundTowardZero_nonneg_le_of_nonneg_between
    {x a b : ℝ} (ha_nonneg : 0 ≤ a) (hbetween : a ≤ x ∧ x ≤ b) :
    0 ≤ adjacentRoundTowardZero x a b ∧
      adjacentRoundTowardZero x a b ≤ x := by
  have hx_nonneg : 0 ≤ x := le_trans ha_nonneg hbetween.1
  by_cases hxb : x = b
  · constructor
    · have hb_nonneg : 0 ≤ b := by simpa [hxb] using hx_nonneg
      simpa [adjacentRoundTowardZero, adjacentRoundTowardNegative,
        not_lt.mpr hb_nonneg, hxb] using hb_nonneg
    · have hb_nonneg : 0 ≤ b := by simpa [hxb] using hx_nonneg
      simp [adjacentRoundTowardZero, adjacentRoundTowardNegative,
        not_lt.mpr hb_nonneg, hxb]
  · constructor
    · simpa [adjacentRoundTowardZero, adjacentRoundTowardNegative,
        not_lt.mpr hx_nonneg, hxb] using ha_nonneg
    · simpa [adjacentRoundTowardZero, adjacentRoundTowardNegative,
        not_lt.mpr hx_nonneg, hxb] using hbetween.1

theorem adjacentRoundTowardZero_le_nonpos_of_nonpos_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hb_nonpos : b ≤ 0) (hbetween : a ≤ x ∧ x ≤ b) :
    x ≤ adjacentRoundTowardZero x a b ∧
      adjacentRoundTowardZero x a b ≤ 0 := by
  have hb_ne : b ≠ 0 :=
    fmt.unboundedNormalizedSystem_ne_zero hadj.2.1
  have hb_neg : b < 0 := lt_of_le_of_ne hb_nonpos hb_ne
  have hx_neg : x < 0 := lt_of_le_of_lt hbetween.2 hb_neg
  have hx_nonpos : x ≤ 0 := le_trans hbetween.2 hb_nonpos
  by_cases hxa : x = a
  · constructor
    · have ha_neg : a < 0 := by simpa [hxa] using hx_neg
      simp [adjacentRoundTowardZero, adjacentRoundTowardPositive, ha_neg,
        hxa]
    · have ha_neg : a < 0 := by simpa [hxa] using hx_neg
      simpa [adjacentRoundTowardZero, adjacentRoundTowardPositive, ha_neg,
        hxa] using hx_nonpos
  · constructor
    · simpa [adjacentRoundTowardZero, adjacentRoundTowardPositive, hx_neg,
        hxa] using hbetween.2
    · simpa [adjacentRoundTowardZero, adjacentRoundTowardPositive, hx_neg,
        hxa] using hb_nonpos

theorem adjacentRoundTowardZero_abs_le_abs_of_nonneg_between
    {x a b : ℝ} (ha_nonneg : 0 ≤ a) (hbetween : a ≤ x ∧ x ≤ b) :
    |adjacentRoundTowardZero x a b| ≤ |x| := by
  have hx_nonneg : 0 ≤ x := le_trans ha_nonneg hbetween.1
  by_cases hxb : x = b
  · have hsel : adjacentRoundTowardZero x a b = x := by
      have hb_nonneg : 0 ≤ b := by simpa [hxb] using hx_nonneg
      simp [adjacentRoundTowardZero, adjacentRoundTowardNegative,
        not_lt.mpr hb_nonneg, hxb]
    rw [hsel]
  · have hsel : adjacentRoundTowardZero x a b = a := by
      simp [adjacentRoundTowardZero, adjacentRoundTowardNegative,
        not_lt.mpr hx_nonneg, hxb]
    rw [hsel, abs_of_nonneg ha_nonneg, abs_of_nonneg hx_nonneg]
    exact hbetween.1

theorem adjacentRoundTowardZero_abs_le_abs_of_nonpos_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hb_nonpos : b ≤ 0) (hbetween : a ≤ x ∧ x ≤ b) :
    |adjacentRoundTowardZero x a b| ≤ |x| := by
  have hb_ne : b ≠ 0 :=
    fmt.unboundedNormalizedSystem_ne_zero hadj.2.1
  have hb_neg : b < 0 := lt_of_le_of_ne hb_nonpos hb_ne
  have hx_neg : x < 0 := lt_of_le_of_lt hbetween.2 hb_neg
  have hx_nonpos : x ≤ 0 := le_trans hbetween.2 hb_nonpos
  by_cases hxa : x = a
  · have hsel : adjacentRoundTowardZero x a b = x := by
      have ha_neg : a < 0 := by simpa [hxa] using hx_neg
      simp [adjacentRoundTowardZero, adjacentRoundTowardPositive, ha_neg,
        hxa]
    rw [hsel]
  · have hsel : adjacentRoundTowardZero x a b = b := by
      simp [adjacentRoundTowardZero, adjacentRoundTowardPositive, hx_neg,
        hxa]
    rw [hsel, abs_of_nonpos hb_nonpos, abs_of_nonpos hx_nonpos]
    linarith

theorem exists_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : a ≤ x ∧ x ≤ b) :
    ∃ y : ℝ, (y = a ∨ y = b) ∧ fmt.nearestRoundingToUnbounded x y := by
  rcases le_total |x - a| |x - b| with hleft | hright
  · exact ⟨a, Or.inl rfl,
      fmt.nearestRoundingToUnbounded_left_of_realOrderAdjacent_ordered_between
        hadj hbetween hleft⟩
  · exact ⟨b, Or.inr rfl,
      fmt.nearestRoundingToUnbounded_right_of_realOrderAdjacent_ordered_between
        hadj hbetween hright⟩

theorem nearestRoundingToUnbounded_abs_sub_le_half_adjacent_gap
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : (a ≤ x ∧ x ≤ b) ∨ (b ≤ x ∧ x ≤ a)) :
    |x - y| ≤ (1 / 2 : ℝ) * |a - b| := by
  have hsel :=
    fmt.nearestRoundingToUnbounded_eq_left_or_right_of_realOrderAdjacent_between
      hround hadj hbetween
  rcases hsel with hya | hyb
  · have hbetween_y : (y ≤ x ∧ x ≤ b) ∨ (b ≤ x ∧ x ≤ y) := by
      simpa [hya] using hbetween
    have hhalf :=
      nearestRoundingIn_abs_sub_le_half_abs_sub_of_between
        hround hadj.2.1 hbetween_y
    simpa [hya] using hhalf
  · have hbetween' : (b ≤ x ∧ x ≤ a) ∨ (a ≤ x ∧ x ≤ b) := by
      rcases hbetween with hbetween | hbetween
      · exact Or.inr hbetween
      · exact Or.inl hbetween
    have hbetween_y : (y ≤ x ∧ x ≤ a) ∨ (a ≤ x ∧ x ≤ y) := by
      simpa [hyb] using hbetween'
    have hhalf :=
      nearestRoundingIn_abs_sub_le_half_abs_sub_of_between
        hround hadj.1 hbetween_y
    simpa [hyb, abs_sub_comm] using hhalf

theorem nearestRoundingToUnbounded_abs_sub_le_unitRoundoff_mul_anchor_of_realOrderAdjacent_between
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : (a ≤ x ∧ x ≤ b) ∨ (b ≤ x ∧ x ≤ a))
    (hanchor : |a| ≤ |x|) :
    |x - y| ≤ fmt.unitRoundoff * |x| := by
  have hhalf :=
    fmt.nearestRoundingToUnbounded_abs_sub_le_half_adjacent_gap
      hround hadj hbetween
  have hspace : |a - b| ≤ fmt.machineEpsilon * |a| :=
    (fmt.realOrderAdjacentNormalized_spacing_bounds_left hadj).2
  have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have heps_nonneg : 0 ≤ fmt.machineEpsilon := by
    unfold machineEpsilon
    exact le_of_lt (fmt.betaR_zpow_pos (1 - (fmt.t : ℤ)))
  have hgap_le :
      (1 / 2 : ℝ) * |a - b| ≤
        (1 / 2 : ℝ) * (fmt.machineEpsilon * |a|) :=
    mul_le_mul_of_nonneg_left hspace hhalf_nonneg
  have hanchor_le :
      fmt.machineEpsilon * |a| ≤ fmt.machineEpsilon * |x| :=
    mul_le_mul_of_nonneg_left hanchor heps_nonneg
  have hanchor_scaled :
      (1 / 2 : ℝ) * (fmt.machineEpsilon * |a|) ≤
        (1 / 2 : ℝ) * (fmt.machineEpsilon * |x|) :=
    mul_le_mul_of_nonneg_left hanchor_le hhalf_nonneg
  have hmain :
      |x - y| ≤ (1 / 2 : ℝ) * (fmt.machineEpsilon * |x|) :=
    le_trans hhalf (le_trans hgap_le hanchor_scaled)
  simpa [unitRoundoff, mul_assoc] using hmain

theorem nearestRoundingToUnbounded_abs_sub_le_unitRoundoff_mul_self_of_nonneg_between
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (ha_nonneg : 0 ≤ a)
    (hbetween : a ≤ x ∧ x ≤ b) :
    |x - y| ≤ fmt.unitRoundoff * |x| := by
  have hx_nonneg : 0 ≤ x := le_trans ha_nonneg hbetween.1
  have hanchor : |a| ≤ |x| := by
    rw [abs_of_nonneg ha_nonneg, abs_of_nonneg hx_nonneg]
    exact hbetween.1
  exact
    fmt.nearestRoundingToUnbounded_abs_sub_le_unitRoundoff_mul_anchor_of_realOrderAdjacent_between
      hround hadj (Or.inl hbetween) hanchor

theorem nearestRoundingToUnbounded_abs_sub_le_unitRoundoff_mul_self_of_nonpos_between
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hb_nonpos : b ≤ 0)
    (hbetween : a ≤ x ∧ x ≤ b) :
    |x - y| ≤ fmt.unitRoundoff * |x| := by
  have hx_nonpos : x ≤ 0 := le_trans hbetween.2 hb_nonpos
  have hanchor : |b| ≤ |x| := by
    rw [abs_of_nonpos hb_nonpos, abs_of_nonpos hx_nonpos]
    linarith
  exact
    fmt.nearestRoundingToUnbounded_abs_sub_le_unitRoundoff_mul_anchor_of_realOrderAdjacent_between
      hround (fmt.realOrderAdjacentNormalized_symm hadj) (Or.inr hbetween) hanchor

theorem nearestRoundingToUnbounded_abs_sub_lt_unitRoundoff_mul_self_of_nonneg_between
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (ha_nonneg : 0 ≤ a)
    (hbetween : a ≤ x ∧ x ≤ b) :
    |x - y| < fmt.unitRoundoff * |x| := by
  have ha_ne : a ≠ 0 :=
    fmt.unboundedNormalizedSystem_ne_zero hadj.1
  have hb_ne : b ≠ 0 :=
    fmt.unboundedNormalizedSystem_ne_zero hadj.2.1
  have ha_pos : 0 < a := lt_of_le_of_ne ha_nonneg (by
    intro hzero
    exact ha_ne hzero.symm)
  have hx_pos : 0 < x := lt_of_lt_of_le ha_pos hbetween.1
  have hu_pos : 0 < fmt.unitRoundoff := fmt.unitRoundoff_pos
  have hhalf :=
    fmt.nearestRoundingToUnbounded_abs_sub_le_half_adjacent_gap
      hround hadj (Or.inl hbetween)
  have hspace : |a - b| ≤ fmt.machineEpsilon * |a| :=
    (fmt.realOrderAdjacentNormalized_spacing_bounds_left hadj).2
  have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have hgap_le :
      (1 / 2 : ℝ) * |a - b| ≤
        (1 / 2 : ℝ) * (fmt.machineEpsilon * |a|) :=
    mul_le_mul_of_nonneg_left hspace hhalf_nonneg
  have hmain_anchor :
      |x - y| ≤ fmt.unitRoundoff * |a| := by
    have hmain :
        |x - y| ≤ (1 / 2 : ℝ) * (fmt.machineEpsilon * |a|) :=
      le_trans hhalf hgap_le
    simpa [unitRoundoff, mul_assoc] using hmain
  have hsel :=
    fmt.nearestRoundingToUnbounded_eq_left_or_right_of_realOrderAdjacent_ordered_between
      hround hadj hbetween
  rcases hsel with hya | hyb
  · by_cases hxa : x = a
    · have hpos_rhs : 0 < fmt.unitRoundoff * |x| :=
        mul_pos hu_pos (abs_pos.mpr (by
          intro hxzero
          exact ha_ne (by simpa [hxa] using hxzero)))
      simpa [hxa, hya] using hpos_rhs
    · have ha_lt_x : a < x := lt_of_le_of_ne hbetween.1 (by
        intro hax
        exact hxa hax.symm)
      have hanchor_lt : fmt.unitRoundoff * |a| < fmt.unitRoundoff * |x| := by
        rw [abs_of_pos ha_pos, abs_of_pos hx_pos]
        exact mul_lt_mul_of_pos_left ha_lt_x hu_pos
      exact lt_of_le_of_lt hmain_anchor hanchor_lt
  · by_cases hxb : x = b
    · have hpos_rhs : 0 < fmt.unitRoundoff * |x| :=
        mul_pos hu_pos (abs_pos.mpr (by
          intro hxzero
          exact hb_ne (by simpa [hxb] using hxzero)))
      simpa [hxb, hyb] using hpos_rhs
    · by_cases hxa : x = a
      · have hmin_a :=
          nearestRoundingIn_minimal hround hadj.1
        have hgap_le_zero : |a - b| ≤ 0 := by
          simpa [hxa, hyb] using hmin_a
        have hgap_pos : 0 < |a - b| :=
          abs_pos.mpr (by
            intro hzero
            exact hadj.2.2.1 (sub_eq_zero.mp hzero))
        exact False.elim ((not_lt_of_ge hgap_le_zero) hgap_pos)
      · have ha_lt_x : a < x := lt_of_le_of_ne hbetween.1 (by
          intro hax
          exact hxa hax.symm)
        have hanchor_lt : fmt.unitRoundoff * |a| < fmt.unitRoundoff * |x| := by
          rw [abs_of_pos ha_pos, abs_of_pos hx_pos]
          exact mul_lt_mul_of_pos_left ha_lt_x hu_pos
        exact lt_of_le_of_lt hmain_anchor hanchor_lt

theorem nearestRoundingToUnbounded_abs_sub_lt_unitRoundoff_mul_self_of_nonpos_between
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hb_nonpos : b ≤ 0)
    (hbetween : a ≤ x ∧ x ≤ b) :
    |x - y| < fmt.unitRoundoff * |x| := by
  have ha_ne : a ≠ 0 :=
    fmt.unboundedNormalizedSystem_ne_zero hadj.1
  have hb_ne : b ≠ 0 :=
    fmt.unboundedNormalizedSystem_ne_zero hadj.2.1
  have hb_neg : b < 0 := lt_of_le_of_ne hb_nonpos (by
    intro hzero
    exact hb_ne hzero)
  have hx_neg : x < 0 := lt_of_le_of_lt hbetween.2 hb_neg
  have hu_pos : 0 < fmt.unitRoundoff := fmt.unitRoundoff_pos
  have hhalf :=
    fmt.nearestRoundingToUnbounded_abs_sub_le_half_adjacent_gap
      hround hadj (Or.inl hbetween)
  have hspace : |a - b| ≤ fmt.machineEpsilon * |b| := by
    have hspace' :=
      (fmt.realOrderAdjacentNormalized_spacing_bounds_left
        (fmt.realOrderAdjacentNormalized_symm hadj)).2
    simpa [abs_sub_comm] using hspace'
  have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have hgap_le :
      (1 / 2 : ℝ) * |a - b| ≤
        (1 / 2 : ℝ) * (fmt.machineEpsilon * |b|) :=
    mul_le_mul_of_nonneg_left hspace hhalf_nonneg
  have hmain_anchor :
      |x - y| ≤ fmt.unitRoundoff * |b| := by
    have hmain :
        |x - y| ≤ (1 / 2 : ℝ) * (fmt.machineEpsilon * |b|) :=
      le_trans hhalf hgap_le
    simpa [unitRoundoff, mul_assoc] using hmain
  have hsel :=
    fmt.nearestRoundingToUnbounded_eq_left_or_right_of_realOrderAdjacent_ordered_between
      hround hadj hbetween
  rcases hsel with hya | hyb
  · by_cases hxa : x = a
    · have hpos_rhs : 0 < fmt.unitRoundoff * |x| :=
        mul_pos hu_pos (abs_pos.mpr (by
          intro hxzero
          exact ha_ne (by simpa [hxa] using hxzero)))
      simpa [hxa, hya] using hpos_rhs
    · by_cases hxb : x = b
      · have hmin_b :=
          nearestRoundingIn_minimal hround hadj.2.1
        have hgap_le_zero : |b - a| ≤ 0 := by
          simpa [hxb, hya] using hmin_b
        have hgap_pos : 0 < |b - a| :=
          abs_pos.mpr (by
            intro hzero
            exact hadj.2.2.1 (sub_eq_zero.mp hzero).symm)
        exact False.elim ((not_lt_of_ge hgap_le_zero) hgap_pos)
      · have hx_lt_b : x < b := lt_of_le_of_ne hbetween.2 hxb
        have hanchor_lt : fmt.unitRoundoff * |b| < fmt.unitRoundoff * |x| := by
          rw [abs_of_neg hb_neg, abs_of_neg hx_neg]
          have hneg : -b < -x := neg_lt_neg hx_lt_b
          exact mul_lt_mul_of_pos_left hneg hu_pos
        exact lt_of_le_of_lt hmain_anchor hanchor_lt
  · by_cases hxb : x = b
    · have hpos_rhs : 0 < fmt.unitRoundoff * |x| :=
        mul_pos hu_pos (abs_pos.mpr (by
          intro hxzero
          exact hb_ne (by simpa [hxb] using hxzero)))
      simpa [hxb, hyb] using hpos_rhs
    · have hx_lt_b : x < b := lt_of_le_of_ne hbetween.2 hxb
      have hanchor_lt : fmt.unitRoundoff * |b| < fmt.unitRoundoff * |x| := by
        rw [abs_of_neg hb_neg, abs_of_neg hx_neg]
        have hneg : -b < -x := neg_lt_neg hx_lt_b
        exact mul_lt_mul_of_pos_left hneg hu_pos
      exact lt_of_le_of_lt hmain_anchor hanchor_lt

theorem nearestRoundingToUnbounded_abs_sub_le_unitRoundoff_mul_rounded_of_realOrderAdjacent_between
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : (a ≤ x ∧ x ≤ b) ∨ (b ≤ x ∧ x ≤ a)) :
    |x - y| ≤ fmt.unitRoundoff * |y| := by
  have hhalf :=
    fmt.nearestRoundingToUnbounded_abs_sub_le_half_adjacent_gap
      hround hadj hbetween
  have hsel :=
    fmt.nearestRoundingToUnbounded_eq_left_or_right_of_realOrderAdjacent_between
      hround hadj hbetween
  have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
  rcases hsel with hya | hyb
  · have hspace : |a - b| ≤ fmt.machineEpsilon * |a| :=
      (fmt.realOrderAdjacentNormalized_spacing_bounds_left hadj).2
    have hgap_le :
        (1 / 2 : ℝ) * |a - b| ≤
          (1 / 2 : ℝ) * (fmt.machineEpsilon * |a|) :=
      mul_le_mul_of_nonneg_left hspace hhalf_nonneg
    have hmain :
        |x - y| ≤ (1 / 2 : ℝ) * (fmt.machineEpsilon * |a|) :=
      le_trans hhalf hgap_le
    simpa [hya, unitRoundoff, mul_assoc] using hmain
  · have hspace : |a - b| ≤ fmt.machineEpsilon * |b| := by
      have hspace' :=
        (fmt.realOrderAdjacentNormalized_spacing_bounds_left
          (fmt.realOrderAdjacentNormalized_symm hadj)).2
      simpa [abs_sub_comm] using hspace'
    have hgap_le :
        (1 / 2 : ℝ) * |a - b| ≤
          (1 / 2 : ℝ) * (fmt.machineEpsilon * |b|) :=
      mul_le_mul_of_nonneg_left hspace hhalf_nonneg
    have hmain :
        |x - y| ≤ (1 / 2 : ℝ) * (fmt.machineEpsilon * |b|) :=
      le_trans hhalf hgap_le
    simpa [hyb, unitRoundoff, mul_assoc] using hmain

theorem relErrorComputedDenom_le_unitRoundoff_of_abs_sub_le_unitRoundoff_mul_abs
    {fmt : FloatingPointFormat} {computed exact : ℝ}
    (hcomputed : computed ≠ 0)
    (hbound : |exact - computed| ≤ fmt.unitRoundoff * |computed|) :
    relErrorComputedDenom computed exact ≤ fmt.unitRoundoff := by
  unfold relErrorComputedDenom
  have hbound' : |computed - exact| ≤ fmt.unitRoundoff * |computed| := by
    simpa [abs_sub_comm] using hbound
  calc
    |computed - exact| / |computed| ≤
        (fmt.unitRoundoff * |computed|) / |computed| :=
      div_le_div_of_nonneg_right hbound' (abs_nonneg computed)
    _ = fmt.unitRoundoff := by
      have hcomputed_abs_pos : 0 < |computed| := abs_pos.mpr hcomputed
      field_simp [ne_of_gt hcomputed_abs_pos]

theorem nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_of_realOrderAdjacent_between
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : (a ≤ x ∧ x ≤ b) ∨ (b ≤ x ∧ x ≤ a)) :
    relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  have hy_ne : y ≠ 0 :=
    fmt.unboundedNormalizedSystem_ne_zero (nearestRoundingIn_mem hround)
  have hbound :=
    fmt.nearestRoundingToUnbounded_abs_sub_le_unitRoundoff_mul_rounded_of_realOrderAdjacent_between
      hround hadj hbetween
  exact
    fmt.relErrorComputedDenom_le_unitRoundoff_of_abs_sub_le_unitRoundoff_mul_abs
      hy_ne hbound

theorem signedRelErrorWitness_of_abs_sub_le_unitRoundoff_mul_abs
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : x ≠ 0)
    (hbound : |x - y| ≤ fmt.unitRoundoff * |x|) :
    ∃ δ : ℝ, |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases exists_signedRelErrorWitness_of_relErrorDefined y x hx with
    ⟨δ, hδ, hrel⟩
  refine ⟨δ, ?_, hδ⟩
  rw [← hrel]
  unfold relError
  have hxabs_pos : 0 < |x| := abs_pos.mpr hx
  have hbound' : |y - x| ≤ fmt.unitRoundoff * |x| := by
    simpa [abs_sub_comm] using hbound
  calc
    |y - x| / |x| ≤ (fmt.unitRoundoff * |x|) / |x| :=
      div_le_div_of_nonneg_right hbound' (abs_nonneg x)
    _ = fmt.unitRoundoff := by
      field_simp [ne_of_gt hxabs_pos]

theorem signedRelErrorWitness_of_abs_sub_lt_unitRoundoff_mul_abs
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : x ≠ 0)
    (hbound : |x - y| < fmt.unitRoundoff * |x|) :
    ∃ δ : ℝ, |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases exists_signedRelErrorWitness_of_relErrorDefined y x hx with
    ⟨δ, hδ, hrel⟩
  refine ⟨δ, ?_, hδ⟩
  rw [← hrel]
  unfold relError
  have hxabs_pos : 0 < |x| := abs_pos.mpr hx
  have hbound' : |y - x| < fmt.unitRoundoff * |x| := by
    simpa [abs_sub_comm] using hbound
  calc
    |y - x| / |x| < (fmt.unitRoundoff * |x|) / |x| :=
      div_lt_div_of_pos_right hbound' hxabs_pos
    _ = fmt.unitRoundoff := by
      field_simp [ne_of_gt hxabs_pos]

theorem nearestRoundingToUnbounded_signedRelErrorWitness_of_nonneg_between
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (ha_nonneg : 0 ≤ a)
    (hbetween : a ≤ x ∧ x ≤ b) :
    ∃ δ : ℝ,
      |δ| ≤ fmt.unitRoundoff ∧
        signedRelErrorWitness y x δ ∧
          fmt.nearestRoundingToUnbounded x y := by
  have ha_ne : a ≠ 0 :=
    fmt.unboundedNormalizedSystem_ne_zero hadj.1
  have ha_pos : 0 < a := lt_of_le_of_ne ha_nonneg (by
    intro hzero
    exact ha_ne hzero.symm)
  have hx_pos : 0 < x := lt_of_lt_of_le ha_pos hbetween.1
  have hbound :=
    fmt.nearestRoundingToUnbounded_abs_sub_le_unitRoundoff_mul_self_of_nonneg_between
      hround hadj ha_nonneg hbetween
  rcases fmt.signedRelErrorWitness_of_abs_sub_le_unitRoundoff_mul_abs
      (ne_of_gt hx_pos) hbound with ⟨δ, hδ, hwit⟩
  exact ⟨δ, hδ, hwit, hround⟩

theorem nearestRoundingToUnbounded_signedRelErrorWitness_of_nonpos_between
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hb_nonpos : b ≤ 0)
    (hbetween : a ≤ x ∧ x ≤ b) :
    ∃ δ : ℝ,
      |δ| ≤ fmt.unitRoundoff ∧
        signedRelErrorWitness y x δ ∧
          fmt.nearestRoundingToUnbounded x y := by
  have hb_ne : b ≠ 0 :=
    fmt.unboundedNormalizedSystem_ne_zero hadj.2.1
  have hb_neg : b < 0 := lt_of_le_of_ne hb_nonpos (by
    intro hzero
    exact hb_ne hzero)
  have hx_neg : x < 0 := lt_of_le_of_lt hbetween.2 hb_neg
  have hbound :=
    fmt.nearestRoundingToUnbounded_abs_sub_le_unitRoundoff_mul_self_of_nonpos_between
      hround hadj hb_nonpos hbetween
  rcases fmt.signedRelErrorWitness_of_abs_sub_le_unitRoundoff_mul_abs
      (ne_of_lt hx_neg) hbound with ⟨δ, hδ, hwit⟩
  exact ⟨δ, hδ, hwit, hround⟩

theorem nearestRoundingToUnbounded_signedRelErrorWitness_lt_of_nonneg_between
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (ha_nonneg : 0 ≤ a)
    (hbetween : a ≤ x ∧ x ≤ b) :
    ∃ δ : ℝ,
      |δ| < fmt.unitRoundoff ∧
        signedRelErrorWitness y x δ ∧
          fmt.nearestRoundingToUnbounded x y := by
  have ha_ne : a ≠ 0 :=
    fmt.unboundedNormalizedSystem_ne_zero hadj.1
  have ha_pos : 0 < a := lt_of_le_of_ne ha_nonneg (by
    intro hzero
    exact ha_ne hzero.symm)
  have hx_pos : 0 < x := lt_of_lt_of_le ha_pos hbetween.1
  have hbound :=
    fmt.nearestRoundingToUnbounded_abs_sub_lt_unitRoundoff_mul_self_of_nonneg_between
      hround hadj ha_nonneg hbetween
  rcases fmt.signedRelErrorWitness_of_abs_sub_lt_unitRoundoff_mul_abs
      (ne_of_gt hx_pos) hbound with ⟨δ, hδ, hwit⟩
  exact ⟨δ, hδ, hwit, hround⟩

theorem nearestRoundingToUnbounded_signedRelErrorWitness_lt_of_nonpos_between
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hb_nonpos : b ≤ 0)
    (hbetween : a ≤ x ∧ x ≤ b) :
    ∃ δ : ℝ,
      |δ| < fmt.unitRoundoff ∧
        signedRelErrorWitness y x δ ∧
          fmt.nearestRoundingToUnbounded x y := by
  have hb_ne : b ≠ 0 :=
    fmt.unboundedNormalizedSystem_ne_zero hadj.2.1
  have hb_neg : b < 0 := lt_of_le_of_ne hb_nonpos (by
    intro hzero
    exact hb_ne hzero)
  have hx_neg : x < 0 := lt_of_le_of_lt hbetween.2 hb_neg
  have hbound :=
    fmt.nearestRoundingToUnbounded_abs_sub_lt_unitRoundoff_mul_self_of_nonpos_between
      hround hadj hb_nonpos hbetween
  rcases fmt.signedRelErrorWitness_of_abs_sub_lt_unitRoundoff_mul_abs
      (ne_of_lt hx_neg) hbound with ⟨δ, hδ, hwit⟩
  exact ⟨δ, hδ, hwit, hround⟩

/-- The explicit local round-away selector inherits Higham's strict
source-relative error witness on nonnegative adjacent brackets. -/
theorem nearestAdjacentRoundAway_signedRelErrorWitness_lt_of_nonneg_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (ha_nonneg : 0 ≤ a)
    (hbetween : a ≤ x ∧ x ≤ b) :
    ∃ δ : ℝ,
      |δ| < fmt.unitRoundoff ∧
        signedRelErrorWitness (nearestAdjacentRoundAway x a b) x δ ∧
          fmt.nearestRoundingToUnbounded x (nearestAdjacentRoundAway x a b) := by
  have hround :=
    fmt.nearestAdjacentRoundAway_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
      hadj hbetween
  rcases
    fmt.nearestRoundingToUnbounded_signedRelErrorWitness_lt_of_nonneg_between
      hround hadj ha_nonneg hbetween with
    ⟨δ, hδ, hwit, hround'⟩
  exact ⟨δ, hδ, hwit, hround'⟩

/-- The explicit local round-away selector inherits Higham's strict
source-relative error witness on nonpositive adjacent brackets. -/
theorem nearestAdjacentRoundAway_signedRelErrorWitness_lt_of_nonpos_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hb_nonpos : b ≤ 0)
    (hbetween : a ≤ x ∧ x ≤ b) :
    ∃ δ : ℝ,
      |δ| < fmt.unitRoundoff ∧
        signedRelErrorWitness (nearestAdjacentRoundAway x a b) x δ ∧
          fmt.nearestRoundingToUnbounded x (nearestAdjacentRoundAway x a b) := by
  have hround :=
    fmt.nearestAdjacentRoundAway_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
      hadj hbetween
  rcases
    fmt.nearestRoundingToUnbounded_signedRelErrorWitness_lt_of_nonpos_between
      hround hadj hb_nonpos hbetween with
    ⟨δ, hδ, hwit, hround'⟩
  exact ⟨δ, hδ, hwit, hround'⟩

theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_of_nonneg_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (ha_nonneg : 0 ≤ a)
    (hbetween : a ≤ x ∧ x ≤ b) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases fmt.exists_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
      hadj hbetween with ⟨y, _hyab, hround⟩
  rcases fmt.nearestRoundingToUnbounded_signedRelErrorWitness_of_nonneg_between
      hround hadj ha_nonneg hbetween with ⟨δ, hδ, hwit, _⟩
  exact ⟨y, δ, hround, hδ, hwit⟩

theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_of_nonpos_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hb_nonpos : b ≤ 0)
    (hbetween : a ≤ x ∧ x ≤ b) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases fmt.exists_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
      hadj hbetween with ⟨y, _hyab, hround⟩
  rcases fmt.nearestRoundingToUnbounded_signedRelErrorWitness_of_nonpos_between
      hround hadj hb_nonpos hbetween with ⟨δ, hδ, hwit, _⟩
  exact ⟨y, δ, hround, hδ, hwit⟩

theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_of_nonneg_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (ha_nonneg : 0 ≤ a)
    (hbetween : a ≤ x ∧ x ≤ b) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases fmt.exists_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
      hadj hbetween with ⟨y, _hyab, hround⟩
  rcases fmt.nearestRoundingToUnbounded_signedRelErrorWitness_lt_of_nonneg_between
      hround hadj ha_nonneg hbetween with ⟨δ, hδ, hwit, _⟩
  exact ⟨y, δ, hround, hδ, hwit⟩

theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_of_nonpos_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hb_nonpos : b ≤ 0)
    (hbetween : a ≤ x ∧ x ≤ b) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases fmt.exists_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
      hadj hbetween with ⟨y, _hyab, hround⟩
  rcases fmt.nearestRoundingToUnbounded_signedRelErrorWitness_lt_of_nonpos_between
      hround hadj hb_nonpos hbetween with ⟨δ, hδ, hwit, _⟩
  exact ⟨y, δ, hround, hδ, hwit⟩

theorem nearestRoundingToUnbounded_exact_relErrorComputedDenom_le_unitRoundoff
    {fmt : FloatingPointFormat} {x : ℝ}
    (_hx : fmt.unboundedNormalizedSystem x) :
    relErrorComputedDenom x x ≤ fmt.unitRoundoff := by
  unfold relErrorComputedDenom
  simpa using fmt.unitRoundoff_nonneg

theorem exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_of_realOrderAdjacent_ordered_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : a ≤ x ∧ x ≤ b) :
    ∃ y : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  rcases fmt.exists_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
      hadj hbetween with ⟨y, _hyab, hround⟩
  have hy_ne : y ≠ 0 :=
    fmt.unboundedNormalizedSystem_ne_zero (nearestRoundingIn_mem hround)
  have hrel :=
    fmt.nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_of_realOrderAdjacent_between
      hround hadj (Or.inl hbetween)
  exact ⟨y, hround, hy_ne, hrel⟩

/-- Same-exponent positive nearest-rounding theorem.  Once a positive input
is known to lie between the smallest and largest normalized values at a fixed
exponent, the floor bracketing theorem and local adjacent-rounding bounds
produce Higham's signed relative-error witness for nearest rounding in `G`. -/
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_sameExponent_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hmin : fmt.normalizedValue false fmt.minNormalMantissa e ≤ x)
    (hmax : x ≤ fmt.normalizedValue false fmt.maxNormalMantissa e) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases fmt.exists_unboundedNormalized_or_realOrderAdjacent_bracket_sameExponent
      hmin hmax with hrepr | hbracket
  · rcases hrepr with ⟨m, hm, hx_eq⟩
    have hx_mem : fmt.unboundedNormalizedSystem x :=
      ⟨false, m, e, hm, hx_eq⟩
    rcases fmt.nearestRoundingToUnbounded_exact_signedRelErrorWitness hx_mem with
      ⟨δ, hδ, hwit, hround⟩
    exact ⟨x, δ, hround, hδ, hwit⟩
  · rcases hbracket with ⟨a, b, hadj, ha_nonneg, ha_le_x, hx_le_b⟩
    exact
      fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_of_nonneg_between
        hadj ha_nonneg ⟨ha_le_x, hx_le_b⟩

/-- Same-exponent negative-bin nearest-rounding theorem.  This is the sign
mirror of the positive fixed-exponent theorem and packages the adjacent-bracket
core into Higham's signed relative-error form for negative inputs in one
exponent bin. -/
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_sameExponent_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : fmt.normalizedValue true fmt.maxNormalMantissa e ≤ x)
    (hhi : x ≤ fmt.normalizedValue true fmt.minNormalMantissa e) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases fmt.exists_unboundedNormalized_or_realOrderAdjacent_bracket_sameExponent_negative
      hlo hhi with hrepr | hbracket
  · rcases hrepr with ⟨m, hm, hx_eq⟩
    have hx_mem : fmt.unboundedNormalizedSystem x :=
      ⟨true, m, e, hm, hx_eq⟩
    rcases fmt.nearestRoundingToUnbounded_exact_signedRelErrorWitness hx_mem with
      ⟨δ, hδ, hwit, hround⟩
    exact ⟨x, δ, hround, hδ, hwit⟩
  · rcases hbracket with ⟨a, b, hadj, hb_nonpos, ha_le_x, hx_le_b⟩
    exact
      fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_of_nonpos_between
        hadj hb_nonpos ⟨ha_le_x, hx_le_b⟩

theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_sameExponent_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hmin : fmt.normalizedValue false fmt.minNormalMantissa e ≤ x)
    (hmax : x ≤ fmt.normalizedValue false fmt.maxNormalMantissa e) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases fmt.exists_unboundedNormalized_or_realOrderAdjacent_bracket_sameExponent
      hmin hmax with hrepr | hbracket
  · rcases hrepr with ⟨m, hm, hx_eq⟩
    have hx_mem : fmt.unboundedNormalizedSystem x :=
      ⟨false, m, e, hm, hx_eq⟩
    rcases fmt.nearestRoundingToUnbounded_exact_signedRelErrorWitness_lt hx_mem with
      ⟨δ, hδ, hwit, hround⟩
    exact ⟨x, δ, hround, hδ, hwit⟩
  · rcases hbracket with ⟨a, b, hadj, ha_nonneg, ha_le_x, hx_le_b⟩
    exact
      fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_of_nonneg_between
        hadj ha_nonneg ⟨ha_le_x, hx_le_b⟩

theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_sameExponent_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : fmt.normalizedValue true fmt.maxNormalMantissa e ≤ x)
    (hhi : x ≤ fmt.normalizedValue true fmt.minNormalMantissa e) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases fmt.exists_unboundedNormalized_or_realOrderAdjacent_bracket_sameExponent_negative
      hlo hhi with hrepr | hbracket
  · rcases hrepr with ⟨m, hm, hx_eq⟩
    have hx_mem : fmt.unboundedNormalizedSystem x :=
      ⟨true, m, e, hm, hx_eq⟩
    rcases fmt.nearestRoundingToUnbounded_exact_signedRelErrorWitness_lt hx_mem with
      ⟨δ, hδ, hwit, hround⟩
    exact ⟨x, δ, hround, hδ, hwit⟩
  · rcases hbracket with ⟨a, b, hadj, hb_nonpos, ha_le_x, hx_le_b⟩
    exact
      fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_of_nonpos_between
        hadj hb_nonpos ⟨ha_le_x, hx_le_b⟩

/-- Same-exponent positive theorem with the local round-away selector exposed.
In the exact case the selected value is `x`; in the adjacent-bracket case it is
`nearestAdjacentRoundAway x a b`. -/
theorem exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_sameExponent_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hmin : fmt.normalizedValue false fmt.minNormalMantissa e ≤ x)
    (hmax : x ≤ fmt.normalizedValue false fmt.maxNormalMantissa e) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            ((∃ m : ℕ,
                fmt.normalizedMantissa m ∧
                  x = fmt.normalizedValue false m e ∧ y = x) ∨
              ∃ a b : ℝ,
                fmt.realOrderAdjacentNormalized a b ∧
                  0 ≤ a ∧ a ≤ x ∧ x ≤ b ∧
                    y = nearestAdjacentRoundAway x a b) := by
  rcases fmt.exists_unboundedNormalized_or_realOrderAdjacent_bracket_sameExponent
      hmin hmax with hrepr | hbracket
  · rcases hrepr with ⟨m, hm, hx_eq⟩
    have hx_mem : fmt.unboundedNormalizedSystem x :=
      ⟨false, m, e, hm, hx_eq⟩
    rcases fmt.nearestRoundingToUnbounded_exact_signedRelErrorWitness_lt hx_mem with
      ⟨δ, hδ, hwit, hround⟩
    exact ⟨x, δ, hround, hδ, hwit, Or.inl ⟨m, hm, hx_eq, rfl⟩⟩
  · rcases hbracket with ⟨a, b, hadj, ha_nonneg, ha_le_x, hx_le_b⟩
    rcases
      fmt.nearestAdjacentRoundAway_signedRelErrorWitness_lt_of_nonneg_between
        hadj ha_nonneg ⟨ha_le_x, hx_le_b⟩ with
      ⟨δ, hδ, hwit, hround⟩
    exact
      ⟨nearestAdjacentRoundAway x a b, δ, hround, hδ, hwit,
        Or.inr ⟨a, b, hadj, ha_nonneg, ha_le_x, hx_le_b, rfl⟩⟩

/-- Same-exponent negative theorem with the local round-away selector exposed.
In the exact case the selected value is `x`; in the adjacent-bracket case it is
`nearestAdjacentRoundAway x a b`. -/
theorem exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_sameExponent_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : fmt.normalizedValue true fmt.maxNormalMantissa e ≤ x)
    (hhi : x ≤ fmt.normalizedValue true fmt.minNormalMantissa e) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            ((∃ m : ℕ,
                fmt.normalizedMantissa m ∧
                  x = fmt.normalizedValue true m e ∧ y = x) ∨
              ∃ a b : ℝ,
                fmt.realOrderAdjacentNormalized a b ∧
                  b ≤ 0 ∧ a ≤ x ∧ x ≤ b ∧
                    y = nearestAdjacentRoundAway x a b) := by
  rcases fmt.exists_unboundedNormalized_or_realOrderAdjacent_bracket_sameExponent_negative
      hlo hhi with hrepr | hbracket
  · rcases hrepr with ⟨m, hm, hx_eq⟩
    have hx_mem : fmt.unboundedNormalizedSystem x :=
      ⟨true, m, e, hm, hx_eq⟩
    rcases fmt.nearestRoundingToUnbounded_exact_signedRelErrorWitness_lt hx_mem with
      ⟨δ, hδ, hwit, hround⟩
    exact ⟨x, δ, hround, hδ, hwit, Or.inl ⟨m, hm, hx_eq, rfl⟩⟩
  · rcases hbracket with ⟨a, b, hadj, hb_nonpos, ha_le_x, hx_le_b⟩
    rcases
      fmt.nearestAdjacentRoundAway_signedRelErrorWitness_lt_of_nonpos_between
        hadj hb_nonpos ⟨ha_le_x, hx_le_b⟩ with
      ⟨δ, hδ, hwit, hround⟩
    exact
      ⟨nearestAdjacentRoundAway x a b, δ, hround, hδ, hwit,
        Or.inr ⟨a, b, hadj, hb_nonpos, ha_le_x, hx_le_b, rfl⟩⟩

theorem exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_sameExponent_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hmin : fmt.normalizedValue false fmt.minNormalMantissa e ≤ x)
    (hmax : x ≤ fmt.normalizedValue false fmt.maxNormalMantissa e) :
    ∃ y : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  rcases fmt.exists_unboundedNormalized_or_realOrderAdjacent_bracket_sameExponent
      hmin hmax with hrepr | hbracket
  · rcases hrepr with ⟨m, hm, hx_eq⟩
    have hx_mem : fmt.unboundedNormalizedSystem x :=
      ⟨false, m, e, hm, hx_eq⟩
    exact
      ⟨x, fmt.nearestRoundingToUnbounded_self hx_mem,
        fmt.unboundedNormalizedSystem_ne_zero hx_mem,
        fmt.nearestRoundingToUnbounded_exact_relErrorComputedDenom_le_unitRoundoff
          hx_mem⟩
  · rcases hbracket with ⟨a, b, hadj, _ha_nonneg, ha_le_x, hx_le_b⟩
    exact
      fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_of_realOrderAdjacent_ordered_between
        hadj ⟨ha_le_x, hx_le_b⟩

theorem exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_sameExponent_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : fmt.normalizedValue true fmt.maxNormalMantissa e ≤ x)
    (hhi : x ≤ fmt.normalizedValue true fmt.minNormalMantissa e) :
    ∃ y : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  rcases fmt.exists_unboundedNormalized_or_realOrderAdjacent_bracket_sameExponent_negative
      hlo hhi with hrepr | hbracket
  · rcases hrepr with ⟨m, hm, hx_eq⟩
    have hx_mem : fmt.unboundedNormalizedSystem x :=
      ⟨true, m, e, hm, hx_eq⟩
    exact
      ⟨x, fmt.nearestRoundingToUnbounded_self hx_mem,
        fmt.unboundedNormalizedSystem_ne_zero hx_mem,
        fmt.nearestRoundingToUnbounded_exact_relErrorComputedDenom_le_unitRoundoff
          hx_mem⟩
  · rcases hbracket with ⟨a, b, hadj, _hb_nonpos, ha_le_x, hx_le_b⟩
    exact
      fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_of_realOrderAdjacent_ordered_between
        hadj ⟨ha_le_x, hx_le_b⟩

/-- Source-shaped positive fixed-exponent interval version of the local
Theorem 2.2 bridge.  The hypotheses are the displayed lower and upper
normalized endpoints for one exponent bin. -/
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerInterval_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hmin : fmt.betaR ^ (e - 1) ≤ x)
    (hmax : x ≤ fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  have hmin' : fmt.normalizedValue false fmt.minNormalMantissa e ≤ x := by
    rw [fmt.normalizedValue_false_minNormalMantissa_eq]
    exact hmin
  have hmax' : x ≤ fmt.normalizedValue false fmt.maxNormalMantissa e := by
    rw [fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hmax
  exact
    fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_sameExponent_positive
      (e := e) hmin' hmax'

/-- Source-shaped negative fixed-exponent interval version of the local
Theorem 2.2 bridge.  The hypotheses are the negated upper/lower displayed
endpoints for one exponent bin. -/
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerInterval_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))) ≤ x)
    (hhi : x ≤ -(fmt.betaR ^ (e - 1))) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  have hlo' : fmt.normalizedValue true fmt.maxNormalMantissa e ≤ x := by
    rw [fmt.normalizedValue_true_eq_neg_false,
      fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hlo
  have hhi' : x ≤ fmt.normalizedValue true fmt.minNormalMantissa e := by
    rw [fmt.normalizedValue_true_eq_neg_false,
      fmt.normalizedValue_false_minNormalMantissa_eq]
    exact hhi
  exact
    fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_sameExponent_negative
      (e := e) hlo' hhi'

theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerInterval_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hmin : fmt.betaR ^ (e - 1) ≤ x)
    (hmax : x ≤ fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  have hmin' : fmt.normalizedValue false fmt.minNormalMantissa e ≤ x := by
    rw [fmt.normalizedValue_false_minNormalMantissa_eq]
    exact hmin
  have hmax' : x ≤ fmt.normalizedValue false fmt.maxNormalMantissa e := by
    rw [fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hmax
  exact
    fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_sameExponent_positive
      (e := e) hmin' hmax'

theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerInterval_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))) ≤ x)
    (hhi : x ≤ -(fmt.betaR ^ (e - 1))) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  have hlo' : fmt.normalizedValue true fmt.maxNormalMantissa e ≤ x := by
    rw [fmt.normalizedValue_true_eq_neg_false,
      fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hlo
  have hhi' : x ≤ fmt.normalizedValue true fmt.minNormalMantissa e := by
    rw [fmt.normalizedValue_true_eq_neg_false,
      fmt.normalizedValue_false_minNormalMantissa_eq]
    exact hhi
  exact
    fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_sameExponent_negative
      (e := e) hlo' hhi'

theorem exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerInterval_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hmin : fmt.betaR ^ (e - 1) ≤ x)
    (hmax : x ≤ fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            ((∃ m : ℕ,
                fmt.normalizedMantissa m ∧
                  x = fmt.normalizedValue false m e ∧ y = x) ∨
              ∃ a b : ℝ,
                fmt.realOrderAdjacentNormalized a b ∧
                  0 ≤ a ∧ a ≤ x ∧ x ≤ b ∧
                    y = nearestAdjacentRoundAway x a b) := by
  have hmin' : fmt.normalizedValue false fmt.minNormalMantissa e ≤ x := by
    rw [fmt.normalizedValue_false_minNormalMantissa_eq]
    exact hmin
  have hmax' : x ≤ fmt.normalizedValue false fmt.maxNormalMantissa e := by
    rw [fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hmax
  exact
    fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_sameExponent_positive
      (e := e) hmin' hmax'

theorem exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerInterval_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))) ≤ x)
    (hhi : x ≤ -(fmt.betaR ^ (e - 1))) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            ((∃ m : ℕ,
                fmt.normalizedMantissa m ∧
                  x = fmt.normalizedValue true m e ∧ y = x) ∨
              ∃ a b : ℝ,
                fmt.realOrderAdjacentNormalized a b ∧
                  b ≤ 0 ∧ a ≤ x ∧ x ≤ b ∧
                    y = nearestAdjacentRoundAway x a b) := by
  have hlo' : fmt.normalizedValue true fmt.maxNormalMantissa e ≤ x := by
    rw [fmt.normalizedValue_true_eq_neg_false,
      fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hlo
  have hhi' : x ≤ fmt.normalizedValue true fmt.minNormalMantissa e := by
    rw [fmt.normalizedValue_true_eq_neg_false,
      fmt.normalizedValue_false_minNormalMantissa_eq]
    exact hhi
  exact
    fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_sameExponent_negative
      (e := e) hlo' hhi'

theorem exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerInterval_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hmin : fmt.betaR ^ (e - 1) ≤ x)
    (hmax : x ≤ fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))) :
    ∃ y : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  have hmin' : fmt.normalizedValue false fmt.minNormalMantissa e ≤ x := by
    rw [fmt.normalizedValue_false_minNormalMantissa_eq]
    exact hmin
  have hmax' : x ≤ fmt.normalizedValue false fmt.maxNormalMantissa e := by
    rw [fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hmax
  exact
    fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_sameExponent_positive
      (e := e) hmin' hmax'

theorem exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerInterval_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))) ≤ x)
    (hhi : x ≤ -(fmt.betaR ^ (e - 1))) :
    ∃ y : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  have hlo' : fmt.normalizedValue true fmt.maxNormalMantissa e ≤ x := by
    rw [fmt.normalizedValue_true_eq_neg_false,
      fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hlo
  have hhi' : x ≤ fmt.normalizedValue true fmt.minNormalMantissa e := by
    rw [fmt.normalizedValue_true_eq_neg_false,
      fmt.normalizedValue_false_minNormalMantissa_eq]
    exact hhi
  exact
    fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_sameExponent_negative
      (e := e) hlo' hhi'

/-- Source-shaped positive exponent-boundary interval version of the local
Theorem 2.2 bridge.  This covers the gap between the largest value at exponent
`e` and the smallest value at exponent `e+1`. -/
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerBoundary_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))) ≤ x)
    (hhi : x ≤ fmt.betaR ^ e) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  let a := fmt.normalizedValue false fmt.maxNormalMantissa e
  let b := fmt.normalizedValue false fmt.minNormalMantissa (e + 1)
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨false, e, Or.inl ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have ha_nonneg : 0 ≤ a :=
    le_of_lt
      (fmt.normalizedValue_false_pos
        (m := fmt.maxNormalMantissa) (e := e)
        fmt.maxNormalMantissa_normalized)
  have ha_le_x : a ≤ x := by
    rw [show a = fmt.normalizedValue false fmt.maxNormalMantissa e from rfl]
    rw [fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hlo
  have hx_le_b : x ≤ b := by
    rw [show b = fmt.normalizedValue false fmt.minNormalMantissa (e + 1) from rfl]
    rw [fmt.normalizedValue_false_minNormalMantissa_succ_eq_beta_pow]
    exact hhi
  exact
    fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_of_nonneg_between
      hadj ha_nonneg ⟨ha_le_x, hx_le_b⟩

/-- Source-shaped negative exponent-boundary interval version of the local
Theorem 2.2 bridge.  This is the sign mirror of the positive boundary case. -/
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerBoundary_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : -(fmt.betaR ^ e) ≤ x)
    (hhi : x ≤ -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))))) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  let a := fmt.normalizedValue true fmt.minNormalMantissa (e + 1)
  let b := fmt.normalizedValue true fmt.maxNormalMantissa e
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨true, e, Or.inr ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have hb_nonpos : b ≤ 0 :=
    le_of_lt
      (fmt.normalizedValue_true_neg
        (m := fmt.maxNormalMantissa) (e := e)
        fmt.maxNormalMantissa_normalized)
  have ha_le_x : a ≤ x := by
    rw [show a = fmt.normalizedValue true fmt.minNormalMantissa (e + 1) from rfl]
    rw [fmt.normalizedValue_true_eq_neg_false,
      fmt.normalizedValue_false_minNormalMantissa_succ_eq_beta_pow]
    exact hlo
  have hx_le_b : x ≤ b := by
    rw [show b = fmt.normalizedValue true fmt.maxNormalMantissa e from rfl]
    rw [fmt.normalizedValue_true_eq_neg_false,
      fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hhi
  exact
    fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_of_nonpos_between
      hadj hb_nonpos ⟨ha_le_x, hx_le_b⟩

theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerBoundary_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))) ≤ x)
    (hhi : x ≤ fmt.betaR ^ e) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  let a := fmt.normalizedValue false fmt.maxNormalMantissa e
  let b := fmt.normalizedValue false fmt.minNormalMantissa (e + 1)
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨false, e, Or.inl ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have ha_nonneg : 0 ≤ a :=
    le_of_lt
      (fmt.normalizedValue_false_pos
        (m := fmt.maxNormalMantissa) (e := e)
        fmt.maxNormalMantissa_normalized)
  have ha_le_x : a ≤ x := by
    rw [show a = fmt.normalizedValue false fmt.maxNormalMantissa e from rfl]
    rw [fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hlo
  have hx_le_b : x ≤ b := by
    rw [show b = fmt.normalizedValue false fmt.minNormalMantissa (e + 1) from rfl]
    rw [fmt.normalizedValue_false_minNormalMantissa_succ_eq_beta_pow]
    exact hhi
  exact
    fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_of_nonneg_between
      hadj ha_nonneg ⟨ha_le_x, hx_le_b⟩

theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerBoundary_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : -(fmt.betaR ^ e) ≤ x)
    (hhi : x ≤ -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))))) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  let a := fmt.normalizedValue true fmt.minNormalMantissa (e + 1)
  let b := fmt.normalizedValue true fmt.maxNormalMantissa e
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨true, e, Or.inr ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have hb_nonpos : b ≤ 0 :=
    le_of_lt
      (fmt.normalizedValue_true_neg
        (m := fmt.maxNormalMantissa) (e := e)
        fmt.maxNormalMantissa_normalized)
  have ha_le_x : a ≤ x := by
    rw [show a = fmt.normalizedValue true fmt.minNormalMantissa (e + 1) from rfl]
    rw [fmt.normalizedValue_true_eq_neg_false,
      fmt.normalizedValue_false_minNormalMantissa_succ_eq_beta_pow]
    exact hlo
  have hx_le_b : x ≤ b := by
    rw [show b = fmt.normalizedValue true fmt.maxNormalMantissa e from rfl]
    rw [fmt.normalizedValue_true_eq_neg_false,
      fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hhi
  exact
    fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_of_nonpos_between
      hadj hb_nonpos ⟨ha_le_x, hx_le_b⟩

theorem exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerBoundary_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))) ≤ x)
    (hhi : x ≤ fmt.betaR ^ e) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ ∧
          ∃ a b : ℝ,
            fmt.realOrderAdjacentNormalized a b ∧
              0 ≤ a ∧ a ≤ x ∧ x ≤ b ∧
                y = nearestAdjacentRoundAway x a b := by
  let a := fmt.normalizedValue false fmt.maxNormalMantissa e
  let b := fmt.normalizedValue false fmt.minNormalMantissa (e + 1)
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨false, e, Or.inl ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have ha_nonneg : 0 ≤ a :=
    le_of_lt
      (fmt.normalizedValue_false_pos
        (m := fmt.maxNormalMantissa) (e := e)
        fmt.maxNormalMantissa_normalized)
  have ha_le_x : a ≤ x := by
    rw [show a = fmt.normalizedValue false fmt.maxNormalMantissa e from rfl]
    rw [fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hlo
  have hx_le_b : x ≤ b := by
    rw [show b = fmt.normalizedValue false fmt.minNormalMantissa (e + 1) from rfl]
    rw [fmt.normalizedValue_false_minNormalMantissa_succ_eq_beta_pow]
    exact hhi
  rcases
    fmt.nearestAdjacentRoundAway_signedRelErrorWitness_lt_of_nonneg_between
      hadj ha_nonneg ⟨ha_le_x, hx_le_b⟩ with
    ⟨δ, hδ, hwit, hround⟩
  exact
    ⟨nearestAdjacentRoundAway x a b, δ, hround, hδ, hwit,
      ⟨a, b, hadj, ha_nonneg, ha_le_x, hx_le_b, rfl⟩⟩

theorem exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerBoundary_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : -(fmt.betaR ^ e) ≤ x)
    (hhi : x ≤ -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))))) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ ∧
          ∃ a b : ℝ,
            fmt.realOrderAdjacentNormalized a b ∧
              b ≤ 0 ∧ a ≤ x ∧ x ≤ b ∧
                y = nearestAdjacentRoundAway x a b := by
  let a := fmt.normalizedValue true fmt.minNormalMantissa (e + 1)
  let b := fmt.normalizedValue true fmt.maxNormalMantissa e
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨true, e, Or.inr ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have hb_nonpos : b ≤ 0 :=
    le_of_lt
      (fmt.normalizedValue_true_neg
        (m := fmt.maxNormalMantissa) (e := e)
        fmt.maxNormalMantissa_normalized)
  have ha_le_x : a ≤ x := by
    rw [show a = fmt.normalizedValue true fmt.minNormalMantissa (e + 1) from rfl]
    rw [fmt.normalizedValue_true_eq_neg_false,
      fmt.normalizedValue_false_minNormalMantissa_succ_eq_beta_pow]
    exact hlo
  have hx_le_b : x ≤ b := by
    rw [show b = fmt.normalizedValue true fmt.maxNormalMantissa e from rfl]
    rw [fmt.normalizedValue_true_eq_neg_false,
      fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hhi
  rcases
    fmt.nearestAdjacentRoundAway_signedRelErrorWitness_lt_of_nonpos_between
      hadj hb_nonpos ⟨ha_le_x, hx_le_b⟩ with
    ⟨δ, hδ, hwit, hround⟩
  exact
    ⟨nearestAdjacentRoundAway x a b, δ, hround, hδ, hwit,
      ⟨a, b, hadj, hb_nonpos, ha_le_x, hx_le_b, rfl⟩⟩

theorem exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerBoundary_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))) ≤ x)
    (hhi : x ≤ fmt.betaR ^ e) :
    ∃ y : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  let a := fmt.normalizedValue false fmt.maxNormalMantissa e
  let b := fmt.normalizedValue false fmt.minNormalMantissa (e + 1)
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨false, e, Or.inl ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have ha_le_x : a ≤ x := by
    rw [show a = fmt.normalizedValue false fmt.maxNormalMantissa e from rfl]
    rw [fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hlo
  have hx_le_b : x ≤ b := by
    rw [show b = fmt.normalizedValue false fmt.minNormalMantissa (e + 1) from rfl]
    rw [fmt.normalizedValue_false_minNormalMantissa_succ_eq_beta_pow]
    exact hhi
  exact
    fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_of_realOrderAdjacent_ordered_between
      hadj ⟨ha_le_x, hx_le_b⟩

theorem exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerBoundary_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : -(fmt.betaR ^ e) ≤ x)
    (hhi : x ≤ -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))))) :
    ∃ y : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  let a := fmt.normalizedValue true fmt.minNormalMantissa (e + 1)
  let b := fmt.normalizedValue true fmt.maxNormalMantissa e
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨true, e, Or.inr ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have ha_le_x : a ≤ x := by
    rw [show a = fmt.normalizedValue true fmt.minNormalMantissa (e + 1) from rfl]
    rw [fmt.normalizedValue_true_eq_neg_false,
      fmt.normalizedValue_false_minNormalMantissa_succ_eq_beta_pow]
    exact hlo
  have hx_le_b : x ≤ b := by
    rw [show b = fmt.normalizedValue true fmt.maxNormalMantissa e from rfl]
    rw [fmt.normalizedValue_true_eq_neg_false,
      fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hhi
  exact
    fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_of_realOrderAdjacent_ordered_between
      hadj ⟨ha_le_x, hx_le_b⟩

/-- Source-shaped positive one-exponent slice for the local Theorem 2.2 bridge.
The interval is split at the largest normalized value with exponent `e`; the
right-hand part is the exponent-boundary gap to the smallest value at
exponent `e+1`. -/
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerSlice_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : fmt.betaR ^ (e - 1) ≤ x)
    (hhi : x ≤ fmt.betaR ^ e) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  by_cases hbin : x ≤ fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))
  · exact
      fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerInterval_positive
        (e := e) hlo hbin
  · have hgap_lo : fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))) ≤ x :=
      le_of_lt (lt_of_not_ge hbin)
    exact
      fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerBoundary_positive
        (e := e) hgap_lo hhi

/-- Source-shaped negative one-exponent slice for the local Theorem 2.2 bridge.
This is the sign mirror of the positive slice, splitting at the negated largest
normalized value with exponent `e`. -/
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerSlice_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : -(fmt.betaR ^ e) ≤ x)
    (hhi : x ≤ -(fmt.betaR ^ (e - 1))) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  by_cases hboundary : x ≤ -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))))
  · exact
      fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerBoundary_negative
        (e := e) hlo hboundary
  · have hinterval_lo :
        -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))) ≤ x :=
      le_of_lt (lt_of_not_ge hboundary)
    exact
      fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerInterval_negative
        (e := e) hinterval_lo hhi

theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerSlice_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : fmt.betaR ^ (e - 1) ≤ x)
    (hhi : x ≤ fmt.betaR ^ e) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  by_cases hbin : x ≤ fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))
  · exact
      fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerInterval_positive
        (e := e) hlo hbin
  · have hgap_lo : fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))) ≤ x :=
      le_of_lt (lt_of_not_ge hbin)
    exact
      fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerBoundary_positive
        (e := e) hgap_lo hhi

theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerSlice_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : -(fmt.betaR ^ e) ≤ x)
    (hhi : x ≤ -(fmt.betaR ^ (e - 1))) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  by_cases hboundary : x ≤ -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))))
  · exact
      fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerBoundary_negative
        (e := e) hlo hboundary
  · have hinterval_lo :
        -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))) ≤ x :=
      le_of_lt (lt_of_not_ge hboundary)
    exact
      fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerInterval_negative
        (e := e) hinterval_lo hhi

theorem exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerSlice_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : fmt.betaR ^ (e - 1) ≤ x)
    (hhi : x ≤ fmt.betaR ^ e) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            ((∃ m : ℕ,
                fmt.normalizedMantissa m ∧
                  x = fmt.normalizedValue false m e ∧ y = x) ∨
              ∃ a b : ℝ,
                fmt.realOrderAdjacentNormalized a b ∧
                  0 ≤ a ∧ a ≤ x ∧ x ≤ b ∧
                    y = nearestAdjacentRoundAway x a b) := by
  by_cases hbin : x ≤ fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))
  · exact
      fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerInterval_positive
        (e := e) hlo hbin
  · have hgap_lo : fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))) ≤ x :=
      le_of_lt (lt_of_not_ge hbin)
    rcases
      fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerBoundary_positive
        (e := e) hgap_lo hhi with
      ⟨y, δ, hround, hδ, hwit, hpolicy⟩
    exact ⟨y, δ, hround, hδ, hwit, Or.inr hpolicy⟩

theorem exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerSlice_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : -(fmt.betaR ^ e) ≤ x)
    (hhi : x ≤ -(fmt.betaR ^ (e - 1))) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            ((∃ m : ℕ,
                fmt.normalizedMantissa m ∧
                  x = fmt.normalizedValue true m e ∧ y = x) ∨
              ∃ a b : ℝ,
                fmt.realOrderAdjacentNormalized a b ∧
                  b ≤ 0 ∧ a ≤ x ∧ x ≤ b ∧
                    y = nearestAdjacentRoundAway x a b) := by
  by_cases hboundary : x ≤ -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))))
  · rcases
      fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerBoundary_negative
        (e := e) hlo hboundary with
      ⟨y, δ, hround, hδ, hwit, hpolicy⟩
    exact ⟨y, δ, hround, hδ, hwit, Or.inr hpolicy⟩
  · have hinterval_lo :
        -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))) ≤ x :=
      le_of_lt (lt_of_not_ge hboundary)
    exact
      fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerInterval_negative
        (e := e) hinterval_lo hhi

theorem exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerSlice_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : fmt.betaR ^ (e - 1) ≤ x)
    (hhi : x ≤ fmt.betaR ^ e) :
    ∃ y : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  by_cases hbin : x ≤ fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))
  · exact
      fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerInterval_positive
        (e := e) hlo hbin
  · have hgap_lo : fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))) ≤ x :=
      le_of_lt (lt_of_not_ge hbin)
    exact
      fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerBoundary_positive
        (e := e) hgap_lo hhi

theorem exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerSlice_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : -(fmt.betaR ^ e) ≤ x)
    (hhi : x ≤ -(fmt.betaR ^ (e - 1))) :
    ∃ y : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  by_cases hboundary : x ≤ -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))))
  · exact
      fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerBoundary_negative
        (e := e) hlo hboundary
  · have hinterval_lo :
        -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))) ≤ x :=
      le_of_lt (lt_of_not_ge hboundary)
    exact
      fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerInterval_negative
        (e := e) hinterval_lo hhi

/-- Global positive exponent selection for the source-shaped power slices:
every positive real lies in some interval `beta^(e-1) <= x <= beta^e`. -/
theorem exists_powerSliceExponent_positive
    {fmt : FloatingPointFormat} {x : ℝ} (hx : 0 < x) :
    ∃ e : ℤ, fmt.betaR ^ (e - 1) ≤ x ∧ x ≤ fmt.betaR ^ e := by
  have hbeta : 1 < fmt.betaR := by
    unfold betaR
    exact_mod_cast fmt.one_lt_beta
  rcases exists_mem_Ioc_zpow (K := ℝ) (x := x) (y := fmt.betaR) hx hbeta with
    ⟨n, hn⟩
  rcases Set.mem_Ioc.mp hn with ⟨hlo, hhi⟩
  refine ⟨n + 1, ?_, ?_⟩
  · have hexp : (n + 1 - 1 : ℤ) = n := by ring
    simpa [hexp] using le_of_lt hlo
  · exact hhi

/-- Global negative exponent selection, mirrored from the positive source
power-slice selection theorem. -/
theorem exists_powerSliceExponent_negative
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x < 0) :
    ∃ e : ℤ, -(fmt.betaR ^ e) ≤ x ∧ x ≤ -(fmt.betaR ^ (e - 1)) := by
  have hneg_pos : 0 < -x := by linarith
  rcases fmt.exists_powerSliceExponent_positive (x := -x) hneg_pos with
    ⟨e, hlo, hhi⟩
  exact ⟨e, by linarith, by linarith⟩

/-- Global positive unbounded-normalized nearest-rounding bridge for the
non-strict Theorem 2.2 relative-error witness. -/
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_positive
    {fmt : FloatingPointFormat} {x : ℝ} (hx : 0 < x) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases fmt.exists_powerSliceExponent_positive (x := x) hx with ⟨e, hlo, hhi⟩
  exact
    fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerSlice_positive
      (e := e) hlo hhi

/-- Global negative unbounded-normalized nearest-rounding bridge for the
non-strict Theorem 2.2 relative-error witness. -/
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_negative
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x < 0) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases fmt.exists_powerSliceExponent_negative (x := x) hx with ⟨e, hlo, hhi⟩
  exact
    fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerSlice_negative
      (e := e) hlo hhi

theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_positive
    {fmt : FloatingPointFormat} {x : ℝ} (hx : 0 < x) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases fmt.exists_powerSliceExponent_positive (x := x) hx with ⟨e, hlo, hhi⟩
  exact
    fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerSlice_positive
      (e := e) hlo hhi

theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_negative
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x < 0) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases fmt.exists_powerSliceExponent_negative (x := x) hx with ⟨e, hlo, hhi⟩
  exact
    fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerSlice_negative
      (e := e) hlo hhi

/-- Global positive unbounded-normalized nearest-rounding bridge that carries
the explicit local round-away selector evidence through exponent selection. -/
theorem exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_positive
    {fmt : FloatingPointFormat} {x : ℝ} (hx : 0 < x) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            ∃ e : ℤ,
              fmt.betaR ^ (e - 1) ≤ x ∧ x ≤ fmt.betaR ^ e ∧
                ((∃ m : ℕ,
                    fmt.normalizedMantissa m ∧
                      x = fmt.normalizedValue false m e ∧ y = x) ∨
                  ∃ a b : ℝ,
                    fmt.realOrderAdjacentNormalized a b ∧
                      0 ≤ a ∧ a ≤ x ∧ x ≤ b ∧
                        y = nearestAdjacentRoundAway x a b) := by
  rcases fmt.exists_powerSliceExponent_positive (x := x) hx with ⟨e, hlo, hhi⟩
  rcases
    fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerSlice_positive
      (e := e) hlo hhi with
    ⟨y, δ, hround, hδ, hwit, hpolicy⟩
  exact ⟨y, δ, hround, hδ, hwit, ⟨e, hlo, hhi, hpolicy⟩⟩

/-- Global negative unbounded-normalized nearest-rounding bridge that carries
the explicit local round-away selector evidence through exponent selection. -/
theorem exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_negative
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x < 0) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            ∃ e : ℤ,
              -(fmt.betaR ^ e) ≤ x ∧ x ≤ -(fmt.betaR ^ (e - 1)) ∧
                ((∃ m : ℕ,
                    fmt.normalizedMantissa m ∧
                      x = fmt.normalizedValue true m e ∧ y = x) ∨
                  ∃ a b : ℝ,
                    fmt.realOrderAdjacentNormalized a b ∧
                      b ≤ 0 ∧ a ≤ x ∧ x ≤ b ∧
                        y = nearestAdjacentRoundAway x a b) := by
  rcases fmt.exists_powerSliceExponent_negative (x := x) hx with ⟨e, hlo, hhi⟩
  rcases
    fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerSlice_negative
      (e := e) hlo hhi with
    ⟨y, δ, hround, hδ, hwit, hpolicy⟩
  exact ⟨y, δ, hround, hδ, hwit, ⟨e, hlo, hhi, hpolicy⟩⟩

/-- Global nonzero unbounded-normalized nearest-rounding bridge.  This closes
the exponent-selection part of the non-strict Theorem 2.2 foundation for `G`;
finite-format overflow/underflow and total tie-policy surfaces are separate. -/
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_nonzero
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x ≠ 0) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · exact fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_negative hneg
  · exact False.elim (hx hzero)
  · exact fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_positive hpos

theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_nonzero
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x ≠ 0) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · exact fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_negative hneg
  · exact False.elim (hx hzero)
  · exact fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_positive hpos

/-- Global nonzero unbounded-normalized nearest-rounding bridge with explicit
local round-away selector evidence.  This is still an existential source-level
bridge for `G`, not a total finite-format rounding function. -/
theorem exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_nonzero
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x ≠ 0) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            ((∃ e : ℤ,
                fmt.betaR ^ (e - 1) ≤ x ∧ x ≤ fmt.betaR ^ e ∧
                  ((∃ m : ℕ,
                      fmt.normalizedMantissa m ∧
                        x = fmt.normalizedValue false m e ∧ y = x) ∨
                    ∃ a b : ℝ,
                      fmt.realOrderAdjacentNormalized a b ∧
                        0 ≤ a ∧ a ≤ x ∧ x ≤ b ∧
                          y = nearestAdjacentRoundAway x a b)) ∨
              ∃ e : ℤ,
                -(fmt.betaR ^ e) ≤ x ∧ x ≤ -(fmt.betaR ^ (e - 1)) ∧
                  ((∃ m : ℕ,
                      fmt.normalizedMantissa m ∧
                        x = fmt.normalizedValue true m e ∧ y = x) ∨
                    ∃ a b : ℝ,
                      fmt.realOrderAdjacentNormalized a b ∧
                        b ≤ 0 ∧ a ≤ x ∧ x ≤ b ∧
                          y = nearestAdjacentRoundAway x a b)) := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · rcases
      fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_negative
        hneg with
      ⟨y, δ, hround, hδ, hwit, hpolicy⟩
    exact ⟨y, δ, hround, hδ, hwit, Or.inr hpolicy⟩
  · exact False.elim (hx hzero)
  · rcases
      fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_positive
        hpos with
      ⟨y, δ, hround, hδ, hwit, hpolicy⟩
    exact ⟨y, δ, hround, hδ, hwit, Or.inl hpolicy⟩

theorem exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_positive
    {fmt : FloatingPointFormat} {x : ℝ} (hx : 0 < x) :
    ∃ y : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  rcases fmt.exists_powerSliceExponent_positive (x := x) hx with ⟨e, hlo, hhi⟩
  exact
    fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerSlice_positive
      (e := e) hlo hhi

theorem exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_negative
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x < 0) :
    ∃ y : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  rcases fmt.exists_powerSliceExponent_negative (x := x) hx with ⟨e, hlo, hhi⟩
  exact
    fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerSlice_negative
      (e := e) hlo hhi

theorem exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_nonzero
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x ≠ 0) :
    ∃ y : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · exact fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_negative hneg
  · exact False.elim (hx hzero)
  · exact fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_positive hpos

/-- Evidence that a source-level nearest-rounded output was obtained by the
local round-away selector after choosing a signed exponent slice.  Exact
representable inputs are allowed to return themselves; non-exact inputs expose
the adjacent bracket and the value `nearestAdjacentRoundAway x a b`. -/
def sourceRoundAwayEvidence (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  (∃ e : ℤ,
    fmt.betaR ^ (e - 1) ≤ x ∧ x ≤ fmt.betaR ^ e ∧
      ((∃ m : ℕ,
          fmt.normalizedMantissa m ∧
            x = fmt.normalizedValue false m e ∧ y = x) ∨
        ∃ a b : ℝ,
          fmt.realOrderAdjacentNormalized a b ∧
            0 ≤ a ∧ a ≤ x ∧ x ≤ b ∧
              y = nearestAdjacentRoundAway x a b)) ∨
  ∃ e : ℤ,
    -(fmt.betaR ^ e) ≤ x ∧ x ≤ -(fmt.betaR ^ (e - 1)) ∧
      ((∃ m : ℕ,
          fmt.normalizedMantissa m ∧
            x = fmt.normalizedValue true m e ∧ y = x) ∨
        ∃ a b : ℝ,
          fmt.realOrderAdjacentNormalized a b ∧
            b ≤ 0 ∧ a ≤ x ∧ x ≤ b ∧
              y = nearestAdjacentRoundAway x a b)

/-- Evidence that a source-level nearest-rounded output was obtained by the
local round-to-even selector after choosing a signed exponent slice.  In an
adjacent-bracket case the evidence records the normalized mantissa of the left
endpoint in the real-order bracket; exact representable inputs return
themselves.  This is a source-facing tie-policy witness, not an IEEE operation
semantics. -/
def sourceRoundToEvenEvidence (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  (∃ e : ℤ,
    fmt.betaR ^ (e - 1) ≤ x ∧ x ≤ fmt.betaR ^ e ∧
      ((∃ m : ℕ,
          fmt.normalizedMantissa m ∧
            x = fmt.normalizedValue false m e ∧ y = x) ∨
        ∃ a b : ℝ,
          ∃ leftMantissa : ℕ,
            fmt.realOrderAdjacentNormalized a b ∧
              (∃ negative eLeft,
                fmt.normalizedMantissa leftMantissa ∧
                  a = fmt.normalizedValue negative leftMantissa eLeft) ∧
                0 ≤ a ∧ a ≤ x ∧ x ≤ b ∧
                  y = nearestAdjacentRoundToEven x a b leftMantissa)) ∨
  ∃ e : ℤ,
    -(fmt.betaR ^ e) ≤ x ∧ x ≤ -(fmt.betaR ^ (e - 1)) ∧
      ((∃ m : ℕ,
          fmt.normalizedMantissa m ∧
            x = fmt.normalizedValue true m e ∧ y = x) ∨
        ∃ a b : ℝ,
          ∃ leftMantissa : ℕ,
            fmt.realOrderAdjacentNormalized a b ∧
              (∃ negative eLeft,
                fmt.normalizedMantissa leftMantissa ∧
                  a = fmt.normalizedValue negative leftMantissa eLeft) ∧
                b ≤ 0 ∧ a ≤ x ∧ x ≤ b ∧
                  y = nearestAdjacentRoundToEven x a b leftMantissa)

theorem realOrderAdjacentNormalized_right_mantissa_parity
    {fmt : FloatingPointFormat} {a b : ℝ} {leftMantissa : ℕ}
    (hbeta : evenMantissa fmt.beta) (ht : 1 < fmt.t)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hleft :
      ∃ negative eLeft,
        fmt.normalizedMantissa leftMantissa ∧
          a = fmt.normalizedValue negative leftMantissa eLeft) :
    ∃ rightMantissa negativeRight eRight,
      fmt.normalizedMantissa rightMantissa ∧
        b = fmt.normalizedValue negativeRight rightMantissa eRight ∧
          (evenMantissa rightMantissa ↔ ¬ evenMantissa leftMantissa) := by
  rcases hleft with ⟨negativeLeft, eLeft, hmLeft, haLeft⟩
  rcases fmt.adjacentNormalized_of_realOrderAdjacentNormalized hadj with
    hsame | hboundary
  · rcases hsame with ⟨negative, m, e, hm, hmnext, hab⟩
    rcases hab with hab | hab
    · rcases hab with ⟨ha, hb⟩
      have hleft_eq : leftMantissa = m := by
        have hval :
            fmt.normalizedValue negativeLeft leftMantissa eLeft =
              fmt.normalizedValue negative m e := by
          rw [← haLeft, ha]
        exact (fmt.normalizedValue_eq_sign_exp_mantissa hmLeft hm hval).2.2
      exact
        ⟨m + 1, negative, e, hmnext, hb,
          by simpa [hleft_eq] using
            (evenMantissa_succ_iff_not_evenMantissa m)⟩
    · rcases hab with ⟨ha, hb⟩
      have hleft_eq : leftMantissa = m + 1 := by
        have hval :
            fmt.normalizedValue negativeLeft leftMantissa eLeft =
              fmt.normalizedValue negative (m + 1) e := by
          rw [← haLeft, ha]
        exact (fmt.normalizedValue_eq_sign_exp_mantissa hmLeft hmnext hval).2.2
      exact
        ⟨m, negative, e, hm, hb,
          by simpa [hleft_eq] using
            (evenMantissa_iff_not_evenMantissa_succ m)⟩
  · rcases hboundary with ⟨negative, e, hab⟩
    rcases hab with hab | hab
    · rcases hab with ⟨ha, hb⟩
      have hleft_eq : leftMantissa = fmt.maxNormalMantissa := by
        have hval :
            fmt.normalizedValue negativeLeft leftMantissa eLeft =
              fmt.normalizedValue negative fmt.maxNormalMantissa e := by
          rw [← haLeft, ha]
        exact
          (fmt.normalizedValue_eq_sign_exp_mantissa
            hmLeft fmt.maxNormalMantissa_normalized hval).2.2
      exact
        ⟨fmt.minNormalMantissa, negative, e + 1,
          fmt.minNormalMantissa_normalized, hb,
          by simpa [hleft_eq] using
            (fmt.evenMantissa_minNormalMantissa_iff_not_evenMantissa_maxNormalMantissa_of_even_beta
              hbeta ht)⟩
    · rcases hab with ⟨ha, hb⟩
      have hleft_eq : leftMantissa = fmt.minNormalMantissa := by
        have hval :
            fmt.normalizedValue negativeLeft leftMantissa eLeft =
              fmt.normalizedValue negative fmt.minNormalMantissa (e + 1) := by
          rw [← haLeft, ha]
        exact
          (fmt.normalizedValue_eq_sign_exp_mantissa
            hmLeft fmt.minNormalMantissa_normalized hval).2.2
      exact
        ⟨fmt.maxNormalMantissa, negative, e,
          fmt.maxNormalMantissa_normalized, hb,
          by simpa [hleft_eq] using
            (fmt.evenMantissa_maxNormalMantissa_iff_not_evenMantissa_minNormalMantissa_of_even_beta
              hbeta ht)⟩

theorem sourceRoundToEvenEvidence_neg
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hbeta : evenMantissa fmt.beta) (ht : 1 < fmt.t)
    (hpolicy : fmt.sourceRoundToEvenEvidence x y) :
    fmt.sourceRoundToEvenEvidence (-x) (-y) := by
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨e, hlo, hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      have hx_neg :
          -x = fmt.normalizedValue true m e := by
        rw [hx_eq]
        exact (fmt.normalizedValue_not_eq_neg false m e).symm
      have hy_neg : -y = -x := by
        rw [hy_eq]
      exact
        Or.inr ⟨e, by linarith, by linarith,
          Or.inl ⟨m, hm, hx_neg, hy_neg⟩⟩
    · rcases hbracket with
        ⟨a, b, leftMantissa, hadj, hleft, ha_nonneg,
          ha_le_x, hx_le_b, hy_eq⟩
      rcases
          fmt.realOrderAdjacentNormalized_right_mantissa_parity
            hbeta ht hadj hleft with
        ⟨rightMantissa, negativeRight, eRight, hmRight, hb_repr, hparity⟩
      have hleft_neg :
          ∃ negative eLeft,
            fmt.normalizedMantissa rightMantissa ∧
              -b = fmt.normalizedValue negative rightMantissa eLeft := by
        refine ⟨!negativeRight, eRight, hmRight, ?_⟩
        rw [hb_repr]
        exact (fmt.normalizedValue_not_eq_neg negativeRight rightMantissa eRight).symm
      have hy_neg :
          -y =
            nearestAdjacentRoundToEven (-x) (-b) (-a) rightMantissa := by
        rw [hy_eq]
        exact
          (nearestAdjacentRoundToEven_neg_of_even_right_iff_not_even_left
            (x := x) (a := a) (b := b)
            (leftMantissa := leftMantissa)
            (rightMantissa := rightMantissa) hparity).symm
      exact
        Or.inr ⟨e, by linarith, by linarith,
          Or.inr
            ⟨-b, -a, rightMantissa,
              fmt.realOrderAdjacentNormalized_neg_ordered hadj,
              hleft_neg,
              by linarith,
              by linarith,
              by linarith,
              hy_neg⟩⟩
  · rcases hneg with ⟨e, hlo, hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      have hx_neg :
          -x = fmt.normalizedValue false m e := by
        rw [hx_eq]
        exact (fmt.normalizedValue_not_eq_neg true m e).symm
      have hy_neg : -y = -x := by
        rw [hy_eq]
      exact
        Or.inl ⟨e, by linarith, by linarith,
          Or.inl ⟨m, hm, hx_neg, hy_neg⟩⟩
    · rcases hbracket with
        ⟨a, b, leftMantissa, hadj, hleft, hb_nonpos,
          ha_le_x, hx_le_b, hy_eq⟩
      rcases
          fmt.realOrderAdjacentNormalized_right_mantissa_parity
            hbeta ht hadj hleft with
        ⟨rightMantissa, negativeRight, eRight, hmRight, hb_repr, hparity⟩
      have hleft_neg :
          ∃ negative eLeft,
            fmt.normalizedMantissa rightMantissa ∧
              -b = fmt.normalizedValue negative rightMantissa eLeft := by
        refine ⟨!negativeRight, eRight, hmRight, ?_⟩
        rw [hb_repr]
        exact (fmt.normalizedValue_not_eq_neg negativeRight rightMantissa eRight).symm
      have hy_neg :
          -y =
            nearestAdjacentRoundToEven (-x) (-b) (-a) rightMantissa := by
        rw [hy_eq]
        exact
          (nearestAdjacentRoundToEven_neg_of_even_right_iff_not_even_left
            (x := x) (a := a) (b := b)
            (leftMantissa := leftMantissa)
            (rightMantissa := rightMantissa) hparity).symm
      exact
        Or.inl ⟨e, by linarith, by linarith,
          Or.inr
            ⟨-b, -a, rightMantissa,
              fmt.realOrderAdjacentNormalized_neg_ordered hadj,
              hleft_neg,
              by linarith,
              by linarith,
              by linarith,
              hy_neg⟩⟩

/-- Evidence that a source-level output was obtained by local rounding toward
negative infinity after choosing a signed exponent slice.  Exact representable
inputs return themselves; non-exact inputs expose the adjacent bracket and the
exact-endpoint-preserving local selector. -/
def sourceRoundTowardNegativeEvidence
    (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  (∃ e : ℤ,
    fmt.betaR ^ (e - 1) ≤ x ∧ x ≤ fmt.betaR ^ e ∧
      ((∃ m : ℕ,
          fmt.normalizedMantissa m ∧
            x = fmt.normalizedValue false m e ∧ y = x) ∨
        ∃ a b : ℝ,
          fmt.realOrderAdjacentNormalized a b ∧
            0 ≤ a ∧ a ≤ x ∧ x ≤ b ∧
              y = adjacentRoundTowardNegative x a b)) ∨
  ∃ e : ℤ,
    -(fmt.betaR ^ e) ≤ x ∧ x ≤ -(fmt.betaR ^ (e - 1)) ∧
      ((∃ m : ℕ,
          fmt.normalizedMantissa m ∧
            x = fmt.normalizedValue true m e ∧ y = x) ∨
        ∃ a b : ℝ,
          fmt.realOrderAdjacentNormalized a b ∧
            b ≤ 0 ∧ a ≤ x ∧ x ≤ b ∧
              y = adjacentRoundTowardNegative x a b)

/-- Evidence that a source-level output was obtained by local rounding toward
positive infinity after choosing a signed exponent slice. -/
def sourceRoundTowardPositiveEvidence
    (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  (∃ e : ℤ,
    fmt.betaR ^ (e - 1) ≤ x ∧ x ≤ fmt.betaR ^ e ∧
      ((∃ m : ℕ,
          fmt.normalizedMantissa m ∧
            x = fmt.normalizedValue false m e ∧ y = x) ∨
        ∃ a b : ℝ,
          fmt.realOrderAdjacentNormalized a b ∧
            0 ≤ a ∧ a ≤ x ∧ x ≤ b ∧
              y = adjacentRoundTowardPositive x a b)) ∨
  ∃ e : ℤ,
    -(fmt.betaR ^ e) ≤ x ∧ x ≤ -(fmt.betaR ^ (e - 1)) ∧
      ((∃ m : ℕ,
          fmt.normalizedMantissa m ∧
            x = fmt.normalizedValue true m e ∧ y = x) ∨
        ∃ a b : ℝ,
          fmt.realOrderAdjacentNormalized a b ∧
            b ≤ 0 ∧ a ≤ x ∧ x ≤ b ∧
              y = adjacentRoundTowardPositive x a b)

/-- Evidence that a source-level output was obtained by local rounding toward
zero after choosing a signed exponent slice. -/
def sourceRoundTowardZeroEvidence
    (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  (∃ e : ℤ,
    fmt.betaR ^ (e - 1) ≤ x ∧ x ≤ fmt.betaR ^ e ∧
      ((∃ m : ℕ,
          fmt.normalizedMantissa m ∧
            x = fmt.normalizedValue false m e ∧ y = x) ∨
        ∃ a b : ℝ,
          fmt.realOrderAdjacentNormalized a b ∧
            0 ≤ a ∧ a ≤ x ∧ x ≤ b ∧
              y = adjacentRoundTowardZero x a b)) ∨
  ∃ e : ℤ,
    -(fmt.betaR ^ e) ≤ x ∧ x ≤ -(fmt.betaR ^ (e - 1)) ∧
      ((∃ m : ℕ,
          fmt.normalizedMantissa m ∧
            x = fmt.normalizedValue true m e ∧ y = x) ∨
        ∃ a b : ℝ,
          fmt.realOrderAdjacentNormalized a b ∧
            b ≤ 0 ∧ a ≤ x ∧ x ≤ b ∧
              y = adjacentRoundTowardZero x a b)

theorem finiteNormalRange_ne_zero
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    x ≠ 0 := by
  intro hx_zero
  have hmin_pos := fmt.minNormalMagnitude_pos
  have hxlo := hx.1
  rw [hx_zero, abs_zero] at hxlo
  exact (not_lt_of_ge hxlo) hmin_pos

theorem sourceRoundTowardNegativeEvidence_unboundedNormalizedSystem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hpolicy : fmt.sourceRoundTowardNegativeEvidence x y) :
    fmt.unboundedNormalizedSystem y := by
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      exact ⟨false, m, e, hm, by rw [hy_eq, hx_eq]⟩
    · rcases hbracket with ⟨a, b, hadj, _ha_nonneg, _ha_le_x, _hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact fmt.adjacentRoundTowardNegative_mem_unboundedNormalized hadj
  · rcases hneg with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      exact ⟨true, m, e, hm, by rw [hy_eq, hx_eq]⟩
    · rcases hbracket with ⟨a, b, hadj, _hb_nonpos, _ha_le_x, _hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact fmt.adjacentRoundTowardNegative_mem_unboundedNormalized hadj

theorem sourceRoundTowardPositiveEvidence_unboundedNormalizedSystem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hpolicy : fmt.sourceRoundTowardPositiveEvidence x y) :
    fmt.unboundedNormalizedSystem y := by
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      exact ⟨false, m, e, hm, by rw [hy_eq, hx_eq]⟩
    · rcases hbracket with ⟨a, b, hadj, _ha_nonneg, _ha_le_x, _hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact fmt.adjacentRoundTowardPositive_mem_unboundedNormalized hadj
  · rcases hneg with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      exact ⟨true, m, e, hm, by rw [hy_eq, hx_eq]⟩
    · rcases hbracket with ⟨a, b, hadj, _hb_nonpos, _ha_le_x, _hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact fmt.adjacentRoundTowardPositive_mem_unboundedNormalized hadj

theorem sourceRoundTowardZeroEvidence_unboundedNormalizedSystem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hpolicy : fmt.sourceRoundTowardZeroEvidence x y) :
    fmt.unboundedNormalizedSystem y := by
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      exact ⟨false, m, e, hm, by rw [hy_eq, hx_eq]⟩
    · rcases hbracket with ⟨a, b, hadj, ha_nonneg, ha_le_x, hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact
        fmt.adjacentRoundTowardZero_mem_unboundedNormalized_of_nonneg_between
          hadj ha_nonneg ⟨ha_le_x, hx_le_b⟩
  · rcases hneg with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      exact ⟨true, m, e, hm, by rw [hy_eq, hx_eq]⟩
    · rcases hbracket with ⟨a, b, hadj, hb_nonpos, ha_le_x, hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact
        fmt.adjacentRoundTowardZero_mem_unboundedNormalized_of_nonpos_between
          hadj hb_nonpos ⟨ha_le_x, hx_le_b⟩

theorem sourceRoundTowardNegativeEvidence_le
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hpolicy : fmt.sourceRoundTowardNegativeEvidence x y) :
    y ≤ x := by
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨_e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨_m, _hm, _hx_eq, hy_eq⟩
      rw [hy_eq]
    · rcases hbracket with ⟨a, b, _hadj, _ha_nonneg, ha_le_x, hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact adjacentRoundTowardNegative_le_of_ordered_between ⟨ha_le_x, hx_le_b⟩
  · rcases hneg with ⟨_e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨_m, _hm, _hx_eq, hy_eq⟩
      rw [hy_eq]
    · rcases hbracket with ⟨a, b, _hadj, _hb_nonpos, ha_le_x, hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact adjacentRoundTowardNegative_le_of_ordered_between ⟨ha_le_x, hx_le_b⟩

theorem sourceRoundTowardPositiveEvidence_le
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hpolicy : fmt.sourceRoundTowardPositiveEvidence x y) :
    x ≤ y := by
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨_e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨_m, _hm, _hx_eq, hy_eq⟩
      rw [hy_eq]
    · rcases hbracket with ⟨a, b, _hadj, _ha_nonneg, ha_le_x, hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact le_adjacentRoundTowardPositive_of_ordered_between ⟨ha_le_x, hx_le_b⟩
  · rcases hneg with ⟨_e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨_m, _hm, _hx_eq, hy_eq⟩
      rw [hy_eq]
    · rcases hbracket with ⟨a, b, _hadj, _hb_nonpos, ha_le_x, hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact le_adjacentRoundTowardPositive_of_ordered_between ⟨ha_le_x, hx_le_b⟩

theorem sourceRoundTowardZeroEvidence_abs_le_abs
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hpolicy : fmt.sourceRoundTowardZeroEvidence x y) :
    |y| ≤ |x| := by
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨_e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨_m, _hm, _hx_eq, hy_eq⟩
      rw [hy_eq]
    · rcases hbracket with ⟨a, b, _hadj, ha_nonneg, ha_le_x, hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact
        adjacentRoundTowardZero_abs_le_abs_of_nonneg_between
          ha_nonneg ⟨ha_le_x, hx_le_b⟩
  · rcases hneg with ⟨_e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨_m, _hm, _hx_eq, hy_eq⟩
      rw [hy_eq]
    · rcases hbracket with ⟨a, b, hadj, hb_nonpos, ha_le_x, hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact
        fmt.adjacentRoundTowardZero_abs_le_abs_of_nonpos_between
          hadj hb_nonpos ⟨ha_le_x, hx_le_b⟩

theorem exists_sourceRoundTowardNegativeEvidence_positive
    {fmt : FloatingPointFormat} {x : ℝ} (hx : 0 < x) :
    ∃ y : ℝ, fmt.sourceRoundTowardNegativeEvidence x y := by
  rcases fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_positive
      (x := x) hx with
    ⟨_y, _δ, _hround, _hδ, _hwit, hpolicy⟩
  rcases hpolicy with ⟨e, hlo, hhi, hexact | hbracket⟩
  · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
    exact ⟨x, Or.inl ⟨e, hlo, hhi, Or.inl ⟨m, hm, hx_eq, rfl⟩⟩⟩
  · rcases hbracket with ⟨a, b, hadj, ha_nonneg, ha_le_x, hx_le_b, _hy_eq⟩
    exact
      ⟨adjacentRoundTowardNegative x a b,
        Or.inl ⟨e, hlo, hhi,
          Or.inr ⟨a, b, hadj, ha_nonneg, ha_le_x, hx_le_b, rfl⟩⟩⟩

theorem exists_sourceRoundTowardNegativeEvidence_negative
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x < 0) :
    ∃ y : ℝ, fmt.sourceRoundTowardNegativeEvidence x y := by
  rcases fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_negative
      (x := x) hx with
    ⟨_y, _δ, _hround, _hδ, _hwit, hpolicy⟩
  rcases hpolicy with ⟨e, hlo, hhi, hexact | hbracket⟩
  · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
    exact ⟨x, Or.inr ⟨e, hlo, hhi, Or.inl ⟨m, hm, hx_eq, rfl⟩⟩⟩
  · rcases hbracket with ⟨a, b, hadj, hb_nonpos, ha_le_x, hx_le_b, _hy_eq⟩
    exact
      ⟨adjacentRoundTowardNegative x a b,
        Or.inr ⟨e, hlo, hhi,
          Or.inr ⟨a, b, hadj, hb_nonpos, ha_le_x, hx_le_b, rfl⟩⟩⟩

theorem exists_sourceRoundTowardPositiveEvidence_positive
    {fmt : FloatingPointFormat} {x : ℝ} (hx : 0 < x) :
    ∃ y : ℝ, fmt.sourceRoundTowardPositiveEvidence x y := by
  rcases fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_positive
      (x := x) hx with
    ⟨_y, _δ, _hround, _hδ, _hwit, hpolicy⟩
  rcases hpolicy with ⟨e, hlo, hhi, hexact | hbracket⟩
  · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
    exact ⟨x, Or.inl ⟨e, hlo, hhi, Or.inl ⟨m, hm, hx_eq, rfl⟩⟩⟩
  · rcases hbracket with ⟨a, b, hadj, ha_nonneg, ha_le_x, hx_le_b, _hy_eq⟩
    exact
      ⟨adjacentRoundTowardPositive x a b,
        Or.inl ⟨e, hlo, hhi,
          Or.inr ⟨a, b, hadj, ha_nonneg, ha_le_x, hx_le_b, rfl⟩⟩⟩

theorem exists_sourceRoundTowardPositiveEvidence_negative
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x < 0) :
    ∃ y : ℝ, fmt.sourceRoundTowardPositiveEvidence x y := by
  rcases fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_negative
      (x := x) hx with
    ⟨_y, _δ, _hround, _hδ, _hwit, hpolicy⟩
  rcases hpolicy with ⟨e, hlo, hhi, hexact | hbracket⟩
  · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
    exact ⟨x, Or.inr ⟨e, hlo, hhi, Or.inl ⟨m, hm, hx_eq, rfl⟩⟩⟩
  · rcases hbracket with ⟨a, b, hadj, hb_nonpos, ha_le_x, hx_le_b, _hy_eq⟩
    exact
      ⟨adjacentRoundTowardPositive x a b,
        Or.inr ⟨e, hlo, hhi,
          Or.inr ⟨a, b, hadj, hb_nonpos, ha_le_x, hx_le_b, rfl⟩⟩⟩

theorem exists_sourceRoundTowardZeroEvidence_positive
    {fmt : FloatingPointFormat} {x : ℝ} (hx : 0 < x) :
    ∃ y : ℝ, fmt.sourceRoundTowardZeroEvidence x y := by
  rcases fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_positive
      (x := x) hx with
    ⟨_y, _δ, _hround, _hδ, _hwit, hpolicy⟩
  rcases hpolicy with ⟨e, hlo, hhi, hexact | hbracket⟩
  · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
    exact ⟨x, Or.inl ⟨e, hlo, hhi, Or.inl ⟨m, hm, hx_eq, rfl⟩⟩⟩
  · rcases hbracket with ⟨a, b, hadj, ha_nonneg, ha_le_x, hx_le_b, _hy_eq⟩
    exact
      ⟨adjacentRoundTowardZero x a b,
        Or.inl ⟨e, hlo, hhi,
          Or.inr ⟨a, b, hadj, ha_nonneg, ha_le_x, hx_le_b, rfl⟩⟩⟩

theorem exists_sourceRoundTowardZeroEvidence_negative
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x < 0) :
    ∃ y : ℝ, fmt.sourceRoundTowardZeroEvidence x y := by
  rcases fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_negative
      (x := x) hx with
    ⟨_y, _δ, _hround, _hδ, _hwit, hpolicy⟩
  rcases hpolicy with ⟨e, hlo, hhi, hexact | hbracket⟩
  · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
    exact ⟨x, Or.inr ⟨e, hlo, hhi, Or.inl ⟨m, hm, hx_eq, rfl⟩⟩⟩
  · rcases hbracket with ⟨a, b, hadj, hb_nonpos, ha_le_x, hx_le_b, _hy_eq⟩
    exact
      ⟨adjacentRoundTowardZero x a b,
        Or.inr ⟨e, hlo, hhi,
          Or.inr ⟨a, b, hadj, hb_nonpos, ha_le_x, hx_le_b, rfl⟩⟩⟩

theorem exists_sourceRoundTowardNegativeEvidence_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ y : ℝ, fmt.sourceRoundTowardNegativeEvidence x y := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · exact fmt.exists_sourceRoundTowardNegativeEvidence_negative hneg
  · exact False.elim (fmt.finiteNormalRange_ne_zero hx hzero)
  · exact fmt.exists_sourceRoundTowardNegativeEvidence_positive hpos

theorem exists_sourceRoundTowardPositiveEvidence_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ y : ℝ, fmt.sourceRoundTowardPositiveEvidence x y := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · exact fmt.exists_sourceRoundTowardPositiveEvidence_negative hneg
  · exact False.elim (fmt.finiteNormalRange_ne_zero hx hzero)
  · exact fmt.exists_sourceRoundTowardPositiveEvidence_positive hpos

theorem exists_sourceRoundTowardZeroEvidence_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ y : ℝ, fmt.sourceRoundTowardZeroEvidence x y := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · exact fmt.exists_sourceRoundTowardZeroEvidence_negative hneg
  · exact False.elim (fmt.finiteNormalRange_ne_zero hx hzero)
  · exact fmt.exists_sourceRoundTowardZeroEvidence_positive hpos

theorem sourceRoundAwayEvidence_relErrorComputedDenom_le_unitRoundoff
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteNormalRange x)
    (hpolicy : fmt.sourceRoundAwayEvidence x y) :
    y ≠ 0 ∧ relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  have hx_ne := fmt.finiteNormalRange_ne_zero hx
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      have hx_unbounded : fmt.unboundedNormalizedSystem x :=
        ⟨false, m, e, hm, hx_eq⟩
      constructor
      · rw [hy_eq]
        exact hx_ne
      · simpa [hy_eq] using
          fmt.nearestRoundingToUnbounded_exact_relErrorComputedDenom_le_unitRoundoff
            hx_unbounded
    · rcases hbracket with ⟨a, b, hadj, _ha_nonneg, ha_le_x, hx_le_b, hy_eq⟩
      have hround : fmt.nearestRoundingToUnbounded x y := by
        rw [hy_eq]
        exact
          fmt.nearestAdjacentRoundAway_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
            hadj ⟨ha_le_x, hx_le_b⟩
      have hy_ne : y ≠ 0 :=
        fmt.unboundedNormalizedSystem_ne_zero (nearestRoundingIn_mem hround)
      have hrel :=
        fmt.nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_of_realOrderAdjacent_between
          hround hadj (Or.inl ⟨ha_le_x, hx_le_b⟩)
      exact ⟨hy_ne, hrel⟩
  · rcases hneg with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      have hx_unbounded : fmt.unboundedNormalizedSystem x :=
        ⟨true, m, e, hm, hx_eq⟩
      constructor
      · rw [hy_eq]
        exact hx_ne
      · simpa [hy_eq] using
          fmt.nearestRoundingToUnbounded_exact_relErrorComputedDenom_le_unitRoundoff
            hx_unbounded
    · rcases hbracket with ⟨a, b, hadj, _hb_nonpos, ha_le_x, hx_le_b, hy_eq⟩
      have hround : fmt.nearestRoundingToUnbounded x y := by
        rw [hy_eq]
        exact
          fmt.nearestAdjacentRoundAway_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
            hadj ⟨ha_le_x, hx_le_b⟩
      have hy_ne : y ≠ 0 :=
        fmt.unboundedNormalizedSystem_ne_zero (nearestRoundingIn_mem hround)
      have hrel :=
        fmt.nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_of_realOrderAdjacent_between
          hround hadj (Or.inl ⟨ha_le_x, hx_le_b⟩)
      exact ⟨hy_ne, hrel⟩

theorem sourceRoundToEvenEvidence_nearestRoundingToUnbounded
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hpolicy : fmt.sourceRoundToEvenEvidence x y) :
    fmt.nearestRoundingToUnbounded x y := by
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      have hx_unbounded : fmt.unboundedNormalizedSystem x :=
        ⟨false, m, e, hm, hx_eq⟩
      rw [hy_eq]
      exact fmt.nearestRoundingToUnbounded_self hx_unbounded
    · rcases hbracket with
        ⟨a, b, leftMantissa, hadj, _hleft, _ha_nonneg, ha_le_x, hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact
        fmt.nearestAdjacentRoundToEven_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
          leftMantissa hadj ⟨ha_le_x, hx_le_b⟩
  · rcases hneg with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      have hx_unbounded : fmt.unboundedNormalizedSystem x :=
        ⟨true, m, e, hm, hx_eq⟩
      rw [hy_eq]
      exact fmt.nearestRoundingToUnbounded_self hx_unbounded
    · rcases hbracket with
        ⟨a, b, leftMantissa, hadj, _hleft, _hb_nonpos, ha_le_x, hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact
        fmt.nearestAdjacentRoundToEven_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
          leftMantissa hadj ⟨ha_le_x, hx_le_b⟩

theorem sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hpolicy : fmt.sourceRoundToEvenEvidence x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hstrict : a < x ∧ x < b)
    (hleftCloser : |x - a| < |x - b|) :
    y = a := by
  have hnot_exact (hx_mem : fmt.unboundedNormalizedSystem x) : False := by
    exact (hadj.2.2.2 x hx_mem) (Or.inl hstrict)
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
      exact False.elim (hnot_exact ⟨false, m, e, hm, hx_eq⟩)
    · rcases hbracket with
        ⟨c, d, _m, hcd, _hleft, _hc_nonneg, hc_le_x, hx_le_d, hy_eq⟩
      rcases
          fmt.realOrderAdjacentNormalized_bracket_unique_of_strict_between
            hadj hcd hstrict ⟨hc_le_x, hx_le_d⟩ with
        ⟨hc_eq, hd_eq⟩
      subst c
      subst d
      rw [hy_eq]
      exact nearestAdjacentRoundToEven_eq_left_of_left_closer hleftCloser
  · rcases hneg with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
      exact False.elim (hnot_exact ⟨true, m, e, hm, hx_eq⟩)
    · rcases hbracket with
        ⟨c, d, _m, hcd, _hleft, _hd_nonpos, hc_le_x, hx_le_d, hy_eq⟩
      rcases
          fmt.realOrderAdjacentNormalized_bracket_unique_of_strict_between
            hadj hcd hstrict ⟨hc_le_x, hx_le_d⟩ with
        ⟨hc_eq, hd_eq⟩
      subst c
      subst d
      rw [hy_eq]
      exact nearestAdjacentRoundToEven_eq_left_of_left_closer hleftCloser

theorem sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hpolicy : fmt.sourceRoundToEvenEvidence x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hstrict : a < x ∧ x < b)
    (hrightCloser : |x - b| < |x - a|) :
    y = b := by
  have hnot_exact (hx_mem : fmt.unboundedNormalizedSystem x) : False := by
    exact (hadj.2.2.2 x hx_mem) (Or.inl hstrict)
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
      exact False.elim (hnot_exact ⟨false, m, e, hm, hx_eq⟩)
    · rcases hbracket with
        ⟨c, d, _m, hcd, _hleft, _hc_nonneg, hc_le_x, hx_le_d, hy_eq⟩
      rcases
          fmt.realOrderAdjacentNormalized_bracket_unique_of_strict_between
            hadj hcd hstrict ⟨hc_le_x, hx_le_d⟩ with
        ⟨hc_eq, hd_eq⟩
      subst c
      subst d
      rw [hy_eq]
      exact nearestAdjacentRoundToEven_eq_right_of_right_closer hrightCloser
  · rcases hneg with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
      exact False.elim (hnot_exact ⟨true, m, e, hm, hx_eq⟩)
    · rcases hbracket with
        ⟨c, d, _m, hcd, _hleft, _hd_nonpos, hc_le_x, hx_le_d, hy_eq⟩
      rcases
          fmt.realOrderAdjacentNormalized_bracket_unique_of_strict_between
            hadj hcd hstrict ⟨hc_le_x, hx_le_d⟩ with
        ⟨hc_eq, hd_eq⟩
      subst c
      subst d
      rw [hy_eq]
      exact nearestAdjacentRoundToEven_eq_right_of_right_closer hrightCloser

theorem sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_tie_even
    {fmt : FloatingPointFormat} {x y a b : ℝ} {leftMantissa : ℕ}
    {negative : Bool} {eLeft : ℤ}
    (hpolicy : fmt.sourceRoundToEvenEvidence x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hstrict : a < x ∧ x < b)
    (hleftMantissa : fmt.normalizedMantissa leftMantissa)
    (hleft : a = fmt.normalizedValue negative leftMantissa eLeft)
    (htie : |x - a| = |x - b|)
    (heven : evenMantissa leftMantissa) :
    y = a := by
  have hnot_exact (hx_mem : fmt.unboundedNormalizedSystem x) : False := by
    exact (hadj.2.2.2 x hx_mem) (Or.inl hstrict)
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
      exact False.elim (hnot_exact ⟨false, m, e, hm, hx_eq⟩)
    · rcases hbracket with
        ⟨c, d, m, hcd, hleft', _hc_nonneg, hc_le_x, hx_le_d, hy_eq⟩
      rcases
          fmt.realOrderAdjacentNormalized_bracket_unique_of_strict_between
            hadj hcd hstrict ⟨hc_le_x, hx_le_d⟩ with
        ⟨hc_eq, hd_eq⟩
      subst c
      subst d
      rcases hleft' with ⟨negative', eLeft', hm', hc_repr⟩
      have hm_eq : m = leftMantissa := by
        have hval :
            fmt.normalizedValue negative' m eLeft' =
              fmt.normalizedValue negative leftMantissa eLeft := by
          rw [← hc_repr, ← hleft]
        exact
          (fmt.normalizedValue_eq_sign_exp_mantissa
            hm' hleftMantissa hval).2.2
      have heven_m : evenMantissa m := by
        simpa [hm_eq] using heven
      rw [hy_eq]
      exact nearestAdjacentRoundToEven_eq_left_of_tie_even htie heven_m
  · rcases hneg with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
      exact False.elim (hnot_exact ⟨true, m, e, hm, hx_eq⟩)
    · rcases hbracket with
        ⟨c, d, m, hcd, hleft', _hd_nonpos, hc_le_x, hx_le_d, hy_eq⟩
      rcases
          fmt.realOrderAdjacentNormalized_bracket_unique_of_strict_between
            hadj hcd hstrict ⟨hc_le_x, hx_le_d⟩ with
        ⟨hc_eq, hd_eq⟩
      subst c
      subst d
      rcases hleft' with ⟨negative', eLeft', hm', hc_repr⟩
      have hm_eq : m = leftMantissa := by
        have hval :
            fmt.normalizedValue negative' m eLeft' =
              fmt.normalizedValue negative leftMantissa eLeft := by
          rw [← hc_repr, ← hleft]
        exact
          (fmt.normalizedValue_eq_sign_exp_mantissa
            hm' hleftMantissa hval).2.2
      have heven_m : evenMantissa m := by
        simpa [hm_eq] using heven
      rw [hy_eq]
      exact nearestAdjacentRoundToEven_eq_left_of_tie_even htie heven_m

theorem sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
    {fmt : FloatingPointFormat} {x y a b : ℝ} {leftMantissa : ℕ}
    {negative : Bool} {eLeft : ℤ}
    (hpolicy : fmt.sourceRoundToEvenEvidence x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hstrict : a < x ∧ x < b)
    (hleftMantissa : fmt.normalizedMantissa leftMantissa)
    (hleft : a = fmt.normalizedValue negative leftMantissa eLeft)
    (htie : |x - a| = |x - b|)
    (hodd : ¬ evenMantissa leftMantissa) :
    y = b := by
  have hnot_exact (hx_mem : fmt.unboundedNormalizedSystem x) : False := by
    exact (hadj.2.2.2 x hx_mem) (Or.inl hstrict)
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
      exact False.elim (hnot_exact ⟨false, m, e, hm, hx_eq⟩)
    · rcases hbracket with
        ⟨c, d, m, hcd, hleft', _hc_nonneg, hc_le_x, hx_le_d, hy_eq⟩
      rcases
          fmt.realOrderAdjacentNormalized_bracket_unique_of_strict_between
            hadj hcd hstrict ⟨hc_le_x, hx_le_d⟩ with
        ⟨hc_eq, hd_eq⟩
      subst c
      subst d
      rcases hleft' with ⟨negative', eLeft', hm', hc_repr⟩
      have hm_eq : m = leftMantissa := by
        have hval :
            fmt.normalizedValue negative' m eLeft' =
              fmt.normalizedValue negative leftMantissa eLeft := by
          rw [← hc_repr, ← hleft]
        exact
          (fmt.normalizedValue_eq_sign_exp_mantissa
            hm' hleftMantissa hval).2.2
      have hodd_m : ¬ evenMantissa m := by
        simpa [hm_eq] using hodd
      rw [hy_eq]
      exact nearestAdjacentRoundToEven_eq_right_of_tie_odd htie hodd_m
  · rcases hneg with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
      exact False.elim (hnot_exact ⟨true, m, e, hm, hx_eq⟩)
    · rcases hbracket with
        ⟨c, d, m, hcd, hleft', _hd_nonpos, hc_le_x, hx_le_d, hy_eq⟩
      rcases
          fmt.realOrderAdjacentNormalized_bracket_unique_of_strict_between
            hadj hcd hstrict ⟨hc_le_x, hx_le_d⟩ with
        ⟨hc_eq, hd_eq⟩
      subst c
      subst d
      rcases hleft' with ⟨negative', eLeft', hm', hc_repr⟩
      have hm_eq : m = leftMantissa := by
        have hval :
            fmt.normalizedValue negative' m eLeft' =
              fmt.normalizedValue negative leftMantissa eLeft := by
          rw [← hc_repr, ← hleft]
        exact
          (fmt.normalizedValue_eq_sign_exp_mantissa
            hm' hleftMantissa hval).2.2
      have hodd_m : ¬ evenMantissa m := by
        simpa [hm_eq] using hodd
      rw [hy_eq]
      exact nearestAdjacentRoundToEven_eq_right_of_tie_odd htie hodd_m

theorem sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx_mem : fmt.unboundedNormalizedSystem x)
    (hpolicy : fmt.sourceRoundToEvenEvidence x y) :
    y = x := by
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨_m, _hm, _hx_eq, hy_eq⟩
      exact hy_eq
    · rcases hbracket with
        ⟨a, b, leftMantissa, hadj, _hleft, _ha_nonneg,
          ha_le_x, hx_le_b, hy_eq⟩
      rcases lt_or_eq_of_le ha_le_x with ha_lt_x | hax
      · rcases lt_or_eq_of_le hx_le_b with hx_lt_b | hxb
        · exfalso
          exact hadj.2.2.2 x hx_mem (Or.inl ⟨ha_lt_x, hx_lt_b⟩)
        · rw [hy_eq, hxb]
          exact nearestAdjacentRoundToEven_eq_right_endpoint a b leftMantissa
      · rw [hy_eq, ← hax]
        exact nearestAdjacentRoundToEven_eq_left_endpoint a b leftMantissa
  · rcases hneg with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨_m, _hm, _hx_eq, hy_eq⟩
      exact hy_eq
    · rcases hbracket with
        ⟨a, b, leftMantissa, hadj, _hleft, _hb_nonpos,
          ha_le_x, hx_le_b, hy_eq⟩
      rcases lt_or_eq_of_le ha_le_x with ha_lt_x | hax
      · rcases lt_or_eq_of_le hx_le_b with hx_lt_b | hxb
        · exfalso
          exact hadj.2.2.2 x hx_mem (Or.inl ⟨ha_lt_x, hx_lt_b⟩)
        · rw [hy_eq, hxb]
          exact nearestAdjacentRoundToEven_eq_right_endpoint a b leftMantissa
      · rw [hy_eq, ← hax]
        exact nearestAdjacentRoundToEven_eq_left_endpoint a b leftMantissa

theorem sourceRoundToEvenEvidence_eq_nearest_of_realOrderAdjacent_between
    {fmt : FloatingPointFormat} {x y a b : ℝ} {leftMantissa : ℕ}
    (hpolicy : fmt.sourceRoundToEvenEvidence x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hleft :
      ∃ negative eLeft,
        fmt.normalizedMantissa leftMantissa ∧
          a = fmt.normalizedValue negative leftMantissa eLeft)
    (hbetween : a ≤ x ∧ x ≤ b) :
    y = nearestAdjacentRoundToEven x a b leftMantissa := by
  rcases lt_or_eq_of_le hbetween.1 with ha_lt_x | hax
  · rcases lt_or_eq_of_le hbetween.2 with hx_lt_b | hxb
    · by_cases hleftCloser : |x - a| < |x - b|
      · rw [
          sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
            hpolicy hadj ⟨ha_lt_x, hx_lt_b⟩ hleftCloser,
          nearestAdjacentRoundToEven_eq_left_of_left_closer hleftCloser]
      · by_cases hrightCloser : |x - b| < |x - a|
        · rw [
            sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
              hpolicy hadj ⟨ha_lt_x, hx_lt_b⟩ hrightCloser,
            nearestAdjacentRoundToEven_eq_right_of_right_closer hrightCloser]
        · have htie : |x - a| = |x - b| := by
            exact le_antisymm (le_of_not_gt hrightCloser)
              (le_of_not_gt hleftCloser)
          rcases hleft with ⟨negative, eLeft, hm, ha_repr⟩
          by_cases heven : evenMantissa leftMantissa
          · rw [
              sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_tie_even
                hpolicy hadj ⟨ha_lt_x, hx_lt_b⟩ hm ha_repr htie heven,
              nearestAdjacentRoundToEven_eq_left_of_tie_even htie heven]
          · rw [
              sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
                hpolicy hadj ⟨ha_lt_x, hx_lt_b⟩ hm ha_repr htie heven,
              nearestAdjacentRoundToEven_eq_right_of_tie_odd htie heven]
    · have hx_mem : fmt.unboundedNormalizedSystem x := by
        simpa [hxb] using hadj.2.1
      rw [
        sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem hx_mem hpolicy,
        hxb,
        nearestAdjacentRoundToEven_eq_right_endpoint]
  · have hx_mem : fmt.unboundedNormalizedSystem x := by
      simpa [← hax] using hadj.1
    rw [
      sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem hx_mem hpolicy,
      ← hax,
      nearestAdjacentRoundToEven_eq_left_endpoint]

/-- Source round-to-even evidence can only select one of the two endpoints of
an ordered adjacent bracket that contains the source value. -/
theorem sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hpolicy : fmt.sourceRoundToEvenEvidence x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : a ≤ x ∧ x ≤ b) :
    y = a ∨ y = b :=
  fmt.nearestRoundingToUnbounded_eq_left_or_right_of_realOrderAdjacent_ordered_between
    (fmt.sourceRoundToEvenEvidence_nearestRoundingToUnbounded hpolicy)
    hadj hbetween

/-- Same-exponent endpoint-index form of source round-to-even selection.

If the adjacent bracket endpoints are `q` and `q+1` on the same normalized
lattice, any normalized output with the same sign and exponent has mantissa
`q` or `q+1`.  This is the source-policy bridge needed by the binary
guard-word branch of the C4.4 addition roundoff-error proof. -/
theorem sourceRoundToEvenEvidence_sameExponent_mantissa_eq_or_succ_of_bracket
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    {negative : Bool} {l q : ℕ} {e : ℤ}
    (hpolicy : fmt.sourceRoundToEvenEvidence x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : a ≤ x ∧ x ≤ b)
    (hl : fmt.normalizedMantissa l)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1))
    (hy : y = fmt.normalizedValue negative l e)
    (ha : a = fmt.normalizedValue negative q e)
    (hb : b = fmt.normalizedValue negative (q + 1) e) :
    l = q ∨ l = q + 1 := by
  rcases
      fmt.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between
        hpolicy hadj hbetween with hleft | hright
  · have hval :
        fmt.normalizedValue negative l e =
          fmt.normalizedValue negative q e := by
      rw [← hy, hleft, ha]
    exact Or.inl (fmt.normalizedValue_eq_sign_exp_mantissa hl hq hval).2.2
  · have hval :
        fmt.normalizedValue negative l e =
          fmt.normalizedValue negative (q + 1) e := by
      rw [← hy, hright, hb]
    exact Or.inr (fmt.normalizedValue_eq_sign_exp_mantissa hl hqs hval).2.2

/-- Positive aligned binary guard-word source evidence selects the lower
quotient endpoint or, only in the non-exact case, the upper successor endpoint.

This composes the concrete quotient bracket for `k = beta*q+r`, source
round-to-even endpoint selection, and normalized-value uniqueness.  It is the
local bridge needed before applying
`binaryGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil`. -/
theorem sourceRoundToEvenEvidence_positive_binaryGuard_mantissa_eq_or_succ_of_bracket
    {fmt : FloatingPointFormat} {y : ℝ} {k q r l : ℕ} {e : ℤ}
    (hk : k = fmt.beta * q + r)
    (hr : r < fmt.beta)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) y)
    (hl : fmt.normalizedMantissa l)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1))
    (hy : y = fmt.normalizedValue false l (e + 1)) :
    l = q ∨ (l = q + 1 ∧ r ≠ 0) := by
  by_cases hrzero : r = 0
  · have hk_exact : k = fmt.beta * q := by
      rw [hk, hrzero, Nat.add_zero]
    have hsource_eq_left :
        (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) =
          fmt.normalizedValue false q (e + 1) := by
      rw [fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
      simp [signValue]
      have hk_cast : (k : ℝ) = (((fmt.beta * q : ℕ) : ℝ)) := by
        exact_mod_cast hk_exact
      rw [hk_cast]
      simp [Nat.cast_mul]
    have hx_mem :
        fmt.unboundedNormalizedSystem
          ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) := by
      exact ⟨false, q, e + 1, hq, hsource_eq_left⟩
    have hy_self :
        y = (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) :=
      fmt.sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem
        hx_mem hpolicy
    have hval :
        fmt.normalizedValue false l (e + 1) =
          fmt.normalizedValue false q (e + 1) := by
      rw [← hy, hy_self, hsource_eq_left]
    exact Or.inl (fmt.normalizedValue_eq_sign_exp_mantissa hl hq hval).2.2
  · have hadj :
        fmt.realOrderAdjacentNormalized
          (fmt.normalizedValue false q (e + 1))
          (fmt.normalizedValue false (q + 1) (e + 1)) :=
      fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
        ⟨false, q, e + 1, hq, hqs, Or.inl ⟨rfl, rfl⟩⟩
    have hbetween :=
      fmt.binaryGuardSource_between_sameExponentEndpoints_positive
        (k := k) (q := q) (r := r) (e := e) hk hr
    have hsel :
        l = q ∨ l = q + 1 :=
      fmt.sourceRoundToEvenEvidence_sameExponent_mantissa_eq_or_succ_of_bracket
        (a := fmt.normalizedValue false q (e + 1))
        (b := fmt.normalizedValue false (q + 1) (e + 1))
        hpolicy hadj hbetween hl hq hqs hy rfl rfl
    rcases hsel with hlq | hlqs
    · exact Or.inl hlq
    · exact Or.inr ⟨hlqs, hrzero⟩

/-- Positive aligned binary guard-word source evidence gives the `t`-digit
coefficient gap required for finite representability of the local add error. -/
theorem sourceRoundToEvenEvidence_positive_binaryGuard_coeffDiff_natAbs_lt_mantissaBound
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {k q r l : ℕ} {e : ℤ}
    (hk : k = fmt.beta * q + r)
    (hr : r < fmt.beta)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) y)
    (hl : fmt.normalizedMantissa l)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1))
    (hy : y = fmt.normalizedValue false l (e + 1)) :
    (((k : ℤ) - ((fmt.beta * l : ℕ) : ℤ)).natAbs <
      fmt.beta ^ fmt.t) := by
  have hsel :=
    fmt.sourceRoundToEvenEvidence_positive_binaryGuard_mantissa_eq_or_succ_of_bracket
      (k := k) (q := q) (r := r) (l := l) (e := e)
      hk hr hpolicy hl hq hqs hy
  exact
    fmt.binaryGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil
      hbeta hk hr hsel

/-- Negative aligned binary guard-word source evidence selects the quotient
endpoint or, only in the non-exact case, the successor endpoint.

The real-order bracket is reversed for negative values, so this proof reads the
left/right endpoint cases directly instead of using the positive-oriented
same-exponent helper. -/
theorem sourceRoundToEvenEvidence_negative_binaryGuard_mantissa_eq_or_succ_of_bracket
    {fmt : FloatingPointFormat} {y : ℝ} {k q r l : ℕ} {e : ℤ}
    (hk : k = fmt.beta * q + r)
    (hr : r < fmt.beta)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) y)
    (hl : fmt.normalizedMantissa l)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1))
    (hy : y = fmt.normalizedValue true l (e + 1)) :
    l = q ∨ (l = q + 1 ∧ r ≠ 0) := by
  by_cases hrzero : r = 0
  · have hk_exact : k = fmt.beta * q := by
      rw [hk, hrzero, Nat.add_zero]
    have hsource_eq_right :
        fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ)) =
          fmt.normalizedValue true q (e + 1) := by
      rw [fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
      simp [signValue]
      have hk_cast : (k : ℝ) = (((fmt.beta * q : ℕ) : ℝ)) := by
        exact_mod_cast hk_exact
      rw [hk_cast]
      simp [Nat.cast_mul]
    have hx_mem :
        fmt.unboundedNormalizedSystem
          (fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ))) := by
      exact ⟨true, q, e + 1, hq, hsource_eq_right⟩
    have hy_self :
        y = fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ)) :=
      fmt.sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem
        hx_mem hpolicy
    have hval :
        fmt.normalizedValue true l (e + 1) =
          fmt.normalizedValue true q (e + 1) := by
      rw [← hy, hy_self, hsource_eq_right]
    exact Or.inl (fmt.normalizedValue_eq_sign_exp_mantissa hl hq hval).2.2
  · have hadj :
        fmt.realOrderAdjacentNormalized
          (fmt.normalizedValue true (q + 1) (e + 1))
          (fmt.normalizedValue true q (e + 1)) :=
      fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
        ⟨true, q, e + 1, hq, hqs, Or.inr ⟨rfl, rfl⟩⟩
    have hbetween :=
      fmt.binaryGuardSource_between_sameExponentEndpoints_negative
        (k := k) (q := q) (r := r) (e := e) hk hr
    rcases
        fmt.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between
          hpolicy hadj hbetween with hleft | hright
    · have hval :
          fmt.normalizedValue true l (e + 1) =
            fmt.normalizedValue true (q + 1) (e + 1) := by
        rw [← hy, hleft]
      exact Or.inr
        ⟨(fmt.normalizedValue_eq_sign_exp_mantissa hl hqs hval).2.2,
          hrzero⟩
    · have hval :
          fmt.normalizedValue true l (e + 1) =
            fmt.normalizedValue true q (e + 1) := by
        rw [← hy, hright]
      exact Or.inl (fmt.normalizedValue_eq_sign_exp_mantissa hl hq hval).2.2

/-- Negative aligned binary guard-word source evidence gives the same
`t`-digit coefficient gap as the positive branch. -/
theorem sourceRoundToEvenEvidence_negative_binaryGuard_coeffDiff_natAbs_lt_mantissaBound
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {k q r l : ℕ} {e : ℤ}
    (hk : k = fmt.beta * q + r)
    (hr : r < fmt.beta)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) y)
    (hl : fmt.normalizedMantissa l)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1))
    (hy : y = fmt.normalizedValue true l (e + 1)) :
    (((k : ℤ) - ((fmt.beta * l : ℕ) : ℤ)).natAbs <
      fmt.beta ^ fmt.t) := by
  have hsel :=
    fmt.sourceRoundToEvenEvidence_negative_binaryGuard_mantissa_eq_or_succ_of_bracket
      (k := k) (q := q) (r := r) (l := l) (e := e)
      hk hr hpolicy hl hq hqs hy
  exact
    fmt.binaryGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil
      hbeta hk hr hsel

/-- Positive aligned binary guard-word source evidence gives finite
representability of the local roundoff error once the rounded endpoint is
represented on the same next-exponent lattice. -/
theorem sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {k q r l : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hk : k = fmt.beta * q + r)
    (hr : r < fmt.beta)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) y)
    (hl : fmt.normalizedMantissa l)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1))
    (hy : y = fmt.normalizedValue false l (e + 1)) :
    fmt.finiteSystem
      (((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) - y) := by
  have hdiff :=
    fmt.sourceRoundToEvenEvidence_positive_binaryGuard_coeffDiff_natAbs_lt_mantissaBound
      hbeta hk hr hpolicy hl hq hqs hy
  rw [hy, fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
  simpa [signValue] using
    (fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
      (negative := false) (k := (k : ℤ))
      (l := ((fmt.beta * l : ℕ) : ℤ)) (e := e) he hdiff)

/-- Negative aligned binary guard-word source evidence gives finite
representability of the local roundoff error once the rounded endpoint is
represented on the same next-exponent lattice. -/
theorem sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {k q r l : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hk : k = fmt.beta * q + r)
    (hr : r < fmt.beta)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) y)
    (hl : fmt.normalizedMantissa l)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1))
    (hy : y = fmt.normalizedValue true l (e + 1)) :
    fmt.finiteSystem
      ((fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) - y) := by
  have hdiff :=
    fmt.sourceRoundToEvenEvidence_negative_binaryGuard_coeffDiff_natAbs_lt_mantissaBound
      hbeta hk hr hpolicy hl hq hqs hy
  rw [hy, fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
  exact
    (fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
      (negative := true) (k := (k : ℤ))
      (l := ((fmt.beta * l : ℕ) : ℤ)) (e := e) he hdiff)

/-- Positive aligned binary guard-word source evidence gives finite
representability of the local roundoff error from normalized quotient endpoint
data, without separately supplying the rounded endpoint's mantissa. -/
theorem sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem_of_normalizedQuotient
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {k q r : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hk : k = fmt.beta * q + r)
    (hr : r < fmt.beta)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) y)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1)) :
    fmt.finiteSystem
      (((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) - y) := by
  by_cases hrzero : r = 0
  · have hk_exact : k = fmt.beta * q := by
      rw [hk, hrzero, Nat.add_zero]
    have hsource_eq_left :
        (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) =
          fmt.normalizedValue false q (e + 1) := by
      rw [fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
      simp [signValue]
      have hk_cast : (k : ℝ) = (((fmt.beta * q : ℕ) : ℝ)) := by
        exact_mod_cast hk_exact
      rw [hk_cast]
      simp [Nat.cast_mul]
    have hx_mem :
        fmt.unboundedNormalizedSystem
          ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) := by
      exact ⟨false, q, e + 1, hq, hsource_eq_left⟩
    have hy_self :
        y = (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) :=
      fmt.sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem
        hx_mem hpolicy
    rw [hy_self]
    have hzero :
        (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) -
            (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) = 0 := by ring
    rw [hzero]
    exact Or.inl rfl
  · have hadj :
        fmt.realOrderAdjacentNormalized
          (fmt.normalizedValue false q (e + 1))
          (fmt.normalizedValue false (q + 1) (e + 1)) :=
      fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
        ⟨false, q, e + 1, hq, hqs, Or.inl ⟨rfl, rfl⟩⟩
    have hbetween :=
      fmt.binaryGuardSource_between_sameExponentEndpoints_positive
        (k := k) (q := q) (r := r) (e := e) hk hr
    rcases
        fmt.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between
          hpolicy hadj hbetween with hy | hy
    · have hdiff :=
        fmt.binaryGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil
          hbeta hk hr (l := q) (Or.inl rfl)
      rw [hy, fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
      simpa [signValue] using
        (fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
          (negative := false) (k := (k : ℤ))
          (l := ((fmt.beta * q : ℕ) : ℤ)) (e := e) he hdiff)
    · have hdiff :=
        fmt.binaryGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil
          hbeta hk hr (l := q + 1) (Or.inr ⟨rfl, hrzero⟩)
      rw [hy, fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
      simpa [signValue] using
        (fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
          (negative := false) (k := (k : ℤ))
          (l := ((fmt.beta * (q + 1) : ℕ) : ℤ)) (e := e) he hdiff)

/-- Negative aligned binary guard-word source evidence gives finite
representability of the local roundoff error from normalized quotient endpoint
data, without separately supplying the rounded endpoint's mantissa. -/
theorem sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem_of_normalizedQuotient
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {k q r : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hk : k = fmt.beta * q + r)
    (hr : r < fmt.beta)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) y)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1)) :
    fmt.finiteSystem
      ((fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) - y) := by
  by_cases hrzero : r = 0
  · have hk_exact : k = fmt.beta * q := by
      rw [hk, hrzero, Nat.add_zero]
    have hsource_eq_right :
        fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ)) =
          fmt.normalizedValue true q (e + 1) := by
      rw [fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
      simp [signValue]
      have hk_cast : (k : ℝ) = (((fmt.beta * q : ℕ) : ℝ)) := by
        exact_mod_cast hk_exact
      rw [hk_cast]
      simp [Nat.cast_mul]
    have hx_mem :
        fmt.unboundedNormalizedSystem
          (fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ))) := by
      exact ⟨true, q, e + 1, hq, hsource_eq_right⟩
    have hy_self :
        y = fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ)) :=
      fmt.sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem
        hx_mem hpolicy
    rw [hy_self]
    have hzero :
        fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ)) -
          fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ)) = 0 := by ring
    rw [hzero]
    exact Or.inl rfl
  · have hadj :
        fmt.realOrderAdjacentNormalized
          (fmt.normalizedValue true (q + 1) (e + 1))
          (fmt.normalizedValue true q (e + 1)) :=
      fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
        ⟨true, q, e + 1, hq, hqs, Or.inr ⟨rfl, rfl⟩⟩
    have hbetween :=
      fmt.binaryGuardSource_between_sameExponentEndpoints_negative
        (k := k) (q := q) (r := r) (e := e) hk hr
    rcases
        fmt.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between
          hpolicy hadj hbetween with hy | hy
    · have hdiff :=
        fmt.binaryGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil
          hbeta hk hr (l := q + 1) (Or.inr ⟨rfl, hrzero⟩)
      rw [hy, fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
      simpa [signValue] using
        (fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
          (negative := true) (k := (k : ℤ))
          (l := ((fmt.beta * (q + 1) : ℕ) : ℤ)) (e := e) he hdiff)
    · have hdiff :=
        fmt.binaryGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil
          hbeta hk hr (l := q) (Or.inl rfl)
      rw [hy, fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
      simpa [signValue] using
        (fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
          (negative := true) (k := (k : ℤ))
          (l := ((fmt.beta * q : ℕ) : ℤ)) (e := e) he hdiff)

/-- Positive boundary binary guard-word source evidence selects the ceiling-binade
lower endpoint or, only in the non-exact case, the next-binade minimum endpoint.
-/
theorem sourceRoundToEvenEvidence_positive_binaryGuard_boundary_eq_max_or_min
    {fmt : FloatingPointFormat} {y : ℝ} {k r : ℕ} {e : ℤ}
    (hk : k = fmt.beta * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) y) :
    y = fmt.normalizedValue false fmt.maxNormalMantissa (e + 1) ∨
      (y = fmt.normalizedValue false fmt.minNormalMantissa (e + 2) ∧
        r ≠ 0) := by
  by_cases hrzero : r = 0
  · have hk_exact : k = fmt.beta * fmt.maxNormalMantissa := by
      rw [hk, hrzero, Nat.add_zero]
    have hsource_eq_left :
        (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) =
          fmt.normalizedValue false fmt.maxNormalMantissa (e + 1) := by
      rw [fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
      simp [signValue]
      have hk_cast :
          (k : ℝ) = (((fmt.beta * fmt.maxNormalMantissa : ℕ) : ℝ)) := by
        exact_mod_cast hk_exact
      rw [hk_cast]
      simp [Nat.cast_mul]
    have hx_mem :
        fmt.unboundedNormalizedSystem
          ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) := by
      exact ⟨false, fmt.maxNormalMantissa, e + 1,
        fmt.maxNormalMantissa_normalized, hsource_eq_left⟩
    have hy_self :
        y = (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) :=
      fmt.sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem
        hx_mem hpolicy
    exact Or.inl (by rw [hy_self, hsource_eq_left])
  · have hboundary :
        fmt.boundaryAdjacentNormalized
          (fmt.normalizedValue false fmt.maxNormalMantissa (e + 1))
          (fmt.normalizedValue false fmt.minNormalMantissa (e + 2)) := by
      refine ⟨false, e + 1, Or.inl ?_⟩
      constructor
      · rfl
      · rw [show e + 1 + 1 = e + 2 by ring]
    have hadj :
        fmt.realOrderAdjacentNormalized
          (fmt.normalizedValue false fmt.maxNormalMantissa (e + 1))
          (fmt.normalizedValue false fmt.minNormalMantissa (e + 2)) :=
      fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
    have hbetween :=
      fmt.binaryGuardSource_between_boundaryEndpoints_positive
        (k := k) (r := r) (e := e) hk hr
    rcases
        fmt.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between
          hpolicy hadj hbetween with hleft | hright
    · exact Or.inl hleft
    · exact Or.inr ⟨hright, hrzero⟩

/-- Negative boundary binary guard-word source evidence selects the ceiling-binade
lower endpoint or, only in the non-exact case, the next-binade minimum endpoint.
The real-order bracket is reversed, but the returned coefficient cases match the
positive statement. -/
theorem sourceRoundToEvenEvidence_negative_binaryGuard_boundary_eq_max_or_min
    {fmt : FloatingPointFormat} {y : ℝ} {k r : ℕ} {e : ℤ}
    (hk : k = fmt.beta * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) y) :
    y = fmt.normalizedValue true fmt.maxNormalMantissa (e + 1) ∨
      (y = fmt.normalizedValue true fmt.minNormalMantissa (e + 2) ∧
        r ≠ 0) := by
  by_cases hrzero : r = 0
  · have hk_exact : k = fmt.beta * fmt.maxNormalMantissa := by
      rw [hk, hrzero, Nat.add_zero]
    have hsource_eq_right :
        fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ)) =
          fmt.normalizedValue true fmt.maxNormalMantissa (e + 1) := by
      rw [fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
      simp [signValue]
      have hk_cast :
          (k : ℝ) = (((fmt.beta * fmt.maxNormalMantissa : ℕ) : ℝ)) := by
        exact_mod_cast hk_exact
      rw [hk_cast]
      simp [Nat.cast_mul]
    have hx_mem :
        fmt.unboundedNormalizedSystem
          (fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ))) := by
      exact ⟨true, fmt.maxNormalMantissa, e + 1,
        fmt.maxNormalMantissa_normalized, hsource_eq_right⟩
    have hy_self :
        y = fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ)) :=
      fmt.sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem
        hx_mem hpolicy
    exact Or.inl (by rw [hy_self, hsource_eq_right])
  · have hboundary :
        fmt.boundaryAdjacentNormalized
          (fmt.normalizedValue true fmt.minNormalMantissa (e + 2))
          (fmt.normalizedValue true fmt.maxNormalMantissa (e + 1)) := by
      refine ⟨true, e + 1, Or.inr ?_⟩
      constructor
      · rw [show e + 1 + 1 = e + 2 by ring]
      · rfl
    have hadj :
        fmt.realOrderAdjacentNormalized
          (fmt.normalizedValue true fmt.minNormalMantissa (e + 2))
          (fmt.normalizedValue true fmt.maxNormalMantissa (e + 1)) :=
      fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
    have hbetween :=
      fmt.binaryGuardSource_between_boundaryEndpoints_negative
        (k := k) (r := r) (e := e) hk hr
    rcases
        fmt.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between
          hpolicy hadj hbetween with hleft | hright
    · exact Or.inr ⟨hleft, hrzero⟩
    · exact Or.inl hright

/-- Positive boundary binary guard-word source evidence gives a rounded endpoint
coefficient on the original exponent lattice whose gap has fewer than `t`
digits. -/
theorem sourceRoundToEvenEvidence_positive_binaryGuard_boundary_coeffDiff_natAbs_lt_mantissaBound
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {k r : ℕ} {e : ℤ}
    (hk : k = fmt.beta * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) y) :
    ∃ c : ℕ,
      y = fmt.signValue false * (c : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)) ∧
        (((k : ℤ) - (c : ℤ)).natAbs < fmt.beta ^ fmt.t) := by
  rcases
      fmt.sourceRoundToEvenEvidence_positive_binaryGuard_boundary_eq_max_or_min
        (k := k) (r := r) (e := e) hk hr hpolicy with hy | hy
  · refine ⟨fmt.beta * fmt.maxNormalMantissa, ?_, ?_⟩
    · rw [hy, fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
    · exact
        fmt.binaryGuardBoundaryCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_boundary
          hbeta hk hr (Or.inl rfl)
  · rcases hy with ⟨hy, hrne⟩
    refine ⟨fmt.minNormalMantissa * fmt.beta ^ 2, ?_, ?_⟩
    · rw [hy, fmt.normalizedValue_add_twoExponent_eq_beta_sq_scaledInteger]
    · exact
        fmt.binaryGuardBoundaryCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_boundary
          hbeta hk hr (Or.inr ⟨rfl, hrne⟩)

/-- Negative boundary binary guard-word source evidence gives a rounded endpoint
coefficient on the original exponent lattice whose gap has fewer than `t`
digits. -/
theorem sourceRoundToEvenEvidence_negative_binaryGuard_boundary_coeffDiff_natAbs_lt_mantissaBound
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {k r : ℕ} {e : ℤ}
    (hk : k = fmt.beta * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) y) :
    ∃ c : ℕ,
      y = fmt.signValue true * (c : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)) ∧
        (((k : ℤ) - (c : ℤ)).natAbs < fmt.beta ^ fmt.t) := by
  rcases
      fmt.sourceRoundToEvenEvidence_negative_binaryGuard_boundary_eq_max_or_min
        (k := k) (r := r) (e := e) hk hr hpolicy with hy | hy
  · refine ⟨fmt.beta * fmt.maxNormalMantissa, ?_, ?_⟩
    · rw [hy, fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
    · exact
        fmt.binaryGuardBoundaryCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_boundary
          hbeta hk hr (Or.inl rfl)
  · rcases hy with ⟨hy, hrne⟩
    refine ⟨fmt.minNormalMantissa * fmt.beta ^ 2, ?_, ?_⟩
    · rw [hy, fmt.normalizedValue_add_twoExponent_eq_beta_sq_scaledInteger]
    · exact
        fmt.binaryGuardBoundaryCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_boundary
          hbeta hk hr (Or.inr ⟨rfl, hrne⟩)

/-- Positive boundary binary guard-word source evidence gives finite
representability of the local roundoff error. -/
theorem sourceRoundToEvenEvidence_positive_binaryGuard_boundary_error_finiteSystem
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {k r : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hk : k = fmt.beta * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) y) :
    fmt.finiteSystem
      (((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) - y) := by
  rcases
      fmt.sourceRoundToEvenEvidence_positive_binaryGuard_boundary_coeffDiff_natAbs_lt_mantissaBound
        hbeta hk hr hpolicy with ⟨c, hy, hdiff⟩
  rw [hy]
  simpa [signValue] using
    (fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
      (negative := false) (k := (k : ℤ)) (l := (c : ℤ)) (e := e)
      he hdiff)

/-- Negative boundary binary guard-word source evidence gives finite
representability of the local roundoff error. -/
theorem sourceRoundToEvenEvidence_negative_binaryGuard_boundary_error_finiteSystem
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {k r : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hk : k = fmt.beta * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) y) :
    fmt.finiteSystem
      ((fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) - y) := by
  rcases
      fmt.sourceRoundToEvenEvidence_negative_binaryGuard_boundary_coeffDiff_natAbs_lt_mantissaBound
        hbeta hk hr hpolicy with ⟨c, hy, hdiff⟩
  rw [hy]
  exact
    (fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
      (negative := true) (k := (k : ℤ)) (l := (c : ℤ)) (e := e)
      he hdiff)

/-- Positive aligned binary guard-word source evidence gives finite
representability of the local roundoff error directly from the guard coefficient
range.  The quotient dispatcher chooses between the ordinary `q,q+1` bracket
and the exponent-boundary branch. -/
theorem sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem_of_guardCoeffBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {k q r : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hk : k = fmt.beta * q + r)
    (hr : r < fmt.beta)
    (hlo : fmt.beta ^ fmt.t ≤ k)
    (hhi : k < 2 * fmt.beta ^ fmt.t)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) y) :
    fmt.finiteSystem
      (((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) - y) := by
  rcases
      fmt.binaryGuardQuotient_normalized_or_max_of_mantissaBound_le_of_lt_two_mul
        hbeta hk hr hlo hhi with hordinary | hboundary
  · exact
      fmt.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem_of_normalizedQuotient
        hbeta he hk hr hpolicy hordinary.1 hordinary.2
  · subst q
    exact
      fmt.sourceRoundToEvenEvidence_positive_binaryGuard_boundary_error_finiteSystem
        hbeta he hk hr hpolicy

/-- Negative aligned binary guard-word source evidence gives finite
representability of the local roundoff error directly from the guard coefficient
range.  The quotient dispatcher chooses between the ordinary reversed bracket
and the exponent-boundary branch. -/
theorem sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem_of_guardCoeffBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {k q r : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hk : k = fmt.beta * q + r)
    (hr : r < fmt.beta)
    (hlo : fmt.beta ^ fmt.t ≤ k)
    (hhi : k < 2 * fmt.beta ^ fmt.t)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) y) :
    fmt.finiteSystem
      ((fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) - y) := by
  rcases
      fmt.binaryGuardQuotient_normalized_or_max_of_mantissaBound_le_of_lt_two_mul
        hbeta hk hr hlo hhi with hordinary | hboundary
  · exact
      fmt.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem_of_normalizedQuotient
        hbeta he hk hr hpolicy hordinary.1 hordinary.2
  · subst q
    exact
      fmt.sourceRoundToEvenEvidence_negative_binaryGuard_boundary_error_finiteSystem
        hbeta he hk hr hpolicy

/-- Positive same-sign, same-exponent normalized addition has finite
representable local roundoff error under binary round-to-even evidence.

This bridges the operand-level C4.4 addition case to the guard-word dispatcher:
the exact sum of two aligned normalized operands has coefficient `m+n`, whose
binary quotient/remainder supplies the one-guard-digit source interval. -/
theorem sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_sameExponent_error_finiteSystem
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {m n : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.normalizedMantissa n)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e + fmt.normalizedValue false n e) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e + fmt.normalizedValue false n e) - y) := by
  let k : ℕ := m + n
  let q : ℕ := k / fmt.beta
  let r : ℕ := k % fmt.beta
  have hk : k = fmt.beta * q + r := by
    rw [show q = k / fmt.beta by rfl, show r = k % fmt.beta by rfl]
    exact (Nat.div_add_mod k fmt.beta).symm
  have hr : r < fmt.beta := by
    rw [show r = k % fmt.beta by rfl]
    exact Nat.mod_lt k (lt_trans Nat.zero_lt_one fmt.one_lt_beta)
  have hlo : fmt.beta ^ fmt.t ≤ k := by
    have hsum_min : fmt.minNormalMantissa + fmt.minNormalMantissa ≤ m + n :=
      Nat.add_le_add hm.1 hn.1
    have hB_eq :
        fmt.beta ^ fmt.t = fmt.minNormalMantissa + fmt.minNormalMantissa := by
      rw [← fmt.minNormalMantissa_mul_beta_eq_mantissaBound, hbeta]
      ring
    omega
  have hhi : k < 2 * fmt.beta ^ fmt.t := by
    simpa [k] using
      (normalizedMantissa_add_lt_two_mul_mantissaBound
        (fmt := fmt) hm hn)
  have hsource :
      fmt.normalizedValue false m e + fmt.normalizedValue false n e =
        ((k : ℕ) : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) := by
    simpa [k, signValue] using
      (fmt.normalizedValue_add_sameSign_sameExponent_eq_scaledInteger
        false m n e)
  have hpolicy' :
      fmt.sourceRoundToEvenEvidence
        (((k : ℕ) : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) y := by
    simpa [hsource] using hpolicy
  have hfin :
      fmt.finiteSystem
        ((((k : ℕ) : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) - y) :=
    fmt.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem_of_guardCoeffBounds
      hbeta he hk hr hlo hhi hpolicy'
  simpa [hsource] using hfin

/-- Negative same-sign, same-exponent normalized addition has finite
representable local roundoff error under binary round-to-even evidence. -/
theorem sourceRoundToEvenEvidence_negative_normalizedValue_add_sameSign_sameExponent_error_finiteSystem
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {m n : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.normalizedMantissa n)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true m e + fmt.normalizedValue true n e) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true m e + fmt.normalizedValue true n e) - y) := by
  let k : ℕ := m + n
  let q : ℕ := k / fmt.beta
  let r : ℕ := k % fmt.beta
  have hk : k = fmt.beta * q + r := by
    rw [show q = k / fmt.beta by rfl, show r = k % fmt.beta by rfl]
    exact (Nat.div_add_mod k fmt.beta).symm
  have hr : r < fmt.beta := by
    rw [show r = k % fmt.beta by rfl]
    exact Nat.mod_lt k (lt_trans Nat.zero_lt_one fmt.one_lt_beta)
  have hlo : fmt.beta ^ fmt.t ≤ k := by
    have hsum_min : fmt.minNormalMantissa + fmt.minNormalMantissa ≤ m + n :=
      Nat.add_le_add hm.1 hn.1
    have hB_eq :
        fmt.beta ^ fmt.t = fmt.minNormalMantissa + fmt.minNormalMantissa := by
      rw [← fmt.minNormalMantissa_mul_beta_eq_mantissaBound, hbeta]
      ring
    omega
  have hhi : k < 2 * fmt.beta ^ fmt.t := by
    simpa [k] using
      (normalizedMantissa_add_lt_two_mul_mantissaBound
        (fmt := fmt) hm hn)
  have hsource :
      fmt.normalizedValue true m e + fmt.normalizedValue true n e =
        fmt.signValue true * ((k : ℕ) : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)) := by
    simpa [k] using
      (fmt.normalizedValue_add_sameSign_sameExponent_eq_scaledInteger
        true m n e)
  have hpolicy' :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * ((k : ℕ) : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) y := by
    simpa [hsource] using hpolicy
  have hfin :
      fmt.finiteSystem
        ((fmt.signValue true * ((k : ℕ) : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) - y) :=
    fmt.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem_of_guardCoeffBounds
      hbeta he hk hr hlo hhi hpolicy'
  simpa [hsource] using hfin

/-- Sign-generic same-sign, same-exponent normalized addition has finite
representable local roundoff error under binary round-to-even evidence. -/
theorem sourceRoundToEvenEvidence_normalizedValue_add_sameSign_sameExponent_error_finiteSystem
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {y : ℝ} {m n : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.normalizedMantissa n)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative m e + fmt.normalizedValue negative n e) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative m e + fmt.normalizedValue negative n e) -
        y) := by
  cases negative
  · exact
      fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_sameExponent_error_finiteSystem
        hbeta he hm hn hpolicy
  · exact
      fmt.sourceRoundToEvenEvidence_negative_normalizedValue_add_sameSign_sameExponent_error_finiteSystem
        hbeta he hm hn hpolicy

/-- Same-sign normalized ordered-exponent addition has finite local error under
binary round-to-even evidence in the one-guard-word branch.  The high-exponent
operand is shifted onto the lower exponent lattice, yielding the source
coefficient `mHigh * beta^(eHigh-eLow) + mLow`. -/
theorem sourceRoundToEvenEvidence_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_guardCoeffBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {y : ℝ}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (_hmHigh : fmt.normalizedMantissa mHigh)
    (_hmLow : fmt.normalizedMantissa mLow)
    (_heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hlo :
      fmt.beta ^ fmt.t ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        2 * fmt.beta ^ fmt.t)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) - y) := by
  let shift := Int.toNat (eHigh - eLow)
  let k : ℕ := mHigh * fmt.beta ^ shift + mLow
  let q : ℕ := k / fmt.beta
  let r : ℕ := k % fmt.beta
  have hshift_cast : ((shift : ℕ) : ℤ) = eHigh - eLow := by
    have hnonneg : 0 ≤ eHigh - eLow := sub_nonneg.mpr hle
    simpa [shift] using Int.toNat_of_nonneg hnonneg
  have hshift_endpoint : eHigh - (shift : ℤ) = eLow := by
    omega
  have hshift :
      fmt.normalizedValue negative (mHigh * fmt.beta ^ shift) eLow =
        fmt.normalizedValue negative mHigh eHigh := by
    have h :=
      fmt.normalizedValue_mul_beta_pow_subExponent_eq
        (negative := negative) (m := mHigh) (shift := shift) (e := eHigh)
    rw [hshift_endpoint] at h
    exact h
  have hk : k = fmt.beta * q + r := by
    rw [show q = k / fmt.beta by rfl, show r = k % fmt.beta by rfl]
    exact (Nat.div_add_mod k fmt.beta).symm
  have hr : r < fmt.beta := by
    rw [show r = k % fmt.beta by rfl]
    exact Nat.mod_lt k (lt_trans Nat.zero_lt_one fmt.one_lt_beta)
  have hlo' : fmt.beta ^ fmt.t ≤ k := by
    simpa [k, shift] using hlo
  have hhi' : k < 2 * fmt.beta ^ fmt.t := by
    simpa [k, shift] using hhi
  have hsource :
      fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow =
        fmt.signValue negative * ((k : ℕ) : ℝ) *
          fmt.betaR ^ (eLow - (fmt.t : ℤ)) := by
    rw [← hshift]
    simp [k, normalizedValue, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    ring
  cases negative
  · have hpolicy' :
        fmt.sourceRoundToEvenEvidence
          (((k : ℕ) : ℝ) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ))) y := by
      simpa [hsource, signValue] using hpolicy
    have hfin :
        fmt.finiteSystem
          ((((k : ℕ) : ℝ) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ))) - y) :=
      fmt.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem_of_guardCoeffBounds
        hbeta heLow hk hr hlo' hhi' hpolicy'
    simpa [hsource, signValue] using hfin
  · have hpolicy' :
        fmt.sourceRoundToEvenEvidence
          (fmt.signValue true * ((k : ℕ) : ℝ) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ))) y := by
      simpa [hsource] using hpolicy
    have hfin :
        fmt.finiteSystem
          ((fmt.signValue true * ((k : ℕ) : ℝ) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ))) - y) :=
      fmt.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem_of_guardCoeffBounds
        hbeta heLow hk hr hlo' hhi' hpolicy'
    simpa [hsource] using hfin

/-- Same-sign mixed normal/subnormal addition has finite local error under
binary round-to-even evidence in the one-guard-word branch.  The normalized
operand is shifted onto the subnormal lattice, yielding the source coefficient
`m * beta^(e-emin) + n`. -/
theorem sourceRoundToEvenEvidence_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_guardCoeffBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {y : ℝ}
    {m n : ℕ} {e : ℤ}
    (_hm : fmt.normalizedMantissa m)
    (_hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hlo :
      fmt.beta ^ fmt.t ≤
        m * fmt.beta ^ Int.toNat (e - fmt.emin) + n)
    (hhi :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n <
        2 * fmt.beta ^ fmt.t)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) - y) := by
  let shift := Int.toNat (e - fmt.emin)
  let k : ℕ := m * fmt.beta ^ shift + n
  let q : ℕ := k / fmt.beta
  let r : ℕ := k % fmt.beta
  have hshift_cast : ((shift : ℕ) : ℤ) = e - fmt.emin := by
    have hnonneg : 0 ≤ e - fmt.emin := sub_nonneg.mpr he.1
    simpa [shift] using Int.toNat_of_nonneg hnonneg
  have hshift_endpoint : e - (shift : ℤ) = fmt.emin := by
    omega
  have hshift :
      fmt.normalizedValue negative m e =
        fmt.subnormalValue negative (m * fmt.beta ^ shift) :=
    fmt.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
      (negative := negative) (m := m) (shift := shift) (e := e)
      hshift_endpoint
  have hk : k = fmt.beta * q + r := by
    rw [show q = k / fmt.beta by rfl, show r = k % fmt.beta by rfl]
    exact (Nat.div_add_mod k fmt.beta).symm
  have hr : r < fmt.beta := by
    rw [show r = k % fmt.beta by rfl]
    exact Nat.mod_lt k (lt_trans Nat.zero_lt_one fmt.one_lt_beta)
  have hlo' : fmt.beta ^ fmt.t ≤ k := by
    simpa [k, shift] using hlo
  have hhi' : k < 2 * fmt.beta ^ fmt.t := by
    simpa [k, shift] using hhi
  have hemin : fmt.exponentInRange fmt.emin :=
    ⟨le_rfl, fmt.emin_le_emax⟩
  have hsource :
      fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n =
        fmt.signValue negative * ((k : ℕ) : ℝ) *
          fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
    rw [hshift]
    simp [k, subnormalValue, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    ring
  cases negative
  · have hpolicy' :
        fmt.sourceRoundToEvenEvidence
          (((k : ℕ) : ℝ) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) y := by
      simpa [hsource, signValue] using hpolicy
    have hfin :
        fmt.finiteSystem
          ((((k : ℕ) : ℝ) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) - y) :=
      fmt.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem_of_guardCoeffBounds
        hbeta hemin hk hr hlo' hhi' hpolicy'
    simpa [hsource, signValue] using hfin
  · have hpolicy' :
        fmt.sourceRoundToEvenEvidence
          (fmt.signValue true * ((k : ℕ) : ℝ) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) y := by
      simpa [hsource] using hpolicy
    have hfin :
        fmt.finiteSystem
          ((fmt.signValue true * ((k : ℕ) : ℝ) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) - y) :=
      fmt.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem_of_guardCoeffBounds
        hbeta hemin hk hr hlo' hhi' hpolicy'
    simpa [hsource] using hfin

theorem sourceRoundToEvenEvidence_unique
    {fmt : FloatingPointFormat} {x y z : ℝ}
    (hy : fmt.sourceRoundToEvenEvidence x y)
    (hz : fmt.sourceRoundToEvenEvidence x z) :
    y = z := by
  rcases hy with hpos | hneg
  · rcases hpos with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      have hx_mem : fmt.unboundedNormalizedSystem x :=
        ⟨false, m, e, hm, hx_eq⟩
      rw [hy_eq]
      exact
        (sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem
          hx_mem hz).symm
    · rcases hbracket with
        ⟨a, b, leftMantissa, hadj, hleft, _ha_nonneg,
          ha_le_x, hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact
        (sourceRoundToEvenEvidence_eq_nearest_of_realOrderAdjacent_between
          hz hadj hleft ⟨ha_le_x, hx_le_b⟩).symm
  · rcases hneg with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      have hx_mem : fmt.unboundedNormalizedSystem x :=
        ⟨true, m, e, hm, hx_eq⟩
      rw [hy_eq]
      exact
        (sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem
          hx_mem hz).symm
    · rcases hbracket with
        ⟨a, b, leftMantissa, hadj, hleft, _hb_nonpos,
          ha_le_x, hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact
        (sourceRoundToEvenEvidence_eq_nearest_of_realOrderAdjacent_between
          hz hadj hleft ⟨ha_le_x, hx_le_b⟩).symm

theorem sourceRoundToEvenEvidence_relErrorComputedDenom_le_unitRoundoff
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteNormalRange x)
    (hpolicy : fmt.sourceRoundToEvenEvidence x y) :
    y ≠ 0 ∧ relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  have hx_ne := fmt.finiteNormalRange_ne_zero hx
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      have hx_unbounded : fmt.unboundedNormalizedSystem x :=
        ⟨false, m, e, hm, hx_eq⟩
      constructor
      · rw [hy_eq]
        exact hx_ne
      · simpa [hy_eq] using
          fmt.nearestRoundingToUnbounded_exact_relErrorComputedDenom_le_unitRoundoff
            hx_unbounded
    · rcases hbracket with
        ⟨a, b, leftMantissa, hadj, _hleft, _ha_nonneg, ha_le_x, hx_le_b, hy_eq⟩
      have hround : fmt.nearestRoundingToUnbounded x y := by
        rw [hy_eq]
        exact
          fmt.nearestAdjacentRoundToEven_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
            leftMantissa hadj ⟨ha_le_x, hx_le_b⟩
      have hy_ne : y ≠ 0 :=
        fmt.unboundedNormalizedSystem_ne_zero (nearestRoundingIn_mem hround)
      have hrel :=
        fmt.nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_of_realOrderAdjacent_between
          hround hadj (Or.inl ⟨ha_le_x, hx_le_b⟩)
      exact ⟨hy_ne, hrel⟩
  · rcases hneg with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      have hx_unbounded : fmt.unboundedNormalizedSystem x :=
        ⟨true, m, e, hm, hx_eq⟩
      constructor
      · rw [hy_eq]
        exact hx_ne
      · simpa [hy_eq] using
          fmt.nearestRoundingToUnbounded_exact_relErrorComputedDenom_le_unitRoundoff
            hx_unbounded
    · rcases hbracket with
        ⟨a, b, leftMantissa, hadj, _hleft, _hb_nonpos, ha_le_x, hx_le_b, hy_eq⟩
      have hround : fmt.nearestRoundingToUnbounded x y := by
        rw [hy_eq]
        exact
          fmt.nearestAdjacentRoundToEven_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
            leftMantissa hadj ⟨ha_le_x, hx_le_b⟩
      have hy_ne : y ≠ 0 :=
        fmt.unboundedNormalizedSystem_ne_zero (nearestRoundingIn_mem hround)
      have hrel :=
        fmt.nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_of_realOrderAdjacent_between
          hround hadj (Or.inl ⟨ha_le_x, hx_le_b⟩)
      exact ⟨hy_ne, hrel⟩

/-- Source-facing positive finite-normal-range nearest-rounding theorem for the
finite relation.  This is the non-strict `|delta| <= u` variant of Higham's
Theorem 2.2 for positive normal-range inputs. -/
theorem exists_nearestRoundingToFinite_signedRelErrorWitness_positive_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxlo : fmt.minNormalMagnitude ≤ x)
    (hxhi : x ≤ fmt.maxFiniteMagnitude) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  have hxpos : 0 < x := lt_of_lt_of_le fmt.minNormalMagnitude_pos hxlo
  rcases fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_positive
      (x := x) hxpos with ⟨y, δ, hround, hδ, hwit⟩
  have hyfin :=
    fmt.nearestRoundingToUnbounded_output_finite_of_minNormalMagnitude_le_of_le_maxFiniteMagnitude
      hround hxlo hxhi
  have hfiniteRound :=
    fmt.nearestRoundingToFinite_of_nearestRoundingToUnbounded_of_finite_of_minNormalMagnitude_le
      hround hyfin hxlo
  exact ⟨y, δ, hfiniteRound, hδ, hwit⟩

/-- Source-facing negative finite-normal-range nearest-rounding theorem for the
finite relation.  This is the sign mirror of the positive normal-range wrapper. -/
theorem exists_nearestRoundingToFinite_signedRelErrorWitness_negative_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxlo : -fmt.maxFiniteMagnitude ≤ x)
    (hxhi : x ≤ -fmt.minNormalMagnitude) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  have hxneg : x < 0 := by
    have hmin_pos := fmt.minNormalMagnitude_pos
    linarith
  rcases fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_negative
      (x := x) hxneg with ⟨y, δ, hround, hδ, hwit⟩
  have hyfin :=
    fmt.nearestRoundingToUnbounded_output_finite_of_neg_maxFiniteMagnitude_le_of_le_neg_minNormalMagnitude
      hround hxlo hxhi
  have hfiniteRound :=
    fmt.nearestRoundingToFinite_of_nearestRoundingToUnbounded_of_finite_of_le_neg_minNormalMagnitude
      hround hyfin hxhi
  exact ⟨y, δ, hfiniteRound, hδ, hwit⟩

theorem exists_nearestRoundingToFinite_signedRelErrorWitness_lt_positive_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxlo : fmt.minNormalMagnitude ≤ x)
    (hxhi : x ≤ fmt.maxFiniteMagnitude) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  have hxpos : 0 < x := lt_of_lt_of_le fmt.minNormalMagnitude_pos hxlo
  rcases fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_positive
      (x := x) hxpos with ⟨y, δ, hround, hδ, hwit⟩
  have hyfin :=
    fmt.nearestRoundingToUnbounded_output_finite_of_minNormalMagnitude_le_of_le_maxFiniteMagnitude
      hround hxlo hxhi
  have hfiniteRound :=
    fmt.nearestRoundingToFinite_of_nearestRoundingToUnbounded_of_finite_of_minNormalMagnitude_le
      hround hyfin hxlo
  exact ⟨y, δ, hfiniteRound, hδ, hwit⟩

theorem exists_nearestRoundingToFinite_signedRelErrorWitness_lt_negative_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxlo : -fmt.maxFiniteMagnitude ≤ x)
    (hxhi : x ≤ -fmt.minNormalMagnitude) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  have hxneg : x < 0 := by
    have hmin_pos := fmt.minNormalMagnitude_pos
    linarith
  rcases fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_negative
      (x := x) hxneg with ⟨y, δ, hround, hδ, hwit⟩
  have hyfin :=
    fmt.nearestRoundingToUnbounded_output_finite_of_neg_maxFiniteMagnitude_le_of_le_neg_minNormalMagnitude
      hround hxlo hxhi
  have hfiniteRound :=
    fmt.nearestRoundingToFinite_of_nearestRoundingToUnbounded_of_finite_of_le_neg_minNormalMagnitude
      hround hyfin hxhi
  exact ⟨y, δ, hfiniteRound, hδ, hwit⟩

/-- Source-facing finite-normal-range nearest-rounding theorem for the finite
relation.  This packages the positive and negative wrappers into the
non-strict `|delta| <= u` finite-format relation version of Higham Theorem 2.2
over `finiteNormalRange`.  It remains relation-valued and does not choose a
total tie policy. -/
theorem exists_nearestRoundingToFinite_signedRelErrorWitness_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · have hx_abs : |x| = -x := abs_of_neg hneg
    have hxlo : -fmt.maxFiniteMagnitude ≤ x := by
      have h := hx.2
      rw [hx_abs] at h
      linarith
    have hxhi : x ≤ -fmt.minNormalMagnitude := by
      have h := hx.1
      rw [hx_abs] at h
      linarith
    exact
      fmt.exists_nearestRoundingToFinite_signedRelErrorWitness_negative_finiteNormalRange
        hxlo hxhi
  · subst x
    have hmin_pos := fmt.minNormalMagnitude_pos
    rcases hx with ⟨hxlo, _hxhi⟩
    rw [abs_zero] at hxlo
    exact False.elim (not_lt_of_ge hxlo hmin_pos)
  · have hx_abs : |x| = x := abs_of_pos hpos
    have hxlo : fmt.minNormalMagnitude ≤ x := by
      simpa [hx_abs] using hx.1
    have hxhi : x ≤ fmt.maxFiniteMagnitude := by
      simpa [hx_abs] using hx.2
    exact
      fmt.exists_nearestRoundingToFinite_signedRelErrorWitness_positive_finiteNormalRange
        hxlo hxhi

/-- Every real input has at least one finite nearest-rounded value in the
relation-valued finite system.  This is the total existence theorem for the
nearest-rounding relation; it still does not choose among ties or define an
operational IEEE `fl` function. -/
theorem exists_nearestRoundingToFinite
    (fmt : FloatingPointFormat) (x : ℝ) :
    ∃ y : ℝ, fmt.nearestRoundingToFinite x y := by
  by_cases hunder : fmt.finiteUnderflowRange x
  · exact fmt.exists_nearestRoundingToFinite_finiteUnderflowRange hunder
  · have hmin_le : fmt.minNormalMagnitude ≤ |x| := by
      rw [finiteUnderflowRange] at hunder
      exact le_of_not_gt hunder
    by_cases hover : fmt.finiteOverflowRange x
    · exact
        ⟨fmt.finiteOverflowSaturation x,
          fmt.finiteOverflowSaturation_nearestRoundingToFinite_of_finiteOverflowRange
            hover⟩
    · have hmax_le : |x| ≤ fmt.maxFiniteMagnitude := by
        rw [finiteOverflowRange] at hover
        exact le_of_not_gt hover
      rcases fmt.exists_nearestRoundingToFinite_signedRelErrorWitness_finiteNormalRange
          ⟨hmin_le, hmax_le⟩ with
        ⟨y, _δ, hround, _hδ, _hwit⟩
      exact ⟨y, hround⟩

/-- A total source-facing finite nearest-rounding choice.  It chooses an
arbitrary nearest value from the relation, so ties are intentionally not
specified; round-to-even and IEEE exception behavior remain separate. -/
noncomputable def finiteNearestFl (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  Classical.choose (fmt.exists_nearestRoundingToFinite x)

theorem finiteNearestFl_nearestRoundingToFinite
    (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.nearestRoundingToFinite x (fmt.finiteNearestFl x) :=
  Classical.choose_spec (fmt.exists_nearestRoundingToFinite x)

theorem finiteNearestFl_output_not_finiteOverflowRange
    (fmt : FloatingPointFormat) (x : ℝ) :
    ¬ fmt.finiteOverflowRange (fmt.finiteNearestFl x) :=
  fmt.nearestRoundingToFinite_output_not_finiteOverflowRange
    (fmt.finiteNearestFl_nearestRoundingToFinite x)

theorem finiteNearestFl_output_abs_le_maxFiniteMagnitude
    (fmt : FloatingPointFormat) (x : ℝ) :
    |fmt.finiteNearestFl x| ≤ fmt.maxFiniteMagnitude :=
  fmt.nearestRoundingToFinite_output_abs_le_maxFiniteMagnitude
    (fmt.finiteNearestFl_nearestRoundingToFinite x)

/-- Strict source-facing finite-normal-range nearest-rounding theorem for the
finite relation, matching Higham Theorem 2.2's `|delta| < u` over the normal
range.  It remains relation-valued and independent of a concrete tie policy. -/
theorem exists_nearestRoundingToFinite_signedRelErrorWitness_lt_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · have hx_abs : |x| = -x := abs_of_neg hneg
    have hxlo : -fmt.maxFiniteMagnitude ≤ x := by
      have h := hx.2
      rw [hx_abs] at h
      linarith
    have hxhi : x ≤ -fmt.minNormalMagnitude := by
      have h := hx.1
      rw [hx_abs] at h
      linarith
    exact
      fmt.exists_nearestRoundingToFinite_signedRelErrorWitness_lt_negative_finiteNormalRange
        hxlo hxhi
  · subst x
    have hmin_pos := fmt.minNormalMagnitude_pos
    rcases hx with ⟨hxlo, _hxhi⟩
    rw [abs_zero] at hxlo
    exact False.elim (not_lt_of_ge hxlo hmin_pos)
  · have hx_abs : |x| = x := abs_of_pos hpos
    have hxlo : fmt.minNormalMagnitude ≤ x := by
      simpa [hx_abs] using hx.1
    have hxhi : x ≤ fmt.maxFiniteMagnitude := by
      simpa [hx_abs] using hx.2
    exact
      fmt.exists_nearestRoundingToFinite_signedRelErrorWitness_lt_positive_finiteNormalRange
        hxlo hxhi

/-- Positive finite-normal-range nearest-rounding theorem that preserves the
explicit source-level round-away selector evidence. -/
theorem exists_finiteNormalRoundAway_signedRelErrorWitness_lt_positive_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxlo : fmt.minNormalMagnitude ≤ x)
    (hxhi : x ≤ fmt.maxFiniteMagnitude) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            fmt.sourceRoundAwayEvidence x y := by
  have hxpos : 0 < x := lt_of_lt_of_le fmt.minNormalMagnitude_pos hxlo
  rcases
    fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_positive
      (x := x) hxpos with
    ⟨y, δ, hround, hδ, hwit, hpolicy⟩
  have hyfin :=
    fmt.nearestRoundingToUnbounded_output_finite_of_minNormalMagnitude_le_of_le_maxFiniteMagnitude
      hround hxlo hxhi
  have hfiniteRound :=
    fmt.nearestRoundingToFinite_of_nearestRoundingToUnbounded_of_finite_of_minNormalMagnitude_le
      hround hyfin hxlo
  exact ⟨y, δ, hfiniteRound, hδ, hwit, Or.inl hpolicy⟩

/-- Negative finite-normal-range nearest-rounding theorem that preserves the
explicit source-level round-away selector evidence. -/
theorem exists_finiteNormalRoundAway_signedRelErrorWitness_lt_negative_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxlo : -fmt.maxFiniteMagnitude ≤ x)
    (hxhi : x ≤ -fmt.minNormalMagnitude) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            fmt.sourceRoundAwayEvidence x y := by
  have hxneg : x < 0 := by
    have hmin_pos := fmt.minNormalMagnitude_pos
    linarith
  rcases
    fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_negative
      (x := x) hxneg with
    ⟨y, δ, hround, hδ, hwit, hpolicy⟩
  have hyfin :=
    fmt.nearestRoundingToUnbounded_output_finite_of_neg_maxFiniteMagnitude_le_of_le_neg_minNormalMagnitude
      hround hxlo hxhi
  have hfiniteRound :=
    fmt.nearestRoundingToFinite_of_nearestRoundingToUnbounded_of_finite_of_le_neg_minNormalMagnitude
      hround hyfin hxhi
  exact ⟨y, δ, hfiniteRound, hδ, hwit, Or.inr hpolicy⟩

/-- Finite-normal-range nearest-rounding theorem that chooses a nearest value
by the source-level round-away policy.  This is still a normal-range theorem:
finite underflow/overflow and IEEE exception behavior remain separate. -/
theorem exists_finiteNormalRoundAway_signedRelErrorWitness_lt_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            fmt.sourceRoundAwayEvidence x y := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · have hx_abs : |x| = -x := abs_of_neg hneg
    have hxlo : -fmt.maxFiniteMagnitude ≤ x := by
      have h := hx.2
      rw [hx_abs] at h
      linarith
    have hxhi : x ≤ -fmt.minNormalMagnitude := by
      have h := hx.1
      rw [hx_abs] at h
      linarith
    exact
      fmt.exists_finiteNormalRoundAway_signedRelErrorWitness_lt_negative_finiteNormalRange
        hxlo hxhi
  · subst x
    have hmin_pos := fmt.minNormalMagnitude_pos
    rcases hx with ⟨hxlo, _hxhi⟩
    rw [abs_zero] at hxlo
    exact False.elim (not_lt_of_ge hxlo hmin_pos)
  · have hx_abs : |x| = x := abs_of_pos hpos
    have hxlo : fmt.minNormalMagnitude ≤ x := by
      simpa [hx_abs] using hx.1
    have hxhi : x ≤ fmt.maxFiniteMagnitude := by
      simpa [hx_abs] using hx.2
    exact
      fmt.exists_finiteNormalRoundAway_signedRelErrorWitness_lt_positive_finiteNormalRange
        hxlo hxhi

/-- Global positive unbounded-normalized nearest-rounding bridge that carries
the explicit local round-to-even selector evidence through exponent selection.
The left endpoint's normalized mantissa is recorded for the tie rule. -/
theorem exists_nearestAdjacentRoundToEven_signedRelErrorWitness_lt_positive
    {fmt : FloatingPointFormat} {x : ℝ} (hx : 0 < x) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            fmt.sourceRoundToEvenEvidence x y := by
  rcases fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_positive
      hx with
    ⟨_yAway, _δAway, _hroundAway, _hδAway, _hwitAway, hpolicy⟩
  rcases hpolicy with ⟨e, hlo, hhi, hexact | hbracket⟩
  · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
    have hx_mem : fmt.unboundedNormalizedSystem x :=
      ⟨false, m, e, hm, hx_eq⟩
    rcases fmt.nearestRoundingToUnbounded_exact_signedRelErrorWitness_lt hx_mem with
      ⟨δ, hδ, hwit, hround⟩
    exact
      ⟨x, δ, hround, hδ, hwit,
        Or.inl ⟨e, hlo, hhi, Or.inl ⟨m, hm, hx_eq, rfl⟩⟩⟩
  · rcases hbracket with ⟨a, b, hadj, ha_nonneg, ha_le_x, hx_le_b, _hy_eq⟩
    rcases hadj.1 with ⟨negative, leftMantissa, eLeft, hmLeft, ha_repr⟩
    let y := nearestAdjacentRoundToEven x a b leftMantissa
    have hround : fmt.nearestRoundingToUnbounded x y := by
      dsimp [y]
      exact
        fmt.nearestAdjacentRoundToEven_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
          leftMantissa hadj ⟨ha_le_x, hx_le_b⟩
    rcases
      fmt.nearestRoundingToUnbounded_signedRelErrorWitness_lt_of_nonneg_between
        hround hadj ha_nonneg ⟨ha_le_x, hx_le_b⟩ with
      ⟨δ, hδ, hwit, _hround⟩
    exact
      ⟨y, δ, hround, hδ, hwit,
        Or.inl ⟨e, hlo, hhi,
          Or.inr
            ⟨a, b, leftMantissa, hadj,
              ⟨negative, eLeft, hmLeft, ha_repr⟩,
              ha_nonneg, ha_le_x, hx_le_b, rfl⟩⟩⟩

/-- Global negative unbounded-normalized nearest-rounding bridge that carries
the explicit local round-to-even selector evidence through exponent selection.
The left endpoint's normalized mantissa is recorded for the tie rule. -/
theorem exists_nearestAdjacentRoundToEven_signedRelErrorWitness_lt_negative
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x < 0) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            fmt.sourceRoundToEvenEvidence x y := by
  rcases fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_negative
      hx with
    ⟨_yAway, _δAway, _hroundAway, _hδAway, _hwitAway, hpolicy⟩
  rcases hpolicy with ⟨e, hlo, hhi, hexact | hbracket⟩
  · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
    have hx_mem : fmt.unboundedNormalizedSystem x :=
      ⟨true, m, e, hm, hx_eq⟩
    rcases fmt.nearestRoundingToUnbounded_exact_signedRelErrorWitness_lt hx_mem with
      ⟨δ, hδ, hwit, hround⟩
    exact
      ⟨x, δ, hround, hδ, hwit,
        Or.inr ⟨e, hlo, hhi, Or.inl ⟨m, hm, hx_eq, rfl⟩⟩⟩
  · rcases hbracket with ⟨a, b, hadj, hb_nonpos, ha_le_x, hx_le_b, _hy_eq⟩
    rcases hadj.1 with ⟨negative, leftMantissa, eLeft, hmLeft, ha_repr⟩
    let y := nearestAdjacentRoundToEven x a b leftMantissa
    have hround : fmt.nearestRoundingToUnbounded x y := by
      dsimp [y]
      exact
        fmt.nearestAdjacentRoundToEven_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
          leftMantissa hadj ⟨ha_le_x, hx_le_b⟩
    rcases
      fmt.nearestRoundingToUnbounded_signedRelErrorWitness_lt_of_nonpos_between
        hround hadj hb_nonpos ⟨ha_le_x, hx_le_b⟩ with
      ⟨δ, hδ, hwit, _hround⟩
    exact
      ⟨y, δ, hround, hδ, hwit,
        Or.inr ⟨e, hlo, hhi,
          Or.inr
            ⟨a, b, leftMantissa, hadj,
              ⟨negative, eLeft, hmLeft, ha_repr⟩,
              hb_nonpos, ha_le_x, hx_le_b, rfl⟩⟩⟩

/-- Positive finite-normal-range nearest-rounding theorem that preserves the
explicit source-level round-to-even selector evidence. -/
theorem exists_finiteNormalRoundToEven_signedRelErrorWitness_lt_positive_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxlo : fmt.minNormalMagnitude ≤ x)
    (hxhi : x ≤ fmt.maxFiniteMagnitude) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            fmt.sourceRoundToEvenEvidence x y := by
  have hxpos : 0 < x := lt_of_lt_of_le fmt.minNormalMagnitude_pos hxlo
  rcases
    fmt.exists_nearestAdjacentRoundToEven_signedRelErrorWitness_lt_positive
      (x := x) hxpos with
    ⟨y, δ, hround, hδ, hwit, hpolicy⟩
  have hyfin :=
    fmt.nearestRoundingToUnbounded_output_finite_of_minNormalMagnitude_le_of_le_maxFiniteMagnitude
      hround hxlo hxhi
  have hfiniteRound :=
    fmt.nearestRoundingToFinite_of_nearestRoundingToUnbounded_of_finite_of_minNormalMagnitude_le
      hround hyfin hxlo
  exact ⟨y, δ, hfiniteRound, hδ, hwit, hpolicy⟩

/-- Negative finite-normal-range nearest-rounding theorem that preserves the
explicit source-level round-to-even selector evidence. -/
theorem exists_finiteNormalRoundToEven_signedRelErrorWitness_lt_negative_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxlo : -fmt.maxFiniteMagnitude ≤ x)
    (hxhi : x ≤ -fmt.minNormalMagnitude) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            fmt.sourceRoundToEvenEvidence x y := by
  have hxneg : x < 0 := by
    have hmin_pos := fmt.minNormalMagnitude_pos
    linarith
  rcases
    fmt.exists_nearestAdjacentRoundToEven_signedRelErrorWitness_lt_negative
      (x := x) hxneg with
    ⟨y, δ, hround, hδ, hwit, hpolicy⟩
  have hyfin :=
    fmt.nearestRoundingToUnbounded_output_finite_of_neg_maxFiniteMagnitude_le_of_le_neg_minNormalMagnitude
      hround hxlo hxhi
  have hfiniteRound :=
    fmt.nearestRoundingToFinite_of_nearestRoundingToUnbounded_of_finite_of_le_neg_minNormalMagnitude
      hround hyfin hxhi
  exact ⟨y, δ, hfiniteRound, hδ, hwit, hpolicy⟩

/-- Finite-normal-range nearest-rounding theorem that chooses a nearest value
by the source-level round-to-even policy.  This is still a normal-range theorem:
finite underflow/overflow and IEEE exception behavior remain separate. -/
theorem exists_finiteNormalRoundToEven_signedRelErrorWitness_lt_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            fmt.sourceRoundToEvenEvidence x y := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · have hx_abs : |x| = -x := abs_of_neg hneg
    have hxlo : -fmt.maxFiniteMagnitude ≤ x := by
      have h := hx.2
      rw [hx_abs] at h
      linarith
    have hxhi : x ≤ -fmt.minNormalMagnitude := by
      have h := hx.1
      rw [hx_abs] at h
      linarith
    exact
      fmt.exists_finiteNormalRoundToEven_signedRelErrorWitness_lt_negative_finiteNormalRange
        hxlo hxhi
  · subst x
    have hmin_pos := fmt.minNormalMagnitude_pos
    rcases hx with ⟨hxlo, _hxhi⟩
    rw [abs_zero] at hxlo
    exact False.elim (not_lt_of_ge hxlo hmin_pos)
  · have hx_abs : |x| = x := abs_of_pos hpos
    have hxlo : fmt.minNormalMagnitude ≤ x := by
      simpa [hx_abs] using hx.1
    have hxhi : x ≤ fmt.maxFiniteMagnitude := by
      simpa [hx_abs] using hx.2
    exact
      fmt.exists_finiteNormalRoundToEven_signedRelErrorWitness_lt_positive_finiteNormalRange
        hxlo hxhi

/-- Any finite nearest-rounded value of a finite-normal input satisfies the
non-strict forward relative-error model.  This upgrades the relation-valued
existence theorem into an arbitrary-output theorem for the finite nearest
relation; tie choices may select any nearest endpoint. -/
theorem nearestRoundingToFinite_signedRelErrorWitness_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hround : fmt.nearestRoundingToFinite x y)
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases fmt.exists_nearestRoundingToFinite_signedRelErrorWitness_finiteNormalRange
      hx with ⟨y₀, δ₀, hround₀, hδ₀, hwit₀⟩
  have hmin : |x - y| ≤ |x - y₀| :=
    nearestRoundingIn_minimal hround (nearestRoundingIn_mem hround₀)
  have hy₀_bound : |x - y₀| ≤ fmt.unitRoundoff * |x| := by
    have hdiff : x - y₀ = -x * δ₀ := by
      unfold signedRelErrorWitness at hwit₀
      rw [hwit₀]
      ring
    calc
      |x - y₀| = |x| * |δ₀| := by
        rw [hdiff, abs_mul, abs_neg]
      _ ≤ |x| * fmt.unitRoundoff :=
        mul_le_mul_of_nonneg_left hδ₀ (abs_nonneg x)
      _ = fmt.unitRoundoff * |x| := by ring
  have hbound : |x - y| ≤ fmt.unitRoundoff * |x| :=
    le_trans hmin hy₀_bound
  have hx_ne : x ≠ 0 := by
    intro hx_zero
    have hmin_pos := fmt.minNormalMagnitude_pos
    have hxlo := hx.1
    rw [hx_zero, abs_zero] at hxlo
    exact (not_lt_of_ge hxlo) hmin_pos
  exact fmt.signedRelErrorWitness_of_abs_sub_le_unitRoundoff_mul_abs hx_ne hbound

/-- Strict arbitrary-output version of Higham Theorem 2.2 on the finite normal
range: every finite nearest-rounded value, not only the existentially selected
one, satisfies a strict signed relative-error witness. -/
theorem nearestRoundingToFinite_signedRelErrorWitness_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hround : fmt.nearestRoundingToFinite x y)
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases fmt.exists_nearestRoundingToFinite_signedRelErrorWitness_lt_finiteNormalRange
      hx with ⟨y₀, δ₀, hround₀, hδ₀, hwit₀⟩
  have hx_ne : x ≠ 0 := by
    intro hx_zero
    have hmin_pos := fmt.minNormalMagnitude_pos
    have hxlo := hx.1
    rw [hx_zero, abs_zero] at hxlo
    exact (not_lt_of_ge hxlo) hmin_pos
  have hxabs_pos : 0 < |x| := abs_pos.mpr hx_ne
  have hmin : |x - y| ≤ |x - y₀| :=
    nearestRoundingIn_minimal hround (nearestRoundingIn_mem hround₀)
  have hy₀_bound : |x - y₀| < fmt.unitRoundoff * |x| := by
    have hdiff : x - y₀ = -x * δ₀ := by
      unfold signedRelErrorWitness at hwit₀
      rw [hwit₀]
      ring
    calc
      |x - y₀| = |x| * |δ₀| := by
        rw [hdiff, abs_mul, abs_neg]
      _ < |x| * fmt.unitRoundoff :=
        mul_lt_mul_of_pos_left hδ₀ hxabs_pos
      _ = fmt.unitRoundoff * |x| := by ring
  have hbound : |x - y| < fmt.unitRoundoff * |x| :=
    lt_of_le_of_lt hmin hy₀_bound
  exact fmt.signedRelErrorWitness_of_abs_sub_lt_unitRoundoff_mul_abs hx_ne hbound

theorem exists_nearestRoundingToFinite_relErrorComputedDenom_le_unitRoundoff_positive_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxlo : fmt.minNormalMagnitude ≤ x)
    (hxhi : x ≤ fmt.maxFiniteMagnitude) :
    ∃ y : ℝ,
      fmt.nearestRoundingToFinite x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  have hxpos : 0 < x := lt_of_lt_of_le fmt.minNormalMagnitude_pos hxlo
  rcases fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_positive
      (x := x) hxpos with ⟨y, hround, hy_ne, hrel⟩
  have hyfin :=
    fmt.nearestRoundingToUnbounded_output_finite_of_minNormalMagnitude_le_of_le_maxFiniteMagnitude
      hround hxlo hxhi
  have hfiniteRound :=
    fmt.nearestRoundingToFinite_of_nearestRoundingToUnbounded_of_finite_of_minNormalMagnitude_le
      hround hyfin hxlo
  exact ⟨y, hfiniteRound, hy_ne, hrel⟩

theorem exists_nearestRoundingToFinite_relErrorComputedDenom_le_unitRoundoff_negative_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxlo : -fmt.maxFiniteMagnitude ≤ x)
    (hxhi : x ≤ -fmt.minNormalMagnitude) :
    ∃ y : ℝ,
      fmt.nearestRoundingToFinite x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  have hxneg : x < 0 := by
    have hmin_pos := fmt.minNormalMagnitude_pos
    linarith
  rcases fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_negative
      (x := x) hxneg with ⟨y, hround, hy_ne, hrel⟩
  have hyfin :=
    fmt.nearestRoundingToUnbounded_output_finite_of_neg_maxFiniteMagnitude_le_of_le_neg_minNormalMagnitude
      hround hxlo hxhi
  have hfiniteRound :=
    fmt.nearestRoundingToFinite_of_nearestRoundingToUnbounded_of_finite_of_le_neg_minNormalMagnitude
      hround hyfin hxhi
  exact ⟨y, hfiniteRound, hy_ne, hrel⟩

theorem exists_nearestRoundingToFinite_relErrorComputedDenom_le_unitRoundoff_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ y : ℝ,
      fmt.nearestRoundingToFinite x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · have hx_abs : |x| = -x := abs_of_neg hneg
    have hxlo : -fmt.maxFiniteMagnitude ≤ x := by
      have h := hx.2
      rw [hx_abs] at h
      linarith
    have hxhi : x ≤ -fmt.minNormalMagnitude := by
      have h := hx.1
      rw [hx_abs] at h
      linarith
    exact
      fmt.exists_nearestRoundingToFinite_relErrorComputedDenom_le_unitRoundoff_negative_finiteNormalRange
        hxlo hxhi
  · subst x
    have hmin_pos := fmt.minNormalMagnitude_pos
    rcases hx with ⟨hxlo, _hxhi⟩
    rw [abs_zero] at hxlo
    exact False.elim (not_lt_of_ge hxlo hmin_pos)
  · have hx_abs : |x| = x := abs_of_pos hpos
    have hxlo : fmt.minNormalMagnitude ≤ x := by
      simpa [hx_abs] using hx.1
    have hxhi : x ≤ fmt.maxFiniteMagnitude := by
      simpa [hx_abs] using hx.2
    exact
      fmt.exists_nearestRoundingToFinite_relErrorComputedDenom_le_unitRoundoff_positive_finiteNormalRange
        hxlo hxhi

end FloatingPointFormat

/-- Higham Chapter 2 inverse relative-error witness: the computed value is the
exact value divided by a small factor `1 + δ`. -/
def inverseRelErrorWitness (computed exact δ : ℝ) : Prop :=
  1 + δ ≠ 0 ∧ computed = exact / (1 + δ)

/-- Higham Chapter 2 equation (2.5), packaged with a displayed error bound. -/
def inverseRelErrorModel (computed exact u : ℝ) : Prop :=
  ∃ δ : ℝ, |δ| ≤ u ∧ inverseRelErrorWitness computed exact δ

/-- The inverse witness `computed = exact/(1+δ)` is algebraically equivalent to
the usual signed relative-error witness with the computed value as denominator. -/
theorem inverseRelErrorWitness_iff_signedRelErrorWitness (computed exact δ : ℝ)
    (hδ : 1 + δ ≠ 0) :
    inverseRelErrorWitness computed exact δ ↔
      signedRelErrorWitness exact computed δ := by
  constructor
  · intro h
    rcases h with ⟨_, hcomp⟩
    unfold signedRelErrorWitness
    rw [hcomp]
    field_simp [hδ]
  · intro h
    refine ⟨hδ, ?_⟩
    unfold signedRelErrorWitness at h
    rw [h]
    field_simp [hδ]

/-- Computed-denominator relative error is the magnitude of the inverse
relative-error factor. -/
theorem relErrorComputedDenom_eq_abs_inverse_factor (computed exact : ℝ)
    (hcomputed : computed ≠ 0) :
    relErrorComputedDenom computed exact = |exact / computed - 1| := by
  unfold relErrorComputedDenom
  have hrewrite :
      exact / computed - 1 = (exact - computed) / computed := by
    field_simp [hcomputed]
  rw [hrewrite, abs_div, abs_sub_comm]

/-- A computed-denominator relative-error bound yields the inverse model (2.5)
when the exact and computed values are nonzero. -/
theorem inverseRelErrorModel_of_relErrorComputedDenom_le
    (computed exact u : ℝ)
    (hcomputed : computed ≠ 0) (hexact : exact ≠ 0)
    (hbound : relErrorComputedDenom computed exact ≤ u) :
    inverseRelErrorModel computed exact u := by
  let δ : ℝ := exact / computed - 1
  refine ⟨δ, ?_, ?_⟩
  · rw [← relErrorComputedDenom_eq_abs_inverse_factor computed exact hcomputed]
    exact hbound
  · have hden : 1 + δ ≠ 0 := by
      have hone : 1 + δ = exact / computed := by
        unfold δ
        ring
      rw [hone]
      exact div_ne_zero hexact hcomputed
    refine ⟨hden, ?_⟩
    have hone : 1 + δ = exact / computed := by
      unfold δ
      ring
    rw [hone]
    field_simp [hexact, hcomputed]

/-- The inverse model (2.5) implies the computed-denominator relative-error
bound, provided the computed value is nonzero. -/
theorem relErrorComputedDenom_le_of_inverseRelErrorModel
    (computed exact u : ℝ)
    (hcomputed : computed ≠ 0)
    (hmodel : inverseRelErrorModel computed exact u) :
    relErrorComputedDenom computed exact ≤ u := by
  rcases hmodel with ⟨δ, hδbound, hδ⟩
  rcases hδ with ⟨hden, hcomp⟩
  have hsigned : signedRelErrorWitness exact computed δ := by
    exact (inverseRelErrorWitness_iff_signedRelErrorWitness computed exact δ hden).mp
      ⟨hden, hcomp⟩
  have hrel : relError exact computed = |δ| :=
    relError_eq_abs_of_signedRelErrorWitness hcomputed hsigned
  rw [relErrorComputedDenom_eq_relError_swap, hrel]
  exact hδbound

/-- Exact theorem-surface equivalence between Higham's equation (2.5) and a
computed-denominator relative-error bound. -/
theorem inverseRelErrorModel_iff_relErrorComputedDenom_le
    (computed exact u : ℝ)
    (hcomputed : computed ≠ 0) (hexact : exact ≠ 0) :
    inverseRelErrorModel computed exact u ↔
      relErrorComputedDenom computed exact ≤ u := by
  constructor
  · exact relErrorComputedDenom_le_of_inverseRelErrorModel computed exact u hcomputed
  · exact inverseRelErrorModel_of_relErrorComputedDenom_le computed exact u hcomputed hexact

/-- Higham's modified model (2.5) implies the computed-denominator absolute
error form used in Chapter 3 running error analyses:
`|exact - computed| <= u * |computed|`. -/
theorem inverseRelErrorModel_abs_exact_sub_computed_le
    (computed exact u : ℝ)
    (hmodel : inverseRelErrorModel computed exact u) :
    |exact - computed| ≤ u * |computed| := by
  rcases hmodel with ⟨δ, hδbound, hδ⟩
  rcases hδ with ⟨hden, hcomp⟩
  have hsigned : signedRelErrorWitness exact computed δ :=
    (inverseRelErrorWitness_iff_signedRelErrorWitness computed exact δ hden).mp
      ⟨hden, hcomp⟩
  have hdiff : exact - computed = computed * δ := by
    unfold signedRelErrorWitness at hsigned
    rw [hsigned]
    ring
  calc
    |exact - computed| = |computed| * |δ| := by
      rw [hdiff, abs_mul]
    _ ≤ |computed| * u :=
      mul_le_mul_of_nonneg_left hδbound (abs_nonneg computed)
    _ = u * |computed| := by ring

namespace FloatingPointFormat

theorem exists_nearestRoundingToFinite_inverseRelErrorModel_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ y : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        inverseRelErrorModel y x fmt.unitRoundoff := by
  rcases fmt.exists_nearestRoundingToFinite_relErrorComputedDenom_le_unitRoundoff_finiteNormalRange
      hx with ⟨y, hround, hy_ne, hrel⟩
  have hx_ne : x ≠ 0 := by
    intro hx_zero
    have hmin_pos := fmt.minNormalMagnitude_pos
    have hxlo := hx.1
    rw [hx_zero, abs_zero] at hxlo
    exact (not_lt_of_ge hxlo) hmin_pos
  exact
    ⟨y, hround,
      inverseRelErrorModel_of_relErrorComputedDenom_le
        y x fmt.unitRoundoff hy_ne hx_ne hrel⟩

theorem exists_nearestRoundingToFinite_inverseRelErrorWitness_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ inverseRelErrorWitness y x δ := by
  rcases fmt.exists_nearestRoundingToFinite_inverseRelErrorModel_finiteNormalRange
      hx with ⟨y, hround, hmodel⟩
  rcases hmodel with ⟨δ, hδ, hwit⟩
  exact ⟨y, δ, hround, hδ, hwit⟩

/-- Source-style round-away tie choice for `fl` on the finite normal range.
Exact representable inputs return themselves; non-exact inputs use
`nearestAdjacentRoundAway` after sign and exponent-slice bracketing.  This is
not a full finite-format operation with underflow/overflow or IEEE exceptions. -/
noncomputable def finiteNormalRoundAway (fmt : FloatingPointFormat) (x : ℝ)
    (hx : fmt.finiteNormalRange x) : ℝ :=
  Classical.choose
    (fmt.exists_finiteNormalRoundAway_signedRelErrorWitness_lt_finiteNormalRange hx)

theorem finiteNormalRoundAway_spec
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite x (fmt.finiteNormalRoundAway x hx) ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness (fmt.finiteNormalRoundAway x hx) x δ ∧
            fmt.sourceRoundAwayEvidence x (fmt.finiteNormalRoundAway x hx) := by
  exact
    Classical.choose_spec
      (fmt.exists_finiteNormalRoundAway_signedRelErrorWitness_lt_finiteNormalRange hx)

theorem finiteNormalRoundAway_nearestRoundingToFinite
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.nearestRoundingToFinite x (fmt.finiteNormalRoundAway x hx) := by
  rcases fmt.finiteNormalRoundAway_spec hx with ⟨δ, hround, _hδ, _hwit, _hpolicy⟩
  exact hround

theorem finiteNormalRoundAway_sourceRoundAwayEvidence
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.sourceRoundAwayEvidence x (fmt.finiteNormalRoundAway x hx) := by
  rcases fmt.finiteNormalRoundAway_spec hx with ⟨δ, _hround, _hδ, _hwit, hpolicy⟩
  exact hpolicy

theorem finiteNormalRoundAway_signedRelErrorWitness_lt
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite x (fmt.finiteNormalRoundAway x hx) ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness (fmt.finiteNormalRoundAway x hx) x δ := by
  rcases fmt.finiteNormalRoundAway_spec hx with ⟨δ, hround, hδ, hwit, _hpolicy⟩
  exact ⟨δ, hround, hδ, hwit⟩

theorem finiteNormalRoundAway_inverseRelErrorModel
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    inverseRelErrorModel (fmt.finiteNormalRoundAway x hx) x
      fmt.unitRoundoff := by
  have hpolicy := fmt.finiteNormalRoundAway_sourceRoundAwayEvidence hx
  rcases
    fmt.sourceRoundAwayEvidence_relErrorComputedDenom_le_unitRoundoff
      hx hpolicy with
    ⟨hy_ne, hrel⟩
  have hx_ne := fmt.finiteNormalRange_ne_zero hx
  exact
    inverseRelErrorModel_of_relErrorComputedDenom_le
      (fmt.finiteNormalRoundAway x hx) x fmt.unitRoundoff hy_ne hx_ne hrel

theorem finiteNormalRoundAway_inverseRelErrorWitness
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite x (fmt.finiteNormalRoundAway x hx) ∧
        |δ| ≤ fmt.unitRoundoff ∧
          inverseRelErrorWitness (fmt.finiteNormalRoundAway x hx) x δ := by
  rcases fmt.finiteNormalRoundAway_inverseRelErrorModel hx with ⟨δ, hδ, hwit⟩
  exact ⟨δ, fmt.finiteNormalRoundAway_nearestRoundingToFinite hx, hδ, hwit⟩

/-- Source-style round-to-even tie choice for `fl` on the finite normal range.
Exact representable inputs return themselves; non-exact inputs use
`nearestAdjacentRoundToEven` after sign and exponent-slice bracketing, with the
left endpoint's normalized mantissa recorded for tie parity.  This is not a
full finite-format operation with underflow/overflow or IEEE exceptions. -/
noncomputable def finiteNormalRoundToEven (fmt : FloatingPointFormat) (x : ℝ)
    (hx : fmt.finiteNormalRange x) : ℝ :=
  Classical.choose
    (fmt.exists_finiteNormalRoundToEven_signedRelErrorWitness_lt_finiteNormalRange hx)

theorem finiteNormalRoundToEven_spec
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite x (fmt.finiteNormalRoundToEven x hx) ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness (fmt.finiteNormalRoundToEven x hx) x δ ∧
            fmt.sourceRoundToEvenEvidence x (fmt.finiteNormalRoundToEven x hx) := by
  exact
    Classical.choose_spec
      (fmt.exists_finiteNormalRoundToEven_signedRelErrorWitness_lt_finiteNormalRange hx)

theorem finiteNormalRoundToEven_nearestRoundingToFinite
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.nearestRoundingToFinite x (fmt.finiteNormalRoundToEven x hx) := by
  rcases fmt.finiteNormalRoundToEven_spec hx with
    ⟨δ, hround, _hδ, _hwit, _hpolicy⟩
  exact hround

theorem finiteNormalRoundToEven_sourceRoundToEvenEvidence
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.sourceRoundToEvenEvidence x (fmt.finiteNormalRoundToEven x hx) := by
  rcases fmt.finiteNormalRoundToEven_spec hx with
    ⟨δ, _hround, _hδ, _hwit, hpolicy⟩
  exact hpolicy

theorem finiteNormalRoundToEven_eq_of_sourceRoundToEvenEvidence
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteNormalRange x)
    (hpolicy : fmt.sourceRoundToEvenEvidence x y) :
    fmt.finiteNormalRoundToEven x hx = y :=
  sourceRoundToEvenEvidence_unique
    (fmt.finiteNormalRoundToEven_sourceRoundToEvenEvidence hx) hpolicy

theorem finiteNormalRoundToEven_neg
    {fmt : FloatingPointFormat} {x : ℝ}
    (hbeta : evenMantissa fmt.beta) (ht : 1 < fmt.t)
    (hx : fmt.finiteNormalRange x) (hxneg : fmt.finiteNormalRange (-x)) :
    fmt.finiteNormalRoundToEven (-x) hxneg =
      -fmt.finiteNormalRoundToEven x hx := by
  have hpolicy :=
    fmt.finiteNormalRoundToEven_sourceRoundToEvenEvidence hx
  have hpolicy_neg :=
    fmt.sourceRoundToEvenEvidence_neg hbeta ht hpolicy
  exact
    fmt.finiteNormalRoundToEven_eq_of_sourceRoundToEvenEvidence
      hxneg hpolicy_neg

theorem finiteNormalRoundToEven_signedRelErrorWitness_lt
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite x (fmt.finiteNormalRoundToEven x hx) ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness (fmt.finiteNormalRoundToEven x hx) x δ := by
  rcases fmt.finiteNormalRoundToEven_spec hx with
    ⟨δ, hround, hδ, hwit, _hpolicy⟩
  exact ⟨δ, hround, hδ, hwit⟩

theorem finiteNormalRoundToEven_inverseRelErrorModel
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    inverseRelErrorModel (fmt.finiteNormalRoundToEven x hx) x
      fmt.unitRoundoff := by
  have hpolicy := fmt.finiteNormalRoundToEven_sourceRoundToEvenEvidence hx
  rcases
    fmt.sourceRoundToEvenEvidence_relErrorComputedDenom_le_unitRoundoff
      hx hpolicy with
    ⟨hy_ne, hrel⟩
  have hx_ne := fmt.finiteNormalRange_ne_zero hx
  exact
    inverseRelErrorModel_of_relErrorComputedDenom_le
      (fmt.finiteNormalRoundToEven x hx) x fmt.unitRoundoff hy_ne hx_ne hrel

theorem finiteNormalRoundToEven_inverseRelErrorWitness
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite x (fmt.finiteNormalRoundToEven x hx) ∧
        |δ| ≤ fmt.unitRoundoff ∧
          inverseRelErrorWitness (fmt.finiteNormalRoundToEven x hx) x δ := by
  rcases fmt.finiteNormalRoundToEven_inverseRelErrorModel hx with ⟨δ, hδ, hwit⟩
  exact ⟨δ, fmt.finiteNormalRoundToEven_nearestRoundingToFinite hx, hδ, hwit⟩

/-- Source-style finite-normal selector for rounding toward negative infinity.
This is a normal-range selector only; finite underflow/overflow and IEEE flags
are handled by later total finite/IEEE layers. -/
noncomputable def finiteNormalRoundTowardNegative
    (fmt : FloatingPointFormat) (x : ℝ) (hx : fmt.finiteNormalRange x) : ℝ :=
  Classical.choose (fmt.exists_sourceRoundTowardNegativeEvidence_finiteNormalRange hx)

theorem finiteNormalRoundTowardNegative_sourceRoundTowardNegativeEvidence
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.sourceRoundTowardNegativeEvidence x
      (fmt.finiteNormalRoundTowardNegative x hx) :=
  Classical.choose_spec
    (fmt.exists_sourceRoundTowardNegativeEvidence_finiteNormalRange hx)

theorem finiteNormalRoundTowardNegative_unboundedNormalizedSystem
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.unboundedNormalizedSystem (fmt.finiteNormalRoundTowardNegative x hx) :=
  fmt.sourceRoundTowardNegativeEvidence_unboundedNormalizedSystem
    (fmt.finiteNormalRoundTowardNegative_sourceRoundTowardNegativeEvidence hx)

theorem finiteNormalRoundTowardNegative_le
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.finiteNormalRoundTowardNegative x hx ≤ x :=
  sourceRoundTowardNegativeEvidence_le
    (fmt.finiteNormalRoundTowardNegative_sourceRoundTowardNegativeEvidence hx)

/-- Source-style finite-normal selector for rounding toward positive infinity. -/
noncomputable def finiteNormalRoundTowardPositive
    (fmt : FloatingPointFormat) (x : ℝ) (hx : fmt.finiteNormalRange x) : ℝ :=
  Classical.choose (fmt.exists_sourceRoundTowardPositiveEvidence_finiteNormalRange hx)

theorem finiteNormalRoundTowardPositive_sourceRoundTowardPositiveEvidence
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.sourceRoundTowardPositiveEvidence x
      (fmt.finiteNormalRoundTowardPositive x hx) :=
  Classical.choose_spec
    (fmt.exists_sourceRoundTowardPositiveEvidence_finiteNormalRange hx)

theorem finiteNormalRoundTowardPositive_unboundedNormalizedSystem
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.unboundedNormalizedSystem (fmt.finiteNormalRoundTowardPositive x hx) :=
  fmt.sourceRoundTowardPositiveEvidence_unboundedNormalizedSystem
    (fmt.finiteNormalRoundTowardPositive_sourceRoundTowardPositiveEvidence hx)

theorem le_finiteNormalRoundTowardPositive
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    x ≤ fmt.finiteNormalRoundTowardPositive x hx :=
  sourceRoundTowardPositiveEvidence_le
    (fmt.finiteNormalRoundTowardPositive_sourceRoundTowardPositiveEvidence hx)

/-- Source-style finite-normal selector for rounding toward zero. -/
noncomputable def finiteNormalRoundTowardZero
    (fmt : FloatingPointFormat) (x : ℝ) (hx : fmt.finiteNormalRange x) : ℝ :=
  Classical.choose (fmt.exists_sourceRoundTowardZeroEvidence_finiteNormalRange hx)

theorem finiteNormalRoundTowardZero_sourceRoundTowardZeroEvidence
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.sourceRoundTowardZeroEvidence x
      (fmt.finiteNormalRoundTowardZero x hx) :=
  Classical.choose_spec
    (fmt.exists_sourceRoundTowardZeroEvidence_finiteNormalRange hx)

theorem finiteNormalRoundTowardZero_unboundedNormalizedSystem
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.unboundedNormalizedSystem (fmt.finiteNormalRoundTowardZero x hx) :=
  fmt.sourceRoundTowardZeroEvidence_unboundedNormalizedSystem
    (fmt.finiteNormalRoundTowardZero_sourceRoundTowardZeroEvidence hx)

theorem finiteNormalRoundTowardZero_abs_le_abs
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    |fmt.finiteNormalRoundTowardZero x hx| ≤ |x| :=
  sourceRoundTowardZeroEvidence_abs_le_abs
    (fmt.finiteNormalRoundTowardZero_sourceRoundTowardZeroEvidence hx)

/-- Values that are neither in the source-facing underflow range nor in the
source-facing overflow range are exactly in the finite normal magnitude band. -/
theorem finiteNormalRange_of_not_finiteUnderflowRange_of_not_finiteOverflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : ¬ fmt.finiteUnderflowRange x)
    (hover : ¬ fmt.finiteOverflowRange x) :
    fmt.finiteNormalRange x := by
  have hmin : fmt.minNormalMagnitude ≤ |x| := by
    rw [finiteUnderflowRange] at hunder
    exact le_of_not_gt hunder
  have hmax : |x| ≤ fmt.maxFiniteMagnitude := by
    rw [finiteOverflowRange] at hover
    exact le_of_not_gt hover
  exact ⟨hmin, hmax⟩

/-- Total source-facing finite selector for rounding toward negative infinity.
Underflow uses the subnormal directed lattice, finite-normal inputs use the
source-level adjacent-bracket selector, and overflow uses finite saturation.
This is still a finite-value selector; IEEE infinities and flags are modeled by
the separate IEEE result layer. -/
noncomputable def finiteRoundTowardNegative
    (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  by
    classical
    exact
      if hunder : fmt.finiteUnderflowRange x then
        fmt.finiteUnderflowRoundTowardNegative x
      else if hover : fmt.finiteOverflowRange x then
        fmt.finiteOverflowSaturation x
      else
        fmt.finiteNormalRoundTowardNegative x
          (fmt.finiteNormalRange_of_not_finiteUnderflowRange_of_not_finiteOverflowRange
            hunder hover)

/-- Total source-facing finite selector for rounding toward positive infinity. -/
noncomputable def finiteRoundTowardPositive
    (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  by
    classical
    exact
      if hunder : fmt.finiteUnderflowRange x then
        fmt.finiteUnderflowRoundTowardPositive x
      else if hover : fmt.finiteOverflowRange x then
        fmt.finiteOverflowSaturation x
      else
        fmt.finiteNormalRoundTowardPositive x
          (fmt.finiteNormalRange_of_not_finiteUnderflowRange_of_not_finiteOverflowRange
            hunder hover)

/-- Total source-facing finite selector for rounding toward zero. -/
noncomputable def finiteRoundTowardZero
    (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  by
    classical
    exact
      if hunder : fmt.finiteUnderflowRange x then
        fmt.finiteUnderflowRoundTowardZero x
      else if hover : fmt.finiteOverflowRange x then
        fmt.finiteOverflowSaturation x
      else
        fmt.finiteNormalRoundTowardZero x
          (fmt.finiteNormalRange_of_not_finiteUnderflowRange_of_not_finiteOverflowRange
            hunder hover)

theorem finiteRoundTowardNegative_eq_underflow
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    fmt.finiteRoundTowardNegative x =
      fmt.finiteUnderflowRoundTowardNegative x := by
  classical
  unfold finiteRoundTowardNegative
  simp [hunder]

theorem finiteRoundTowardPositive_eq_underflow
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    fmt.finiteRoundTowardPositive x =
      fmt.finiteUnderflowRoundTowardPositive x := by
  classical
  unfold finiteRoundTowardPositive
  simp [hunder]

theorem finiteRoundTowardZero_eq_underflow
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    fmt.finiteRoundTowardZero x =
      fmt.finiteUnderflowRoundTowardZero x := by
  classical
  unfold finiteRoundTowardZero
  simp [hunder]

theorem finiteRoundTowardNegative_eq_overflow_of_not_underflow
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : ¬ fmt.finiteUnderflowRange x)
    (hover : fmt.finiteOverflowRange x) :
    fmt.finiteRoundTowardNegative x = fmt.finiteOverflowSaturation x := by
  classical
  unfold finiteRoundTowardNegative
  simp [hunder, hover]

theorem finiteRoundTowardPositive_eq_overflow_of_not_underflow
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : ¬ fmt.finiteUnderflowRange x)
    (hover : fmt.finiteOverflowRange x) :
    fmt.finiteRoundTowardPositive x = fmt.finiteOverflowSaturation x := by
  classical
  unfold finiteRoundTowardPositive
  simp [hunder, hover]

theorem finiteRoundTowardZero_eq_overflow_of_not_underflow
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : ¬ fmt.finiteUnderflowRange x)
    (hover : fmt.finiteOverflowRange x) :
    fmt.finiteRoundTowardZero x = fmt.finiteOverflowSaturation x := by
  classical
  unfold finiteRoundTowardZero
  simp [hunder, hover]

theorem finiteRoundTowardNegative_le_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    fmt.finiteRoundTowardNegative x ≤ x := by
  rw [fmt.finiteRoundTowardNegative_eq_underflow hunder]
  exact fmt.finiteUnderflowRoundTowardNegative_le hunder

theorem le_finiteRoundTowardPositive_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    x ≤ fmt.finiteRoundTowardPositive x := by
  rw [fmt.finiteRoundTowardPositive_eq_underflow hunder]
  exact fmt.le_finiteUnderflowRoundTowardPositive hunder

theorem finiteRoundTowardZero_abs_le_abs_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    |fmt.finiteRoundTowardZero x| ≤ |x| := by
  rw [fmt.finiteRoundTowardZero_eq_underflow hunder]
  exact fmt.finiteUnderflowRoundTowardZero_abs_le_abs hunder

theorem finiteRoundTowardNegative_le_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.finiteRoundTowardNegative x ≤ x := by
  classical
  unfold finiteRoundTowardNegative
  have hunder : ¬ fmt.finiteUnderflowRange x := by
    intro h
    exact not_lt_of_ge hx.1 h
  have hover : ¬ fmt.finiteOverflowRange x := by
    intro h
    exact not_lt_of_ge hx.2 h
  simp [hunder, hover]
  exact fmt.finiteNormalRoundTowardNegative_le _

theorem le_finiteRoundTowardPositive_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    x ≤ fmt.finiteRoundTowardPositive x := by
  classical
  unfold finiteRoundTowardPositive
  have hunder : ¬ fmt.finiteUnderflowRange x := by
    intro h
    exact not_lt_of_ge hx.1 h
  have hover : ¬ fmt.finiteOverflowRange x := by
    intro h
    exact not_lt_of_ge hx.2 h
  simp [hunder, hover]
  exact fmt.le_finiteNormalRoundTowardPositive _

theorem finiteRoundTowardZero_abs_le_abs_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    |fmt.finiteRoundTowardZero x| ≤ |x| := by
  classical
  unfold finiteRoundTowardZero
  have hunder : ¬ fmt.finiteUnderflowRange x := by
    intro h
    exact not_lt_of_ge hx.1 h
  have hover : ¬ fmt.finiteOverflowRange x := by
    intro h
    exact not_lt_of_ge hx.2 h
  simp [hunder, hover]
  exact fmt.finiteNormalRoundTowardZero_abs_le_abs _

theorem finiteRoundTowardZero_abs_le_abs
    (fmt : FloatingPointFormat) (x : ℝ) :
    |fmt.finiteRoundTowardZero x| ≤ |x| := by
  classical
  unfold finiteRoundTowardZero
  by_cases hunder : fmt.finiteUnderflowRange x
  · simp [hunder]
    exact fmt.finiteUnderflowRoundTowardZero_abs_le_abs hunder
  · simp [hunder]
    by_cases hover : fmt.finiteOverflowRange x
    · simp [hover]
      exact fmt.finiteOverflowSaturation_abs_le_abs_of_finiteOverflowRange
        hover
    · simp [hover]
      exact fmt.finiteNormalRoundTowardZero_abs_le_abs _

/-- Total source-facing finite round-away selector.  Underflow uses the
subnormal-lattice round-away selector, finite normal inputs use the
source-level adjacent-bracket round-away selector, and overflow saturates to
the signed largest finite endpoint.  This is still not an IEEE operation:
exception flags, infinities, NaNs, directed modes, and signed zeros are outside
this model. -/
noncomputable def finiteRoundAway (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  by
    classical
    exact
      if hunder : fmt.finiteUnderflowRange x then
        fmt.finiteUnderflowRoundAway x
      else if hover : fmt.finiteOverflowRange x then
        fmt.finiteOverflowSaturation x
      else
        fmt.finiteNormalRoundAway x (by
          have hmin : fmt.minNormalMagnitude ≤ |x| := by
            rw [finiteUnderflowRange] at hunder
            exact le_of_not_gt hunder
          have hmax : |x| ≤ fmt.maxFiniteMagnitude := by
            rw [finiteOverflowRange] at hover
            exact le_of_not_gt hover
          exact ⟨hmin, hmax⟩)

theorem finiteRoundAway_nearestRoundingToFinite
    (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.nearestRoundingToFinite x (fmt.finiteRoundAway x) := by
  classical
  unfold finiteRoundAway
  by_cases hunder : fmt.finiteUnderflowRange x
  · simp [hunder]
    exact fmt.finiteUnderflowRoundAway_nearestRoundingToFinite hunder
  · simp [hunder]
    by_cases hover : fmt.finiteOverflowRange x
    · simp [hover]
      exact
        fmt.finiteOverflowSaturation_nearestRoundingToFinite_of_finiteOverflowRange
          hover
    · simp [hover]
      exact fmt.finiteNormalRoundAway_nearestRoundingToFinite _

theorem finiteRoundAway_output_not_finiteOverflowRange
    (fmt : FloatingPointFormat) (x : ℝ) :
    ¬ fmt.finiteOverflowRange (fmt.finiteRoundAway x) :=
  fmt.nearestRoundingToFinite_output_not_finiteOverflowRange
    (fmt.finiteRoundAway_nearestRoundingToFinite x)

theorem finiteRoundAway_output_abs_le_maxFiniteMagnitude
    (fmt : FloatingPointFormat) (x : ℝ) :
    |fmt.finiteRoundAway x| ≤ fmt.maxFiniteMagnitude :=
  fmt.nearestRoundingToFinite_output_abs_le_maxFiniteMagnitude
    (fmt.finiteRoundAway_nearestRoundingToFinite x)

theorem finiteRoundAway_sourceRoundAwayEvidence_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.sourceRoundAwayEvidence x (fmt.finiteRoundAway x) := by
  classical
  unfold finiteRoundAway
  have hunder : ¬ fmt.finiteUnderflowRange x := by
    intro h
    exact not_lt_of_ge hx.1 h
  have hover : ¬ fmt.finiteOverflowRange x := by
    intro h
    exact not_lt_of_ge hx.2 h
  simp [hunder, hover]
  exact fmt.finiteNormalRoundAway_sourceRoundAwayEvidence _

theorem finiteRoundAway_signedRelErrorWitness_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite x (fmt.finiteRoundAway x) ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness (fmt.finiteRoundAway x) x δ := by
  have hround := fmt.finiteRoundAway_nearestRoundingToFinite x
  rcases
    fmt.nearestRoundingToFinite_signedRelErrorWitness_lt_of_finiteNormalRange
      hround hx with
    ⟨δ, hδ, hwit⟩
  exact ⟨δ, hround, hδ, hwit⟩

theorem finiteRoundAway_inverseRelErrorModel_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    inverseRelErrorModel (fmt.finiteRoundAway x) x fmt.unitRoundoff := by
  have hpolicy :=
    fmt.finiteRoundAway_sourceRoundAwayEvidence_of_finiteNormalRange hx
  rcases
    fmt.sourceRoundAwayEvidence_relErrorComputedDenom_le_unitRoundoff
      hx hpolicy with
    ⟨hy_ne, hrel⟩
  have hx_ne := fmt.finiteNormalRange_ne_zero hx
  exact
    inverseRelErrorModel_of_relErrorComputedDenom_le
      (fmt.finiteRoundAway x) x fmt.unitRoundoff hy_ne hx_ne hrel

theorem finiteRoundAway_inverseRelErrorWitness_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite x (fmt.finiteRoundAway x) ∧
        |δ| ≤ fmt.unitRoundoff ∧
          inverseRelErrorWitness (fmt.finiteRoundAway x) x δ := by
  rcases
    fmt.finiteRoundAway_inverseRelErrorModel_of_finiteNormalRange hx with
    ⟨δ, hδ, hwit⟩
  exact ⟨δ, fmt.finiteRoundAway_nearestRoundingToFinite x, hδ, hwit⟩

/-- Total source-facing finite round-to-even selector.  Underflow uses the
subnormal-lattice round-to-even selector, finite normal inputs use the
source-level adjacent-bracket round-to-even selector, and overflow saturates to
the signed largest finite endpoint.  This is still not an IEEE operation:
exception flags, infinities, NaNs, directed modes, and signed zeros are outside
this model. -/
noncomputable def finiteRoundToEven (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  by
    classical
    exact
      if hunder : fmt.finiteUnderflowRange x then
        fmt.finiteUnderflowRoundToEven x
      else if hover : fmt.finiteOverflowRange x then
        fmt.finiteOverflowSaturation x
      else
        fmt.finiteNormalRoundToEven x (by
          have hmin : fmt.minNormalMagnitude ≤ |x| := by
            rw [finiteUnderflowRange] at hunder
            exact le_of_not_gt hunder
          have hmax : |x| ≤ fmt.maxFiniteMagnitude := by
            rw [finiteOverflowRange] at hover
            exact le_of_not_gt hover
          exact ⟨hmin, hmax⟩)

/-- Total source-facing finite selector parameterized by an IEEE rounding mode.
The nearest/even branch uses the nearest-even finite selector, while the
directed branches use the total finite directed selectors.  This remains a
finite real-valued selector; IEEE infinities, NaNs, signed zeros, and exception
flags live in the separate IEEE result layer. -/
noncomputable def finiteRoundToMode
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) : ℝ :=
  match mode with
  | IeeeRoundingMode.nearestEven => fmt.finiteRoundToEven x
  | IeeeRoundingMode.towardZero => fmt.finiteRoundTowardZero x
  | IeeeRoundingMode.towardPositive => fmt.finiteRoundTowardPositive x
  | IeeeRoundingMode.towardNegative => fmt.finiteRoundTowardNegative x

theorem finiteRoundToMode_nearestEven
    (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.finiteRoundToMode IeeeRoundingMode.nearestEven x =
      fmt.finiteRoundToEven x := rfl

theorem finiteRoundToMode_towardZero
    (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.finiteRoundToMode IeeeRoundingMode.towardZero x =
      fmt.finiteRoundTowardZero x := rfl

theorem finiteRoundToMode_towardPositive
    (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.finiteRoundToMode IeeeRoundingMode.towardPositive x =
      fmt.finiteRoundTowardPositive x := rfl

theorem finiteRoundToMode_towardNegative
    (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.finiteRoundToMode IeeeRoundingMode.towardNegative x =
      fmt.finiteRoundTowardNegative x := rfl

/-- Operation-level finite rounding selector parameterized by an IEEE rounding
mode. -/
noncomputable def finiteRoundToModeOp
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (op : BasicOp) (x y : ℝ) : ℝ :=
  fmt.finiteRoundToMode mode (BasicOp.exact op x y)

/-- IEEE-facing wrapper for the source-facing finite round-to-even selector.
It is finite and flag-free by construction; full IEEE exception and special
value behavior is represented by separate future semantics. -/
noncomputable def finiteRoundToEvenIeeeFiniteResult
    (fmt : FloatingPointFormat) (x : ℝ) : IeeeOperationResult :=
  IeeeOperationResult.finiteNoFlags (fmt.finiteRoundToEven x)

theorem finiteRoundToEvenIeeeFiniteResult_isFinite
    (fmt : FloatingPointFormat) (x : ℝ) :
    (fmt.finiteRoundToEvenIeeeFiniteResult x).isFinite :=
  IeeeOperationResult.finiteNoFlags_isFinite _

theorem finiteRoundToEvenIeeeFiniteResult_noFlags
    (fmt : FloatingPointFormat) (x : ℝ) :
    (fmt.finiteRoundToEvenIeeeFiniteResult x).noFlags :=
  IeeeOperationResult.finiteNoFlags_noFlags _

theorem finiteRoundToEvenIeeeFiniteResult_toReal?
    (fmt : FloatingPointFormat) (x : ℝ) :
    (fmt.finiteRoundToEvenIeeeFiniteResult x).value.toReal? =
      some (fmt.finiteRoundToEven x) :=
  IeeeOperationResult.finiteNoFlags_toReal? _

theorem finiteRoundToEven_nearestRoundingToFinite
    (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.nearestRoundingToFinite x (fmt.finiteRoundToEven x) := by
  classical
  unfold finiteRoundToEven
  by_cases hunder : fmt.finiteUnderflowRange x
  · simp [hunder]
    exact fmt.finiteUnderflowRoundToEven_nearestRoundingToFinite hunder
  · simp [hunder]
    by_cases hover : fmt.finiteOverflowRange x
    · simp [hover]
      exact
        fmt.finiteOverflowSaturation_nearestRoundingToFinite_of_finiteOverflowRange
          hover
    · simp [hover]
      exact fmt.finiteNormalRoundToEven_nearestRoundingToFinite _

/-- The total finite round-to-even selector always returns a finite
representable value. -/
theorem finiteRoundToEven_finiteSystem
    (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.finiteSystem (fmt.finiteRoundToEven x) :=
  nearestRoundingIn_mem (fmt.finiteRoundToEven_nearestRoundingToFinite x)

theorem finiteRoundToEven_neg_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    fmt.finiteRoundToEven (-x) = -fmt.finiteRoundToEven x := by
  classical
  have hunder_neg : fmt.finiteUnderflowRange (-x) :=
    (fmt.finiteUnderflowRange_neg_iff x).2 hunder
  unfold finiteRoundToEven
  simp [hunder, hunder_neg, fmt.finiteUnderflowRoundToEven_neg x]

theorem finiteRoundToEven_neg_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hover : fmt.finiteOverflowRange x) :
    fmt.finiteRoundToEven (-x) = -fmt.finiteRoundToEven x := by
  classical
  have hover_neg : fmt.finiteOverflowRange (-x) :=
    (fmt.finiteOverflowRange_neg_iff x).2 hover
  have hunder : ¬ fmt.finiteUnderflowRange x := by
    intro hunder
    have hle := fmt.minNormalMagnitude_le_maxFiniteMagnitude
    rw [finiteUnderflowRange] at hunder
    rw [finiteOverflowRange] at hover
    linarith
  have hunder_neg : ¬ fmt.finiteUnderflowRange (-x) := by
    intro h
    exact hunder ((fmt.finiteUnderflowRange_neg_iff x).1 h)
  unfold finiteRoundToEven
  simp [hunder, hunder_neg, hover, hover_neg,
    fmt.finiteOverflowSaturation_neg_of_finiteOverflowRange hover]

theorem finiteRoundToEven_neg_of_not_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hnot : ¬ fmt.finiteNormalRange x) :
    fmt.finiteRoundToEven (-x) = -fmt.finiteRoundToEven x := by
  by_cases hunder : fmt.finiteUnderflowRange x
  · exact fmt.finiteRoundToEven_neg_of_finiteUnderflowRange hunder
  · by_cases hover : fmt.finiteOverflowRange x
    · exact fmt.finiteRoundToEven_neg_of_finiteOverflowRange hover
    · have hnormal :=
        fmt.finiteNormalRange_of_not_finiteUnderflowRange_of_not_finiteOverflowRange
          hunder hover
      exact False.elim (hnot hnormal)

/-- On source-facing underflow inputs, the total finite round-to-even selector
satisfies Higham's gradual-underflow additive absolute-error bound. -/
theorem finiteRoundToEven_absError_le_gradualUnderflowEtaBound_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    absError (fmt.finiteRoundToEven x) x ≤ fmt.gradualUnderflowEtaBound := by
  classical
  unfold finiteRoundToEven
  simp [hunder]
  exact fmt.finiteUnderflowRoundToEven_absError_le_gradualUnderflowEtaBound hunder

/-- Strict source-facing underflow absolute-error bound for the total finite
round-to-even selector, away from exact half-cell ties. -/
theorem finiteRoundToEven_absError_lt_gradualUnderflowEtaBound_of_finiteUnderflowRange_of_noHalfTie
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x)
    (hnotie : fmt.finiteUnderflowNoHalfTie x) :
    absError (fmt.finiteRoundToEven x) x < fmt.gradualUnderflowEtaBound := by
  classical
  unfold finiteRoundToEven
  simp [hunder]
  exact
    fmt.finiteUnderflowRoundToEven_absError_lt_gradualUnderflowEtaBound_of_noHalfTie
      hunder hnotie

/-- Underflow branch of Higham's additive model (2.8) for the total finite
round-to-even selector: `δ = 0` and the additive term is the absolute rounding
error, bounded by the gradual-underflow `eta` constant. -/
theorem finiteRoundToEven_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    ∃ η : ℝ,
      additiveUnderflowModelWitness (fmt.finiteRoundToEven x) x
        fmt.unitRoundoff fmt.gradualUnderflowEtaBound 0 η := by
  exact
    ⟨fmt.finiteRoundToEven x - x,
      additiveUnderflowModelWitness_underflow_branch_of_absError_le
        fmt.unitRoundoff_pos
        (fmt.finiteRoundToEven_absError_le_gradualUnderflowEtaBound_of_finiteUnderflowRange
          hunder)⟩

/-- Strict underflow branch of Higham's additive model (2.8) for the total
finite round-to-even selector, away from exact half-cell ties. -/
theorem finiteRoundToEven_strictAdditiveUnderflowModel_underflow_branch_of_finiteUnderflowRange_of_noHalfTie
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x)
    (hnotie : fmt.finiteUnderflowNoHalfTie x) :
    ∃ η : ℝ,
      strictAdditiveUnderflowModelWitness (fmt.finiteRoundToEven x) x
        fmt.unitRoundoff fmt.gradualUnderflowEtaBound 0 η := by
  exact
    ⟨fmt.finiteRoundToEven x - x,
      strictAdditiveUnderflowModelWitness_underflow_branch_of_absError_lt
        fmt.unitRoundoff_pos
        (fmt.finiteRoundToEven_absError_lt_gradualUnderflowEtaBound_of_finiteUnderflowRange_of_noHalfTie
          hunder hnotie)⟩

theorem finiteRoundToEven_output_not_finiteOverflowRange
    (fmt : FloatingPointFormat) (x : ℝ) :
    ¬ fmt.finiteOverflowRange (fmt.finiteRoundToEven x) :=
  fmt.nearestRoundingToFinite_output_not_finiteOverflowRange
    (fmt.finiteRoundToEven_nearestRoundingToFinite x)

theorem finiteRoundToEven_output_abs_le_maxFiniteMagnitude
    (fmt : FloatingPointFormat) (x : ℝ) :
    |fmt.finiteRoundToEven x| ≤ fmt.maxFiniteMagnitude :=
  fmt.nearestRoundingToFinite_output_abs_le_maxFiniteMagnitude
    (fmt.finiteRoundToEven_nearestRoundingToFinite x)

theorem finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) := by
  classical
  unfold finiteRoundToEven
  have hunder : ¬ fmt.finiteUnderflowRange x := by
    intro h
    exact not_lt_of_ge hx.1 h
  have hover : ¬ fmt.finiteOverflowRange x := by
    intro h
    exact not_lt_of_ge hx.2 h
  simp [hunder, hover]
  exact fmt.finiteNormalRoundToEven_sourceRoundToEvenEvidence _

theorem finiteRoundToEven_eq_finiteNormalRoundToEven_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.finiteRoundToEven x = fmt.finiteNormalRoundToEven x hx :=
  sourceRoundToEvenEvidence_unique
    (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hx)
    (fmt.finiteNormalRoundToEven_sourceRoundToEvenEvidence hx)

theorem finiteRoundToEven_neg_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hbeta : evenMantissa fmt.beta) (ht : 1 < fmt.t)
    (hx : fmt.finiteNormalRange x) :
    fmt.finiteRoundToEven (-x) = -fmt.finiteRoundToEven x := by
  have hxneg : fmt.finiteNormalRange (-x) :=
    (fmt.finiteNormalRange_neg_iff x).2 hx
  have hpolicy :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hx
  have hpolicy_neg :=
    fmt.sourceRoundToEvenEvidence_neg hbeta ht hpolicy
  exact
    sourceRoundToEvenEvidence_unique
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
        hxneg)
      hpolicy_neg

theorem finiteRoundToEven_neg
    (fmt : FloatingPointFormat)
    (hbeta : evenMantissa fmt.beta) (ht : 1 < fmt.t)
    (x : ℝ) :
    fmt.finiteRoundToEven (-x) = -fmt.finiteRoundToEven x := by
  by_cases hx : fmt.finiteNormalRange x
  · exact fmt.finiteRoundToEven_neg_of_finiteNormalRange hbeta ht hx
  · exact fmt.finiteRoundToEven_neg_of_not_finiteNormalRange hx

theorem finiteRoundToEven_signedRelErrorWitness_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite x (fmt.finiteRoundToEven x) ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness (fmt.finiteRoundToEven x) x δ := by
  have hround := fmt.finiteRoundToEven_nearestRoundingToFinite x
  rcases
    fmt.nearestRoundingToFinite_signedRelErrorWitness_lt_of_finiteNormalRange
      hround hx with
    ⟨δ, hδ, hwit⟩
  exact ⟨δ, hround, hδ, hwit⟩

theorem finiteRoundToEven_inverseRelErrorModel_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    inverseRelErrorModel (fmt.finiteRoundToEven x) x fmt.unitRoundoff := by
  have hpolicy :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hx
  rcases
    fmt.sourceRoundToEvenEvidence_relErrorComputedDenom_le_unitRoundoff
      hx hpolicy with
    ⟨hy_ne, hrel⟩
  have hx_ne := fmt.finiteNormalRange_ne_zero hx
  exact
    inverseRelErrorModel_of_relErrorComputedDenom_le
      (fmt.finiteRoundToEven x) x fmt.unitRoundoff hy_ne hx_ne hrel

theorem finiteRoundToEven_inverseRelErrorWitness_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite x (fmt.finiteRoundToEven x) ∧
        |δ| ≤ fmt.unitRoundoff ∧
          inverseRelErrorWitness (fmt.finiteRoundToEven x) x δ := by
  rcases
    fmt.finiteRoundToEven_inverseRelErrorModel_of_finiteNormalRange hx with
    ⟨δ, hδ, hwit⟩
  exact ⟨δ, fmt.finiteRoundToEven_nearestRoundingToFinite x, hδ, hwit⟩

/-- Exact finite representable inputs are fixed by the total finite
round-to-even selector. -/
theorem finiteRoundToEven_eq_self_of_finiteSystem
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteSystem x) :
    fmt.finiteRoundToEven x = x :=
  fmt.nearestRoundingToFinite_eq_self_of_finiteSystem hx
    (fmt.finiteRoundToEven_nearestRoundingToFinite x)

/-- Normal-range branch of Higham's additive underflow model (2.8) for the
total finite round-to-even selector: away from underflow, the additive term is
zero and the usual strict relative-error witness supplies `δ`. -/
theorem finiteRoundToEven_strictAdditiveUnderflowModel_normal_branch_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ η : ℝ,
      strictAdditiveUnderflowModelWitness (fmt.finiteRoundToEven x) x
        fmt.unitRoundoff fmt.gradualUnderflowEtaBound δ η := by
  rcases
    fmt.finiteRoundToEven_signedRelErrorWitness_lt_of_finiteNormalRange hx with
    ⟨δ, _hround, hδ, hwit⟩
  exact
    ⟨δ, 0,
      strictAdditiveUnderflowModelWitness_normal_branch
        hδ fmt.gradualUnderflowEtaBound_pos hwit⟩

/-- Operation-level finite round-to-even wrapper for Higham's primitive
arithmetic operations.  It rounds the exact real operation with the total
source-facing finite selector.  This is the ordinary finite, non-exceptional
bridge; IEEE special values, exception flags, directed modes, and signed zeros
remain outside this real-valued wrapper. -/
noncomputable def finiteRoundToEvenOp (fmt : FloatingPointFormat)
    (op : BasicOp) (x y : ℝ) : ℝ :=
  fmt.finiteRoundToEven (BasicOp.exact op x y)

theorem finiteRoundToModeOp_nearestEven
    (fmt : FloatingPointFormat) (op : BasicOp) (x y : ℝ) :
    fmt.finiteRoundToModeOp IeeeRoundingMode.nearestEven op x y =
      fmt.finiteRoundToEvenOp op x y := rfl

theorem finiteRoundToMode_ieeeUnderflowModeRoundingEvidence_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    fmt.ieeeUnderflowModeRoundingEvidence mode x
      (fmt.finiteRoundToMode mode x) := by
  cases mode
  · simpa [finiteRoundToMode] using fmt.finiteRoundToEven_nearestRoundingToFinite x
  · constructor
    · rw [finiteRoundToMode_towardZero,
        fmt.finiteRoundTowardZero_eq_underflow hunder]
      exact fmt.finiteUnderflowRoundTowardZero_finiteSystem hunder
    · rw [finiteRoundToMode_towardZero]
      exact fmt.finiteRoundTowardZero_abs_le_abs_of_finiteUnderflowRange
        hunder
  · constructor
    · rw [finiteRoundToMode_towardPositive,
        fmt.finiteRoundTowardPositive_eq_underflow hunder]
      exact fmt.finiteUnderflowRoundTowardPositive_finiteSystem hunder
    · rw [finiteRoundToMode_towardPositive]
      exact fmt.le_finiteRoundTowardPositive_of_finiteUnderflowRange
        hunder
  · constructor
    · rw [finiteRoundToMode_towardNegative,
        fmt.finiteRoundTowardNegative_eq_underflow hunder]
      exact fmt.finiteUnderflowRoundTowardNegative_finiteSystem hunder
    · rw [finiteRoundToMode_towardNegative]
      exact fmt.finiteRoundTowardNegative_le_of_finiteUnderflowRange
        hunder

theorem finiteRoundToModeOp_ieeeUnderflowModeRoundingEvidence_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteUnderflowRange (BasicOp.exact op x y)) :
    fmt.ieeeUnderflowModeRoundingEvidence mode (BasicOp.exact op x y)
      (fmt.finiteRoundToModeOp mode op x y) := by
  simpa [finiteRoundToModeOp] using
    fmt.finiteRoundToMode_ieeeUnderflowModeRoundingEvidence_of_finiteUnderflowRange
      (mode := mode) hxy

/-- IEEE-facing finite/no-flags wrapper for the source-facing finite primitive
operation selector. -/
noncomputable def finiteRoundToEvenOpIeeeFiniteResult
    (fmt : FloatingPointFormat) (op : BasicOp) (x y : ℝ) :
    IeeeOperationResult :=
  IeeeOperationResult.finiteNoFlags (fmt.finiteRoundToEvenOp op x y)

theorem finiteRoundToEvenOpIeeeFiniteResult_isFinite
    (fmt : FloatingPointFormat) (op : BasicOp) (x y : ℝ) :
    (fmt.finiteRoundToEvenOpIeeeFiniteResult op x y).isFinite :=
  IeeeOperationResult.finiteNoFlags_isFinite _

theorem finiteRoundToEvenOpIeeeFiniteResult_noFlags
    (fmt : FloatingPointFormat) (op : BasicOp) (x y : ℝ) :
    (fmt.finiteRoundToEvenOpIeeeFiniteResult op x y).noFlags :=
  IeeeOperationResult.finiteNoFlags_noFlags _

theorem finiteRoundToEvenOpIeeeFiniteResult_toReal?
    (fmt : FloatingPointFormat) (op : BasicOp) (x y : ℝ) :
    (fmt.finiteRoundToEvenOpIeeeFiniteResult op x y).value.toReal? =
      some (fmt.finiteRoundToEvenOp op x y) :=
  IeeeOperationResult.finiteNoFlags_toReal? _

/-- IEEE-facing nearest/even primitive-operation wrapper with the first
overflow branch.  If the exact real result is in the source-facing overflow
range, it returns the flagged IEEE overflow default result.  If the exact real
result is in the underflow range, it returns the finite rounded value with the
underflow flag.  Otherwise it uses the finite/no-flags source-facing
round-to-even operation wrapper.  Special-value inputs remain separate future
semantics. -/
noncomputable def ieeeRoundToNearestEvenOpResult
    (fmt : FloatingPointFormat) (op : BasicOp) (x y : ℝ) :
    IeeeOperationResult := by
  classical
  let exact := BasicOp.exact op x y
  let rounded := fmt.finiteRoundToEvenOp op x y
  exact
    if fmt.finiteOverflowRange exact then
      fmt.ieeeOverflowDefaultResult IeeeRoundingMode.nearestEven exact
    else if fmt.finiteUnderflowRange exact then
      fmt.ieeeUnderflowDefaultResult exact rounded
    else
      IeeeOperationResult.finiteNoFlags rounded

theorem ieeeRoundToNearestEvenOpResult_ieeeOverflowResult_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteOverflowRange (BasicOp.exact op x y)) :
    fmt.ieeeOverflowResult IeeeRoundingMode.nearestEven (BasicOp.exact op x y)
      (fmt.ieeeRoundToNearestEvenOpResult op x y) := by
  classical
  simpa [ieeeRoundToNearestEvenOpResult, hxy] using
    (fmt.ieeeOverflowDefaultResult_ieeeOverflowResult_of_finiteOverflowRange
      (mode := IeeeRoundingMode.nearestEven) hxy)

theorem ieeeRoundToNearestEvenOpResult_noFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hover : ¬ fmt.finiteOverflowRange (BasicOp.exact op x y))
    (hunder : ¬ fmt.finiteUnderflowRange (BasicOp.exact op x y)) :
    (fmt.ieeeRoundToNearestEvenOpResult op x y).noFlags := by
  classical
  simpa [ieeeRoundToNearestEvenOpResult, hover, hunder] using
    (IeeeOperationResult.finiteNoFlags_noFlags
      (fmt.finiteRoundToEvenOp op x y))

theorem ieeeRoundToNearestEvenOpResult_toReal?_of_not_finiteOverflowRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : ¬ fmt.finiteOverflowRange (BasicOp.exact op x y)) :
    (fmt.ieeeRoundToNearestEvenOpResult op x y).value.toReal? =
      some (fmt.finiteRoundToEvenOp op x y) := by
  classical
  by_cases hunder : fmt.finiteUnderflowRange (BasicOp.exact op x y)
  · simpa [ieeeRoundToNearestEvenOpResult, hxy, hunder] using
      (fmt.ieeeUnderflowDefaultResult_toReal? (BasicOp.exact op x y)
        (fmt.finiteRoundToEvenOp op x y))
  · simpa [ieeeRoundToNearestEvenOpResult, hxy, hunder] using
      (IeeeOperationResult.finiteNoFlags_toReal?
        (fmt.finiteRoundToEvenOp op x y))

/-- Finite-normal exact primitive results take the nearest/even finite/no-flags
IEEE wrapper branch. -/
theorem ieeeRoundToNearestEvenOpResult_eq_finiteNoFlags_of_finiteNormalRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y)) :
    fmt.ieeeRoundToNearestEvenOpResult op x y =
      IeeeOperationResult.finiteNoFlags (fmt.finiteRoundToEvenOp op x y) := by
  classical
  simp [ieeeRoundToNearestEvenOpResult,
    fmt.finiteNormalRange_not_finiteOverflowRange hxy,
    fmt.finiteNormalRange_not_finiteUnderflowRange hxy]

/-- Finite-normal exact primitive results do not raise IEEE flags in the
nearest/even source-facing wrapper. -/
theorem ieeeRoundToNearestEvenOpResult_noFlags_of_finiteNormalRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y)) :
    (fmt.ieeeRoundToNearestEvenOpResult op x y).noFlags := by
  rw [fmt.ieeeRoundToNearestEvenOpResult_eq_finiteNoFlags_of_finiteNormalRange hxy]
  exact IeeeOperationResult.finiteNoFlags_noFlags _

/-- Finite-normal exact primitive results expose the finite round-to-even
operation value in the nearest/even IEEE wrapper. -/
theorem ieeeRoundToNearestEvenOpResult_toReal?_of_finiteNormalRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y)) :
    (fmt.ieeeRoundToNearestEvenOpResult op x y).value.toReal? =
      some (fmt.finiteRoundToEvenOp op x y) := by
  rw [fmt.ieeeRoundToNearestEvenOpResult_eq_finiteNoFlags_of_finiteNormalRange hxy]
  exact IeeeOperationResult.finiteNoFlags_toReal? _

theorem ieeeRoundToNearestEvenOpResult_ieeeUnderflowResult_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteUnderflowRange (BasicOp.exact op x y)) :
    fmt.ieeeUnderflowResult (BasicOp.exact op x y)
      (fmt.finiteRoundToEvenOp op x y)
      (fmt.ieeeRoundToNearestEvenOpResult op x y) := by
  classical
  have hover : ¬ fmt.finiteOverflowRange (BasicOp.exact op x y) := by
    intro hover
    have hle := fmt.minNormalMagnitude_le_maxFiniteMagnitude
    rw [finiteUnderflowRange] at hxy
    rw [finiteOverflowRange] at hover
    linarith
  simpa [ieeeRoundToNearestEvenOpResult, hover, hxy] using
    (fmt.ieeeUnderflowDefaultResult_ieeeUnderflowResult
      hxy
      (by
        simpa [finiteRoundToEvenOp] using
          fmt.finiteRoundToEven_nearestRoundingToFinite
            (BasicOp.exact op x y)))

theorem ieeeRoundToNearestEvenOpResult_ieeeUnderflowResult_and_additiveUnderflowModel
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteUnderflowRange (BasicOp.exact op x y)) :
    fmt.ieeeUnderflowResult (BasicOp.exact op x y)
        (fmt.finiteRoundToEvenOp op x y)
        (fmt.ieeeRoundToNearestEvenOpResult op x y) ∧
      ∃ η : ℝ,
        additiveUnderflowModelWitness (fmt.finiteRoundToEvenOp op x y)
          (BasicOp.exact op x y) fmt.unitRoundoff
          fmt.gradualUnderflowEtaBound 0 η := by
  have hmodel :
      ∃ η : ℝ,
        additiveUnderflowModelWitness
          (fmt.finiteRoundToEven (BasicOp.exact op x y))
          (BasicOp.exact op x y) fmt.unitRoundoff
          fmt.gradualUnderflowEtaBound 0 η :=
    fmt.finiteRoundToEven_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange
      hxy
  exact
    ⟨fmt.ieeeRoundToNearestEvenOpResult_ieeeUnderflowResult_of_finiteUnderflowRange
        hxy,
      by simpa [finiteRoundToEvenOp] using hmodel⟩

/-- IEEE-facing primitive-operation wrapper parameterized by an IEEE rounding
mode.  Overflow dispatch uses the mode-dependent `ieeeOverflowValue` table, and
the finite underflow/no-flag branches use the source-facing finite selector for
the same mode.  Special-value inputs, traps, and NaN payload/signaling behavior
remain separate future semantics. -/
noncomputable def ieeeRoundToModeOpResult
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (op : BasicOp) (x y : ℝ) : IeeeOperationResult := by
  classical
  let exact := BasicOp.exact op x y
  let rounded := fmt.finiteRoundToModeOp mode op x y
  exact
    if fmt.finiteOverflowRange exact then
      fmt.ieeeOverflowDefaultResult mode exact
    else if fmt.finiteUnderflowRange exact then
      fmt.ieeeUnderflowDefaultResult exact rounded
    else
      IeeeOperationResult.finiteNoFlags rounded

/-- Directed-mode alias for round toward zero. -/
noncomputable def ieeeRoundTowardZeroOpResult
    (fmt : FloatingPointFormat) (op : BasicOp) (x y : ℝ) :
    IeeeOperationResult :=
  fmt.ieeeRoundToModeOpResult IeeeRoundingMode.towardZero op x y

/-- Directed-mode alias for round toward positive infinity. -/
noncomputable def ieeeRoundTowardPositiveOpResult
    (fmt : FloatingPointFormat) (op : BasicOp) (x y : ℝ) :
    IeeeOperationResult :=
  fmt.ieeeRoundToModeOpResult IeeeRoundingMode.towardPositive op x y

/-- Directed-mode alias for round toward negative infinity. -/
noncomputable def ieeeRoundTowardNegativeOpResult
    (fmt : FloatingPointFormat) (op : BasicOp) (x y : ℝ) :
    IeeeOperationResult :=
  fmt.ieeeRoundToModeOpResult IeeeRoundingMode.towardNegative op x y

theorem ieeeRoundToModeOpResult_nearestEven
    (fmt : FloatingPointFormat) (op : BasicOp) (x y : ℝ) :
    fmt.ieeeRoundToModeOpResult IeeeRoundingMode.nearestEven op x y =
      fmt.ieeeRoundToNearestEvenOpResult op x y := by
  classical
  rfl

theorem ieeeRoundToModeOpResult_ieeeOverflowResult_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteOverflowRange (BasicOp.exact op x y)) :
    fmt.ieeeOverflowResult mode (BasicOp.exact op x y)
      (fmt.ieeeRoundToModeOpResult mode op x y) := by
  classical
  simpa [ieeeRoundToModeOpResult, hxy] using
    (fmt.ieeeOverflowDefaultResult_ieeeOverflowResult_of_finiteOverflowRange
      (mode := mode) hxy)

theorem ieeeRoundToModeOpResult_eq_finiteNoFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hover : ¬ fmt.finiteOverflowRange (BasicOp.exact op x y))
    (hunder : ¬ fmt.finiteUnderflowRange (BasicOp.exact op x y)) :
    fmt.ieeeRoundToModeOpResult mode op x y =
      IeeeOperationResult.finiteNoFlags
        (fmt.finiteRoundToModeOp mode op x y) := by
  classical
  simp [ieeeRoundToModeOpResult, hover, hunder]

theorem ieeeRoundToModeOpResult_noFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hover : ¬ fmt.finiteOverflowRange (BasicOp.exact op x y))
    (hunder : ¬ fmt.finiteUnderflowRange (BasicOp.exact op x y)) :
    (fmt.ieeeRoundToModeOpResult mode op x y).noFlags := by
  rw [
    fmt.ieeeRoundToModeOpResult_eq_finiteNoFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
      hover hunder]
  exact IeeeOperationResult.finiteNoFlags_noFlags _

theorem ieeeRoundToModeOpResult_toReal?_of_not_finiteOverflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hxy : ¬ fmt.finiteOverflowRange (BasicOp.exact op x y)) :
    (fmt.ieeeRoundToModeOpResult mode op x y).value.toReal? =
      some (fmt.finiteRoundToModeOp mode op x y) := by
  classical
  by_cases hunder : fmt.finiteUnderflowRange (BasicOp.exact op x y)
  · simpa [ieeeRoundToModeOpResult, hxy, hunder] using
      (fmt.ieeeUnderflowDefaultResult_toReal? (BasicOp.exact op x y)
        (fmt.finiteRoundToModeOp mode op x y))
  · simpa [ieeeRoundToModeOpResult, hxy, hunder] using
      (IeeeOperationResult.finiteNoFlags_toReal?
        (fmt.finiteRoundToModeOp mode op x y))

/-- Finite-normal exact primitive results take the finite/no-flags branch for
any source-facing IEEE rounding mode wrapper. -/
theorem ieeeRoundToModeOpResult_eq_finiteNoFlags_of_finiteNormalRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y)) :
    fmt.ieeeRoundToModeOpResult mode op x y =
      IeeeOperationResult.finiteNoFlags
        (fmt.finiteRoundToModeOp mode op x y) := by
  exact
    fmt.ieeeRoundToModeOpResult_eq_finiteNoFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
      (fmt.finiteNormalRange_not_finiteOverflowRange hxy)
      (fmt.finiteNormalRange_not_finiteUnderflowRange hxy)

/-- Finite-normal exact primitive results do not raise IEEE flags for any
source-facing rounding mode wrapper. -/
theorem ieeeRoundToModeOpResult_noFlags_of_finiteNormalRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y)) :
    (fmt.ieeeRoundToModeOpResult mode op x y).noFlags := by
  rw [fmt.ieeeRoundToModeOpResult_eq_finiteNoFlags_of_finiteNormalRange hxy]
  exact IeeeOperationResult.finiteNoFlags_noFlags _

/-- Finite-normal exact primitive results expose the selected finite rounded
value for any source-facing IEEE rounding mode wrapper. -/
theorem ieeeRoundToModeOpResult_toReal?_of_finiteNormalRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y)) :
    (fmt.ieeeRoundToModeOpResult mode op x y).value.toReal? =
      some (fmt.finiteRoundToModeOp mode op x y) := by
  rw [fmt.ieeeRoundToModeOpResult_eq_finiteNoFlags_of_finiteNormalRange hxy]
  exact IeeeOperationResult.finiteNoFlags_toReal? _

theorem ieeeRoundToModeOpResult_ieeeUnderflowModeResult_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode}
    {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteUnderflowRange (BasicOp.exact op x y)) :
    fmt.ieeeUnderflowModeResult mode (BasicOp.exact op x y)
      (fmt.finiteRoundToModeOp mode op x y)
      (fmt.ieeeRoundToModeOpResult mode op x y) := by
  classical
  have hover : ¬ fmt.finiteOverflowRange (BasicOp.exact op x y) := by
    intro hover
    have hle := fmt.minNormalMagnitude_le_maxFiniteMagnitude
    rw [finiteUnderflowRange] at hxy
    rw [finiteOverflowRange] at hover
    linarith
  simpa [ieeeRoundToModeOpResult, hover, hxy] using
    (fmt.ieeeUnderflowDefaultResult_ieeeUnderflowModeResult
      hxy
      (fmt.finiteRoundToModeOp_ieeeUnderflowModeRoundingEvidence_of_finiteUnderflowRange
        (mode := mode) hxy))

theorem ieeeRoundTowardZeroOpResult_ieeeOverflowResult_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteOverflowRange (BasicOp.exact op x y)) :
    fmt.ieeeOverflowResult IeeeRoundingMode.towardZero
      (BasicOp.exact op x y)
      (fmt.ieeeRoundTowardZeroOpResult op x y) := by
  simpa [ieeeRoundTowardZeroOpResult] using
    (fmt.ieeeRoundToModeOpResult_ieeeOverflowResult_of_finiteOverflowRange
      (mode := IeeeRoundingMode.towardZero) hxy)

theorem ieeeRoundTowardPositiveOpResult_ieeeOverflowResult_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteOverflowRange (BasicOp.exact op x y)) :
    fmt.ieeeOverflowResult IeeeRoundingMode.towardPositive
      (BasicOp.exact op x y)
      (fmt.ieeeRoundTowardPositiveOpResult op x y) := by
  simpa [ieeeRoundTowardPositiveOpResult] using
    (fmt.ieeeRoundToModeOpResult_ieeeOverflowResult_of_finiteOverflowRange
      (mode := IeeeRoundingMode.towardPositive) hxy)

theorem ieeeRoundTowardNegativeOpResult_ieeeOverflowResult_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteOverflowRange (BasicOp.exact op x y)) :
    fmt.ieeeOverflowResult IeeeRoundingMode.towardNegative
      (BasicOp.exact op x y)
      (fmt.ieeeRoundTowardNegativeOpResult op x y) := by
  simpa [ieeeRoundTowardNegativeOpResult] using
    (fmt.ieeeRoundToModeOpResult_ieeeOverflowResult_of_finiteOverflowRange
      (mode := IeeeRoundingMode.towardNegative) hxy)

theorem finiteRoundToEvenOp_nearestRoundingToFinite
    (fmt : FloatingPointFormat) (op : BasicOp) (x y : ℝ) :
    fmt.nearestRoundingToFinite (BasicOp.exact op x y)
      (fmt.finiteRoundToEvenOp op x y) := by
  simpa [finiteRoundToEvenOp] using
    fmt.finiteRoundToEven_nearestRoundingToFinite (BasicOp.exact op x y)

/-- The finite round-to-even primitive-operation wrapper returns a finite
representable value. -/
theorem finiteRoundToEvenOp_finiteSystem
    (fmt : FloatingPointFormat) (op : BasicOp) (x y : ℝ) :
    fmt.finiteSystem (fmt.finiteRoundToEvenOp op x y) := by
  simpa [finiteRoundToEvenOp] using
    fmt.finiteRoundToEven_finiteSystem (BasicOp.exact op x y)

/-- If the exact primitive operation result is finite representable, the
finite round-to-even operation wrapper returns it exactly. -/
theorem finiteRoundToEvenOp_eq_exact_of_finiteSystem
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteSystem (BasicOp.exact op x y)) :
    fmt.finiteRoundToEvenOp op x y = BasicOp.exact op x y := by
  simpa [finiteRoundToEvenOp] using
    fmt.finiteRoundToEven_eq_self_of_finiteSystem hxy

/-- Exact-add branch for aligned same-sign normalized operands whose source
coefficient already fits in `t` digits. -/
theorem finiteRoundToEvenOp_add_sameSign_sameExponent_eq_exact_of_add_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hadd : m + n < fmt.beta ^ fmt.t) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue negative m e)
        (fmt.normalizedValue negative n e) =
      fmt.normalizedValue negative m e +
        fmt.normalizedValue negative n e := by
  exact
    fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.normalizedValue negative m e)
      (y := fmt.normalizedValue negative n e)
      (fmt.normalizedValue_add_sameSign_sameExponent_finiteSystem_of_add_lt_mantissaBound
        (negative := negative) (m := m) (n := n) (e := e) he hadd)

/-- Exact-add branch for same-sign normalized operands with ordered exponents
whose aligned lower-lattice coefficient already fits in `t` digits. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_eq_exact_of_alignedCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        fmt.beta ^ fmt.t) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue negative mHigh eHigh)
        (fmt.normalizedValue negative mLow eLow) =
      fmt.normalizedValue negative mHigh eHigh +
        fmt.normalizedValue negative mLow eLow := by
  have hfin :
      fmt.finiteSystem
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) :=
    fmt.normalizedValue_add_sameSign_orderedExponent_finiteSystem_of_alignedCoeff_lt_mantissaBound
      (negative := negative) hmHigh hmLow heHigh heLow hle hcoeff
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.normalizedValue negative mHigh eHigh)
      (y := fmt.normalizedValue negative mLow eLow) hfin)

/-- The ordered-exponent exact normalized-add branch has zero local roundoff
error. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_alignedCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mHigh eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
  rw [
    finiteRoundToEvenOp_add_sameSign_orderedExponent_eq_exact_of_alignedCoeff_lt_mantissaBound
      hmHigh hmLow heHigh heLow hle hcoeff]
  simpa using fmt.finiteSystem_zero

/-- Commuted exact-add branch for same-sign normalized operands with ordered
exponents whose aligned lower-lattice coefficient already fits in `t` digits. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_eq_exact_of_alignedCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        fmt.beta ^ fmt.t) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue negative mLow eLow)
        (fmt.normalizedValue negative mHigh eHigh) =
      fmt.normalizedValue negative mLow eLow +
        fmt.normalizedValue negative mHigh eHigh := by
  have hfin :
      fmt.finiteSystem
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) :=
    fmt.normalizedValue_add_sameSign_orderedExponent_finiteSystem_of_alignedCoeff_lt_mantissaBound
      (negative := negative) hmHigh hmLow heHigh heLow hle hcoeff
  have hfin_comm :
      fmt.finiteSystem
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh) := by
    convert hfin using 1
    ring
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.normalizedValue negative mLow eLow)
      (y := fmt.normalizedValue negative mHigh eHigh) hfin_comm)

/-- The commuted ordered-exponent exact normalized-add branch has zero local
roundoff error. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_alignedCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh)) := by
  rw [
    finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_eq_exact_of_alignedCoeff_lt_mantissaBound
      hmHigh hmLow heHigh heLow hle hcoeff]
  simpa using fmt.finiteSystem_zero

theorem finiteRoundToEvenOp_eq_finiteNormalRoundToEven_of_finiteNormalRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y)) :
    fmt.finiteRoundToEvenOp op x y =
      fmt.finiteNormalRoundToEven (BasicOp.exact op x y) hxy := by
  simpa [finiteRoundToEvenOp] using
    fmt.finiteRoundToEven_eq_finiteNormalRoundToEven_of_finiteNormalRange hxy

/-- Operation-level handoff for the finite-normal add branch.

If a source-level round-to-even witness for the exact sum has a finite local
error, uniqueness of the finite-normal round-to-even selector transfers that
finite-error certificate to the concrete `finiteRoundToEvenOp add` wrapper. -/
theorem finiteRoundToEvenOp_add_error_finite_of_sourceRoundToEvenEvidence
    {fmt : FloatingPointFormat} {a b y : ℝ}
    (hxy : fmt.finiteNormalRange (a + b))
    (hpolicy : fmt.sourceRoundToEvenEvidence (a + b) y)
    (herr : fmt.finiteSystem ((a + b) - y)) :
    fmt.finiteSystem
      ((a + b) - fmt.finiteRoundToEvenOp BasicOp.add a b) := by
  have hop :
      fmt.finiteRoundToEvenOp BasicOp.add a b =
        fmt.finiteNormalRoundToEven (a + b) hxy := by
    simpa [BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_finiteNormalRoundToEven_of_finiteNormalRange
        (op := BasicOp.add) (x := a) (y := b) hxy)
  have hround :
      fmt.finiteNormalRoundToEven (a + b) hxy = y :=
    fmt.finiteNormalRoundToEven_eq_of_sourceRoundToEvenEvidence hxy hpolicy
  rw [hop, hround]
  exact herr

/-- Operation-level aligned same-sign normalized addition has finite
representable local roundoff error in the finite-normal binary branch. -/
theorem finiteRoundToEvenOp_add_sameSign_sameExponent_error_finiteSystem
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {m n : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.normalizedMantissa n)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative m e +
          fmt.normalizedValue negative n e)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative m e +
          fmt.normalizedValue negative n e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative m e)
          (fmt.normalizedValue negative n e)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative m e +
          fmt.normalizedValue negative n e)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative m e)
          (fmt.normalizedValue negative n e)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_sameExponent_error_finiteSystem
      hbeta he hm hn hpolicy

/-- Operation-level same-sign normalized ordered-exponent addition has finite
representable local roundoff error in the binary one-guard-word branch. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_guardCoeffBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hlo :
      fmt.beta ^ fmt.t ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        2 * fmt.beta ^ fmt.t)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mHigh eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mHigh eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_guardCoeffBounds
      hbeta hmHigh hmLow heHigh heLow hle hlo hhi hpolicy

/-- Commuted operation-level same-sign normalized ordered-exponent addition has
finite representable local roundoff error in the binary one-guard-word branch. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_guardCoeffBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hlo :
      fmt.beta ^ fmt.t ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        2 * fmt.beta ^ fmt.t)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh)) := by
  have hpolicy_comm :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh)) := by
    convert hpolicy_comm using 1
    ring
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue negative mHigh eHigh +
            fmt.normalizedValue negative mLow eLow) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.normalizedValue negative mLow eLow)
            (fmt.normalizedValue negative mHigh eHigh)) :=
    fmt.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_guardCoeffBounds
      hbeta hmHigh hmLow heHigh heLow hle hlo hhi hpolicy
  convert hfin using 1
  ring

/-- Operation-level same-sign normalized ordered-exponent addition has finite
representable local roundoff error throughout the exact-or-one-guard range
`alignedCoeff < 2*beta^t`. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_alignedCoeff_lt_two_mul_mantissaBound
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        2 * fmt.beta ^ fmt.t)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mHigh eHigh)
          (fmt.normalizedValue negative mLow eLow)) := by
  by_cases hsmall :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        fmt.beta ^ fmt.t
  · exact
      fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_alignedCoeff_lt_mantissaBound
        hmHigh hmLow heHigh heLow hle hsmall
  · have hlo :
        fmt.beta ^ fmt.t ≤
          mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow :=
      le_of_not_gt hsmall
    exact
      fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_error_finiteSystem_of_guardCoeffBounds
        hbeta hmHigh hmLow heHigh heLow hle hlo hhi hxy

/-- Commuted operation-level same-sign normalized ordered-exponent addition has
finite representable local roundoff error throughout the exact-or-one-guard
range `alignedCoeff < 2*beta^t`. -/
theorem finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_alignedCoeff_lt_two_mul_mantissaBound
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        2 * fmt.beta ^ fmt.t)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mLow eLow +
          fmt.normalizedValue negative mHigh eHigh) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative mLow eLow)
          (fmt.normalizedValue negative mHigh eHigh)) := by
  by_cases hsmall :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        fmt.beta ^ fmt.t
  · exact
      fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_alignedCoeff_lt_mantissaBound
        hmHigh hmLow heHigh heLow hle hsmall
  · have hlo :
        fmt.beta ^ fmt.t ≤
          mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow :=
      le_of_not_gt hsmall
    exact
      fmt.finiteRoundToEvenOp_add_sameSign_orderedExponent_comm_error_finiteSystem_of_guardCoeffBounds
        hbeta hmHigh hmLow heHigh heLow hle hlo hhi hxy

/-- Opposite-sign, same-exponent normalized addition is exact for the concrete
finite round-to-even operation wrapper.  This is the same-exponent subtraction
branch of the remaining C4.4/FastTwoSum sign split. -/
theorem finiteRoundToEvenOp_add_oppositeSign_sameExponent_eq_exact
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (he : fmt.exponentInRange e) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue negative m e)
        (fmt.normalizedValue (!negative) n e) =
      fmt.normalizedValue negative m e +
        fmt.normalizedValue (!negative) n e := by
  have hfin_sub :
      fmt.finiteSystem
        (fmt.normalizedValue negative m e -
          fmt.normalizedValue negative n e) :=
    fmt.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_normalizedMantissas
      (negative := negative) (m := m) (n := n) (e := e) hm hn he
  have hfin_add :
      fmt.finiteSystem
        (fmt.normalizedValue negative m e +
          fmt.normalizedValue (!negative) n e) := by
    simpa [fmt.normalizedValue_not_eq_neg negative n e, sub_eq_add_neg]
      using hfin_sub
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.normalizedValue negative m e)
      (y := fmt.normalizedValue (!negative) n e) hfin_add)

/-- Opposite-sign, same-exponent normalized addition has zero local roundoff
error, hence a finite representable error. -/
theorem finiteRoundToEvenOp_add_oppositeSign_sameExponent_error_finiteSystem
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (he : fmt.exponentInRange e) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative m e +
          fmt.normalizedValue (!negative) n e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative m e)
          (fmt.normalizedValue (!negative) n e)) := by
  rw [finiteRoundToEvenOp_add_oppositeSign_sameExponent_eq_exact hm hn he]
  simpa using fmt.finiteSystem_zero

/-- Same-sign subnormal addition is exact for the concrete finite
round-to-even operation wrapper. -/
theorem finiteRoundToEvenOp_add_sameSign_subnormal_eq_exact
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ}
    (hm : fmt.subnormalMantissa m)
    (hn : fmt.subnormalMantissa n) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.subnormalValue negative m)
        (fmt.subnormalValue negative n) =
      fmt.subnormalValue negative m + fmt.subnormalValue negative n := by
  have hfin :
      fmt.finiteSystem
        (fmt.subnormalValue negative m +
          fmt.subnormalValue negative n) :=
    fmt.subnormalValue_add_sameSign_finiteSystem_of_subnormalMantissas
      (negative := negative) hm hn
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.subnormalValue negative m)
      (y := fmt.subnormalValue negative n) hfin)

/-- Same-sign subnormal addition has zero local roundoff error, hence a finite
representable error. -/
theorem finiteRoundToEvenOp_add_sameSign_subnormal_error_finiteSystem
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ}
    (hm : fmt.subnormalMantissa m)
    (hn : fmt.subnormalMantissa n) :
    fmt.finiteSystem
      ((fmt.subnormalValue negative m +
          fmt.subnormalValue negative n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue negative m)
          (fmt.subnormalValue negative n)) := by
  rw [finiteRoundToEvenOp_add_sameSign_subnormal_eq_exact hm hn]
  simpa using fmt.finiteSystem_zero

/-- Opposite-sign subnormal addition is exact for the concrete finite
round-to-even operation wrapper, reducing to same-sign subnormal subtraction on
the common lattice. -/
theorem finiteRoundToEvenOp_add_oppositeSign_subnormal_eq_exact
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ}
    (hm : fmt.subnormalMantissa m)
    (hn : fmt.subnormalMantissa n) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.subnormalValue negative m)
        (fmt.subnormalValue (!negative) n) =
      fmt.subnormalValue negative m + fmt.subnormalValue (!negative) n := by
  have hfin_sub :
      fmt.finiteSystem
        (fmt.subnormalValue negative m -
          fmt.subnormalValue negative n) :=
    fmt.subnormalValue_sub_sameSign_finiteSystem_of_subnormalMantissas
      (negative := negative) (m := m) (n := n) hm hn
  have hfin_add :
      fmt.finiteSystem
        (fmt.subnormalValue negative m +
          fmt.subnormalValue (!negative) n) := by
    simpa [fmt.subnormalValue_not_eq_neg negative n, sub_eq_add_neg]
      using hfin_sub
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.subnormalValue negative m)
      (y := fmt.subnormalValue (!negative) n) hfin_add)

/-- Opposite-sign subnormal addition has zero local roundoff error, hence a
finite representable error. -/
theorem finiteRoundToEvenOp_add_oppositeSign_subnormal_error_finiteSystem
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ}
    (hm : fmt.subnormalMantissa m)
    (hn : fmt.subnormalMantissa n) :
    fmt.finiteSystem
      ((fmt.subnormalValue negative m +
          fmt.subnormalValue (!negative) n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue negative m)
          (fmt.subnormalValue (!negative) n)) := by
  rw [finiteRoundToEvenOp_add_oppositeSign_subnormal_eq_exact hm hn]
  simpa using fmt.finiteSystem_zero

/-- Arbitrary-sign subnormal addition is exact for the concrete finite
round-to-even operation wrapper. -/
theorem finiteRoundToEvenOp_add_subnormal_eq_exact
    {fmt : FloatingPointFormat} {negativeX negativeY : Bool} {m n : ℕ}
    (hm : fmt.subnormalMantissa m)
    (hn : fmt.subnormalMantissa n) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.subnormalValue negativeX m)
        (fmt.subnormalValue negativeY n) =
      fmt.subnormalValue negativeX m + fmt.subnormalValue negativeY n := by
  cases negativeX <;> cases negativeY
  · exact fmt.finiteRoundToEvenOp_add_sameSign_subnormal_eq_exact hm hn
  · exact fmt.finiteRoundToEvenOp_add_oppositeSign_subnormal_eq_exact hm hn
  · exact fmt.finiteRoundToEvenOp_add_oppositeSign_subnormal_eq_exact
      (negative := true) hm hn
  · exact fmt.finiteRoundToEvenOp_add_sameSign_subnormal_eq_exact hm hn

/-- Arbitrary-sign subnormal addition has zero local roundoff error, hence a
finite representable error. -/
theorem finiteRoundToEvenOp_add_subnormal_error_finiteSystem
    {fmt : FloatingPointFormat} {negativeX negativeY : Bool} {m n : ℕ}
    (hm : fmt.subnormalMantissa m)
    (hn : fmt.subnormalMantissa n) :
    fmt.finiteSystem
      ((fmt.subnormalValue negativeX m +
          fmt.subnormalValue negativeY n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue negativeX m)
          (fmt.subnormalValue negativeY n)) := by
  rw [finiteRoundToEvenOp_add_subnormal_eq_exact hm hn]
  simpa using fmt.finiteSystem_zero

/-- Same-sign mixed normal/subnormal addition is exact for the concrete finite
round-to-even operation wrapper when the aligned coefficient already fits in
`t` radix digits. -/
theorem finiteRoundToEvenOp_add_normalized_sameSign_subnormal_eq_exact_of_alignedCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hcoeff :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n < fmt.beta ^ fmt.t) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue negative m e)
        (fmt.subnormalValue negative n) =
      fmt.normalizedValue negative m e + fmt.subnormalValue negative n := by
  have hfin :
      fmt.finiteSystem
        (fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) :=
    fmt.normalizedValue_add_sameSign_subnormal_finiteSystem_of_alignedCoeff_lt_mantissaBound
      (negative := negative) hm hn he hcoeff
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.normalizedValue negative m e)
      (y := fmt.subnormalValue negative n) hfin)

/-- Same-sign mixed normal/subnormal addition has zero local roundoff error in
the aligned exact branch. -/
theorem finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_alignedCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hcoeff :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n < fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative m e)
          (fmt.subnormalValue negative n)) := by
  rw [
    finiteRoundToEvenOp_add_normalized_sameSign_subnormal_eq_exact_of_alignedCoeff_lt_mantissaBound
      hm hn he hcoeff]
  simpa using fmt.finiteSystem_zero

/-- Commuted same-sign mixed subnormal/normal exact-add branch for the concrete
finite round-to-even operation wrapper. -/
theorem finiteRoundToEvenOp_add_subnormal_sameSign_normalized_eq_exact_of_alignedCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hcoeff :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n < fmt.beta ^ fmt.t) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.subnormalValue negative n)
        (fmt.normalizedValue negative m e) =
      fmt.subnormalValue negative n + fmt.normalizedValue negative m e := by
  have hfin :
      fmt.finiteSystem
        (fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) :=
    fmt.normalizedValue_add_sameSign_subnormal_finiteSystem_of_alignedCoeff_lt_mantissaBound
      (negative := negative) hm hn he hcoeff
  have hfin_comm :
      fmt.finiteSystem
        (fmt.subnormalValue negative n +
          fmt.normalizedValue negative m e) := by
    convert hfin using 1
    ring
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add)
      (x := fmt.subnormalValue negative n)
      (y := fmt.normalizedValue negative m e) hfin_comm)

/-- Commuted same-sign mixed subnormal/normal addition has zero local roundoff
error in the aligned exact branch. -/
theorem finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_alignedCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hcoeff :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n < fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      ((fmt.subnormalValue negative n +
          fmt.normalizedValue negative m e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue negative n)
          (fmt.normalizedValue negative m e)) := by
  rw [
    finiteRoundToEvenOp_add_subnormal_sameSign_normalized_eq_exact_of_alignedCoeff_lt_mantissaBound
      hm hn he hcoeff]
  simpa using fmt.finiteSystem_zero

/-- Operation-level same-sign mixed normal/subnormal addition has finite
representable local roundoff error in the binary one-guard-word branch. -/
theorem finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_guardCoeffBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hlo :
      fmt.beta ^ fmt.t ≤
        m * fmt.beta ^ Int.toNat (e - fmt.emin) + n)
    (hhi :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n <
        2 * fmt.beta ^ fmt.t)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative m e)
          (fmt.subnormalValue negative n)) := by
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative m e)
          (fmt.subnormalValue negative n)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  exact
    fmt.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_guardCoeffBounds
      hbeta hm hn he hlo hhi hpolicy

/-- Commuted operation-level same-sign mixed subnormal/normal addition has
finite representable local roundoff error in the binary one-guard-word branch. -/
theorem finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_guardCoeffBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hlo :
      fmt.beta ^ fmt.t ≤
        m * fmt.beta ^ Int.toNat (e - fmt.emin) + n)
    (hhi :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n <
        2 * fmt.beta ^ fmt.t)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue negative n +
          fmt.normalizedValue negative m e)) :
    fmt.finiteSystem
      ((fmt.subnormalValue negative n +
          fmt.normalizedValue negative m e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue negative n)
          (fmt.normalizedValue negative m e)) := by
  have hpolicy_comm :
      fmt.sourceRoundToEvenEvidence
        (fmt.subnormalValue negative n +
          fmt.normalizedValue negative m e)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue negative n)
          (fmt.normalizedValue negative m e)) := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxy)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n)
        (fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue negative n)
          (fmt.normalizedValue negative m e)) := by
    convert hpolicy_comm using 1
    ring
  have hfin :
      fmt.finiteSystem
        ((fmt.normalizedValue negative m e +
            fmt.subnormalValue negative n) -
          fmt.finiteRoundToEvenOp BasicOp.add
            (fmt.subnormalValue negative n)
            (fmt.normalizedValue negative m e)) :=
    fmt.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_guardCoeffBounds
      hbeta hm hn he hlo hhi hpolicy
  convert hfin using 1
  ring

/-- Operation-level same-sign mixed normal/subnormal addition has finite
representable local roundoff error throughout the exact-or-one-guard range
`alignedCoeff < 2*beta^t`. -/
theorem finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_alignedCoeff_lt_two_mul_mantissaBound
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hhi :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n <
        2 * fmt.beta ^ fmt.t)
    (hxy :
      fmt.finiteNormalRange
        (fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n)) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue negative m e)
          (fmt.subnormalValue negative n)) := by
  by_cases hsmall :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n <
        fmt.beta ^ fmt.t
  · exact
      fmt.finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_alignedCoeff_lt_mantissaBound
        hm hn he hsmall
  · have hlo :
        fmt.beta ^ fmt.t ≤
          m * fmt.beta ^ Int.toNat (e - fmt.emin) + n :=
      le_of_not_gt hsmall
    exact
      fmt.finiteRoundToEvenOp_add_normalized_sameSign_subnormal_error_finiteSystem_of_guardCoeffBounds
        hbeta hm hn he hlo hhi hxy

/-- Commuted operation-level same-sign mixed subnormal/normal addition has
finite representable local roundoff error throughout the exact-or-one-guard
range `alignedCoeff < 2*beta^t`. -/
theorem finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_alignedCoeff_lt_two_mul_mantissaBound
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hhi :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n <
        2 * fmt.beta ^ fmt.t)
    (hxy :
      fmt.finiteNormalRange
        (fmt.subnormalValue negative n +
          fmt.normalizedValue negative m e)) :
    fmt.finiteSystem
      ((fmt.subnormalValue negative n +
          fmt.normalizedValue negative m e) -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.subnormalValue negative n)
          (fmt.normalizedValue negative m e)) := by
  by_cases hsmall :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n <
        fmt.beta ^ fmt.t
  · exact
      fmt.finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_alignedCoeff_lt_mantissaBound
        hm hn he hsmall
  · have hlo :
        fmt.beta ^ fmt.t ≤
          m * fmt.beta ^ Int.toNat (e - fmt.emin) + n :=
      le_of_not_gt hsmall
    exact
      fmt.finiteRoundToEvenOp_add_subnormal_sameSign_normalized_error_finiteSystem_of_guardCoeffBounds
        hbeta hm hn he hlo hhi hxy

/-- Adding the negation of a normalized operand is exact under Sterbenz's ratio
condition.  This packages the opposite-sign normalized-add branch as ordinary
Sterbenz subtraction. -/
theorem finiteRoundToEvenOp_add_neg_right_normalizedSystem_eq_exact_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.normalizedSystem x)
    (hy : fmt.normalizedSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteRoundToEvenOp BasicOp.add x (-y) = x + (-y) := by
  have hfin_sub : fmt.finiteSystem (x - y) :=
    fmt.normalizedSystem_sub_finiteSystem_of_sterbenzRatioCondition
      hx hy hsterbenz
  have hfin_add : fmt.finiteSystem (x + (-y)) := by
    simpa [sub_eq_add_neg] using hfin_sub
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add) (x := x) (y := -y) hfin_add)

/-- The local roundoff error is finite for normalized `x + (-y)` under
Sterbenz's ratio condition, since the rounded add is exact. -/
theorem finiteRoundToEvenOp_add_neg_right_normalizedSystem_error_finiteSystem_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.normalizedSystem x)
    (hy : fmt.normalizedSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteSystem
      ((x + (-y)) - fmt.finiteRoundToEvenOp BasicOp.add x (-y)) := by
  rw [
    fmt.finiteRoundToEvenOp_add_neg_right_normalizedSystem_eq_exact_of_sterbenzRatioCondition
      hx hy hsterbenz]
  simpa using fmt.finiteSystem_zero

/-- Positive normalized specialization of the Sterbenz exact `x + (-y)` branch,
written with an explicit negative second operand. -/
theorem finiteRoundToEvenOp_add_neg_right_positive_normalizedValue_eq_exact_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.normalizedMantissa n)
    (he : fmt.exponentInRange e)
    (he' : fmt.exponentInRange e')
    (hsterbenz : fmt.sterbenzRatioCondition
      (fmt.normalizedValue false m e)
      (fmt.normalizedValue false n e')) :
    fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.normalizedValue false m e)
        (fmt.normalizedValue true n e') =
      fmt.normalizedValue false m e + fmt.normalizedValue true n e' := by
  have hx : fmt.normalizedSystem (fmt.normalizedValue false m e) :=
    ⟨false, m, e, hm, he, rfl⟩
  have hy : fmt.normalizedSystem (fmt.normalizedValue false n e') :=
    ⟨false, n, e', hn, he', rfl⟩
  simpa [fmt.normalizedValue_true_eq_neg_false n e'] using
    (fmt.finiteRoundToEvenOp_add_neg_right_normalizedSystem_eq_exact_of_sterbenzRatioCondition
      hx hy hsterbenz)

/-- Positive normalized specialization of the finite-error form of exact
Sterbenz `x + (-y)` addition. -/
theorem finiteRoundToEvenOp_add_neg_right_positive_normalizedValue_error_finiteSystem_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.normalizedMantissa n)
    (he : fmt.exponentInRange e)
    (he' : fmt.exponentInRange e')
    (hsterbenz : fmt.sterbenzRatioCondition
      (fmt.normalizedValue false m e)
      (fmt.normalizedValue false n e')) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e +
          fmt.normalizedValue true n e') -
        fmt.finiteRoundToEvenOp BasicOp.add
          (fmt.normalizedValue false m e)
          (fmt.normalizedValue true n e')) := by
  rw [
    fmt.finiteRoundToEvenOp_add_neg_right_positive_normalizedValue_eq_exact_of_sterbenzRatioCondition
      hm hn he he' hsterbenz]
  simpa using fmt.finiteSystem_zero

/-- Adding the negation of a finite representable operand is exact under
Sterbenz's ratio condition, including normal, subnormal, and mixed branches. -/
theorem finiteRoundToEvenOp_add_neg_right_finiteSystem_eq_exact_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystem x)
    (hy : fmt.finiteSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteRoundToEvenOp BasicOp.add x (-y) = x + (-y) := by
  have hfin_sub : fmt.finiteSystem (x - y) :=
    fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition hx hy hsterbenz
  have hfin_add : fmt.finiteSystem (x + (-y)) := by
    simpa [sub_eq_add_neg] using hfin_sub
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add) (x := x) (y := -y) hfin_add)

/-- The local roundoff error is finite for finite-system `x + (-y)` under
Sterbenz's ratio condition, since the rounded add is exact. -/
theorem finiteRoundToEvenOp_add_neg_right_finiteSystem_error_finiteSystem_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystem x)
    (hy : fmt.finiteSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteSystem
      ((x + (-y)) - fmt.finiteRoundToEvenOp BasicOp.add x (-y)) := by
  rw [
    fmt.finiteRoundToEvenOp_add_neg_right_finiteSystem_eq_exact_of_sterbenzRatioCondition
      hx hy hsterbenz]
  simpa using fmt.finiteSystem_zero

/-- Commuted finite-system form of exact Sterbenz addition with an explicit
negative operand. -/
theorem finiteRoundToEvenOp_add_neg_left_finiteSystem_eq_exact_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystem x)
    (hy : fmt.finiteSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteRoundToEvenOp BasicOp.add (-y) x = (-y) + x := by
  have hfin_sub : fmt.finiteSystem (x - y) :=
    fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition hx hy hsterbenz
  have hfin_add : fmt.finiteSystem ((-y) + x) := by
    convert hfin_sub using 1
    ring
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add) (x := -y) (y := x) hfin_add)

/-- The local roundoff error is finite for the commuted finite-system
Sterbenz add-neg branch. -/
theorem finiteRoundToEvenOp_add_neg_left_finiteSystem_error_finiteSystem_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystem x)
    (hy : fmt.finiteSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteSystem
      (((-y) + x) - fmt.finiteRoundToEvenOp BasicOp.add (-y) x) := by
  rw [
    fmt.finiteRoundToEvenOp_add_neg_left_finiteSystem_eq_exact_of_sterbenzRatioCondition
      hx hy hsterbenz]
  simpa using fmt.finiteSystem_zero

/-- Same-sign, same-exponent subtraction is exact for the concrete finite
round-to-even operation wrapper.  The finite-system side condition is discharged
by the derived same-exponent finite-difference selector. -/
theorem finiteRoundToEvenOp_sub_sameSign_sameExponent_eq_exact
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (he : fmt.exponentInRange e) :
    fmt.finiteRoundToEvenOp BasicOp.sub
        (fmt.normalizedValue negative m e)
        (fmt.normalizedValue negative n e) =
      fmt.normalizedValue negative m e -
        fmt.normalizedValue negative n e := by
  have hfin :
      fmt.finiteSystem
        (fmt.normalizedValue negative m e -
          fmt.normalizedValue negative n e) :=
    fmt.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_normalizedMantissas
      (negative := negative) (m := m) (n := n) (e := e) hm hn he
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub)
      (x := fmt.normalizedValue negative m e)
      (y := fmt.normalizedValue negative n e) hfin)

/-- Positive adjacent-exponent Sterbenz subtraction is exact for the concrete
finite round-to-even operation wrapper. -/
theorem finiteRoundToEvenOp_sub_positive_adjacentExponent_eq_exact_of_sterbenzAdjacent
    {fmt : FloatingPointFormat} {mHigh mLow : ℕ} {e : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (he : fmt.exponentInRange e)
    (hsterbenz : fmt.sterbenzRatioCondition
      (fmt.normalizedValue false mHigh (e + 1))
      (fmt.normalizedValue false mLow e)) :
    fmt.finiteRoundToEvenOp BasicOp.sub
        (fmt.normalizedValue false mHigh (e + 1))
        (fmt.normalizedValue false mLow e) =
      fmt.normalizedValue false mHigh (e + 1) -
        fmt.normalizedValue false mLow e := by
  have hfin :
      fmt.finiteSystem
        (fmt.normalizedValue false mHigh (e + 1) -
          fmt.normalizedValue false mLow e) :=
    fmt.normalizedValue_sub_positive_adjacentExponent_finiteSystem_of_sterbenzAdjacent
      (mHigh := mHigh) (mLow := mLow) (e := e)
      hmHigh hmLow he hsterbenz
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub)
      (x := fmt.normalizedValue false mHigh (e + 1))
      (y := fmt.normalizedValue false mLow e) hfin)

/-- Positive normalized Sterbenz subtraction is exact for the concrete finite
round-to-even operation wrapper. -/
theorem finiteRoundToEvenOp_sub_positive_eq_exact_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.normalizedMantissa n)
    (he : fmt.exponentInRange e)
    (he' : fmt.exponentInRange e')
    (hsterbenz : fmt.sterbenzRatioCondition
      (fmt.normalizedValue false m e)
      (fmt.normalizedValue false n e')) :
    fmt.finiteRoundToEvenOp BasicOp.sub
        (fmt.normalizedValue false m e)
        (fmt.normalizedValue false n e') =
      fmt.normalizedValue false m e -
        fmt.normalizedValue false n e' := by
  have hfin :
      fmt.finiteSystem
        (fmt.normalizedValue false m e -
          fmt.normalizedValue false n e') :=
    fmt.normalizedValue_sub_positive_finiteSystem_of_sterbenzRatioCondition
      (m := m) (n := n) (e := e) (e' := e')
      hm hn he he' hsterbenz
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub)
      (x := fmt.normalizedValue false m e)
      (y := fmt.normalizedValue false n e') hfin)

/-- Source-shaped normalized Sterbenz subtraction is exact for the concrete
finite round-to-even operation wrapper. -/
theorem finiteRoundToEvenOp_sub_normalizedSystem_eq_exact_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.normalizedSystem x)
    (hy : fmt.normalizedSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteRoundToEvenOp BasicOp.sub x y = x - y := by
  have hfin : fmt.finiteSystem (x - y) :=
    fmt.normalizedSystem_sub_finiteSystem_of_sterbenzRatioCondition
      hx hy hsterbenz
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := x) (y := y) hfin)

/-- Same-sign subnormal subtraction is exact for the concrete finite
round-to-even operation wrapper. -/
theorem finiteRoundToEvenOp_sub_sameSign_subnormal_eq_exact
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ}
    (hm : fmt.subnormalMantissa m)
    (hn : fmt.subnormalMantissa n) :
    fmt.finiteRoundToEvenOp BasicOp.sub
        (fmt.subnormalValue negative m)
        (fmt.subnormalValue negative n) =
      fmt.subnormalValue negative m -
        fmt.subnormalValue negative n := by
  have hfin :
      fmt.finiteSystem
        (fmt.subnormalValue negative m -
          fmt.subnormalValue negative n) :=
    fmt.subnormalValue_sub_sameSign_finiteSystem_of_subnormalMantissas
      (negative := negative) (m := m) (n := n) hm hn
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub)
      (x := fmt.subnormalValue negative m)
      (y := fmt.subnormalValue negative n) hfin)

/-- Source-shaped subnormal Sterbenz subtraction is exact for the concrete
finite round-to-even operation wrapper. -/
theorem finiteRoundToEvenOp_sub_subnormalSystem_eq_exact_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.subnormalSystem x)
    (hy : fmt.subnormalSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteRoundToEvenOp BasicOp.sub x y = x - y := by
  have hfin : fmt.finiteSystem (x - y) :=
    fmt.subnormalSystem_sub_finiteSystem_of_sterbenzRatioCondition
      hx hy hsterbenz
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := x) (y := y) hfin)

/-- Mixed normal/subnormal Sterbenz subtraction is exact for the concrete
finite round-to-even operation wrapper. -/
theorem finiteRoundToEvenOp_sub_normalizedSystem_subnormalSystem_eq_exact_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.normalizedSystem x)
    (hy : fmt.subnormalSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteRoundToEvenOp BasicOp.sub x y = x - y := by
  have hfin : fmt.finiteSystem (x - y) :=
    fmt.normalizedSystem_sub_subnormalSystem_finiteSystem_of_sterbenzRatioCondition
      hx hy hsterbenz
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := x) (y := y) hfin)

/-- Mixed subnormal/normal Sterbenz subtraction is exact for the concrete
finite round-to-even operation wrapper. -/
theorem finiteRoundToEvenOp_sub_subnormalSystem_normalizedSystem_eq_exact_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.subnormalSystem x)
    (hy : fmt.normalizedSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteRoundToEvenOp BasicOp.sub x y = x - y := by
  have hfin : fmt.finiteSystem (x - y) :=
    fmt.subnormalSystem_sub_normalizedSystem_finiteSystem_of_sterbenzRatioCondition
      hx hy hsterbenz
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := x) (y := y) hfin)

/-- Full source-facing finite-system Sterbenz subtraction is exact for the
concrete finite round-to-even operation wrapper. -/
theorem finiteRoundToEvenOp_sub_finiteSystem_eq_exact_of_sterbenzRatioCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystem x)
    (hy : fmt.finiteSystem y)
    (hsterbenz : fmt.sterbenzRatioCondition x y) :
    fmt.finiteRoundToEvenOp BasicOp.sub x y = x - y := by
  have hfin : fmt.finiteSystem (x - y) :=
    fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition
      hx hy hsterbenz
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := x) (y := y) hfin)

theorem finiteRoundToEvenOp_sub_eq_exact_of_guardDigitBranchSubtractionData
    {fmt : FloatingPointFormat} {x y : ℝ}
    (d : GuardDigitBranchSubtractionData fmt x y) :
    fmt.finiteRoundToEvenOp BasicOp.sub x y = x - y := by
  have hfin :
      fmt.finiteSystem (BasicOp.exact BasicOp.sub x y) := by
    simpa [BasicOp.exact] using
      (Or.inr (Or.inl
        (fmt.normalizedExponentRepresentation_normalizedSystem d.hz)) :
        fmt.finiteSystem (x - y))
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := x) (y := y) hfin)

theorem finiteRoundToEvenOp_sub_eq_exact_of_fergusonCondition
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hcond : fmt.fergusonExponentCondition x y) :
    fmt.finiteRoundToEvenOp BasicOp.sub x y = x - y := by
  have hfin :
      fmt.finiteSystem (BasicOp.exact BasicOp.sub x y) := by
    simpa [BasicOp.exact] using
      (Or.inr (Or.inl
        (fmt.fergusonExponentCondition_sub_normalized hcond)) :
        fmt.finiteSystem (x - y))
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := x) (y := y) hfin)

/-- Finite round-to-even addition satisfies the left-add-zero law whenever the
input is finite representable.  This is the concrete side condition needed for
the `FPModel.fl_add_zero` law on the ordinary finite wrapper. -/
theorem finiteRoundToEvenOp_add_zero_of_finiteSystem
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteSystem x) :
    fmt.finiteRoundToEvenOp BasicOp.add 0 x = x := by
  simpa [finiteRoundToEvenOp, BasicOp.exact] using
    fmt.finiteRoundToEven_eq_self_of_finiteSystem hx

theorem finiteRoundToEvenOp_signedRelErrorWitness_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y)) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite (BasicOp.exact op x y)
          (fmt.finiteRoundToEvenOp op x y) ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness (fmt.finiteRoundToEvenOp op x y)
            (BasicOp.exact op x y) δ := by
  rcases
    fmt.finiteRoundToEven_signedRelErrorWitness_lt_of_finiteNormalRange
      hxy with
    ⟨δ, hround, hδ, hwit⟩
  exact
    ⟨δ, by simpa [finiteRoundToEvenOp] using hround, hδ,
      by simpa [finiteRoundToEvenOp] using hwit⟩

theorem finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y)) :
    ∃ δ : ℝ,
      |δ| < fmt.unitRoundoff ∧
        fmt.finiteRoundToEvenOp op x y =
          BasicOp.exact op x y * (1 + δ) := by
  rcases
    fmt.finiteRoundToEvenOp_signedRelErrorWitness_lt_of_finiteNormalRange
      hxy with
    ⟨δ, _hround, hδ, hwit⟩
  exact ⟨δ, hδ, by simpa [signedRelErrorWitness] using hwit⟩

theorem finiteRoundToEvenOp_inverseRelErrorWitness_of_finiteNormalRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y)) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite (BasicOp.exact op x y)
          (fmt.finiteRoundToEvenOp op x y) ∧
        |δ| ≤ fmt.unitRoundoff ∧
          inverseRelErrorWitness (fmt.finiteRoundToEvenOp op x y)
            (BasicOp.exact op x y) δ := by
  rcases
    fmt.finiteRoundToEven_inverseRelErrorWitness_of_finiteNormalRange
      hxy with
    ⟨δ, hround, hδ, hwit⟩
  exact
    ⟨δ, by simpa [finiteRoundToEvenOp] using hround, hδ,
      by simpa [finiteRoundToEvenOp] using hwit⟩

/-- Normal-range branch of Higham's additive underflow model (2.8) for the
ordinary finite primitive-operation wrapper: away from underflow, `η = 0`. -/
theorem finiteRoundToEvenOp_strictAdditiveUnderflowModel_normal_branch_of_finiteNormalRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y)) :
    ∃ δ η : ℝ,
      strictAdditiveUnderflowModelWitness (fmt.finiteRoundToEvenOp op x y)
        (BasicOp.exact op x y) fmt.unitRoundoff fmt.gradualUnderflowEtaBound
        δ η := by
  rcases
    fmt.finiteRoundToEvenOp_signedRelErrorWitness_lt_of_finiteNormalRange
      hxy with
    ⟨δ, _hround, hδ, hwit⟩
  exact
    ⟨δ, 0,
      strictAdditiveUnderflowModelWitness_normal_branch
        hδ fmt.gradualUnderflowEtaBound_pos hwit⟩

/-- Underflow branch of Higham's additive model (2.8) for the ordinary finite
primitive-operation wrapper. -/
theorem finiteRoundToEvenOp_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteUnderflowRange (BasicOp.exact op x y)) :
    ∃ η : ℝ,
      additiveUnderflowModelWitness (fmt.finiteRoundToEvenOp op x y)
        (BasicOp.exact op x y) fmt.unitRoundoff fmt.gradualUnderflowEtaBound
        0 η := by
  simpa [finiteRoundToEvenOp] using
    fmt.finiteRoundToEven_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange
      (x := BasicOp.exact op x y) hxy

/-- Strict underflow branch of Higham's additive model (2.8) for the ordinary
finite primitive-operation wrapper, away from exact half-cell ties. -/
theorem finiteRoundToEvenOp_strictAdditiveUnderflowModel_underflow_branch_of_finiteUnderflowRange_of_noHalfTie
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteUnderflowRange (BasicOp.exact op x y))
    (hnotie : fmt.finiteUnderflowNoHalfTie (BasicOp.exact op x y)) :
    ∃ η : ℝ,
      strictAdditiveUnderflowModelWitness (fmt.finiteRoundToEvenOp op x y)
        (BasicOp.exact op x y) fmt.unitRoundoff fmt.gradualUnderflowEtaBound
        0 η := by
  simpa [finiteRoundToEvenOp] using
    fmt.finiteRoundToEven_strictAdditiveUnderflowModel_underflow_branch_of_finiteUnderflowRange_of_noHalfTie
      (x := BasicOp.exact op x y) hxy hnotie

/-- Operation-level finite round-to-even wrapper for the real square root used
in Higham's standard model note after (2.4).  The standard-model theorem below
is stated on nonnegative inputs whose exact square root is finite-normal. -/
noncomputable def finiteRoundToEvenSqrt (fmt : FloatingPointFormat)
    (x : ℝ) : ℝ :=
  fmt.finiteRoundToEven (Real.sqrt x)

/-- Operation-level finite square-root selector parameterized by an IEEE
rounding mode.  It rounds the exact real square root with the total
source-facing finite selector for that mode. -/
noncomputable def finiteRoundToModeSqrt
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) : ℝ :=
  fmt.finiteRoundToMode mode (Real.sqrt x)

theorem finiteRoundToModeSqrt_nearestEven
    (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.finiteRoundToModeSqrt IeeeRoundingMode.nearestEven x =
      fmt.finiteRoundToEvenSqrt x := rfl

theorem finiteRoundToModeSqrt_ieeeUnderflowModeRoundingEvidence_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hsqrt : fmt.finiteUnderflowRange (Real.sqrt x)) :
    fmt.ieeeUnderflowModeRoundingEvidence mode (Real.sqrt x)
      (fmt.finiteRoundToModeSqrt mode x) := by
  simpa [finiteRoundToModeSqrt] using
    fmt.finiteRoundToMode_ieeeUnderflowModeRoundingEvidence_of_finiteUnderflowRange
      (mode := mode) hsqrt

/-- IEEE-facing finite/no-flags wrapper for the source-facing finite square-root
selector. -/
noncomputable def finiteRoundToEvenSqrtIeeeFiniteResult
    (fmt : FloatingPointFormat) (x : ℝ) : IeeeOperationResult :=
  IeeeOperationResult.finiteNoFlags (fmt.finiteRoundToEvenSqrt x)

theorem finiteRoundToEvenSqrtIeeeFiniteResult_isFinite
    (fmt : FloatingPointFormat) (x : ℝ) :
    (fmt.finiteRoundToEvenSqrtIeeeFiniteResult x).isFinite :=
  IeeeOperationResult.finiteNoFlags_isFinite _

theorem finiteRoundToEvenSqrtIeeeFiniteResult_noFlags
    (fmt : FloatingPointFormat) (x : ℝ) :
    (fmt.finiteRoundToEvenSqrtIeeeFiniteResult x).noFlags :=
  IeeeOperationResult.finiteNoFlags_noFlags _

theorem finiteRoundToEvenSqrtIeeeFiniteResult_toReal?
    (fmt : FloatingPointFormat) (x : ℝ) :
    (fmt.finiteRoundToEvenSqrtIeeeFiniteResult x).value.toReal? =
      some (fmt.finiteRoundToEvenSqrt x) :=
  IeeeOperationResult.finiteNoFlags_toReal? _

theorem finiteRoundToEvenSqrt_nearestRoundingToFinite
    (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.nearestRoundingToFinite (Real.sqrt x)
      (fmt.finiteRoundToEvenSqrt x) := by
  simpa [finiteRoundToEvenSqrt] using
    fmt.finiteRoundToEven_nearestRoundingToFinite (Real.sqrt x)

/-- The finite round-to-even square-root wrapper returns a finite
representable value. -/
theorem finiteRoundToEvenSqrt_finiteSystem
    (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.finiteSystem (fmt.finiteRoundToEvenSqrt x) := by
  simpa [finiteRoundToEvenSqrt] using
    fmt.finiteRoundToEven_finiteSystem (Real.sqrt x)

/-- If the exact square-root result is finite representable, the finite
round-to-even square-root wrapper returns it exactly. -/
theorem finiteRoundToEvenSqrt_eq_exact_of_finiteSystem
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsqrt : fmt.finiteSystem (Real.sqrt x)) :
    fmt.finiteRoundToEvenSqrt x = Real.sqrt x := by
  simpa [finiteRoundToEvenSqrt] using
    fmt.finiteRoundToEven_eq_self_of_finiteSystem hsqrt

theorem finiteRoundToEvenSqrt_standardModel_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (_hx_nonneg : 0 ≤ x) (hsqrt : fmt.finiteNormalRange (Real.sqrt x)) :
    ∃ δ : ℝ,
      |δ| < fmt.unitRoundoff ∧
        fmt.finiteRoundToEvenSqrt x = Real.sqrt x * (1 + δ) := by
  rcases
    fmt.finiteRoundToEven_signedRelErrorWitness_lt_of_finiteNormalRange
      hsqrt with
    ⟨δ, _hround, hδ, hwit⟩
  exact ⟨δ, hδ, by simpa [finiteRoundToEvenSqrt, signedRelErrorWitness] using hwit⟩

theorem finiteRoundToEvenSqrt_inverseRelErrorWitness_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsqrt : fmt.finiteNormalRange (Real.sqrt x)) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite (Real.sqrt x)
          (fmt.finiteRoundToEvenSqrt x) ∧
        |δ| ≤ fmt.unitRoundoff ∧
          inverseRelErrorWitness (fmt.finiteRoundToEvenSqrt x)
            (Real.sqrt x) δ := by
  rcases
    fmt.finiteRoundToEven_inverseRelErrorWitness_of_finiteNormalRange
      hsqrt with
    ⟨δ, hround, hδ, hwit⟩
  exact
    ⟨δ, by simpa [finiteRoundToEvenSqrt] using hround, hδ,
      by simpa [finiteRoundToEvenSqrt] using hwit⟩

/-- Normal-range branch of Higham's additive underflow model (2.8) for the
finite square-root wrapper: away from underflow, `η = 0`. -/
theorem finiteRoundToEvenSqrt_strictAdditiveUnderflowModel_normal_branch_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (_hx_nonneg : 0 ≤ x) (hsqrt : fmt.finiteNormalRange (Real.sqrt x)) :
    ∃ δ η : ℝ,
      strictAdditiveUnderflowModelWitness (fmt.finiteRoundToEvenSqrt x)
        (Real.sqrt x) fmt.unitRoundoff fmt.gradualUnderflowEtaBound δ η := by
  rcases
    fmt.finiteRoundToEven_signedRelErrorWitness_lt_of_finiteNormalRange
      hsqrt with
    ⟨δ, _hround, hδ, hwit⟩
  exact
    ⟨δ, 0,
      strictAdditiveUnderflowModelWitness_normal_branch
        hδ fmt.gradualUnderflowEtaBound_pos
        (by simpa [finiteRoundToEvenSqrt] using hwit)⟩

/-- Underflow branch of Higham's additive model (2.8) for the finite
square-root wrapper. -/
theorem finiteRoundToEvenSqrt_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsqrt : fmt.finiteUnderflowRange (Real.sqrt x)) :
    ∃ η : ℝ,
      additiveUnderflowModelWitness (fmt.finiteRoundToEvenSqrt x)
        (Real.sqrt x) fmt.unitRoundoff fmt.gradualUnderflowEtaBound 0 η := by
  simpa [finiteRoundToEvenSqrt] using
    fmt.finiteRoundToEven_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange
      (x := Real.sqrt x) hsqrt

/-- Strict underflow branch of Higham's additive model (2.8) for the finite
square-root wrapper, away from exact half-cell ties. -/
theorem finiteRoundToEvenSqrt_strictAdditiveUnderflowModel_underflow_branch_of_finiteUnderflowRange_of_noHalfTie
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsqrt : fmt.finiteUnderflowRange (Real.sqrt x))
    (hnotie : fmt.finiteUnderflowNoHalfTie (Real.sqrt x)) :
    ∃ η : ℝ,
      strictAdditiveUnderflowModelWitness (fmt.finiteRoundToEvenSqrt x)
        (Real.sqrt x) fmt.unitRoundoff fmt.gradualUnderflowEtaBound 0 η := by
  simpa [finiteRoundToEvenSqrt] using
    fmt.finiteRoundToEven_strictAdditiveUnderflowModel_underflow_branch_of_finiteUnderflowRange_of_noHalfTie
      (x := Real.sqrt x) hsqrt hnotie

/-- IEEE-facing nearest/even square-root wrapper for the real-valued square
root reference on nonnegative inputs, with the IEEE invalid-operation/NaN
branch for negative inputs.  For nonnegative inputs, `Real.sqrt x` is the exact
real quantity being rounded.  Overflow and underflow of that exact result
dispatch to the corresponding flagged IEEE-facing result; ordinary finite
results use the finite/no-flags source-facing square-root wrapper. -/
noncomputable def ieeeRoundToNearestEvenSqrtResult
    (fmt : FloatingPointFormat) (x : ℝ) : IeeeOperationResult := by
  classical
  exact
    if x < 0 then
      ieeeSqrtInvalidDefaultResult x
    else
      let exact := Real.sqrt x
      let rounded := fmt.finiteRoundToEvenSqrt x
      if fmt.finiteOverflowRange exact then
        fmt.ieeeOverflowDefaultResult IeeeRoundingMode.nearestEven exact
      else if fmt.finiteUnderflowRange exact then
        fmt.ieeeUnderflowDefaultResult exact rounded
      else
        IeeeOperationResult.finiteNoFlags rounded

theorem ieeeRoundToNearestEvenSqrtResult_ieeeSqrtInvalidResult_of_neg
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : x < 0) :
    ieeeSqrtInvalidResult x (fmt.ieeeRoundToNearestEvenSqrtResult x) := by
  classical
  simpa [ieeeRoundToNearestEvenSqrtResult, hx] using
    (ieeeSqrtInvalidDefaultResult_ieeeSqrtInvalidResult hx)

theorem ieeeRoundToNearestEvenSqrtResult_ieeeInvalidOperationResult_of_neg
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : x < 0) :
    ieeeInvalidOperationResult
      (fmt.ieeeRoundToNearestEvenSqrtResult x) :=
  (fmt.ieeeRoundToNearestEvenSqrtResult_ieeeSqrtInvalidResult_of_neg hx).2

theorem ieeeRoundToNearestEvenSqrtResult_value_of_neg
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : x < 0) :
    (fmt.ieeeRoundToNearestEvenSqrtResult x).value = IeeeValue.nan :=
  ieeeInvalidOperationResult_value
    (fmt.ieeeRoundToNearestEvenSqrtResult_ieeeInvalidOperationResult_of_neg hx)

theorem ieeeRoundToNearestEvenSqrtResult_hasInvalidOperationFlag_of_neg
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : x < 0) :
    (fmt.ieeeRoundToNearestEvenSqrtResult x).hasFlag
      IeeeExceptionFlag.invalidOperation :=
  ieeeInvalidOperationResult_hasInvalidOperationFlag
    (fmt.ieeeRoundToNearestEvenSqrtResult_ieeeInvalidOperationResult_of_neg hx)

theorem ieeeRoundToNearestEvenSqrtResult_toReal?_of_neg
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : x < 0) :
    (fmt.ieeeRoundToNearestEvenSqrtResult x).value.toReal? = none := by
  rw [fmt.ieeeRoundToNearestEvenSqrtResult_value_of_neg hx]
  rfl

theorem ieeeRoundToNearestEvenSqrtResult_ieeeOverflowResult_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteOverflowRange (Real.sqrt x)) :
    fmt.ieeeOverflowResult IeeeRoundingMode.nearestEven (Real.sqrt x)
      (fmt.ieeeRoundToNearestEvenSqrtResult x) := by
  classical
  have hnot : ¬ x < 0 := not_lt.mpr hx_nonneg
  simpa [ieeeRoundToNearestEvenSqrtResult, hnot, hsqrt] using
    (fmt.ieeeOverflowDefaultResult_ieeeOverflowResult_of_finiteOverflowRange
      (mode := IeeeRoundingMode.nearestEven) hsqrt)

theorem ieeeRoundToNearestEvenSqrtResult_noFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hover : ¬ fmt.finiteOverflowRange (Real.sqrt x))
    (hunder : ¬ fmt.finiteUnderflowRange (Real.sqrt x)) :
    (fmt.ieeeRoundToNearestEvenSqrtResult x).noFlags := by
  classical
  have hnot : ¬ x < 0 := not_lt.mpr hx_nonneg
  simpa [ieeeRoundToNearestEvenSqrtResult, hnot, hover, hunder] using
    (IeeeOperationResult.finiteNoFlags_noFlags
      (fmt.finiteRoundToEvenSqrt x))

theorem ieeeRoundToNearestEvenSqrtResult_toReal?_of_not_finiteOverflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : ¬ fmt.finiteOverflowRange (Real.sqrt x)) :
    (fmt.ieeeRoundToNearestEvenSqrtResult x).value.toReal? =
      some (fmt.finiteRoundToEvenSqrt x) := by
  classical
  have hnot : ¬ x < 0 := not_lt.mpr hx_nonneg
  by_cases hunder : fmt.finiteUnderflowRange (Real.sqrt x)
  · simpa [ieeeRoundToNearestEvenSqrtResult, hnot, hsqrt, hunder] using
      (fmt.ieeeUnderflowDefaultResult_toReal? (Real.sqrt x)
        (fmt.finiteRoundToEvenSqrt x))
  · simpa [ieeeRoundToNearestEvenSqrtResult, hnot, hsqrt, hunder] using
      (IeeeOperationResult.finiteNoFlags_toReal?
        (fmt.finiteRoundToEvenSqrt x))

/-- Finite-normal exact square-root results take the nearest/even finite/no-flags
IEEE wrapper branch. -/
theorem ieeeRoundToNearestEvenSqrtResult_eq_finiteNoFlags_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteNormalRange (Real.sqrt x)) :
    fmt.ieeeRoundToNearestEvenSqrtResult x =
      IeeeOperationResult.finiteNoFlags (fmt.finiteRoundToEvenSqrt x) := by
  classical
  have hnot : ¬ x < 0 := not_lt.mpr hx_nonneg
  simp [ieeeRoundToNearestEvenSqrtResult, hnot,
    fmt.finiteNormalRange_not_finiteOverflowRange hsqrt,
    fmt.finiteNormalRange_not_finiteUnderflowRange hsqrt]

/-- Finite-normal exact square-root results do not raise IEEE flags in the
nearest/even source-facing sqrt wrapper. -/
theorem ieeeRoundToNearestEvenSqrtResult_noFlags_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteNormalRange (Real.sqrt x)) :
    (fmt.ieeeRoundToNearestEvenSqrtResult x).noFlags := by
  rw [fmt.ieeeRoundToNearestEvenSqrtResult_eq_finiteNoFlags_of_finiteNormalRange
    hx_nonneg hsqrt]
  exact IeeeOperationResult.finiteNoFlags_noFlags _

/-- Finite-normal exact square-root results expose the finite round-to-even
sqrt value in the nearest/even IEEE wrapper. -/
theorem ieeeRoundToNearestEvenSqrtResult_toReal?_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteNormalRange (Real.sqrt x)) :
    (fmt.ieeeRoundToNearestEvenSqrtResult x).value.toReal? =
      some (fmt.finiteRoundToEvenSqrt x) := by
  rw [fmt.ieeeRoundToNearestEvenSqrtResult_eq_finiteNoFlags_of_finiteNormalRange
    hx_nonneg hsqrt]
  exact IeeeOperationResult.finiteNoFlags_toReal? _

theorem ieeeRoundToNearestEvenSqrtResult_ieeeUnderflowResult_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteUnderflowRange (Real.sqrt x)) :
    fmt.ieeeUnderflowResult (Real.sqrt x)
      (fmt.finiteRoundToEvenSqrt x)
      (fmt.ieeeRoundToNearestEvenSqrtResult x) := by
  classical
  have hnot : ¬ x < 0 := not_lt.mpr hx_nonneg
  have hover : ¬ fmt.finiteOverflowRange (Real.sqrt x) := by
    intro hover
    have hle := fmt.minNormalMagnitude_le_maxFiniteMagnitude
    rw [finiteUnderflowRange] at hsqrt
    rw [finiteOverflowRange] at hover
    linarith
  simpa [ieeeRoundToNearestEvenSqrtResult, hnot, hover, hsqrt] using
    (fmt.ieeeUnderflowDefaultResult_ieeeUnderflowResult
      hsqrt (fmt.finiteRoundToEvenSqrt_nearestRoundingToFinite x))

theorem ieeeRoundToNearestEvenSqrtResult_ieeeUnderflowResult_and_additiveUnderflowModel
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteUnderflowRange (Real.sqrt x)) :
    fmt.ieeeUnderflowResult (Real.sqrt x)
        (fmt.finiteRoundToEvenSqrt x)
        (fmt.ieeeRoundToNearestEvenSqrtResult x) ∧
      ∃ η : ℝ,
        additiveUnderflowModelWitness (fmt.finiteRoundToEvenSqrt x)
          (Real.sqrt x) fmt.unitRoundoff
          fmt.gradualUnderflowEtaBound 0 η := by
  exact
    ⟨fmt.ieeeRoundToNearestEvenSqrtResult_ieeeUnderflowResult_of_finiteUnderflowRange
        hx_nonneg hsqrt,
      fmt.finiteRoundToEvenSqrt_additiveUnderflowModel_underflow_branch_of_finiteUnderflowRange
        hsqrt⟩

/-- IEEE-facing square-root wrapper parameterized by an IEEE rounding mode.
The negative real-input branch is invalid-operation/NaN for every mode.  For
nonnegative real inputs, overflow uses the IEEE mode-dependent overflow table
and finite underflow/no-flag branches use the finite selector for the same
mode. -/
noncomputable def ieeeRoundToModeSqrtResult
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) :
    IeeeOperationResult := by
  classical
  exact
    if x < 0 then
      ieeeSqrtInvalidDefaultResult x
    else
      let exact := Real.sqrt x
      let rounded := fmt.finiteRoundToModeSqrt mode x
      if fmt.finiteOverflowRange exact then
        fmt.ieeeOverflowDefaultResult mode exact
      else if fmt.finiteUnderflowRange exact then
        fmt.ieeeUnderflowDefaultResult exact rounded
      else
        IeeeOperationResult.finiteNoFlags rounded

/-- Directed-mode alias for square root rounded toward zero. -/
noncomputable def ieeeRoundTowardZeroSqrtResult
    (fmt : FloatingPointFormat) (x : ℝ) : IeeeOperationResult :=
  fmt.ieeeRoundToModeSqrtResult IeeeRoundingMode.towardZero x

/-- Directed-mode alias for square root rounded toward positive infinity. -/
noncomputable def ieeeRoundTowardPositiveSqrtResult
    (fmt : FloatingPointFormat) (x : ℝ) : IeeeOperationResult :=
  fmt.ieeeRoundToModeSqrtResult IeeeRoundingMode.towardPositive x

/-- Directed-mode alias for square root rounded toward negative infinity. -/
noncomputable def ieeeRoundTowardNegativeSqrtResult
    (fmt : FloatingPointFormat) (x : ℝ) : IeeeOperationResult :=
  fmt.ieeeRoundToModeSqrtResult IeeeRoundingMode.towardNegative x

theorem ieeeRoundToModeSqrtResult_nearestEven
    (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.ieeeRoundToModeSqrtResult IeeeRoundingMode.nearestEven x =
      fmt.ieeeRoundToNearestEvenSqrtResult x := by
  classical
  rfl

theorem ieeeRoundToModeSqrtResult_ieeeSqrtInvalidResult_of_neg
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx : x < 0) :
    ieeeSqrtInvalidResult x (fmt.ieeeRoundToModeSqrtResult mode x) := by
  classical
  simpa [ieeeRoundToModeSqrtResult, hx] using
    (ieeeSqrtInvalidDefaultResult_ieeeSqrtInvalidResult hx)

theorem ieeeRoundToModeSqrtResult_ieeeInvalidOperationResult_of_neg
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx : x < 0) :
    ieeeInvalidOperationResult
      (fmt.ieeeRoundToModeSqrtResult mode x) :=
  (fmt.ieeeRoundToModeSqrtResult_ieeeSqrtInvalidResult_of_neg
    (mode := mode) hx).2

theorem ieeeRoundToModeSqrtResult_value_of_neg
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx : x < 0) :
    (fmt.ieeeRoundToModeSqrtResult mode x).value = IeeeValue.nan :=
  ieeeInvalidOperationResult_value
    (fmt.ieeeRoundToModeSqrtResult_ieeeInvalidOperationResult_of_neg
      (mode := mode) hx)

theorem ieeeRoundToModeSqrtResult_hasInvalidOperationFlag_of_neg
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx : x < 0) :
    (fmt.ieeeRoundToModeSqrtResult mode x).hasFlag
      IeeeExceptionFlag.invalidOperation :=
  ieeeInvalidOperationResult_hasInvalidOperationFlag
    (fmt.ieeeRoundToModeSqrtResult_ieeeInvalidOperationResult_of_neg
      (mode := mode) hx)

theorem ieeeRoundToModeSqrtResult_toReal?_of_neg
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx : x < 0) :
    (fmt.ieeeRoundToModeSqrtResult mode x).value.toReal? = none := by
  rw [fmt.ieeeRoundToModeSqrtResult_value_of_neg (mode := mode) hx]
  rfl

theorem ieeeRoundToModeSqrtResult_ieeeOverflowResult_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteOverflowRange (Real.sqrt x)) :
    fmt.ieeeOverflowResult mode (Real.sqrt x)
      (fmt.ieeeRoundToModeSqrtResult mode x) := by
  classical
  have hnot : ¬ x < 0 := not_lt.mpr hx_nonneg
  simpa [ieeeRoundToModeSqrtResult, hnot, hsqrt] using
    (fmt.ieeeOverflowDefaultResult_ieeeOverflowResult_of_finiteOverflowRange
      (mode := mode) hsqrt)

theorem ieeeRoundToModeSqrtResult_eq_finiteNoFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hover : ¬ fmt.finiteOverflowRange (Real.sqrt x))
    (hunder : ¬ fmt.finiteUnderflowRange (Real.sqrt x)) :
    fmt.ieeeRoundToModeSqrtResult mode x =
      IeeeOperationResult.finiteNoFlags
        (fmt.finiteRoundToModeSqrt mode x) := by
  classical
  have hnot : ¬ x < 0 := not_lt.mpr hx_nonneg
  simp [ieeeRoundToModeSqrtResult, hnot, hover, hunder]

theorem ieeeRoundToModeSqrtResult_noFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hover : ¬ fmt.finiteOverflowRange (Real.sqrt x))
    (hunder : ¬ fmt.finiteUnderflowRange (Real.sqrt x)) :
    (fmt.ieeeRoundToModeSqrtResult mode x).noFlags := by
  rw [
    fmt.ieeeRoundToModeSqrtResult_eq_finiteNoFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
      hx_nonneg hover hunder]
  exact IeeeOperationResult.finiteNoFlags_noFlags _

theorem ieeeRoundToModeSqrtResult_toReal?_of_not_finiteOverflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : ¬ fmt.finiteOverflowRange (Real.sqrt x)) :
    (fmt.ieeeRoundToModeSqrtResult mode x).value.toReal? =
      some (fmt.finiteRoundToModeSqrt mode x) := by
  classical
  have hnot : ¬ x < 0 := not_lt.mpr hx_nonneg
  by_cases hunder : fmt.finiteUnderflowRange (Real.sqrt x)
  · simpa [ieeeRoundToModeSqrtResult, hnot, hsqrt, hunder] using
      (fmt.ieeeUnderflowDefaultResult_toReal? (Real.sqrt x)
        (fmt.finiteRoundToModeSqrt mode x))
  · simpa [ieeeRoundToModeSqrtResult, hnot, hsqrt, hunder] using
      (IeeeOperationResult.finiteNoFlags_toReal?
        (fmt.finiteRoundToModeSqrt mode x))

/-- Finite-normal exact square-root results take the finite/no-flags branch for
any source-facing IEEE rounding mode wrapper. -/
theorem ieeeRoundToModeSqrtResult_eq_finiteNoFlags_of_finiteNormalRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteNormalRange (Real.sqrt x)) :
    fmt.ieeeRoundToModeSqrtResult mode x =
      IeeeOperationResult.finiteNoFlags
        (fmt.finiteRoundToModeSqrt mode x) := by
  exact
    fmt.ieeeRoundToModeSqrtResult_eq_finiteNoFlags_of_not_finiteOverflowRange_of_not_finiteUnderflowRange
      hx_nonneg
      (fmt.finiteNormalRange_not_finiteOverflowRange hsqrt)
      (fmt.finiteNormalRange_not_finiteUnderflowRange hsqrt)

/-- Finite-normal exact square-root results do not raise IEEE flags for any
source-facing rounding mode wrapper. -/
theorem ieeeRoundToModeSqrtResult_noFlags_of_finiteNormalRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteNormalRange (Real.sqrt x)) :
    (fmt.ieeeRoundToModeSqrtResult mode x).noFlags := by
  rw [fmt.ieeeRoundToModeSqrtResult_eq_finiteNoFlags_of_finiteNormalRange
    hx_nonneg hsqrt]
  exact IeeeOperationResult.finiteNoFlags_noFlags _

/-- Finite-normal exact square-root results expose the selected finite rounded
sqrt value for any source-facing IEEE rounding mode wrapper. -/
theorem ieeeRoundToModeSqrtResult_toReal?_of_finiteNormalRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteNormalRange (Real.sqrt x)) :
    (fmt.ieeeRoundToModeSqrtResult mode x).value.toReal? =
      some (fmt.finiteRoundToModeSqrt mode x) := by
  rw [fmt.ieeeRoundToModeSqrtResult_eq_finiteNoFlags_of_finiteNormalRange
    hx_nonneg hsqrt]
  exact IeeeOperationResult.finiteNoFlags_toReal? _

theorem ieeeRoundToModeSqrtResult_ieeeUnderflowModeResult_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {mode : IeeeRoundingMode} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteUnderflowRange (Real.sqrt x)) :
    fmt.ieeeUnderflowModeResult mode (Real.sqrt x)
      (fmt.finiteRoundToModeSqrt mode x)
      (fmt.ieeeRoundToModeSqrtResult mode x) := by
  classical
  have hnot : ¬ x < 0 := not_lt.mpr hx_nonneg
  have hover : ¬ fmt.finiteOverflowRange (Real.sqrt x) := by
    intro hover
    have hle := fmt.minNormalMagnitude_le_maxFiniteMagnitude
    rw [finiteUnderflowRange] at hsqrt
    rw [finiteOverflowRange] at hover
    linarith
  simpa [ieeeRoundToModeSqrtResult, hnot, hover, hsqrt] using
    (fmt.ieeeUnderflowDefaultResult_ieeeUnderflowModeResult
      hsqrt
      (fmt.finiteRoundToModeSqrt_ieeeUnderflowModeRoundingEvidence_of_finiteUnderflowRange
        (mode := mode) hsqrt))

theorem ieeeRoundTowardZeroSqrtResult_ieeeOverflowResult_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteOverflowRange (Real.sqrt x)) :
    fmt.ieeeOverflowResult IeeeRoundingMode.towardZero (Real.sqrt x)
      (fmt.ieeeRoundTowardZeroSqrtResult x) := by
  simpa [ieeeRoundTowardZeroSqrtResult] using
    (fmt.ieeeRoundToModeSqrtResult_ieeeOverflowResult_of_finiteOverflowRange
      (mode := IeeeRoundingMode.towardZero) hx_nonneg hsqrt)

theorem ieeeRoundTowardPositiveSqrtResult_ieeeOverflowResult_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteOverflowRange (Real.sqrt x)) :
    fmt.ieeeOverflowResult IeeeRoundingMode.towardPositive (Real.sqrt x)
      (fmt.ieeeRoundTowardPositiveSqrtResult x) := by
  simpa [ieeeRoundTowardPositiveSqrtResult] using
    (fmt.ieeeRoundToModeSqrtResult_ieeeOverflowResult_of_finiteOverflowRange
      (mode := IeeeRoundingMode.towardPositive) hx_nonneg hsqrt)

theorem ieeeRoundTowardNegativeSqrtResult_ieeeOverflowResult_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hsqrt : fmt.finiteOverflowRange (Real.sqrt x)) :
    fmt.ieeeOverflowResult IeeeRoundingMode.towardNegative (Real.sqrt x)
      (fmt.ieeeRoundTowardNegativeSqrtResult x) := by
  simpa [ieeeRoundTowardNegativeSqrtResult] using
    (fmt.ieeeRoundToModeSqrtResult_ieeeOverflowResult_of_finiteOverflowRange
      (mode := IeeeRoundingMode.towardNegative) hx_nonneg hsqrt)

/-- IEEE-facing nearest/even square-root wrapper over IEEE values.  Finite
payloads use the real-input wrapper above; non-finite special values take the
first explicit Chapter 2 special-value branches. -/
noncomputable def ieeeRoundToNearestEvenSqrtValueResult
    (fmt : FloatingPointFormat) : IeeeValue → IeeeOperationResult
  | IeeeValue.finite x => fmt.ieeeRoundToNearestEvenSqrtResult x
  | IeeeValue.posZero => IeeeOperationResult.valueNoFlags IeeeValue.posZero
  | IeeeValue.negZero => IeeeOperationResult.valueNoFlags IeeeValue.negZero
  | IeeeValue.posInf => IeeeOperationResult.valueNoFlags IeeeValue.posInf
  | IeeeValue.negInf => ieeeInvalidOperationDefaultResult
  | IeeeValue.nan => IeeeOperationResult.valueNoFlags IeeeValue.nan

theorem ieeeRoundToNearestEvenSqrtValueResult_finite
    {fmt : FloatingPointFormat} (x : ℝ) :
    fmt.ieeeRoundToNearestEvenSqrtValueResult (IeeeValue.finite x) =
      fmt.ieeeRoundToNearestEvenSqrtResult x := rfl

theorem ieeeRoundToNearestEvenSqrtValueResult_nan_special
    {fmt : FloatingPointFormat} :
    ieeeSqrtSpecialValueResult IeeeValue.nan
      (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.nan) :=
  ieeeSqrtSpecialValueResult_nan_valueNoFlags

theorem ieeeRoundToNearestEvenSqrtValueResult_posZero_signedZero
    {fmt : FloatingPointFormat} :
    ieeeSqrtSignedZeroResult IeeeValue.posZero
      (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.posZero) :=
  ieeeSqrtSignedZeroResult_posZero_valueNoFlags

theorem ieeeRoundToNearestEvenSqrtValueResult_negZero_signedZero
    {fmt : FloatingPointFormat} :
    ieeeSqrtSignedZeroResult IeeeValue.negZero
      (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.negZero) :=
  ieeeSqrtSignedZeroResult_negZero_valueNoFlags

theorem ieeeRoundToNearestEvenSqrtValueResult_posInf_special
    {fmt : FloatingPointFormat} :
    ieeeSqrtSpecialValueResult IeeeValue.posInf
      (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.posInf) :=
  ieeeSqrtSpecialValueResult_posInf_valueNoFlags

theorem ieeeRoundToNearestEvenSqrtValueResult_negInf_special
    {fmt : FloatingPointFormat} :
    ieeeSqrtSpecialValueResult IeeeValue.negInf
      (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.negInf) :=
  ieeeSqrtSpecialValueResult_negInf_invalid

theorem ieeeRoundToNearestEvenSqrtValueResult_nan_value
    {fmt : FloatingPointFormat} :
    (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.nan).value =
      IeeeValue.nan :=
  ieeeSqrtSpecialValueResult_value_nan
    (fmt.ieeeRoundToNearestEvenSqrtValueResult_nan_special)

theorem ieeeRoundToNearestEvenSqrtValueResult_nan_noFlags
    {fmt : FloatingPointFormat} :
    (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.nan).noFlags :=
  ieeeSqrtSpecialValueResult_noFlags_nan
    (fmt.ieeeRoundToNearestEvenSqrtValueResult_nan_special)

theorem ieeeRoundToNearestEvenSqrtValueResult_posZero_value
    {fmt : FloatingPointFormat} :
    (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.posZero).value =
      IeeeValue.posZero :=
  ieeeSqrtSignedZeroResult_value_posZero
    (fmt.ieeeRoundToNearestEvenSqrtValueResult_posZero_signedZero)

theorem ieeeRoundToNearestEvenSqrtValueResult_posZero_noFlags
    {fmt : FloatingPointFormat} :
    (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.posZero).noFlags :=
  ieeeSqrtSignedZeroResult_noFlags_posZero
    (fmt.ieeeRoundToNearestEvenSqrtValueResult_posZero_signedZero)

theorem ieeeRoundToNearestEvenSqrtValueResult_posZero_toReal?
    {fmt : FloatingPointFormat} :
    (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.posZero).value.toReal? =
      some 0 := by
  rw [fmt.ieeeRoundToNearestEvenSqrtValueResult_posZero_value]
  rfl

theorem ieeeRoundToNearestEvenSqrtValueResult_negZero_value
    {fmt : FloatingPointFormat} :
    (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.negZero).value =
      IeeeValue.negZero :=
  ieeeSqrtSignedZeroResult_value_negZero
    (fmt.ieeeRoundToNearestEvenSqrtValueResult_negZero_signedZero)

theorem ieeeRoundToNearestEvenSqrtValueResult_negZero_noFlags
    {fmt : FloatingPointFormat} :
    (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.negZero).noFlags :=
  ieeeSqrtSignedZeroResult_noFlags_negZero
    (fmt.ieeeRoundToNearestEvenSqrtValueResult_negZero_signedZero)

theorem ieeeRoundToNearestEvenSqrtValueResult_negZero_toReal?
    {fmt : FloatingPointFormat} :
    (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.negZero).value.toReal? =
      some 0 := by
  rw [fmt.ieeeRoundToNearestEvenSqrtValueResult_negZero_value]
  rfl

theorem ieeeRoundToNearestEvenSqrtValueResult_posInf_value
    {fmt : FloatingPointFormat} :
    (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.posInf).value =
      IeeeValue.posInf :=
  ieeeSqrtSpecialValueResult_value_posInf
    (fmt.ieeeRoundToNearestEvenSqrtValueResult_posInf_special)

theorem ieeeRoundToNearestEvenSqrtValueResult_posInf_noFlags
    {fmt : FloatingPointFormat} :
    (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.posInf).noFlags :=
  ieeeSqrtSpecialValueResult_noFlags_posInf
    (fmt.ieeeRoundToNearestEvenSqrtValueResult_posInf_special)

theorem ieeeRoundToNearestEvenSqrtValueResult_negInf_ieeeInvalidOperationResult
    {fmt : FloatingPointFormat} :
    ieeeInvalidOperationResult
      (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.negInf) :=
  ieeeSqrtSpecialValueResult_negInf_ieeeInvalidOperationResult
    (fmt.ieeeRoundToNearestEvenSqrtValueResult_negInf_special)

theorem ieeeRoundToNearestEvenSqrtValueResult_negInf_value
    {fmt : FloatingPointFormat} :
    (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.negInf).value =
      IeeeValue.nan :=
  ieeeInvalidOperationResult_value
    (fmt.ieeeRoundToNearestEvenSqrtValueResult_negInf_ieeeInvalidOperationResult)

theorem ieeeRoundToNearestEvenSqrtValueResult_negInf_hasInvalidOperationFlag
    {fmt : FloatingPointFormat} :
    (fmt.ieeeRoundToNearestEvenSqrtValueResult IeeeValue.negInf).hasFlag
      IeeeExceptionFlag.invalidOperation :=
  ieeeInvalidOperationResult_hasInvalidOperationFlag
    (fmt.ieeeRoundToNearestEvenSqrtValueResult_negInf_ieeeInvalidOperationResult)

/-- Source-style arbitrary tie choice for `fl` on the finite normal range.
This is a noncomputable choice from the nearest-rounding relation, not a
round-to-even or IEEE tie-breaking rule. -/
noncomputable def finiteNormalFl (fmt : FloatingPointFormat) (x : ℝ)
    (hx : fmt.finiteNormalRange x) : ℝ :=
  Classical.choose
    (fmt.exists_nearestRoundingToFinite_inverseRelErrorModel_finiteNormalRange hx)

theorem finiteNormalFl_spec
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.nearestRoundingToFinite x (fmt.finiteNormalFl x hx) ∧
      inverseRelErrorModel (fmt.finiteNormalFl x hx) x fmt.unitRoundoff := by
  exact
    Classical.choose_spec
      (fmt.exists_nearestRoundingToFinite_inverseRelErrorModel_finiteNormalRange hx)

theorem finiteNormalFl_nearestRoundingToFinite
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.nearestRoundingToFinite x (fmt.finiteNormalFl x hx) :=
  (fmt.finiteNormalFl_spec hx).1

theorem finiteNormalFl_inverseRelErrorModel
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    inverseRelErrorModel (fmt.finiteNormalFl x hx) x fmt.unitRoundoff :=
  (fmt.finiteNormalFl_spec hx).2

theorem finiteNormalFl_inverseRelErrorWitness
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite x (fmt.finiteNormalFl x hx) ∧
        |δ| ≤ fmt.unitRoundoff ∧
          inverseRelErrorWitness (fmt.finiteNormalFl x hx) x δ := by
  rcases fmt.finiteNormalFl_inverseRelErrorModel hx with ⟨δ, hδ, hwit⟩
  exact ⟨δ, fmt.finiteNormalFl_nearestRoundingToFinite hx, hδ, hwit⟩

theorem finiteNormalFl_signedRelErrorWitness
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite x (fmt.finiteNormalFl x hx) ∧
        |δ| ≤ fmt.unitRoundoff ∧
          signedRelErrorWitness (fmt.finiteNormalFl x hx) x δ := by
  rcases
    fmt.nearestRoundingToFinite_signedRelErrorWitness_of_finiteNormalRange
      (fmt.finiteNormalFl_nearestRoundingToFinite hx) hx with
    ⟨δ, hδ, hwit⟩
  exact ⟨δ, fmt.finiteNormalFl_nearestRoundingToFinite hx, hδ, hwit⟩

theorem finiteNormalFl_signedRelErrorWitness_lt
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite x (fmt.finiteNormalFl x hx) ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness (fmt.finiteNormalFl x hx) x δ := by
  rcases
    fmt.nearestRoundingToFinite_signedRelErrorWitness_lt_of_finiteNormalRange
      (fmt.finiteNormalFl_nearestRoundingToFinite hx) hx with
    ⟨δ, hδ, hwit⟩
  exact ⟨δ, fmt.finiteNormalFl_nearestRoundingToFinite hx, hδ, hwit⟩

end FloatingPointFormat

end

end LeanFpAnalysis.FP
