# Chapter 4 Problem 4.2 Wilkinson Attainability Bottleneck

## Source Target

- Source: `references/Chapter04_full.pdf`, pp. 100--101, Problem 4.2.
- Supporting source: Higham solution 4.2, p. 542 of
  `references/HighamBook.pdf`.
- Cited source: Wilkinson [1088] 1963, pp. 19--20.
- Claim: Wilkinson's powers-of-two input family nearly attains the recursive
  summation bounds (4.3) and (4.4).

Higham's hint fixes `u = 2^-t`, `n = 2^r`, with `r << t`, and uses the list

```text
x(1) = 1,
x(2) = 1 - 2^-t,
x(3:4) = 1 - 2^(1-t),
...
x(2^(r-1)+1 : 2^r) = 1 - 2^(r-1-t).
```

The solution sketch says that the low-order `2^(k-t)` part does not propagate
through the corresponding rounded addition, so the computed recursive sum is
`2^r`.  The exact source sum is lower by the accumulated defect, and that
defect is then compared with the bounds (4.3) and (4.4).

## Resolution Status

The red bottleneck for the concrete IEEE-double route is closed.  The local
formalization proves the displayed family for `t = 53`, `r <= 52`, concrete
IEEE-double round-to-even addition, finite representability of every displayed
input, the exact rounded trace, the realized-error identity, and constant-factor
near-attainment wrappers.

The source text is stated in generic `t`-digit language.  This file therefore
does not claim a fully generic arbitrary-precision base-2 theorem; it records
the completed IEEE-double instantiation and the optional generic lifting target
below.

## Closed IEEE-Double Theorem Surface

The current source-family, trace, and error algebra is in
`LeanFpAnalysis/FP/Algorithms/WilkinsonAttainability.lean`.

- `wilkinsonProblem42BlockValue`
- `wilkinsonProblem42Input`
- `wilkinsonProblem42ExactSum`
- `wilkinsonProblem42Defect`
- `wilkinsonProblem42Vector`
- `finiteRoundToEvenRecursiveSum`
- `finiteRoundToEvenListSum`
- `finiteRoundToEvenRecursiveSum_eq_listSum`
- `wilkinsonProblem42Input_length`
- `wilkinsonProblem42Input_sum_eq`
- `wilkinsonProblem42Input_zero`
- `wilkinsonProblem42Input_succ`
- `wilkinsonProblem42Vector_toList`
- `wilkinsonProblem42Vector_sum_eq`
- `wilkinsonProblem42ExactSum_add_defect`
- `wilkinsonProblem42Defect_nonneg`
- `wilkinsonProblem42Defect_closed_form`
- `wilkinsonProblem42ExactSum_le_pow`
- `wilkinsonProblem42_first_order_bound_le_three_defect_plus_u`
- `wilkinsonProblem42_gamma_bound_le_three_defect_plus_u_div`
- `wilkinsonProblem42_abs_error_eq_defect_of_recursiveSum_eq_pow`
- `wilkinsonProblem42_recursiveSum_eq_pow_zero`
- `wilkinsonProblem42BlockValue_ieeeDouble_finiteSystem`
- `wilkinsonProblem42Input_ieeeDouble_all_finiteSystem`
- `wilkinsonProblem42Vector_ieeeDouble_finiteSystem`
- `wilkinsonProblem42_ieeeDouble_sameBinade_add_rounds_to_nat`
- `wilkinsonProblem42_ieeeDouble_block_boundary_add_rounds_to_pow`
- `wilkinsonProblem42_ieeeDouble_block_prefix_accumulator`
- `wilkinsonProblem42_ieeeDouble_block_rounds_pow_to_next_pow`
- `wilkinsonProblem42_ieeeDouble_listRecursiveSum_eq_pow`
- `wilkinsonProblem42_ieeeDouble_finiteRecursiveSum_eq_pow`
- `wilkinsonProblem42_ieeeDouble_abs_error_eq_defect`
- `wilkinsonProblem42_ieeeDouble_abs_error_closed_form`
- `wilkinsonProblem42_unit_roundoff_le_defect_of_pos`
- `wilkinsonProblem42_ieeeDouble_first_order_bound_le_three_abs_error_plus_u`
- `wilkinsonProblem42_ieeeDouble_first_order_bound_le_four_abs_error`
- `wilkinsonProblem42_ieeeDouble_gamma_bound_le_three_abs_error_plus_u_div`
- `wilkinsonProblem42_ieeeDouble_gamma_bound_le_eight_abs_error`
- `wilkinsonProblem42BlockValue_nonneg_of_le`
- `wilkinsonProblem42Input_nonneg_of_le`
- `wilkinsonProblem42Vector_nonneg_of_le`
- `wilkinsonProblem42Vector_oneSigned_of_le`
- `wilkinsonProblem42Vector_sum_abs_eq`
- `wilkinsonProblem42ExactSum_pos_of_le`
- `wilkinsonProblem42ExactSum_ne_zero_of_le`
- `wilkinsonProblem42_recursiveSum_running_error_bound`
- `wilkinsonProblem42_recursiveSum_forward_error_bound`
- `wilkinsonProblem42_recursiveSum_relError_le_gamma`
- `wilkinsonProblem42_recursiveSum_relError_le_pow_mul_u`

## Final Concrete Theorem Family

```lean
theorem wilkinsonProblem42BlockValue_ieeeDouble_finiteSystem
    {j : ℕ} (hj : j ≤ 52) :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem
      (wilkinsonProblem42BlockValue 53 j)

theorem wilkinsonProblem42Input_ieeeDouble_all_finiteSystem
    {r : ℕ} (hr : r ≤ 53) :
    ∀ x ∈ wilkinsonProblem42Input 53 r,
      FloatingPointFormat.ieeeDoubleFormat.finiteSystem x

theorem wilkinsonProblem42Vector_ieeeDouble_finiteSystem
    {r : ℕ} (hr : r ≤ 53) (i : Fin (2 ^ r)) :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem
      (wilkinsonProblem42Vector 53 r i)

theorem wilkinsonProblem42_ieeeDouble_finiteRecursiveSum_eq_pow
    {r : ℕ} (hr : r ≤ 52) :
    finiteRoundToEvenRecursiveSum FloatingPointFormat.ieeeDoubleFormat
        (2 ^ r) (wilkinsonProblem42Vector 53 r) =
      (2 : ℝ) ^ r

theorem wilkinsonProblem42_ieeeDouble_abs_error_eq_defect
    {r : ℕ} (hr : r ≤ 52) :
    |finiteRoundToEvenRecursiveSum FloatingPointFormat.ieeeDoubleFormat
        (2 ^ r) (wilkinsonProblem42Vector 53 r) -
        wilkinsonProblem42ExactSum 53 r| =
      wilkinsonProblem42Defect 53 r

theorem wilkinsonProblem42_ieeeDouble_first_order_bound_le_four_abs_error
    {r : ℕ} (hr : r ≤ 52) (hrpos : 0 < r) :
    (((2 ^ r - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-(53 : ℤ))) *
        wilkinsonProblem42ExactSum 53 r ≤
      4 * |finiteRoundToEvenRecursiveSum FloatingPointFormat.ieeeDoubleFormat
          (2 ^ r) (wilkinsonProblem42Vector 53 r) -
          wilkinsonProblem42ExactSum 53 r|

theorem wilkinsonProblem42_ieeeDouble_gamma_bound_le_eight_abs_error
    (fp : FPModel) {r : ℕ}
    (hr : r ≤ 52) (hrpos : 0 < r)
    (hunit : fp.u = (2 : ℝ) ^ (-(53 : ℤ)))
    (hsmall :
      2 * (((2 ^ r - 1 : ℕ) : ℝ) *
        (2 : ℝ) ^ (-(53 : ℤ))) ≤ 1) :
    gamma fp (2 ^ r - 1) * wilkinsonProblem42ExactSum 53 r ≤
      8 * |finiteRoundToEvenRecursiveSum FloatingPointFormat.ieeeDoubleFormat
          (2 ^ r) (wilkinsonProblem42Vector 53 r) -
          wilkinsonProblem42ExactSum 53 r|
```

## Dependency Checklist

| Dependency | Status | Lean evidence |
|---|---|---|
| Source list matches the displayed Problem 4.2 family | closed | `wilkinsonProblem42Input_zero`, `wilkinsonProblem42Input_succ`, `wilkinsonProblem42Input_length` |
| `Fin (2^r)` bridge for recursive summation | closed | `wilkinsonProblem42Vector`, `wilkinsonProblem42Vector_toList`, `wilkinsonProblem42Vector_sum_eq` |
| Exact source-sum plus low-order defect equals `2^r` | closed | `wilkinsonProblem42ExactSum_add_defect` |
| Closed form for the low-order defect | closed | `wilkinsonProblem42Defect_closed_form` |
| First-order comparison with the displayed (4.4) scale | closed | `wilkinsonProblem42_first_order_bound_le_three_defect_plus_u` |
| Exact gamma-denominator comparison with the displayed (4.4) upper bound | closed | `wilkinsonProblem42_gamma_bound_le_three_defect_plus_u_div` |
| Concrete base-2 input representability for IEEE double | closed | `wilkinsonProblem42BlockValue_ieeeDouble_finiteSystem`, `wilkinsonProblem42Input_ieeeDouble_all_finiteSystem`, `wilkinsonProblem42Vector_ieeeDouble_finiteSystem` |
| Reusable IEEE-double same-binade step | closed | `wilkinsonProblem42_ieeeDouble_sameBinade_add_rounds_to_nat` |
| Reusable IEEE-double power-boundary step | closed | `wilkinsonProblem42_ieeeDouble_block_boundary_add_rounds_to_pow` |
| Complete IEEE-double block iteration | closed | `wilkinsonProblem42_ieeeDouble_block_prefix_accumulator`, `wilkinsonProblem42_ieeeDouble_block_rounds_pow_to_next_pow` |
| Arbitrary IEEE-double list and `Fin` trace | closed | `wilkinsonProblem42_ieeeDouble_listRecursiveSum_eq_pow`, `wilkinsonProblem42_ieeeDouble_finiteRecursiveSum_eq_pow` |
| Concrete realized error and closed form | closed | `wilkinsonProblem42_ieeeDouble_abs_error_eq_defect`, `wilkinsonProblem42_ieeeDouble_abs_error_closed_form` |
| First-order smallness-to-factor packaging | closed | `wilkinsonProblem42_ieeeDouble_first_order_bound_le_four_abs_error` |
| Gamma smallness-to-factor packaging | closed | `wilkinsonProblem42_ieeeDouble_gamma_bound_le_eight_abs_error` |
| Generic arbitrary-precision `t`-digit base-2 theorem | open / not claimed | Optional lift from the IEEE-double proof pattern to a parameterized format. |

## Failed Or Insufficient Routes

- The abstract `FPModel` standard model is insufficient for the rounded trace:
  it supplies a bounded local relative error witness, but it does not determine
  whether the low-order term is rounded away at each step.
- The exact defect theorem alone is not a near-attainment theorem.  It closes
  only the algebra after assuming the finite-format trace returns `2^r`; the
  concrete IEEE-double trace is now proved separately.

## Optional Generic Lifting Target

The next theorem only matters if the Chapter 4 row is required at full generic
`t`-digit source generality rather than at the concrete IEEE-double
instantiation:

```lean
theorem wilkinsonProblem42BlockValue_baseTwo_finiteSystem
    (fmt : FloatingPointFormat) (t : ℕ)
    (hbeta : fmt.beta = 2) (ht : fmt.t = t)
    (he0 : fmt.exponentInRange 0)
    {j : ℕ} (hj : j + 1 ≤ t) :
    fmt.finiteSystem (wilkinsonProblem42BlockValue t j)
```

That theorem would be followed by parameterized versions of the same-binade
step, boundary step, block iteration, and trace theorem.  The current verified
repository theorem surface intentionally closes the concrete IEEE-double route.
