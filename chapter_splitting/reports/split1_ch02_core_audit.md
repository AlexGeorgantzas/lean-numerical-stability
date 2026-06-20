# Higham Chapter 2 Formalization Report

## Source and scope

- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM).
- Chapter: Chapter 2, "Floating Point Arithmetic".
- Printed pages: 35-60 in the chapter PDF; Appendix A solution rows on pp. 532-535.
- Source file: `References/1.9780898718027.ch2.pdf`.
- Mode: core.
- Parallel split: 1.
- Planning documents consulted: `HIGHAM_PARALLEL_FORMALIZATION_BLUEPRINT.md`, Split 1 of `split_primary_contracts.md`, and `chapter_index.md`.
- Selected-scope gate: PASS after the Chapter 2 patches listed below and the validation commands recorded at the end.

## Closure added in this pass

| Source label | Lean declaration | File | Theorem surface | Notes |
|---|---|---|---|---|
| Theorem 2.4 | `FloatingPointFormat.fergusonExponentConditionLe`, `finiteRoundToEvenOp_sub_eq_exact_of_fergusonConditionLe`, `fergusonExponentConditionLe_sub_finiteNormalRange`, `ieeeRoundToNearestEvenOpResult_sub_eq_finiteNoFlags_of_fergusonConditionLe`, `ieeeRoundToNearestEvenOpResult_sub_noFlags_of_fergusonConditionLe`, `ieeeRoundToNearestEvenOpResult_sub_toReal?_of_fergusonConditionLe` | `LeanFpAnalysis/FP/Analysis/FloatingPointArithmetic.lean` | Inclusive source endpoint `e(x-y) <= min(e(x),e(y))`; exact subtraction and nearest/even IEEE finite/no-flags wrappers. | Previous strict wrappers remain available, but the PDF statement uses `<=`. |
| Theorem 2.5 | `FloatingPointFormat.sterbenzRatioConditionLe`, `finiteSystem_sub_finiteSystem_of_sterbenzRatioConditionLe`, `finiteRoundToEvenOp_sub_finiteSystem_eq_exact_of_sterbenzRatioConditionLe` | `LeanFpAnalysis/FP/Analysis/FloatingPointArithmetic.lean` | Inclusive source endpoint `y/2 <= x <= 2*y`; exact finite subtraction. | The gradual-underflow removal of the side condition is represented by finite/subnormal branch wrappers. |
| Problem 2.17 | `FloatingPointFormat.problem2_17_two_mul_maxFiniteMagnitude_finiteOverflowRange` | `LeanFpAnalysis/FP/Analysis/FloatingPointArithmetic.lean` | `2*xmax` lies in the finite overflow range; mode-specific finite/infinite result is supplied by the existing IEEE overflow table. | This corrects a local numbering drift where an older `Problem2_17.lean` file covers a discriminant discussion, not source Problem 2.17. |
| Problem 2.26 | `FloatingPointFormat.finiteRoundToEvenFMA_product_correction_add_eq_product_of_finiteSystem`, `FloatingPointFormat.finiteRoundToEvenFMA_product_expansion_with_rounded_product` | `LeanFpAnalysis/FP/Analysis/FusedMultiplyAdd.lean` | If the FMA correction term is representable, `a + flFMA(x,y,-a) = x*y`, including `a = fl(x*y)`. | This is the source's product decomposition exercise. |
| Repository navigation | README Chapter 2 rows | `README.md` | The lookup names now include the inclusive Ferguson/Sterbenz declarations, the true source Problem 2.17 row, and the FMA product decomposition row. | The older discriminant row was relabeled as a Section 2.7/FMA-discussion artifact. |

## Primary labels

| Source label | Decision | Lean artifact/status |
|---|---|---|
| Lemma 2.1 | FORMALIZE_CORE | Closed by `FloatingPointFormat.problem2_2_lemma2_1_spacing_bounds` and adjacent-spacing infrastructure. |
| Theorem 2.2 | FORMALIZE_CORE | Closed by `FloatingPointFormat.nearestRoundingToFinite_signedRelErrorWitness_lt_of_finiteNormalRange` and finite normal nearest/even wrappers. |
| Theorem 2.3 | FORMALIZE_CORE | Closed by `FloatingPointFormat.problem2_4_theorem2_3_*`, `inverseRelErrorWitness`, and `inverseRelErrorModel`. |
| Theorem 2.4 | FORMALIZE_CORE | Closed by the new inclusive Ferguson condition and exact subtraction wrappers. |
| Theorem 2.5 | FORMALIZE_CORE | Closed by the new inclusive Sterbenz condition and exact finite/subnormal subtraction wrappers. |

## Numbered equations

| Equation | Decision | Lean artifact/status |
|---|---|---|
| (2.1) | FORMALIZE_CORE | `FloatingPointFormat.normalizedValue` and `FloatingPointFormat.finiteSystem`. |
| (2.2) | FORMALIZE_CORE | `FloatingPointFormat.digitStringInRange`, `positionalMantissa`, and `positionalValue`. |
| (2.3) | FORMALIZE_CORE | Theorem 2.2 signed relative-error witness wrappers. |
| (2.4) | FORMALIZE_CORE | `FPModel.model_basicOp`, `FPModel.model_sqrt`, and finite normal standard-model wrappers. |
| (2.5) | FORMALIZE_CORE | `inverseRelErrorWitness`, `inverseRelErrorModel`, `inverseRelErrorModel_iff_relErrorComputedDenom_le`. |
| (2.6), (2.6a), (2.6b) | FORMALIZE_CORE | `NoGuardFPModel`, `noGuardAddWitness`, `noGuardSubWitness`, `noGuardMulDivWitness`, `noGuardBasicOpWitness`. |
| (2.7) | FORMALIZE_CORE | `kahanHeronArea` and the Problem 2.23/Heron theorem surface. |
| (2.8) | FORMALIZE_CORE | `additiveUnderflowModelWitness`, `strictAdditiveUnderflowModelWitness`, and finite operation/square-root underflow wrappers. |

## Problem ledger

| Problem | Decision | Reason code | Lean artifact/status |
|---|---|---|---|
| 2.1 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Count formulas and IEEE single/double constants are in the Chapter 2 finite-format vocabulary. |
| 2.2 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Closed by `problem2_2_lemma2_1_spacing_bounds`. |
| 2.3 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Closed by `Problem2_3IeeeSingleAdjacentGap` and same-exponent/boundary/subnormal count classifiers. |
| 2.4 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Closed by the Theorem 2.3 inverse-error wrappers. |
| 2.5 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Closed by `Problem2_5.lean` binary expansion and IEEE-single rounding-error results. |
| 2.6 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Closed by `Problem2_6.lean` exact integer interval theorems; listed even though the split contract omits it. |
| 2.7 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Closed by `Problem2_7.lean` finite IEEE true/false and counterexample rows. |
| 2.8 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Decimal midpoint counterexample and guarded midpoint inequality are closed by `problem2_8_*` theorem surfaces. Full concrete IEEE instruction semantics remain outside core. |
| 2.9 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Closed by `problem2_9_*` double-rounding theorems. |
| 2.10 | SKIP | SKIP-EMPIRICAL | Source asks to "Test the theorem on your computer." The historical machine run is not a Lean obligation. Optional mathematical Kahan-theorem infrastructure and `experiments/chapter02/problem2_10_kahan_test.py` remain advisory/non-gating. |
| 2.11 | SKIP | SKIP-EMPIRICAL | Leading-digit investigations over powers, factorials, random eigenvalues, constants, and newspapers are empirical/source-data tasks. The deterministic distribution infrastructure in `LeadingDigitDistribution.lean` is a replacement mathematical phenomenon, not a required historical-output proof. |
| 2.12 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Closed by `Problem2_12.lean` reciprocal product theorem. |
| 2.13 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Closed by `Problem2_13.lean` certificate for the smallest `j`. |
| 2.14 | SKIP | SKIP-EMPIRICAL | Source asks to test Kahan's estimate on available machines. Local finite single/double theorem surfaces are mathematical replacements; the machine-test instruction is non-gating. |
| 2.15 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Closed by `Problem2_15_16.lean` IEEE exponentiation convention/probe surface. |
| 2.16 | SKIP | SKIP-MACHINE-SPECIFIC | Source explicitly says the results are not specified by IEEE and asks for an available environment. The local underdetermination/probe artifacts document this without promoting environment output to theorem status. |
| 2.17 | FORMALIZE_CORE | CORE-THEORETICAL-EXERCISE | Closed by `problem2_17_two_mul_maxFiniteMagnitude_finiteOverflowRange` plus existing IEEE overflow-mode result predicates. |
| 2.18 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Closed by `Problem2_18.lean` base-10 counterexample. |
| 2.19 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Closed by the finite exact-rounding theorem `finiteRoundToEvenOp_eq_exact_of_finiteSystem`, the finite-underflow classifiers, and concrete subnormal-lattice exact branches such as `finiteRoundToEvenOp_add_subnormalSystem_eq_exact` and `finiteRoundToEvenOp_sub_sameSign_subnormal_eq_exact`. |
| 2.20 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Closed by `Problem2_19.lean` in local naming: square-root identity and counterexample theorem surface. |
| 2.21 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Closed by `Problem2_20.lean` norm-ratio/counterexample surface. |
| 2.22 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Closed by `Problem2_21.lean` NaN/max-code surface. |
| 2.23 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Closed by `Problem2_22.lean` and `Heron.lean` model-level Kahan-Heron area theorem surface. |
| 2.24 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Closed by `Problem2_23.lean` guard/no-guard `(x+x)-x` results. |
| 2.25 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Closed by `Problem2_24.lean` Kahan nonzero expression theorem surface. |
| 2.26 | FORMALIZE_CORE | CORE-THEORETICAL-EXERCISE | Closed by the new FMA product decomposition theorems in `FusedMultiplyAdd.lean`. |
| 2.27 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Closed by `Problem2_25.lean` determinant/FMA high-relative-accuracy surface. |
| 2.28 | REUSE_EXISTING | CORE-THEORETICAL-EXERCISE | Closed by `Problem2_27.lean` convergence-test theorem surface; local filename numbering drifts from the source label. |

## Empirical source outputs

| Source location | Printed claim/output | Missing machine details | Precise subclaim/replacement theorem | Status |
|---|---|---|---|---|
| Problem 2.10 | "Test the theorem on your computer." | Hardware, compiler/runtime, exact program, rounding state, extended registers/FMA behavior, decimal I/O, and output format. | Kahan theorem infrastructure and local reproducibility experiment are advisory. | SKIP-EMPIRICAL, non-gating. |
| Problem 2.11 | Leading-digit data from powers/factorials/random matrices/tables/newspapers. | Data source, random law/seed, matrix generation details, data extraction, and output summaries. | `LeadingDigitDistribution.lean` gives exact distribution infrastructure for the mathematical phenomenon. | SKIP-EMPIRICAL, non-gating. |
| Problem 2.14 | Test `|3*(4/3-1)-1|` against `u` on available machines. | Machine arithmetic, compiler/runtime, operation order, rounding mode, extended precision, decimal conversion, and printed output. | Local finite single/double theorem surfaces model fixed abstract formats. | SKIP-EMPIRICAL, non-gating. |
| Problem 2.16 | Evaluate IEEE-environment expressions whose results are not IEEE-specified. | Language/library semantics, libm version, environment, exception/trap settings, NaN/sign conventions, and formatting. | Local underdetermination/probe artifacts keep the machine-specific nature explicit. | SKIP-MACHINE-SPECIFIC, non-gating. |

## Open selected-scope items

None for Chapter 2 core mode after this pass. Remaining non-core work is deliberately outside the selected gate: full executable IEEE instruction semantics, traps, signaling-NaN/payload behavior, complete hardware/environment behavior for elementary functions and exponentiation, and historical machine outputs.

## Hidden-hypothesis and weak-component summary

- The inclusive Ferguson and Sterbenz closures are weak components because endpoint strictness previously mismatched the source. The new source-shaped predicates match the PDF inequalities and route to existing finite exactness theorems.
- Problem 2.17 is weak because repository filenames used an older numbering convention. The source-facing `2*xmax` theorem is now named and documented separately.
- Problems 2.10, 2.11, 2.14, and 2.16 are empirical or machine-specific by the skill policy. They remain visible here and are not counted as unproved mathematical theorems.
- Problem 2.19 is closed at the mathematical floating-point-format layer, not as a total hardware-emulation theorem. This matches the chapter's gradual-underflow argument and leaves traps/special-value instruction semantics out of core scope.

## Verification

- `lake env lean LeanFpAnalysis/FP/Analysis/FloatingPointArithmetic.lean`: PASS.
- `lake env lean LeanFpAnalysis/FP/Analysis/FusedMultiplyAdd.lean`: PASS.
- `lake build`: PASS, 3471 jobs. The QR/FastMatMul linter warnings are pre-existing baseline warnings, not introduced by the Chapter 2 edits.
- `lake env lean examples/LibraryLookup.lean`: PASS; this prints the full lookup index.
- `git diff --check`: PASS.
- Lean-source placeholder scan, `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis Main.lean examples`: PASS with no matches. A broader README/report scan only found ordinary prose occurrences.
- `#print axioms` for `fergusonExponentConditionLe`, `finiteRoundToEvenOp_sub_eq_exact_of_fergusonConditionLe`, `sterbenzRatioConditionLe`, `finiteRoundToEvenOp_sub_finiteSystem_eq_exact_of_sterbenzRatioConditionLe`, `problem2_17_two_mul_maxFiniteMagnitude_finiteOverflowRange`, and `finiteRoundToEvenFMA_product_expansion_with_rounded_product`: only standard Mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Documentation

- Inventory/report path: `chapter_splitting/reports/split1_ch02_core_audit.md`.
- No separate proof-source or bottleneck ledger was triggered for Chapter 2 core mode.
- No theorem PDF was generated for this chapter pass.
