# Higham Chapter 14 Formalization Report

## Source And Scope

- Edition: Nicholas J. Higham, 2nd ed., SIAM, 2002
- Chapter: 14, "Matrix Inversion"
- Printed pages: 259-285
- Source file: `References/1.9780898718027.ch14.pdf`
- Appendix: `References/1.9780898718027.appa.pdf`, Chapter 14 solutions
- Mode: core, plus intentionally selected precise Problems
- Parallel split: 3A
- Planning documents: blueprint, Split 3A contract, chapter index
- Selected-scope gate: **PASS**

The complete source audit contains 78 rows: 68 selected and 10 intentionally excluded. The old 76-row startup inventory omitted empirical Tables 14.1 and 14.6; both are now recorded.

## Completed Selected Targets

| Source group | Main Lean declarations/modules | Theorem surface |
|---|---|---|
| Product-error notation | `Ch14ProductErrorNotation.lean` | Compatible rectangular factors, arbitrary binary parenthesization, exact operation budget, `gamma_p` and explicit `2pu` componentwise bounds |
| Equations (14.1)-(14.7) | `MatrixInversion.lean`, `Ch14ForwardErrorEndpoint.lean`, `Ch14AsymptoticFamilies.lean` | Exact residual/forward identities and genuine vanishing-family `O(u^2)` endpoints |
| Triangular Methods 1, 2, 1B, 2B, 2C | `Ch14Method2Loop.lean`, `Ch14Method1BWhole.lean`, `MatrixInversionMethod2BInstance.lean`, `Ch14Method2CWhole.lean` | Concrete loops and block recursions; Method 2B instability is retained rather than normalized away |
| General inverse Methods A-D | `MatrixInversion.lean`, `Ch14MethodsBC.lean`, `Ch14MethodDProductDischarge.lean` | Doolittle/triangular-operation routes to (14.15)-(14.24), including Method D normwise bound |
| Algorithm 14.4 and (14.25)-(14.30) | `GaussJordanPivoting.lean`, `Ch14GaussJordanSourceClosure.lean`, `Ch14GJESourceAccumulationBridge.lean` | Successful-run correctness, source-active masked recurrences, literal accumulated error sums, and the source (14.29) bridge |
| Theorem 14.5 and (14.31)-(14.33) | `Ch14GaussJordanQConstruction.lean`, `Ch14GJETheorem145SourceClosure.lean` | Exact printed factors/constants, explicit `O(u^2)` remainders, and derived `Pabs`, `Q`, and `Xabs` boundedness under a genuine vanishing family |
| Corollaries 14.6 and 14.7 | `Ch14Corollary146SourceClosure.lean`, `Ch14Corollary147SourceClosure.lean` | Source-active SPD and row-dominant endpoints with the printed constants, explicit `O(u^2)` remainders, and no assumed final residual/forward conclusion |
| Determinant section | `MatrixInversion.lean`, `Ch14HymanDeterminant.lean`, `Ch14SourceCorrections.lean` | GEPP determinant formula, Hyman backward error, scaling invariance, and corrected Hadamard condition-number sign |
| Selected Problems | `MatrixInversion.lean`, `Ch14Problem142Families.lean`, `Ch14AsymptoticFamilies.lean`, `Ch14Problem1413Boundary.lean`, `Chapter14Problem1415Weyl.lean` | Problems 14.2-14.5, 14.7-14.8, and 14.10-14.15, including all positive dimensions for (14.37) |

The exact row-to-declaration map is in `CHAPTER14_SOURCE_INVENTORY.md`.

## Reused From Repository Or Mathlib

| Concept | Reused surface |
|---|---|
| Floating-point operations | `FPModel`, `fl_matMul`, rounded triangular solve operations, `gamma`, `gammaValid` |
| Matrix algebra | finite matrices, exact multiplication, determinants, inverse predicates, vector and matrix norms |
| Factorization analysis | Chapter 8/9 triangular solve and LU backward-error declarations |
| Analysis | Mathlib finite sums, continuity, l2 operator norm, singular values, and asymptotic filters |

## New Dependencies

| Declaration/module | Why needed | Used by | Status |
|---|---|---|---|
| `Ch14ProductErrorNotation.lean` | Literal arbitrary-order rectangular product-error notation | Chapter-wide product-error references | COMPLETE |
| `Ch14AsymptoticFamilies.lean` | Make first-order `O(u^2)` claims genuinely uniform | (14.3), (14.6), (14.7), Problem 14.5 | COMPLETE |
| `Ch14GJEAsymptoticFamilies.lean` | Uniform residual and forward higher-order calculus | Theorem 14.5, (14.31), (14.32), corollaries | COMPLETE |
| `Ch14Problem142Families.lean` | Family forms of (13.4)/(13.5) | Problem 14.2 | COMPLETE |
| `Ch14GJESourceAccumulationBridge.lean` | Connect source-active local recurrences to (14.29) | Algorithm 14.4 / Theorem 14.5 | COMPLETE |
| `Ch14GJETheorem145SourceClosure.lean` | Derive the printed (14.30)-(14.32) family endpoints from the masked trace | Theorem 14.5 | COMPLETE |
| `Ch14Corollary146Closure.lean` | SPD norm, condition-number proximity, bootstrap, and asymptotic helper machinery | Corollary 14.6 | COMPLETE |
| `Ch14Corollary146SourceClosure.lean` | Instantiate the SPD closure on the masked Algorithm 14.4 source trace | Corollary 14.6 | COMPLETE |
| `Ch14Corollary147SourceClosure.lean` | Derive factor/inverse proximity and absorb the forward solution ratio | Corollary 14.7 | COMPLETE |

## External Proof Sources

| Claim/source | Role | Local status |
|---|---|---|
| Higham Chapter 14 and Appendix A | Primary statements and proof routes | Adopted steps proved locally |
| Higham Chapters 3, 8, 9, 13 | Book-cited dependencies | Existing repository declarations reused |
| Oracle / GPT-5.5 Pro attempt | Requested second-model review | Stalled with no substantive output; nothing adopted |

See `CHAPTER14_PROOF_SOURCE_LEDGER.md` for the full trust record.

## Skipped And Empirical Items

| Source items | Classification | Reason |
|---|---|---|
| Table 14.1, Figure 14.1, Table 14.2, Tables 14.3-14.5, Table 14.6 | SKIP-EMPIRICAL | Historical or MATLAB output without a unique machine execution |
| Parallel inversion methods | DEFER-MISSING-PRECISE-STATEMENT | Literature survey and qualitative stability/complexity discussion |
| Section 14.7 notes | SKIP-LITERATURE-REVIEW | Bibliographic notes |
| Problems 14.1, 14.6, 14.9 | OPTIONAL-PROBLEM-NOT-SELECTED | Optional core exclusions; Problem 14.1 is reflective prose |

The mathematical Method 2B instability phenomenon and the abstract fast-operation analysis from Problem 14.2 were separated from empirical outputs and formalized.

## Selected-Scope Result

The gate is closed. Of the 78 source rows, 66 are `PASS`, two are `SOURCE-ERROR/CORRECTED`, and ten are intentional exclusions. No selected theorem remains open.

The generic helper in `Ch14GJEPrintedEnvelopeClosure.lean` was not accepted as the final source closure because its older family contract did not encode the masked Algorithm 14.4 trace and carried an `Xabs = O(1)` premise. The accepted endpoint is the source-active theorem in `Ch14GJETheorem145SourceClosure.lean`, where the required boundedness is derived from the finite stages.

The first Corollary 14.6 candidate likewise depended on the older unmasked recurrence. The final reconciliation rejected that overclaim, and `Ch14Corollary146SourceClosure.lean` now derives the same printed SPD constants directly from `ch14ext_gjeSourceTrace`.

## Hidden-Hypothesis Summary

| Hypothesis class | Examples | Audit result |
|---|---|---|
| Source assumptions | nonsingularity, SPD, row diagonal dominance, (13.4)/(13.5) operation models | Preserved explicitly |
| Domain assumptions | positive dimension, nonzero denominators, positive exact solution norm | Mathematically necessary and visible |
| FP/model validity | `gammaValid`, successful nonzero/positive pivots, small operation budget | Visible operational/model guards; no error conclusion is assumed |
| Uniform asymptotic regularity | source-level `O(1)` inputs and Chapter 9 perturbation contracts | Used only to make Landau constants independent of precision index; GJE `Pabs`, `Q`, and `Xabs` bounds are derived |
| Suspicious proof artifacts | rounded dominance, final residual/forward bounds, `x_hat=x+O(u)` | None is assumed; factor/inverse proximity, forward bootstrap, and ratio absorption are proved locally |

## Weak-Component Audit

| Component | First check | Independent check | Status |
|---|---|---|---|
| Rectangular product error | Standalone build and standard-axiom audit | Source formula/dimension comparison | PASS |
| (14.3), (14.6), (14.7), Problem 14.5 asymptotics | Genuine filter-indexed theorem types | Remainder expansion and source comparison | PASS |
| Methods B-D | Concrete operation path and build | No target-shaped residual hypotheses | PASS |
| Problem 14.2 | Family theorem types and build | Operation contracts compared with (13.4)/(13.5) | PASS |
| Algorithm 14.4 through Theorem 14.5 | Source-active recurrence build | Independent rows 40-53 source/type/axiom audit | PASS |
| Corollary 14.6 | Masked source-trace family theorem and standard-axiom audit | Independent exact-constant, recurrence, proximity, bootstrap, and remainder comparison | PASS |
| Corollary 14.7 | Source-active family theorem and standard-axiom audit | Independent factor-induction, ratio-absorption, and remainder comparison | PASS |
| Source corrections | Rendered-page inspection | Checked Lean witnesses | PASS |

## Source Corrections

1. The Section 14.6 signed ratio `det(D)/det(A)` is incompatible with the asserted nonnegative Hadamard condition number. The formal primary definition uses `|det(A)|`; the signed form and negative witness remain explicit.
2. Problem 14.15's printed `<1` guard does not ensure positivity of `1-nx`. The final theorem uses the necessary `<1/n` guard and includes a checked `n=2`, `x=3/4` witness against the printed shape.

## Verification

Completed at the final gate:

```text
lake build LeanFpAnalysis.FP.Algorithms
lake build LeanFpAnalysis.FP.Algorithms.Ch14ProductErrorNotation
lake build LeanFpAnalysis.FP.Algorithms.Ch14AsymptoticFamilies
lake build LeanFpAnalysis.FP.Algorithms.Ch14GJEAsymptoticFamilies
lake build LeanFpAnalysis.FP.Algorithms.Ch14Problem142Families
lake build LeanFpAnalysis.FP.Algorithms.Ch14GJETheorem145SourceClosure
lake build LeanFpAnalysis.FP.Algorithms.Ch14Corollary146Closure
lake build LeanFpAnalysis.FP.Algorithms.Ch14Corollary146SourceClosure
lake build LeanFpAnalysis.FP.Algorithms.Ch14Corollary147SourceClosure
lake build
lake env lean examples/LibraryLookup.lean
git diff --check
placeholder and conflict scans
headline #print axioms audits
```

Results: all focused, umbrella, full, and lookup builds pass. Changed Chapter 14 files have no placeholders or conflict markers; the three final headline declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. Warnings shown by the builds are pre-existing deprecation/linter warnings.

## Documentation

- Inventory: `docs/chapter14/CHAPTER14_SOURCE_INVENTORY.md`
- Not-proved ledger: `docs/chapter14/CHAPTER14_NOT_PROVED_LEDGER.md`
- Proof-source ledger: `docs/chapter14/CHAPTER14_PROOF_SOURCE_LEDGER.md`
- These four audit documents are versioned; the local skill, `References/`, and temporary audit/render artifacts under `tmp/` remain excluded from the repository push.
