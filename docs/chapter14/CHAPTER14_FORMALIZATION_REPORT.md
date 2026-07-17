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
- Selected-scope gate: **OPEN / FAIL**

The corrected completion audit contains 82 rows: 71 selected and 11
intentionally excluded.  Of the selected rows, 68 pass, two retain explicit
source corrections, and one remains open.  The earlier 78-row audit incorrectly
collapsed the precise p. 278 Schulz claims into a single literature exclusion.

## Progress Snapshot

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| 14 | core completion audit | 100 | 99 | 98 | 99 | 100 | 95 | 1 | Spectral-2-norm Schulz initializer convergence and rectangular pseudoinverse clause | medium |

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
| Schulz algebra on p. 278 | `Ch14SchulzIteration.lean` | Both printed step forms, left/right residual squaring, `E_k=E_0^(2^k)`, the printed transpose initializer, Moore--Penrose support/error identities, and square convergence under the stronger sufficient condition `‖I-AX_0‖∞<1` |
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
| `Ch14SchulzIteration.lean` | Correct the false whole-row deferral of the p. 278 parallel-inversion section | Schulz step and residual identities; partial convergence support | PARTIAL: PRINTED INITIALIZER CONVERGENCE OPEN |

## External Proof Sources

| Claim/source | Role | Local status |
|---|---|---|
| Higham Chapter 14 and Appendix A | Primary statements and proof routes | Adopted steps proved locally |
| Higham Chapters 3, 8, 9, 13 | Book-cited dependencies | Existing repository declarations reused |
| Oracle session `ch14-schulz-initialize`, GPT-5.5 Pro | Audited the exact spectral initializer, rank assumptions, and rectangular nullspace obstruction | Partly adopted after local proof: support invariance and `Aplus-X_k=(I-X_kA)Aplus`.  Native transcript completed; the separate stable-header harvester failed operationally, as recorded in the proof-source ledger. |

See `CHAPTER14_PROOF_SOURCE_LEDGER.md` for the full trust record.

## Skipped And Empirical Items

| Source items | Classification | Reason |
|---|---|---|
| Table 14.1, Figure 14.1, Table 14.2, Tables 14.3-14.5, Table 14.6 | SKIP-EMPIRICAL | Historical or MATLAB output without a unique machine execution |
| Schulz slow-start estimate | SKIP-QUALITATIVE | Informal `delta << 1`, approximate count, and no unique quadratic-regime threshold |
| Csanky/parallel-complexity and stability discussion | SKIP-LITERATURE-REVIEW | Citation, complexity comparison, and qualitative finite-precision observations |
| Section 14.7 notes | SKIP-LITERATURE-REVIEW | Bibliographic notes |
| Problems 14.1, 14.6, 14.9 | OPTIONAL-PROBLEM-NOT-SELECTED | Optional core exclusions; Problem 14.1 is reflective prose |

The mathematical Method 2B instability phenomenon and the abstract fast-operation analysis from Problem 14.2 were separated from empirical outputs and formalized.

## Selected-Scope Result

The gate is open.  Of the 82 source rows, 68 are `PASS`, two are
`SOURCE-ERROR/CORRECTED`, one is `PARTIAL / OPEN`, and eleven are intentional
exclusions.  The remaining selected obligation is the source's p. 278
convergence claim for `X_0=alpha A^T` under
`0<alpha<2/||A||_2^2`, including an honest disposition of the rectangular
pseudoinverse clause.  The new infinity-norm contraction theorem is useful but
is strictly stronger and is not counted as that closure.

The generic helper in `Ch14GJEPrintedEnvelopeClosure.lean` was not accepted as the final source closure because its older family contract did not encode the masked Algorithm 14.4 trace and carried an `Xabs = O(1)` premise. The accepted endpoint is the source-active theorem in `Ch14GJETheorem145SourceClosure.lean`, where the required boundedness is derived from the finite stages.

The first Corollary 14.6 candidate likewise depended on the older unmasked recurrence. The final reconciliation rejected that overclaim, and `Ch14Corollary146SourceClosure.lean` now derives the same printed SPD constants directly from `ch14ext_gjeSourceTrace`.

## Hidden-Hypothesis Summary

| Hypothesis class | Examples | Audit result |
|---|---|---|
| Source assumptions | nonsingularity, SPD, row diagonal dominance, (13.4)/(13.5) operation models | Preserved explicitly |
| Domain assumptions | positive dimension, nonzero denominators, positive exact solution norm | Mathematically necessary and visible |
| FP/model validity | `gammaValid`, successful nonzero/positive pivots, small operation budget | Visible operational/model guards; no error conclusion is assumed |
| Uniform asymptotic regularity | source-level `O(1)` inputs and Chapter 9 perturbation contracts | Used to make Landau constants independent of precision index.  Theorem 14.5 derives its finite-stage `Pabs`, `Q`, and `Xabs` bounds.  `Ch14Cor147SourceFamily` instead exposes `P_abs_isBigO_one` and `X_abs_isBigO_one` as explicit fields; factor and inverse proximity are derived. |
| Suspicious proof artifacts | rounded dominance, final residual/forward bounds, `x_hat=x+O(u)` | None is assumed; factor/inverse proximity, forward bootstrap, and ratio absorption are proved locally |

For the p. 278 initializer, no full-row-rank or full-column-rank hypothesis is
mathematically required.  The printed quotient tacitly excludes `A=0`; with
Lean's total real division, its two strict inequalities are simply
inconsistent when `opNorm2 A=0`.  A future denominator-free general endpoint
can instead use `0<alpha` and `alpha*(opNorm2 A)^2<2`, which includes the
trivial zero-matrix case without a hidden rank premise.

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
| p. 278 Schulz section | Rendered-source reinspection, standalone build, and Moore--Penrose certificate audit | Exact step/residual/support identities checked; theorem types compared with the printed spectral initializer criterion | PARTIAL / OPEN |
| Source corrections | Rendered-page inspection | Checked Lean witnesses | PASS |

## Source Corrections

1. The Section 14.6 signed ratio `det(D)/det(A)` is incompatible with the asserted nonnegative Hadamard condition number. The formal primary definition uses `|det(A)|`; the signed form and negative witness remain explicit.
2. Problem 14.15's printed `<1` guard does not ensure positivity of `1-nx`. The final theorem uses the necessary `<1/n` guard and includes a checked `n=2`, `x=3/4` witness against the printed shape.

## Verification

Completed for this audit/fix batch:

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
lake build LeanFpAnalysis.FP.Algorithms.Ch14SchulzIteration
lake build
lake env lean /tmp/ch14_primary_axioms.lean
lake env lean /tmp/ch14_schulz_axioms.lean
git diff --check
placeholder and conflict scans
```

Results: the seven primary source modules passed together (3083 jobs), the
focused Schulz module passed (2537 jobs), the final Algorithms umbrella passed
(4268 jobs), and the final full project build passed (4319 jobs).  The focused
Chapter 14 lookup and `#print axioms` files pass.  The audited primary and
Schulz declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`.  Changed Chapter 14 files have no placeholders or conflict
markers; warnings shown by the builds are pre-existing deprecation/linter
warnings.

The repository-wide `examples/LibraryLookup.lean` is not reported as a pass:
Lean aborts with a stack overflow (exit 134) after printing thousands of
pre-existing checks, both with a 64 MiB stack and with an unlimited process
stack.  The Chapter 14 additions occur later in that oversized file, so the
focused import/check/axiom audit above is the reliable lookup evidence for this
batch.  This harness limitation does not change the selected-scope gate, which
remains open for the mathematical convergence obligation stated above.

## Documentation

- Inventory: `docs/chapter14/CHAPTER14_SOURCE_INVENTORY.md`
- Not-proved ledger: `docs/chapter14/CHAPTER14_NOT_PROVED_LEDGER.md`
- Proof-source ledger: `docs/chapter14/CHAPTER14_PROOF_SOURCE_LEDGER.md`
- These four audit documents are versioned; the local skill, `References/`, and temporary audit/render artifacts under `tmp/` remain excluded from the repository push.
