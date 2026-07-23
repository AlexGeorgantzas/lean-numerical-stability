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

The complete source audit contains 79 rows: 69 selected and 10 intentionally excluded. The precise Schulz claims on p. 278 are separated from the remaining parallel-inversion survey prose.

## Completed Selected Targets

| Source group | Main Lean declarations/modules | Theorem surface |
|---|---|---|
| Product-error notation | `Ch14ProductErrorNotation.lean` | Compatible rectangular factors, arbitrary binary parenthesization, exact operation budget, `gamma_p` and explicit `2pu` componentwise bounds |
| Equations (14.1)-(14.7) | `MatrixInversion.lean`, `Ch14ForwardErrorEndpoint.lean`, `Ch14AsymptoticFamilies.lean` | Exact residual/forward identities and genuine vanishing-family `O(u^2)` endpoints |
| Triangular Methods 1, 2, 1B, 2B, 2C | `Ch14Method2Loop.lean`, `Ch14Method1BWhole.lean`, `MatrixInversionMethod2BInstance.lean`, `Ch14Method2CWhole.lean` | Concrete loops and block recursions; Method 2B instability is retained rather than normalized away |
| General inverse Methods A-D | `MatrixInversion.lean`, `Ch14MethodsBC.lean`, `Ch14MethodDProductDischarge.lean` | Doolittle/triangular-operation routes to (14.15)-(14.24), including Method D normwise bound |
| Algorithm 14.4 and (14.25)-(14.30) | `GaussJordanPivoting.lean`, `Ch14GaussJordanSourceClosure.lean`, `Ch14GJESourceAccumulationBridge.lean` | Successful-run correctness, source-active masked recurrences, literal accumulated error sums, and the source (14.29) bridge |
| Theorem 14.5 and (14.31)-(14.33) | `Ch14GaussJordanQConstruction.lean`, `Ch14GJEOperationalBridge.lean`, `Ch14GJEFinalDivisionClosure.lean` | Structural finalization and the literal componentwise final divisions construct the actual Algorithm 14.4 output and prove the exact printed envelopes and first-order constants; the PDF's unparameterized `O(u^2)` prose is retained as a terminal deferral |
| Corollaries 14.6 and 14.7 | `Ch14GJEFinalDivisionClosure.lean`, `Ch14Cor146UniformInverseBridge.lean`, `Ch14Cor147FinalDivisionFamilyClosure.lean`, `Ch14Cor147SourceDomainConstructor.lean` | Exact printed constants for the actual final-division output, with the SPD and row-dominant source-domain witnesses constructed rather than postulated; unparameterized source `O(u^2)` prose remains explicitly deferred |
| Section 14.5 Schulz iteration | `Ch14SchulzIteration.lean` | Exact update equivalence; left/right residual squaring; `E_k=E_0^(2^k)`; quadratic/double-exponential residual bounds; residual and inverse convergence; printed `alpha A^T` initialization criterion |
| Determinant section | `MatrixInversion.lean`, `Ch14HymanDeterminant.lean`, `Source/Higham/Chapter14/Discrepancies.lean` | GEPP determinant formula, Hyman backward error, scaling invariance, and corrected Hadamard condition-number sign |
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
| `Ch14GJEOperationalBridge.lean` | Construct output/inverse/solve witnesses and expose the old literal-storage finalization defect | Theorem 14.5 and corollaries | COMPLETE diagnostic bridge; the defect is repaired by structural finalization |
| `Ch14GJEFinalDivisionClosure.lean` | Carry the structurally finalized trace through the literal componentwise final divisions | (14.27), (14.29)-(14.32), Theorem 14.5, Corollary 14.6 | COMPLETE |
| `Ch14Cor146UniformInverseBridge.lean` | Construct and control the scaled upper inverse under the printed SPD policy | Corollary 14.6 | COMPLETE |
| `Ch14Cor147FinalDivisionFamilyClosure.lean`, `Ch14Cor147SourceDomainConstructor.lean` | Close the actual-output row-dominant family and construct its exact-domain witnesses | Corollary 14.7 | COMPLETE |
| `Ch14Corollary146Closure.lean` | SPD norm, condition-number proximity, bootstrap, and asymptotic helper machinery | Corollary 14.6 | COMPLETE |
| `Ch14Corollary146SourceClosure.lean` | Instantiate the SPD closure on the masked Algorithm 14.4 source trace | Corollary 14.6 | COMPLETE |
| `Ch14Corollary147SourceClosure.lean` | Derive factor/inverse proximity and absorb the forward solution ratio | Corollary 14.7 | COMPLETE |
| `Ch14SchulzIteration.lean` | Formalize the determinate mathematical claims in the parallel-inversion paragraph | Section 14.5, p. 278 | COMPLETE |

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
| Remaining parallel inversion prose | DEFER-MISSING-PRECISE-STATEMENT | Csanky/processor/complexity discussion, acceleration suggestions, and qualitative floating-point stability observations; the precise Schulz claims are formalized |
| Section 14.7 notes | SKIP-LITERATURE-REVIEW | Bibliographic notes |
| Problems 14.1, 14.6, 14.9 | OPTIONAL-PROBLEM-NOT-SELECTED | Optional core exclusions; Problem 14.1 is reflective prose |

The mathematical Method 2B instability phenomenon and the abstract fast-operation analysis from Problem 14.2 were separated from empirical outputs and formalized.

## Selected-Scope Result

The strict selected-scope gate is **PASS**. Of the 79 source rows, 66 close at
their determinate source strength, one is a terminal
`DEFER-MISSING-PRECISE-STATEMENT`, two are
`SOURCE-ERROR/CORRECTED`, and ten are intentional exclusions. Every row now
has a terminal classification.

The eight rows formerly blocked by the pre-division trace--(14.27),
(14.29)-(14.32), Theorem 14.5, and Corollaries 14.6-14.7--are closed by the
structural-finalization producer and `Ch14GJEFinalDivisionClosure.lean`, with
the specialized Corollary 14.6 and 14.7 adapters constructing their remaining
source-domain witnesses. Row 48, the qualitative fixed-matrix assertion that
general final diagonal scaling has a "negligible effect", has no quantitative
error budget or asymptotic family in the PDF and is therefore terminally
deferred rather than treated as an open proof obligation.

Likewise, the bare `O(u^2)` phrases attached to Theorem 14.5 and Corollaries
14.6-14.7 are not standalone formal statements: the formalization proves exact
named remainders and proves `O(u^2)` for explicit displayed vanishing-roundoff
families, while recording the book's unparameterized prose as a non-gating
terminal deferral.

## Hidden-Hypothesis Summary

| Hypothesis class | Examples | Audit result |
|---|---|---|
| Source assumptions | nonsingularity, SPD, row diagonal dominance, (13.4)/(13.5) operation models | Preserved explicitly |
| Domain assumptions | positive dimension, nonzero denominators, positive exact solution norm | Mathematically necessary and visible |
| FP/model validity | `gammaValid`, successful nonzero/positive pivots, small operation budget | Visible operational/model guards; no error conclusion is assumed |
| Uniform asymptotic regularity | source-level `O(1)` inputs and Chapter 9 perturbation contracts | The finalized family adapters derive the required inverse/domain regularity from the visible SPD or row-dominance assumptions; no hidden source-domain producer remains |
| Suspicious proof artifacts | old literal-storage rounded-trace finalization | The counterexample correctly rejects the old trace's identity claim; the canonical producer instead writes dead eliminated entries as structural zeros, ends at the actual diagonal, and applies the printed final divisions |

## Weak-Component Audit

| Component | First check | Independent check | Status |
|---|---|---|---|
| Rectangular product error | Standalone build and standard-axiom audit | Source formula/dimension comparison | PASS |
| (14.3), (14.6), (14.7), Problem 14.5 asymptotics | Genuine filter-indexed theorem types | Remainder expansion and source comparison | PASS |
| Methods B-D | Concrete operation path and build | No target-shaped residual hypotheses | PASS |
| Problem 14.2 | Family theorem types and build | Operation contracts compared with (13.4)/(13.5) | PASS |
| Algorithm 14.4 through Theorem 14.5 | Source-active recurrence and literal final-division build | Structural-finalization producer plus actual-output envelope audit | PASS at determinate source strength; unparameterized `O(u^2)` prose terminally deferred |
| Corollary 14.6 | Exact printed constants for the actual final-division output | SPD policy and uniform-inverse constructor audit | PASS at determinate source strength; unparameterized `O(u^2)` prose terminally deferred |
| Corollary 14.7 | Exact printed constants for the actual final-division output | Row-dominance domain constructor and family audit | PASS at determinate source strength; unparameterized `O(u^2)` prose terminally deferred |
| Source corrections | Rendered-page inspection | Checked Lean witnesses | PASS |
| Section 14.5 Schulz iteration | Focused module build | Exact spectral initialization and recurrence audit | PASS |

## Source Corrections

1. The Section 14.6 signed ratio `det(D)/det(A)` is incompatible with the asserted nonnegative Hadamard condition number. The formal primary definition uses `|det(A)|`; the signed form and negative witness remain explicit.
2. Problem 14.15's printed `<1` guard does not ensure positivity of `1-nx`. The final theorem uses the necessary `<1/n` guard and includes a checked `n=2`, `x=3/4` witness against the printed shape.

## Verification

The earlier conditional endpoint batch had passed the following checks before
this fresh producer audit:

```text
lake build NumStability.Algorithms
lake build NumStability.Algorithms.Ch14ProductErrorNotation
lake build NumStability.Algorithms.Ch14AsymptoticFamilies
lake build NumStability.Algorithms.Ch14GJEAsymptoticFamilies
lake build NumStability.Algorithms.Ch14Problem142Families
lake build NumStability.Algorithms.Ch14GJETheorem145SourceClosure
lake build NumStability.Algorithms.Ch14Corollary146Closure
lake build NumStability.Algorithms.Ch14Corollary146SourceClosure
lake build NumStability.Algorithms.Ch14Corollary147SourceClosure
lake build
lake env lean examples/LibraryLookup.lean
git diff --check
placeholder and conflict scans
headline #print axioms audits
```

Those checks first established the conditional analysis and exposed the old
literal-storage trace defect. The later canonical repair additionally checks
the structural-finalization producer, `Ch14GJEFinalDivisionClosure.lean`,
`Ch14Cor146UniformInverseBridge.lean`,
`Ch14Cor147FinalDivisionFamilyClosure.lean`, and
`Ch14Cor147SourceDomainConstructor.lean`. The finalized declarations compile,
and the audited headlines depend only on `propext`, `Classical.choice`, and
`Quot.sound`. The old counterexample remains useful evidence that the repaired
producer was necessary; it is not evidence of a current open gate.

## Documentation

- Inventory: `docs/chapter14/CHAPTER14_SOURCE_INVENTORY.md`
- Not-proved ledger: `docs/chapter14/CHAPTER14_NOT_PROVED_LEDGER.md`
- Proof-source ledger: `docs/chapter14/CHAPTER14_PROOF_SOURCE_LEDGER.md`
- These four audit documents are versioned; the local skill, `References/`, and temporary audit/render artifacts under `tmp/` remain excluded from the repository push.
