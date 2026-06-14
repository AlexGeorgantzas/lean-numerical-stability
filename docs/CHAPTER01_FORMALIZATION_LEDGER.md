# Chapter01.pdf Formalization Ledger

Source: `references/Chapter01.pdf`

Audit date: 2026-06-11

Scope note: the local PDF has 6 pages and ends at the opening of Higham
Chapter 1, Section 1.3.  It is not the full printed Chapter 1 through Section
1.19.  This ledger audits the exact local PDF file, not later Chapter 1 pages
that are absent from the repository copy.

Extraction and inspection:

- `pdfinfo references/Chapter01.pdf` reported 6 pages.
- `pdftotext -layout` and per-page `pdftotext` were used for text.
- Rendered pages 3--6 were inspected because `pdftotext` drops several
  displayed formulas.

## Closure Summary

Status: PASS for the formalizable mathematical content in the local six-page
excerpt.

The existing repository already contained the base scalar error definitions.
This audit found and closed the following gaps:

- Higham equation (1.1) was exposed only through the per-operation `FPModel`
  fields; it now has a unified primitive-operation wrapper.
- The signed relative-error equivalence was not stated as a theorem.
- The scale-invariance of relative error was not stated as a theorem.
- The normwise vector relative-error convention was not named.
- The componentwise relative error existed only as a bound predicate, not as the
  displayed finite maximum.
- Section 1.3's three source classes were not represented by a local type.

Closed Lean surface:

- `BasicOp`, `BasicOp.exact`, `FPModel.round`, `FPModel.model_basicOp`
- `absError`, `relError`, `relErrorDefined`, `signedRelErrorWitness`
- `absError_nonneg`, `relError_nonneg`, `absError_smul`, `relError_smul`
- `relError_eq_abs_of_signedRelErrorWitness`
- `exists_signedRelErrorWitness_of_relErrorDefined`
- `normwiseRelError`
- `compRelError`, `compRelErrorBounded`
- `relError_le_compRelError`, `compRelError_le_iff`, `compRelError_nonneg`
- `ErrorSource`, `ErrorSource.chapterOneMainSource_exhaustive`

## Page-By-Page Audit

| PDF page | Source content | Formalization status |
|---|---|---|
| 1 | Chapter title and epigraphs. | Prose-only front matter; no theorem obligation. |
| 2 | Book/chapter scope, assumptions, warning about special examples. | Prose-only scope notes; no theorem obligation. |
| 2 | Matrix/vector/scalar naming conventions; real and complex vector spaces; MATLAB-like pseudocode and submatrix notation. | Represented structurally by the repository's `Fin`-indexed vectors/matrices and Mathlib matrix types where used. Naming and pseudocode conventions are documentation, not theorem claims. |
| 3 | Integer range notation. | Documentation-only convention; Lean uses `Fin n`, finite sums, and ranges locally. |
| 3 | Higham equation (1.1): primitive operations `+`, `-`, `*`, `/` satisfy `fl(x op y) = (x op y)(1 + delta)` with `|delta| <= u`. | Closed by `BasicOp`, `BasicOp.exact`, `FPModel.round`, and `FPModel.model_basicOp`; division exposes the nonzero denominator side condition. |
| 3 | Unit roundoff examples and computed-quantity hat convention. | Unit roundoff is represented by `FPModel.u` with `FPModel.u_nonneg`; hat notation is a prose naming convention used in theorem names/comments. |
| 3 | Floor, ceiling, normal-distribution notation, flop-count convention, experimental hardware. | Notation/prose only in this excerpt. Floor/ceiling and asymptotic notation are Mathlib/background concepts, but the excerpt states no theorem using them. |
| 4 | Scalar absolute error `|x - xhat|`. | Closed by `absError`; nonnegativity by `absError_nonneg`. |
| 4 | Scalar relative error `|x - xhat| / |x|`, undefined when `x = 0`. | Closed by `relError` plus the explicit domain predicate `relErrorDefined`. |
| 4 | Equivalent signed relative-error form `xhat = x(1 + rho)` and `E_rel = |rho|`. | Closed by `signedRelErrorWitness`, `relError_eq_abs_of_signedRelErrorWitness`, and `exists_signedRelErrorWitness_of_relErrorDefined`. |
| 4 | Relative error is scale independent under `x -> alpha x` and `xhat -> alpha xhat`. | Closed by `relError_smul`; the proof requires `alpha != 0`, as mathematically necessary. |
| 4--5 | Significant-digit definitions, examples, and anomalies. | Explanatory discussion rather than a stable theorem target. The excerpt itself emphasizes that precise significant-digit definitions are problematic; no local theorem is claimed. |
| 5 | Relative error is the more precise/base-independent measure; approximate answers should state a relative-error estimate or bound. | Closed by the definitions and bound interfaces above; the recommendation is prose. |
| 5 | Normwise vector relative error `||x - xhat|| / ||x||`. | Closed by `normwiseRelError`, parameterized by the chosen norm so downstream files can use Mathlib-native norms or repository compatibility norms. |
| 5 | Common norms `||.||_inf`, `||.||_1`, and `||.||_2`. | Treated as standard norm choices; `normwiseRelError` is norm-parameterized and avoids duplicating local norm definitions in the foundational error file. Existing matrix/vector norm infrastructure is documented in `docs/LIBRARY_LOOKUP.md`. |
| 5 | Componentwise relative error `max_i |x_i - xhat_i| / |x_i|`. | Closed by `compRelError`; each component bound by the maximum is `relError_le_compRelError`; least-bound equivalence is `compRelError_le_iff`; nonnegativity is `compRelError_nonneg`. |
| 5 | Tablemaker's dilemma. | Explanatory aside; no theorem obligation. |
| 5--6 | Three main error sources: rounding, data uncertainty, truncation. | Closed by `ErrorSource` and `ErrorSource.chapterOneMainSource_exhaustive`. |
| 5--6 | Data errors are analyzed by perturbation theory; intermediate rounding errors require method-specific analysis. | Prose-level methodological guidance. Perturbation and method-specific rounding analyses are formalized in later files when invoked by concrete algorithms. |
| 6 | Truncation/discretization discussion, Trefethen quotation, symbolic-manipulation note. | Explanatory prose; no theorem obligation in this excerpt. |

## Hidden-Hypothesis Audit

- Relative error theorem surfaces that match Higham's undefined-at-zero caveat
  carry `relErrorDefined exact`, i.e. `exact != 0`.
- `relError_smul` carries the necessary `alpha != 0` hypothesis.  Without it,
  both exact and computed values can collapse to zero.
- `FPModel.model_basicOp` carries `y != 0` only for division.
- `compRelError` carries `0 < n` because `Finset.sup'` requires a nonempty
  component set.  The older `compRelErrorBounded` predicate remains total for
  all `n`.
- `normwiseRelError` is parameterized by a norm function and does not assert
  norm axioms by itself.  Downstream theorem statements must supply or reuse
  the relevant norm facts.

## Not-Proved Ledger

No open paper-level theorem remains for the local six-page `Chapter01.pdf`
excerpt.

Items deliberately not turned into Lean theorem obligations:

- Epigraphs, historical notes, experimental hardware, and wording conventions.
- Significant-digit examples and tablemaker's dilemma discussion, because the
  source presents them as explanatory illustrations and explicitly notes the
  definitional ambiguity.
- Later Chapter 1 sections referenced by the introduction but absent from the
  local PDF.

## Proof Sources

No external proof source was needed.  All closed results are direct
formalizations of the displayed definitions and elementary consequences in the
local PDF excerpt.

## Validation

Validation commands for this audit:

- `lake env lean LeanFpAnalysis/FP/Model.lean`
- `lake env lean LeanFpAnalysis/FP/Analysis/Error.lean`
- `lake env lean examples/LibraryLookup.lean`
- `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Model.lean LeanFpAnalysis/FP/Analysis/Error.lean examples/LibraryLookup.lean`
- `git diff --check`

