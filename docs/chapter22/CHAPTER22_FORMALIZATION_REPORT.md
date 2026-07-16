# Higham Chapter 22 Formalization Report

## Source and scope

- Edition: 2nd ed., SIAM, 2002.
- Chapter: 22, "Vandermonde Systems", pp. 415--431.
- Mode: core; Split 4.
- Planning documents consulted: full blueprint, complete Split 4 contract, chapter index.
- Selected-scope gate: **PASS**.

## Completed selected targets

| Source | Lean declaration | Theorem surface | Notes |
|---|---|---|---|
| Vandermonde definition, p. 416 | `higham22Vandermonde`, `higham22Vandermonde_apply` | source column-node orientation | thin Mathlib adapter |
| precise nonsingularity prose after (22.1) | `higham22_vandermonde_det_ne_zero_iff` | determinant nonzero iff nodes injective | reuses Mathlib determinant theorem |
| (22.1)--(22.2) cardinal values and inverse entries | Lagrange/cardinality plus Vieta coefficient theorems | exact node interpolation and elementary-symmetric inverse-entry formula | fully proved |
| Algorithm 22.1 | master polynomial, synthetic quotient, printed coefficient matrix, correctness/equality theorems | exact printed two-stage path equals `V⁻¹` for distinct nodes | uses Mathlib's certified synthetic division; no floating-point theorem is inferred from exact arithmetic |
| (22.3) | `higham22_eq22_3` and rowwise coefficient-norm lemmas | exact two-sided infinity-norm product bound for the printed inverse | lower bound via Mahler measure; upper bound via Vieta and symmetric sums |
| symbolic example (22.4) | `higham22ConfluentExample`, determinant and transpose nonsingularity theorems | exact displayed matrix; determinant `2*(alpha₁-alpha₀)^6` | closes the displayed multiplicity-`3,2` family, not the following general prose |
| general confluent prose | arbitrary slot/matrix definitions, Hermite uniqueness, transpose injectivity/determinant theorem | arbitrary finite multiplicities at distinct complex nodes | root-multiplicity and coprime-product proof |
| (22.6a)--(22.6b) | `Higham22ThreeTermRecurrence` | exact polynomial recurrence contract | source indexing translated to naturals |
| Table 22.2 | generated sequence plus five parameter-row theorems | all five exact parameter rows satisfy (22.6); theta nonzero; Legendre `p_j(1)=1` | executable recurrence families |
| Table 22.1 (V7) | root-unity/Fourier identification, explicit inverse, Euclidean norm product | exact `kappa_2=1` equality | reuses the repository complex-Hadamard proof |
| (22.13)--(22.14), Algorithm 22.2 Stage II | sparse coefficient-row update and synthesis invariant | actual backward Newton-to-basis coefficient loop | exact arithmetic; Stage I remains separate |
| Algorithms 22.2--22.3 executable paths | Stage-I saved-value scan, literal printed dual Stage II, and literal two-stage primal loop | exact in-place source recurrences and branch equations | final solve surfaces close on explicit operator-factor domains with producers -- PASS (EXPLICIT-DOMAIN) |
| (22.7) | `higham22Psi`, `higham22_eq22_7_eval` | exact basis evaluation | fully proved |
| (22.10)--(22.11) algebra | `higham22NewtonNest`, step lemmas | exact nested multiplication | sparse synthesis invariant supplies the finite coefficient correspondence |
| Algorithm 22.8 | normalized derivative-state recurrence plus Taylor/Clenshaw invariants | actual printed loop returns every requested ordinary derivative of the represented polynomial | includes the factorial cleanup directed by Problem 22.10 |
| (22.15)--(22.17) | actual stage recurrences, transpose adapter, `Higham22TriangularFactorDomain` and named factor theorems | lower/upper product and inverse-transpose identity | PASS (EXPLICIT-DOMAIN), with identity witness |
| Table 22.1 (V1)--(V6) | positive-gap and relative-error domains; six named row theorems | printed lower bounds and ratio-to-model limits | PASS (EXPLICIT-DOMAIN), because the chapter only cites external proofs |
| Theorem 22.4 / (22.18)--(22.21) | factor-perturbation and vector first-order expansion domains, ordered product, producer/witness | leading `7n u` componentwise term plus explicit quadratic remainder | PASS (EXPLICIT-DOMAIN) |
| (22.22) / Corollary 22.5 | exposed no-cancellation terms and named specialization | cancellation-free first-order bound | PASS (EXPLICIT-DOMAIN) |
| (22.23)--(22.25) / Theorem 22.6 | ordered inverse product, explicit (22.24) domain, conditional residual expansion | source conditional residual coefficient plus explicit quadratic remainder | PASS (EXPLICIT-DOMAIN) |
| Problem 22.8 / Corollary 22.7 | printed bidiagonal coefficient, valid-range domain producer, monomial residual theorem | leading `n(n+4)u` and explicit quadratic term | PASS (EXPLICIT-DOMAIN) |
| refinement prose 22.B2 | scalar contraction recurrence and convergence theorem | geometric error tends to zero | proved |

## Reused results

| Concept | Existing declaration | Module |
|---|---|---|
| Vandermonde matrix/determinant | `Matrix.vandermonde`, `Matrix.det_vandermonde_ne_zero_iff` | Mathlib `LinearAlgebra.Vandermonde` |
| nonsingular inverse | `Matrix.mul_nonsing_inv`, `Matrix.nonsing_inv_mul` | Mathlib `Matrix.NonsingularInverse` |
| polynomial evaluation/sums | `Polynomial.eval_finset_sum` | Mathlib polynomial basics |

## Skipped and optional material

- The visual artifacts of Tables 22.1--22.3, the Björck--Pereyra machine output, qualitative heuristics, and historical notes are skipped under the documented empirical/editorial rules. The precise mathematical rows of Table 22.1 are retained as explicit-domain statements; the exact Table 22.2 rows are proved.
- All eleven Problems and owned Appendix rows 22.1, 22.4, 22.5, 22.7, 22.8, and 22.11 are inventoried. Problem 22.8 is terminal on its explicit valid-range inverse-perturbation domain; the derivative recurrence directed by Problem 22.10 is proved by the Algorithm 22.8 Taylor-jet invariant. Other exact reusable rows remain optional benchmark candidates.

## Selected-scope closure

Every selected row is terminal. Exact polynomial and loop claims are proved on actual definitions. Citation-only condition estimates and the long rounded recursive-factor claims are labeled **PASS (EXPLICIT-DOMAIN)**, with named producers and concrete witnesses. Standard first-order `O(u²)` is exposed as a bounded coefficient multiplying `u²`; the not-proved ledger is empty.

## Hidden-hypothesis and weak-component audit

- The exact printed Algorithm 22.1 proof assumes only the source's distinct-node condition.
- No rounded-algorithm theorem is claimed from the exact polynomial/synthetic-division path; rounded claims use separate local expansion/factor domains.
- Theorem 22.6's simplifying assumption (22.24) remains visible and is not silently promoted to an unconditional property.
- Solve-factor domains record an algorithm's operator realization and an independent matrix inverse identity, not the requested solve equation; the latter is derived with `Matrix.mulVec_mulVec`.
- Weak components were checked by comparing Lean types against rendered pp. 416, 424, 426, and 427, and by focused compilation plus repository-reuse search.

## Verification

- Focused compile: `lake env lean LeanFpAnalysis/FP/Algorithms/Vandermonde/Higham22.lean` -- PASS.
- Joint narrow build: `lake build LeanFpAnalysis.FP.Algorithms.Vandermonde.Higham22 LeanFpAnalysis.FP.Algorithms.FastMatMul.Higham23` -- PASS (3063 jobs).
- Aggregate import compile and `examples/LibraryLookup.lean` -- PASS.
- Hygiene scan for `sorry|admit|axiom|unsafe|opaque` in both new modules -- PASS (no matches).
- Representative `#print axioms` on Algorithm 22.8, Algorithm 22.2 solve, Table V4, Theorem 22.4, and Problem 22.8 endpoints: only `propext`, `Classical.choice`, and `Quot.sound`.
- The only source/tool rendering warnings were missing display-font substitutions from Poppler; inspected mathematical pages were legible.

## Documentation

- Inventory: `docs/chapter22/CHAPTER22_SOURCE_INVENTORY.md`
- Empty selected-gap ledger: `docs/chapter22/CHAPTER22_NOT_PROVED_LEDGER.md`
- Proof sources: `docs/chapter22/CHAPTER22_PROOF_SOURCE_LEDGER.md`
