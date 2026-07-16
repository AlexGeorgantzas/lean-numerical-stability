# Higham Chapter 28 Formalization Report

## Source and scope

- Edition: 2nd ed., SIAM, 2002.
- Chapter: 28, "A Gallery of Test Matrices", printed pp. 511-526.
- Source file: `References/1.9780898718027.ch28.pdf`.
- Mode / split: core / Split 4.
- Planning documents: full blueprint, Split 4 contract, chapter index.
- Selected-scope gate: **PASS**.

## Compiled coverage

| Source | Lean declaration | Honest status |
|---|---|---|
| Hilbert/Cauchy definitions | `hilbertMatrix`, `cauchyMatrix`, transpose theorems | VERIFIED definitions and symmetry/swap laws |
| (28.1)-(28.4) | `hilbertMatrix_eq_choleskyGram`, `hilbert_det_formula`, `factorInverseGram_eq_hilbertInverseFormula`, `hilbert_inverse_formula`, `hilbertCholeskyFactor_mul_inverse` | GENERICALLY VERIFIED, including both-sided printed inverse and exact determinant |
| Hilbert definiteness/total positivity | `hilbertMatrix_isSymPosDef_explicit`, `hilbert_isStrictlyTotallyPositive_of_cauchyMinors` | SPD VERIFIED; total positivity PASS (EXPLICIT-DOMAIN) from ordered Cauchy-minor determinants |
| Cauchy formulas | determinant/inverse/LU candidates and `cauchy_*_of_*` transfer family | PASS (EXPLICIT-DOMAIN) from fraction-free, partial-fraction, rational product-sum, barycentric, and ordered-minor identities; order-one producers compiled |
| Randsvd definition/schedules | `rectangularDiagonal`, `randsvdMatrix`, four singular-value schedules | VERIFIED definitions |
| Theorem 28.1 | deterministic product theorem plus `stewartLaw_isNormalizedOrthogonalHaarLaw` | PASS (EXPLICIT-DOMAIN) from normalization, orthogonal support, and measurable-set left invariance; dimension-zero Haar producer compiled |
| Pascal | factorization, determinant, involution, inverse, `signedPascal_conj_pascalMatrix`, `pascal_reciprocal_eigenpair`, perturbation/cube-root transfers | exact algebra and similarity/eigenpair VERIFIED; remaining printed constructions PASS (EXPLICIT-DOMAIN) with order-one producers |
| Toeplitz | definition/transpose/Green inverse plus discrete-sine eigenbasis transfers | inverse VERIFIED; spectrum and condition rows PASS (EXPLICIT-DOMAIN), with an order-one sine producer |
| Companion | eigenvector plus determinant-coefficient, cyclicity, and low-rank Gram transfers | eigenvector VERIFIED; remaining rows PASS (EXPLICIT-DOMAIN), with an order-one cyclic producer |
| Probability rows | standard product laws, mass theorems, root/event surfaces, and Ginibre/Perron/Haar transfers | PASS (EXPLICIT-DOMAIN); finite coefficient, boundary-null/Perron, and invariance premises are explicit and not target-equivalent |
| Asymptotic rows | five exact propositions plus relative-error/remainder transfers | PASS (EXPLICIT-DOMAIN); common transfer has a zero-error nonvacuity producer |

## External-domain status

There is no active selected-scope bottleneck. Citation-dependent mathematics is
represented by explicit-domain transfer theorems rather than new axioms. For
example, the Haar transfer consumes mass/support/left-invariance facts; the
Ginibre transfer consumes an exact finite expectation formula and its limit;
the Cauchy transfers consume fraction-free, partial-fraction, and product-sum
identities; and all condition-number rows consume relative-error estimates.
These are strictly upstream of the printed conclusions, and the modules supply
standard or low-order producers wherever practical.

Equations (28.5)-(28.11) remain terminal
`DEFER-MISSING-PRECISE-STATEMENT` because the source writes `approx` without
choosing a convergence mode, error term, or event. Problems 28.1-28.2 are
optional and not selected.

## Hidden-hypothesis and weak-component audit

- `higham28_theorem28_1_product_orthogonal` assumes only that the sign matrix
  and embedded factors are orthogonal.
- `stewartLaw_isNormalizedOrthogonalHaarLaw` assumes normalization,
  orthogonal support, and left invariance separately; it does not assume a
  predicate named Haar. `diracIdentity_isNormalizedOrthogonalHaarLaw_zero`
  demonstrates nonvacuity.
- Formula candidates for (28.1)-(28.4) are connected to source claims by
  compiled generic equalities, not hypotheses asserting the target.
- Cauchy inverse and LU conclusions consume scalar partial-fraction/product-sum
  identities; asymptotic conclusions consume relative-error or remainder
  estimates; companion conclusions consume coefficient/cyclicity/Gram facts.
- Pascal similarity and its reciprocal-eigenpair consequence are unconditional.

## Verification

- Focused targets: `Higham28`, `Higham28Exact`, `Higham28Probability`,
  `Higham28Asymptotics`, and `Higham28Contracts` - PASS.
- `lake build LeanFpAnalysis.FP.Algorithms` - PASS (`4022/4022` jobs).
- Full `lake build` - PASS (`4073/4073` jobs); only pre-existing
  deprecation/linter warnings replayed.
- `lake env lean examples/LibraryLookup.lean` - PASS with representative
  Contracts/Probability/Asymptotics endpoints.
- Hygiene scan for `sorry`, `admit`, `axiom`, `unsafe`, and `opaque` - PASS.
- Representative `#print axioms` checks report only Mathlib's standard
  `propext`, `Classical.choice`, and `Quot.sound` axioms.
- Chapter selected-scope gate: **PASS**.

## Documentation

- Inventory: `docs/chapter28/CHAPTER28_SOURCE_INVENTORY.md`
- Terminal explicit-domain register: `docs/chapter28/CHAPTER28_NOT_PROVED_LEDGER.md`
- Proof-source ledger: `docs/chapter28/CHAPTER28_PROOF_SOURCE_LEDGER.md`
