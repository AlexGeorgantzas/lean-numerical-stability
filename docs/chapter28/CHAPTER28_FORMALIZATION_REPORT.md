# Higham Chapter 28 Formalization Report

## Source and scope

- Edition: 2nd ed., SIAM, 2002.
- Chapter: 28, "A Gallery of Test Matrices", printed pp. 511-526.
- Source file: `References/1.9780898718027.ch28.pdf`.
- Mode / split: core / Split 4.
- Planning documents: full blueprint, Split 4 contract, chapter index.
- Selected-scope gate: **FAIL** because the selected Hilbert/Pascal
  asymptotic and total-positivity rows, the p. 515 Cauchy formulas, the p. 517
  random-matrix probability producers and normalized-Haar conclusion, the
  p. 517-518 prescribed-spectrum, rank-2, and symmetric randsvd endpoints, and
  the remaining p. 522-523 Toeplitz/companion endpoints are open.

## Compiled coverage

| Source | Lean declaration | Honest status |
|---|---|---|
| Hilbert/Cauchy definitions | `hilbertMatrix`, `cauchyMatrix`, transpose theorems | VERIFIED definitions and symmetry/swap laws |
| (28.1)-(28.4) | `hilbertMatrix_eq_choleskyGram`, `hilbert_det_formula`, `factorInverseGram_eq_hilbertInverseFormula`, `hilbert_inverse_formula`, `hilbertCholeskyFactor_mul_inverse` | GENERICALLY VERIFIED, including both-sided printed inverse and exact determinant |
| Hilbert definiteness/total positivity | `hilbertMatrix_isSymPosDef_explicit`; Cauchy formula positivity precursor | SPD VERIFIED; total positivity OPEN pending the general ordered-minor determinant formula |
| Cauchy formulas | exact candidates, `CauchyAdmissible`, nonzero factor/entry lemmas, source-shaped L/U and `cauchy_firstPivot_schur_entry` | PARTIAL; general determinant, inverse, LU, inverse-entry sum, and total positivity OPEN |
| Randsvd definition/schedules | `rectangularDiagonal`, `randsvdMatrix`, four singular-value schedules, `randsvdMatrix_transpose_mul_self`, `stewartRandsvdMatrix` | VERIFIED definitions and samplewise Gram algebra; PARTIAL/OPEN for the prescribed singular-value multiset and `alpha = kappa_2(A)`, the single-Householder rank-2 decomposition, and the symmetric prescribed-eigenvalue adaptation; exact Haar laws of the paired factors also depend on the open Theorem 28.1 endpoint |
| Theorem 28.1 | `stewartGaussianInputMeasure`, exact local reduction, embedded Householder/sign/product producer, `stewartOrthogonalGroupOutput`, `stewartOrthogonalGroupLaw`, `StewartTheorem28_1HaarConclusion` | PARTIAL/OPEN: input normalization, reduction, every-sample orthogonality, producer measurability, and push-forward normalization are VERIFIED; the Gaussian push-forward Haar/left-invariance theorem is not proved |
| Pascal | explicit SPD quadratic form, factorization, determinant, involution, inverse, Cohen entries, `signedPascal_conj_pascalMatrix`, `pascal_reciprocal_eigenpair`, final-entry kernel, rotated cube identity | finite SPD/algebra, the all-orders singular perturbation, `T³=I`, and the central-binomial/factorial-ratio Stirling endpoints are VERIFIED; the general moment/contour representation and characteristic-polynomial palindromicity are OPEN, the literal first condition-number `~` is a source-notation discrepancy, and a faithful rough-order theorem, optimal perturbation norm, total positivity, and eigenvector sign changes remain OPEN |
| Toeplitz | definition/transpose/Green inverse plus direct sine eigenpairs and normalized DST diagonalization | Green inverse and the full symmetric-family spectrum VERIFIED; general `T_n(c,d,e)` spectrum and the second-difference operator-norm/asymptotic endpoint PARTIAL/OPEN; LU/cyclic-reduction convergence prose is DEFERRED as underspecified |
| Companion | eigenvector, exact target-polynomial coefficients, explicit all-order left Krylov basis, unit-determinant scalar-shift minor/rank bound, and direct Gram identity | eigenvector/Krylov/rank-form nonderogatory/Gram algebra VERIFIED; characteristic polynomial, `compan(poly(A))` eigenvalue preservation, similarity transport, and `2≤n` singular-value formulas remain PARTIAL/OPEN. The printed complex normality iff is a SOURCE DISCREPANCY; its repaired `n≥2`, `|a_0|=1` form is open. |
| Probability rows | normalized product laws, multiplicity-correct real-root count, event surfaces, conditional Ginibre/Perron transfers, and Stewart's exact orthogonal-group push-forward surface | PARTIAL/OPEN: root-count measurability/integrability, the finite Ginibre expectation/asymptotic, the uniform boundary-null/Perron producer, and Stewart left-invariance/Haar proof are absent |
| Asymptotic rows | exact proposition surfaces plus unconditional Pascal Stirling theorems | PARTIAL/OPEN: only the central-binomial and factorial-ratio Stirling endpoints are closed; the literal Hilbert determinant and first Pascal condition-number ratio readings are too strong, faithful log/rough-order theorems remain open, and rounded `3.5` is not strict ratio equivalence |

## External-domain status

The p.515 Cauchy subgroup is an active selected-scope bottleneck. The removed
determinant, inverse, LU, inverse-entry-sum, and total-positivity transfers
required the missing rational/minor identity as a premise and used order-one
examples as nonvacuity evidence. The repaired module instead proves
source-only regularity and algebraic precursors. A general finite Cauchy
determinant/partial-fraction or Schur-complement induction is still required.
The Stewart subgroup is a second active bottleneck.  Its exact normalized
product-Gaussian input, source-ordered Householder/sign sample path, exact
local reduction, measurable orthogonal-group-valued output, and normalized
push-forward law are now concrete.  A genuine Gaussian/Householder argument
that this push-forward is left invariant (hence Haar) is still required.
For randsvd itself, the exact Gram identity does not yet supply the printed
singular-value multiset or `alpha = kappa_2(A)` conclusion. The
single-Householder diagonal-plus-rank-2 warning and the symmetric
`Q Lambda Q^T` prescribed-eigenvalue construction are also open; the printed
operation-count comparison is terminal deferred because no exact cost model
is selected.
The Toeplitz/companion re-audit removed transfer lemmas that assumed the
missing component, coefficient, cyclicity, or low-rank conclusion.  Direct
trigonometric recurrence and Chapter 9 sine orthogonality now prove the full
symmetric Toeplitz diagonalization; an explicit transpose Krylov basis and an
unit-determinant shift minor, and an entrywise `CᴴC` computation provide
genuine companion results. The general
nonsymmetric Toeplitz square-root spectrum, condition-number norm/asymptotic
bridge, companion determinant recurrence, and Gram-spectrum/SVD calculation
remain open.

The probability re-audit keeps the normalized real-Ginibre and uniform
product laws, corrects `realEigenvalueCount` to count algebraic multiplicity,
and retains useful conditional transfers, but does not count missing
measurability/integrability or their assumed finite expectation, limit,
boundary-null, or Perron premises as closure. The
Pascal re-audit replaces the former cube-root transfer with the genuine
all-orders identity `pascalIdentityCubeRootCandidate_cube`, and proves the two
Stirling endpoints unconditionally. The page's own Pascal norm bound rules out
a literal ratio-one reading of its first condition-number `~`; a faithful
constant-factor or log-rate theorem, the optimal perturbation norm, total
positivity, and sign-change theorem remain open. The Hilbert determinant
shorthand likewise still needs a log-scale formulation because its literal
ratio-equivalence interpretation is too strong.

Equations (28.5)-(28.11) remain terminal
`DEFER-MISSING-PRECISE-STATEMENT` because the source writes `approx` without
choosing a convergence mode, error term, or event. The qualitative
GE/Cholesky stability prose and LU-diagonal/cyclic-reduction convergence prose
are also accounted for as terminal deferred rows, and Table 28.1 is explicitly
excluded as a software catalogue. Problems 28.1-28.2 are optional and not
selected.

## Hidden-hypothesis and weak-component audit

- `higham28_theorem28_1_product_orthogonal` assumes only that the sign matrix
  and embedded factors are orthogonal.
- `stewartOrthogonalMatrix_orthogonal` supplies those premises from the actual
  Gaussian-tail sample-path construction rather than an arbitrary list.
- `stewartLaw_isNormalizedOrthogonalHaarLaw` only constructs an ambient
  compatibility predicate from assumed normalization, support, and left
  invariance. It does not prove those fields for `stewartOrthogonalGroupLaw`
  or discharge Mathlib's exact `Measure.IsHaarMeasure` endpoint.
- `diracIdentity_isNormalizedOrthogonalHaarLaw_zero` concerns a singleton
  ambient matrix space, not the printed general-order Gaussian producer.
- Formula candidates for (28.1)-(28.4) are connected to source claims by
  compiled generic equalities, not hypotheses asserting the target.
- Cauchy inverse/LU/determinant conclusions are not exposed through assumed
  partial-fraction or product-sum propositions. Only source-domain
  admissibility, exact candidates, nonzero denominators, triangularity,
  product positivity, and the first-pivot Schur identity are claimed.
- Pascal similarity, its reciprocal-eigenpair consequence, the final-entry
  kernel, the rotated cube identity, and the two Stirling endpoints are
  unconditional. No theorem assumes the missing spectral/optimality or
  total-positivity conclusions and counts them as closure. The source's moment
  representation and characteristic-polynomial palindromicity are separately
  inventoried as open rather than inferred from those weaker results.
- The Ginibre and uniform/Perron transfer theorems remain explicitly
  conditional; their target-bearing probability premises are open ledger
  dependencies, not completion evidence.
- Toeplitz sine identities and independence are proved directly, not carried
  as hypotheses. The verified diagonalization is explicitly limited to the
  symmetric family `T_n(c,d,c)`.
- Companion cyclicity, the scalar-shift rank bound, and `CᴴC` are genuine
  all-order constructions. The rank-form nonderogatory statement is verified;
  characteristic-polynomial equality, `compan(poly(A))` eigenvalue transport,
  similarity transport, and the `2≤n` singular-value endpoints remain open.
  The printed complex normality iff is false for `a_0=-1` and at `n=1`; a
  repaired `n≥2`, `|a_0|=1` theorem remains open.

## Verification

- The seven-module Chapter 28 focused build (`Higham28`, `Higham28Exact`,
  `Higham28Stewart`, `Higham28Probability`, `Higham28Asymptotics`,
  `Higham28Pascal`, and `Higham28Contracts`) passed all 3,138 jobs.
- `lake build LeanFpAnalysis.FP.Algorithms` passed all 4,036 jobs, and the full
  repository `lake build` passed all 4,087 jobs.
- `lake env lean examples/LibraryLookup.lean` compiled successfully with the
  new Pascal, Stewart, Toeplitz, companion, and Chapter 24 entry points.
- Representative `#print axioms` checks on Pascal SPD/cube, Stewart
  orthogonality, Toeplitz diagonalization, companion rank, and the other Split 4
  chapter endpoints report only `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden-token, merge-marker, deleted-transfer-name, import/lookup,
  stale-gate, and `git diff --check` scans passed; the diff check emitted only
  line-ending notices.
- Chapter selected-scope gate: **FAIL**.

## Documentation

- Inventory: `docs/chapter28/CHAPTER28_SOURCE_INVENTORY.md`
- Terminal explicit-domain register: `docs/chapter28/CHAPTER28_NOT_PROVED_LEDGER.md`
- Proof-source ledger: `docs/chapter28/CHAPTER28_PROOF_SOURCE_LEDGER.md`
- Bottleneck ledger: `docs/chapter28/CHAPTER28_BOTTLENECK_LEDGER.md`
