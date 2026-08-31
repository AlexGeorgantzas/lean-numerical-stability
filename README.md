# NumStability

NumStability is a Lean 4 library for machine-checked floating-point error
analysis and numerical stability. It develops reusable mathematics for rounding,
summation, matrix computations, perturbation theory, and related numerical
algorithms. It also provides source correspondence with Nicholas J. Higham's
*Accuracy and Stability of Numerical Algorithms* (2nd ed.) and a randomized
numerical linear algebra (RandNLA) case study based on work by Drineas and
Mahoney.

The library contains material from all 28 chapters of Higham. This does not mean
that every sentence in the book has been formalized: the
[source audit](docs/source_coverage/AUDIT_ch01-28_PDF_FIRST_2026-07-21.md)
tracks a selected precise scope and distinguishes source-strength proofs,
checked discrepancies with corrected statements, and claims that the source
does not specify precisely enough to formalize honestly.

## Reorganization acceptance record

Checkpoint C0008 (exact code commit
`897557779a2102aa0e23b0b2f63edeb35b06bc68`) is the current accepted
checkpoint. It accepts milestone M13 with its I01 wave (the reviewed
R0014/R0015 union applied on `main` at
`9fbb1e36bcc85f866893e902cbe206ba468a65b0` under the primary human's recorded
2026-08-30 cutover decision) and is the evidence checkpoint for bounded-phase
completion. Repository-wide completion remains incomplete. Repository
reorganization follows
[`docs/architecture/PROCESS.md`](docs/architecture/PROCESS.md).

The accepted C0007/R09-R10 epoch retains the following checkpoint facts as
immutable history; the current production statistics appear below.
C0005 accepts M04/R04 and M08/R08 at exact integrated code commit
`ad92bbfae62d538f3e52829a269a846688a8e213`. Its generated evidence records
2,818 production modules: 2,685 classified, 133 unclassified, and 0 mixed. M04
and M08 are accepted; M07 became ready and B0010/R07 was delivered from exact
C0005 base code `ad92bbfae62d538f3e52829a269a846688a8e213`. Immutable delivery
`2f55e0aa5687829ca3a7dd54d5f90663ec4293cc` is preserved by true merge
`4e298a102c6f914b42581492152ab9eea1cd0edf`, whose first parent is exact
activation-control commit `35cb1a7c5f136f291398dddd99d8012dcf38f967`.
The separate integration-control commit applies exact R0011 and reviewed
correction `DFF0256BCDAB3DA2A3248D85A5A390E345AE5C49D45C6E099E26E315CF03B909`.
The resulting projection was 2,860 production modules: 2,770 classified, 90
unclassified, and 0 mixed, with the residual queue exactly R09=72 and R10=18.
That queue is now empty: R09 and R10 were integrated at
`09512c1b15fd4f6892a313341b1edc8c02bb913d`, after which the accepted C0007
baseline recorded 2,927 production modules with 0 unclassified; the later I01
landing brought the live tree to 2,928 production modules, still with 0
unclassified.

Exact integration-control commit `b2b9ab9057deda15c3fcf27745b76dcc49d3a1a5`
passed GitHub Lean CI run 32616508317 (job 97138028649). Checkpoint C0006 is
accepted by `primary-human` at exact code commit
`fda296b2079acae3bf1d3565b2dc6e45dc8f6ef5`: M07 is accepted at C0006, B0010 is
accepted with retirement due, and P0010 is retired and R0011 is applied with
its reviewed supplemental correction. The remote worker ref remains preserved
at the immutable delivery. Branch retirement remains a separate later control.

## Floating-point model

The core library uses an
[abstract real-arithmetic model](NumStability/FloatingPoint/Model.lean), not a
concrete IEEE-754 implementation. An `FPModel` supplies a nonnegative unit
roundoff `u` and rounded addition, subtraction, multiplication, division, and
square root. For the binary operations, the central relative-error law is

```text
fl(x ◦ y) = (x ◦ y)(1 + δ),    |δ| ≤ u.
```

Division carries a nonzero-denominator condition, square root a nonnegative-input
condition, and the model assumes `fl_add 0 x = x`. Individual theorems state any
additional guards they need, such as bounds ensuring `γ(n)` is defined.

Results are parameterized by this model. The exact-arithmetic instance
`FPModel.exactWithUnitRoundoff` is also useful for proving that an overly strong
claim cannot follow from the abstract assumptions alone. Exact algebra and
matrix norms come from Mathlib; new APIs use Mathlib's `Matrix` and norm
interfaces directly, while older function-shaped matrix APIs remain available
through compatibility wrappers.

## Coverage

All 28 chapter rows are terminal under the audit rules, with no unresolved
precise core rows. In the table, **Closed** means compiled at source strength,
**Discrepancy** means the printed claim has a compiled counterexample and a
faithful correction, and **Defer** records an imprecise source statement or an
external citation rather than a proof hole. The detailed evidence lives in the
[per-chapter ledgers](docs/source_coverage/) and the
[PDF-first audit](docs/source_coverage/AUDIT_ch01-28_PDF_FIRST_2026-07-21.md).

| Ch. | Topic | Audit result |
|---:|---|---|
| 1 | Principles of finite precision | Closed |
| 2 | Floating-point arithmetic | Closed |
| 3 | Basics (dot products, `γ(n)`) | Closed |
| 4 | Summation | Closed |
| 5 | Polynomials and Horner's method | Closed |
| 6 | Norms | Discrepancy |
| 7 | Perturbation theory for linear systems | Discrepancy |
| 8 | Triangular systems | Discrepancy · Defer |
| 9 | LU factorization and linear equations | Closed |
| 10 | Cholesky factorization | Discrepancy |
| 11 | Symmetric indefinite and skew-symmetric systems | Discrepancy |
| 12 | Iterative refinement | Closed · Defer |
| 13 | Block LU factorization | Closed |
| 14 | Matrix inversion | Closed · Discrepancy · Defer |
| 15 | Condition-number estimation | Discrepancy · Defer |
| 16 | The Sylvester equation | Closed · Defer |
| 17 | Stationary iterative methods | Closed |
| 18 | Matrix powers | Closed · Defer |
| 19 | QR factorization | Closed · Discrepancy · Defer |
| 20 | The least-squares problem | Discrepancy · Defer |
| 21 | Underdetermined systems | Discrepancy |
| 22 | Vandermonde systems | Discrepancy |
| 23 | Fast matrix multiplication | Closed · Defer |
| 24 | The FFT and applications | Closed |
| 25 | Nonlinear systems and Newton's method | Discrepancy · Defer |
| 26 | Automatic error analysis | Discrepancy · Defer |
| 27 | Software issues in floating point | Discrepancy · Defer |
| 28 | A gallery of test matrices | Discrepancy · Defer |

The RandNLA case study separates reusable algorithms and analysis under
[`NumStability/Algorithms/RandomizedLinearAlgebra/`](NumStability/Algorithms/RandomizedLinearAlgebra/)
from source correspondence under
[`NumStability/Source/DrineasMahoney/RandNLA2016/`](NumStability/Source/DrineasMahoney/RandNLA2016/).
Historical `NumStability.Algorithms.RandNLA` imports remain available as
compatibility paths. The development covers sampling, matrix concentration,
low-rank approximation, and least-squares preconditioning.

## Project statistics

The latest generated production snapshot is the accepted
[`C0007` baseline](docs/architecture/phases/2026-08-repository-reorganization-completion/baselines/C0007-combined.json),
measured at C0007 code commit `4e26820d1f4989ec4ec77b7113085f593570e11b`. The
figures below are that accepted snapshot, not a live measurement:

| Metric | Count |
|---|---:|
| Production Lean modules | **2,927** |
| Nonblank Lean source lines | **1,457,465** |
| Elaborated declarations | **56,913** |
| Theorem and lemma declarations | **43,179** |
| Definition declarations | **11,982** |
| Direct imports | **31,329** (19,558 internal; 11,771 external) |
| Import cycles | **0** |
| Classified modules | **2,927 / 2,927 (100%)** |
| Modules with documentation | **2,927 / 2,927 (100%)** |
| `sorry` / `admit` / top-level `axiom` or `constant` commands | **0** |

The reviewed I01 wave (R0014/R0015, applied at
`9fbb1e36bcc85f866893e902cbe206ba468a65b0`) landed after this snapshot and
added one production module: the live tree contains 2,928 production modules,
all classified and documented, with 712 import-only forwarding modules over
2,364 canonical targets. Regenerate the baseline for fresh live figures.

Source, import, tier, and declaration figures come from the generated baseline.
The placeholder and layout invariants are enforced by
[`tools/architecture/check_layout.py`](tools/architecture/check_layout.py);
the accepted checkpoint evidence is recorded in
[`C0007-gates.md`](docs/architecture/phases/2026-08-repository-reorganization-completion/checkpoints/C0007-gates.md).

## Building

Install Git and [elan](https://github.com/leanprover/elan), then clone the
repository. The project pins Lean `4.29.0-rc3` in
[`lean-toolchain`](lean-toolchain) and pins Mathlib to an exact revision in
[`lakefile.toml`](lakefile.toml).

```bash
lake exe cache get
lake build NumStability NumStabilityTest
lake test
```

To build one module, pass its Lean module name to Lake, for example:

```bash
lake build NumStability.FloatingPoint.Model
```

## Key entry points

Choose the narrowest import that supplies the declarations you need.

| Import | Purpose |
|---|---|
| `NumStability.Core` | Small reusable foundation for the floating-point model and core error analysis |
| `NumStability.FloatingPoint` | Reusable floating-point foundations and IEEE-facing utilities |
| `NumStability.Analysis` | Broad analysis discovery surface; prefer a narrower family import when possible |
| `NumStability.Algorithms` | Broad historical algorithm surface; prefer a canonical family import when possible |
| `NumStability.Source` | Canonical umbrella for book- and paper-specific correspondence |
| `NumStability.Source.Higham` | Higham chapter correspondence and cross-chapter bridges |
| `NumStability.All` | Complete supported library surface |
| `NumStability` | Historical compatibility entry point forwarding to `NumStability.All` |

See [`ARCHITECTURE.md`](ARCHITECTURE.md) for layer boundaries and the full entry
point map. Historical imports are documented in
[`docs/architecture/COMPATIBILITY.md`](docs/architecture/COMPATIBILITY.md).

## Use as a dependency

Add the latest tagged release to your `lakefile.toml`:

```toml
[[require]]
name = "numStability"
git = "https://github.com/AlexGeorgantzas/lean-numerical-stability"
rev = "v0.1.0"
```

Use `rev = "main"` instead if you intentionally want the current development
branch. A minimal reusable import looks like this:

```lean
import NumStability.FloatingPoint.Model

open NumStability

#check FPModel
#check FPModel.exactWithUnitRoundoff
```

## Project structure

The map below emphasizes canonical entry points and stable family boundaries
rather than every theorem leaf. Paired `Family.lean` and `Family/` paths are
usually an import umbrella and its implementation subtree. See
[`ARCHITECTURE.md`](ARCHITECTURE.md) for the authoritative API tiers and
dependency rules.

```text
NumStability.lean                    historical complete-tree entry point → NumStability.All
NumStability/
├── Core.lean                       intentionally small reusable foundation
├── All.lean                        reusable code, source correspondence, and case studies
├── FloatingPoint.lean              complete reusable floating-point umbrella
├── FloatingPoint/
│   ├── Model.lean                  abstract FPModel and primitive rounding assumptions
│   ├── OperationLaws.lean          laws for rounded operations
│   ├── FusedMultiplyAdd/           FMA foundations and dot-product operation counts
│   ├── IEEE.lean                   IEEE-facing operations umbrella
│   └── IEEE/
│       └── NaiveMaximum.lean       value-level maximum and NaN comparison API
├── Analysis.lean                   broad analysis discovery aggregate, including legacy work
├── Analysis/
│   ├── Error/
│   │   ├── Measures/               forward, backward, and relative error measures
│   │   ├── MatrixProducts/         matrix-product error analysis
│   │   └── RoundingProducts/       reusable rounding-product bounds
│   ├── FloatingPointArithmetic/    formats, rounding, special values, and local error laws
│   ├── Asymptotics/                reusable asymptotic bounds
│   ├── FirstOrder/                 fixed-precision and asymptotic first-order analysis
│   ├── Conditioning/               distance-to-singularity and inverse-perturbation theory
│   ├── Perturbation/               perturbation theory, including least squares
│   ├── LinearOperators/
│   │   ├── Jordan/                 Jordan-form support
│   │   ├── MatrixPowers/           power bounds and semiconvergence
│   │   ├── NumericalRadius/        numerical-radius inequalities
│   │   ├── Pseudospectra/          pseudospectral analysis
│   │   └── Schur/                  real and complex Schur theory
│   ├── VectorNorms/                duality, interpolation, and attainment
│   ├── OperatorNorms/              operator-norm definitions and attainment
│   ├── MatrixNorms/                comparisons, spectral extrema, and invariant norms
│   ├── SingularValues/             singular-value and Weyl–Mirsky theory
│   ├── Equidistribution/
│   │   └── AddCircle.lean          Fourier/Haar orbit-equidistribution API
│   ├── LeadingDigits/
│   │   ├── Decimal.lean            decimal leading-digit predicate
│   │   ├── DecimalPowers.lean      powers, logarithms, and decimal arcs
│   │   ├── Empirical.lean          finite empirical digit histograms
│   │   └── LogarithmicDistribution.lean  logarithmic leading-digit law
│   ├── Probability/
│   │   ├── Gaussian/               Gaussian probability analysis
│   │   └── Haar/                   Haar probability and invariant measures
│   ├── Summation/
│   │   ├── Signs.lean              sign and absolute-sum identities
│   │   └── ErrorBounds.lean        summation conditioning and error bounds
│   ├── Statistics/                 sample-statistics analysis
│   └── TestMatrices/               reusable structured and random matrix families
├── Algorithms.lean                 broad historical algorithm aggregate
├── Algorithms/
│   ├── Arithmetic/DotProduct/      sequential, no-guard, and tree dot products
│   ├── Summation/
│   │   ├── Recursive/              sequential recursive summation
│   │   ├── Pairwise/               pairwise summation
│   │   ├── Compensated/            compensated summation
│   │   ├── Insertion/              insertion schedules and error layers
│   │   └── Tree/                   tree-structured summation
│   ├── LinearSystems/              canonical semantic hierarchy for linear solvers
│   │   ├── Cholesky/               factorization, solves, and error analysis
│   │   ├── CramersRule/            reusable Cramer's-rule core
│   │   ├── GaussJordan/            Gauss–Jordan analysis
│   │   ├── Iterative/              stationary iterations and semiconvergence
│   │   ├── IterativeRefinement/    iterative-refinement methods
│   │   ├── LeastSquares/           QR, normal equations, and refinement
│   │   ├── LU/                     block LU, Doolittle, and related families
│   │   ├── QR/                     Givens, Gram–Schmidt, Householder, and solves
│   │   ├── SymmetricIndefinite/    Aasen, block LDLᵀ, pivoting, and error analysis
│   │   ├── Triangular/             forward/back substitution and error bounds
│   │   └── Underdetermined/        minimum-norm and seminormal methods
│   ├── MatrixEquations/Sylvester/  equations, solvers, perturbation, and conditioning
│   ├── MatrixInversion/
│   │   ├── LUFactors/              inversion from LU factors
│   │   ├── Residuals/              residual-based analysis
│   │   └── Triangular/             triangular inversion
│   ├── MatrixPowers/               computed iteration and Jordan-based methods
│   ├── NormEstimation/
│   │   ├── OneNorm/                one-norm estimators
│   │   ├── PNorm/                  p-norm estimators
│   │   └── TwoNorm/                two-norm estimators
│   ├── PolynomialEvaluation/       scalar, derivative, and matrix-polynomial bounds
│   ├── RandomizedLinearAlgebra/
│   │   ├── Sampling/               randomized sampling primitives
│   │   ├── Concentration/          concentration inequalities
│   │   ├── LowRankApproximation/   randomized low-rank methods
│   │   ├── LeastSquaresSketching/  sketched least-squares methods
│   │   └── Preconditioning/        randomized preconditioners
│   └── FastMatMul/                 reusable recurrences plus unsupported historical internals
├── Source.lean                      canonical source-correspondence entry point
├── Source/
│   ├── Higham.lean                 Higham source-correspondence umbrella
│   ├── Higham/
│   │   ├── Chapter01.lean … Chapter28.lean
│   │   │                              chapter-level import umbrellas
│   │   ├── Chapter01/ … Chapter28/ numbered results, algorithms, problems, and corrections
│   │   ├── CrossChapter.lean       cross-chapter umbrella
│   │   └── CrossChapter/           explicit bridges between chapters
│   └── DrineasMahoney/
│       └── RandNLA2016/             algorithm- and equation-indexed correspondence
│           ├── Algorithm01/ … Algorithm03/
│           └── Equation02/, Equation04/ … Equation09/
├── Higham.lean                      historical wrapper → NumStability.Source.Higham
├── Higham/                          historical Higham compatibility paths
└── Upstream/Lindemann/              attributed Mathlib adaptation and backports

NumStabilityTest.lean                complete test-library entry point
NumStabilityTest/
├── Import/                          entry-point and canonical-import smoke tests
├── Compatibility/                   forwarding-path regression tests
├── Reorganization/                  migration and declaration-placement regressions
└── Worker/                          focused proof-audit and integration suites

docs/
├── architecture/
│   ├── COMPATIBILITY.md             forwarding-path contract
│   └── baselines/                   generated graph and inventory baselines
├── source_coverage/                  per-chapter ledgers and PDF-first audits
├── chapter12/, chapter14/
├── chapter20/ … chapter28/           detailed proof ledgers for selected chapters
└── benchmarking/                     benchmark methodology and reports

tools/
├── architecture/                     layout, provenance, compatibility, and graph checks
└── benchmark/                        reproducible build-timing runner

examples/LibraryLookup.lean           representative executable #check lookup
experiments/                          C/Python reproductions of selected source examples
├── chapter01/
├── chapter02/
└── chapter04/

ARCHITECTURE.md                       API-tier and dependency policy
RENAME_LEDGER.md                      archived package/repository/library identity record
                                      (module forwarding: docs/architecture/COMPATIBILITY.md)
lakefile.toml                         Lake package and build configuration
lean-toolchain                        pinned Lean toolchain
```

## Documentation and status

- [`docs/README.md`](docs/README.md) maps current policy, source audits, and
  historical evidence.
- [`ARCHITECTURE.md`](ARCHITECTURE.md) defines layers, dependency direction, and
  supported entry points.
- [`CONTRIBUTING.md`](CONTRIBUTING.md) explains module placement and required
  checks.
- [`CHANGELOG.md`](CHANGELOG.md) records release-facing changes.

The selected source-audit scope is terminal, but repository organization work
is still in progress. Checkpoint C0008 is accepted; the
[active phase registry](docs/architecture/phases/2026-08-repository-reorganization-completion/README.md)
is the authoritative source for remaining migration work.

## References

- N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
  SIAM, 2002.
- P. Drineas and M. W. Mahoney,
  [“RandNLA: Randomized Numerical Linear Algebra”](https://dl.acm.org/doi/10.1145/2842602),
  *Communications of the ACM* 59(6), 80–90, 2016.

## License and citation

Except where an individual file states otherwise, NumStability is licensed
under the [MIT License](LICENSE). Files carrying an Apache-2.0 notice are
licensed under the [Apache License, Version 2.0](LICENSES/Apache-2.0.txt).
Third-party attribution is recorded in
[`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md), and citation metadata is
available in [`CITATION.cff`](CITATION.cff).
