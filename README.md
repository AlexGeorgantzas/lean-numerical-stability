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
[`C0007` baseline](docs/architecture/phases/2026-08-repository-reorganization-completion/baselines/C0007-combined.json):

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

```text
NumStability.lean                 compatibility entry point → NumStability.All
NumStability/
├── Core.lean                    small reusable foundation
├── All.lean                     complete supported surface
├── FloatingPoint.lean
├── FloatingPoint/               abstract model and IEEE-facing support
├── Analysis.lean
├── Analysis/                    reusable analysis and historical aggregates
├── Algorithms.lean
├── Algorithms/                  numerical algorithm families
├── Source.lean
├── Source/
│   ├── Higham/                  Higham chapter correspondence
│   └── DrineasMahoney/          RandNLA source correspondence
├── Higham/                      historical compatibility paths
└── Upstream/                    attributed adapted or backported code
NumStabilityTest/                import, compatibility, and theorem smoke tests
docs/
├── source_coverage/             chapter ledgers and source audits
└── architecture/                policy, manifests, and migration evidence
tools/architecture/              generated baselines and repository checks
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
is still in progress. Checkpoint C0007 is accepted; the
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
