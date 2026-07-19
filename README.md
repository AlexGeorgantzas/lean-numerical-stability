# LeanFpAnalysis

A Lean 4 library for formally verified floating-point error analysis, following
Nicholas J. Higham's *Accuracy and Stability of Numerical Algorithms*
(2nd ed., SIAM, 2002), together with a randomized numerical linear algebra
(RandNLA) case study.

The library contains machine-checked material from **all 28 chapters** of
Higham. The tree contains **no `sorry`, `admit`, or `axiom` declarations**, and
sampled headline theorems depend only on the standard
`[propext, Classical.choice, Quot.sound]` axioms. The fresh audit closes every
selected core row either at source strength or, when the printed statement is
false, with a theorem-level counterexample and a faithful corrected theorem.

## Floating-point model

The library uses an **abstract** floating-point model
([`FP/Model.lean`](LeanFpAnalysis/FP/Model.lean)), not a concrete IEEE-754
representation. An `FPModel` carries a unit roundoff `u` and rounding operations
`fl_add / fl_sub / fl_mul / fl_div / fl_sqrt`, each satisfying the standard model

```
fl(x ∘ y) = (x ∘ y)(1 + δ),   |δ| ≤ u
```

Because everything is parametric over `u` and the rounding operations, results
hold for **any** arithmetic satisfying the standard model. A concrete instance
`FPModel.exactWithUnitRoundoff` (operations exact, `δ = 0`, formal `u ≥ 0`) is
used to *prove obstructions* — for example, to refute overly strong norm or
factor-identification claims before replacing them with faithful statements.

## What's covered

Higham chapters 1–28, plus the RandNLA case study. Per-chapter status is tracked
in the ledgers under [`docs/source_coverage/`](docs/source_coverage/). The
authoritative from-scratch audit is
[`docs/source_coverage/AUDIT_ch01-28_2026-07-19.md`](docs/source_coverage/AUDIT_ch01-28_2026-07-19.md).

| Ch | Topic | Strict gate |
|----|-------|-------------|
| 1  | Principles of finite precision | PASS |
| 2  | Floating point arithmetic | PASS |
| 3  | Basics (dot products, `γ(n)`) | PASS |
| 4  | Summation | PASS |
| 5  | Polynomials (Horner) | PASS |
| 6  | Norms | PASS |
| 7  | Perturbation theory for linear systems | PASS |
| 8  | Triangular systems | PASS |
| 9  | LU factorization and linear equations | PASS |
| 10 | Cholesky factorization | PASS / SOURCE-DISCREPANCY |
| 11 | Symmetric indefinite / skew-symmetric systems | PASS / SOURCE-DISCREPANCY |
| 12 | Iterative refinement | PASS |
| 13 | Block LU factorization | PASS |
| 14 | Matrix inversion | PASS |
| 15 | Condition number estimation | PASS |
| 16 | The Sylvester equation | PASS |
| 17 | Stationary iterative methods | PASS |
| 18 | Matrix powers | PASS |
| 19 | QR factorization | PASS (explicit domain) |
| 20 | The least squares problem | PASS (explicit domain) |
| 21 | Underdetermined systems | PASS |
| 22 | Vandermonde systems | PASS |
| 23 | Fast matrix multiplication | PASS |
| 24 | The FFT and applications | PASS |
| 25 | Nonlinear systems and Newton's method | PASS / SOURCE-DISCREPANCY |
| 26 | Automatic error analysis | PASS |
| 27 | Software issues in floating point | PASS |
| 28 | A gallery of test matrices | PASS / SOURCE-DISCREPANCY |

Fresh result: **28 PASS, 0 FAIL, 0 BLOCKED**.

`PASS` means every precise selected theorem, lemma, equation, and
implementation-facing claim is terminal under the audit rules. A
`SOURCE-DISCREPANCY` qualification means the printed statement is false and the
library contains both a theorem-level counterexample and a faithful correction;
it does not mean that the source formula was made provable by adding a hidden
hypothesis. Unparameterized higher-order notation, qualitative observations,
visual tables, and unspecified algorithms are explicitly inventoried and
deferred rather than converted into arbitrary propositions.

- **Chapter 11:** Theorems 11.3, 11.4, and the literal support-aware 11.7 path
  are closed. Theorem 11.8 is false as printed because it gives a zero norm
  radius at `n=1`; the actual scalar Aasen execution refutes that clause and the
  sharp correction has backward error `u/(1+u) ≤ γ_1`.
- **Chapters 19 and 20:** literal rounded MGS and pivoted stored-QR / least-
  squares executors close the source-rate endpoints. Computed nonbreakdown is
  stated as the natural domain implicit in the source's “computed matrices” and
  “computed solution” language, not assumed as an error budget.
- **Chapters 10, 25, and 28:** false printed formulas remain visible as checked
  source discrepancies with corrected theorems. Chapter 10's operational
  Cholesky chain and sharpness results, Chapter 25's multiplicity-one bordered
  eigenproblem, and Chapter 28's exact Hilbert rate and Gaussian-QR Haar law are
  otherwise closed.
- **Chapters 4, 8, 14, 15, 20, and 22:** the fresh repairs add the missing
  literal finite-format/executor, fan-in, finalized Gauss-Jordan, probability,
  pivoted least-squares, and monomial-stage bridges instead of relying on
  target-bearing readiness or residual premises.

The **RandNLA case study**
([`FP/Algorithms/RandNLA/`](LeanFpAnalysis/FP/Algorithms/RandNLA), 17 modules)
formalizes the meta-algorithms of Drineas and Mahoney's CACM survey
["RandNLA: Randomized Numerical Linear Algebra"](https://dl.acm.org/doi/10.1145/2842602)
— row/elementwise/leverage-score sampling, matrix concentration, low-rank
approximation, and least-squares preconditioning.

## Project statistics

Snapshot of the current `LeanFpAnalysis/` tree:

| | |
|---|---|
| Lean files | **558** |
| Lines of Lean | **~1.31 million** |
| Theorems + lemmas proved | **~37,300** (35,433 `theorem` + 1,830 `lemma`) |
| Definitions | **8,282** `def`, 170 `abbrev` |
| Structures / instances | 367 `structure`, 79 `instance` |
| `sorry` / `admit` / `axiom` declarations | **0** |
| Full serialized `lake build` | **4,387 jobs** |

Everything is proved against Mathlib; sampled headline theorems depend only on
the standard `[propext, Classical.choice, Quot.sound]` axioms. (Declaration
counts are declaration-line matches across `LeanFpAnalysis/**/*.lean`; the line
count is total physical lines, including comments and blanks.)

## Building

Requires [`elan`](https://github.com/leanprover/elan) (which pins Lean/Lake from
`lean-toolchain`: `leanprover/lean4:v4.29.0-rc3`, Mathlib `v4.29.0`). From a
clone:

```bash
lake exe cache get   # download prebuilt Mathlib oleans — skipping this makes the build very slow
lake build           # 4387 build jobs in the audited tree
```

Build a single module, e.g.:

```bash
lake build LeanFpAnalysis.FP.Algorithms.GaussJordan
```

If a fresh build fails fetching ProofWidgets, drop its release build in place:

```bash
curl -L https://github.com/leanprover-community/ProofWidgets4/releases/download/v0.0.90/ProofWidgets4.tar.gz -o /tmp/pw.tar.gz
mkdir -p .lake/build/packages/proofwidgets && tar xzf /tmp/pw.tar.gz -C .lake/build/packages/proofwidgets
```

## Use as a dependency

Add to your `lakefile.toml`:

```toml
[[require]]
name = "LeanFpAnalysis"
git = "https://github.com/AlexGeorgantzas/lean-fp-analysis"
rev = "main"
```

then `import LeanFpAnalysis.FP`.

```lean
import LeanFpAnalysis.FP
open LeanFpAnalysis.FP

variable (fp : FPModel) (n : ℕ)

#check gamma fp n                -- γ(n) = nu / (1 - nu)
#check dotProduct_error_bound    -- |fl(x·y) - x·y| ≤ γ(n)·Σ|xᵢ||yᵢ|
#check backSub_backward_error    -- (U + ΔU)x̂ = b, |ΔU| ≤ γ(n)|U|
#check lu_solve_backward_error   -- (A + ΔA)x̂ = b, |ΔA| ≤ (3γ(n)+γ(n)²)|L̂||Û|
```

## Project structure

```
LeanFpAnalysis/
  FP.lean                     -- top-level aggregate (import this)
  FP/
    Model.lean                -- the abstract floating-point model
    Analysis/                 -- perturbation theory, matrix algebra, norms,
                              --   concentration, probability (foundations)
    Analysis/MatrixAlgebra.lean  -- shared exact matrix-algebra layer
    Algorithms/               -- algorithm formalizations, per chapter, with
                              --   clusters LU/ QR/ Cholesky/ FFT/ Vandermonde/
                              --   Nonlinear/ RandNLA/ and TestMatrices/
docs/
  source_coverage/            -- per-chapter coverage ledgers + fresh ch01–28 audit
  chapterNN/                  -- detailed source inventories / proof ledgers
```

## Exact algebra and matrix norms

Mathlib is the source of truth for exact algebra and norms; new APIs use Mathlib
notation directly (e.g. `‖A‖` under the appropriate matrix-norm scope) and the
alias `RMat m n := Matrix (Fin m) (Fin n) ℝ`. The legacy algorithm layer uses
function-shaped matrices `RMatFn m n := Fin m → Fin n → ℝ` with documented
compatibility wrappers (`frobNorm`, `infNorm`) that coerce through `Matrix.of`
and reuse Mathlib's norms — they are not independent norm definitions.

## References

- N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
  SIAM, 2002.
- P. Drineas and M. W. Mahoney,
  ["RandNLA: Randomized Numerical Linear Algebra"](https://dl.acm.org/doi/10.1145/2842602),
  *Communications of the ACM* 59(6), 80–90, 2016.

## Roadmap

The selected core scope is closed. Natural follow-up work includes optional
Problems, additional quantitative versions of prose that the source leaves
unparameterized, and stronger corrected variants of source-discrepancy rows.
Issues and contributions for specific algorithms or results are welcome.

## License

MIT.
