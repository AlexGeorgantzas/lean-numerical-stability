# LeanFpAnalysis

A Lean 4 library for formally verified floating-point error analysis, following
Nicholas J. Higham's *Accuracy and Stability of Numerical Algorithms*
(2nd ed., SIAM, 2002), together with a randomized numerical linear algebra
(RandNLA) case study.

The library covers material from **all 28 chapters** of Higham. Every result is
machine-checked against Mathlib: the tree contains **no `sorry`, `admit`, or
`axiom` declarations**, and sampled headline theorems depend only on the standard
`[propext, Classical.choice, Quot.sound]` axioms. Bounds use tight constants
matching Higham where the full local analysis is proved (e.g. `γ(n)`, not
`γ(n+1)`, for the dot-product bound). Some higher-chapter results are stated at an
honest, documented strength — abstract interfaces whose hypotheses spell out the
remaining local analysis, or an exact-arithmetic model where the general rounded
statement is provably out of reach; these are recorded per chapter under
[`docs/source_coverage/`](docs/source_coverage/).

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
used to *prove obstructions* — e.g. that certain Chapter 19 backward-error
identities cannot hold over the abstract model.

## What's covered

Higham chapters 1–28, plus the RandNLA case study. Per-chapter status is tracked
in the ledgers under [`docs/source_coverage/`](docs/source_coverage/); the
cross-chapter re-audit of Chapters 12–28 is in
[`docs/source_coverage/AUDIT_ch12-28_2026-07.md`](docs/source_coverage/AUDIT_ch12-28_2026-07.md).

| Ch | Topic | Gate |
|----|-------|------|
| 1  | Principles of finite precision | ✅ |
| 2  | Floating point arithmetic | ✅ |
| 3  | Basics (dot products, `γ(n)`) | ✅ |
| 4  | Summation | ✅ |
| 5  | Polynomials (Horner) | ✅ |
| 6  | Norms | ✅ |
| 7  | Perturbation theory for linear systems | ✅ |
| 8  | Triangular systems | ✅ |
| 9  | LU factorization and linear equations | ✅ |
| 10 | Cholesky factorization | ✅ |
| 11 | Symmetric indefinite / skew-symmetric systems | ✅ |
| 12 | Iterative refinement | ✅ |
| 13 | Block LU factorization | ✅ |
| 14 | Matrix inversion | ✅ |
| 15 | Condition number estimation | ✅ |
| 16 | The Sylvester equation | ✅ |
| 17 | Stationary iterative methods | ✅ |
| 18 | Matrix powers | ✅ |
| 19 | QR factorization | ⚠️ terminal `BLOCKED` (see below) |
| 20 | The least squares problem | ✅ |
| 21 | Underdetermined systems | ✅ |
| 22 | Vandermonde systems | ✅ |
| 23 | Fast matrix multiplication | ✅ |
| 24 | The FFT and applications | ✅ |
| 25 | Nonlinear systems and Newton's method | ✅ |
| 26 | Automatic error analysis | ✅ |
| 27 | Software issues in floating point | ✅ |
| 28 | A gallery of test matrices | ✅ |

✅ = selected-scope gate passes (every selected theorem/lemma/equation is verified
at printed strength, or is an honest, documented partial). A ✅ chapter may still
carry a small number of source-faithful residuals, noted in its ledger.

- **Chapter 19** is a documented terminal `BLOCKED`: Theorems 19.6 and 19.13 hold
  only under an exact-arithmetic strong model, and the bare-`FPModel` versions are
  *proven impossible* by an in-tree counterexample. Every other Chapter 19 result
  (Lemmas 19.1–19.3, 19.7–19.9; Theorems 19.4, 19.5, 19.10) is verified.
- **Chapter 11**'s four primary theorems are now derived from the floating-point
  model in dedicated closure modules
  ([`FP/Algorithms/Cholesky/*Ch11Closure.lean`](LeanFpAnalysis/FP/Algorithms/Cholesky)),
  each assuming only Higham's own inputs (the eq. (11.5) 2×2-solve family). Theorems
  11.3, 11.4, and 11.7 are closed at printed / source-faithful strength; for the
  Bunch symmetric-tridiagonal method (11.7) the bounded element growth is *derived*
  from Algorithm 11.6's fixed-scale pivoting, not assumed. Theorem 11.8 (Aasen) is
  closed with one disclosed middle-solve idealization (`hmiddle_factors`), recorded
  in the ledger.

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
| Lean files | **512** |
| Lines of Lean | **~1.33 million** |
| Theorems + lemmas proved | **~34,400** (32,605 `theorem` + 1,794 `lemma`) |
| Definitions | **7,890** `def`, 229 `abbrev` |
| Structures / instances | 346 `structure`, 131 `instance` |
| `sorry` / `admit` / `axiom` declarations | **0** |
| Full `lake build` | **~4,300** jobs |

Everything is proved against Mathlib; sampled headline theorems depend only on
the standard `[propext, Classical.choice, Quot.sound]` axioms. (Declaration
counts are keyword occurrences across `LeanFpAnalysis/**/*.lean`; the line count
is total physical lines, including comments and blanks.)

## Building

Requires [`elan`](https://github.com/leanprover/elan) (which pins Lean/Lake from
`lean-toolchain`: `leanprover/lean4:v4.29.0-rc3`, Mathlib `v4.29.0`). From a
clone:

```bash
lake exe cache get   # download prebuilt Mathlib oleans — skipping this makes the build very slow
lake build           # ~4300 build jobs
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
  source_coverage/            -- per-chapter coverage ledgers + the ch12–28 audit
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

Deepen the remaining honest-partial rows toward full printed strength (notably
Chapter 19 under a faithful rounded model, and discharging Chapter 11's Theorem
11.8 middle-solve idealization). Issues and contributions for specific algorithms
or results are welcome.

## License

MIT.
