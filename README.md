# LeanFpAnalysis

A Lean 4 library for formally verified floating-point error analysis, following
Nicholas J. Higham's *Accuracy and Stability of Numerical Algorithms*
(2nd ed., SIAM, 2002), together with a randomized numerical linear algebra
(RandNLA) case study.

The library contains machine-checked material from **all 28 chapters** of
Higham. The tree contains **no `sorry`, `admit`, or `axiom` declarations**, and
sampled headline theorems depend only on the standard
`[propext, Classical.choice, Quot.sound]` axioms. That proof hygiene is distinct
from source-strength closure: several selected rows remain conditional, partial,
or tied to an exact-arithmetic model. The strict per-chapter gates below count
only results proved at the printed strength.

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
in the ledgers under [`docs/source_coverage/`](docs/source_coverage/). The
authoritative from-scratch audit is
[`docs/source_coverage/AUDIT_ch01-28_2026-07-18.md`](docs/source_coverage/AUDIT_ch01-28_2026-07-18.md).

| Ch | Topic | Strict gate |
|----|-------|-------------|
| 1  | Principles of finite precision | PASS |
| 2  | Floating point arithmetic | PASS |
| 3  | Basics (dot products, `γ(n)`) | PASS |
| 4  | Summation | FAIL |
| 5  | Polynomials (Horner) | PASS |
| 6  | Norms | PASS |
| 7  | Perturbation theory for linear systems | PASS |
| 8  | Triangular systems | FAIL |
| 9  | LU factorization and linear equations | PASS |
| 10 | Cholesky factorization | FAIL |
| 11 | Symmetric indefinite / skew-symmetric systems | FAIL |
| 12 | Iterative refinement | PASS |
| 13 | Block LU factorization | PASS |
| 14 | Matrix inversion | FAIL |
| 15 | Condition number estimation | FAIL |
| 16 | The Sylvester equation | FAIL |
| 17 | Stationary iterative methods | PASS |
| 18 | Matrix powers | FAIL |
| 19 | QR factorization | BLOCKED |
| 20 | The least squares problem | FAIL |
| 21 | Underdetermined systems | PASS |
| 22 | Vandermonde systems | FAIL |
| 23 | Fast matrix multiplication | PASS |
| 24 | The FFT and applications | PASS |
| 25 | Nonlinear systems and Newton's method | FAIL |
| 26 | Automatic error analysis | PASS |
| 27 | Software issues in floating point | PASS |
| 28 | A gallery of test matrices | FAIL |

Fresh result: **15 PASS, 12 FAIL, 1 BLOCKED**. A failed gate can still contain
substantial verified material; it means at least one selected printed-strength
producer or bridge remains open.

`PASS` means every selected theorem, lemma, equation, and implementation-facing
claim is verified at printed strength. An honest `PARTIAL`, conditional transfer,
or exact-arithmetic subcase remains useful formalization, but does not make the
stronger source row pass.

- **Chapter 19** is a documented terminal `BLOCKED`: Theorems 19.6 and 19.13 hold
  only under an exact-arithmetic strong model, and the bare-`FPModel` versions are
  *proven impossible* by an in-tree counterexample. Every other Chapter 19 result
  (Lemmas 19.1–19.3, 19.7–19.9; Theorems 19.4, 19.5, 19.10) is verified.
- **Chapter 11** has Theorems 11.3, 11.4, and 11.7 closed, but Theorem 11.8 is
  conditional on `hmiddle_factors`, which is not a source hypothesis. A concrete
  2-by-2 Aasen/GEPP trace now refutes its coefficient-one inequality; the library
  also proves the strongest currently available unconditional `2 n²` replacement.
- **Chapter 20** is not closed merely by importing Chapter 19. Its Theorem 20.7
  policy and component-budget records are not produced by the rounded pivoted-QR
  executor; a legal full-rank 2-by-2 trace additionally demonstrates rounded
  breakdown in the bare model.
- **Chapter 10** has several target-bearing perturbation/backward-error premises,
  an extra Theorem 10.7 spectral premise, and no source-strength rank-deficient
  10.9(b), Kahan sharpness, or (10.22) producer.
- **Chapter 22** now has a genuine Chapter 5 residual bridge, but its actual
  monomial Stage-II factor producer, refinement contraction, and precise Table
  22.1 V1--V6 claims remain open.
- **Chapter 25** now has the bordered Jacobian, literal rounded residual, and a
  kernel theorem from an explicit simple-eigenpair certificate. Its strict gap
  is the producer from algebraic multiplicity one to that certificate. The
  printed coefficient `2‖A‖` is separately refuted at `A=0` and corrected to
  the universal infinity-norm coefficient `2`.
- **Chapter 28** remains open only at the exact Hilbert condition-number log
  rate and the normalized-Gaussian-QR-to-Haar producer. Its general
  reciprocal-spectrum SPD construction is now formalized; the printed final
  column-scaling clause is refuted and replaced by the correct row/transpose
  scaling identity.

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
| Lean files | **524** |
| Lines of Lean | **~1.34 million** |
| Theorems + lemmas proved | **~34,300** (32,455 `theorem` + 1,820 `lemma`) |
| Definitions | **7,994** `def`, 229 `abbrev` |
| Structures / instances | 348 `structure`, 131 `instance` |
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

Deepen the remaining strict-fail rows listed in the fresh audit, notably Chapter
19 under a faithful rounded model and Chapter 11's Theorem 11.8 middle-solve
idealization. Issues and contributions for specific algorithms or results are
welcome.

## License

MIT.
