# LeanFpAnalysis

A Lean 4 library for formally verified floating-point error analysis, following Higham's *Accuracy and Stability of Numerical Algorithms* (2nd ed., SIAM, 2002).

The core results are machine-checked with **zero sorry statements**. Proofs use tight constants matching Higham exactly where the library proves the full local analysis (e.g., γ(n) not γ(n+1) for the dot product bound). Some high-level chapter modules intentionally expose abstract interfaces whose hypotheses state the remaining local algorithm analysis explicitly.

## Floating-point model

The library uses an axiomatic floating-point model ([`FP/Model.lean`](LeanFpAnalysis/FP/Model.lean)) rather than a concrete IEEE 754 representation. Every arithmetic operation satisfies:

```
fl(x ∘ y) = (x ∘ y)(1 + δ),  |δ| ≤ u
```

where `u` is the unit roundoff. This makes all results valid for **any** floating-point system satisfying the standard model.

## What's covered

The library formalizes reusable results and stability contracts from **Chapters 1, 3, 4, 8, and 9** of Higham, plus selected higher-chapter interfaces used for compositional stability proofs. It also includes a RandNLA case study for the element-wise sampling meta-algorithm from Drineas and Mahoney's CACM survey, ["RandNLA: Randomized Numerical Linear Algebra"](https://dl.acm.org/doi/10.1145/2842602).

For a searchable map from stability-analysis goals to files, definitions, and
theorem names, see [`docs/LIBRARY_LOOKUP.md`](docs/LIBRARY_LOOKUP.md).  For a
Lean `#check` companion index, see [`examples/LibraryLookup.lean`](examples/LibraryLookup.lean).

### Core theory

| Topic | Higham ref | Key results |
|---|---|---|
| Error measures | §1.2 | `absError`, `relError`, `compRelErrorBounded` |
| Backward stability | §1.7–1.9 | `backwardErrorBounded`, `condNumber`, `forward_from_backward` |
| γ-function | §3.1, §3.4 | `gamma`, `prod_error_bound`, `gamma_mul`, `gamma_inv`, `gamma_div` |
| Summation error | §3.1 | `fl_sum_error`, `fl_sum_error_init`, `fl_sub_sum_error_init` |

### Algorithms

| Algorithm | Higham ref | Key results |
|---|---|---|
| Dot product | §3.5 | `dotProduct_error_bound` — tight γ(n) bound |
| Matrix-vector product | §3.5 | `matVec_backward_error`, `matVec_error_bound` |
| Outer product | §3.1 | `outerProduct_error_bound` |
| Matrix multiplication | §3.5 | `matMul_error_bound` |
| RandNLA element-wise sampling | [Drineas-Mahoney Algorithm 1](https://dl.acm.org/doi/10.1145/2842602) | `fl_elementwiseTraceSketch_sqMag_error_bound`, `highProbability_sqMagTraceStability_of_markov_budget`, `highProbability_sqMagTraceStability_of_pairwise_chebyshev_budget`, `highProbability_sqMagTraceStability_of_independent_chernoff_budget`, `highProbability_sqMagTraceStability_of_independent_chernoff_optimized_tail_budget` |
| Recursive summation | §4.1–4.2 | `recursive_sum_backward_error`, `recursive_sum_forward_error` |
| Pairwise summation | §4.2 | Backward and forward error bounds |
| Tree summation | §4.2 | `sumTree_backward_error` |
| Back substitution | §8.1 | `backSub_backward_error` (Theorem 8.5) |
| Forward substitution | §8.1 | `forwardSub_backward_error` (Theorem 8.5) |
| Combined LU solve | §8.1 | `lu_solve_combined_backward_error` (Corollary 8.6) |
| Forward error bounds | §8.2 | `diag_dominant_forward_error` (Th. 8.7), `theorem_8_9` |
| M-matrix solutions | §8.2 | `mmatrix_forwardSub_relative_error` (componentwise relative error in μ-form) |
| Inverse bounds | §8.3 | `theorem_8_11_first_ineq`, `theorem_8_11_upper_bound` (Th. 8.13) |
| LU factorization | §9.3 | `LUBackwardError` (Theorem 9.3) |
| LU solve | §9.4 | `lu_solve_backward_error` (Theorem 9.4) |
| SPD matrices | §9.4 | `spd_growth_factor_bound`, `spd_backward_stability` (Th. 9.11) |
| M-matrix LU | §9.4 | `mmatrix_optimal_growth` (Theorem 9.11) |
| Banded LU | §9.5 | `banded_lu_backward_error` |

## Installation

Add to your `lakefile.toml`:

```toml
[[require]]
name = "LeanFpAnalysis"
git = "https://github.com/AlexGeorgantzas/lean-fp-analysis"
rev = "main"
```

Or to your `lakefile.lean`:

```lean
require LeanFpAnalysis from git
  "https://github.com/AlexGeorgantzas/lean-fp-analysis" @ "main"
```

Then in your Lean files:

```lean
import LeanFpAnalysis.FP
```

## Building

Requires [Lean 4](https://leanprover.github.io) with [Lake](https://github.com/leanprover/lean4/tree/master/src/lake).

```bash
lake build
```

- Lean toolchain: `leanprover/lean4:v4.29.0-rc3`
- Mathlib: `v4.29.0`

> **Note:** On a fresh clone, `lake build` may fail with a ProofWidgets build error. Run:
> ```bash
> curl -L https://github.com/leanprover-community/ProofWidgets4/releases/download/v0.0.90/ProofWidgets4.tar.gz \
>   -o /tmp/pw.tar.gz
> mkdir -p .lake/build/packages/proofwidgets
> tar xzf /tmp/pw.tar.gz -C .lake/build/packages/proofwidgets
> ```

## Usage example

```lean
import LeanFpAnalysis.FP
open LeanFpAnalysis.FP

variable (fp : FPModel) (n : ℕ)

-- The γ-function bounds accumulated rounding error
#check gamma fp n  -- γ(n) = nu / (1 - nu)

-- Dot product: |fl(x·y) - x·y| ≤ γ(n) · Σ|xᵢ||yᵢ|
#check dotProduct_error_bound

-- Back substitution: (U + ΔU)x̂ = b with |ΔU| ≤ γ(n)|U|
#check backSub_backward_error

-- LU solve: (A + ΔA)x̂ = b with |ΔA| ≤ (3γ(n) + γ(n)²)|L̂||Û|
#check lu_solve_backward_error
```

## RandNLA Algorithm 1

The RandNLA development formalizes Algorithm 1 from Petros Drineas and
Michael W. Mahoney, ["RandNLA: Randomized Numerical Linear Algebra"](https://dl.acm.org/doi/10.1145/2842602),
Communications of the ACM 59(6), 80-90, 2016. It uses element-wise sampling
with squared-magnitude probabilities

```
p_ij = A_ij^2 / sum_{k,l} A_kl^2.
```

The deterministic theorem family reduces the floating-point trace error to a bound on the hit counter `q_ij`. The randomized theorem family then proves high-probability hit-count bounds using finite Markov, pairwise-Chebyshev, and Chernoff arguments.

Key entry points:

```lean
import LeanFpAnalysis.FP.Algorithms.RandNLA
open LeanFpAnalysis.FP

#check fl_elementwiseTraceSketch_sqMag_error_bound
#check highProbability_sqMagTraceStability_of_markov_budget
#check highProbability_sqMagTraceStability_of_pairwise_chebyshev_budget
#check highProbability_sqMagTraceStability_of_independent_chernoff_budget
#check highProbability_sqMagTraceStability_of_independent_chernoff_optimized_tail_budget
```

For the theorem ledger and prose proof summary, see
[`docs/RANDNLA_ALGORITHM1_STABILITY_LEDGER.md`](docs/RANDNLA_ALGORITHM1_STABILITY_LEDGER.md)
and [`docs/Algorithm1_Stability_Proof_Summary.pdf`](docs/Algorithm1_Stability_Proof_Summary.pdf).

## Module structure

```
LeanFpAnalysis/FP/
├── Model.lean                  — Axiomatic FPModel
├── Analysis/
│   ├── Error.lean              — Error measures (§1.2)
│   ├── Rounding.lean           — γ-function, product error bounds (§3.1, §3.4)
│   ├── Summation.lean          — Summation error (§3.1)
│   ├── SubtractionFold.lean    — Subtraction fold error (§3.1)
│   ├── Stability.lean          — Backward stability definitions (§1.7–1.9)
│   ├── ForwardError.lean       — Forward error from backward error (§8.2)
│   ├── FiniteProbability.lean  — Finite probability, Markov/Chebyshev/Chernoff kernels
│   ├── MatrixAlgebra.lean      — Exact matrix algebra and norms
│   └── PerturbationTheory.lean — Forward-error perturbation theory
└── Algorithms/
    ├── DotProduct.lean         — Dot product (§3.5)
    ├── MatVec.lean             — Matrix-vector product (§3.5)
    ├── OuterProduct.lean       — Outer product (§3.1)
    ├── MatMul.lean             — Matrix multiplication
    ├── RandNLA/
    │   ├── ElementwiseSampling.lean    — Algorithm 1 updates, traces, hit counts, stability events
    │   └── HitCountConcentration.lean  — Markov, Chebyshev, Chernoff high-probability stability
    ├── RecursiveSum.lean       — Recursive summation (§4.1–4.2)
    ├── PairwiseSum.lean        — Pairwise summation (§4.2)
    ├── SumTree.lean            — Tree summation (§4.2)
    ├── TriangularSolve.lean    — Back substitution (§8.1)
    ├── ForwardSub.lean         — Forward substitution (§8.1)
    ├── TriangularSolveCombined.lean    — Combined LU solve (§8.1)
    ├── TriangularForwardBound.lean     — Diagonal dominance bounds (§8.2)
    ├── TriangularForwardComparison.lean — Comparison matrix bounds (§8.2)
    ├── InverseBounds.lean      — Inverse bounds (§8.3)
    ├── MMatrix.lean            — M-matrix properties (§8.2)
    └── LU/
        ├── GaussianElimination.lean    — LU backward error (§9.3)
        ├── LUSolve.lean                — LU solve backward error (§9.4)
        ├── GrowthFactor.lean           — Growth factor (§9.3–9.4)
        ├── SpecialMatrices.lean        — SPD, M-matrix, sign-equivalent (§9.4)
        ├── Tridiagonal.lean            — Banded/tridiagonal LU (§9.5)
        ├── TridiagonalRecurrence.lean  — Tridiagonal recurrence
        └── Doolittle.lean              — Doolittle algorithm
```

## Roadmap

More chapters from Higham are planned. Contributions and requests are welcome — open an issue if there's a specific algorithm or result you need formalized.

## References

N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002.

P. Drineas and M. W. Mahoney, ["RandNLA: Randomized Numerical Linear Algebra"](https://dl.acm.org/doi/10.1145/2842602), *Communications of the ACM*, 59(6), 80-90, 2016.

## License

MIT
