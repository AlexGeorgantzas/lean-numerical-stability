# lean-fp-analysis

A Lean 4 library for formally verifying the floating-point error analysis of numerical algorithms, following Higham's *Accuracy and Stability of Numerical Algorithms*.

## Goal

Automatically prove backward and forward stability bounds for standard linear algebra algorithms in finite-precision arithmetic — using Lean's type system and Mathlib as the mathematical foundation.

## Model

The library is built on a Higham-style axiomatic floating-point model ([`FP/Model.lean`](LeanFpAnalysis/FP/Model.lean)). Every arithmetic operation satisfies:

```
fl(x ∘ y) = (x ∘ y)(1 + δ),   |δ| ≤ u
```

where `u` is the unit roundoff. No specific precision (e.g. IEEE 754) is assumed; all results hold for any model satisfying the axiom.

## Module Structure

```
LeanFpAnalysis/
  FP/
    Model.lean               — FPModel structure (axiomatic model)
    Analysis/
      Error.lean             — absError, relError (§1.2)
      Rounding.lean          — gamma, prod_error_bound, gamma_mul, gamma_inv
      Summation.lean         — fl_sum_error, fl_sum_error_init
      Stability.lean         — backward stability predicates, condition number (§1.7–1.9)
    Algorithms/
      DotProduct.lean        — fl_dotProduct, dotProduct_error_bound  (Higham §3.5)
      MatVec.lean            — fl_matVec, matVec_backward_error, matVec_error_bound
```

## Key Results

| Lemma | Location | Statement |
|---|---|---|
| `prod_error_bound` | `Analysis/Rounding` | `\|∏(1+δᵢ) - 1\| ≤ γ(n)` |
| `gamma_mul` | `Analysis/Rounding` | `γ(j)·γ(k) + γ(j) + γ(k) ≤ γ(j+k)` |
| `gamma_inv` | `Analysis/Rounding` | `\|1/(1+θ) - 1\| ≤ γ(2k)` when `\|θ\| ≤ γ(k)` |
| `fl_sum_error` | `Analysis/Summation` | Accumulated sum error ≤ γ(n)·Σ\|xᵢ\| |
| `dotProduct_error_bound` | `Algorithms/DotProduct` | `\|fl(xᵀy) - xᵀy\| ≤ γ(n)·Σ\|xᵢ\|\|yᵢ\|` (Higham §3.5) |
| `matVec_error_bound` | `Algorithms/MatVec` | `\|fl(Ax)ᵢ - (Ax)ᵢ\| ≤ γ(n)·Σⱼ\|Aᵢⱼ\|\|xⱼ\|` |

## Building

Requires [Lean 4](https://leanprover.github.io) with [Lake](https://github.com/leanprover/lean4/tree/master/src/lake).

```bash
lake build
```

Toolchain: `leanprover/lean4:v4.29.0-rc3`, Mathlib `v4.29.0`.

> **Note:** On a fresh clone, `lake build` may fail with a ProofWidgets build error. Run:
> ```bash
> curl -L https://github.com/leanprover-community/ProofWidgets4/releases/download/v0.0.90/ProofWidgets4.tar.gz \
>   -o /tmp/pw.tar.gz
> mkdir -p .lake/build/packages/proofwidgets
> tar xzf /tmp/pw.tar.gz -C .lake/build/packages/proofwidgets
> ```

## References

N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002.
