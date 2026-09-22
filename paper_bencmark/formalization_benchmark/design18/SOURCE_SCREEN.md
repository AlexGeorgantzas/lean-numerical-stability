# Probabilistic twelve — source-side screening (draft)

Status: provider-free first pass; **not** an independent faithfulness decision
or admission to measurement. All page numbers below are PDF pages, one-based.
The exact frozen source PDFs and hashes are in `CORPUS_12.json`.

## Shared source contracts

Higham–Mary uses the standard relative-error arithmetic model and Model 2.1:
each operation's relative error is an independent, mean-zero random variable
bounded by unit roundoff `u`. The paper defines `gammaTilde_k(lambda)` in (2.1),
`P(lambda)` in (2.2), and `Q(lambda,m)=1-m*(1-P(lambda))` in (3.1). The source
does **not** claim that ordinary deterministic rounding actually satisfies
Model 2.1. Its theorem probabilities must therefore be conditional on that
model, not stated for every floating-point execution.

Hallman uses a different Model 2.1: independent, mean-zero summation errors
bounded by `u`. Its `lambda(delta)=sqrt(2*log(2/delta))` and `gammaTilde`
are defined in (2.1) and Lemma 3.2. The vector `s_n` in Theorem 3.3 is the
list of exact partial sums `s_2,...,s_n`, **not** the final scalar sum.

Castro et al. use stochastic rounding (SR) and `gamma_m(u)=(1+u)^m-1`.
The finite inequalities in Theorems 4.1–4.2 are the selected conclusions;
their accompanying big-O notation is explanatory asymptotic language and
must not replace the exact coefficients. Both relative-error conclusions
require the exact denominator to be nonzero; the status of that hypothesis in
the paper must be independently checked before a packet is frozen.

## Selected results and outstanding checks

| Task | Exact source location | Paper claim to retain | Source-side check |
|---|---|---|---|
| `HM19-2-4` | Thm. 2.4, (2.1)–(2.2), PDF p. 6 | For arbitrary signs `rho_i=±1`, the product of `(1+delta_i)^rho_i` differs from 1 by at most `gammaTilde_n(lambda)` with probability at least `P(lambda)` for every `lambda>0`. | Keep independence, mean zero, `|delta_i|<=u`, and `u<1`; no deterministic replacement. |
| `HM19-3-1` | Thm. 3.1, (3.2)–(3.3), PDF p. 8–9 | Dot-product backward representations perturbing `a` and `b`, componentwise bounded by `gammaTilde_n(lambda)`, with probability at least `Q(lambda,n)` for any evaluation order. | Check whether both representations are required on one common event. |
| `HM19-3-2` | Thm. 3.2, (3.7), PDF p. 9 | Rounded `(c−sum_{i<k} a_i b_i)/b_k` admits all `mu_0,...,mu_{k-1}` with `|mu_i|<=gammaTilde_k(lambda)` in the stated backward equation, probability at least `Q(lambda,k)`, for any evaluation order. | Bind nonzero divisor and exact equation; do not assume the desired perturbations in the run structure. |
| `HM19-3-3` | Thm. 3.3, (3.9), PDF p. 10 | Rounded `A*x` equals `(A+DeltaA)*x`, `|DeltaA|<=gammaTilde_n(lambda)*|A|` componentwise, probability at least `Q(lambda,m*n)`. | Preserve rectangular dimensions and rowwise event aggregation. |
| `HM19-3-4` | Thm. 3.4, (3.11)–(3.12), PDF p. 10 | Per-column backward representation and full matrix forward bound; the latter has probability at least `Q(lambda,m*n*p)`. | **Printed index mismatch:** (3.11) says `j=1:n` although `B` has `p` columns and proof combines `p` instances. Resolve whether target is (3.12) alone or the full theorem with an explicitly documented correction. |
| `HM19-3-5` | Thm. 3.5, (3.13), PDF p. 10–11 | Substitution for nonsingular triangular `T` yields `(T+DeltaT)*xhat=b`, `|DeltaT|<=gammaTilde_n(lambda)*|T|`, probability at least `Q(lambda,n*(n+1)/2)`. | Include triangular orientation or the source's any-orientation argument without restricting to one branch. |
| `HM19-3-6` | Thm. 3.6, (3.15), PDF p. 11 | If Gaussian elimination runs to completion, computed Doolittle factors satisfy `A+DeltaA=Lhat*Uhat`, `|DeltaA|<=gammaTilde_n(lambda)*|Lhat|*|Uhat|`, probability at least `Q(lambda,n^3/3+n^2/2+n/6)`. | Preserve run-to-completion and full output-factor link. |
| `HM19-3-7` | Thm. 3.7, (3.16), PDF p. 11–12 | Gaussian-elimination solution satisfies `(A+DeltaA)*xhat=b`, componentwise perturbation coefficient `3*gammaTilde_n(lambda)+gammaTilde_n(lambda)^2`, probability at least `Q(lambda,n^3/3+3*n^2/2+7*n/6)`. | Confirm exact coefficient and both triangular solves in the source contract. |
| `HM19-3-8` | Thm. 3.8, (3.17), PDF p. 12 | Completed Cholesky of SPD `A` satisfies `Rhatᵀ*Rhat=A+DeltaA`, `|DeltaA|<=gammaTilde_(n+1)(lambda)*|Rhatᵀ|*|Rhat|`, probability at least `Q(lambda,n^3/6+n^2/2+n/3)`. | Include SPD and run-to-completion; check the square-root-operation model. |
| `HALL21-3-3` | Thm. 3.3, (3.2), PDF p. 5 | Recursive summation forward error is at most `u*||[s_2,...,s_n]||₂*lambda(delta/2)*(1+gammaTilde_n(delta/2))` with failure probability at most `delta`. | Preserve `delta in (0,1)`, Model 2.1, and all-orders factor. |
| `CASTRO24-4-1` | Thm. 4.1, (4.1), PDF p. 8 | Pairwise-summation relative forward error is at most `K*sqrt(u*gamma_(2h)(u))*sqrt(log(2/lambda))` with probability at least `1-lambda`. | **Height concern:** theorem prints `h=floor(log₂ n)` while the illustrated ceiling split can have height `ceil(log₂ n)` when `n` is not a power of two. Do not silently restrict to powers of two or substitute another h. |
| `CASTRO24-4-2` | Thm. 4.2, (4.2), PDF p. 10 | Horner relative forward error is at most `K*sqrt(u*gamma_(4n)(u))*sqrt(log(2/lambda))` with probability at least `1-lambda`. | Verify coefficient/order convention, polynomial condition number, and stochastic execution model. |

The later [author-hosted HAL v3 PDF](https://hal.science/hal-04787542v3/file/main.pdf)
still prints `h=floor(log₂ n)` for Theorem 4.1 while describing the recursively
split tree. Thus the discrepancy is not resolved by swapping to that version.
This is a source concern, not yet a proved counterexample or permission to
weaken the selected statement.

## Admission rule

An independent source-contract pass must resolve every flagged item and verify
that the eventual Lean target covers the complete selected conclusion and domain.
These notes do not authorize a solver to assume a desired event or bound. An
unresolved or false source statement is a reported task-source incident, not
a negative library result and not permission to weaken the faithfulness audit.
