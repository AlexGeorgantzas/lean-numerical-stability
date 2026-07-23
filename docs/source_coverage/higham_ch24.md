# Higham Chapter 24 Source Coverage

- Source: `References/1.9780898718027.ch24.pdf`, printed pp. 451-457.
- Audit: complete seven-page text and rendered-page inspection on 2026-07-16.
- Core status: **PASS**; see
  `docs/chapter24/CHAPTER24_SOURCE_INVENTORY.md`.

## Coverage map

- DFT and inverse DFT:
  `NumStability/Source/Higham/Chapter24/FourierTransform.lean`.
- Roots-of-unity inverse proof reused from:
  `NumStability/Algorithms/HighamChapter9.lean`.
- Weight model and scalar (24.5) accumulation bound:
  `NumStability/Source/Higham/Chapter24/FourierTransform.lean`.
- Literal exact/rounded radix-2 recursion, source butterfly/Kronecker stages,
  complete (24.3) norm identities, computed-weight stage perturbation (24.4),
  bit-reversal DFT correctness, and the literal Theorem 24.2 proof:
  `NumStability/Source/Higham/Chapter24/Radix2FFT.lean`.
- Produced input-dependent rank-one form of (24.6), including the zero case,
  and both literal forward stages of (24.7):
  `NumStability/Source/Higham/Chapter24/ForwardFFTPerturbation.lean`.
- Literal complex-division diagonal scaling, conjugated-forward inverse FFT,
  and the composed actual four-stage rounded solver:
  `NumStability/Source/Higham/Chapter24/RoundedDiagonalSolve.lean`,
  `InverseFFT.lean`, and `RoundedCirculantSolver.lean`.
- Exact DFT norm scaling and the quantitative backward-stability consequence:
  `NumStability/Source/Higham/Chapter24/FFTBackwardStability.lean`.
- Produced structured perturbations, exact rational radii, the printed
  first-order radius, and an explicit quadratic remainder coefficient:
  `NumStability/Source/Higham/Chapter24/StructuredMixedStability.lean`.
- A finite condition-number forward-error refinement, separated from the
  source's unspecified multiplier:
  `NumStability/Source/Higham/Chapter24/CirculantForwardError.lean`.
- Circulant structure, exact DFT diagonalization, the exact four-stage solver,
  and exact (24.8) algebra:
  `NumStability/Source/Higham/Chapter24/CirculantSystems.lean`.
- Theorem 24.1: PASS; `higham24_theorem24_1_stage_factorization` is the literal
  ordered stage-product/bit-reversal equality.
- Theorem 24.2: PASS for the literal rounded recursive executor.
- Equations (24.6)-(24.7): PASS with produced rank-one perturbations for the
  two literal forward FFT runs.
- Remaining rounded solver stages and their exact composition: PASS with
  produced `E` and `Delta3`, including the sharp inverse `n^-1 f(n,u)` budget.
- Backward-stability consequence after Theorem 24.2: PASS with equality of the
  relative input and output perturbation norms.
- Theorem 24.3: PASS; the literal solver produces `Δc`, `Δb`, and `Δx`,
  proves the exact structured equation, and satisfies
  `t*eta + 6u + O(u²)` with an explicit quadratic coefficient under the
  stated source/domain smallness conditions.
- Problem 24.1: accounted-for optional exercise, excluded in core mode.

Evidence ledgers:

- `docs/chapter24/CHAPTER24_SOURCE_INVENTORY.md`
- `docs/chapter24/CHAPTER24_FORMALIZATION_REPORT.md`
- `docs/chapter24/CHAPTER24_NOT_PROVED_LEDGER.md`
- `docs/chapter24/CHAPTER24_PROOF_SOURCE_LEDGER.md`
