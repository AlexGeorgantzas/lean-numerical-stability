# Higham Chapter 24 Source Coverage

- Source: `References/1.9780898718027.ch24.pdf`, printed pp. 451-457.
- Audit: complete seven-page text and rendered-page inspection on 2026-07-16.
- Core status: **FAIL** only at Theorem 24.3's final structured first-order
  reduction; see
  `docs/chapter24/CHAPTER24_SOURCE_INVENTORY.md`.

## Coverage map

- DFT and inverse DFT: `LeanFpAnalysis/FP/Algorithms/FFT/Higham24.lean`.
- Roots-of-unity inverse proof reused from:
  `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean`.
- Weight model and scalar (24.5) accumulation bound:
  `LeanFpAnalysis/FP/Algorithms/FFT/Higham24.lean`.
- Literal exact/rounded radix-2 recursion, source butterfly/Kronecker stages,
  complete (24.3) norm identities, computed-weight stage perturbation (24.4),
  bit-reversal DFT correctness, and the literal Theorem 24.2 proof:
  `LeanFpAnalysis/FP/Algorithms/FFT/Higham24Radix2.lean`.
- Produced input-dependent rank-one form of (24.6), including the zero case,
  and both literal forward stages of (24.7):
  `LeanFpAnalysis/FP/Algorithms/Circulant/Higham24ForwardPerturbation.lean`.
- Literal complex-division diagonal scaling, conjugated-forward inverse FFT,
  and the composed actual four-stage rounded solver:
  `LeanFpAnalysis/FP/Algorithms/Circulant/Higham24Rounded.lean`,
  `Higham24InverseFFT.lean`, and `Higham24LiteralSolver.lean`.
- Exact DFT norm scaling and the quantitative backward-stability consequence:
  `LeanFpAnalysis/FP/Algorithms/Circulant/Higham24BackwardStability.lean`.
- Circulant structure, exact DFT diagonalization, the exact four-stage solver,
  and exact (24.8) algebra:
  `LeanFpAnalysis/FP/Algorithms/Circulant/Higham24.lean`.
- Theorem 24.1: PASS; `higham24_theorem24_1_stage_factorization` is the literal
  ordered stage-product/bit-reversal equality.
- Theorem 24.2: PASS for the literal rounded recursive executor.
- Equations (24.6)-(24.7): PASS with produced rank-one perturbations for the
  two literal forward FFT runs.
- Remaining rounded solver stages and their exact composition: PASS with
  produced `E` and `Delta3`, including the sharp inverse `n^-1 f(n,u)` budget.
- Backward-stability consequence after Theorem 24.2: PASS with equality of the
  relative input and output perturbation norms.
- Theorem 24.3: OPEN; the asymptotic execution family has an actual `IsBigO`
  remainder, but its solver perturbation split is not yet produced by the
  rounded four-stage implementation.
- Problem 24.1: accounted-for optional exercise, excluded in core mode.

Evidence ledgers:

- `docs/chapter24/CHAPTER24_SOURCE_INVENTORY.md`
- `docs/chapter24/CHAPTER24_FORMALIZATION_REPORT.md`
- `docs/chapter24/CHAPTER24_NOT_PROVED_LEDGER.md`
- `docs/chapter24/CHAPTER24_PROOF_SOURCE_LEDGER.md`
