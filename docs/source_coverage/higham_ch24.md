# Higham Chapter 24 Source Coverage

- Source: `References/1.9780898718027.ch24.pdf`, printed pp. 451-457.
- Audit: complete seven-page text and rendered-page inspection on 2026-07-16.
- Core status: **PASS**; see `docs/chapter24/CHAPTER24_SOURCE_INVENTORY.md`.

## Coverage map

- DFT and inverse DFT: `LeanFpAnalysis/FP/Algorithms/FFT/Higham24.lean`.
- Roots-of-unity inverse proof reused from:
  `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean`.
- Weight model and scalar (24.5) accumulation bound:
  `LeanFpAnalysis/FP/Algorithms/FFT/Higham24.lean`.
- Literal exact/rounded radix-2 recursion, source butterfly/Kronecker stages,
  complete (24.3) norm identities, computed-weight stage perturbation (24.4),
  bit-reversal DFT correctness, and conditional trace-to-bound assembly:
  `LeanFpAnalysis/FP/Algorithms/FFT/Higham24Radix2.lean`.
- Circulant structure, exact DFT diagonalization, the exact four-stage solver,
  and exact (24.8) algebra:
  `LeanFpAnalysis/FP/Algorithms/Circulant/Higham24.lean`.
- Theorem 24.1: PASS; `higham24_theorem24_1_stage_factorization` is the literal
  ordered stage-product/bit-reversal equality.
- Theorem 24.2: PASS on a nonvacuous explicit stage-execution domain.
- Equations (24.6)-(24.7): PASS on explicit matrix/solver execution domains.
- Theorem 24.3: PASS on an explicit asymptotic execution family with an actual
  `IsBigO` quadratic remainder.
- Problem 24.1: accounted-for optional exercise, excluded in core mode.

Evidence ledgers:

- `docs/chapter24/CHAPTER24_SOURCE_INVENTORY.md`
- `docs/chapter24/CHAPTER24_FORMALIZATION_REPORT.md`
- `docs/chapter24/CHAPTER24_NOT_PROVED_LEDGER.md`
- `docs/chapter24/CHAPTER24_PROOF_SOURCE_LEDGER.md`
