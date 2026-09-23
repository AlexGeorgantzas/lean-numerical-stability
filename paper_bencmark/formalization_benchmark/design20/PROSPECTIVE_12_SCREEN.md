# Prospective twelve-task expansion screen (before Pilot 23 first-pair verdict)

This is a **priority-ordered screening queue, not an admitted corpus**. It was
written while Pilot 23's first pair was still running, before its paired
result. No task below may be timed until its PDF/source packet is hash-frozen,
an independent source review passes, a declaration-by-declaration content
collision check confirms that NumStability contains components but not the
selected result, and a full-domain private `sorry` skeleton compiles in the
frozen L environment. Source mismatches or absent direct components exclude a
task regardless of its expected performance. Correlated same-paper tasks
must be reported as such, not as independent replicates.

The first three are already admitted **development canaries** under
`ADMISSION_3.json`: `FAB19-EQ3.5`, `FAB19-EQ3.7`, `H20-8`.

Next priorities to reach twelve tasks, selected on source/component shape:

| Priority | Candidate result | Direct lower-level NumStability component to verify | Main admission risk |
| --- | --- | --- | --- |
| 4 | Rump 2012 Theorem 3.4, unrestricted-length round-to-nearest recursive-sum bound | `fl_recursiveSum`; floating-format operations | Must model genuine round-to-nearest and representable inputs, not only abstract `FPModel`; retain underflow allowance and no `nu<1` guard. |
| 5 | Rump 2012 Theorem 3.5, computable `ufp` sum-error bound | `fl_recursiveSum` used for original and absolute-value sums | `ufp` and sharpness are source conclusions, not unproved hypotheses; exact format model needed. |
| 6 | Rump 2012 Theorem 4.3, dot-product error estimate | `fl_dotProduct`, `fl_recursiveSum` | Preserve the additive underflow term, `(n+2)u <= 1`, and the computed absolute-product sum. |
| 7 | Blanchard–Higham–Mary 2019 equation (3.6), compensated FABsum | `fl_recursiveSum`, `fl_kahanSum` | Check the library Kahan variant matches Algorithm 2.1 and cover `b=1`, `b=n`. |
| 8 | Castaldo–Whaley–Chronopoulos 2008 Proposition 3.2, t-level superblock dot-product bound | `fl_blockDotProduct`, `fl_dotProduct`, `gamma` | Need exact integral-block domain and t-level algorithm, not merely the library's already-proved two-level bound. |
| 9 | Langlois–Louvet 2007 Theorem 4, CompHorner forward-error bound | `fl_hornerDesc`, `FastTwoSum` family where compatible | EFT-Horner/TwoProd are not in the library and must be defined without assuming the result; preserve no-underflow and floating coefficients/input. |
| 10 | Langlois–Louvet 2007 Theorem 7, condition-number criterion for faithful rounding | `fl_hornerDesc`, compatible EFT/rounding infrastructure | Preserve the full algorithm and faithful-neighbour semantics; inherited no-underflow condition must be checked. |
| 11 | Blanchard–Higham–Mary 2019 Theorem 4.1, FABsum inner product | `fl_dotProduct` for recursive block dot products, plus summation components | Keep the multiplication rounding and the exact Algorithm 4.1; do not reduce to an assumed abstract error contract. |
| 12 | Blanchard–Higham–Mary 2019 Theorem 4.2, matrix–vector **and** matrix–matrix products | `fl_dotProduct`/matrix infrastructure | Both conclusions of the labelled theorem are required; do not split into easy partial cases. |

Reserve in source-review order, only for an objectively excluded priority task:

1. Castaldo–Whaley–Chronopoulos 2008 section 3.1 fixed-three-level
   superblock forward-error claim. Its printed integral block assumptions and
   OCR-damaged coefficient need visual verification.
2. Carson–Higham 2018 three-precision iterative-refinement bounds. The exact
   selected theorem and a directly compatible NumStability algorithm remain
   unidentified; topical overlap alone is insufficient.
3. Blanchard–Higham–Mary 2019 Theorems 4.4–4.6 for triangular solve/LU. Their
   direct-use algorithm compatibility is not established.

Source PDFs checked so far:

- Blanchard, Higham, Mary, *A Class of Fast and Accurate Summation Algorithms*,
  [author PDF](https://eprints.maths.manchester.ac.uk/2729/3/paper.pdf),
  already pinned as `design20/sources/FAB19.pdf`.
- Rump, *Error Estimation of Floating-Point Summation and Dot Product*,
  [author PDF](https://www.tuhh.de/ti3/paper/rump/altRu11.pdf).
- Castaldo, Whaley, Chronopoulos, *Reducing Floating Point Error in Dot Product
  Using the Superblock Family of Algorithms*,
  [author PDF](https://www.cs.utsa.edu/~atc/pub/J42.pdf).
- Langlois and Louvet, *Faithful Polynomial Evaluation with Compensated Horner
  Algorithm*, [arXiv PDF](https://arxiv.org/pdf/cs/0610122), already pinned as
  `design20/sources/LL07-CompHorner.pdf`.
- Carson and Higham, *Accelerating the Solution of Linear Systems by Iterative
  Refinement in Three Precisions*,
  [author PDF](https://eprints.maths.manchester.ac.uk/2629/1/cahi18.pdf).

Initial text scan of the pinned NumStability snapshot found no `FABsum`,
`superblock`, `CompHorner`, `EFTHorner`, or `ufp` symbol/content hit. This is
only a negative keyword screen, not the required semantic collision review.
The library **does** already prove the postload two-level block-dot-product
bound from Castaldo et al. equation (2.2), so that result is explicitly
excluded. Rump Theorem 3.4 differs from NumStability's existing guarded
`gamma` forward-error bound; its unguarded round-to-nearest conclusion still
needs a full content review before admission.
