# Chapter 23 Proof-Source Ledger

| Selected claim | Source location | Local route | Status |
|---|---|---|---|
| (23.2) Winograd identity | p. 434 | paired finite-sum algebra | PROVED |
| (23.4) Strassen formulas | p. 435 | exact seven-product block evaluator | PROVED |
| (23.5) operation counts | p. 435 | executable count recurrence and closed forms | PROVED |
| (23.6) Winograd--Strassen formulas | p. 436 | exact 15-addition block evaluator | PROVED |
| (23.7a)--(23.7b) | pp. 436--437 | exact tensor product/reconstruction and correctness predicate | PROVED one level |
| (23.8)--(23.9) 3M | pp. 437--438 | exact noncommutative three-product identity | PROVED |
| (23.10), (23.17) | pp. 438, 442 | actual rounded conventional matrix evaluator | PROVED with explicit quadratic remainder |
| (23.11), Miller | p. 438; cited result | import/reconstruct Miller's theorem for an actual finite rounded polynomial algorithm | OPEN |
| Theorem 23.1 / (23.12) | p. 439 | actual rounded Winograd inner product and factor expansion | PROVED |
| Theorem 23.2 / (23.14)--(23.16) | pp. 440--442 | actual rounded recursive Strassen evaluator plus the printed induction | PARTIAL: scalar 12/46 recurrence proved; theorem OPEN |
| Theorem 23.3 / (23.18) | pp. 442--443 | actual rounded recursive Winograd--Strassen evaluator plus induction | PARTIAL: scalar 18/89 recurrence proved; theorem OPEN |
| Theorem 23.4 / (23.19) | p. 443; Bini--Lotti citation | external constants/theorem and actual rounded bilinear recursion | OPEN; only parameterized coefficient algebra retained |
| (23.20)--(23.24) and scaling | pp. 445--446 | actual conventional/3M rounded evaluators and row-sum norms | PROVED |
| 23.B3 / Problem 23.6 | pp. 446, 449 | combine actual 3M and recursively rounded Strassen paths | PARTIAL coefficient / OPEN theorem |

The proof source was the rendered local PDF
`References/1.9780898718027.ch23.pdf`, especially pp. 438, 440, 442--443.
Exact algebra was checked with Lean's noncommutative ring normalization.
No synthetic first-order expansion or zero-error witness is counted as a
proof source.
