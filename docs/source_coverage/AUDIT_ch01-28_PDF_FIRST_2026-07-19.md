# Higham Chapters 1–28 — PDF-first closure audit (2026-07-19)

> **SUPERSEDED.** This report audited baseline
> `4d5f7ae00c1d45edadd7cab9dc7ce9f59caa6d40`, and its final `28 PASS`
> conclusion is not the result of the new independent rerun requested against
> remote `main`.  That rerun found obligations this report missed: the literal
> Theorem 9.7 classification, the complex source domains of Theorems
> 9.8--9.11, Algorithm 14.4's final divisions, Theorem 19.5's columnwise
> statement and (19.14), and a circular Chapter 12-to-22 refinement handoff.
> See `AUDIT_ch01-28_PDF_FIRST_RERUN_2026-07-19.md` for the authoritative
> corpus fingerprint, repairs, bridge audit, and verification record.

## Result

**Final gate: 28 PASS, 0 FAIL, 0 BLOCKED.**

This is a new audit of the remote `main` baseline
`4d5f7ae00c1d45edadd7cab9dc7ce9f59caa6d40`.  It does not inherit the
conclusions of an older audit or accept a coverage-ledger entry as evidence of
closure.  The chapter PDFs were treated as the source of truth, and the Lean
declaration types and implementation handoffs were checked again from that
baseline.

## Source corpus and audit method

The audited source corpus is the 28 files
`References/1.9780898718027.ch1.pdf` through
`References/1.9780898718027.ch28.pdf`: 7,102,905 bytes and 513 PDF pages.
The per-chapter page counts are:

```text
33 26 18 14 12 13 19 18 37 18 17 14 14 27
18 15 17 14 28 26  8 18 17  7 11 17 21 16
```

The PDF pass inventoried 165 named result headings in the chapter bodies and
585 numbered body-equation labels.  Literal theorem/equation identifiers were
then searched in the production tree and every miss was read in PDF context.
This caught, among other things, Theorem 9.7 being present in code but absent
from the old summary ledger.  Four named headings do not have a literal source
string in a declaration name—Theorems 12.1, 12.2, 25.1, and 25.2—but their
printed statements use undefined approximation/qualitative relations, so their
exact algebraic cores were checked and the indeterminate envelopes were not
invented.  Of the 585 equation labels, 511 have a literal-number trace and the
remaining 74 were individually classified from their PDF context; they are
proof intermediates, worked examples, qualitative/asymptotic displays, or
semantic encodings rather than silently omitted precise endpoints.

Text extraction was not trusted for fragile formulas.  Rendered pages were
visually checked, including Chapter 1 pp. 1–2; Chapter 7 pp. 7–8; Chapter 8
pp. 6 and 10; Chapter 10 p. 7 and p. 15; Chapter 11 p. 12; Chapter 18 p. 11;
Chapter 19 p. 20; Chapter 20 pp. 15 and 18; Chapter 25 pp. 3–4; and Chapter 28
pp. 7 and 12.  The existing ledgers were used only after the PDF inventory, as
navigation and cross-check material.

The strict gate used here is the repository chapter-formalization skill's core
mode:

- every selected precise named result, numbered equation, algorithm, and
  central prose claim needs a compiled source-strength endpoint;
- a premise that merely assumes the desired residual, error budget, growth
  bound, or execution certificate does not produce that claim;
- implementation-facing claims must start from the named rounded executor;
- normal mathematical domains (dimension, nonbreakdown, model validity) remain
  explicit, but numerical conclusions cannot be smuggled in as hypotheses;
- an undefined `≈`, `≲`, unquantified `O(·)`, qualitative observation, or
  unspecified algorithm is terminally classified
  `DEFER-MISSING-PRECISE-STATEMENT` rather than assigned an arbitrary meaning;
  and
- a false printed statement is terminal only when a compiled counterexample
  and the strongest faithful correction are both present.

Problems and exercises remain outside core mode unless a selected chapter
theorem consumes them.  This matters in Chapter 11: the local two-by-two solve
estimate explicitly assigned as Problem 11.5 remains a sanctioned local input,
but it cannot be used to assume the global rook-pivoting conclusion.

## Defects exposed by the fresh PDF pass

The remote baseline's headline “28 PASS” conclusion was too strong.  The fresh
pass exposed these nonterminal or incorrectly classified bridges before the
repairs in this audit:

- Chapters 1–9: Priest Algorithm 4.3's unstated assumptions; Chapter 7's SPD
  scaling/property-A/sparsity refinements, (7.25), and the certificate-free
  Rump theorem (7.26); Chapter 8's (8.10), bidiagonal inverse/Algorithm 8.13
  chain, and fan-in asymptotic bridge; and Theorem 9.15's normwise and
  componentwise source endpoints.
- Chapters 10–18: pivoted PSD Cholesky (10.21)–(10.28), the Mathias condition
  behind (10.29), the complex positive-definite growth argument (10.30), the
  global rook-pivot path in Algorithm 11.5, skew growth, (13.22),
  (15.2)–(15.6), and the source block form in (17.22).
- Chapters 19–28: the literal rectangular sequence in Lemma 19.3, actual
  rounded executors for Theorem 19.6/Lemmas 19.8–19.9/Theorem 19.10, the actual
  pivoted-QR/least-squares assembly for Theorem 20.7, Algorithm 22.2
  nonbreakdown, Chapter 26's coordinate sweep/complex Cardano/(26.8), and
  Chapter 27's sticky flags, gradual underflow, and mixed/internal-precision
  BLAS semantics.

The PDF comparison also found source-level defects or missing domains that may
not be repaired by silently strengthening a theorem: Chapter 7's same-`p` row
scaling sentence, the reversed inequality in Lemma 8.8, Algorithm 8.13's
uninitialized `y_i`, Theorem 10.8's omitted domain, Theorem 11.8 at `n = 1`,
Chapter 14's raw signed-determinant Hadamard-condition formula and LINPACK
residual statement, printed (15.4) under the normalized dual convention,
Chapter 20's post-Theorem-20.1 equal-rank
generalization, Theorem 21.3's `min` versus `inf`, the missing nonzero-branch
qualification after Cardano formula (26.5), Chapter 27's universal Smith
avoid-overflow wording, and several Chapter 28 normality/asymptotic claims.

## Repairs and source-faithful terminal classifications

The repair set adds or strengthens the following compiled producers.

- `HighamChapters1To9SourceClosure` and `Higham726Rump` supply the missing
  Chapter 7 scaling/(7.25)/(7.26), Chapter 8 inverse/fan-in, and Theorem 9.15
  chains.  The new Rump endpoint constructs its eigenpair certificate from the
  source hypotheses; callers no longer provide it.
- `Higham1014SourceSuccess`, `Higham1014SourceError`, and
  `Ch10PivotedPSDSourceClosure` start from the literal rounded pivoted-Cholesky
  executor.  The source condition (10.21) now yields execution success and the
  exact determinate (10.23)–(10.25) endpoint.  The unparameterized `O(u²)` in
  (10.22) is explicitly deferred.
- `Higham1029Source`, `HighamMathiasFirstBreakdown`, and `HighamMathiasSource`
  formalize the literal operator-2-norm form of (10.29), the first-zero-pivot
  contradiction, the source condition number, the sharp first-stage error, the
  Mathias perturbation/induction chain, and premise-free rounded-execution
  success under `24 n^(3/2) kappa_H(A) u ≤ 1`.
- `Ch10ComplexPositiveDefiniteSourceClosure` constructs no-pivot LU and the
  complete Schur trace directly from `B` and `C` SPD, then proves the printed
  growth factor `< 3`; no trace or growth conclusion is assumed.  The following
  phrase “perfectly normwise backward stable” gives neither a specified rounded
  complex operation order nor a quantitative constant and is classified
  qualitatively rather than
  misrepresented as the real-field `γ_n` theorem.
- `Higham11RookSourceClosure`, `Higham11RookExecutorAdapter`, and
  `Higham11RookExactTrace` construct the complete exact bounded-search trace,
  including its permutations, schedule, `L`, `D`, multiplier origins, block
  support, and global growth/product endpoint. `Higham11RookRoundedGap` then
  gives two compiled obstructions to transplanting that exact cap unchanged to
  the current rounded mixed executor: its terminal `2 x 2` predicate is
  vacuous, and an aligned legal division rounding already exceeds the printed
  exact Schur-growth bound. The exact theorem is retained; the false rounded
  strengthening is classified as a source/model discrepancy.
- The modifications to `BlockLU`, `Chapter15CondEst`, `PNormPowerMethod`,
  the new concrete `PNormPowerMethodGeneralP`,
  `Higham19Labels`, `Higham19Lemma9DisjointSweep`, and the new
  `Higham19Theorem10ActualMatrix`,
  `Higham20Theorem20_7ActualAssembly`, `Higham22`, `Higham26`, and `Higham27`,
  plus `Ch17SemiconvergentBlockFormSourceClosure`, provide the remaining
  block-LU, condition-estimation, QR/least-squares, Vandermonde, automatic-error,
  software-semantics, and stationary-iteration bridges listed above.

## Per-chapter gate

| Ch. | Gate | PDF-first conclusion |
|---:|:---:|---|
| 1 | PASS | Precise principles/examples retain compiled source endpoints. |
| 2 | PASS | Representability and total-rounding monotonicity are produced. |
| 3 | PASS | Dot-product, gamma, Frobenius/spectral, and rectangular-norm bridges are closed. |
| 4 | PASS | Neumaier is literal; Priest's precise operational strengthening is proved, while the book's unstated “reasonable assumptions” sentence is deferred. |
| 5 | PASS | Literal Horner/derivative/complex and inverse-product recurrences are closed. |
| 6 | PASS | The selected norm and perturbation functionals, including downstream consumers, are closed. |
| 7 | PASS / SOURCE-DISCREPANCY | Scaling/property-A/sparse refinements, (7.25), and certificate-free (7.26) are closed; the false same-`p` row-scaling form has a counterexample and dual-`q` correction. |
| 8 | PASS / SOURCE-DISCREPANCY | (8.10), bidiagonal/Algorithm 8.13, and literal fan-in chains are closed; the reversed/undefined source text is recorded and corrected. |
| 9 | PASS | Theorem 9.15's normwise source route is premise-free and its invalid componentwise shortcut is separated from the valid resolvent theorem. |
| 10 | PASS | Pivoted Cholesky, literal operator-norm (10.29), premise-free Mathias rounded execution, and exact complex growth are closed; imprecise `O(u²)`/qualitative envelopes are explicitly deferred. |
| 11 | PASS / SOURCE-DISCREPANCY | The exact bounded-search rook trace discharges origin, support, pivot, and growth premises. Compiled examples refute the unmodified exact growth cap for the present rounded mixed executor; the generic `BlockLDLTBackwardError` remains an explicit separate boundary. |
| 12 | PASS | Exact recurrence/convergence cores are closed; undefined `≈`/`≲` theorem envelopes are deferred. |
| 13 | PASS | The point-row scalar/block chain reaches exact (13.22)/(13.23). |
| 14 | PASS / SOURCE-DISCREPANCY | The actual finalized Gauss–Jordan executor is connected; the false raw signed-determinant Hadamard-condition formula and LINPACK residual statement have checked corrections. |
| 15 | PASS / SOURCE-DISCREPANCY | Concrete finite-dimensional real `l^p` norms and Holder duals give the literal rectangular full-rank (15.2)–(15.3) endpoints; (15.6) is closed, while printed normalized-dual (15.4) has a counterexample and faithful correction. |
| 16 | PASS | The supplied-factor rounded path is closed; the source gives no determinate QR/Schur iteration to invent upstream. |
| 17 | PASS | The source semiconvergent block form and spectral-radius bridge in (17.22) are constructed. |
| 18 | PASS | Exact (18.8) is closed; Theorem 18.2's discarded unspecified `O(ε²)` term is deferred. |
| 19 | PASS | Literal rectangular, pivoted stored-QR, and MGS executors reach their source rates. The canonical Givens matrix stage-fold constructs `Q`, `Rhat`, and `DeltaA` and proves Theorem 19.10's exact factorization and `m+n-2` columnwise bound without a residual or nonbreakdown premise. |
| 20 | PASS / SOURCE-DISCREPANCY | The actual pivoted QR/RHS/back-substitution trace closes Theorem 20.7; the false equal-rank generalization is recorded and corrected. |
| 21 | PASS / SOURCE-DISCREPANCY | Householder/Givens nonbreakdown and replay bridges are produced; the printed unattained `min` is corrected to `inf`. |
| 22 | PASS | Algorithm 22.2's actual divisors/nonbreakdown and the monomial-stage Theorem 22.4/Corollary 22.7 chain are closed. |
| 23 | PASS | Literal conventional and fast rounded multiplication endpoints and explicit remainders are closed. |
| 24 | PASS | The rounded FFT solver constructs its structured perturbation endpoint. |
| 25 | PASS | Precise bordered-eigenproblem and residual cores are closed; undefined approximation theorems are deferred and the false coefficient has a counterexample/correction. |
| 26 | PASS / SOURCE-DISCREPANCY | Coordinate sweep/exact line search and (26.8) are closed. The complex Cardano path constructs cube roots and reaches the original cubic on each nonzero branch; a compiled zero-branch example supplies the qualification missing after (26.5). |
| 27 | PASS / SOURCE-DISCREPANCY | Sticky flags, gradual-underflow subtraction, and mixed/internal BLAS precision are represented; the universal Smith overflow wording is corrected. |
| 28 | PASS | Precise Hilbert/Gaussian-QR/test-matrix rows are closed; false companion normality and overstrong asymptotic statements have checked corrections, while empirical/qualitative rows are deferred. |

## Cross-chapter bridges

The root-import graph was recomputed independently of the ledgers.  At the
audit working tree it contains 576 Lean modules under `NumStability`; 574 are
reachable from `NumStability`.  The only unreachable files are the two
pre-existing untracked scratch experiments
`TestMatrices/Higham28GinibreSignedIntegrability.lean` and
`TestMatrices/ScratchSigned.lean`.  They are not production modules and are not
staged by this audit.  Thus every tracked or newly selected production module,
including all sixteen new audit modules, is in the aggregate build.

The semantic bridge pass also followed downstream uses rather than merely
checking imports.  In particular:

- the universal Chapter 7 Rump producer feeds the source distance sandwich;
- Chapter 10's source condition feeds actual pivoted-Cholesky execution and
  then (10.23)–(10.25), rather than consuming a success certificate;
- Chapter 13's scalar first-step theorem feeds the block tableau;
- Chapter 17's orbit convergence constructs the block decomposition before the
  spectral-radius conclusion;
- the Chapter 19 canonical disjoint-stage executor supplies the local
  `gamma_6` residual, Pythagorean stage bound, accumulated matrix recurrence,
  and final `A + DeltaA = Q Rhat` source endpoint;
- Chapter 20's factor, RHS, and triangular-solve traces meet in one actual
  source endpoint; and
- Chapter 22's actual Stage-II nonzero denominators reach the factor/residual
  consumer.

## Verification

The final frozen tree passed all required gates:

```text
Chapter 11 exact-rook/rounded-gap focused build       3,060 jobs  PASS
Chapter 15 concrete general-p focused build           3,014 jobs  PASS
Chapter 19 actual matrix Theorem 19.10 focused build  3,077 jobs  PASS
NumStability.Algorithms                          4,356 jobs  PASS
NumStability                                     4,403 jobs  PASS
lake build (whole package)                            4,405 jobs  PASS
```

A fresh `#print axioms` harness sampled 22 new headline producers and
counterexamples across Chapters 7, 10, 11, 15, 17, 19, 20, 22, 26, and 27.
Every declaration reported exactly the standard Mathlib axioms `propext`,
`Classical.choice`, and `Quot.sound`; none reported a project axiom or
`sorryAx`.  Declaration scans found no `sorry`, `admit`, `axiom`, `opaque`, or
`unsafe` declaration in the production tree.

The root-import recomputation found 576 Lean files under `NumStability`, 574
reachable from `NumStability`, and precisely the two pre-existing untracked
Chapter 28 scratch experiments unreachable.  Thus all 574 production modules
are root-reachable.  The exact staging-set diff check passed, and a final remote
fetch immediately before commit confirmed that `origin/main` still named the
audited baseline `4d5f7ae00c1d45edadd7cab9dc7ce9f59caa6d40`.
