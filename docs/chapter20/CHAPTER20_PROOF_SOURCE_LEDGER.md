# Chapter 20 Proof-Source Ledger

## Scope and gate

This ledger records proof sources used or materially reflected in the Chapter
20 development. Citations, Appendix hints, implementation contracts, and model
reviews are advisory until their mathematical content is proved in Lean.

The core proof-source gate is **FAIL** because selected source-strength rows
remain open. No external prose result is accepted as a Lean axiom.

## External and repository sources

| Source | Exact role | Local disposition | Status |
|---|---|---|---|
| Higham, 2nd ed., Chapter 20, printed pp. 381-406 | Primary statements, equations, algorithms, constants, assumptions, examples, and empirical material | All 26 pages were read and compared with local theorem types; every named result, printed equation tag, Problem, and precise selected prose row is classified in the inventory | PRIMARY / ADOPTED OR CLASSIFIED |
| Higham, Appendix A, Chapter 20 solutions, printed pp. 565-567 | Proof routes for Problems 20.1-20.11 | Each row is inventoried separately; adopted steps must be locally proved | ADVISORY UNTIL PROVED |
| Higham Chapters 7-13 and 19 | Pseudoinverse, norm, triangular/Cholesky solve, iterative-refinement, Householder, and MGS dependencies | Existing `LeanFpAnalysis` declarations are reused; source-facing wrappers expose model-validity and nonbreakdown assumptions | REUSED |
| Wedin [1218, 1973], cited by Higham | Theorem 20.1 and the approximate-attainability attribution | The full-column inequalities are reconstructed locally. The stronger p. 402 equal-rank/general-shape sentence is refuted by a checked exact rational counterexample | CITED; CORE INEQUALITY PROVED; STRONGER SENTENCE REJECTED |
| Stewart [1067] and Stewart-Sun [1083], cited on p. 400 | Cross-projection norm equality in Lemma 20.12 | `higham20_lemma20_12_equalRank_moorePenrose` proves the arbitrary-equal-rank Moore-Penrose surface locally | ROUTE ADOPTED AND PROVED |
| Walden-Karlson-Sun [1203], cited in Theorem 20.5 | Weighted normwise LS backward-error and eigenvalue formula | Finite positive-`theta`, eigenvalue/singular-value, and matrix-only limit arguments are proved locally; the 2026-07-16 repair removes the former tall-matrix/full-row-rank mismatch | ROUTE ADOPTED AND PROVED AT THE FINAL COMPILED API |
| Kielbasinski-Schwetlick attribution in Lemma 20.6 | Combination of two augmented perturbations into one symmetric perturbation | The chapter proof is reconstructed locally, including Frobenius and operator-2 bounds | ATTRIBUTION ONLY; PROVED |
| Powell-Reid and Cox-Higham sources cited for Theorem 20.7 | Printed row-local `alpha_i`, `beta_i`, `phi`, pivot-position `j^2`, and row-sorting envelopes | Chapter 20 assembly and an exact literal runtime certificate are proved. The runtime scales are accumulated local residual/top-`R` quantities, not the printed compression. The printed producer remains conditional on explicit Chapter 19 row-policy/component-budget obligations | CITED; ASSEMBLY PROVED; PRINTED PRODUCER OPEN |
| Elden and Cox-Higham sources cited for Theorem 20.8 | LSE perturbation organization and first-order coefficient | `Theorem20_8.source_facing_firstOrder_plus_eps_sq_of_finalSmallnessThreshold` proves the displacement bound with an explicit quadratic term on a source-only local threshold | ADOPTED AND PROVED (EXPLICIT DOMAIN) |
| Cox-Higham source cited for Theorem 20.10 | Finite-precision GQR mixed/backward stability | Positive-block Part A/B endpoints are local. This split adds genuine rounded `p=0,q>0` ordinary-QR and `q=0,p>0` constraint-only Part A/B endpoints; both derive nonbreakdown from source rank and explicit unit-roundoff thresholds | ADOPTED AND LOCALLY PROVED (EXPLICIT-DOMAIN) |
| Bjorck/Paige sources and Appendix 20.5 | MGS forward/backward/columnwise stability | Literal rounded MGS, accumulated-polar and computed-Gram repairs, back substitution, and Chapter 20 minimizer transfer are local. The printed dimension-only, condition-number-independent `c3*u` producer is not derived | PARTIAL AT PRINTED STRENGTH |
| Bjorck and related SNE/CSNE sources | Exact SNE/CSNE algorithms and rough forward-error prose | Exact algorithms are selected and proved; statements using unspecified `c_mn`, `lesssim`, or qualitative comparisons are deferred | PROVED OR DEFERRED |
| Mathlib and existing `LeanFpAnalysis` | Algebraic, analytic, matrix, norm, singular-value, QR, triangular-solve, Cholesky, and FP foundations | Reused through ordinary imports; final axiom audits permit only standard foundational axioms | REUSED |
| Rendered Chapter 20 and Appendix pages in `tmp/pdfs/` | Visual verification of formulas, signs, tags, Problems, and Appendix rows | Audit-only temporary material, not a proof artifact | ADVISORY |
| Oracle second-model consultation, slug `chapter20-theorem20-7-audit` | Independent audit of whether the existing runtime Theorem 20.7 endpoint matches the printed `alpha`/`beta`/`phi` theorem and identification of the smallest honest dependency plan | Prompt supplied the printed statement, runtime/conditional interfaces, and Chapter 19 obstruction. After a browser disconnect, `oracle session ... --harvest` recovered the answer. It agreed that the runtime theorem is a different-scale result and that the printed producer remains open. Only conclusions independently checked against the PDF and Lean types were adopted | ADVISORY; VERIFIED CLASSIFICATION/PLAN ADOPTED |

## Named-result proof disposition

| Result | Printed proof status | Local disposition |
|---|---|---|
| Theorem 20.1 | Chapter proof; attainability cited | Exact full-column solution/residual inequalities proved. Approximate attainability remains attribution-only. |
| Theorem 20.2 | Derived in chapter | Printed componentwise and absolute-norm inequalities proved. Approximate attainability is not invented. |
| Theorem 20.3 | Problem 20.2 / Appendix 20.2 | Actual panel/RHS/back-substitution theorem proved on explicit gamma/nonbreakdown domain. |
| Theorem 20.4 | Proof omitted | The actual totals and systems are now packaged with a common-panel majorant plus the exact transported triangular term. Absorption of that term into each printed Frobenius-unit witness is still missing; `PARTIAL`. |
| Theorem 20.5 | Attribution; Problem 20.9 for alternative formula | Source-general tall-matrix formula, eigenvalue/singular-value bridge, and matrix-only limit proved at the final compiled APIs. |
| Lemma 20.6 | Full chapter proof | Proved locally, including both norm bounds. |
| Theorem 20.7 | Citation-only | Exact minimizer assembly and conservative literal runtime producer are proved. The unconditional printed Cox-Higham `alpha`/`beta`/`phi` producer is open; `PARTIAL`. |
| Theorem 20.8 | Citation-only | Printed first-order coefficient plus explicit quadratic remainder proved on a source-only local threshold. |
| Theorem 20.9 | Full chapter proof | `GeneralizedQRFactorization.exists_theorem20_9_exact_householder` now proves unconditional existence; rank assumptions are confined to the separate nonsingularity equivalence. |
| Theorem 20.10 | Citation-only | Positive-block Part A/B and both genuine rounded nontrivial empty-block boundary branches are proved on explicit source-rank/roundoff domains. |
| Lemma 20.11 | Short proof invokes a standard singular-value result | Arbitrary equal-rank Moore-Penrose theorem proved locally, including rank zero. |
| Lemma 20.12 | One inequality proved; equality cited | Arbitrary equal-rank cross-projection equality and `min` bound proved locally. |

## Appendix decisions

| Row | Decision | Local status |
|---|---|---|
| 20.1 | ADOPT | Normal-equation and residual-orthogonality iff theorems proved. |
| 20.2 | ADOPT | Theorem 20.3 actual implementation route proved on its explicit domain. |
| 20.3 | ADOPT | Compact-SVD Moore-Penrose construction, uniqueness, and involution proved. |
| 20.4 | DO NOT ADOPT IN CORE | Optional Problem 20.4 is inventoried and excluded. |
| 20.5 | ADOPT | Literal MGS transfer proved; the printed `c3*u` producer remains open, so the source row is `PARTIAL`. |
| 20.6 | DO NOT ADOPT AS A TARGET | Optional consequence; its numbered-equation dependencies are selected separately. |
| 20.7 | ADOPT WITH CORRECTION | The spectral basis and full minimization/attainment/max-lower-bound package are proved for `n<m`. A compiled square scalar counterexample shows the printed `sqrt(2)` lower envelope does not extend to `m=n`; the row is closed as **PROVED / SOURCE DISCREPANCY**. |
| 20.8 | DO NOT ADOPT AS A TARGET | Optional specialization; the broader matrix-only limit is selected. |
| 20.9 | ADOPT | WKS eigenvalue/singular-value conversion proved. |
| 20.10 | ADOPT | KKT characterization proved locally rather than trusted as “standard.” |
| 20.11 | ADOPT | Unconstrained coefficient specialization of Theorem 20.8 proved. |

## Oracle consultation record

| Field | Record |
|---|---|
| Theorem | Theorem 20.7, printed row-wise weighted-LS QR backward stability |
| Reason | The existing endpoint is long and exact for a literal computation, but its scales differ from the source; an independent type/source audit was requested before changing the gate. |
| Prompt summary | Compare the printed `alpha_i`, `beta_i`, `phi`, pivot-position `j^2`, and source-row `n^2` theorem with the runtime and conditional Lean surfaces; reject weaker-object closure; identify the smallest exact dependency plan. |
| Answer summary | The current named-row PASS is invalid. The literal runtime theorem and conditional assembly are honest at their own APIs, but use different scales or assume the missing producer. A source-exact closure needs pivot-position `j^2` with triangular column support, a genuine Cox-Higham row-specific producer for the literal trace, a dimension-only `gamma_tilde_m`, and source-rank-derived nonbreakdown. Row sorting is a later cap, not part of the named theorem. |
| Adopted content | The FAIL classification and the dependency outline above. The suggestion to preserve pivot-position indexing and use a permutation-aware source wrapper agrees with the local formal counterexample; the new `topR_row` theorem closes one small policy field. |
| Lean/source verification | The PDF prints `alpha_i`, `beta_i`, `phi`, pivot-position `j^2`, and the source-row `n^2` envelope. The runtime definitions instead use accumulated local errors/top-`R` norms; the conditional producer assumes row-policy/component budgets. `pivotPositionFactor_not_le_sourceColumnFactor_forall` forbids naive source-index relabeling, and `Theorem20_7.pivotedStoredQRTopR_abs_le_printedAlphaScale` verifies the newly discharged field. |

## Trust result

No cited theorem, Appendix sentence, or model response is introduced as
`axiom`, `sorry`, `admit`, `unsafe`, or `opaque`. The final report records the
focused builds, placeholder scan, and representative `#print axioms` results.
Open rows remain visible as open rows rather than hypotheses renamed as
closure.
