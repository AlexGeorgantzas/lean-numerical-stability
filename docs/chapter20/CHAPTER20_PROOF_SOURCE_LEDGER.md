# Chapter 20 Proof-Source Ledger

## Scope and gate

This ledger records proof sources used or materially reflected in the Chapter
20 development. Citations, Appendix hints, implementation contracts, and model
reviews are advisory until their mathematical content is proved in Lean.

The core proof-source gate is **PASS**. No external prose result or
target-bearing transfer contract is accepted as a Lean proof. In particular,
Theorem 20.7 is counted only through the concrete actual-trace producer
`higham20_7_sourceConstructed_actual_closed`, not through its older conditional
policy/component-budget API.

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
| Powell-Reid and Cox-Higham sources cited for Theorem 20.7 | Printed row-local `alpha_i`, `beta_i`, `phi`, pivot-position `j^2`, uniform source-order `n^2`, and row-sorting envelopes | `Higham20Theorem20_7ActualBackSub.lean` reconstructs the cited Cox-Higham analysis for the literal rounded pivoted stored-QR/RHS/back-substitution trace, including the actual matrix/RHS budgets, direct `Q Delta R` multiplier, source-coordinate transport, exact minimizer, and a common explicit dimension-only coefficient. The visible computed-diagonal premise is necessary by the compiled rounded-breakdown example. Independently, `Higham20RowSorting.lean` proves the separate exact row-sorting cap and `phi` invariance. | ROUTE ADOPTED AND LOCALLY PROVED (EXPLICIT-DOMAIN); SEPARATE PROSE ROW PROVED |
| Elden and Cox-Higham sources cited for Theorem 20.8 | LSE perturbation organization and first-order coefficient | `Theorem20_8.source_facing_firstOrder_plus_eps_sq_of_finalSmallnessThreshold` proves the displacement bound with an explicit quadratic term on a source-only local threshold | ADOPTED AND PROVED (EXPLICIT DOMAIN) |
| Cox-Higham source cited for Theorem 20.10 | Finite-precision GQR mixed/backward stability | Positive-block Part A/B endpoints are local. This split adds genuine rounded `p=0,q>0` ordinary-QR and `q=0,p>0` constraint-only Part A/B endpoints; both derive nonbreakdown from source rank and explicit unit-roundoff thresholds | ADOPTED AND LOCALLY PROVED (EXPLICIT-DOMAIN) |
| Bjorck/Paige sources and Appendix 20.5 | Qualitative MGS stability attribution and optional-exercise route | Literal rounded MGS, accumulated-polar and computed-Gram repairs, back substitution, and the Chapter 20 minimizer transfer are local. The p. 386 prose prints no bound, while Appendix 20.5 uses an unspecified `c_{m,n} u` coefficient | ATTRIBUTION-ONLY / OPTIONAL EXERCISE; EXTRA LOCAL COVERAGE RETAINED |
| Bjorck and related SNE/CSNE sources | Exact SNE/CSNE algorithms and rough forward-error prose | Exact algorithms are selected and proved; statements using unspecified `c_mn`, `lesssim`, or qualitative comparisons are deferred | PROVED OR DEFERRED |
| Mathlib and existing `LeanFpAnalysis` | Algebraic, analytic, matrix, norm, singular-value, QR, triangular-solve, Cholesky, and FP foundations | Reused through ordinary imports; final axiom audits permit only standard foundational axioms | REUSED |
| Rendered Chapter 20 and Appendix pages in `tmp/pdfs/` | Visual verification of formulas, signs, tags, Problems, and Appendix rows | Audit-only temporary material, not a proof artifact | ADVISORY |
| Oracle second-model consultation, slug `chapter20-theorem20-7-audit` | Independent audit of whether the earlier runtime endpoint matched the printed `alpha`/`beta`/`phi` theorem and identification of the smallest honest dependency plan | The audit correctly rejected the earlier weaker-scale closure and required pivot-position/source-order support plus a genuine rounded-feedback producer. The concrete actual-trace producer is now proved locally; the distinct row-sorting follow-on is also proved from an executable exact trace. No model assertion is used as a premise. | ADVISORY; VERIFIED DIAGNOSIS ADOPTED; PLAN LOCALLY COMPLETED |
| Oracle second-model consultation, slug `chapter20-minnorm-invariance`; Sun [1108], BIT 37(1):179-188 (1997) metadata/abstract | Audited the p. 404 domain and requested a constructive rank-deficient route | Reattachment recovered a strict-tall density route and a proposed square counterexample. The paper metadata confirms Sun's matrix-only, strict-tall setting. The counterexample was then independently derived and compiled locally; no external assertion was trusted as a Lean premise | ADVISORY ROUTE; VERIFIED SOURCE-DISCREPANCY CONCLUSION ADOPTED via `higham20_p404_square_source_discrepancy` |

## Named-result proof disposition

| Result | Printed proof status | Local disposition |
|---|---|---|
| Theorem 20.1 | Chapter proof; attainability cited | Exact full-column solution/residual inequalities proved. Approximate attainability remains attribution-only. |
| Theorem 20.2 | Derived in chapter | Printed componentwise and absolute-norm inequalities proved. Approximate attainability is not invented. |
| Theorem 20.3 | Problem 20.2 / Appendix 20.2 | Actual panel/RHS/back-substitution theorem proved on explicit gamma/nonbreakdown domain. |
| Theorem 20.4 | Proof omitted | `...theorem20_4_printed_total_perturbations` derives the transported triangular bounds from the exact QR relation, combines both with the panel witness, normalizes one shared nonnegative Frobenius-unit witness, and proves the printed matrix/RHS bounds and exact system; `PASS (EXPLICIT-DOMAIN)`. |
| Theorem 20.5 | Attribution; Problem 20.9 for alternative formula | Source-general tall-matrix formula, eigenvalue/singular-value bridge, and matrix-only limit proved at the final compiled APIs. |
| Lemma 20.6 | Full chapter proof | Proved locally, including both norm bounds. |
| Theorem 20.7 | Citation-only | `higham20_7_sourceConstructed_actual_closed` executes the actual rounded pivoted stored-QR, paired RHS transformation, and `fl_backSub`; derives the raw/prefix growth and local operation budgets; constructs the back-substitution and `Q Delta R` perturbations; returns the exact perturbed minimizer; and proves both printed uniform source-order envelopes with one explicit coefficient depending only on `fp,m`. It assumes gamma validity, the visible half-gamma guard, and nonzero computed diagonal, but no policy or target-bearing certificate. The separately inventoried p. 395 row-sorting prose is proved independently. **PASS (EXPLICIT-DOMAIN)**. |
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
| 20.5 | DO NOT ADOPT IN CORE | Optional exercise supporting only qualitative prose; Appendix uses an unspecified `c_{m,n} u` coefficient. Literal MGS transfer remains proved as extra coverage. |
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
| Adopted content | The dependency outline and rejection of the earlier weaker-scale closure. The 2026-07-19 repair follows that outline with a concrete actual-trace producer, derives the numerical budgets and `Q[dR;0]` transport, and packages a common data-independent coefficient. The old conditional endpoint remains historical infrastructure rather than closure evidence. |
| Lean/source verification | The PDF prints `alpha_i`, `beta_i`, `phi`, pivot-position `j^2`, a source-order `n^2` envelope, and then the separate row-sorting cap plus `phi` invariance. `higham20_7_sourceConstructed_actual_closed` proves the literal actual rounded execution at the uniform source-order surface; `Higham20RowSorting.lean` independently supplies the executable cap and literal-`phi`-invariance proof. |

## Trust result

No cited theorem, Appendix sentence, or model response is introduced as
`axiom`, `sorry`, `admit`, `unsafe`, or `opaque`. The final report records the
focused builds, placeholder scan, and representative `#print axioms` results.
The final Theorem 20.7 implementation theorem has no local trace-budget,
policy, readiness, residual, or target-bound assumption. Its visible gamma and
computed-nonbreakdown hypotheses are recorded as the honest explicit domain
rather than hidden or renamed as unconditional closure.
