# Chapter 20 Proof-Source Ledger

## Scope

This ledger records the proof sources used or materially reflected in the
Chapter 20 Lean development. A citation, an Appendix hint, a generated proof
idea, or an implementation contract is not itself treated as a proof of a
stronger Lean theorem. The source inventory is
`docs/chapter20/CHAPTER20_SOURCE_INVENTORY.md`.

The Chapter 20 modular proof-source gate is **PASS**. All 12 named results pass
at their documented APIs, and all selected numbered equations are closed or
explicitly deferred. Literal Split 3B numerical producers are proved locally;
stronger printed compressions that still require upstream algorithm-analysis
hypotheses remain identified below without being treated as Chapter 20 proof
terms.

## Source Ledger

| Source | Exact role in Chapter 20 | Lean disposition | Trust status |
|---|---|---|---|
| Higham, 2nd ed., Chapter 20, printed pp. 381-406 | Primary statements, formulas, algorithms, constants, source generality, proof sketches, and exclusions | Compared against all 26 PDF pages and local theorem types; source-facing claims are classified row-by-row in the inventory | PRIMARY / ADOPTED OR CLASSIFIED |
| Higham, Appendix A, Chapter 20 solutions, printed pp. 565-567 | Proof routes for Problems 20.1-20.11, especially Theorem 20.3, MGS stability, (20.18)-(20.19), (20.21), KKT conditions, and the first-order specialization of (20.25) | Each solution row is individually inventoried; adopted steps must be proved locally | ADVISORY UNTIL LOCALLY PROVED |
| Higham Chapters 7-10, 12-13, and 19 | Pseudoinverse/condition facts, triangular and Cholesky solve analysis, iterative refinement, and Householder/MGS QR dependencies cited by Chapter 20 | Existing repository declarations are reused; no Chapter 20 axiom is introduced for them | REUSED; LOCAL THEOREM TYPES CONTROL |
| Wedin [1218, 1973], Theorem 5.1 and Section 6, as cited in Higham's Chapter 20 notes | Original perturbation theorem and approximate-attainability attribution behind Theorem 20.1 | The chapter's full-column proof route is reconstructed locally. For the stronger equal-rank/general-shape sentence on p. 402, `Higham20GeneralWedin.lean` proves the exact MP decomposition and a rational equal-rank counterexample to the printed (20.1) extension | CITED / NOT A LEAN PROOF; STRONGER SOURCE SENTENCE REFUTED LOCALLY |
| Stewart [1067, 1977, Thm. 2.3] and Stewart-Sun [1083, 1990, Lem. 3.3.5], cited on p. 400 | Nontrivial equality of the two cross-projection norms in Lemma 20.12 | `Higham20Lemma20_12.lean` proves the equal-rank `A,B,A^+,B^+` wrapper from Moore--Penrose certificates and local finite spectral/rank machinery; no external axiom is used | ROUTE ADOPTED AND LOCALLY PROVED AT THE ARBITRARY-EQUAL-RANK API |
| Walden, Karlson, and Sun [1203, 1995], as cited in Theorem 20.5 | Normwise LS backward-error formula and eigenvalue characterization | The finite-positive source-block formula, eigenvalue equivalence, and matrix-only limiting model are proved in `LSQRSolve.lean`; Problem 20.9 supplies the chapter's algebraic route | ADOPTED AND LOCALLY PROVED AT SELECTED APIs |
| Kielbasinski and Schwetlick attribution in Lemma 20.6 | Attribution for combining asymmetric augmented perturbations into one symmetric matrix perturbation | The chapter prints the proof; local projector-mixture and norm theorems prove the result | ATTRIBUTION ONLY; LOCALLY PROVED |
| Powell-Reid and Cox-Higham sources cited by Theorem 20.7 and Chapter 19.6 | Row-wise weighted-LS Householder QR perturbation envelopes and row-growth estimates | `PivotedStoredQRSplit3BNumericalContract` states only the literal-trace QR, RHS, and back-substitution transport bounds and contains no minimizer or returned-vector conclusion. `fl_pivotedStoredQR_returnedX_exactMinimizer_of_split3B` proves the complete Chapter 20 least-squares assembly from it. `Higham20Theorem20_7Runtime.lean` provides a fully instantiated literal producer: `pivotedStoredQR_split3B_numericalContract_runtime` bounds the matrix and RHS telescopes by finite sums of their local `Eseq` norms and transports the triangular correction with a final top-`R` norm scale; `fl_pivotedStoredQR_returnedX_exactMinimizer_of_runtime` is the direct exact-minimizer endpoint. This is an execution-derived exact-Real runtime certificate on an explicit `n > 0`, gamma-valid, nonzero-top-diagonal domain, not a Lean-executability claim. `Higham20Theorem20_7QdR.lean` formalizes the separate Cox--Higham (3.7) prefix route. `pivotedStoredQR_split3B_numericalContract_of_coxHigham` and its direct endpoint remain the stronger conditional printed producer from explicit forward-policy and component-budget hypotheses; optional row-sorting caps supply the source-row form. Formal counterexamples record the false strict-history, source-index, and unsorted same-row strengthenings. | LITERAL QR/RHS/BACK-SUBSTITUTION RUNTIME PRODUCER LOCALLY PROVED ON EXPLICIT DOMAIN; PRINTED COX--HIGHAM ROW-LOCAL COMPRESSION PROVED CONDITIONALLY FROM EXPLICIT FORWARD/LOCAL ARITHMETIC OBLIGATIONS |
| Elden and Cox-Higham sources attributed by Theorem 20.8 | LSE perturbation formula, KKT/null-space proof organization, and first-order coefficient | `Theorem20_8.source_facing_firstOrder_plus_eps_sq_of_finalSmallnessThreshold` reconstructs the local KKT inverse argument, derives perturbed ranks, and proves the actual displacement bound with the printed coefficient plus an explicit quadratic term | ADOPTED AND LOCALLY PROVED (EXPLICIT LOCAL DOMAIN) |
| Cox-Higham source cited for Theorem 20.10 | Finite-precision generalized-QR mixed/backward stability theorem | `Higham20Theorem20_10.lean` proves the same named concrete computed vector satisfies the Part (a) mixed-stability and Part (b) backward-error conclusions under an explicit source-rank/unit-roundoff domain, with conservative gamma envelopes | ADOPTED AND LOCALLY PROVED (EXPLICIT-DOMAIN) |
| Bjorck/Paige and related sources cited in Section 20.3 and Appendix solution 20.5 | Forward, normwise backward, and columnwise stability of the MGS LS method | `Higham19Alg12MGSRounded.lean` implements the literal rounded Algorithm 19.12 loop, telescopes the local trace errors, and proves an accumulated-polar `ModifiedGramSchmidtGlobalRepair`. `Higham19Alg12MGSRepair.lean` turns an independent computed-Gram bound `<= gramCoeff*u` into the explicit coefficient `sum_j (localBudget_j + gramCoeff*u*||Rhat(:,j)||₂)/||A(:,j)||₂`. `Problem20_5.actualAugmentedMGSBackSub_end_to_end_accumulatedPolar` and `_localGram` fix the actual `[A b]` factors and `fl_backSub` return and prove the nearby exact minimizer result. The accumulated-polar route has no external repair premise on its explicit tall/full-pivot/positive-column and gamma-valid domain. The condition-number-independent printed `c3*u` strengthening is not inferred from this polar route. | LITERAL END-TO-END ACCUMULATED-POLAR ROUTE LOCALLY PROVED ON EXPLICIT DOMAIN; COMPUTED-GRAM ROUTE PROVED ON ITS VISIBLE GRAM-DEFECT DOMAIN; PRINTED `c3*u` PRODUCER REMAINS UPSTREAM |
| Bjorck and related SNE/CSNE sources cited in Section 20.6 | Seminormal/corrected-seminormal algorithms and rough forward-error discussion | Exact algorithm rows are selected separately; the rough `c_mn`/`lesssim` bound is deferred rather than sharpened by invention | CITED / DEFERRED OR OPEN |
| Mathlib and existing `LeanFpAnalysis` matrix, norm, singular-value, QR, Cholesky, triangular-solve, and FP machinery | Standard algebraic and analytic foundations plus implementation-backed computation paths | Reused through ordinary imports; source-facing wrappers must expose any nonbreakdown/model-validity hypotheses | REUSED |
| Rendered chapter and Appendix pages under `tmp/pdfs/` during the audit | Visual verification of tags, formulas, signs, source pages, Problems, and Appendix rows | Audit evidence only; temporary renders are not part of the formal proof | ADVISORY ONLY |
| GPT Pro / Oracle consultation attempts recorded in `docs/source_coverage/higham_ch20.md` | Requested review of difficult closure points | No substantive mathematical output was obtained or adopted | REJECTED / NO OUTPUT |

## Named-Result Proof Status

| Selected result | Printed proof status | Local proof-source disposition |
|---|---|---|
| Theorem 20.1 | Chapter proof in Section 20.10; attainability cited externally | Local full-column Wedin route and compiled combined wrapper prove the source inequalities. The legacy contract is not used as proof; approximate attainability remains an attribution-only prose boundary. |
| Theorem 20.2 | Chapter derivation from augmented-system inverse | Locally proved for exact minimizers under the printed full-rank/componentwise assumptions. |
| Theorem 20.3 | Proof delegated to Problem 20.2 / Appendix p. 566 | Concrete actual-panel/RHS/back-substitution endpoint is compiled under explicit gamma-validity and computed-diagonal nonbreakdown guards. |
| Theorem 20.4 | Proof omitted as tedious | Locally proved at an explicit full-rank-plus-computed-nonbreakdown domain. The omitted source proof is not supplied by citation. |
| Theorem 20.5 | Attribution/statement; Problem 20.9 proves alternative formula | Locally proved at finite-positive, eigenvalue, and matrix-only limiting APIs. |
| Lemma 20.6 | Full proof in chapter | Locally proved, including Frobenius and operator-2 bounds. |
| Theorem 20.7 | Citation-only | `fl_pivotedStoredQR_returnedX_exactMinimizer_of_split3B` proves the exact-minimizer assembly from `PivotedStoredQRSplit3BNumericalContract`, an honest numerical-only interface with no target-equivalent field. `fl_pivotedStoredQR_returnedX_exactMinimizer_of_runtime` now instantiates that path for the actual literal QR/RHS/back-substitution execution using conservative local-`Eseq`/top-`R` scales and no Cox--Higham row-policy or component-budget premise. The conditional printed producer separately exposes the forward alpha/beta scales, two-scale RHS transport, primitive component coefficients, and optional row-sorting cap. The theorem is **PASS (CH20 ASSEMBLY / LITERAL RUNTIME PRODUCER; EXPLICIT-DOMAIN; SOURCE-COORDINATE CORRECTION)**. Formal counterexamples reject false strict rounded sigma history, source-index relabeling of the pivot-position `j^2` factor, and universal same-row scaling for the unsorted trace; corrected source-coordinate endpoints use `n^2`. |
| Theorem 20.8 | Citation-only first-order theorem | `Theorem20_8.source_facing_firstOrder_plus_eps_sq_of_finalSmallnessThreshold` constructs the rank-tolerant pseudoinverse, derives both perturbed rank conditions, and proves the actual relative displacement is the printed first-order coefficient plus an explicit quadratic term on one source-only local threshold. |
| Theorem 20.9 | Full chapter proof | Exact constructed GQR existence, shapes, solve, and nonsingularity equivalence are locally proved. |
| Theorem 20.10 | Citation-only | The compact same-`computedX` Part A/Part B endpoints compile through the aggregate import and prove the printed conclusion shapes on their visible nondegenerate unit-roundoff domain. |
| Lemma 20.11 | Short proof invokes a standard singular-value perturbation result | `higham20_lemma20_11_equalRank_pseudoinverse_op2_le` proves the arbitrary-equal-rank result, including rank zero, from Moore--Penrose certificates and the repository's complexified real-matrix rank surface. The needed pseudoinverse norm identity and all-index singular-value perturbation route are local proofs. |
| Lemma 20.12 | One inequality proved; equality cited to external projection-angle results | `higham20_lemma20_12_equalRank_moorePenrose` proves the exact arbitrary-equal-rank `A,B,A^+,B^+` source theorem, including the zero-row case. |

## Appendix Proof-Source Decisions

| Appendix row | Adoption decision | Reason |
|---|---|---|
| 20.1 | ADOPT | Required normal-equation/geometric dependency; proved locally. |
| 20.2 | ADOPT | Primary proof source for selected Theorem 20.3; its actual-panel/RHS/back-substitution route is locally proved on the explicit algorithm domain. |
| 20.3 | ADOPT | The Appendix hint is expanded into a local compact-SVD construction, the four Penrose equations, uniqueness, and involution in `Higham20Problem20_3.lean`. |
| 20.4 | DO NOT ADOPT IN CORE | Optional Problem 20.4 is not selected. |
| 20.5 | ADOPT | The literal rounded Algorithm 19.12 state now constructs an accumulated-polar `ModifiedGramSchmidtGlobalRepair`; the actual augmented `[A b]` factors, literal `fl_backSub` return, and Appendix perturbation/minimizer transfer are end-to-end. A computed-Gram variant exposes only `||I-QhatᵀQhat||_F <= gramCoeff*u`. The stronger printed `c3*u` coefficient remains upstream. |
| 20.6 | DO NOT ADOPT AS A TARGET | Optional consequence; underlying numbered equations remain selected. |
| 20.7 | ADOPT | Proof source for selected (20.18)-(20.19); locally formalized at the selected singular-value API. |
| 20.8 | DO NOT ADOPT AS A TARGET | Optional specialization; the broader matrix-only limit is selected. |
| 20.9 | ADOPT | Proof source for selected (20.21); locally formalized. |
| 20.10 | ADOPT | Selected KKT characterization; locally proved instead of trusting the word "standard." |
| 20.11 | ADOPT | The unconstrained coefficient reduction is proved locally and composes with the closed source-facing Theorem 20.8 endpoint. |

## Selected Proof-Source and Integration Boundaries

| Claim | Why citation alone is insufficient | Required local closure |
|---|---|---|
| Approximate attainability in Theorems 20.1 and 20.2 | No construction/proof is printed in the chapter | Classified as an attribution-only prose boundary; it is not a selected gate blocker. |
| MGS stability sentence and Problem 20.5 | Citation alone cannot supply either the literal rounded accumulation or the printed constant | The literal state-to-global-repair accumulation/polar construction and Chapter 20 transfer are closed, including a computed-Gram `gramCoeff*u` endpoint. Upstream work is now limited to the stronger condition-number-independent Theorem 19.13 `c3*u` coefficient. |
| Theorem 20.7 | Citation alone cannot supply the three Cox--Higham numerical trace bounds, and the strict sigma history, source-index `j^2` relabeling, and unsorted same-row initial-scale strengthening are formally false | Chapter 20 assembly is closed at `PivotedStoredQRSplit3BNumericalContract`, and the execution-derived exact-Real runtime producer now closes the literal QR/RHS/back-substitution path on its explicit nonbreakdown/gamma-valid domain without row-policy or component-budget premises. The printed `alpha`/`beta` producer remains a stronger conditional specialization from explicit forward-policy and local component-budget obligations; row sorting is a separate optional cap. `j^2` stays in pivot coordinates and source coordinates use `n^2`. |
| p. 385 zero-`Delta b` variant | The source citation does not itself discharge invertibility and graph bounds | Closed locally: `metricGraphSmallness_of_frobNorm_le` derives the certificate from `rho < 1` and metric-defect `< 1`, and the scalar-smallness endpoint proves the actual matrix-only result for every RHS. |

## Trust Result

No external prose result listed above is accepted as a Lean axiom. The local
files use ordinary repository and Mathlib declarations. The final consolidated
dependency audit of representative public endpoints reported only the standard
foundational axioms `propext`, `Classical.choice`, and `Quot.sound`. The
forbidden-token and whitespace audits also passed. The remaining items above
are stronger printed source constants or row-local compressions, not missing
no-placeholder literal producers or Chapter 20-owned selected proof gaps.
