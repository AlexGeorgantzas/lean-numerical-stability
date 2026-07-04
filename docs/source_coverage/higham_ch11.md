# Higham Chapter 11 Formalization Report — "Symmetric Indefinite and Skew-Symmetric Systems"

## Source and scope
- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002).
- Chapter: 11, "Symmetric Indefinite and Skew-Symmetric Systems" (printed pp. 213–229).
- Source file: `higham-split/sources/chapter-pdfs/1.9780898718027.ch11.pdf`.
- Mode: core.
- Parallel split: 2 (chapters 7–12).
- Planning documents consulted: blueprint, Split 2 section of `split_primary_contracts.md`, `chapter_index.md`.
- **Selected-scope gate: FAIL.** The chapter's four primary *theorems* (11.3, 11.4, 11.7,
  11.8) are backward-error / stability results whose Lean surfaces are currently
  **conditional-transfer interfaces**: they take the analytic backward-error bound as a
  hypothesis and restate it (`h : P ⊢ P`). Per the project honesty policy a conditional
  transfer does not close the stronger source row, so these rows remain **open**. The five
  *algorithms* (11.1, 11.2, 11.5, 11.6, 11.9) are modeled as honest decision predicates plus
  the genuinely-proved pivot-parameter and per-step growth lemmas listed below.

Primary Lean module: `LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean`
(chapter-label surface); reusable definitions and proofs in
`LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskyIndefinite.lean`.

## Completed selected targets (genuinely proved)
| Source item | Lean declaration(s) | File | Notes |
|---|---|---|---|
| Alg 11.1 α = (1+√17)/8 root of 4α²−α−1 | `bunch_parlett_alpha_root`, `higham11_1_bunch_parlett_alpha_root` | CholeskyIndefinite / Ch11 | exact algebraic identity |
| Alg 11.6 α = (√5−1)/2 root of α²+α−1 | `bunch_tridiagonal_alpha_root`, `higham11_6_bunch_tridiagonal_alpha_root` | " | exact algebraic identity |
| §11.1.1 1×1 multiplier bound `|c/e| ≤ 1/α` | `oneByOne_multiplier_bound`, `higham11_1_oneByOne_multiplier_bound` | " | **new this session**; derived from pivot test `α·ω ≤ |e|`; the honest content behind the `bunch_parlett_L_bound`/`bunch_kaufman` `‖L‖`-interfaces |
| §11.1.1 / §11.1.2 1×1 Schur step growth `|b−c₁c₂/e| ≤ (1+1/α)μ₀` | `oneByOne_schur_growth`, `higham11_1_oneByOne_schur_growth` | " | **new this session**; printed bound `|ã_ij| ≤ μ₀+μ₀²/μ₁ ≤ (1+1/α)μ₀`; mechanism behind ρₙ ≤ (1+α⁻¹)^{n−1} |
| §11.1.1 2×2 pivot det bound `det E ≤ (α²−1)μ₀²` | `twoByTwo_completePivot_det_bound`, `higham11_4_twoByTwo_det_bound` | " | **new this session**; printed `det(E) ≤ μ₁²−μ₀² ≤ (α²−1)μ₀²` |
| §11.1.1 2×2 pivot nonsingularity `|det E| ≥ (1−α²)μ₀²` | `twoByTwo_completePivot_absdet_lower`, `higham11_4_twoByTwo_absdet_lower` | " | **new this session**; α∈[0,1); printed `|det E| ≥ (1−α²)μ₀²` |
| §11.1.1 2×2 Schur step growth `|ã| ≤ (1+2/(1−α))μ₀` (eq 11.4) | `twoByTwo_schur_growth`, `higham11_4_twoByTwo_schur_growth` (+ helper `abs_triple_mul_le`) | " | **new this session**; inverse-block entries `≤ αK,K`, `K = 1/((1−α²)μ₀)`; with the 1×1 bound this gives both single-step growth bounds of §11.1.1 |
| §11.1.1 α-derivation: growth balance `(1+1/α)² = 1+2/(1−α)` ⟺ `4α²−α−1=0`; `0<α<1` | `growth_balance_of_root`, `bunch_parlett_growth_balance`, `bunch_parlett_alpha_pos`, `bunch_parlett_alpha_lt_one`, `higham11_1_growth_balance` | " | **new this session**; the printed derivation fixing `α = (1+√17)/8`; ties the two single-step growth bounds together |
| §11.1.1 growth-factor recursion `r n ≤ (1+1/α)ⁿ·ρ₀` from per-stage ratio `r(k+1) ≤ (1+1/α)·r k` | `geom_growth_iterate`, `higham11_1_growth_factor_recursion` | " | **new this session**; derives the printed `ρₙ ≤ (1+α⁻¹)^{n−1}` from the single-step bounds (induction, not assumed) |
| §11.1.1 printed inverse bound `|E⁻¹| ≤ K·[[α,1],[1,α]]`, `K=1/((1−α²)μ₀)` | `twoByTwo_inverse_entry_bounds`, `higham11_4_twoByTwo_inverse_entry_bounds` | " | **new this session**; entrywise bounds on `E⁻¹=d⁻¹[[e₂₂,−e₂₁],[−e₂₁,e₁₁]]`, derived from the determinant magnitude bound |
| §11.1.1 self-contained 2×2 growth (eq 11.4 with actual `E⁻¹`) | `twoByTwo_schur_growth_of_block`, `higham11_4_twoByTwo_schur_growth_of_block` | " | **new this session**; `\|ã\| ≤ (1+2/(1−α))μ₀` from pivot-block data alone — **no inverse-entry bounds assumed** |
| Eq (11.6) example factorization A = LDLᵀ (partial pivoting) | `higham11_6_partialPivotExample_factorization` | Ch11 | exact `fin_cases` algebra, ε≠0 |
| §11.3 skew-symmetric diag zero | `skewSymmetric_diag_zero`, `higham11_16_skew_diag_zero` | " | Aᵀ=−A ⇒ Aᵢᵢ=0 |
| Problem-support algebra 11.1/11.2/11.4/11.7/11.8/11.9 | `higham11_problem_11_*` (see file) | Ch11 | reusable symmetric/SPD/quasidefinite algebra; not exercise transcriptions |

## Source predicates / definitions (honest models, no assumed conclusions)
- Eq (11.1) block LDLᵀ spec `BlockLDLTSpec`; (11.2) `higham11_2_NonsingularPivotBlock`;
  (11.3) `higham11_3_symmetricSchurComplement`; (11.4) `higham11_4_twoByTwoSchurEntry`.
- Alg 11.1/11.2/11.5/11.6/11.9 decision predicates: `BunchParlettCompletePivotChoice`,
  `BunchKaufmanPartialPivotCase`, `SymmetricRookFirstPivotChoice`,
  `BunchTridiagonalPivotChoice`, `SkewBunchPivotChoice`, plus `PivotSize`, `BunchKaufmanCase`.
- §11.2 Aasen: `AasenSpec`, `IsSymTridiagonal`, eqs (11.10)–(11.15) `higham11_1{0,2,3,4,5}_*`.
- §11.3 skew: `IsSkewSymmetric`, `IsSkewBlockDiag`, `SkewBlockLDLTSpec`, eq (11.16)
  `higham11_16_skewSchurComplement`.

## Reused from repository
| Source concept | Existing declaration | File |
|---|---|---|
| SPD predicate, symmetric part, nonsym-posdef | `IsSymPosDef`, `symmetricPart`, `IsNonsymPosDef`, `nonsymPosDef_iff_symPartSPD` | Ch10 / Cholesky |
| Permutation predicate | `IsPermutation` | LU/GaussianElimination |
| 2×2 principal-minor positivity (SPD) | `higham10_problem_10_1_two_by_two_minor_pos` | Ch10 |

## Open selected-scope items (not-proved ledger)
These are the rows that keep the gate FAIL. Each is currently a conditional-transfer
interface (`hypothesis ⊢ same statement`); the *analysis* — full block-LDLᵀ / Bunch–Kaufman
floating-point backward-error derivation — is the missing foundation.

| Source label | Exact claim | Current Lean status | Missing foundation | Smallest next Lean theorem |
|---|---|---|---|---|
| Theorem 11.3 | block LDLᵀ backward error: `P(A+ΔA₁)Pᵀ = L̂D̂L̂ᵀ`, `(A+ΔA₂)x̂=b`, `|ΔAᵢ| ≤ p(n)u(|A|+Pᵀ|L̂||D̂||L̂ᵀ|P)+O(u²)` (eq 11.5) | `higham11_3_block_ldlt_backward_error_interface` (assumes the bound) | fl-model recursion for the block factorization + per-2×2 solve error (11.5) | fl error for one block-LDLᵀ step producing the componentwise `|ΔA| ≤ γ·|L̂||D̂||L̂ᵀ|` on a 2×2 pivot |
| Theorem 11.4 | Bunch–Kaufman normwise stability `(A+ΔA)x̂=b`, `‖ΔA‖_M ≤ p(n)ρₙu‖A‖_M+O(u²)` via `‖|L̂||D̂||L̂ᵀ|‖_M ≤ 36nρₙ‖A‖_M` | `higham11_4_bunch_kaufman_stability` / `..._solve_backward_error_interface` (assume) | remaining: the `36nρₙ` product bound [608,1997] + a factorization data structure discharging the per-stage ratio hypothesis for the computed matrices. The single-step growth bounds AND their geometric recursion `geom_growth_iterate` (⇒ `ρₙ ≤ (1+α⁻¹)^{n−1}`) are now proved. | a `cpState`-style recursion whose stage maxima satisfy `oneByOne_schur_growth`/`twoByTwo_schur_growth`, fed into `geom_growth_iterate` |
| Theorem 11.7 | Bunch tridiagonal normwise stability, `(A+ΔA₂)x̂=b`, `|ΔAᵢ| ≤ c·u·‖A‖` | `higham11_7_tridiagonal_backward_error_interface` (assumes) | tridiagonal block-LDLᵀ fl analysis | fl error for one 2×2 tridiagonal pivot step |
| Theorem 11.8 | Aasen componentwise backward error + `‖ΔA‖_∞ ≤ (n−1)²γ_{15n+25}‖T̂‖_∞` | `higham11_8_aasen_backward_error_interface` (assumes) | fl analysis of the Aasen recurrences (11.12)–(11.14) + solve chain (11.15) | fl error for the Aasen column update (11.14) |

Both single-step §11.1.1 element-growth bounds are now proved: the 1×1 step
`(1+1/α)μ₀` (`oneByOne_schur_growth`) and the 2×2 step `(1+2/(1−α))μ₀`
(`twoByTwo_schur_growth`), the latter resting on the proved determinant magnitude
bound `twoByTwo_completePivot_absdet_lower` and the length-2 inner product over the
inverse-block entries. What remains for Theorem 11.4 is the *recursion*: iterating
these per-stage bounds over the whole factorization to obtain the growth factor
`ρₙ ≤ (1+α⁻¹)^{n−1}`, plus the `36nρₙ` product bound and the floating-point solve
error — the foundation tracked in the ledger row above.

## Skipped items (reason codes)
| Source location | Summary | Reason |
|---|---|---|
| Ch 11 epigraphs (Bunch–Kaufman, Bunch quotes) | motivation | editorial |
| §11.1.2 "no example known to attain the bound", timing "≈40%" | empirical observation | empirical, no formalizable subclaim |
| §11.4 Notes and References, LAPACK/LINPACK pointers | historical / software | non-mathematical |

## Benchmark-reserved (identifiers only — NOT formalized as chapter work)
Problems 11.1–11.7, 11.9, 11.10 and Appendix A solutions 11.1, 11.3, 11.4, 11.7, 11.8, 11.9
are benchmark-reserved. Some independent, reusable symmetric/SPD/quasidefinite algebra facts
carry `higham11_problem_11_*` names; they are general lemmas (e.g. singular-principal-pivots ⇒
zero matrix, quasidefinite kernel-trivial), not transcriptions of the exercise tasks, and are
used only as chapter infrastructure.

## Hidden-hypothesis summary
- New lemmas (`oneByOne_multiplier_bound`, `oneByOne_schur_growth`,
  `twoByTwo_completePivot_det_bound`, `twoByTwo_completePivot_absdet_lower`,
  `twoByTwo_schur_growth`): all hypotheses are on the *data* (entry magnitudes
  `≤ μ₀/μ₁/ω`, pivot-acceptance `α·μ₀ ≤ |e|`, inverse-entry bounds `≤ αK,K` with the
  *equational* scale constraint `(1−α²)μ₀K = 1`, α range), never on the conclusion. The
  growth/determinant bounds are derived, not assumed. The self-contained corollary
  `twoByTwo_schur_growth_of_block` additionally *discharges* the inverse-entry
  hypotheses via `twoByTwo_inverse_entry_bounds`, so the 2×2 growth follows from the
  pivot-block data alone.
- Interface theorems (11.3/11.4/11.7/11.8): the analytic bound IS taken as a hypothesis and
  restated — this is exactly why those rows are logged OPEN, not closed.

## Verification
- Commands:
  - `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`.
  - `#print axioms` on the new declarations (`oneByOne_multiplier_bound`,
    `oneByOne_schur_growth`, `twoByTwo_completePivot_det_bound`,
    `twoByTwo_completePivot_absdet_lower`, `twoByTwo_schur_growth`, `abs_triple_mul_le`,
    and the `higham11_*` wrappers) → `[propext, Classical.choice, Quot.sound]`
    (no `sorryAx`, no custom axioms).
  - Placeholder scan `grep -nE 'sorry|admit|^\s*axiom |native_decide|unsafe '` over ch11 +
    CholeskyIndefinite → clean.
- New vs pre-existing warnings: **no new warnings** from the two edited files. The only build
  warnings are pre-existing in `HighamChapter10.lean` (an unused-simp-arg hint, one unused
  variable `hm`, and `Fin.coe_castAdd`/`Fin.coe_natAdd` deprecations).

## Documentation
- Inventory + report: `docs/source_coverage/higham_ch11.md` (this file).
- Not-proved ledger: the "Open selected-scope items" table above (4 primary theorems: 11.3, 11.4, 11.7, 11.8). The 2×2 growth sub-step listed there last session is now proved (`twoByTwo_schur_growth`).

## Open issues
- Gate is FAIL by design: Theorems 11.3/11.4/11.7/11.8 remain conditional-transfer
  interfaces. This session added the honest per-step §11.1.1 element-growth,
  multiplier, and determinant lemmas — **both** single-step growth bounds
  (`oneByOne_schur_growth` `(1+1/α)μ₀`, `twoByTwo_schur_growth` `(1+2/(1−α))μ₀`) and the
  2×2 determinant nonsingularity bound — the genuine building blocks of the Theorem 11.4
  growth-factor bound, all derived from the pivot-acceptance tests. Converting the
  interfaces to end-to-end proofs requires (i) the per-stage-to-`ρₙ` recursion, (ii) the
  `36nρₙ` product bound, and (iii) the block-LDLᵀ / Aasen floating-point backward-error
  foundation — a multi-session effort tracked in the not-proved ledger.
