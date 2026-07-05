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
| §11.1 fl backward error of one 1×1 Schur step (toward Thm 11.3) | `fl_oneByOne_schur_step_error`, `higham11_3_fl_oneByOne_schur_step_error` | " | **new this session**; computed `fl(a−fl(fl(c₁/e)·c₂)) = (a−c₁c₂/e)+Δ`, `\|Δ\| ≤ γ₃(\|a\|+\|c₁c₂/e\|)` **derived** via `prod_error_bound` (standard model), not assumed — the atomic per-step ingredient of Thm 11.3 |
| §11.1 fl backward error of 1×1 pivot solve (Thm 11.3 / eq 11.5, s=1) | `fl_oneByOne_solve_backward_error`, `higham11_3_fl_oneByOne_solve_backward_error` | " | **new this session**; `x̂ = fl(b/e)` satisfies `(e+Δe)x̂ = b`, `\|Δe\| ≤ γ₁\|e\|` — **derived** 1×1 instance of the (11.5) block-solve perturbation hypothesis |
| §4.2 per-stage trailing fl backward error (Higham [608,1997]) | `fl_oneByOne_stage_trailing_error`, `higham11_3_fl_stage_trailing_error` | " | **new this session**; `l̂_i·e·l̂_j + fl(b−fl(l̂_i·c_j)) = b + Δ`, `\|Δ\| ≤ 2γ₃(\|b\|+\|c_i c_j/e\|)`, via `prod_error_bound` — the atomic (i,j) step of Thm 11.3's componentwise fl induction |
| §4.2 fl **trailing-block backward error** (inductive step of Thm 11.3) | `fl_blockLDLT_trailing_bound`, `higham11_3_fl_blockLDLT_trailing_bound` | " | **new this session**; recursive `L_S,D_S` within `Bs` of the computed Schur ⇒ `\|(L̂D̂L̂ᵀ)_{i+1,j+1} − A_{i+1,j+1}\| ≤ 2γ₃(\|A_{i+1,j+1}\| + \|A_{i+1,0}A_{0,j+1}/A00\|) + Bs i j`; combines the per-stage error with the recursion IH |
| §4.2 fl **pivot-row/col backward error** (other half of the stage) | `fl_blockLDLT_pivot_row_bound`, `fl_blockLDLT_pivot_col_bound` (+ `higham11_3_` wrappers) | " | **new this session**; `(L̂D̂L̂ᵀ)_{0,0} = A00` exactly, `\|(L̂D̂L̂ᵀ)_{0,j+1} − A_{0,j+1}\|`, `\|(L̂D̂L̂ᵀ)_{i+1,0} − A_{i+1,0}\| ≤ u·\|·\|` — **all four index cases** of the single 1×1-pivot fl assemble step now proved |
| §4.2 fl **one-stage all-index backward-error envelope** | `flBlockLDLTOneByOneStageBound`, `fl_blockLDLT_oneByOne_stage_bound`, `higham11_3_fl_oneByOneStageBound`, `higham11_3_fl_blockLDLT_oneByOne_stage_bound` | " | **new this session**; packages pivot entry, pivot row, pivot column, and trailing-block estimates into one `∀ I J` bound for a rounded 1×1-pivot assemble step, leaving only the recursive trailing envelope `Bs` explicit |
| §11.1 exact block-LDLᵀ step, eq (11.3) `s=1`: `∑ L·D·Lᵀ = A` | `oneByOne_step_factorization`, `higham11_3_oneByOne_step_factorization` | " | **new this session**; exact 1×1-pivot factorization identity (unit-lower-tri `L`, block-diag `D` with Schur complement) — the **exact base of Theorem 11.3's diagonal-pivoting recursion** (fl version adds `fl_oneByOne_schur_step_error`) |
| §11.1 exact block-LDLᵀ **inductive step**, eq (11.1)/(11.3) | `blockLDLT_assemble_step`, `higham11_3_blockLDLT_assemble_step` | " | **new this session**; trailing block factorized recursively (`L_S·D_S·L_Sᵀ = S`, IH) + 1×1 multipliers ⇒ assembled `∑ L·D·Lᵀ = A`; iterating gives the exact `PAPᵀ = LDLᵀ` recursion |
| §11.1 exact **full recursion**, eq (11.1)/(11.2): `∃ L D, ∑ L·D·Lᵀ = A` | `exact_blockLDLT_all_oneByOne`, `higham11_1_exact_blockLDLT_all_oneByOne` (+ `schurCompl`, `schurCompl_symm`, `AllOnePivots`) | " | **new this session**; symmetric `A` with all Schur-complement pivots nonzero ⇒ exact `LDLᵀ` (no-2×2-pivot case), by induction on `n` via `blockLDLT_assemble_step` — the exact factorization scaffold for Theorem 11.3 |
| Thm 11.4 constant, Higham [608,1997] eq (4.13): `(3+α²)(3+α)/(1−α²)² ≤ 36` | `bunch_kaufman_bound_const_le_36`, `higham11_4_bound_const_le_36` | " | **new this session**; the `36` in `‖\|L̂\|\|D̂\|\|L̂ᵀ\|‖_M ≤ 36nρₙ‖A‖_M` (α=(1+√17)/8) |
| Thm 11.4 constant, Higham [608,1997] (A.3): `(3+α²)/(1−α²) ≤ 6` (`\|E\|\|E⁻¹\|\|E\| ≤ 6\|E\|`) | `bunch_kaufman_pivot_norm_const_le_six`, `higham11_4_pivot_norm_const_le_six` | " | **new this session** |
| §11.1.2 1×1-pivot growth constant `1/α < 2` (Higham [608,1997]) | `bunch_kaufman_recip_alpha_lt_two`, `higham11_4_recip_alpha_lt_two` | " | **new this session**; `g_ij ≤ α⁻¹·max < 2·max` |
| α bounds `1/2 < α ≤ 5/7`, `α² = (α+1)/4` | `bunch_parlett_alpha_gt_half`, `bunch_parlett_alpha_le_5_7`, `bunch_parlett_alpha_sq` | " | **new this session**; supporting the Thm 11.4 constants |
| Eq (11.6) example factorization A = LDLᵀ (partial pivoting) | `higham11_6_partialPivotExample_factorization` | Ch11 | exact `fin_cases` algebra, ε≠0 |
| §11.3 skew-symmetric diag zero | `skewSymmetric_diag_zero`, `higham11_16_skew_diag_zero` | " | Aᵀ=−A ⇒ Aᵢᵢ=0 |
| §11.3 / Alg 11.9 skew 2×2 multiplier bound `|c/a₂₁| ≤ 1` | `skew_twoByTwo_multiplier_bound`, `higham11_9_skew_multiplier_bound` | " | **new this session**; from `|c| ≤ |a₂₁|` (pivot is max) — honest content behind `higham11_9_skew_L_entry_bound_interface` |
| §11.3 / Alg 11.9 skew Schur entry bound `|s| ≤ 3M` | `skew_twoByTwo_schur_entry_bound`, `higham11_9_skew_schur_entry_bound` | " | **new this session**; `s = a_ij − (a_{i2}/a₂₁)a_{j1} + (a_{i1}/a₂₁)a_{j2}` (printed formula); establishes `higham11_9_skewSchurEntryBound` |
| §11.2 Aasen recurrence eq (11.12) from `A=LH` | `higham11_12_aasen_diagonal_equation_of_product` | Ch11 | **new this session**; exact-arithmetic: unit-lower-tri `L` ⇒ `A i i = ∑_{j<i} L i j·H j i + H i i` |
| §11.2 Aasen recurrence eq (11.13) from `A=LH` | `higham11_13_aasen_subdiagonal_equation_of_product` | Ch11 | **new this session**; `k=i+1` ⇒ `A k i = ∑_{j≤i} L k j·H j i + H k i` — the Aasen recurrence structure (exact), toward Thm 11.8 |
| §11.2 Aasen band structure `H j i = 0` (`j>i+1`), from `H=TLᵀ` | `higham11_10_aasenH_band` | Ch11 | **new this session**; `T` tridiagonal + `L` lower-tri ⇒ `H` banded |
| §11.2 Aasen recurrence eq (11.14) next-column update from `A=LH` | `higham11_14_aasen_next_column_of_product` | Ch11 | **new this session**; `L k next = (A k i − ∑_{j≤i} L k j·H j i)/H next i` (`next=i+1`, `k≥i+2`, `H next i≠0`) — completes the exact Aasen recurrence trio (11.12)–(11.14) |
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
interface (`hypothesis ⊢ same statement`). **Update (2026-07-05):** the proofs are no
longer citation-blocked — Higham [608,1997] was obtained (see *External proof sources*
below), giving the full proof of Theorems 11.3/11.4. What remains is *formalizing* the
block-matrix backward-error **induction** (a large but now-unblocked, tractable effort);
this session proved the exact base case and the key constants.

| Source label | Exact claim | Current Lean status | Missing foundation | Smallest next Lean theorem |
|---|---|---|---|---|
| Theorem 11.3 | block LDLᵀ backward error: `P(A+ΔA₁)Pᵀ = L̂D̂L̂ᵀ`, `(A+ΔA₂)x̂=b`, `|ΔAᵢ| ≤ p(n)u(|A|+Pᵀ|L̂||D̂||L̂ᵀ|P)+O(u²)` (eq 11.5) | `higham11_3_block_ldlt_backward_error_interface` (assumes the whole conclusion) | **substantially advanced (all-1×1 case)**: proved the exact recursion (`exact_blockLDLT_all_oneByOne`), the component stage bounds, and the packaged all-index one-stage envelope (`fl_blockLDLT_oneByOne_stage_bound`, `higham11_3_fl_blockLDLT_oneByOne_stage_bound`). NOTE: (11.5) for 2×2 pivots = **Problem 11.5 (benchmark-reserved)** → stays a hypothesis. | prove the **full recursion** for the packaged one-stage envelope: needs the computed Schur complement **stored symmetrically** (real algorithm stores one triangle; fl Schur is not exactly symmetric), so the per-stage symmetry hypothesis holds at every level — then induct on `n` accumulating the componentwise bound |
| Theorem 11.4 | Bunch–Kaufman normwise stability `(A+ΔA)x̂=b`, `‖ΔA‖_M ≤ p(n)ρₙu‖A‖_M+O(u²)` via `‖|L̂||D̂||L̂ᵀ|‖_M ≤ 36nρₙ‖A‖_M` | `higham11_4_bunch_kaufman_stability` / `..._solve_backward_error_interface` (assume) | proof now available (Higham [608,1997] §4.3, eqs 4.11–4.14, appendix A). The **constants** are proved (`bunch_kaufman_bound_const_le_36` = eq 4.13's `36`, `..._pivot_norm_const_le_six` = A.3, `..._recip_alpha_lt_two`). Remaining: the entrywise `|L||D||Lᵀ|` block bound (4.11)–(4.12) + recursion into (4.14) via `geom_growth_iterate`. | assemble the per-pivot `\|E\|\|E⁻¹\|\|E\|`/`CE⁻¹` entry bounds (constants proved) over the `‖S‖_M ≤ ρₙ‖A‖_M` recursion into eq (4.14) |
| Theorem 11.7 | Bunch tridiagonal normwise stability, `(A+ΔA₂)x̂=b`, `|ΔAᵢ| ≤ c·u·‖A‖` | `higham11_7_tridiagonal_backward_error_interface` (assumes) | tridiagonal block-LDLᵀ fl analysis | fl error for one 2×2 tridiagonal pivot step |
| Theorem 11.8 | Aasen componentwise backward error + `‖ΔA‖_∞ ≤ (n−1)²γ_{15n+25}‖T̂‖_∞` | `higham11_8_aasen_backward_error_interface` (assumes) | remaining: **fl** analysis of the Aasen recurrences + solve chain (11.15). The **exact-arithmetic** recurrence identities (11.12), (11.13) are now proved (`higham11_12/13_aasen_*_equation_of_product`). | fl error for the Aasen column update (11.14), then the solve-chain error over (11.15) |

Both single-step §11.1.1 element-growth bounds are now proved: the 1×1 step
`(1+1/α)μ₀` (`oneByOne_schur_growth`) and the 2×2 step `(1+2/(1−α))μ₀`
(`twoByTwo_schur_growth`), the latter resting on the proved determinant magnitude
bound `twoByTwo_completePivot_absdet_lower` and the length-2 inner product over the
inverse-block entries. What remains for Theorem 11.4 is the *recursion*: iterating
these per-stage bounds over the whole factorization to obtain the growth factor
`ρₙ ≤ (1+α⁻¹)^{n−1}`, plus the `36nρₙ` product bound and the floating-point solve
error — the foundation tracked in the ledger row above.

## External proof sources
| Selected claim | Source and exact location | Role | Local Lean closure | Status |
|---|---|---|---|---|
| Theorems 11.3, 11.4 (proofs not in book ch.11) | N. J. Higham, *Stability of the diagonal pivoting method with partial pivoting*, SIAM J. Matrix Anal. Appl. 18(1) (1997) 52–65 = book ref **[608]**. Free: `nhigham.com/wp-content/uploads/2022/11/high97d.pdf`, MIMS EPrints 344. Obtained 2026-07-05 (Max authorized web pull). | full proof: paper Thm 4.1 = book 11.3 (componentwise induction §4.2, eqs 4.6–4.10), paper Thm 4.2 = book 11.4 (norm bound §4.3, eqs 4.11–4.14, appendix A.1–A.3) | constants formalized (`bunch_kaufman_bound_const_le_36` eq 4.13, `..._pivot_norm_const_le_six` A.3, `..._recip_alpha_lt_two`); exact base `oneByOne_step_factorization`; per-step fl `fl_oneByOne_schur_step_error`/`_solve_backward_error` | **partially formalized**; block-matrix induction remains (unblocked, large). Paper's (4.5) 2×2-solve backward error = book **Problem 11.5 (benchmark-reserved)** → stays a hypothesis. |
| Theorem 11.7 | N. J. Higham, *Stability of block LDLᵀ factorization of a symmetric tridiagonal matrix*, Linear Algebra Appl. 287 (1999) 181–189 = ref **[613]**. Free (NA report): `maths.manchester.ac.uk/~higham/narep/narep308.pdf`. Located 2026-07-05, not yet formalized. | tridiagonal block-LDLᵀ stability proof | — | located; formalization is later multi-session fl work |
| Theorem 11.8 | Higham **[612, 1999]** (Aasen backward error) — precise ref identified, free PDF not yet located | Aasen backward-error proof | exact recurrences (11.12)–(11.14) proved | to locate |

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

**Important scope note (Problem 11.5).** Problem 11.5 asks to prove that condition
(11.5) — `(E+ΔE)ŷ=f`, `|ΔE| ≤ (cu+O(u²))|E|` — holds for the 2×2 pivots when the
system is solved by GEPP or the explicit inverse. This is exactly the *hypothesis*
of Theorem 11.3. Because Problem 11.5 is benchmark-reserved, (11.5) for 2×2 pivots
must remain a **hypothesis** of any honest Theorem 11.3 formalization and must not be
proved as chapter work. The 1×1 instance of (11.5) is *not* the reserved problem
(1×1 pivots "involve no computation" per §11.3) and is proved as
`fl_oneByOne_solve_backward_error`; the atomic 1×1 Schur-update fl error
(`fl_oneByOne_schur_step_error`) is likewise general chapter infrastructure, not a
Problem transcription.

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
