# Higham Chapter 14 Source Coverage Ledger

> **PDF-first rerun correction (2026-07-19): selected-scope gate PASS after
> repair.**  The previous operational bridge stopped before Algorithm 14.4's
> literal final componentwise divisions, so its “computed output” was not the
> output printed by the PDF.  `Ch14GJEFinalDivisionClosure.lean` now starts
> from `ch14ext_gjeFinalizedDivOutput`, proves the scalar `fl_div` residual,
> propagates it through the general-diagonal (14.29)--(14.30) identities, and
> derives the actual-output (14.31)--(14.32) pair and Theorem 14.5, with named
> exact higher-order remainders.  The fixed-run Corollary 14.6--14.7 adapters
> also use that output.  `ch14ext_cor146Finalized_vanishing_family_endpoint`
> and, in `Ch14Cor147FinalDivisionFamilyClosure.lean`,
> `ch14ext_cor147Finalized_vanishing_family_endpoint` prove the literal printed
> leading constants with named `O(u^2)` remainders for the same actual output,
> not for the pre-division state.  In Corollary 14.6 the leading residual term
> now uses the printed exact `‖x‖₂`; the actual-output/exact-solution norm
> correction is absorbed into a named remainder proved `O(u^2)` from the
> actual output's `O(u)` error.  Historical text below that calls the
> pre-division vector the literal Algorithm 14.4 output is superseded.

> **Fresh strict audit (updated 2026-07-19): selected-scope gate PASS.** The
> concrete structural-finalization producer is built and feeds the determinate
> (14.25)--(14.30) accumulation endpoints. The exact all-orders envelopes and
> every literal first-order coefficient used by Theorem 14.5 and Corollaries
> 14.6--14.7 are formalized. Only the book's unparameterized `O(u^2)` clauses
> and its qualitative general-`D` "negligible effect" sentence are classified
> `DEFER-MISSING-PRECISE-STATEMENT`; they do not fail the selected gate.

## Source and Scope

- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002).
- Chapter: 14, "Matrix Inversion". Mode: core. Split: 3A.
- Detailed inventories: `docs/chapter14/CHAPTER14_SOURCE_INVENTORY.md`, `docs/chapter14/CHAPTER14_NOT_PROVED_LEDGER.md`; Claude coverage note: `docs/source_coverage/higham_ch14_claude.md`. This file is the canonical top-level source-coverage ledger.
- **Selected-scope gate: PASS.** Lemmas 14.1-14.3, Algorithm 14.4, the executed
  matrix/RHS recurrences, structural zeroing, final diagonal, exact all-orders
  envelopes, and all determinate first-order constants are closed. No
  invented family, modulus, or diagonal-scaling error bound is used to replace
  the source's underspecified higher-order prose.

## Primary-label coverage

| Label | Status | Lean declaration(s) / module |
|---|---|---|
| **Lemma 14.1** / (14.8) — Method 2 triangular-inverse left residual | VERIFIED | `ch14ext_method2_left_residual`(`_normwise`), `Ch14Method2Loop.lean` — concrete reverse-column loop, `γ_{n+2}` |
| **Lemma 14.2** / (14.10)–(14.13) — Method 1B block right residual | VERIFIED | `ch14ext_method1B_whole_right_residual`(`_normwise`), `Ch14Method1BWhole.lean` — whole-matrix, any block partition, `γ_n` |
| **Lemma 14.3** — Method 2C block left residual | VERIFIED | `ch14ext_method2C_whole_left_residual`(`_normwise`), `Ch14Method2CWhole.lean` — whole-matrix N-block |
| **Algorithm 14.4** — GJE with partial pivoting | VERIFIED (spec + structure) | `GaussJordanPivoting.lean` (`ch14ext_pivotRow_max`, `ch14ext_perm_isPermutation`, `ch14ext_pivoted_multiplier_abs_le_one`, elimination = matmul) |
| **Theorem 14.5** / (14.31)–(14.33) — overall GJE residual + forward error | VERIFIED (determinate content); unparameterized source `O(u^2)` prose DEFER | `Ch14GJEFinalDivisionClosure.lean` begins with the literal componentwise `fl_div` output, derives (14.29), (14.30a-c), the exact (14.31)/(14.32) envelopes and (14.33) residual identity, and gives an explicit vanishing-roundoff family realization in which the named remainders are `O(u^2)`. The PDF itself does not state that family or its regularity hypotheses. |
| **Corollary 14.6** — SPD GJE forward stability | VERIFIED (determinate constants, symmetry-exploiting policy); unparameterized source `O(u^2)` prose DEFER | `ch14ext_cor146Finalized_vanishing_family_endpoint` proves the printed `8 n^3 u ‖A‖₂ ‖x‖₂` residual (exact solution norm) and `8 n^(5/2)` relative-forward coefficients for the literal final-division output. `Ch14Cor146UniformInverseBridge.lean` constructs the scaled-upper inverse from triangularity and positive pivots and derives its required `O(1)` regularity from SPD nonsingularity, the proved `O(u)` matrix perturbation, and continuity of finite-dimensional inversion; neither fact remains an independent family premise. The PDF's stated “symmetry is exploited” mode remains an explicit `symmetric_factor_relation` policy premise. |
| **Corollary 14.7** — row diagonally dominant GJE | VERIFIED (determinate constants); unparameterized source `O(u^2)` prose DEFER | `Ch14Cor147FinalDivisionFamilyClosure.lean` proves the printed `32 n^2` rowwise residual and `4 n^3 (kappa_inf(A)+3)` relative-forward coefficients for the literal final-division output; the computed/exact norm ratio is removed by an eventual bootstrap and both actual terminal remainders are `O(u^2)` under the displayed family hypotheses. `Ch14Cor147SourceDomainConstructor.lean` derives the fixed exact `L`, `U`, and `U⁻¹` witnesses directly from row diagonal dominance, nonsingularity, and dimension via the Chapter 9 Theorem 9.9 closure and the canonical upper-triangular inverse, so those witnesses are no longer extra source-domain inputs. |
| **Problem 14.14** — Hyman determinant backward error | VERIFIED | `ch14ext_hyman_flDet_backward_error_original`, `Ch14HymanDeterminant.lean` — exact fl-Hyman det of `H+ΔH`, `\|ΔH\| ≤ γ_{2n-1}\|H\|` |
| **Problem 14.15** — determinant perturbation bound | VERIFIED | `ch14ext_problem14_15_abs_det_add_rel_le_of_kappa2_opNorm2_inv_card_guard`, `Chapter14Problem1415Weyl.lean` — built the all-index Weyl singular-value perturbation bound from scratch |

## Equation coverage

(14.1)/(14.2) ideal residuals VERIFIED; (14.3) forward error with explicit `ε²` remainder VERIFIED; (14.4)–(14.7) Method 1 VERIFIED; (14.8) = Lemma 14.1; (14.10)–(14.13) = Lemma 14.2; (14.14) Method 2B instability CLOSED via explicit witness `Δ=[0,ε]`; (14.15)–(14.19) Methods A/B/C (conditional interfaces); (14.20)–(14.22) Method D exact algebra + `(4γ+2γ²)` envelope; (14.23) Method D left residual (with upper-tri-inverse certificate); (14.25)–(14.30) local recurrences, accumulated identities, computed-output forward error, and backward error VERIFIED for the structurally finalized trace (with the actual final `D`, and `I` on the source-normalized unit-diagonal input); (14.31)–(14.33) exact envelopes and literal first-order coefficients VERIFIED. Only the uninstantiated asymptotic `O(u^2)`/"negligible effect" clauses are `DEFER-MISSING-PRECISE-STATEMENT`.

## Honest-strength notes / residuals (non-gating)

- Corollary 14.6 is scoped exactly to the PDF's symmetry-exploiting variant.
  Its `symmetric_factor_relation` is deliberately not inferred from the generic
  rounded Doolittle executor: independent rounded divisions do not in general
  give the exact entrywise identity needed by that relation. Consequently the
  generic actual-Doolittle adapter is not advertised as an implementation of
  the symmetry-exploiting policy. Once that source policy relation and positive
  pivots hold, the scaled inverse, perturbed inverse, perturbation convergence,
  and uniform `O(1)` inverse bound are all derived rather than assumed.
- `ch14ext_gjeSourceComputedOutput` makes the returned vector definitionally
  equal to the recursively executed trace. Nonsingularity constructs the exact
  inverse and solve witnesses through
  `ch14ext_gjeCanonicalUpperInverse_isInverse` and
  `ch14ext_gjeCanonicalUpperSolve_exact`; their family boundedness reduces to
  boundedness of the canonical inverse.
- The dead-storage part of the finalization bridge is now closed by
  `ch14ext_gjeFinalizedSourceStepMatrix`: it writes the eliminated pivot-column
  entry as structural zero, preserves all other rounded operations, and
  `ch14ext_gjeFinalizedSourceStepMatrix_local_14_25` proves that this introduces
  no additional local error. The recursive producer ends at the actual
  diagonal `D` (`ch14ext_gjeFinalizedSourceTrace_final_diagonal`), derives the
  identity for unit-diagonal input, and feeds the existing accumulation through
  `ch14ext_gjeFinalizedSourceTrace_stage2_forward_error_14_29` and
  `...stage2_backward_error_14_30abc`.
- The remaining source text is intentionally deferred, not a gate blocker.
  On p. 274 Higham first derives
  (14.25)--(14.26), then says “without loss of generality” that the final
  diagonal `D` is the identity (all pivots are one), adding only that this has a
  “negligible effect” on the bound. Neither the pseudocode nor the proof gives
  a rounded scaling operation or a quantitative transfer from general `D`.
  The old literal-storage trace includes the eliminated column: for a legal
  multiplication-biased `FPModel`, the 2-by-2 successful trace leaves that
  dead stored entry equal to `-u`, not zero.
  `ch14ext_finalizationCounter_all_local_guards_but_not_identity` proves this
  while satisfying both gamma guards and pivot success. The new executor fixes
  exactly that storage issue rather than relabeling the old trace. Under the
  repository content-selection policy, inventing a family, modulus, or scaling
  budget would strengthen this underspecified prose. Accordingly those
  higher-order clauses are recorded as `DEFER-MISSING-PRECISE-STATEMENT`, while
  the determinate operational and first-order claims are closed.
- Method D's remaining upstream inputs (Thm 9.3 LU backward error for arbitrary A, fl-matmul) are proved elsewhere in the repo; the product-error is discharged.
- Cross-chapter role: consumes ch3 γ-calculus, ch8 triangular-solve backward error, ch9 LU (`LUBackwardError`), ch10 Cholesky (SPD Cor 14.6), ch6 Lemma 6.6 (SPD 2-norm); provides matrix-inversion backward/forward error used by condition-estimation (ch15) context.

## Verification

- `lake build NumStability.Algorithms.Ch14Cor146UniformInverseBridge
  NumStability.Algorithms.Ch14Cor147SourceDomainConstructor` succeeds on
  2026-07-19. `#print axioms` on both constructors and the new continuity
  bridge reports only `[propext, Classical.choice, Quot.sound]`.
- Fresh finalized-trace declarations compile directly on 2026-07-19;
  `#print axioms` on the local bound, final-diagonal/identity producer,
  recurrence bridge, (14.29), and (14.30a-c) reports only
  `[propext, Classical.choice, Quot.sound]`. Forbidden-token scan is clean.
