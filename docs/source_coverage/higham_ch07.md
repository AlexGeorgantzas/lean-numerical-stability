# Higham Chapter 7 Formalization Report — "Perturbation Theory for Linear Systems"

## Source and scope
- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002).
- Chapter: 7, "Perturbation Theory for Linear Systems" (printed pp. 119–133).
- Source file: `References/1.9780898718027.ch7.pdf`.
- Mode: core.
- Parallel split: 2 (chapters 7–12).
- Selected-scope gate: **PASS** (fresh audit and closure 2026-07-18). Theorem
  7.8 now has an attained-minimum (`IsLeast`) surface, equation (7.17) has its
  complete symbolic Kahan family and exact condition-number comparison, and
  equation (7.32) has an end-to-end arbitrary subordinate-norm calculus
  theorem. This supersedes the 2026-07-11 certification, which had classified
  (7.17) and (7.32) as skips contrary to the core-mode selection rule.

Primary Lean module: `NumStability/Analysis/HighamChapter7.lean`
(~26k lines, ~895 declarations); heavy perturbation proofs in
`NumStability/Analysis/PerturbationTheory.lean`.

## Primary labels (9)
| Source label | Status | Lean declaration(s) | Notes |
|---|---|---|---|
| Theorem 7.1 (Rigal–Gaches, normwise backward error, eqs (7.1)–(7.3)) | CLOSED | `theorem7_1_subordinate` (+`_necessary`/`_sufficient`); core `rigal_gaches` (PerturbationTheory); attaining perturbations `eq_7_3_subordinate_attaining_perturbations` | |
| Theorem 7.2 (normwise forward error, eq (7.4)) | CLOSED | `theorem7_2_subordinate_forward_error_bound` | |
| Theorem 7.3 (Oettli–Prager, componentwise backward error, eqs (7.7)–(7.9)) | CLOSED | `oettli_prager` (+`_necessary`/`_sufficient`, PerturbationTheory) | docstrings cite "Higham Theorem 7.3" |
| Theorem 7.4 (componentwise forward error, eq (7.10)) | CLOSED | `theorem7_4_absolute_forward_error_bound`; componentwise core in PerturbationTheory | |
| Theorem 7.5 (van der Sluis, column/row equilibration near-optimality) | CLOSED | `theorem7_5_p1_column_equilibration_isLeast_right_scalings`, `theorem7_5_p2_column_equilibration_le_sqrt_card_min_right_scalings_of_rect_left_inverse`, `theorem7_5_lp_*`, `theorem7_5_pinf_row_*` family | large family; supported by `eq_7_18`/`eq_7_20`/`eq_7_21` |
| Corollary 7.6 | CLOSED | `corollary7_6_cholesky_scaled_cond_le_card_sInf_symmetric_scalings` + `corollary7_6_cholesky_*` family | |
| Theorem 7.7 (Stewart–Sun, Frobenius scaling) | CLOSED | `theorem7_7_stewart_sun_frobenius_scaling` (+`_of_left_inverse`, lower bound) | |
| Theorem 7.8 (Bauer, two-sided scaling, eq (7.24)) | CLOSED | `theorem7_8_bauer_scaledInfKappaSet_isLeast_spectralRadius`; companion aliases `theorem7_8_bauer_scaledInfCondSet_sInf_eq_spectralRadius`, `theorem7_8_bauer_scaledInfKappaSet_sInf_eq_spectralRadius` | The attained-minimum theorem composes the irreducibility-to-positive-Perron-witness producer with the conditional `IsLeast` theorem, whose proof constructs the canonical diagonal scalings. Thus the formal surface states the printed minimum/attainment result directly; the older `sInf` aliases remain as companion formulations. The book delegates the proof to Problem 7.10, so the implementation legitimately lives in the `problem7_10*` family. |
| Lemma 7.9 (practical error bounds, eqs (7.28)–(7.29)) | CLOSED | `lemma7_9_componentwise_bound`, `lemma7_9_relative_infNorm_bound`, `lemma7_9_exact_for_residual_multiple` | neighbors `eq_7_30`, `eq_7_31` |

## Equations (7.1)–(7.33)
- Direct/labeled surfaces (26): (7.3), (7.4), (7.5), (7.9)–(7.23),
  (7.25), (7.26), (7.28)–(7.33) — via `eq_7_N*` declarations or
  docstring-cited surfaces in the two chapter files.
- (7.1), (7.2): the η definition and formula — inside Theorem 7.1's statement
  (covered by that row).
- (7.7), (7.8): the ω definition and formula — inside Theorem 7.3's statement
  (covered by that row).
- (7.24): Theorem 7.8's display (covered by that row).
- (7.27): §7.7 restatement of (7.2)+(7.8) — REUSE_EXISTING (same content as the
  Theorem 7.1/7.3 formulas).
- (7.6): a MATLAB experiment output (`1.00×10⁻¹⁰`) — SKIP (empirical).
- (7.17): **CLOSED** by `eq_7_17_kahan_symbolic_example` and the
  `ch7Kahan*` definitions. The explicit range `0 < ε ≤ 1/2` is a sufficient
  sign regime for the source's `0 < ε ≪ 1` assumption. The theorem proves
  `Ax=b`, a two-sided inverse, the displayed `|A⁻¹||A|`, and all three exact
  source values
  `κ∞(A)=2(1+ε⁻¹)`, `cond(A)=3+(2ε)⁻¹`, `cond(A,x)=5/2+ε`, and their strict
  comparison chain.
- (7.32): **CLOSED** by
  `eq_7_32_subordinate_differentiable_system`, with
  `eq_7_32_subordinate_from_differentiated_system` as its algebraic core.
  Coordinatewise `HasDerivAt` witnesses and `A(t)x(t)=b(t)` yield the
  differentiated system by the finite-sum product rule; the conclusion is the
  complete arbitrary subordinate-norm inequality-and-equality chain.

## Skipped items (reason codes)
| Source location | Summary | Reason |
|---|---|---|
| epigraphs, §7.1/§7.2 numerical examples, (7.6) | MATLAB experiments and fixed numerical output | empirical |
| §7.5 Extensions | survey of νₚ-measure, multiple-RHS, structured variants | survey prose; no owned primary label |
| §7.6 Numerical Stability | informal stability definitions, Table 7.2 | definitional prose (informal by the book's own choice) |
| §7.8 prose surrounding (7.32) | calculus-versus-algebra discussion | methodological prose only; exact display (7.32) is formalized |
| §7.9 Notes and References | history | non-mathematical ((7.33) `Pe = e` has a Lean surface: `IsStochasticMatrix`/`stochasticMatrix_mul_ones`) |

## Benchmark-reserved
Contract problem ledger for ch7: 7.1–7.6, 7.10–7.14 (benchmark-reserved).
Pre-existing `problem7_*` declarations exist throughout the chapter file
(~150, covering 7.1–7.11, 7.13, 7.15). Sampled docstrings uniformly wrap
general facts/building blocks and do not transcribe exercise statements.
Note: Problems 7.7, 7.8, 7.9, 7.15 are NOT in the reserved ledger, so their
surfaces are unrestricted. The `problem7_10*` family doubles as the proof of
primary Theorem 7.8 because the book delegates that proof to Problem 7.10;
this is recorded here as sanctioned overlap, now fronted by `theorem7_8_*`
aliases. These declarations predate the benchmark policy; recorded for
coordinator awareness, no action required.

## Verification (2026-07-18 repair)
- `lake build NumStability.Analysis.HighamChapter7`: PASS (3025 jobs);
  the attained-minimum Theorem 7.8 surface and the new (7.17)/(7.32)
  declarations type-check in the focused module rebuild.
- Hygiene: no `sorry`/`admit`/`axiom` in `HighamChapter7.lean` or
  `PerturbationTheory.lean`.
- `#print axioms` on `eq_7_17_kahan_symbolic_example`, both (7.32)
  declarations, and the attained-minimum Theorem 7.8 alias:
  `[propext, Classical.choice, Quot.sound]` only for each.

## Open selected-scope items
None.
