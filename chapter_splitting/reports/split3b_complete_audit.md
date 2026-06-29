# Higham Split 3B Complete Formalization Audit

This is the canonical from-scratch Split 3B audit requested before continuing
formalization work.  It follows
`chapter_splitting/skills/higham_chapter_formalization_shared_SKILL.md`; the
older `split3b_startup_audit.md` path is kept only as a compatibility pointer.

## Source and scope

- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002), verified from repository metadata and the chapter PDFs.
- Split: Split 3B of 4.
- Chapters: 16, 17, 18, and 19.
- Appendix A rows owned by Split 3B: solutions 16.1-16.4, 17.1, 18.1-18.2, and 19.1-19.14.
- Source files:
  - `References/1.9780898718027.ch16.pdf` (15 PDF pages)
  - `References/1.9780898718027.ch17.pdf` (17 PDF pages)
  - `References/1.9780898718027.ch18.pdf` (14 PDF pages)
  - `References/1.9780898718027.ch19.pdf` (28 PDF pages)
  - `References/1.9780898718027.appa.pdf`
- Mode: core.
- Planning documents consulted, in required order:
  - `chapter_splitting/HIGHAM_PARALLEL_FORMALIZATION_BLUEPRINT.md`
  - Split 3B section of `chapter_splitting/split_primary_contracts.md`
  - ch16-ch19 rows of `chapter_splitting/chapter_index.md`
- Repository-local instructions: no `AGENTS.md` file was found by `rg --files -g AGENTS.md`.
- Toolchain: `leanprover/lean4:v4.29.0-rc3`; Mathlib rev `v4.29.0`; package `LeanFpAnalysis`.
- Selected-scope gate: FAIL.  The complete split-owned row set is now accounted for in this audit, but many selected source rows remain open and only the priority Ch.19 QR contracts have source-facing wrappers.

## Audit method

This audit was rebuilt from the skill and planning documents rather than from
the prior partial summary.  It accounts for every split-owned primary label,
numbered equation ledger entry, problem row, and Appendix A solution row listed
in the Split 3B contract.  It also records the current local Lean candidate
foundations and the reason they do not yet close source rows.

PDF extraction was used for source navigation and spot checks.  Because formula
extraction mangles subscripts, hats, transposes, and matrix layouts, exact theorem
statement design still requires rendered-page inspection before proof work.  The
audit therefore distinguishes:

- `inventory-accounted`: the source row is owned and visible in this report;
- `candidate foundation`: local Lean declarations exist but have not been matched
  to the exact printed statement;
- `source-closed`: a local theorem matches the source statement and has compiled.

Two Split 3B QR outward rows now have compiled source-facing theorems:
`H19.Theorem19_4.householder_qr_backward_error` and
`H19.Theorem19_10.givens_qr_backward_error`.  The surrounding Ch.19 equation,
sign-convention, and exact printed-constant audits remain visible as weak
components, but the Split 4-facing Householder and Givens QR contracts are
exported.  The Ch.19 Gram-Schmidt/MGS workstream now also has compiled
source-facing Algorithm 19.11/19.12 state surfaces and a Theorem 19.13 contract
shape, plus an exact one-step-factor product recurrence and exact
`A = Q R` factorization for the `(19.33)` route, a source-facing
Householder-MGS vector bridge with `v_k^T v_k = 2` for `(19.28)` under an
explicit unit-column hypothesis, exact reflector symmetry and `P_k^2 = I`
under the corresponding self-dot condition, one-reflector padded-action lemmas
showing that `P_k [0; A]` produces the top dot-product row and bottom MGS
projection update, the diagonal scalar channel `q_k^T a_k^(k) = r_kk`, and
padded-stage endpoints `[0; A]` and `[R; 0]`, the exact one-step padded-stage
transition `P_k B_k = B_{k+1}`, the forward-prefix endpoint from `[0; A]`
to `[R; 0]`, the computed-column unit/self-dot dependency, and the exact
reverse one-step transition plus reverse-prefix endpoint for the reverse
orientation of the `(19.34)` route, with exact top/bottom block extraction
from that endpoint, plus the printed `[Delta A3; A + Delta A4]` perturbation
shape, generic top/bottom perturbation extraction with eta reassembly, row
reindexing to the `Fin (n + m)` Householder QR input shape, and
column-norm/bound transport into the stacked-column bound vocabulary,
Theorem 19.4 instantiation on the padded input, the block-form `(19.34)`
handoff theorem with the perturbed product equation and zero bottom `Rhat`
block, the economy-product extraction `A + Delta A4 = Q21 * R11`, the
top-block extraction `Delta A3 = P11 * R11`, the full block-data theorem,
block-column orthogonality identities for `P11` and `Q21`, the pre-repair
norm consequence from a `P11` bound to an economy-block Gram-residual bound,
common-`R` right-inverse algebra and norm bridge, exact Gram-residual expansion plus the
`2*delta + delta^2` operator-norm conversion, a conditional
source-output assembly bridge from common-`R` bounds, and the conditional
QR-sensitivity assembly bridge for Theorem 19.13, plus the source-shaped
Problem 19.12 correction-map algebra, including the CS-shaped factor bridge
from `P11 = U*C*W^T`, `P21 = V*S*W^T`, `Q = V*W^T`,
`F = V*T*U^T`, and `T*C = I-S` to `F*P11 = Q-P21`, a source-shaped
orthogonal-CS constructor deriving `Q` orthonormality and the unit `F` bound
from `U`/`W` orthogonality, `V` orthonormal columns, and `||T||_2 <= 1`,
diagonal CS scalar/algebra lemmas proving `||diag(c/(1+s))||_2 <= 1` and
`diag(c/(1+s))*diag(c) = I-diag(s)` from `c_i^2+s_i^2=1` and `s_i>=0`,
diagonal sine/cosine contraction proofs for `diag(s)` and `diag(c)`, and the
derived `P21 = V*S*W^T` and `P11 = U*C*W^T` contraction consequences,
a source-shaped diagonal CS factor-data payload with checked conversion to
pure correction-map data and Gram/contraction consequences, a
factor-payload-existence bridge to pure correction-map data existence, and
pure-data-existence fixed-budget source-output wrappers, plus determinant-
nonzero `R11` wrappers that recover the pointwise diagonal nonbreakdown
hypothesis from the full block-data upper-trapezoidal shape,
a diagonal-CS constructor deriving the correction-map contract directly from
diagonal `C`, `S`, and `T` data,
and the downstream repair theorem that turns the resulting bounded
`F * DeltaA3` correction into the repaired orthonormal common-`R`
factorization, plus repaired-perturbation budget lemmas that derive the
operator and columnwise bounds for `F*dTop + dBottom` from separate top and
bottom perturbation bounds and the unit correction-map bound.  The concrete
Householder handoff now also has diagonal-CS
source-output and small-unit-roundoff assemblies that feed this repair data
directly into the current `MGSQRBounds` route; the final stability theorem
`H19.Theorem19_13.mgs_qr_bounds` remains open.  A new hidden-hypothesis sanity
check, `mgsProblem1912_add_factor_gram_sum_not_dimension_free` with the H19
wrapper `H19.Theorem19_13.problem1912_add_factor_gram_sum_not_dimension_free`,
formally rules out the dimension-free target "Gram identity alone implies
additive Problem 19.12 witnesses"; the corrected target surface is now
compiled as `MGSProblem1912CSPolarInput` and
`H19.Theorem19_13.Problem1912CSPolarInput`, carrying `n <= m` plus the block
Gram identity before the remaining CS/polar theorem can be closed.  The actual
padded Householder economy blocks now feed this corrected input through
`MGSProblem1912CSPolarInput.of_paddedEconomy_blocks`,
`H19.Theorem19_13.problem1912_csPolarInput_of_paddedEconomy_blocks`, and
`H19.Theorem19_13.householder_paddedFinInput_csPolarInput`.  The corrected
input now also proves the block contractions
`MGSProblem1912CSPolarInput.p11_opNorm2Le_one` and
`MGSProblem1912CSPolarInput.p21_rectOpNorm2Le_one`, with H19 wrappers and
concrete padded Householder consequences for both economy blocks.  It also
exports the complementary Gram identities
`MGSProblem1912CSPolarInput.p21_gram_eq_id_sub_p11_gram` and
`MGSProblem1912CSPolarInput.p11_gram_eq_id_sub_p21_gram`, again mirrored by
H19 and concrete padded Householder wrappers.  The corrected input now also
exposes Gram symmetry and Gram commutation through
`rectangularGram_symmetric`, `rectangularGram_commute_of_add_eq_id`,
`MGSProblem1912CSPolarInput.p11_gram_symmetric`,
`MGSProblem1912CSPolarInput.p21_gram_symmetric`, and
`MGSProblem1912CSPolarInput.grams_commute`, again mirrored by H19 and concrete
padded Householder wrappers for the actual top/bottom economy-block Grams.

## Progress snapshot

These percentages are formalization-readiness estimates, not source coverage
claims.  The inventory score reflects complete contract-row accounting plus
partial exact-statement extraction.  It is intentionally capped because full
rendered statement comparison is still open.

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| ch16 | core | 45 | 15 | 20 | 10 | 50 | 23 | 37 plus Appendix A rows | All 32 equation rows and 5 problems are accounted for; Sylvester/Lyapunov candidate files compile, but exact source statements and local mapping are not yet source-checked. | low |
| ch17 | core | 45 | 15 | 20 | 10 | 50 | 23 | 36 plus Appendix A row | All 35 equation rows and problem 17.1 are accounted for; `StationaryIteration.lean` compiles, but its comments use shifted chapter numbering and need source-row remapping. | low |
| ch18 | core | 50 | 20 | 25 | 15 | 50 | 27 | 23 plus Appendix A rows | Theorems 18.1-18.2 and 17 equation rows are accounted for; `MatrixPowers.lean` compiles as a candidate foundation but uses older chapter-number comments. | low-medium |
| ch19 | core | 90 | 94 | 99 | 98 | 99 | 95 | 51 plus Appendix A rows | Ch.19 has detailed per-row inventory; Householder and Givens outward contracts compile; Theorem 19.13 now has determinant/source-condition/fallback `MGSQRBounds` wrappers, the CS/polar correction-map existence gate is closed, and the recursive/stored final-panel route now has self-dot beta bridges plus a two-column actual-active stored-step endpoint. Remaining gates: the full recursive normalized-reflector versus stored active-reflector match through the stored sequence, sharper source condition estimates for `R11`, exact printed constants, and final source-strength audit of `H19.Theorem19_13.mgs_qr_bounds`. | medium |

Latest Ch19 audit refresh (2026-06-29): the recursive/stored final-panel route
now has a compiled two-column endpoint using actual pivot-1 active-vector data:
`H19.Theorem19_13.qrPanel_R_two_col_eq_secondStoredActiveStep_one_of_tail_reflector_self_dot_of_subtractZeroExact`.
It consumes the tail active-vector identification with the recursive normalized
reflector, the source-style tail self-dot normalization, the determinant
nonbreakdown premises, and the exact subtract-zero copy convention.  This moves
the route from an artificial `Fin.cases 0 v1` normalized-vector endpoint to the
stored loop's own successor-pivot active vector with beta one.

Previous Ch19 audit refresh (2026-06-29): the recursive/stored final-panel route
can derive beta-one data from the source-style normalization `v^T v = 2` not
only for the one-column base case, but also for successor pivots after passing
to the once-shrunk trailing panel.  The support lemma
`householderBetaSpec_eq_one_of_inner_self_eq_two` proves that a vector with
square norm `2` has exact beta `1`; H19 exposes the trailing-active wrapper
`H19.Theorem19_13.householderTrailingActiveVector_betaSpec_eq_one_of_self_dot`
plus the zero-prefix/successor wrappers
`H19.Theorem19_13.householderBetaSpec_zero_cons_eq_one_of_inner_self_eq_two`
and
`H19.Theorem19_13.householderBetaSpec_trailingActiveVector_succ_zeroPrefix_eq_one_of_tail_self_dot`.
The new stored-step consumers
`H19.Theorem19_13.storedPanelStep_succ_trailingActiveVector_one_eq_panelFromTopAndTrailing_one_of_tail_self_dot_of_subtractZeroExact_of_succ`
and
`H19.Theorem19_13.storedPanelStep_succ_trailingActiveVector_one_eq_panelFromTopAndTrailing_one_of_tail_self_dot_of_subtractZeroExact_anyCols`
combine that successor beta bridge with the exact subtract-zero copy convention
to lift a beta-one trailing stored step back into the full stored panel.  The
terminal base consumers
`H19.Theorem19_13.storedSigned_one_col_final_panel_eq_qrPanel_R_of_reflector_self_dot`
and
`H19.Theorem19_13.storedSignedSequence_one_col_final_panel_eq_qrPanel_R_of_reflector_self_dot`.
This closes another listed dependency for the full shrinking-panel sequence
match, which still remains open.

Previous Ch19 audit refresh (2026-06-29): the exact beta-normalization side of
the recursive/stored reflector-data match is now named and checked.  The support
lemmas `householderBetaSpec_nonneg` and
`householder_normalizedVector_eq_betaSpec` prove that the exact
`householderBetaSpec` reflector is algebraically identical to its beta-one
normalized reflector.  The H19 wrapper
`H19.Theorem19_13.householderTrailingActiveVector_normalized_reflector_eq_betaSpec`
specializes this to the stored trailing-active Householder vector used in the
source recurrence.  This closes the exact matrix-level beta-normalization
dependency, but it does not assert equality of rounded compact stored steps; the
full recursive normalized-reflector versus stored active-reflector sequence
match remains open.

Previous Ch19 audit refresh: the CS/polar existence gate is closed and consumed
by the concrete Householder repair/source-output route.  The chapter-facing
`H19.Theorem19_13.mgs_qr_bounds` theorem now exists under explicit `det R11 !=
0` and Frobenius-inverse/final-budget hypotheses, with source-diagonal,
condition-budget, explicit-radius, Frobenius-fallback, Frobenius-self, and
stored-loop fallback variants.  The newest stored-loop variants replace the
pointwise `hR11` premise by the full final-panel equality
`A_hat n = fl_householderQRPanel_R ...`, using
`H19.Theorem19_13.householder_paddedFinInput_R11_eq_top_block_of_final_panel_eq`
to supply the extracted top-block equality internally.  The newest checked
dependency is the recursive/stored active-entry kernel bridge:
`fl_householderApplyCompactPanel_eq_applyMatrixRect`,
`fl_householderStoredPanelStep_eq_applyMatrixRect_of_active_not_below`, and
`H19.Theorem19_13.storedPanelStep_eq_applyMatrixRect_of_active_not_below`.
The first-pivot local storage-shape bridge
`H19.Theorem19_13.firstStoredPanelStep_eq_panelFromTopAndTrailing_applyMatrixRect`
now also identifies one rounded rectangular Householder panel update, stored via
`panelFromTopAndTrailing`, with the stored-panel pivot-zero update for identical
reflector data.  The nonzero first recursive layer
`H19.Theorem19_13.qrPanel_R_nonzero_eq_firstStoredPanelStep` now rewrites
`fl_householderQRPanel_R` as the QR storage reconstruction over the trailing
panel of that same first stored step.  Its top-left, top-row-tail, and
trailing-panel projections are now named by
`H19.Theorem19_13.panelTopLeft_qrPanel_R_nonzero_eq_firstStoredPanelStep`,
`H19.Theorem19_13.panelTopRowTail_qrPanel_R_nonzero_eq_firstStoredPanelStep`,
and
`H19.Theorem19_13.trailingPanel_qrPanel_R_nonzero_eq_qrPanel_R_firstStoredPanelStep`.
The row-indexing layer
`H19.Theorem19_13.householder_paddedFinInput_R11_eq_top_block_of_final_panel_eq`
now turns a full final-panel recursive/stored equality into the concrete
extracted-`R11` top-block equality, and the corresponding stored-loop
nonbreakdown and `MGSQRBounds` wrappers consume that final-panel equality
directly.  The remaining `R11` equality work is proving that full final-panel
recursive/stored equality by iterating/lifting the one-step bridge through
later shrinking panels and identifying later-pivot reflector data, plus source
nonbreakdown/condition estimates and exact printed-constant audits.

Latest Ch19 increment: the corrected Problem 19.12 CS/polar input now exposes
the Gram symmetry and Gram commutation facts needed by the simultaneous
diagonalization side of the CS/polar route.  The raw generic lemmas
`rectangularGram_symmetric` and `rectangularGram_commute_of_add_eq_id` give,
respectively, symmetry of any `Q^T Q` and commutation of two Grams whose sum is
`I`.  They feed
`MGSProblem1912CSPolarInput.p11_gram_symmetric`,
`MGSProblem1912CSPolarInput.p21_gram_symmetric`, and
`MGSProblem1912CSPolarInput.grams_commute`, with H19 wrappers
`H19.Theorem19_13.problem1912_csPolarInput_p11_gram_symmetric`,
`H19.Theorem19_13.problem1912_csPolarInput_p21_gram_symmetric`, and
`H19.Theorem19_13.problem1912_csPolarInput_grams_commute`.  The actual padded
Householder blocks expose the same route prerequisites through
`H19.Theorem19_13.householder_paddedFinInput_p11_gram_symmetric`,
`H19.Theorem19_13.householder_paddedFinInput_p21_gram_symmetric`, and
`H19.Theorem19_13.householder_paddedFinInput_grams_commute`.  This is still a
dependency layer, not the CS/polar existence theorem itself.

Previous Ch19 increment: the corrected Problem 19.12 CS/polar input now exposes
both complementary Gram identities for the CS/polar route.  Raw
`MGSProblem1912CSPolarInput.p21_gram_eq_id_sub_p11_gram` rewrites
`P21^T P21` as `I - P11^T P11`, while
`MGSProblem1912CSPolarInput.p11_gram_eq_id_sub_p21_gram` gives the symmetric
top-block complement.  H19 mirrors these as
`H19.Theorem19_13.problem1912_csPolarInput_p21_gram_eq_id_sub_p11_gram` and
`H19.Theorem19_13.problem1912_csPolarInput_p11_gram_eq_id_sub_p21_gram`; the
actual padded Householder blocks expose the same facts through
`H19.Theorem19_13.householder_paddedFinInput_p21_gram_eq_id_sub_p11_gram` and
`H19.Theorem19_13.householder_paddedFinInput_p11_gram_eq_id_sub_p21_gram`.
This closes another direct algebraic consequence of the corrected input, not
the CS/polar existence theorem itself.

Earlier Ch19 increment: the corrected Problem 19.12 CS/polar input now proves
the top and bottom block contraction facts needed by the CS/polar route.  The
new raw quadratic-form expansion
`rectangularGram_quadratic_eq_vecNorm2Sq` supports generic lemmas
`rectOpNorm2Le_one_left_of_rectangularGram_add_eq_id` and
`rectOpNorm2Le_one_right_of_rectangularGram_add_eq_id`: if
`A^T A + B^T B = I`, each block is a unit rectangular contraction.  This yields
`MGSProblem1912CSPolarInput.p11_opNorm2Le_one` and
`MGSProblem1912CSPolarInput.p21_rectOpNorm2Le_one`, mirrored by
`H19.Theorem19_13.problem1912_csPolarInput_p11_opNorm2Le_one` and
`H19.Theorem19_13.problem1912_csPolarInput_p21_rectOpNorm2Le_one`.  The actual
padded Householder blocks expose these as
`H19.Theorem19_13.householder_paddedFinInput_p11_opNorm2Le_one` and
`H19.Theorem19_13.householder_paddedFinInput_p21_rectOpNorm2Le_one`.  This still
does not prove CS/polar existence, but it closes a direct norm consequence of
the corrected input without invoking diagonal CS witness data.

Previous Ch19 increment: the corrected Problem 19.12 CS/polar input is now
available for the actual padded Householder economy blocks.  Raw
`MGSProblem1912CSPolarInput.of_paddedEconomy_blocks` packages full padded
orthogonality plus the explicit `n <= m` side condition into
`MGSProblem1912CSPolarInput m n (mgsPaddedEconomyP11 P)
(mgsPaddedEconomyQ P)`.  H19 mirrors this as
`H19.Theorem19_13.problem1912_csPolarInput_of_paddedEconomy_blocks`, and the
concrete `H19.Theorem19_13.householder_paddedFinInput_csPolarInput` extracts the
orthogonality witness from `householder_paddedFinInput_full_block_data` for
`fl_householderQRPanel_Q fp (n + m) n (paddedFinInput A)`.  This still does not
prove CS/polar existence, but it ties the remaining existence theorem directly
to the `(19.34)` Householder block handoff instead of only to an abstract
surface.

Previous Ch19 increment: the Problem 19.12 CS/polar target now has a compiled
corrected input surface.  Raw `MGSProblem1912CSPolarInput` packages the source
tallness condition `n <= m` with the block-column Gram identity
`P11^T P11 + P21^T P21 = I`; H19 exposes it as
`H19.Theorem19_13.Problem1912CSPolarInput`.  The bridge
`MGSProblem1912CSPolarInput.of_csDiagonalFactorData`, mirrored by
`H19.Theorem19_13.problem1912_csPolarInput_of_csDiagonalFactorData`, records
that supplied diagonal CS factor data satisfies this corrected input once the
source tallness hypothesis is explicit.  The next existence theorem should
consume this input predicate rather than the rejected dimension-free Gram-only
target.

Previous Ch19 increment: the Problem 19.12 CS/polar target audit now has a
compiled hidden-hypothesis sanity check.  Raw
`mgsProblem1912_add_factor_gram_sum_not_dimension_free` and H19 wrapper
`H19.Theorem19_13.problem1912_add_factor_gram_sum_not_dimension_free` show that
`P11^T P11 + P21^T P21 = I` alone cannot imply the additive repair witnesses:
with `m=0`, `n=1`, `P11=I`, and empty `P21`, the Gram identity holds but no
zero-row matrix has one orthonormal column.  The next CS/polar theorem must
therefore keep the source tall/full-column-rank hypotheses instead of targeting
the former dimension-free Gram-identity statement.

Previous Ch19 increment: packaged Problem 19.12 diagonal CS factor data now
projects directly to the additive CS/polar witness shape.  Raw
`MGSProblem1912CSDiagonalFactorData.add_factor_eq` gives
`hcs.q = P21 + hcs.f*P11`, while
`mgsProblem1912_add_factor_exists_of_csDiagonalFactorData` and
`mgsProblem1912_add_factor_exists_of_csDiagonalFactorData_nonempty` produce
existential `Q`/`F` witnesses with the additive identity, orthonormality of
`Q`, and the unit `F` bound.  H19 exposes these as
`H19.Theorem19_13.problem1912_csDiagonalFactorData_add_factor_eq`,
`H19.Theorem19_13.problem1912_add_factor_exists_of_csDiagonalFactorData`, and
`H19.Theorem19_13.problem1912_add_factor_exists_of_csDiagonalFactorData_nonempty`.
This still does not prove CS/polar existence; it lets that theorem stop at the
source-facing additive witness shape or at packaged diagonal factor data without
requiring downstream consumers to reopen the stored subtraction-oriented fields.

Previous Ch19 increment: the pure Problem 19.12 correction-map interface now has
a checked additive orientation for the CS/polar theorem.  Raw
`MGSProblem1912CorrectionMapData.add_factor_eq` projects existing data to
`Q = P21 + F*P11`, while `mgsProblem1912_correctionMapData_of_add_factor`
builds the stored subtraction-oriented data from that additive identity,
orthonormality of `Q`, and the unit `F` bound.  H19 exposes these as
`H19.Theorem19_13.problem1912_correctionMapData_add_factor_eq` and
`H19.Theorem19_13.problem1912_correctionMapData_of_add_factor`.  This does not
prove CS/polar existence; it aligns the remaining existence theorem with the
source/Oracle-advised orientation before routing the data through the existing
repair and source-output wrappers.

Previous Ch19 increment: the source-output/MGSQRBounds fixed-budget route can now
consume packaged Problem 19.12 CS factor data, and `Nonempty` packaged factor
data, under determinant nonzero for the extracted `R11` block instead of a
pointwise nonzero-diagonal hypothesis.  The helper
`H19.Theorem19_13.householder_paddedFinInput_R11_diag_ne_zero_of_det_ne_zero`
uses `householder_paddedFinInput_full_block_data` to recover the
upper-trapezoidal shape of `R11` and then applies the existing triangular
determinant lemma.  The new determinant wrappers
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_det_ne_zero_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`,
`H19.Theorem19_13.mgs_qr_bounds_of_householder_det_ne_zero_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`,
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_det_ne_zero_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`, and
`H19.Theorem19_13.mgs_qr_bounds_of_householder_det_ne_zero_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`
reuse the existing pure correction-map-data route; the matching
`correctionMapDataExistsRepair` determinant wrappers select `Q`/`F` internally.
The new factor-data determinant wrappers include
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_det_ne_zero_csDiagonalFactorDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`,
`H19.Theorem19_13.mgs_qr_bounds_of_householder_det_ne_zero_csDiagonalFactorDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`,
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_det_ne_zero_csDiagonalFactorDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`, and
`H19.Theorem19_13.mgs_qr_bounds_of_householder_det_ne_zero_csDiagonalFactorDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`;
they convert the packaged CS payload to pure correction-map data internally.
The remaining source nonbreakdown target is now naturally `det R11 != 0` (or a
sharper inverse/condition estimate implying it), not separate diagonal
nonzero certificates.

Previous Ch19 increment: the fixed-budget route also consumes existence of
the pure Problem 19.12 correction-map data directly.  Raw
`mgsProblem1912_correctionMapData_exists_of_csDiagonalFactorData_nonempty`
turns `Nonempty MGSProblem1912CSDiagonalFactorData` into
`Exists Q F, MGSProblem1912CorrectionMapData ...`, and H19 exposes this as
`H19.Theorem19_13.problem1912_correctionMapData_exists_of_csDiagonalFactorData_nonempty`.
The new H19 wrappers
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`,
`H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_correctionMapDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`,
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`, and
`H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_correctionMapDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`
select the repaired `Q` and correction map internally and reuse the checked
pure-data fixed-budget route.  The remaining CS/polar theorem may now target
either pure correction-map-data existence or the stronger packaged factor-data
existence.

Previous Ch19 increment: the fixed-budget route consumes existence of the
packaged CS factor payload directly.  Raw
`mgsProblem1912_csDiagonalFactorData_nonempty_of_csDiagonalAlgebra` turns
explicit CS witnesses into `Nonempty MGSProblem1912CSDiagonalFactorData`, and
H19 exposes this as
`H19.Theorem19_13.problem1912_csDiagonalFactorData_nonempty_of_csDiagonalAlgebra`.
The H19 wrappers
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalFactorDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`,
`H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_csDiagonalFactorDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`,
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalFactorDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`, and
`H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_csDiagonalFactorDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`
unwrap `Nonempty Problem1912CSDiagonalFactorData` internally and reuse the
checked factor-data fixed-budget route.

Earlier Ch19 increment: explicit diagonal CS witnesses now package into the
source-shaped factor-data payload.  Raw
`mgsProblem1912_csDiagonalFactorData_of_csDiagonalAlgebra` constructs
`MGSProblem1912CSDiagonalFactorData` from the source CS factor equations,
orthogonality/orthonormal-column certificates, diagonal `C/S/T` identities,
`s_i >= 0`, and `c_i^2+s_i^2=1`.  The existential raw theorem
`mgsProblem1912_csDiagonalFactorData_exists_of_csDiagonalAlgebra` retains the
projected repaired `Q` and correction map `F`.  H19 exposes the same route as
`H19.Theorem19_13.problem1912_csDiagonalFactorData_of_csDiagonalAlgebra` and
`H19.Theorem19_13.problem1912_csDiagonalFactorData_exists_of_csDiagonalAlgebra`.
This narrows the remaining CS/polar gate: once the source existence theorem
provides the explicit CS witnesses, the payload construction is checked and the
existing factor-data fixed-budget wrappers can consume it directly.

Previous Ch19 increment: the Problem 19.12 route now has a single source-shaped
diagonal CS factor-data payload.  Raw
`MGSProblem1912CSDiagonalFactorData` packages the `P11 = U*C*W^T`,
`P21 = V*S*W^T`, `Q = V*W^T`, `F = V*T*U^T`, diagonal `C/S/T`, and
orthogonality data that the remaining CS/polar existence theorem should
produce.  It converts to pure `MGSProblem1912CorrectionMapData` through
`MGSProblem1912CSDiagonalFactorData.to_correctionMapData`, with an existential
bridge `mgsProblem1912_correctionMapData_exists_of_csDiagonalFactorData` and
checked Gram/top-block/bottom-block consequences.  The H19-facing wrappers are
`H19.Theorem19_13.Problem1912CSDiagonalFactorData`,
`H19.Theorem19_13.problem1912_correctionMapData_of_csDiagonalFactorData`,
`H19.Theorem19_13.problem1912_correctionMapData_exists_of_csDiagonalFactorData`,
`H19.Theorem19_13.problem1912_csDiagonalFactorData_gram_sum_eq_id`,
`H19.Theorem19_13.problem1912_csDiagonalFactorData_p11_opNorm2Le_one`, and
`H19.Theorem19_13.problem1912_csDiagonalFactorData_p21_rectOpNorm2Le_one`.

The fixed-budget Householder-stacked route now also consumes that one factor
payload directly through
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalFactorDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`,
`H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_csDiagonalFactorDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`,
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalFactorDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`, and
`H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_csDiagonalFactorDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`.
This does not prove CS/polar existence; it sharpens the remaining gate to
producing the packaged source-shaped CS data and the source estimates for
`R11`.

Previous Ch19 increment: the Problem 19.12 route also closes the diagonal
CS square identity, the factor-level CS block-column Gram identity, and the
paired top/bottom CS-data contraction consequences.  The base lemmas
`matMul_finiteDiagonal_self`,
`matMul_finiteDiagonal_csSquareSum`, and
`mgsProblem1912_csDiagonal_square_sum`, exposed as
`H19.Theorem19_13.problem1912_matMul_finiteDiagonal_csSquareSum` and
`H19.Theorem19_13.problem1912_csDiagonal_square_sum`, prove
`diag(c)^2 + diag(s)^2 = I` from `c_i^2+s_i^2=1`.
The transpose and factor-strip helpers `finiteTranspose_finiteTranspose`,
`finiteTranspose_matMul`, `finiteTranspose_finiteDiagonal`,
`rectangularGram_matMulRect_of_orthonormal_left`,
`rectangularGram_matMul_left_orthogonal`,
`rectangularGram_matMul_orthogonal_diag_right`,
`rectangularGram_matMulRect_orthonormal_diag_right`, and
`mgsProblem1912_csDiagonal_gram_sum_eq_id`, exposed as
`H19.Theorem19_13.problem1912_csDiagonal_gram_sum_eq_id`, prove
`P11^T P11 + P21^T P21 = I` from source-shaped CS factor data
`P11 = U*C*W^T`, `P21 = V*S*W^T`, orthogonality/orthonormal-column
certificates, and `c_i^2+s_i^2=1`.
`H19.Theorem19_13.problem1912_opNorm2Le_finiteDiagonal_csSine` and
`H19.Theorem19_13.problem1912_opNorm2Le_finiteDiagonal_csCosine` prove
`||diag(s)||_2 <= 1` and `||diag(c)||_2 <= 1` from `c_i^2+s_i^2=1`, while
`H19.Theorem19_13.problem1912_p21_rectOpNorm2Le_one_of_csDiagonalAlgebra`
and `H19.Theorem19_13.problem1912_p11_opNorm2Le_one_of_csDiagonalAlgebra`
prove the source-shaped bottom and top CS blocks `P21 = V*S*W^T` and
`P11 = U*C*W^T` are contractions from the supplied orthogonality data.  This
does not prove the CS/polar existence theorem; it closes required consequences
once that factor data is available.

The newest Oracle-advised correction-map interface now separates the pure
Problem 19.12 repair data from the common-`R` factorization transport.  The
raw declarations `MGSProblem1912CorrectionMapData`,
`MGSProblem1912CorrectionMapData.to_correctionMap`,
`mgsProblem1912_correctionMapData_of_csAlgebra`,
`mgsProblem1912_correctionMapData_of_csOrthogonalAlgebra`, and
`mgsProblem1912_correctionMapData_of_csDiagonalAlgebra`, exposed through
`H19.Theorem19_13.Problem1912CorrectionMapData`,
`H19.Theorem19_13.problem1912_correctionMapData_of_csAlgebra`,
`H19.Theorem19_13.problem1912_correctionMapData_to_correctionMap`,
`H19.Theorem19_13.problem1912_correctionMapData_of_csOrthogonalAlgebra`, and
`H19.Theorem19_13.problem1912_correctionMapData_of_csDiagonalAlgebra`,
package exactly the data the future CS/polar theorem should produce:
orthonormal `Q`, a correction factor `F` with `F*P11 = Q - P21`, and
`||F||_2 <= 1`.  This is not an existence proof; it is the checked data target
that can later specialize to the older common-`R`
`Problem1912CorrectionMap` contract.

The data-first interface now also reaches the downstream repair and
source-output route.  Raw theorems
`mgsProblem1912_repair_of_correctionMapData` and
`mgsProblem1912_repair_of_correctionMapData_of_perturbation_bounds`, exposed as
`H19.Theorem19_13.problem1912_repair_of_correctionMapData` and
`H19.Theorem19_13.problem1912_repair_of_correctionMapData_of_perturbation_bounds`,
transport pure correction-map data through `DeltaA_top = P11*R`.  The H19
wrappers
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair`,
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_perturbation_bounds`,
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_stacked_budget`,
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_budget`,
`H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_budget_of_small_unit_roundoff`,
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_budget_frobInv`, and
`H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_budget_frobInv_of_small_unit_roundoff`
now feed that pure data through the actual `(19.34)` stacked perturbation
handoff into the current `MGSQRBounds` surface.  The fixed-budget pure-data
wrappers
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`,
`H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`,
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`, and
`H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`
reuse the same residual budget for the top and bottom inputs, specialize
`eta2 = 2*eta1`, and fix the source coefficient as `c3 = 4*k` under the
small-unit-roundoff guard.  The fixed-budget `frobInv` variants instantiate
the same route with
`rho = ||nonsingInv R11||_F`, so future CS/polar data no longer needs a separate
fallback inverse-norm certificate.  This still leaves CS/polar existence,
source nonbreakdown, and sharp condition estimates open; it removes the need
for future work to rebuild either the common-`R` transport or the scalar
budget plumbing after data is available.

The new factor-data layer sits immediately above that pure-data route.  Once
the CS/polar theorem produces `Problem1912CSDiagonalFactorData` for the actual
Householder block, the factor-data fixed-budget wrappers convert it to the
pure correction-map data internally and reuse the same Householder-stacked
transport, fixed `c3 = 4*k` budget, and Frobenius-inverse fallback.  This keeps
the future existence proof from threading all CS factor equations through the
source-output assembly by hand.

The same Problem 19.12 route was already
pushed past the monolithic
repaired-budget hypotheses.  The compiled helpers
`mgsRepairedPerturbation_rectOpNorm2Le_of_bounds` and
`mgsRepairedPerturbation_columnFrob_le_of_column_budget`, exposed as
`H19.Theorem19_13.problem1912_repairedPerturbation_rectOpNorm2Le_of_bounds`
and
`H19.Theorem19_13.problem1912_repairedPerturbation_columnFrob_le_of_column_budget`,
prove that a unit correction map `F`, a top perturbation budget for `dTop`,
and a bottom perturbation budget for `dBottom` imply the operator and
columnwise budgets for `F*dTop + dBottom`.  The repair wrappers
`H19.Theorem19_13.problem1912_repair_of_correctionMap_of_perturbation_bounds`,
`H19.Theorem19_13.problem1912_repair_of_csDiagonalAlgebra_of_perturbation_bounds`,
and
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_perturbation_bounds`,
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_stacked_budget`,
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_budget`,
`H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_stacked_budget_of_small_unit_roundoff`,
and
`H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_budget_of_small_unit_roundoff`,
plus
`H19.Theorem19_13.gamma_tilde_two_column_budget`,
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_same_residual_budget`,
and
`H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_same_residual_budget_of_small_unit_roundoff`
plus
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_budget`
and
`H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_budget_of_small_unit_roundoff`
plus
`H19.Theorem19_13.gamma_tilde_two_le_four_index_mul_unit_roundoff_of_small`,
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`,
and
`H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`
plus the Frobenius-inverse fallback wrappers
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`
and
`H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`
now thread those derived budgets through the diagonal-CS repair and source-output
assemblies.  The strongest route uses the actual stacked perturbation bound
returned by `householder_paddedFinInput_full_block_data`, reuses the same
residual budget for the top and bottom perturbation inputs, and derives the
per-column repair budget from the scalar coefficient inequality
`2*gamma_tilde <= c3*u`.  The double-residual variants further specialize
`eta2 = 2*eta1`, discharging the norm budget and deriving the nonnegative
QR-sensitivity radius from the residual budget.  The coefficient-budget
variants then derive `2*gamma_tilde <= 4*k*u` from the existing small-unit
roundoff guard and fix `c3 = 4*k`.  The repaired perturbation layer therefore
no longer needs a separate top residual budget, bottom residual budget,
per-column budget hypothesis, separate norm-budget hypothesis, or source column
coefficient-budget hypothesis.  The Frobenius fallback also no longer needs a
separate inverse-norm certificate or nonnegative `rho` proof.  The remaining hard
source work is therefore more specific:
prove the CS/polar existence theorem that supplies the diagonal factor data and
orthogonality data, prove source determinant/nonbreakdown and sharp
right-inverse/condition estimates for `R11`, and check the exact printed
constants/final radius budget.  The fallback Frobenius-inverse wrappers remain
valid fallback assemblies, but they are still weaker than the source
condition-number route.

## Complete split-owned row inventory

Rows below are selected in core mode unless explicitly marked `SKIP`,
`DEFER`, or `BENCHMARK_CANDIDATE`.  Exact theorem surfaces are not copied from
the book; they must be designed from rendered pages before implementation.

### Chapter 16 - The Sylvester Equation

Owned source surface: section-level Sylvester/Lyapunov definitions and results,
32 numbered equations, 5 problems, and Appendix A solutions 16.1-16.4.

| ID | Source location | Kind | Statement summary | Precision | Generality | Source proof | Dependencies | Decision | Reason code | Lean artifact/status |
|---|---|---|---|---|---|---|---|---|---|---|
| `H16.Section16_1` | Sec. 16.1 | definition/theorem cluster | Sylvester equation, vec/Kronecker viewpoint, solvability and uniqueness conditions. | partly precise until rendered | general | varies | matrix algebra, Kronecker/vec, eigenvalue separation | FORMALIZE_CORE | CORE-PRECISE-PROSE | Candidate local files: `SylvesterSpec.lean`; not source-closed. |
| `H16.Section16_2` | Sec. 16.2 | theorem cluster | backward error and residual relationships for Sylvester solves. | partly precise until rendered | general | varies | residuals, norms, SVD-style backward error | FORMALIZE_CORE | CORE-PRECISE-PROSE | Candidate local files: `SylvesterSpec.lean`, `SylvesterBackward.lean`; not source-closed. |
| `H16.Section16_2_1` | Sec. 16.2.1 | definition/theorem cluster | Lyapunov specialization of Sylvester equation. | partly precise until rendered | general | varies | transpose/symmetry, Sylvester specialization | FORMALIZE_CORE | CORE-PRECISE-PROSE | Candidate local files: `SylvesterSpec.lean`, `SylvesterPerturbation.lean`; not source-closed. |
| `H16.Section16_4` | Sec. 16.4 | theorem/algorithm cluster | practical error bounds and condition estimates. | partly precise until rendered | general | varies | Split 3A inverse/condition-estimation interfaces if used | FORMALIZE_CORE | CORE-PRECISE-PROSE | Candidate local surface unknown; do not duplicate Ch14-Ch15 contracts. |
| `H16.Section16_5` | Sec. 16.5 | extension cluster | extensions of Sylvester/Lyapunov analysis. | partly precise until rendered | general | varies | source-specific | DEFER until exact selected claim audit | DEFER-MISSING-PRECISE-STATEMENT | Needs rendered source classification. |

Chapter 16 numbered equation queue:

| Row set | Source labels | Decision | Current Lean status |
|---|---|---|---|
| `H16.Eq16_1` through `H16.Eq16_32` | `(16.1)`, `(16.2)`, `(16.3)`, `(16.4)`, `(16.5)`, `(16.6)`, `(16.7)`, `(16.8)`, `(16.9)`, `(16.10)`, `(16.11)`, `(16.12)`, `(16.13)`, `(16.14)`, `(16.15)`, `(16.16)`, `(16.17)`, `(16.18)`, `(16.19)`, `(16.20)`, `(16.21)`, `(16.22)`, `(16.23)`, `(16.24)`, `(16.25)`, `(16.26)`, `(16.27)`, `(16.28)`, `(16.29)`, `(16.30)`, `(16.31)`, `(16.32)` | FORMALIZE_CORE by default | Inventory-accounted.  Local Sylvester declarations have promising surfaces, but comments refer to older `Higham Sec. 15` labels.  Split 3B source labels remain open until rendered-statement mapping is complete. |

Chapter 16 problem and Appendix A queue:

| Row set | Source labels | Decision | Current Lean status |
|---|---|---|---|
| `H16.Problem16_1` through `H16.Problem16_5` | 16.1, 16.2, 16.3, 16.4, 16.5 | FORMALIZE_CORE if theoretical; SKIP empirical subclaims if any | Inventory-accounted.  Exact subpart classification pending rendered problem and Appendix A inspection. |
| `H16.AppendixA` | A.16.1, A.16.2, A.16.3, A.16.4 | FORMALIZE_DEPENDENCY or REUSE_EXISTING when used | Inventory-accounted.  Solution rows must be checked for proofs omitted in Ch.16. |

### Chapter 17 - Stationary Iterative Methods

Owned source surface: section-level stationary-iteration definitions and error
recurrences, 35 numbered equations, 1 problem, and Appendix A solution 17.1.

| ID | Source location | Kind | Statement summary | Precision | Generality | Source proof | Dependencies | Decision | Reason code | Lean artifact/status |
|---|---|---|---|---|---|---|---|---|---|---|
| `H17.Section17_1` | Sec. 17.1 | survey/theorem cluster | survey of forward and backward error analysis for stationary iteration. | partly precise until rendered | general | varies | matrix splittings, residuals | FORMALIZE_CORE for precise claims | CORE-PRECISE-PROSE | Candidate local file: `StationaryIteration.lean`; not source-closed. |
| `H17.Section17_2_1` | Sec. 17.2.1 | algorithm/specialization | Jacobi method specialization. | partly precise until rendered | general | varies | splitting definitions | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Candidate `jacobi_splitting_abs`; source label audit pending. |
| `H17.Section17_2_2` | Sec. 17.2.2 | algorithm/specialization | SOR specialization. | partly precise until rendered | general | varies | splitting definitions, relaxation parameter | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Candidate `sor_splitting_bound`; source label audit pending. |
| `H17.Section17_3` | Sec. 17.3 | theorem cluster | backward error analysis. | partly precise until rendered | general | varies | residual and norm bounds | FORMALIZE_CORE | CORE-PRECISE-PROSE | Candidate local theorem family exists; source audit pending. |
| `H17.Section17_4` | Sec. 17.4 | theorem cluster | singular systems and theoretical background. | partly precise until rendered | general | varies | singular systems, forward error, projectors likely | FORMALIZE_CORE if precise | CORE-PRECISE-PROSE | Candidate local surface incomplete/unknown. |
| `H17.Section17_5` | Sec. 17.5 | theorem/criterion cluster | stopping rules for iterative methods. | partly precise until rendered | general | varies | residual bounds, inverse or condition estimates | FORMALIZE_CORE if precise | CORE-PRECISE-PROSE | Needs rendered source classification. |

Chapter 17 numbered equation queue:

| Row set | Source labels | Decision | Current Lean status |
|---|---|---|---|
| `H17.Eq17_1` through `H17.Eq17_33c` | `(17.1)`, `(17.2)`, `(17.3)`, `(17.4)`, `(17.5)`, `(17.6)`, `(17.7)`, `(17.8)`, `(17.9)`, `(17.10)`, `(17.11)`, `(17.12)`, `(17.13)`, `(17.14)`, `(17.15)`, `(17.16)`, `(17.17)`, `(17.18)`, `(17.19)`, `(17.20)`, `(17.21)`, `(17.22)`, `(17.23)`, `(17.24)`, `(17.25)`, `(17.26)`, `(17.27)`, `(17.28)`, `(17.29)`, `(17.30)`, `(17.31)`, `(17.32)`, `(17.33a)`, `(17.33b)`, `(17.33c)` | FORMALIZE_CORE by default | Inventory-accounted.  Candidate `StationaryIteration.lean` comments call this material `Higham Chapter 16`, so every candidate must be remapped to current Ch.17 source rows before closure. |

Chapter 17 problem and Appendix A queue:

| Row set | Source labels | Decision | Current Lean status |
|---|---|---|---|
| `H17.Problem17_1` | 17.1 | FORMALIZE_CORE if theoretical | Inventory-accounted.  Exact problem and solution statement pending rendered source check. |
| `H17.AppendixA` | A.17.1 | FORMALIZE_DEPENDENCY or REUSE_EXISTING when used | Inventory-accounted. |

### Chapter 18 - Matrix Powers

Owned source surface: Theorems 18.1 and 18.2, 17 numbered equation labels,
4 problems, and Appendix A solutions 18.1-18.2.

| ID | Source location | Kind | Statement summary | Precision | Generality | Source proof | Dependencies | Decision | Reason code | Lean artifact/status |
|---|---|---|---|---|---|---|---|---|---|---|
| `H18.Theorem18_1` | Sec. 18.2, PDF p. 9 | theorem | finite precision matrix-power bound/convergence theorem. | partly precise until rendered | general | source proof present | matrix powers, norm bounds, gamma calculus | FORMALIZE_CORE | CORE-NAMED-RESULT | Candidate `higham_knight_17_1` and related `MatrixPowers.lean` facts; local comments use old `Theorem 17.1`. Not source-closed. |
| `H18.Theorem18_2` | Sec. 18.2, PDF p. 11 | theorem | second finite precision matrix-power bound/theorem. | partly precise until rendered | general | source proof present | Theorem 18.1 dependencies, matrix power error model | FORMALIZE_CORE | CORE-NAMED-RESULT | Candidate local surface unknown; not source-closed. |

Chapter 18 numbered equation queue:

| Row set | Source labels | Decision | Current Lean status |
|---|---|---|---|
| `H18.Eq18_1a` through `H18.Eq18_15` | `(18.1a)`, `(18.1b)`, `(18.2)`, `(18.3)`, `(18.4)`, `(18.5)`, `(18.1)`, `(18.6)`, `(18.7)`, `(18.8)`, `(18.9)`, `(18.10)`, `(18.11)`, `(18.12)`, `(18.13)`, `(18.14)`, `(18.15)` | FORMALIZE_CORE by default | Inventory-accounted.  Candidate `MatrixPowers.lean` includes computed-power and Higham-Knight-style theorems, but comments use old Ch.17 numbering.  Exact source-row audit pending. |

Chapter 18 problem and Appendix A queue:

| Row set | Source labels | Decision | Current Lean status |
|---|---|---|---|
| `H18.Problem18_1` through `H18.Problem18_4` | 18.1, 18.2, 18.3, 18.4 | FORMALIZE_CORE if theoretical; SKIP empirical subclaims if any | Inventory-accounted.  Exact problem and solution subpart classification pending. |
| `H18.AppendixA` | A.18.1, A.18.2 | FORMALIZE_DEPENDENCY or REUSE_EXISTING when used | Inventory-accounted. |

### Chapter 19 - QR Factorization

Owned source surface: 13 primary labels, 41 equation labels, 13 problems
excluding problem 19.8 by split contract, and Appendix A solutions 19.1-19.14.
Split 4 needs the QR interfaces first.

Primary label inventory:

| ID | Source location | Kind | Statement summary | Precision | Generality | Source proof | Dependencies | Decision | Reason code | Lean artifact/status |
|---|---|---|---|---|---|---|---|---|---|---|
| `H19.Lemma19_1` | Sec. 19.3, PDF p. 5 | theorem | computed Householder vector/beta error model. | precise after rendered formula check | general real vectors | proof present | FP model, norm, Householder construction | FORMALIZE_CORE | CORE-NAMED-RESULT | Candidate `HouseholderReflector.lean`; old `18.x` comments; open. |
| `H19.Lemma19_2` | Sec. 19.3, PDF p. 6 | theorem | applying a computed Householder transformation gives a perturbation model. | precise after rendered formula check | general real vectors/matrices | proof present | Lemma 19.1, Householder application | FORMALIZE_CORE | CORE-NAMED-RESULT | Candidate `HouseholderApply*.lean`; open. |
| `H19.Lemma19_3` | Sec. 19.3, PDF p. 7 | theorem | sequence of Householder transformations gives matrix/columnwise backward-error bounds. | precise after rendered formula check | rectangular real matrices | proof present | Lemma 19.2, product perturbation, gamma calculus | FORMALIZE_CORE | CORE-NAMED-RESULT | Candidate `HouseholderQR.lean`; open. |
| `H19.Theorem19_4.householder_qr_backward_error` | Sec. 19.3, PDF p. 8 | theorem | rectangular Householder QR backward error for computed upper trapezoidal `R`, with orthogonal `Q` and columnwise perturbation bounds. | precise after rendered formula check | real `m x n`, `m >= n` | proof present | Lemmas 19.1-19.3, QR semantics | FORMALIZE_CORE | CORE-NAMED-RESULT | Source-facing wrapper proved in `LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean`; assumptions expose `0 < n`, `n <= m`, and `gammaValid`. |
| `H19.Theorem19_5` | Sec. 19.3, PDF p. 9 | theorem | QR-based solve backward error for nonsingular systems. | precise after rendered formula check | real square nonsingular systems | proof present | Theorem 19.4, triangular solve | FORMALIZE_CORE | CORE-NAMED-RESULT | Candidate `QRSolve.lean`; distinguish from factorization row; open. |
| `H19.Theorem19_6` | Sec. 19.4, PDF p. 10 | theorem | column-pivoted Householder row-wise stability result. | precise after rendered formula check | real rectangular, pivoted | proof sketch/problem-linked | pivoting, row-growth, Problem 19.6 | FORMALIZE_CORE | CORE-NAMED-RESULT | Candidate Cox-Higham support facts exist; no source closure. |
| `H19.Lemma19_7` | Sec. 19.6, PDF p. 14 | theorem | computed Givens rotation parameters satisfy relative error bounds. | precise after rendered formula check | real Givens coefficients | proof omitted/sketch | FP sqrt/division, Givens construction | FORMALIZE_CORE | CORE-NAMED-RESULT | Candidate `GivensSpec.lean`; constants conservative; open. |
| `H19.Lemma19_8` | Sec. 19.6, PDF p. 14 | theorem | applying a computed Givens rotation gives a perturbation bound. | precise after rendered formula check | real vector/matrix rotation | proof present | Lemma 19.7, Givens application | FORMALIZE_CORE | CORE-NAMED-RESULT | Candidate `GivensSpec.lean`, `GivensMatrixStep.lean`; open. |
| `H19.Lemma19_9` | Sec. 19.6, PDF p. 15 | theorem | sequence/product of Givens rotations gives backward-error bounds. | precise after rendered formula check | rectangular real matrices | proof sketch | Lemma 19.8, product perturbation | FORMALIZE_CORE | CORE-NAMED-RESULT | Candidate `GivensQR.lean`; open. |
| `H19.Theorem19_10.givens_qr_backward_error` | Sec. 19.6, PDF p. 16 | theorem | rectangular Givens QR backward error with standard rotation choices/order. | precise after rendered formula check | real `m x n`, `m >= n` | proof present | Lemmas 19.7-19.9, annihilation schedule | FORMALIZE_CORE | CORE-NAMED-RESULT | Source-facing wrapper proved in `LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean`; assumptions expose `0 < n`, `n <= m`, and `gammaValid fp 8`; coefficient is the repository's conservative staged-schedule `gamma_tilde`. |
| `H19.Algorithm19_11` | Sec. 19.8, PDF p. 17 | algorithm/spec | classical Gram-Schmidt QR pseudocode. | precise after rendered formula check | full-rank real `m x n` | algorithm | dot products, norms, triangular factor semantics | FORMALIZE_CORE | CORE-NAMED-RESULT | Compiled source-facing state surface: `H19.Algorithm19_11.State` and residual alias backed by `ClassicalGramSchmidtState`/`classicalGramSchmidtResidual` in `GramSchmidt.lean`; exact rendered formula cross-link still open. |
| `H19.Algorithm19_12` | Sec. 19.8, PDF p. 18 | algorithm/spec | modified Gram-Schmidt QR pseudocode. | precise after rendered formula check | full-rank real `m x n` | algorithm | dot products, norms, triangular factor semantics | FORMALIZE_CORE | CORE-NAMED-RESULT | Compiled exact MGS stage/Q/R definitions, source-stage matrices, one-step `R_k` factors, shape theorems, recombination facts, full source-stage recurrence, exact one-step product factorization, exact `A = Q R` result, diagonal scalar channel, and unit MGS-column channel: `H19.Algorithm19_12.exact_state`, `computedR_upper_trapezoidal`, `stepR_upper_trapezoidal`, `stageVectors_succ_later`, `computedQ_stage_self_dot`, `computedQ_column_norm_sq`, `sourceStage_current_recombine`, `sourceStage_later_recombine`, `sourceStage_matrix_recurrence`, `stepRProduct`, `sourceStage_initial_matrix_recurrence`, `exact_product_factorization`, `stepRProduct_eq_computedR`, and `exact_factorization`; exact rendered formula cross-link still open. |
| `H19.Theorem19_13.mgs_qr_bounds` | Sec. 19.8, PDF p. 20 | theorem | MGS residual, orthogonality-loss, and R-factor quality bounds. | precise after rendered formula check | full-rank real `m x n` | proof present | Algorithm 19.12, Householder-MGS connection, QR sensitivity | FORMALIZE_CORE | CORE-NAMED-RESULT | Contract shape now compiled as `H19.Theorem19_13.MGSQRBounds` backed by `ModifiedGramSchmidtBackwardError`; the `(19.27)`-`(19.34)` padded Householder-MGS route, block data, block Gram identities, Problem 19.12 CS/polar correction-map existence, repaired-budget algebra, common-`R` sensitivity algebra, exact-unit-roundoff coefficient bridge, determinant/source-condition/fallback `MGSQRBounds` wrappers, concrete Householder-stacked CS/polar repair wrappers, and the chapter-facing `H19.Theorem19_13.mgs_qr_bounds` determinant-plus-budget route compile.  The current increment adds `householderBetaSpec_eq_one_of_inner_self_eq_two`, `H19.Theorem19_13.householderTrailingActiveVector_betaSpec_eq_one_of_self_dot`, and the one-column stored/recursive final-panel self-dot wrappers. Remaining source-strength gates are the full recursive/stored final-panel equality, source determinant/nonbreakdown and sharp `R11` condition estimates, exact printed constants/radius audit, and rendered-source comparison. |

Chapter 19 numbered equation queue:

Detailed per-row inventory path: `chapter_splitting/reports/split3b_ch19_source_inventory.md`.

| Row set | Source labels | Decision | Current Lean status |
|---|---|---|---|
| Householder setup equations | `(19.1)`, `(19.2a)`, `(19.2b)`, `(19.3)`, `(19.4)`, `(19.2)` | FORMALIZE_CORE | Inventory-accounted. Candidate Householder definitions exist; old numbering audit required. |
| Householder error-analysis equations | `(19.5)`, `(19.6)`, `(19.7)`, `(19.8)`, `(19.9)`, `(19.10)`, `(19.11)`, `(19.12)`, `(19.13)`, `(19.14)`, `(19.15)` | FORMALIZE_CORE | Inventory-accounted. Candidate Householder QR/QRSolve theorem families exist; no H19 source closure yet. |
| Aggregated Householder equations | `(19.16)`, `(19.17)`, `(19.18)`, `(19.19)`, `(19.20)`, `(19.21)`, `(19.22)` | FORMALIZE_CORE if precise and used | Inventory-accounted. Candidate local surface unknown. |
| Givens equations | `(19.23)`, `(19.24)`, `(19.25)` | FORMALIZE_CORE | Inventory-accounted. Candidate Givens declarations exist; constants/schedule audit pending. |
| Gram-Schmidt/MGS equations | `(19.26)`, `(19.27)`, `(19.28)`, `(19.29)`, `(19.30)`, `(19.31)`, `(19.32)`, `(19.33)`, `(19.34)` | FORMALIZE_CORE | Inventory-accounted. `GramSchmidt.lean` now supplies CGS residual/state definitions, exact MGS stage/Q/R definitions, source-stage matrices, one-step `R_k` factors and upper-trapezoidal shape, the full source-stage recurrence for `(19.32)`, exact one-step-factor product recurrence/factorization and exact `A = Q R` factorization for `(19.33)`, the diagonal scalar channel `q_k^T a_k^(k) = r_kk`, the unit MGS-column channel, padded-input and Householder-MGS padded-stage/vector/reflector vocabulary for `(19.27)`-`(19.28)` and `(19.34)`, the proved `v_k^T v_k = 2` vector-normalization channel under an explicit unit-column hypothesis and for computed MGS columns under the nonzero stage-norm hypothesis, exact reflector symmetry and `P_k^2 = I` under the self-dot condition, exact one-reflector action lemmas for `P_k [0; A]`, exact padded-stage endpoints `[0; A]` and `[R; 0]`, exact forward/reverse one-step padded-stage transitions, the forward-prefix endpoint from `[0; A]` to `[R; 0]`, the reverse-prefix endpoint from `[R; 0]` to `[0; A]`, exact top/bottom block extraction from the reverse-prefix endpoint, generic `[Delta A3; A + Delta A4]` perturbation shape, row reindexing, stacked-column bound transport, Theorem 19.4 padded-input handoff, block-form `(19.34)` product packaging, rectangular Gram residual, and the Theorem 19.13 contract shape. The final stability proof rows remain open. |
| Gram-Schmidt/MGS extraction | `(19.34)` | FORMALIZE_DEPENDENCY | New compiled extraction bridge: `mgsPaddedTopPerturbation`, `mgsPaddedBottomPerturbation`, `mgsPaddedTopPerturbation_perturbedInput`, `mgsPaddedBottomPerturbation_perturbedInput`, `mgsPaddedPerturbedInput_eta`, and the `H19.Theorem19_13.*` wrappers. Any padded matrix can now be reassembled as `[Delta A3; A + Delta A4]` from its extracted perturbation blocks; the remaining gate is transferring Theorem 19.4's columnwise bound through these blocks. |
| Gram-Schmidt/MGS row reindex | `(19.34)` | FORMALIZE_DEPENDENCY | New compiled row-shape bridge: `mgsPaddedRowToFin`, `mgsPaddedRowFromFin`, `mgsPaddedRowsToFin`, `mgsPaddedRowsFromFin`, `mgsPaddedFinInput`, both matrix round trips, and `H19.Theorem19_13.*` wrappers. The next gate is column-norm/bound transport between the `Fin (n + m)` Householder error and the sum-indexed stacked perturbation. |
| Gram-Schmidt/MGS bound transport | `(19.34)` | FORMALIZE_DEPENDENCY | New compiled bound bridge: `mgsPaddedColumnNorm_rowsFromFin`, `mgsPaddedColumnNorm_paddedInput`, `columnFrob_paddedFinInput`, `mgsStackedPerturbationColumnNorm_rowsFromFin_add`, `mgsStackedPerturbationColumnwiseBound_of_rowsFromFin_add_padded_bound`, and `H19.Theorem19_13.*` wrappers. A Theorem 19.4-style bound on a `Fin (n + m)` perturbation of `paddedFinInput A` now yields the stacked `[Delta A3; Delta A4]` columnwise bound after row conversion and extraction. |
| Gram-Schmidt/MGS Householder handoff | `(19.34)` | FORMALIZE_DEPENDENCY | New compiled handoff: `H19.Theorem19_13.householder_paddedFinInput_stackedPerturbation` instantiates Theorem 19.4 on `paddedFinInput A` and returns the existential `dA`, product equation, and stacked perturbation columnwise bound. The printed orientation is handled by the block-form and economy-product rows below; QR sensitivity remains open. |
| Gram-Schmidt/MGS block-form handoff | `(19.34)` | FORMALIZE_DEPENDENCY | New compiled block-form handoff: `H19.Theorem19_13.paddedBottomBlock_rowsFromFin_of_upper` and `H19.Theorem19_13.householder_paddedFinInput_perturbedInput_blocks` package the perturbed product equation in sum-indexed padded rows, prove the converted `Rhat` bottom block is zero, and retain the stacked perturbation columnwise bound. The remaining gate is QR sensitivity and the final stability bounds. |
| Gram-Schmidt/MGS economy-product handoff | `(19.34)` | FORMALIZE_DEPENDENCY | New compiled economy-product bridge: `mgsPaddedEconomyQ`, `mgsPaddedEconomyR`, `mgsPaddedPerturbedInput_bottom_eq_economyProduct`, and `H19.Theorem19_13.householder_paddedFinInput_economyProduct` extract the bottom block as `A + Delta A4 = Q21 * R11`, keep the zero lower `Rhat` block, and retain the stacked perturbation bound. The remaining gate is the QR-sensitivity theorem for `(19.35a)`-`(19.37)`. |
| QR sensitivity equations | `(19.35a)`, `(19.35b)`, `(19.36)`, `(19.37)`, `(19.35)` | FORMALIZE_CORE if precise | Inventory-accounted. Candidate bridge surface now compiled as `ModifiedGramSchmidtQRSensitivitySourceOutput`, `ModifiedGramSchmidtQRSensitivitySourceOutput.of_commonR_bounds`, `ModifiedGramSchmidtQRSensitivityBridge.of_source_output`, `H19.Theorem19_13.QRSensitivitySourceOutput`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_commonR_bounds`, `H19.Theorem19_13.qrsensitivityBridge_of_source_output`, and `H19.Theorem19_13.QRSensitivityBridge`, plus the assembly theorems through `H19.Theorem19_13.mgs_qr_bounds_of_householder_economy_product_sensitivity_of_coefficient_budget`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_economy_product_source_sensitivity_of_coefficient_budget`, `H19.Theorem19_4.gamma_tilde_le_two_index_mul_unit_roundoff_of_small`, and `H19.Theorem19_13.mgs_qr_bounds_of_householder_economy_product_source_sensitivity_of_small_unit_roundoff`; Householder gamma nonnegativity is discharged by `H19.Theorem19_4.gamma_tilde_nonneg`, and the exact-unit-roundoff route discharges the coefficient budget from `k*u <= 1/2`. GPT-5.5 Pro audit `split3b-qr-sensitivit` found that these two source-output fields are acceptable final output channels but not a faithful decomposition of `(19.35a)`-`(19.37)` by themselves; the source proof also needs the full `(19.34)` block data and the Problem 19.12 correction-map route. The CS/polar correction-map existence gate, downstream repair algebra, common-`R` algebra/norm bridge, exact Gram-residual expansion, `2*delta + delta^2` operator-norm conversion, and conditional common-`R` source-output assembly now compile. Remaining gates are the recursive/stored final-panel equality, source right-inverse/condition estimates for `R11`, exact printed constants, and rendered-source comparison. |

Chapter 19 problem and Appendix A queue:

| Row set | Source labels | Decision | Current Lean status |
|---|---|---|---|
| Theoretical QR problems | 19.1, 19.2, 19.3, 19.4, 19.5, 19.6, 19.7, 19.9, 19.10, 19.11, 19.12, 19.13, 19.14 | FORMALIZE_CORE if theoretical; SKIP empirical subclaims if any | Inventory-accounted. Exact problem and Appendix A subpart classification pending. |
| Excluded by split contract | 19.8 | SKIP | Excluded from Split 3B problem ledger even though Appendix A ownership includes A.19.8. Do not implement unless contract changes. |
| `H19.AppendixA` | A.19.1 through A.19.14 | FORMALIZE_DEPENDENCY or REUSE_EXISTING when used | Inventory-accounted. Solution rows must be checked for omitted proof details, especially pivoting/MGS/QR sensitivity material. |

## Candidate local foundation map

| Source area | Candidate local declarations/files | Current audit classification | Why not source-closed |
|---|---|---|---|
| Ch16 Sylvester/Lyapunov | `sylvesterOp`, `sylvesterResidual`, `SepLowerBound`, `lyapunovOp`, `residual_decomposition`, `residual_bound`, `backward_error_*`, `sylvester_perturbation_*`, `condSylvester` in `LeanFpAnalysis/FP/Algorithms/Sylvester/*.lean` | candidate foundation | Comments refer to old `Higham Sec. 15` labels; exact Ch16 statement mapping and equation closure are not done. |
| Ch17 stationary iteration | `SplittingSpec`, `iterMatrix`, `ComputedIteration`, `one_step_error`, `componentwise_forward_bound`, `jacobi_splitting_abs`, `sor_splitting_bound`, residual/normwise bound theorems in `StationaryIteration.lean` | candidate foundation | File comments refer to `Higham Chapter 16`; current Split 3B owns this as Ch17. Exact source remapping is required. |
| Ch18 matrix powers | `ComputedMatPowVec`, `matPow_*` bound theorems, `JordanFormSpec`, `higham_knight_17_1` in `MatrixPowers.lean` | candidate foundation | File comments refer to old Ch17/Theorem 17.1; current Split 3B source rows are Ch18 Theorems 18.1-18.2 and equations. |
| Ch19 Householder QR | `HouseholderQRBackwardError`, `HouseholderQRPanelColumnwiseBackwardError`, `StructuredHouseholderQRPanelHighamBackwardError`, `fl_householderQRPanel_R_higham_backward_error_gammaHigham_of_global_gammaValid`, `fl_householderQR_backward_error_gammaHigham_of_global_gammaValid`, `fl_householderQR_explicit_backward_error_gammaHigham_of_global_gammaValid`, `H19.Theorem19_4.householder_qr_backward_error` | source-facing wrapper exported | Theorem 19.4 now has a compiled public wrapper.  The old-numbered implementation comments and sign/equation audit remain documentation risks, not blockers for the outward contract. |
| Ch19 Givens QR | `GivensCoeffError`, `SparseGivensAppError`, `fl_givensApply_coeffError_sparse_app_error`, `SparseColumnwiseGivensStepErrorRect`, `fl_givensApply_computed_matrix_sparse_step_error_rect`, `SparseColumnwiseGivensStepErrorRect.exists_residual_matrix_bound_row_support`, `GivensQRTask`, `GivensQRTask.instFinite`, `GivensQRTask.instFintype`, `GivensQRTask.same_stage_rowPair_disjoint`, `GivensQRTask.stage_lt_stageCount`, `givensQRStageTasks`, `mem_givensQRStageTasks_iff`, `givensQRStageTasks_stage`, `givensQRStageTasks_complete`, `givensQRStageTasks_nodup`, `ZeroedThrough.zero`, `ZeroedThrough.prev_pair_zero_of_task`, `ZeroedThrough.succ_of_stageTargetsZero`, `StageTargetsZero`, `PairBlockSupported`, `fl_givensQRTaskStep`, `fl_givensQRTaskStep_active_ne_target`, `fl_givensQRTaskStep_prev_col_exact_rotation`, `fl_givensQRTaskStep_target_exact_rotation`, `fl_givensQRTaskStep_sparse_residual_of_prev_pair_zero`, `fl_givensQRTaskStepOfTask_sparse_residual_of_zeroedThrough`, `givensQRTaskRotation`, `givensQRTaskRotation_orthogonal`, `givensQRTaskRotation_frobNorm`, `fl_givensQRTaskStepOfTask_residual_of_zeroedThrough`, `fl_givensQRTaskStepOfTask_residual_uniform_of_zeroedThrough`, `orthogonal_sequence_one_step_of_columnFrob_residual_rect`, `residual_orthogonal_sequence_columnFrob_backward_error_rect`, `fl_givensQRTask_sequence_backward_error_uniform`, `fl_givensQRTask_sequence_columnFrob_backward_error_uniform`, `fl_givensQRTaskStepOfTask_preserves_zeroedThrough_stage`, `fl_givensQRTaskStepOfTask_preserves_same_stage_target`, `fl_givensQRTaskList`, `fl_givensQRTaskList_preserves_zeroedThrough_stage`, `fl_givensQRTaskList_take_preserves_zeroedThrough_stage`, `fl_givensQRTaskList_preserves_same_stage_target`, `fl_givensQRTaskList_stage_target_zero_of_mem`, `fl_givensQRTaskList_zeroedThrough_succ_of_stage_complete`, `fl_givensQRStageTasks_zeroedThrough_succ`, `fl_givensQRStageTasks_take_preserves_zeroedThrough`, `fl_givensQRStageTasks_prefix_task_residual_uniform`, `fl_givensQRStageTasks_prefix_task_columnFrob_uniform`, `fl_givensQRStageTasks_sequence_backward_error_uniform`, `fl_givensQRStageTasks_sequence_columnFrob_backward_error_uniform`, `residualAccumBound_le_of_le_nat`, `givensQRStageTasks_length_le_stageTaskList_length`, `fl_givensQRStageFold_sequence_backward_error_uniform`, `fl_givensQRStageFold_sequence_columnFrob_backward_error_uniform`, `fl_givensQRStageFold`, `fl_givensQRStageFold_zeroedThrough`, `fl_givensQRStageFold_upper_trapezoidal`, `givensQRStageTaskList`, `fl_givensQRTaskList_append`, `fl_givensQRStageFold_eq_taskList`, `mem_givensQRStageTaskList_iff`, `fl_givensQRStageTaskList_upper_trapezoidal`, `H19.Theorem19_10.givens_qr_backward_error`, `GivensQRBackwardError`, `givens_qr_backward`, `fl_givens_sequence_backward_error_uniform`, `fl_givens_panel_sequence_backward_error_uniform` | source-facing wrapper exported | The sparse vector/panel residual support layer, same-stage row-pair disjointness/preservation, stage range, `ZeroedThrough` previous-column bridge, zero-aware exact task factor/residual, generic normwise and columnwise task-sequence accumulation, frontier advance, task-indexed sparse residual, duplicate-free same-stage task-list accumulation, concrete filtered stage-list coverage, same-stage prefix frontier/residual/columnwise hooks, one concrete anti-diagonal stage normwise and columnwise accumulation, conservative full stage-fold normwise and columnwise accumulation, all-stage stage-fold/flat-list equivalence, upper-trapezoidal shape, and the public `H19.Theorem19_10.givens_qr_backward_error` wrapper compile. Exact printed-constant cross-linking remains a documentation risk, not a missing outward contract. |
| Ch19 CGS/MGS | `GramSchmidt.lean`, `H19.Algorithm19_11.*`, `H19.Algorithm19_12.*`, `H19.Algorithm19_12.computedQ_stage_self_dot`, `H19.Algorithm19_12.computedQ_column_norm_sq`, `H19.Theorem19_13.MGSQRBounds`, `H19.Theorem19_13.paddedStage`, `H19.Theorem19_13.paddedTopBlock`, `H19.Theorem19_13.paddedBottomBlock`, `H19.Theorem19_13.paddedPerturbedInput`, `H19.Theorem19_13.stackedPerturbationColumnwiseBound`, `H19.Theorem19_13.paddedStage_zero`, `H19.Theorem19_13.paddedStage_final`, `H19.Theorem19_13.householderVector_self_dot`, `H19.Theorem19_13.householderVector_self_dot_computedQ`, `H19.Theorem19_13.householderReflector_symmetric`, `H19.Theorem19_13.householderReflector_mul_self_of_self_dot`, `H19.Theorem19_13.householderApply_apply_self_of_self_dot`, `H19.Theorem19_13.householderApply_padded_bottom`, `H19.Theorem19_13.householderColumnInner_paddedStage`, `H19.Theorem19_13.householderApply_paddedStage_eq_succ`, `H19.Theorem19_13.householderApply_paddedStage_succ_eq_current`, `H19.Theorem19_13.householderApplyPrefix_paddedInput_final`, `H19.Theorem19_13.householderApplyReversePrefix`, `H19.Theorem19_13.householderApplyReversePrefix_paddedStage`, `H19.Theorem19_13.householderApplyReversePrefix_paddedRBlock`, `H19.Theorem19_13.householderApplyReversePrefix_paddedRBlock_blocks`, `H19.Theorem19_13.householder_paddedFinInput_stackedPerturbation`, `H19.Theorem19_13.paddedBottomBlock_rowsFromFin_of_upper`, `H19.Theorem19_13.householder_paddedFinInput_perturbedInput_blocks`, `H19.Theorem19_13.paddedEconomyQ`, `H19.Theorem19_13.paddedEconomyP11`, `H19.Theorem19_13.paddedEconomyR`, `H19.Theorem19_13.paddedPerturbedInput_bottom_eq_economyProduct`, `H19.Theorem19_13.paddedPerturbedInput_top_eq_economyProduct`, `H19.Theorem19_13.householder_paddedFinInput_economyProduct`, `H19.Theorem19_13.householder_paddedFinInput_full_block_data`, `H19.Theorem19_13.commonR_difference_product_eq_perturbation_difference`, `H19.Theorem19_13.commonR_difference_eq_perturbation_difference_mul_right_inverse`, `H19.Theorem19_13.commonR_difference_rectOpNorm2Le_of_perturbation_bounds_mul_right_inverse`, `H19.Theorem19_13.gramSchmidtOrthogonalityResidual_eq_close_expansion`, `H19.Theorem19_13.gramSchmidtOrthogonalityResidual_opNorm2Le_of_close_orthonormal`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_commonR_bounds`, `H19.Theorem19_13.paddedEconomyR_upper_trapezoidal`, `H19.Theorem19_13.householder_paddedFinInput_economyProduct_with_upper`, `H19.Theorem19_13.QRSensitivityBridge`, `H19.Theorem19_13.bottomPerturbation_rectOpNorm2Le_of_stackedColumnwiseBound`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_economy_product_sensitivity`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_economy_product_sensitivity_of_residual_budget`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_economy_product_sensitivity_of_valid_residual_budget`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_economy_product_sensitivity_of_coefficient_norm_budget`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_economy_product_sensitivity_of_coefficient_budget` | foundation started | Exact CGS residual/state, MGS stage/Q/R definitions, source-stage matrices, one-step `R_k` factors and product, MGS and one-step upper-trapezoidal shape, columnwise source-stage recombination facts, iterated source-stage recurrence, exact product factorization, exact `stepRProduct = computedR`, exact `A = Q R`, diagonal scalar channel `q_k^T a_k^(k) = r_kk`, unit MGS-column channel, padded-input and Householder-MGS padded-stage/vector/reflector vocabulary, `v_k^T v_k = 2` normalization facts, exact reflector symmetry/involution, one-reflector and padded-stage bridges, block-form `(19.34)` handoff, CS/polar correction-map existence and repair wrappers, common-`R` perturbation algebra, exact Gram-residual expansion and conversion, determinant/source-condition/fallback `MGSQRBounds` wrappers, chapter-facing `H19.Theorem19_13.mgs_qr_bounds` under explicit determinant/budget hypotheses, and the one-column self-dot terminal bridge compile. Remaining source-strength work is the full recursive/stored final-panel equality, source `R11` nonbreakdown/condition estimates, and printed-constant/source audit. |
| Ch19 Eq19.34 extraction | `mgsPaddedTopPerturbation`, `mgsPaddedBottomPerturbation`, `mgsPaddedPerturbedInput_eta`, `H19.Theorem19_13.paddedTopPerturbation`, `H19.Theorem19_13.paddedBottomPerturbation`, `H19.Theorem19_13.paddedPerturbedInput_eta` | foundation started | This closes only the algebraic extraction/reassembly shape for `[Delta A3; A + Delta A4]`. It does not yet supply the floating-point perturbation bound from Theorem 19.4 or the QR-sensitivity step for `mgs_qr_bounds`. |
| Ch19 Eq19.34 row reindex | `mgsPaddedRowsToFin`, `mgsPaddedRowsFromFin`, `mgsPaddedFinInput`, `H19.Theorem19_13.paddedRowsToFin`, `H19.Theorem19_13.paddedRowsFromFin`, `H19.Theorem19_13.paddedFinInput` | foundation started | This closes the row-shape bridge needed to call Theorem 19.4 on the padded matrix. It does not yet prove that Theorem 19.4's `columnFrob` bound transports to `mgsStackedPerturbationColumnwiseBound`. |
| Ch19 Eq19.34 bound transport | `mgsPaddedColumnNorm_rowsFromFin`, `columnFrob_paddedFinInput`, `mgsStackedPerturbationColumnwiseBound_of_rowsFromFin_add_padded_bound`, `H19.Theorem19_13.paddedColumnNorm_rowsFromFin`, `H19.Theorem19_13.columnFrob_paddedFinInput`, `H19.Theorem19_13.stackedPerturbationColumnwiseBound_of_rowsFromFin_add_padded_bound` | foundation started | This closes the column-norm/bound transport from Theorem 19.4's padded input to the stacked perturbation predicate. It does not yet instantiate Theorem 19.4 or connect its product equation to the QR-sensitivity step. |
| Ch19 Eq19.34 Householder handoff | `H19.Theorem19_13.householder_paddedFinInput_stackedPerturbation` | foundation started | This closes the Theorem 19.4 instantiation on `paddedFinInput A` and produces the stacked perturbation bound. The printed block orientation is now handled by the block-form row below; QR sensitivity and the final `mgs_qr_bounds` theorem remain open. |
| Ch19 Eq19.34 block-form handoff | `H19.Theorem19_13.paddedBottomBlock_rowsFromFin_of_upper`, `H19.Theorem19_13.householder_paddedFinInput_perturbedInput_blocks` | foundation started | This packages the Theorem 19.4 padded-input handoff as a sum-indexed perturbed-input product equation, proves the converted `Rhat` bottom block is zero, and retains the stacked columnwise perturbation bound. It does not yet supply the QR-sensitivity theorem needed for residual, orthogonality-loss, or R-factor bounds. |
| Ch19 Eq19.34 economy-product handoff | `mgsPaddedEconomyQ`, `mgsPaddedEconomyR`, `mgsPaddedBottomBlock_rowsFromFin_matMul_of_bottom_zero`, `mgsPaddedPerturbedInput_bottom_eq_economyProduct`, `H19.Theorem19_13.paddedEconomyQ`, `H19.Theorem19_13.paddedEconomyR`, `H19.Theorem19_13.paddedPerturbedInput_bottom_eq_economyProduct`, `H19.Theorem19_13.householder_paddedFinInput_economyProduct` | foundation started | This extracts the bottom block of the padded Householder handoff as `A + Delta A4 = Q21 * R11`, retains the zero lower `Rhat` block, and keeps the stacked perturbation bound for the QR-sensitivity route. It does not yet supply the QR-sensitivity theorem needed for residual, orthogonality-loss, or R-factor bounds. |
| Ch19 Eq19.34 full block data | `mgsPaddedEconomyP11`, `mgsPaddedTopBlock_rowsFromFin_matMul_of_bottom_zero`, `mgsPaddedPerturbedInput_top_eq_economyProduct`, `mgsPaddedEconomy_blocks_gram_sum_eq_id`, `mgsPaddedEconomyQ_gram_eq_id_sub_P11_gram`, `mgsPaddedEconomyQ_orthogonalityResidual_eq_neg_P11_gram`, `H19.Theorem19_13.paddedEconomyP11`, `H19.Theorem19_13.paddedPerturbedInput_top_eq_economyProduct`, `H19.Theorem19_13.householder_paddedFinInput_full_block_data`, `H19.Theorem19_13.paddedEconomy_blocks_gram_sum_eq_id`, `H19.Theorem19_13.paddedEconomyQ_gram_eq_id_sub_P11_gram`, `H19.Theorem19_13.paddedEconomyQ_orthogonalityResidual_eq_neg_P11_gram` | foundation started | Added after GPT-5.5 Pro audit showed that the orthonormal-repair route needs the top block `Delta A3 = P11 * R11` and full padded orthogonality, not only the bottom economy product. The block-column identities now turn full padded orthogonality into `P11^T P11 + Q21^T Q21 = I` and the exact residual identity `Q21^T Q21 - I = -P11^T P11`, giving the next local input for the Problem 19.12 CS/polar repair route. |
| Ch19 Eq19.34 pre-repair Gram-residual norm bridge | `rectOpNorm2Le_neg`, `opNorm2Le_neg`, `rectangularGram_opNorm2Le_of_rectOpNorm2Le`, `mgsPaddedEconomyQ_orthogonalityResidual_opNorm2Le_of_P11_rectOpNorm2Le`, `H19.Theorem19_13.paddedEconomyQ_orthogonalityResidual_opNorm2Le_of_P11_rectOpNorm2Le` | foundation started | Converts the exact block identity `Q21^T Q21 - I = -P11^T P11` into an operator-norm consequence: a `rectOpNorm2Le P11 eta` certificate implies `opNorm2Le (Q21^T Q21 - I) (eta^2)`. The CS/polar correction-map route now closes the repair witness; remaining use of this bridge depends on source `R11` inverse/condition budgets. |
| Ch19 Eq19.34 top-block right-inverse norm bridge | `right_factor_eq_product_mul_right_inverse`, `right_factor_rectOpNorm2Le_of_product_mul_right_inverse`, `mgsPaddedEconomyP11_rectOpNorm2Le_of_top_product_right_inverse`, `mgsPaddedEconomyQ_orthogonalityResidual_opNorm2Le_of_top_product_right_inverse`, `H19.Theorem19_13.paddedEconomyP11_rectOpNorm2Le_of_top_product_right_inverse`, `H19.Theorem19_13.paddedEconomyQ_orthogonalityResidual_opNorm2Le_of_top_product_right_inverse` | foundation started | Uses the source top-block equation `Delta A3 = P11 * R11` and a bounded right inverse for `R11` to derive `rectOpNorm2Le P11 (eta*rho)`, then combines it with full padded orthogonality to get `opNorm2Le (Q21^T Q21 - I) ((eta*rho)^2)`. This removes the arbitrary `P11`-smallness hypothesis from the pre-repair bound, while leaving the source right-inverse/condition estimates themselves open. |
| Ch19 Eq19.34 top-perturbation norm transport | `finiteVecNorm2_le_sumBothVec_left`, `mgsTopPerturbationColumnNorm_le_stacked`, `mgsTopPerturbation_frobNormRect_le_of_stackedColumnwiseBound`, `mgsTopPerturbation_rectOpNorm2Le_of_stackedColumnwiseBound`, `H19.Theorem19_13.topPerturbationColumnNorm_le_stacked`, `H19.Theorem19_13.topPerturbation_frobNormRect_le_of_stackedColumnwiseBound`, `H19.Theorem19_13.topPerturbation_rectOpNorm2Le_of_stackedColumnwiseBound` | foundation started | Converts the stacked `[Delta A3; Delta A4]` columnwise perturbation bound from `(19.34)` into a Frobenius and then operator-norm certificate for the top perturbation block `Delta A3`. This supplies the `Delta A3` norm input consumed by the top-block/right-inverse bridge; source right-inverse/condition estimates remain open. |
| Ch19 Eq19.34 stacked-bound top-right-inverse Gram bridge | `mgsPaddedEconomyQ_orthogonalityResidual_opNorm2Le_of_stacked_bound_top_product_right_inverse`, `H19.Theorem19_13.paddedEconomyQ_orthogonalityResidual_opNorm2Le_of_stacked_bound_top_product_right_inverse` | foundation started | Composes the top-perturbation norm transport with the top-block/right-inverse bridge: the stacked perturbation bound, the source top-block equation, and a bounded `R11` right inverse now directly imply the pre-repair operator-norm bound for `Q21^T Q21 - I`. The remaining open source work is to prove the right-inverse/condition estimates and the Problem 19.12 CS/polar pure correction-map data existence/budgets. |
| Ch19 Eq19.34 concrete Householder pre-repair Gram bridge | `H19.Theorem19_13.householder_paddedFinInput_pre_repair_gram_bound_of_right_inverse_budget` | foundation started | Instantiates the stacked-bound top-right-inverse Gram bridge on the concrete `fl_householderQRPanel_Q/R` objects from `householder_paddedFinInput_full_block_data`. Given a bounded right inverse for the extracted `R11` and a scalar residual budget, it directly yields the pre-repair `Q21^T Q21 - I` operator-norm certificate for the computed padded Householder handoff. |
| Ch19 Eq19.34 determinant/nonsingInv pre-repair Gram bridge | `H19.Theorem19_13.householder_paddedFinInput_pre_repair_gram_bound_of_det_ne_zero_inverse_budget` | foundation started | Specializes the concrete pre-repair bridge to the repository `nonsingInv`: nonzero determinant of the extracted `R11` supplies the right-inverse equation, while a `rectOpNorm2Le (nonsingInv R11) rho` budget supplies the condition estimate consumed by the Gram-residual route. The determinant proof and source condition-number/norm budget remain open. |
| Ch19 Eq19.34 upper-diagonal/nonsingInv pre-repair Gram bridge | `H19.Theorem19_13.householder_paddedFinInput_pre_repair_gram_bound_of_upper_diag_inverse_budget`, `H19.Theorem19_13.rectOpNorm2Le_nonsingInv_frobNorm` | foundation started | Uses `householder_paddedFinInput_full_block_data` to recover the upper-trapezoidal shape of the extracted `R11`, turns nonzero diagonal entries into the determinant hypothesis, and then reuses the determinant/nonsingInv pre-repair bridge. The fallback Frobenius certificate supplies a valid rectangular operator bound for `nonsingInv R11`; the source determinant/nonbreakdown proof and sharp inverse-norm/condition estimate remain open. |
| Ch19 Eq19.34 determinant-to-diagonal `R11` bridge | `H19.Theorem19_13.householder_paddedFinInput_R11_diag_ne_zero_of_det_ne_zero` | foundation started | Uses the full block-data upper-trapezoidal shape of the extracted `R11` to turn `det R11 != 0` into pointwise nonzero diagonal entries, so downstream upper-diagonal wrappers can be fed by a determinant/nonsingularity gate instead of separate diagonal facts. |
| Ch19 Problem 19.12 correction-map algebra | `MGSProblem1912CorrectionMapData.add_factor_eq`, `mgsProblem1912_correctionMapData_of_add_factor`, `MGSProblem1912CSDiagonalFactorData.add_factor_eq`, `mgsProblem1912_add_factor_exists_of_csDiagonalFactorData`, `mgsProblem1912_add_factor_exists_of_csDiagonalFactorData_nonempty`, `MGSProblem1912CorrectionMap`, `matMul_finiteDiagonal_self`, `matMul_finiteDiagonal_csSquareSum`, `mgsProblem1912_csDiagonal_square_sum`, `mgsProblem1912_correctionMap_of_csDiagonalAlgebra`, `mgsRepairedPerturbation_rectOpNorm2Le_of_bounds`, `mgsRepairedPerturbation_columnFrob_le_of_column_budget`, `mgsProblem1912_repair_of_csDiagonalAlgebra_of_perturbation_bounds`, and the `H19.Theorem19_13.problem1912_*` wrappers | foundation started | Appendix A solution 19.12 uses the CS decomposition to build a bounded correction map `F` that changes the bottom block `P21` into an orthonormal `Q`. The compiled algebra proves the CS factor identity, the diagonal CS square identity `C^2+S^2=I`, the additive pure-data orientation `Q = P21 + F*P11`, the packaged factor-data additive witness/existence projections, the orthogonal/diagonal correction-map constructors, the diagonal `T*C = I-S` and `||T||_2 <= 1` estimates, the repaired `F*dTop + dBottom` operator/column budgets from top/bottom inputs, and the repaired common-`R` factorization. The remaining Problem 19.12 gate is the CS/polar existence theorem supplying the diagonal factor data and orthogonality data; the concrete Householder-stacked assembly now derives the needed top/bottom budget inputs from the actual `(19.34)` stacked perturbation bound. |
| Ch19 Eq19.35-19.37 upper-diagonal repair-data assembly | `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_repair`, `H19.Theorem19_13.Problem1912CSDiagonalFactorData`, `H19.Theorem19_13.problem1912_correctionMapData_of_csDiagonalFactorData`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_perturbation_bounds`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_stacked_budget`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_budget`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_budget_of_small_unit_roundoff`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_budget_frobInv`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_budget_frobInv_of_small_unit_roundoff`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalFactorDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_csDiagonalFactorDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalFactorDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_csDiagonalFactorDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`, and their small-unit/fallback `MGSQRBounds` wrappers | foundation started | Assembles the concrete padded Householder handoff, upper-diagonal/nonsingInv route, common-`R` sensitivity algebra, exact-unit-roundoff residual budget, pure correction-map data target, packaged diagonal-CS factor-data target, diagonal-CS repair data, and repaired perturbation budgets into the source-output bridge and current `MGSQRBounds` contract. The data-first wrappers consume pure `Problem1912CorrectionMapData` and carry it through the actual stacked perturbation handoff into `MGSQRBounds`; the pure-data fixed-budget wrappers reuse the same top/bottom residual budget, specialize `eta2 = 2*eta1`, fix `c3 = 4*k`, and the pure-data `frobInv` variants discharge the fallback inverse-norm certificate with `rho = ||nonsingInv R11||_F`. The factor-data fixed-budget wrappers consume one `Problem1912CSDiagonalFactorData` object, convert it to pure correction-map data internally, and reuse the same explicit-`rho` and Frobenius-inverse fixed-budget routes; the new determinant factor-data wrappers use the same conversion while replacing the pointwise diagonal gate by `det R11 != 0`, including `Nonempty` and Frobenius-inverse variants. The strongest diagonal-CS wrapper follows the same fixed-budget surface, with its own `frobInv` variants available as fallback inverse certificates. Remaining gates are CS/polar existence producing the factor-data payload, source determinant/nonbreakdown, sharp inverse-norm/condition estimates, printed constants/final radius budget, and final `mgs_qr_bounds` export. |
| Ch19 common-`R` perturbation algebra and norm bridge | `matMulRect_sub_left_square_right`, `rectOpNorm2Le_sub`, `commonR_difference_product_eq_perturbation_difference`, `commonR_difference_eq_perturbation_difference_mul_right_inverse`, `commonR_difference_rectOpNorm2Le_of_perturbation_difference_mul_right_inverse`, `commonR_difference_rectOpNorm2Le_of_perturbation_bounds_mul_right_inverse`, `H19.Theorem19_13.commonR_difference_product_eq_perturbation_difference`, `H19.Theorem19_13.commonR_difference_eq_perturbation_difference_mul_right_inverse`, `H19.Theorem19_13.commonR_difference_rectOpNorm2Le_of_perturbation_difference_mul_right_inverse`, `H19.Theorem19_13.commonR_difference_rectOpNorm2Le_of_perturbation_bounds_mul_right_inverse` | foundation started | Proves the exact algebraic bridge from two factorizations with the same `Rhat` to `(Qhat - Q) * Rhat = dA1 - dA2`, the right-inverse form `Qhat - Q = (dA1 - dA2) * Rinv`, and the operator-norm consequence from perturbation and `Rinv` certificates. Source construction and condition-bound estimates for `Rinv` remain open. |
| Ch19 Gram-residual expansion and norm conversion | `GramSchmidtOrthonormalColumns.rectOpNorm2Le_one`, `gramSchmidtOrthogonalityResidual_eq_close_expansion`, `gramSchmidtOrthogonalityResidual_opNorm2Le_of_close_orthonormal`, `H19.Theorem19_13.orthonormalColumns_rectOpNorm2Le_one`, `H19.Theorem19_13.gramSchmidtOrthogonalityResidual_eq_close_expansion`, `H19.Theorem19_13.gramSchmidtOrthogonalityResidual_opNorm2Le_of_close_orthonormal` | foundation started | Proves the exact expansion of `Qhat^T Qhat - I` around an orthonormal `Q` and converts a `rectOpNorm2Le (Qhat - Q) delta` closeness certificate into the `2*delta + delta^2` operator-norm orthogonality-loss bound. |
| Ch19 QR sensitivity assembly | `ModifiedGramSchmidtQRSensitivityBridge`, `ModifiedGramSchmidtBackwardError.of_economy_product_sensitivity`, `H19.Theorem19_4.gamma_tilde_nonneg`, `H19.Theorem19_13.QRSensitivityBridge`, `H19.Theorem19_13.paddedEconomyR_upper_trapezoidal`, `H19.Theorem19_13.householder_paddedFinInput_economyProduct_with_upper`, `H19.Theorem19_13.bottomPerturbationColumnNorm_le_stacked`, `H19.Theorem19_13.bottomPerturbation_frobNormRect_le_of_stackedColumnwiseBound`, `H19.Theorem19_13.bottomPerturbation_rectOpNorm2Le_of_stackedColumnwiseBound`, `H19.Theorem19_13.topPerturbationColumnNorm_le_stacked`, `H19.Theorem19_13.topPerturbation_frobNormRect_le_of_stackedColumnwiseBound`, `H19.Theorem19_13.topPerturbation_rectOpNorm2Le_of_stackedColumnwiseBound`, `H19.Theorem19_13.residualBudget_of_gamma_tilde_le_mul_norm_bound`, `H19.Theorem19_13.residualBudget_of_gamma_tilde_le_mul_self`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_economy_product_sensitivity`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_economy_product_sensitivity_of_residual_budget`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_economy_product_sensitivity_of_valid_residual_budget`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_economy_product_sensitivity_of_coefficient_norm_budget`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_economy_product_sensitivity_of_coefficient_budget` | foundation started | This connects the compiled `(19.34)` economy product to the existing `MGSQRBounds` contract once the source-labeled `(19.35a)`-`(19.37)` QR-sensitivity outputs are supplied; the coefficient-budget side is closed on the exact-unit-roundoff smallness route, and both the bottom `Delta A4` and top `Delta A3` perturbation blocks now have operator-norm transport from the stacked columnwise bound. It is an explicit bottleneck interface, not the final Theorem 19.13 proof. |
| Ch19 QR sensitivity source-output bridge | `ModifiedGramSchmidtQRSensitivitySourceOutput`, `ModifiedGramSchmidtQRSensitivitySourceOutput.of_commonR_bounds`, `ModifiedGramSchmidtQRSensitivityBridge.of_source_output`, `H19.Theorem19_13.QRSensitivitySourceOutput`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_commonR_bounds`, `H19.Theorem19_13.qrsensitivityBridge_of_source_output`, `H19.Theorem19_4.gamma_tilde_le_two_index_mul_unit_roundoff_of_small`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_economy_product_source_sensitivity_of_coefficient_budget`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_economy_product_source_sensitivity_of_small_unit_roundoff` | foundation started | This splits the remaining `(19.35a)`-`(19.37)` dependency into source-labeled outputs before assembling the compact bridge, closes the coefficient-budget side for the exact-unit-roundoff route under `k*u <= 1/2`, and conditionally assembles the source-output fields from two common-`R` factorizations, an orthonormal repaired witness, perturbation operator certificates, an `Rhat` right inverse, and the scalar budget `2*((eta1+eta2)*rho)+((eta1+eta2)*rho)^2`. CS/polar pure correction-map data existence/budgets, right-inverse/condition estimates, exact printed constants, and final `H19.Theorem19_13.mgs_qr_bounds` export remain open. |

Latest Ch19 Givens stage-accumulation dependency layer:
`fl_givensQRStagePrefix_zeroedThrough`,
`fl_givensQRStagePrefix_task_residual_uniform`,
`fl_givensQRStagePrefix_eq_taskList_append`,
`fl_givensQRStageTaskList_prefix_zeroedThrough`,
`fl_givensQRStageTasks_take_succ_eq_step`,
`fl_givensQRStageTaskList_prefix_succ_eq_step`, and
`fl_givensQRTaskStep_columnFrob_residual_of_prev_pair_zero`,
`fl_givensQRTaskStepOfTask_columnFrob_residual_of_zeroedThrough`,
`fl_givensQRTaskStepOfTask_columnFrob_uniform_of_zeroedThrough`,
`orthogonal_sequence_one_step_of_columnFrob_residual_rect`,
`residual_orthogonal_sequence_columnFrob_backward_error_rect`,
`fl_givensQRTask_sequence_columnFrob_backward_error_uniform`,
`fl_givensQRStageTaskList_prefix_task_residual_uniform`,
`fl_givensQRStageTasks_prefix_task_columnFrob_uniform`,
`fl_givensQRStageTasks_sequence_backward_error_uniform`, and
`fl_givensQRStageTasks_sequence_columnFrob_backward_error_uniform`, and
`fl_givensQRStageFold_sequence_backward_error_uniform`, and
`fl_givensQRStageFold_sequence_columnFrob_backward_error_uniform` now compile.  These
instantiate the task columnwise residual, frontier, residual, successor-step,
generic task columnwise accumulation, single-stage normwise and columnwise
accumulation, and conservative stage-fold normwise and columnwise accumulation
obligations over the concrete schedule; `H19.Theorem19_10.givens_qr_backward_error`
now exports the public wrapper with the repository's conservative `gamma_tilde`.

## Completed selected targets

| Source row | Lean name | File | Status |
|---|---|---|---|
| Higham Theorem 19.4 | `H19.Theorem19_4.householder_qr_backward_error` | `LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean` | Proved source-facing wrapper for the concrete Householder QR panel algorithm; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| Higham Theorem 19.10 | `H19.Theorem19_10.givens_qr_backward_error` | `LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean` | Proved source-facing wrapper for the concrete staged Givens QR algorithm with conservative `gamma_tilde`; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. |

## External proof sources and GPT-5.5 Pro consultations

| Selected claim/blocker | Oracle session/model | Prompt summary | Key route suggested | Adopted/rejected steps | Lean validation | Status |
|---|---|---|---|---|---|---|
| Ch19 two-column actual-active stored endpoint proof script | `split3b-ch19-proof-repair`, ChatGPT browser `gpt-5.5-pro` resolved as Pro Extended | Compact proof packet with only the local theorem skeleton, available facts `hqr`, `hS1`, `hfull`, and the Lean rewrite failure; no PDFs or bulk Lean files | Keep `Sfull` abstract long enough to use `hfull.symm`; prove a separate `panelFromTopAndTrailing ... S1Norm = Sfull` bridge, then close with transitivity and final `simpa` | Adopted as proof-script repair only; first no-file Oracle attempt was a non-answer and was not used | `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` PASS; `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` PASS; axiom probe only `propext`, `Classical.choice`, `Quot.sound` | advisory accepted and locally formalized |
| Split 3B ordering and QR interface triage | `higham-split3b-current`, `gpt-5.5-pro` browser | Compact reviewed Split 3B planning packet, no PDFs or bulk Lean files | Prioritize Ch19 outward QR interfaces; treat existing QR files as candidate foundations until source-label audit | Adopted for audit ordering; not proof evidence | Oracle status rechecked through bundled Node/pnpm; session completed | advisory accepted for workflow only |
| Ch19 Theorem 19.10 Givens QR blocker | `higham-split3b-givens-inline`, `gpt-5.5-pro` browser | Compact route packet with prompt file and local Givens/H19 files; no PDFs, no secrets, no bulk repo export | Do not wrap current sequence theorems; first prove a sparse zero-aware Givens task step, disjoint-stage schedule, upper-trapezoidal invariant, and columnwise stage accumulation | Adopted as route constraint; no theorem equivalent hypothesis may be added to `H19.Theorem19_10.*` | Advisory route recorded; the advised route now compiles through sparse residuals, zero-aware task residuals, generic normwise/columnwise sequence accumulation, same-stage and full stage-fold accumulation, upper-trapezoidal invariants, and the public `H19.Theorem19_10.givens_qr_backward_error` wrapper | advisory route completed for public wrapper |
| Ch19 Theorem 19.13 QR-sensitivity/source-output blocker | `split3b-qr-sensitivit`, `gpt-5.5-pro` browser, resolved `Pro Extended`, verified `yes` | Prompt file plus current `GramSchmidt.lean`, `Higham19.lean`, `Rounding.lean`, Ch19 inventory, and complete audit | Treat `QRSensitivitySourceOutput` as final output channels only; restore full `(19.34)` block data including `Delta A3 = P11 * R11` and full padded orthogonality, then prove/import Problem 19.12 CS/polar pure correction-map data existence/budgets and source right-inverse/condition estimates for the common-`R` route | Adopted the full-block-data route; CS factor algebra, pure correction-map data/algebra, common-`R` algebra and norm bridge, Gram-residual expansion, Gram-residual norm conversion, and conditional source-output assembly from common-`R` bounds now compile; rejected treating `(19.35a)`-`(19.37)` alone as enough for Theorem 19.13 | Full block-data, common-`R` algebra/norm, Gram-expansion, Gram-norm, source-output common-`R`, and Problem 19.12 CS/correction-map probes report only `propext`, `Classical.choice`, and `Quot.sound` | advisory partially translated into checked Lean |
| Ch19 Problem 19.12 CS/polar existence gate | `split3b-cs-polar`, `gpt-5.5-pro` browser | Compact math-only packet asking for a source-faithful CS/polar proof route and hidden-assumption audit; no files attached | Expose a pure correction-map data object first: orthonormal `Q`, `Q = P21 + F*P11`, and `||F||_2 <= 1`; build it from CS/polar data, then transport it to the common-`R` map. Keep the full block data `(Delta A3 = P11*R11)`, `(A+Delta A4 = P21*R11)`, and `P11^T P11 + P21^T P21 = I`. | Adopted the data-first interface, additive orientation, and packaged factor-data additive projections: `MGSProblem1912CorrectionMapData`, `MGSProblem1912CorrectionMapData.add_factor_eq`, `mgsProblem1912_correctionMapData_of_add_factor`, `MGSProblem1912CSDiagonalFactorData.add_factor_eq`, `mgsProblem1912_add_factor_exists_of_csDiagonalFactorData_nonempty`, and the H19 `problem1912_*add_factor*` wrappers now compile. This is a checked target for the future CS/polar theorem, not an existence proof. | Reattached with bundled `pnpm.cmd dlx @steipete/oracle session split3b-cs-polar --render`; transcript saved under `C:\Users\User\.oracle\sessions\split3b-cs-polar\artifacts\transcript.md`. Focused GramSchmidt and H19 checks/builds pass after translating the advice into Lean; the latest packaged additive-witness probe reports only `propext`, `Classical.choice`, and `Quot.sound`. | advisory partially translated into checked Lean |

Browser connectivity note: Oracle browser mode is usable for GPT-5.5 Pro
consultations, but long browser runs can detach and should be reattached before
treating a session as failed.  The QR-sensitivity run selected a visible Chrome
session and reported model evidence `requested=Pro`,
`resolved=Pro Extended`, `status=switched`, and `verified=yes`.  The later
CS/polar run `split3b-cs-polar` initially detached, then reattached on
2026-06-25 with `oracle session split3b-cs-polar --render`; the transcript was
saved and the session marked completed.

## Open selected-scope items

Ch19 Theorem 19.13 now has a compiled generic extraction/eta bridge for the
printed `(19.34)` perturbation shape, a row-shape bridge to the `Fin (n + m)`
input expected by Theorem 19.4, column-norm/bound transport into
`mgsStackedPerturbationColumnwiseBound`, and Theorem 19.4 instantiated on
`paddedFinInput A`.  The block-form handoff now packages the printed
perturbed product equation, zero bottom `Rhat` block, the bottom economy
product `A + Delta A4 = Q21 * R11`, the top block `Delta A3 = P11 * R11`,
full padded orthogonality, the upper shape of `R11`, and the pre-repair
top-block/right-inverse Gram-residual norm bridge.  The common-`R`
norm bridge plus Gram-residual norm conversion now conditionally assemble the
source-output fields through `H19.Theorem19_13.qrsensitivitySourceOutput_of_commonR_bounds`.
The CS/polar correction-map theorem now supplies the repair data.  The next
open gate is the full recursive/stored final-panel equality, using the
one-column self-dot terminal bridge plus the existing active-entry and
trailing-panel lifts.  The remaining source-output work is to add the source
condition estimates needed to instantiate the common-`R` theorem at the printed
strength and audit the final constants.

| Source location | Exact selected claim | Current Lean status | Why current results do not close it | Missing foundation | Next concrete theorem/action | Blocking final gate? |
|---|---|---|---|---|---|---|
| Ch16 all selected rows | 32 equations, 5 problems, section-level Sylvester/Lyapunov claims | candidate foundations only | Existing Sylvester files are old-numbered and not mapped to the Ch16 source formulas. | rendered statement inventory and source-label map | Extract exact rows and map each to `Sylvester*` declarations. | yes |
| Ch17 all selected rows | 35 equations, problem 17.1, section-level stationary iteration claims | candidate foundations only | Existing stationary-iteration file is old-numbered and not mapped to Ch17. | rendered statement inventory and source-label map | Extract exact rows and map to `StationaryIteration.lean`. | yes |
| Ch18 Theorems 18.1-18.2 | matrix-power finite precision theorems | partial foundation | Existing `higham_knight_17_1` and related theorems are not mapped to current Ch18 theorem statements. | theorem-surface audit | Render Theorems 18.1-18.2 and compare hypotheses/constants to local theorem types. | yes |
| Ch19 Theorem 19.13 | MGS QR bounds | conditional source-facing theorem plus open source-strength gates | The exact algorithm/state, row `(19.32)` source-stage recurrence, row `(19.33)` product/factorization foundation, exact `A = Q R` theorem, `(19.27)`-`(19.28)` padded-input/vector vocabulary, `v_k^T v_k = 2` normalization channel for computed MGS columns, diagonal scalar channel `q_k^T a_k^(k) = r_kk`, exact reflector symmetry/involution lemmas, one-reflector `[0; A]` action lemmas, padded-stage component lemmas, padded-stage endpoints `[0; A]` and `[R; 0]`, exact forward/reverse one-step padded-stage transitions, forward-prefix endpoint from `[0; A]` to `[R; 0]`, reverse-prefix endpoint from `[R; 0]` to `[0; A]`, exact top/bottom block extraction, generic `[Delta A3; A + Delta A4]` perturbation shape, row reindexing, stacked-column bound transport, Theorem 19.4 padded-input handoff, block-form `(19.34)` perturbed product equation, economy-product extraction `A + Delta A4 = Q21 * R11`, top-block extraction `Delta A3 = P11 * R11`, full padded orthogonality, block-column Gram identities, CS/polar correction-map existence, repaired-budget algebra, concrete Householder-stacked source-output wrappers, common-`R` right-inverse algebra and norm bridge, exact Gram-residual expansion plus `2*delta + delta^2` operator-norm conversion, conditional QR-sensitivity assembly bridges, the determinant/source-condition/fallback `MGSQRBounds` wrappers, the one-column stored/recursive self-dot beta bridge, the successor-pivot beta-one stored-step reconstruction, and the two-column actual-active stored endpoint compile. The chapter-facing `H19.Theorem19_13.mgs_qr_bounds` exists under explicit `det R11 != 0` and final budget hypotheses. | Full recursive/stored final-panel equality, source right-inverse/condition estimates for `R11`, final radius/constant budget audit, and rendered source comparison | Generalize the two-column actual-active endpoint into the arbitrary-width two-step bridge and then the full stored-loop final-panel equality; afterwards replace remaining determinant/budget/source-condition hypotheses by source-derived nonbreakdown and conditioning estimates where the printed theorem supplies them. | yes |
| Appendix A Split 3B rows | solution proofs for 16.x-19.x | inventory-accounted only | Solution statements have not been audited for omitted proof dependencies. | Appendix A extraction | Read A.16-A.19 rows and link to main text rows. | yes |

Latest refinement to the Ch19 row: the terminal one-column recursive/stored
final-panel bridge and the successor-pivot stored-step reconstruction now accept
the source-shaped self-dot normalization `v^T v = 2`.  The support lemma
`householderBetaSpec_eq_one_of_inner_self_eq_two`, the successor wrappers
`H19.Theorem19_13.householderBetaSpec_zero_cons_eq_one_of_inner_self_eq_two`
and
`H19.Theorem19_13.householderBetaSpec_trailingActiveVector_succ_zeroPrefix_eq_one_of_tail_self_dot`,
the stored-step bridges
`H19.Theorem19_13.storedPanelStep_succ_trailingActiveVector_one_eq_panelFromTopAndTrailing_one_of_tail_self_dot_of_subtractZeroExact_of_succ`
and
`H19.Theorem19_13.storedPanelStep_succ_trailingActiveVector_one_eq_panelFromTopAndTrailing_one_of_tail_self_dot_of_subtractZeroExact_anyCols`,
and the one-column wrappers
`H19.Theorem19_13.storedSigned_one_col_final_panel_eq_qrPanel_R_of_reflector_self_dot`
and
`H19.Theorem19_13.storedSignedSequence_one_col_final_panel_eq_qrPanel_R_of_reflector_self_dot`
remove raw `householderBetaSpec ... = 1` premises from the active base and
successor steps.  The next action is to assemble these bridges through the
shrinking-panel stored sequence, then discharge the remaining source `R11`
nonbreakdown/condition estimates and printed-constant audits for the final
Theorem 19.13 surface.

Newest Ch19 refinement: the two-column endpoint now uses the actual stored-loop
pivot-1 active vector, not only an artificial zero-prefixed normalized vector.
The theorem
`H19.Theorem19_13.qrPanel_R_two_col_eq_secondStoredActiveStep_one_of_tail_reflector_self_dot_of_subtractZeroExact`
packages the determinant-specialized recursive two-column `R` panel with the
successor-pivot self-dot beta bridge and exact-copy stored-step reconstruction.
The next concrete theorem is the arbitrary-width two-step analogue with actual
pivot-1 active-vector data, then the full induction over the stored sequence.

## Foundation feasibility gate

The Ch19 Problem 19.12 gate now also includes the additive-orientation wrappers
`H19.Theorem19_13.problem1912_correctionMapData_add_factor_eq`,
`H19.Theorem19_13.problem1912_correctionMapData_of_add_factor`,
`H19.Theorem19_13.problem1912_csDiagonalFactorData_add_factor_eq`, and
`H19.Theorem19_13.problem1912_add_factor_exists_of_csDiagonalFactorData_nonempty`;
future CS/polar work can target the source-facing identity
`Q = P21 + F*P11`, or packaged diagonal factor data, and then hand it to the
stored subtraction-oriented data interface.

| Selected theorem/source | Intended Lean theorem | Required foundation | Status | Existing theorem/source | Smallest next Lean target | Downstream work allowed? |
|---|---|---|---|---|---|---|
| Ch19 Theorem 19.4 | `H19.Theorem19_4.householder_qr_backward_error` | Householder vector/apply lemmas, QR panel semantics, exact orthogonal witness, upper-trapezoidal `R`, columnwise bound, gamma validity | exported wrapper | `fl_householderQRPanel_R_columnwise_backward_error_gammaHigham_of_global_gammaValid` | Wrapper built after rendered source check; keep sign-convention/equation-row audit as weak-component documentation. | Split 4 may import the Householder QR contract. |
| Ch19 Theorem 19.10 | `H19.Theorem19_10.givens_qr_backward_error` | Givens coefficient/apply lemmas, sparse two-row step, disjoint-stage accumulation, concrete annihilation schedule, triangular shape, source constants | exported wrapper | `fl_givensQRTaskStepOfTask_sparse_residual_of_zeroedThrough`, `fl_givensQRTaskStep_columnFrob_residual_of_prev_pair_zero`, `fl_givensQRTaskStepOfTask_columnFrob_residual_of_zeroedThrough`, `fl_givensQRTaskStepOfTask_columnFrob_uniform_of_zeroedThrough`, `orthogonal_sequence_one_step_of_columnFrob_residual_rect`, `residual_orthogonal_sequence_columnFrob_backward_error_rect`, `fl_givensQRTask_sequence_columnFrob_backward_error_uniform`, `fl_givensQRStageTasks_sequence_columnFrob_backward_error_uniform`, `fl_givensQRStageFold_sequence_columnFrob_backward_error_uniform`, `fl_givensQRStageFold_upper_trapezoidal`, `fl_givensQRStageTaskList_upper_trapezoidal`, and one-step Givens kernels | Wrapper built with conservative staged-schedule `gamma_tilde`; keep exact printed-constant/equation-row audit as weak-component documentation. | Split 4 may import the Givens QR contract. |
| Ch19 Theorem 19.13 | `H19.Theorem19_13.mgs_qr_bounds` | CGS/MGS algorithms, dot/norm/update FP model, residual bound, orthogonality-loss bound, R-factor quality, condition-number assumptions | foundation-started | Exact MGS and Householder-MGS bridge declarations listed in the Ch19 CGS/MGS candidate-map row above, through `mgsStackedPerturbationColumnwiseBound`, `H19.Theorem19_13.householder_paddedFinInput_stackedPerturbation`, `H19.Theorem19_13.householder_paddedFinInput_perturbedInput_blocks`, `H19.Theorem19_13.householder_paddedFinInput_economyProduct`, `H19.Theorem19_13.householder_paddedFinInput_economyProduct_with_upper`, `H19.Theorem19_13.householder_paddedFinInput_full_block_data`, `H19.Theorem19_13.paddedEconomy_blocks_gram_sum_eq_id`, `H19.Theorem19_13.paddedEconomyQ_gram_eq_id_sub_P11_gram`, `H19.Theorem19_13.paddedEconomyQ_orthogonalityResidual_eq_neg_P11_gram`, `H19.Theorem19_13.Problem1912CSDiagonalFactorData`, `H19.Theorem19_13.problem1912_csDiagonalFactorData_of_csDiagonalAlgebra`, `H19.Theorem19_13.problem1912_csDiagonalFactorData_exists_of_csDiagonalAlgebra`, `H19.Theorem19_13.Problem1912CorrectionMapData`, `H19.Theorem19_13.Problem1912CorrectionMap`, `H19.Theorem19_13.problem1912_csAlgebra_correction_factor`, `H19.Theorem19_13.problem1912_correctionMapData_of_csAlgebra`, `H19.Theorem19_13.problem1912_correctionMapData_to_correctionMap`, `H19.Theorem19_13.problem1912_correctionMap_of_csAlgebra`, `H19.Theorem19_13.problem1912_correctionMapData_of_csOrthogonalAlgebra`, `H19.Theorem19_13.problem1912_correctionMap_of_csOrthogonalAlgebra`, `H19.Theorem19_13.problem1912_opNorm2Le_finiteDiagonal_csHalfTangent`, `H19.Theorem19_13.problem1912_matMul_finiteDiagonal_csHalfTangent`, `H19.Theorem19_13.problem1912_correctionMapData_of_csDiagonalAlgebra`, `H19.Theorem19_13.problem1912_correctionMap_of_csDiagonalAlgebra`, `H19.Theorem19_13.problem1912_repair_of_correctionMap`, `H19.Theorem19_13.problem1912_repair_of_csDiagonalAlgebra`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_budget`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_budget_of_small_unit_roundoff`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_budget_frobInv`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_budget_frobInv_of_small_unit_roundoff`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_budget`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_budget_of_small_unit_roundoff`, `H19.Theorem19_13.gamma_tilde_two_column_budget`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_same_residual_budget`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_same_residual_budget_of_small_unit_roundoff`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_budget`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_budget_of_small_unit_roundoff`, `H19.Theorem19_13.gamma_tilde_two_le_four_index_mul_unit_roundoff_of_small`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`, `H19.Theorem19_13.commonR_difference_product_eq_perturbation_difference`, `H19.Theorem19_13.commonR_difference_eq_perturbation_difference_mul_right_inverse`, `H19.Theorem19_13.commonR_difference_rectOpNorm2Le_of_perturbation_bounds_mul_right_inverse`, `H19.Theorem19_13.gramSchmidtOrthogonalityResidual_eq_close_expansion`, `H19.Theorem19_13.gramSchmidtOrthogonalityResidual_opNorm2Le_of_close_orthonormal`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_commonR_bounds`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_economy_product_sensitivity`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_economy_product_sensitivity_of_residual_budget`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_economy_product_sensitivity_of_valid_residual_budget`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_economy_product_sensitivity_of_coefficient_norm_budget`, and `H19.Theorem19_13.mgs_qr_bounds_of_householder_economy_product_sensitivity_of_coefficient_budget`; contract predicate `ModifiedGramSchmidtBackwardError` and source-facing `H19.Theorem19_13.MGSQRBounds` compile. | Prove/import CS/polar existence and diagonal factor data for the explicit CS witnesses or `H19.Theorem19_13.Problem1912CSDiagonalFactorData` using the full block data and block-column Gram identities, feed that payload through the factor-data fixed-budget Householder-stacked source-output route, then add source right-inverse/condition estimates and final source constant/radius budget; keep `(19.35a)`-`(19.37)` as separate Section 19.9 source rows. | No proof-level downstream dependency. |
| Ch18 Theorems 18.1-18.2 | `H18.Theorem18_1.*`, `H18.Theorem18_2.*` | matrix powers, exact/Jordan decomposition or local model, finite precision recurrence, convergence/pseudospectral conditions | route-choice | `MatrixPowers.lean` | Compare rendered theorem statements to `higham_knight_17_1` and related lemmas. | Inventory and dependency audit only. |
| Ch16 practical bounds | `H16.*` condition/practical-bound contracts | Sylvester condition number, inverse/GJE or condition-estimation contracts from Split 3A if explicit | route-choice | `SylvesterPerturbation.lean`; possible Split 3A placeholders | Extract exact equations 16.28-16.32 and identify external contracts. | Do not duplicate Ch13-Ch15. |

Feasibility update: the Ch19 row's pure-data path now additionally includes
`H19.Theorem19_13.problem1912_repair_of_correctionMapData`,
`H19.Theorem19_13.problem1912_repair_of_correctionMapData_of_perturbation_bounds`,
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair`,
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_perturbation_bounds`,
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_stacked_budget`,
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_budget`,
`H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_budget_of_small_unit_roundoff`,
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_budget_frobInv`, and
`H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_budget_frobInv_of_small_unit_roundoff`,
plus the fixed-budget pure-data wrappers
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`,
`H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`,
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`, and
`H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`.
The determinant-nonzero pure-data wrappers
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_det_ne_zero_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`,
`H19.Theorem19_13.mgs_qr_bounds_of_householder_det_ne_zero_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`,
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_det_ne_zero_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`, and
`H19.Theorem19_13.mgs_qr_bounds_of_householder_det_ne_zero_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`
replace the pointwise `R11` diagonal hypothesis by a single determinant
nonzero certificate; matching `correctionMapDataExistsRepair` variants consume
pure correction-map-data existence directly.
The determinant-nonzero factor-data wrappers
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_det_ne_zero_csDiagonalFactorDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`,
`H19.Theorem19_13.mgs_qr_bounds_of_householder_det_ne_zero_csDiagonalFactorDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`,
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_det_ne_zero_csDiagonalFactorDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`, and
`H19.Theorem19_13.mgs_qr_bounds_of_householder_det_ne_zero_csDiagonalFactorDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`
now consume packaged CS factor data, or `Nonempty` packaged factor data, by
converting it to pure correction-map data internally.
The pure-data existence wrappers
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`,
`H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_correctionMapDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`,
`H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`, and
`H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_correctionMapDataExistsRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`
now select the repaired `Q`/`F` witnesses internally from
`Exists Q F, Problem1912CorrectionMapData ...`.
The next Lean target is no longer common-`R` transport, scalar-budget transport
from data, or diagonal-to-determinant plumbing; it is the actual CS/polar
existence theorem producing that data, followed by source determinant
nonbreakdown and inverse/condition estimates.

The sharper immediate target is to produce either
`Exists Q F, H19.Theorem19_13.Problem1912CorrectionMapData ...` or the stronger
`H19.Theorem19_13.Problem1912CSDiagonalFactorData`/`Nonempty` payload for the
actual padded Householder block.  The factor-data bridge converts the stronger
payload to pure correction-map data internally, and both data-existence routes
reuse the checked fixed-budget explicit-`rho` or Frobenius-inverse
source-output routes.

Additional Ch19 Problem 19.12 CS-data consequences now compiled:
`H19.Theorem19_13.problem1912_matMul_finiteDiagonal_csSquareSum`,
`H19.Theorem19_13.problem1912_csDiagonal_square_sum`,
`H19.Theorem19_13.problem1912_csDiagonal_gram_sum_eq_id`,
`H19.Theorem19_13.problem1912_opNorm2Le_finiteDiagonal_csSine`, and
`H19.Theorem19_13.problem1912_opNorm2Le_finiteDiagonal_csCosine`, plus
`H19.Theorem19_13.problem1912_p21_rectOpNorm2Le_one_of_csDiagonalAlgebra`
and `H19.Theorem19_13.problem1912_p11_opNorm2Le_one_of_csDiagonalAlgebra`.
They close the diagonal square identity `C^2+S^2=I`, the diagonal `S`/`C`,
bottom-block `P21 = V*S*W^T`, and top-block `P11 = U*C*W^T` contraction
consequences under supplied CS factor data; they do not close CS/polar
existence itself.

## Hidden-hypothesis summary

The H19.4 and H19.10 source-facing wrappers are closed and have their axiom
checks recorded above.  No final MGS stability theorem is closed yet, so there
is no final Theorem 19.13 hypothesis list.  The current hidden-hypothesis risks
are:

- Old numbering: several candidate files appear shifted by one chapter relative
  to the current Split 3B contract.
- Floating-point validity: QR and iteration/power bounds depend on explicit
  `gammaValid` or unit-roundoff side conditions; those must remain visible on
  source-facing theorem surfaces.
- Computed versus analysis-only objects: Householder/Givens QR theorems must
  distinguish exact `Q`, computed/stored `R`, computed vectors/rotations, and
  analysis-only perturbations.
- Algorithm identity: Givens sequence results do not automatically close a full
  Givens QR theorem without the annihilation schedule and triangular-shape proof.
- MGS stability still open: the compiled contract shape is not a theorem; no
  proof may assume the residual or orthogonality bound as a hypothesis and
  count it as Theorem 19.13.
- MGS source-output split: GPT-5.5 Pro audit identified that `(19.35a)`-
  `(19.37)` alone do not provide the current output fields.  The top block
  `Delta A3 = P11 * R11` and full padded orthogonality now compile as explicit
  data, the block-column Gram identities for `P11` and `Q21` compile, the
  pre-repair top-block/right-inverse Gram-residual norm consequence compiles, the
  common-`R` right-inverse algebra and norm bridge compile, the
  exact Gram-residual expansion plus norm conversion compiles, and the
  conditional common-`R` source-output assembly compiles.  Problem
  19.12/CS-polar repair, source right-inverse/condition estimates,
  nonsingularity/smallness,
  and higher-order bookkeeping remain open.

## Weak-component and bottleneck summary

Weak components requiring at least two independent checks before closure:

| Component | Why weak | First check | Second check still needed | Status |
|---|---|---|---|---|
| Ch16 Sylvester mapping | old numbering and perturbation theorem surfaces | repo theorem scan done | rendered source/formula comparison | open |
| Ch17 stationary iteration mapping | old numbering and many recurrence formulas | repo theorem scan done | rendered source/formula comparison | open |
| Ch18 matrix-power theorem mapping | old numbering and imported Higham-Knight theorem | repo theorem scan done | rendered source/formula comparison | open |
| Ch19 Householder QR wrapper | implementation-facing FP theorem with many computed objects | rendered theorem page, focused compile, `#check`, and `#print axioms` done | sign-choice universality and equation-row cross-link audit | exported, watch |
| Ch19 Givens QR wrapper | theorem about full algorithm, not just step sequence | rendered Theorem 19.10, focused compile, GPT-5.5 Pro route audit, public wrapper compile, and `#print axioms` done | exact printed constant and equation-row cross-link audit | exported, watch |
| Ch19 MGS theorem | stability foundation missing after algorithm/spec start | Rendered pages 370-373 inspected; compiled CGS/MGS skeleton, exact `(19.32)`-`(19.33)` foundations, diagonal scalar/unit-column channel, `(19.27)`-`(19.28)` padded/vector bridge, exact reflector symmetry/involution, one-reflector `[0; A]` action lemmas, padded-stage `[0; A]`/`[R; 0]` endpoints, forward/reverse one-step padded-stage transitions, forward-prefix endpoint, reverse-prefix endpoint, exact top/bottom block extraction, and generic `[Delta A3; A + Delta A4]` perturbation vocabulary done | residual/orthogonality/R-factor proof route | foundation started |
| Ch19 MGS source-output bridge | risk of mislabeled QR-sensitivity output hiding repair assumptions | GPT-5.5 Pro audit completed; full `(19.34)` block-data theorem, block-column Gram identities for `P11`/`Q21`, CS/polar correction-map existence, pure correction-map data/algebra, data-first repair/source-output/MGSQRBounds bridge with pure-data fixed-budget and Frobenius-inverse fallbacks, determinant-nonzero `R11` wrappers, common-`R` right-inverse algebra and norm bridge, exact Gram-residual expansion, Gram-residual norm conversion, conditional source-output assembly from common-`R` bounds, the self-dot beta bridges, and the actual-active two-column recursive/stored endpoint compile with clean checks | prove the arbitrary-width/full recursive/stored final-panel equality, source determinant nonbreakdown/right-inverse/condition estimates, and final constants/radius audit | foundation started |

The Ch19 Problem 19.12 CS/polar bottleneck ledger is resolved in
`chapter_splitting/reports/split3b_ch19_cs_polar_bottleneck.md`.  The active
Theorem 19.13 gates are now the full recursive/stored final-panel equality,
source `R11` nonbreakdown/conditioning estimates, and exact printed-constant
audits.

## Verification

Commands run in this audit context:

| Command | Result | Notes |
|---|---|---|
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Focused compile after adding the actual-active two-column recursive/stored endpoint and after applying the GPT Pro proof-script repair. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Target build after the actual-active two-column endpoint; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| stdin `#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` with `lean --stdin` | PASS | `H19.Theorem19_13.qrPanel_R_two_col_eq_secondStoredActiveStep_one_of_tail_reflector_self_dot_of_subtractZeroExact` reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over `Higham19.lean` | PASS, no matches | Placeholder/unsafe scan after the actual-active two-column endpoint. |
| bundled Git `diff --check` over `Higham19.lean` and the Split 3B audit report | PASS | Whitespace check after the actual-active endpoint and report refresh; Git repeated expected line-ending notices. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Baseline focused compile before editing, and focused compile after adding the successor-pivot self-dot beta/stored-step bridges. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Target build after the successor-pivot beta-one stored-step bridge; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| stdin `#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` with `lean --stdin` | PASS | The four new H19 bridge names resolve; printed axiom sets contain only `propext`, `Classical.choice`, and `Quot.sound`. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over `Higham19.lean` | PASS, no matches | Placeholder/unsafe scan after the successor-pivot beta-one stored-step bridge. |
| bundled Git `diff --check` over `Higham19.lean` | PASS | Whitespace check after the successor-pivot bridge; Git repeated expected line-ending notices for touched Lean/report files. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\HouseholderSpecSupport.lean` | PASS | Focused compile after adding `householderBetaSpec_eq_one_of_inner_self_eq_two`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.HouseholderSpecSupport` | PASS | Rebuilt the support module so Ch19 could import the new exact-beta bridge. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Focused compile after adding the H19 trailing-active beta wrapper and one-column stored/recursive self-dot consumers. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Target build after the self-dot terminal bridge; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| temporary `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | New support/H19 self-dot bridge names resolve; printed axiom sets contain only `propext`, `Classical.choice`, and `Quot.sound`. |
| placeholder/unsafe scan and bundled Git `diff --check` over `Higham19.lean` and `HouseholderSpecSupport.lean` | PASS | No placeholder tokens found; no whitespace errors. Git repeated expected line-ending notices for touched Lean files. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\HouseholderSpecSupport.lean` | PASS | Focused compile after adding exact beta nonnegativity and normalized-reflector equality for `householderBetaSpec`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.HouseholderSpecSupport` | PASS | Rebuilt the support module so Ch19 could import the new exact-beta bridge. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Focused compile after adding `H19.Theorem19_13.householderTrailingActiveVector_normalized_reflector_eq_betaSpec`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Target build after the exact beta-normalized reflector bridge; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | `householderBetaSpec_nonneg`, `householder_normalizedVector_eq_betaSpec`, and `H19.Theorem19_13.householderTrailingActiveVector_normalized_reflector_eq_betaSpec` resolve; the two printed axiom sets contain only `propext`, `Classical.choice`, and `Quot.sound`. |
| placeholder/unsafe scan, trailing-whitespace scan, and bundled Git `diff --check` over `Higham19.lean` and `HouseholderSpecSupport.lean` | PASS | No placeholder tokens, no trailing whitespace matches, and no whitespace errors; Git repeated the expected line-ending notices for touched Lean files. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Focused check after adding generic Gram symmetry/commutation lemmas and corrected-input projections. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt` | PASS | Built the raw dependency before checking the H19 Gram symmetry/commutation wrappers. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Focused check after exposing abstract and concrete Gram symmetry/commutation wrappers. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Built after the H19 Gram symmetry/commutation wrappers; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Aggregate import check after the corrected-input Gram commutation layer. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Raw and H19 Gram symmetry/commutation names resolve; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| placeholder/unsafe scan over touched QR/H19 Lean files | PASS, no matches | No `sorry`, `admit`, `axiom`, `unsafe`, or `opaque` matches after the Gram symmetry/commutation layer. |
| ASCII and trailing-whitespace scans over touched Lean/report files | PASS, no matches | No non-ASCII or trailing whitespace matches after the Gram symmetry/commutation report refresh. |
| bundled Git `diff --check` over touched Lean/report files | PASS | No whitespace errors after the Gram symmetry/commutation layer plus report refresh. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Focused check after adding corrected-input complementary Gram identities. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt` | PASS | Built the raw dependency before checking the H19 complement wrappers. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Focused check after exposing abstract and concrete complementary Gram wrappers. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Built after the H19 complement wrappers; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Aggregate import check after the corrected-input complementary Gram layer. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Raw and H19 complementary Gram names resolve; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| placeholder/unsafe scan over touched QR/H19 Lean files | PASS, no matches | No `sorry`, `admit`, `axiom`, `unsafe`, or `opaque` matches after the complementary Gram layer. |
| ASCII and trailing-whitespace scans over touched Lean/report files | PASS, no matches | No non-ASCII or trailing whitespace matches after the complement report refresh. |
| bundled Git `diff --check` over touched Lean/report files | PASS | No whitespace errors after the complementary Gram layer plus report refresh. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Focused check after adding the Gram-quadratic expansion, generic block-contraction lemmas, and corrected-input `P11`/`P21` contraction projections. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt` | PASS | Built the raw dependency before checking the H19 contraction wrappers. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Focused check after exposing corrected-input and concrete Householder-block contraction wrappers. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Built after the H19 contraction wrappers; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Aggregate import check after the corrected-input block-contraction layer. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Raw and H19 contraction theorem names resolve; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| placeholder/unsafe scan over touched QR/H19 Lean files | PASS, no matches | No `sorry`, `admit`, `axiom`, `unsafe`, or `opaque` matches after the corrected-input contraction layer. |
| ASCII and trailing-whitespace scans over touched Lean/report files | PASS, no matches | No non-ASCII or trailing whitespace matches after the contraction report refresh. |
| bundled Git `diff --check` over touched Lean/report files | PASS | No whitespace errors after the contraction layer plus report refresh. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Focused check after adding `MGSProblem1912CSPolarInput.of_paddedEconomy_blocks`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt` | PASS | Built the raw dependency before checking the H19 Householder-block input wrappers. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Focused check after exposing `problem1912_csPolarInput_of_paddedEconomy_blocks` and `householder_paddedFinInput_csPolarInput`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Built after the H19 Householder-block input wrappers; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Aggregate import check after the actual padded Householder CS/polar input bridge. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Raw and H19 Householder-block input names resolve; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| placeholder/unsafe scan over touched QR/H19 Lean files | PASS, no matches | No `sorry`, `admit`, `axiom`, `unsafe`, or `opaque` matches after the Householder-block CS/polar input bridge. |
| ASCII and trailing-whitespace scans over touched Lean/report files | PASS, no matches | No non-ASCII or trailing whitespace matches after the Householder-block input report refresh. |
| bundled Git `diff --check` over touched Lean/report files | PASS | No whitespace errors after the Householder-block input bridge plus report refresh. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Focused check after adding `MGSProblem1912CSPolarInput` and `MGSProblem1912CSPolarInput.of_csDiagonalFactorData`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt` | PASS | Built the raw dependency before checking the H19 corrected-input wrapper. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Focused check after exposing `H19.Theorem19_13.Problem1912CSPolarInput` and `problem1912_csPolarInput_of_csDiagonalFactorData`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Built after the H19 corrected-input wrapper; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Aggregate import check after the corrected CS/polar input surface. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Raw and H19 corrected-input names resolve; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| placeholder/unsafe scan over touched QR/H19 Lean files | PASS, no matches | No `sorry`, `admit`, `axiom`, `unsafe`, or `opaque` matches after the corrected CS/polar input surface. |
| ASCII and trailing-whitespace scans over touched Lean/report files | PASS, no matches | No non-ASCII or trailing whitespace matches after the corrected-input report refresh. |
| bundled Git `diff --check` over touched Lean/report files | PASS | No whitespace errors after the corrected-input report refresh. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Focused check after adding `mgsProblem1912_add_factor_gram_sum_not_dimension_free`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt` | PASS | Built the raw dependency before checking the H19 wrapper. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Focused check after exposing `H19.Theorem19_13.problem1912_add_factor_gram_sum_not_dimension_free`; an initial parallel check saw the old dependency before the raw rebuild. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Built after the H19 hidden-hypothesis sanity wrapper; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Aggregate import check after the dimension-free Gram-identity counterexample. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Raw and H19 hidden-hypothesis sanity names resolve; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| placeholder/unsafe scan over touched QR/H19 Lean files | PASS, no matches | No `sorry`, `admit`, `axiom`, `unsafe`, or `opaque` matches after the hidden-hypothesis sanity theorem. |
| ASCII and trailing-whitespace scans over touched Lean/report files | PASS, no matches | No non-ASCII or trailing whitespace matches after the hidden-hypothesis report refresh. |
| bundled Git `diff --check` over touched Lean/report files | PASS | No whitespace errors after the hidden-hypothesis report refresh. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Focused check after adding packaged factor-data additive Problem 19.12 witness projections. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt` | PASS | Built the raw dependency before checking the H19 wrappers. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Focused check after exposing packaged factor-data additive Problem 19.12 wrappers. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Built after exposing packaged factor-data additive wrappers; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Aggregate import check after the packaged factor-data additive witness bridge. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Raw and H19 packaged factor-data additive witness names resolve; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| placeholder/unsafe scan over touched QR/H19 Lean files | PASS, no matches | No `sorry`, `admit`, `axiom`, `unsafe`, or `opaque` matches after the packaged factor-data additive witness bridge. |
| ASCII and trailing-whitespace scans over touched Lean/report files | PASS, no matches | No non-ASCII or trailing whitespace matches after the packaged factor-data additive witness bridge and report refresh. |
| bundled Git `diff --check` over touched Lean/report files | PASS | No whitespace errors after the packaged factor-data additive witness bridge plus report refresh. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Focused check after adding the additive Problem 19.12 correction-map orientation bridge. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt` | PASS | Built the raw dependency before checking the H19 wrappers. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Focused check after exposing the additive Problem 19.12 correction-map orientation wrappers. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Built after exposing the additive Problem 19.12 wrappers; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Aggregate import check after the additive Problem 19.12 orientation bridge. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Raw and H19 additive correction-map names resolve; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| placeholder/unsafe scan over touched QR/H19 Lean files | PASS, no matches | No `sorry`, `admit`, `axiom`, `unsafe`, or `opaque` matches after the additive orientation bridge. |
| ASCII and trailing-whitespace scans over touched Lean/report files | PASS, no matches | No non-ASCII or trailing whitespace matches after the additive orientation bridge and report refresh. |
| bundled Git `diff --check` over touched Lean/report files | PASS | No whitespace errors after the additive orientation bridge plus report refresh. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Focused check after adding determinant-nonzero packaged CS factor-data and `Nonempty` factor-data fixed-budget wrappers. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Built after the determinant factor-data route; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Aggregate import check after the determinant factor-data route. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | The eight determinant factor-data source-output/`MGSQRBounds` wrappers resolve; sampled axiom prints report only `propext`, `Classical.choice`, and `Quot.sound`. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over touched QR/H19 Lean files | PASS, no matches | Placeholder/unsafe scan after the determinant factor-data route. |
| `rg --pcre2 -n "[^\x00-\x7F]"` over touched MGS/H19 Lean files and Split 3B reports | PASS, no matches | ASCII hygiene scan after the determinant factor-data route and report refresh. |
| `rg -n "[ \t]+$"` over touched Lean/report files | PASS, no matches | Trailing-whitespace scan after the determinant factor-data route and report refresh. |
| bundled Git `diff --check` over touched Lean/report files | PASS | Whitespace check after the determinant factor-data route plus report refresh. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Direct check after adding the pure-data fixed-budget source-output and `MGSQRBounds` wrappers, including their Frobenius-inverse fallback variants. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Built after adding the pure-data fixed-budget wrappers; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Aggregate import check after the pure-data fixed-budget wrappers and report refresh; rerun after an initial parallel race checked before the rebuilt `Higham19.olean` was available. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`, `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`, and `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff` resolve; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over touched QR/H19 Lean files | PASS, no matches | Placeholder/unsafe scan after the pure-data fixed-budget wrappers. |
| `rg --pcre2 -n "[^\x00-\x7F]"` over touched MGS/H19 Lean files and Split 3B reports | PASS, no matches | ASCII hygiene scan after the pure-data fixed-budget wrappers and report refresh. |
| `rg -n "[ \t]+$"` over touched Lean/report files | PASS, no matches | Trailing-whitespace scan after the pure-data fixed-budget wrappers and report refresh. |
| bundled Git `diff --check` over touched Lean/report files | PASS | Whitespace check after the pure-data fixed-budget wrappers and report refresh. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Direct check after adding the pure-data Frobenius-inverse source-output and `MGSQRBounds` fallbacks. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Built after adding the pure-data Frobenius-inverse fallback wrappers; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Aggregate import check after the pure-data Frobenius-inverse fallback and report refresh. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_budget_frobInv` and `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_correctionMapDataRepair_of_householder_stacked_budget_frobInv_of_small_unit_roundoff` resolve; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over touched QR/H19 Lean files | PASS, no matches | Placeholder/unsafe scan after the pure-data Frobenius-inverse fallback. |
| `rg --pcre2 -n "[^\x00-\x7F]"` over touched MGS/H19 Lean files and Split 3B reports | PASS, no matches | ASCII hygiene scan after the pure-data Frobenius-inverse fallback and report refresh. |
| `rg -n "[ \t]+$"` over touched Lean/report files | PASS, no matches | Trailing-whitespace scan after the pure-data Frobenius-inverse fallback and report refresh. |
| bundled Git `diff --check` over touched Lean/report files | PASS | Whitespace check after the pure-data Frobenius-inverse fallback plus report refresh. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Built after adding the data-first Problem 19.12 repair, source-output, stacked-budget, and `MGSQRBounds` wrappers; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Aggregate import check after the data-first repair/source-output bridge and report refresh. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | New raw and H19 data-repair/source-output names resolve; `#print axioms` for the perturbation-bounds repair, Householder-stacked source-output, and `MGSQRBounds` wrapper reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over touched QR/H19 Lean files | PASS, no matches | Placeholder/unsafe scan after the data-first repair/source-output bridge. |
| `rg --pcre2 -n "[^\x00-\x7F]"` over touched MGS/H19 Lean files and Split 3B reports | PASS, no matches | ASCII hygiene scan after the data-first repair/source-output bridge and report refresh. |
| `rg -n "[ \t]+$"` over touched Lean/report files | PASS, no matches | Trailing-whitespace scan after the data-first repair/source-output bridge and report refresh. |
| bundled Git `diff --check` over touched Lean/report files | PASS | Whitespace check after the data-first repair/source-output bridge plus report refresh. |
| bundled `pnpm.cmd dlx @steipete/oracle session split3b-cs-polar --render` | PASS | Reattached the CS/polar GPT-5.5 Pro session, saved the transcript under `C:\Users\User\.oracle\sessions\split3b-cs-polar\artifacts\transcript.md`, and used it only as advisory guidance for the pure correction-map data interface. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Focused check after adding `MGSProblem1912CorrectionMapData`, its data-to-map transport, and the CS algebra/orthogonal/diagonal constructors. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Focused check after exposing `H19.Theorem19_13.Problem1912CorrectionMapData` and the `problem1912_correctionMapData_*` wrappers. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Built both touched QR targets after the data-interface report refresh; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Aggregate import check after the pure correction-map data interface and report refresh. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | New raw and H19 correction-map data names resolve; `#print axioms` for the diagonal data constructor and data-to-map wrapper reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over touched QR/H19 Lean files | PASS, no matches | Placeholder/unsafe scan after the pure correction-map data interface. |
| `rg --pcre2 -n "[^\x00-\x7F]"` over touched MGS/H19 Lean files and Split 3B reports | PASS, no matches | ASCII hygiene scan after the pure correction-map data interface and report refresh. |
| `rg -n "[ \t]+$"` over touched Lean/report files | PASS, no matches | Trailing-whitespace scan after the pure correction-map data interface and report refresh. |
| bundled Git `diff --check` over touched Lean/report files | PASS | Whitespace check after the pure correction-map data interface plus report refresh. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Focused check after adding `matMul_finiteDiagonal_self`, `matMul_finiteDiagonal_csSquareSum`, and `mgsProblem1912_csDiagonal_square_sum`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt` | PASS | Built the updated Gram-Schmidt module so downstream H19 wrappers see the diagonal CS square identity. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Direct wrapper check after exposing `H19.Theorem19_13.problem1912_matMul_finiteDiagonal_csSquareSum` and `H19.Theorem19_13.problem1912_csDiagonal_square_sum`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing the Problem 19.12 diagonal CS square-identity wrappers; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Latest aggregate import check after the Problem 19.12 diagonal CS square identity wrappers and report refresh. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | `H19.Theorem19_13.problem1912_matMul_finiteDiagonal_csSquareSum` and `H19.Theorem19_13.problem1912_csDiagonal_square_sum` resolve; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over touched QR/H19 Lean files | PASS, no matches | Latest placeholder/unsafe scan after the Problem 19.12 diagonal CS square identity wrappers. |
| `rg --pcre2 -n "[^\x00-\x7F]"` over touched MGS/H19 Lean files and Split 3B reports | PASS, no matches | Latest ASCII hygiene scan after the Problem 19.12 diagonal CS square identity wrappers and report refresh. |
| `rg -n "[ \t]+$"` over touched Lean/report files | PASS, no matches | Latest trailing-whitespace scan over touched files after the Problem 19.12 diagonal CS square identity wrappers and report refresh. |
| bundled Git `diff --check` over touched Lean/report files | PASS | Latest whitespace check after the Problem 19.12 diagonal CS square identity wrappers plus report refresh. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Focused check after adding `csCosine_abs_le_one`, `opNorm2Le_finiteDiagonal_csCosine`, and `mgsProblem1912_p11_opNorm2Le_one_of_csDiagonalAlgebra`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt` | PASS | Built the updated Gram-Schmidt module so downstream H19 wrappers see the CS cosine and `P11` contraction lemmas. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Direct wrapper check after exposing `H19.Theorem19_13.problem1912_opNorm2Le_finiteDiagonal_csCosine` and `H19.Theorem19_13.problem1912_p11_opNorm2Le_one_of_csDiagonalAlgebra`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing the Problem 19.12 CS cosine and `P11` contraction wrappers; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Latest aggregate import check after the Problem 19.12 top-block CS contraction wrappers and report refresh. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | `H19.Theorem19_13.problem1912_opNorm2Le_finiteDiagonal_csCosine` and `H19.Theorem19_13.problem1912_p11_opNorm2Le_one_of_csDiagonalAlgebra` resolve; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over touched QR/H19 Lean files | PASS, no matches | Latest placeholder/unsafe scan after the Problem 19.12 top-block CS contraction wrappers. |
| `rg --pcre2 -n "[^\x00-\x7F]"` over touched MGS/H19 Lean files and Split 3B reports | PASS, no matches | Latest ASCII hygiene scan after the Problem 19.12 top-block CS contraction wrappers and report refresh. |
| `rg -n "[ \t]+$"` over touched Lean/report files | PASS, no matches | Latest trailing-whitespace scan over touched files. |
| stale wording scan for superseded Problem 19.12 budget/contraction descriptions | PASS, no matches | Confirms the A.19.12 row no longer says repaired-perturbation budgets remain open and the CS contraction wording is not bottom-only. |
| bundled Git `diff --check` over touched Lean/report files | PASS | Latest whitespace check after the Problem 19.12 top-block CS contraction wrappers plus report refresh. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Focused check after adding `csSine_abs_le_one`, `opNorm2Le_finiteDiagonal_csSine`, and `mgsProblem1912_p21_rectOpNorm2Le_one_of_csDiagonalAlgebra`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt` | PASS | Built the updated Gram-Schmidt module so downstream H19 wrappers see the CS sine and `P21` contraction lemmas. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Direct wrapper check after exposing `H19.Theorem19_13.problem1912_opNorm2Le_finiteDiagonal_csSine` and `H19.Theorem19_13.problem1912_p21_rectOpNorm2Le_one_of_csDiagonalAlgebra`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing the Problem 19.12 CS sine and `P21` contraction wrappers; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Latest aggregate import check after the Problem 19.12 CS contraction wrappers and report refresh. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | `H19.Theorem19_13.problem1912_opNorm2Le_finiteDiagonal_csSine` and `H19.Theorem19_13.problem1912_p21_rectOpNorm2Le_one_of_csDiagonalAlgebra` resolve; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over touched QR/H19 Lean files | PASS, no matches | Latest placeholder/unsafe scan after the Problem 19.12 CS contraction wrappers. |
| `rg --pcre2 -n "[^\x00-\x7F]"` over touched MGS/H19 Lean files and Split 3B reports | PASS, no matches | Latest ASCII hygiene scan after the Problem 19.12 CS contraction wrappers and report refresh. |
| `rg -n "[ \t]+$"` over touched Lean/report files | PASS, no matches | Latest trailing-whitespace scan over touched files. |
| bundled Git `diff --check` over touched Lean/report files | PASS | Latest whitespace check after the Problem 19.12 CS contraction wrappers plus report refresh. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Direct wrapper check after adding `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff` and `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after adding the fixed-`c3=4*k` Frobenius-inverse fallback wrappers; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Latest aggregator import check after the fixed-`c3=4*k` Frobenius-inverse fallback wrappers and report refresh. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff` and `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_coefficient_budget_frobInv_of_small_unit_roundoff` resolve; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Direct wrapper check after adding `H19.Theorem19_13.gamma_tilde_two_le_four_index_mul_unit_roundoff_of_small`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`, and `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after adding the fixed-`c3=4*k` Householder-stacked coefficient-budget route; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Latest aggregator import check after the fixed-`c3=4*k` Householder-stacked coefficient-budget wrappers and report refresh. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | `H19.Theorem19_13.gamma_tilde_two_le_four_index_mul_unit_roundoff_of_small`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff`, and `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_coefficient_budget_of_small_unit_roundoff` resolve; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Direct wrapper check after adding `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_budget` and `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_budget_of_small_unit_roundoff`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after adding the double-residual Householder-stacked route; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Latest aggregator import check after the double-residual Householder-stacked wrappers and report refresh. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_budget` and `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_double_residual_budget_of_small_unit_roundoff` resolve; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Direct wrapper check after adding `H19.Theorem19_13.gamma_tilde_two_column_budget`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_same_residual_budget`, and `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_same_residual_budget_of_small_unit_roundoff`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after adding the same-residual Householder-stacked route; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Latest aggregator import check after the same-residual Householder-stacked wrappers and report refresh. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | `H19.Theorem19_13.gamma_tilde_two_column_budget`, `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_same_residual_budget`, and `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_householder_stacked_same_residual_budget_of_small_unit_roundoff` resolve; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over touched QR/H19 Lean files | PASS, no matches | Latest placeholder/unsafe scan after the same-residual Householder-stacked wrappers. |
| `rg --pcre2 -n "[^\x00-\x7F]"` over touched MGS/H19 Lean files and Split 3B reports | PASS, no matches | Latest ASCII hygiene scan after the same-residual Householder-stacked wrappers and report refresh. |
| `rg -n "[ \t]+$"` over touched Lean/report files | PASS, no matches | Latest trailing-whitespace scan over touched files. |
| bundled Git `diff --check` | PASS | No whitespace errors; Git repeated pre-existing line-ending warnings for tracked files outside this Ch19 edit path. |
| `rg --files -g AGENTS.md` | PASS, no output | No repository `AGENTS.md` instructions found. |
| `lake env lean tmp\split3b_qr_contract_probe.lean` | EXPECTED FAIL, historical | Pre-wrapper probe showed the three outward QR names were absent. Superseded for Theorems 19.4 and 19.10 by the passing H19 probe rows below; the final MGS theorem name remains absent, though the `MGSQRBounds` contract shape now exists. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\HouseholderQR.lean` | PASS | Focused Householder QR foundation check. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GivensMatrixStep` | PASS | Rebuilt after adding `PairBlockSupported`, `SparseGivensAppError`, sparse rectangular columnwise residuals, exact Givens panel zero lemmas, and row-supported residual extraction. Pre-existing unused-`simp` warnings remain in `GivensSpec.lean`. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GivensQR.lean` | PASS | Rechecked after adding zero-aware task columnwise residuals and the accumulation layer: `fl_givensQRTaskStep_columnFrob_residual_of_prev_pair_zero`, `fl_givensQRTaskStepOfTask_columnFrob_residual_of_zeroedThrough`, `fl_givensQRTaskStepOfTask_columnFrob_uniform_of_zeroedThrough`, `orthogonal_sequence_one_step_of_columnFrob_residual_rect`, `residual_orthogonal_sequence_columnFrob_backward_error_rect`, `fl_givensQRTask_sequence_columnFrob_backward_error_uniform`, `residualAccumBound_le_of_le_nat`, `givensQRStageTasks_length_le_stageTaskList_length`, `fl_givensQRStageTasks_prefix_task_columnFrob_uniform`, `fl_givensQRStageTasks_sequence_backward_error_uniform`, `fl_givensQRStageTasks_sequence_columnFrob_backward_error_uniform`, `fl_givensQRStageFold_sequence_backward_error_uniform`, and `fl_givensQRStageFold_sequence_columnFrob_backward_error_uniform`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GivensQR` | PASS | Built the updated Givens QR module into Lake artifacts after the one-stage and full stage-fold columnwise accumulators; same pre-existing unused-`simp` warnings replayed from `GivensSpec.lean`. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\QRSolve.lean` | PASS | Focused QR solve foundation check. |
| `pdftoppm` render of Ch.19 PDF page containing Theorem 19.4 | PASS | Source page visually inspected; Poppler emitted font-substitution warnings but rendered the theorem legibly. |
| `pdftoppm` render of Ch.19 PDF page containing Theorem 19.10 | PASS | Source page visually inspected; Poppler emitted font-substitution warnings but rendered the theorem legibly. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Direct compile of the H19 source-facing wrapper module after adding Theorems 19.4 and 19.10. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | H19 wrapper module built into Lake artifacts after adding the Givens QR wrapper. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Aggregator import check after adding `Higham19`, H19.10, and the Gram-Schmidt/MGS source-facing surfaces. |
| `lake env lean LeanFpAnalysis.lean` | PASS | Top-level import check after H19/Givens/Gram-Schmidt edits. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over touched QR/H19 files | PASS, no matches | Placeholder/unsafe scan after the latest H19 MGS bridge addition. |
| bundled Git `diff --check` over touched Lean/report files | PASS | No whitespace errors reported. |
| `lake env lean tmp\split3b_h19_theorem19_4_probe.lean` | PASS | `#check` resolved `H19.Theorem19_4.householder_qr_backward_error`; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean tmp\split3b_h19_theorem19_10_probe.lean` | PASS | `#check` resolved `H19.Theorem19_10.givens_qr_backward_error`; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Direct compile of the new CGS/MGS exact algorithm and Theorem 19.13 contract-shape foundation. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt` | PASS | Built the new Gram-Schmidt QR module into Lake artifacts. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after adding `H19.Algorithm19_11`, `H19.Algorithm19_12`, source-stage/`R_k` aliases, MGS recurrence wrappers, and `H19.Theorem19_13.MGSQRBounds`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_probe.lean` | PASS | `#check` resolved `H19.Algorithm19_11.State`, `H19.Algorithm19_12.exact_state`, `H19.Algorithm19_12.computedR_upper_trapezoidal`, and `H19.Theorem19_13.MGSQRBounds`; `#print axioms` for the two MGS wrapper theorems reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean tmp\split3b_h19_mgs_stage_probe.lean` | PASS | `#check` resolved `H19.Algorithm19_12.sourceStage`, `H19.Algorithm19_12.stepR`, and `H19.Algorithm19_12.stepR_upper_trapezoidal`; `#print axioms` for the step-R wrapper theorem reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean tmp\split3b_h19_mgs_recombine_probe.lean` | PASS | `#check` resolved `H19.Algorithm19_12.stageVectors_succ_later`, `sourceStage_current_recombine`, and `sourceStage_later_recombine`; `#print axioms` for all three reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean tmp\split3b_h19_mgs_matrix_recurrence_probe.lean` | PASS | `#check` resolved `H19.Algorithm19_12.sourceStage_matrix_recurrence`; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after adding `H19.Algorithm19_12.stepRProduct`, `sourceStage_initial_matrix_recurrence`, and `exact_product_factorization`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_product_probe.lean` | PASS | `#check` resolved `H19.Algorithm19_12.stepRProduct`, `sourceStage_initial_matrix_recurrence`, and `exact_product_factorization`; `#print axioms` for the two product theorems reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Aggregator import check after adding the MGS one-step product and exact product factorization wrappers. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after proving `modifiedGramSchmidtStepRProduct_eq_R`, `modifiedGramSchmidt_exact_factorization`, and their H19 wrappers; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_exact_factorization_probe.lean` | PASS | `#check` resolved `H19.Algorithm19_12.stepRProduct_eq_computedR` and `exact_factorization`; `#print axioms` for both reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Aggregator import check after adding the exact `computedR` and `A = Q R` wrappers. |
| `pdftoppm` render of Ch.19 PDF pages 18-21 | PASS | Rendered and visually inspected the Algorithm 19.12, `(19.27)`-`(19.28)`, Theorem 19.13, `(19.32)`-`(19.34)`, and proof-continuation pages. Poppler emitted font-substitution warnings but the formulas were legible. Temporary PNGs deleted. |
| `lake env lean tmp\split3b_h19_mgs_bridge_axioms_probe.lean` | PASS | `#check` resolved `H19.Theorem19_13.paddedInput`, `householderVector`, `householderReflector`, and `householderVector_self_dot`; `#print axioms` for `householderVector_self_dot` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding `mgsPaddedInput`, `mgsHouseholderVector`, `mgsHouseholderReflector`, `mgsHouseholderVector_norm_sq`, and `mgsHouseholderVector_self_dot`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing the padded-input/vector/reflector bridge through `H19.Theorem19_13.*`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding `mgsHouseholderApply`, `mgsHouseholderColumnInner_padded`, and the one-reflector padded-action lemmas. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing the one-reflector padded-action lemmas through `H19.Theorem19_13.*`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_action_axioms_probe.lean` | PASS | `#check` resolved `H19.Theorem19_13.householderColumnInner_padded`, `householderApply_padded_top_current`, `householderApply_padded_top_ne`, and `householderApply_padded_bottom`; `#print axioms` for `householderApply_padded_bottom` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding `mgsHouseholderReflector_symmetric` and `mgsHouseholderReflector_mul_self_of_self_dot`; no new warnings. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing `H19.Theorem19_13.householderReflector_symmetric` and `H19.Theorem19_13.householderReflector_mul_self_of_self_dot`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_reflector_axioms_probe.lean` | PASS | `#check` resolved `H19.Theorem19_13.householderReflector_symmetric` and `householderReflector_mul_self_of_self_dot`; `#print axioms` for `householderReflector_mul_self_of_self_dot` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding `mgsPaddedStage`, `mgsPaddedRBlock`, component lemmas, and exact `mgsPaddedStage_zero` / `mgsPaddedStage_final` endpoints. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing `H19.Theorem19_13.paddedStage`, `paddedRBlock`, component lemmas, and `paddedStage_zero` / `paddedStage_final`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_padded_stage_axioms_probe.lean` | PASS | `#check` resolved `H19.Theorem19_13.paddedStage`, `paddedRBlock`, `paddedStage_zero`, and `paddedStage_final`; `#print axioms` for `paddedStage_final` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding `gsDot_normalize_self`; no new warnings. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing `H19.Algorithm19_12.computedQ_stage_self_dot`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_stage_self_dot_axioms_probe.lean` | PASS | `#check` resolved `H19.Algorithm19_12.computedQ_stage_self_dot`; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean tmp\split3b_h19_mgs_step_probe.lean` | PASS | Temporary proof probe checked `mgsHouseholderColumnInner_paddedStage` and `mgsHouseholderApply_paddedStage_eq_succ`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding `mgsHouseholderColumnInner_paddedStage` and `mgsHouseholderApply_paddedStage_eq_succ`; no new warnings. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing `H19.Theorem19_13.householderColumnInner_paddedStage` and `H19.Theorem19_13.householderApply_paddedStage_eq_succ`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_step_axioms_probe.lean` | PASS | `#check` resolved `H19.Theorem19_13.householderColumnInner_paddedStage` and `H19.Theorem19_13.householderApply_paddedStage_eq_succ`; `#print axioms` for the one-step transition reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean tmp\split3b_h19_mgs_iter_probe.lean` | PASS | Temporary proof probe checked `mgsHouseholderApplyPrefix_paddedInput` and `mgsHouseholderApplyPrefix_paddedInput_final`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding `mgsHouseholderApplyPrefix`, `mgsHouseholderApplyPrefix_paddedInput`, and `mgsHouseholderApplyPrefix_paddedInput_final`; no new warnings. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing `H19.Theorem19_13.householderApplyPrefix`, `householderApplyPrefix_paddedInput`, and `householderApplyPrefix_paddedInput_final`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_iter_axioms_probe.lean` | PASS | `#check` resolved `H19.Theorem19_13.householderApplyPrefix`, `householderApplyPrefix_paddedInput`, and `householderApplyPrefix_paddedInput_final`; `#print axioms` for the final prefix endpoint reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean tmp\split3b_h19_mgs_q_unit_probe.lean` | PASS | Temporary proof probe checked the ASCII-only `gsNormalize_norm_sq` unit-normalization proof. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding `gsNormalize_norm_sq`, `modifiedGramSchmidtQ_column_norm_sq`, and `mgsHouseholderVector_self_dot_computedQ`; no new warnings. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing `H19.Algorithm19_12.computedQ_column_norm_sq` and `H19.Theorem19_13.householderVector_self_dot_computedQ`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_q_unit_axioms_probe.lean` | PASS | `#check` resolved `H19.Algorithm19_12.computedQ_column_norm_sq` and `H19.Theorem19_13.householderVector_self_dot_computedQ`; `#print axioms` for the computed-vector self-dot theorem reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean tmp\split3b_h19_mgs_reverse_probe.lean` | PASS | Temporary proof probe checked `mgsHouseholderApply_apply_self_of_self_dot` and `mgsHouseholderApply_paddedStage_succ_eq_current`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding `mgsHouseholderApply_apply_self_of_self_dot` and `mgsHouseholderApply_paddedStage_succ_eq_current`; no new warnings. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing `H19.Theorem19_13.householderApply_apply_self_of_self_dot` and `H19.Theorem19_13.householderApply_paddedStage_succ_eq_current`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_reverse_axioms_probe.lean` | PASS | `#check` resolved `H19.Theorem19_13.householderApply_apply_self_of_self_dot` and `H19.Theorem19_13.householderApply_paddedStage_succ_eq_current`; `#print axioms` for the reverse stage transition reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean tmp\split3b_h19_mgs_reverse_iter_probe.lean` | PASS | Temporary proof probe checked `mgsHouseholderApplyReversePrefix_paddedStage` and `mgsHouseholderApplyReversePrefix_paddedRBlock`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding `mgsHouseholderApplyReversePrefix`, `mgsHouseholderApplyReversePrefix_paddedStage`, and `mgsHouseholderApplyReversePrefix_paddedRBlock`; no new warnings. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing `H19.Theorem19_13.householderApplyReversePrefix`, `householderApplyReversePrefix_paddedStage`, and `householderApplyReversePrefix_paddedRBlock`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_reverse_iter_axioms_probe.lean` | PASS | `#check` resolved `H19.Theorem19_13.householderApplyReversePrefix`, `householderApplyReversePrefix_paddedStage`, and `householderApplyReversePrefix_paddedRBlock`; `#print axioms` for the reverse-prefix endpoint reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding `mgsPaddedTopBlock`, `mgsPaddedBottomBlock`, and the reverse-prefix top/bottom block endpoint lemmas; no new warnings. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing `H19.Theorem19_13.paddedTopBlock`, `paddedBottomBlock`, and `householderApplyReversePrefix_paddedRBlock_blocks`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_blocks_probe.lean` | PASS | `#check` resolved the raw `LeanFpAnalysis.FP.*` block projections and the `H19.Theorem19_13.*` top/bottom block endpoint wrappers. Temporary probe deleted. |
| `lake env lean tmp\split3b_h19_mgs_blocks_axioms_probe.lean` | PASS | `#print axioms` for `H19.Theorem19_13.householderApplyReversePrefix_paddedRBlock_blocks` and the raw Gram-Schmidt block theorem reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding `mgsPaddedPerturbedInput`, `mgsStackedPerturbationColumnwiseBound`, and the zero-perturbation `(19.34)` endpoint. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing `H19.Theorem19_13.paddedPerturbedInput`, `stackedPerturbationColumnwiseBound`, and `householderApplyReversePrefix_paddedRBlock_perturbedInput_zero`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_perturb_probe.lean` | PASS | `#check` resolved the raw Gram-Schmidt perturbation vocabulary and the `H19.Theorem19_13.*` perturbation wrappers. Temporary probe deleted. |
| `lake env lean tmp\split3b_h19_mgs_perturb_axioms_probe.lean` | PASS | `#print axioms` for `H19.Theorem19_13.householderApplyReversePrefix_paddedRBlock_perturbedInput_zero` and `stackedPerturbationColumnwiseBound_zero` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding `mgsPaddedTopPerturbation`, `mgsPaddedBottomPerturbation`, and `mgsPaddedPerturbedInput_eta`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing `H19.Theorem19_13.paddedTopPerturbation`, `paddedBottomPerturbation`, and `paddedPerturbedInput_eta`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_eta_probe.lean` | PASS | `#check` resolved the raw Gram-Schmidt extraction/eta vocabulary and the `H19.Theorem19_13.*` wrappers. Temporary probe deleted. |
| `lake env lean tmp\split3b_h19_mgs_eta_axioms_probe.lean` | PASS | `#print axioms` for `H19.Theorem19_13.paddedPerturbedInput_eta` and `paddedBottomPerturbation_perturbedInput` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding `mgsPaddedRowToFin`, `mgsPaddedRowFromFin`, `mgsPaddedRowsToFin`, `mgsPaddedRowsFromFin`, `mgsPaddedFinInput`, and the round-trip lemmas. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing `H19.Theorem19_13.paddedRowsToFin`, `paddedRowsFromFin`, `paddedFinInput`, and the round-trip lemmas; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_reindex_probe.lean` | PASS | `#check` resolved the raw Gram-Schmidt row-reindex vocabulary and the `H19.Theorem19_13.*` wrappers. Temporary probe deleted. |
| `lake env lean tmp\split3b_h19_mgs_reindex_axioms_probe.lean` | PASS | `#print axioms` for `H19.Theorem19_13.paddedRowsFromFin_toFin`, `paddedRowsToFin_fromFin`, and `paddedRowsFromFin_finInput` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding the column-norm transport lemmas and `mgsStackedPerturbationColumnwiseBound_of_rowsFromFin_add_padded_bound`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing the `H19.Theorem19_13` column-norm and stacked-bound transport wrappers; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_norm_bridge_probe.lean` | PASS | `#check` resolved the raw Gram-Schmidt norm/bound bridge and the `H19.Theorem19_13.*` wrappers. Temporary probe deleted. |
| `lake env lean tmp\split3b_h19_mgs_norm_bridge_axioms_probe.lean` | PASS | `#print axioms` for `H19.Theorem19_13.paddedColumnNorm_rowsFromFin`, `columnFrob_paddedFinInput`, and `stackedPerturbationColumnwiseBound_of_rowsFromFin_add_padded_bound` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after adding `H19.Theorem19_13.householder_paddedFinInput_stackedPerturbation`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_hh_bridge_probe.lean` | PASS | `#check` resolved `H19.Theorem19_13.householder_paddedFinInput_stackedPerturbation` and an example using its returned existential shape. Temporary probe deleted. |
| `lake env lean tmp\split3b_h19_mgs_hh_bridge_axioms_probe.lean` | PASS | `#print axioms` for `H19.Theorem19_13.householder_paddedFinInput_stackedPerturbation` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after adding `H19.Theorem19_13.householder_paddedFinInput_perturbedInput_blocks`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_block_form_probe.lean` | PASS | `#check` resolved `H19.Theorem19_13.paddedBottomBlock_rowsFromFin_of_upper` and `H19.Theorem19_13.householder_paddedFinInput_perturbedInput_blocks`. Temporary probe deleted. |
| `lake env lean tmp\split3b_h19_mgs_block_form_axioms_probe.lean` | PASS | `#print axioms` for the block-form handoff theorems reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| Direct Poppler render of `References/1.9780898718027.ch19.pdf` pages 21-22 | PASS | Formulas `(19.35a)`, `(19.35b)`, `(19.36)`, and `(19.37)` were visually inspected; Poppler emitted font-substitution warnings but the rendered pages were legible. Temporary PNGs deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding `mgsPaddedEconomyQ`, `mgsPaddedEconomyR`, `mgsPaddedBottomBlock_rowsFromFin_matMul_of_bottom_zero`, and `mgsPaddedPerturbedInput_bottom_eq_economyProduct`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing the economy-product wrappers and `H19.Theorem19_13.householder_paddedFinInput_economyProduct`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_economy_product_probe.lean` | PASS | `#check` resolved the raw Gram-Schmidt economy-product bridge, the `H19.Theorem19_13.*` wrappers, and `H19.Theorem19_13.householder_paddedFinInput_economyProduct`. Temporary probe deleted. |
| `lake env lean tmp\split3b_h19_mgs_economy_product_axioms_probe.lean` | PASS | `#print axioms` for `H19.Theorem19_13.paddedPerturbedInput_bottom_eq_economyProduct` and `H19.Theorem19_13.householder_paddedFinInput_economyProduct` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding `mgsPaddedEconomyR_upper_trapezoidal`, `ModifiedGramSchmidtQRSensitivityBridge`, and `ModifiedGramSchmidtBackwardError.of_economy_product_sensitivity`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing `H19.Theorem19_13.QRSensitivityBridge`, `paddedEconomyR_upper_trapezoidal`, `householder_paddedFinInput_economyProduct_with_upper`, and `mgs_qr_bounds_of_householder_economy_product_sensitivity`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_sensitivity_bridge_probe.lean` | PASS | `#check` resolved the raw sensitivity bridge, the `H19.Theorem19_13.*` wrappers, and the Householder economy-product assembly theorem. Temporary probe deleted. |
| `lake env lean tmp\split3b_h19_mgs_sensitivity_bridge_axioms_probe.lean` | PASS | `#print axioms` for the economy `R` upper-shape lemma, sensitivity assembly lemma, and Householder economy-product assembly theorem reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding bottom-perturbation residual conversion lemmas from stacked column bounds to Frobenius/operator residual bounds. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing bottom-perturbation wrappers and `H19.Theorem19_13.mgs_qr_bounds_of_householder_economy_product_sensitivity_of_residual_budget`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_residual_budget_probe.lean` | PASS | `#check` resolved the bottom-perturbation residual conversion lemmas and the residual-budget Householder assembly theorem. Temporary probe deleted. |
| `lake env lean tmp\split3b_h19_mgs_residual_budget_axioms_probe.lean` | PASS | `#print axioms` for the residual-budget bridge reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after adding `H19.Theorem19_4.gamma_tilde_nonneg` and `H19.Theorem19_13.mgs_qr_bounds_of_householder_economy_product_sensitivity_of_valid_residual_budget`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_valid_residual_budget_probe.lean` | PASS | `#check` resolved the gamma nonnegativity wrapper and valid-residual-budget assembly theorem; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after adding `H19.Theorem19_13.residualBudget_of_gamma_tilde_le_mul_norm_bound` and `H19.Theorem19_13.mgs_qr_bounds_of_householder_economy_product_sensitivity_of_coefficient_norm_budget`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_coefficient_norm_budget_probe.lean` | PASS | `#check` resolved the coefficient/norm residual budget and assembly theorem; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after adding `H19.Theorem19_13.residualBudget_of_gamma_tilde_le_mul_self` and `H19.Theorem19_13.mgs_qr_bounds_of_householder_economy_product_sensitivity_of_coefficient_budget`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_coefficient_budget_probe.lean` | PASS | `#check` resolved the exact-norm coefficient-budget residual theorem and assembly theorem; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `pdftoppm -f 21 -l 22` on `References\1.9780898718027.ch19.pdf` | PASS | Rendered and visually inspected Ch19 QR-sensitivity pages 373-374 to confirm `(19.35a)`, `(19.35b)`, `(19.36)`, and `(19.37)` before adding the source-output bridge. Temporary rendered pages deleted. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after adding `ModifiedGramSchmidtQRSensitivitySourceOutput`, `H19.Theorem19_13.QRSensitivitySourceOutput`, `H19.Theorem19_13.qrsensitivityBridge_of_source_output`, and `H19.Theorem19_13.mgs_qr_bounds_of_householder_economy_product_source_sensitivity_of_coefficient_budget`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_source_sensitivity_probe.lean` | PASS | `#check` resolved the source-output bridge and source-sensitivity coefficient-budget assembly theorem; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after adding `H19.Theorem19_4.gamma_tilde_le_two_index_mul_unit_roundoff_of_small` and `H19.Theorem19_13.mgs_qr_bounds_of_householder_economy_product_source_sensitivity_of_small_unit_roundoff`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_small_unit_roundoff_probe.lean` | PASS | `#check` resolved the smallness-based `gamma_tilde` cap and exact-unit-roundoff source-sensitivity assembly theorem; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `pnpm dlx @steipete/oracle --dry-run summary --files-report ... split3b_oracle_qr_sensitivity_prompt.md ...` | PASS | Dry-run confirmed six attachments: the prompt, Ch19 inventory, complete audit, `GramSchmidt.lean`, `Higham19.lean`, and `Rounding.lean`. |
| `pnpm dlx @steipete/oracle --engine browser --model gpt-5.5-pro --slug split3b-qr-sensitivity ...` | PASS | Browser run completed as session `split3b-qr-sensitivit`; model evidence reported `requested=Pro`, `resolved=Pro Extended`, `status=switched`, `verified=yes`. Advisory output redirected Theorem 19.13 from a narrow `(19.35a)`-`(19.37)` route to the full `(19.34)` block-data plus CS/polar repair route. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding `mgsPaddedEconomyP11`, `mgsPaddedTopBlock_rowsFromFin_matMul_of_bottom_zero`, and `mgsPaddedPerturbedInput_top_eq_economyProduct`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing `H19.Theorem19_13.paddedEconomyP11`, `H19.Theorem19_13.paddedPerturbedInput_top_eq_economyProduct`, and `H19.Theorem19_13.householder_paddedFinInput_full_block_data`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_full_block_data_probe.lean` | PASS | `#check` resolved the raw and `H19.Theorem19_13` full-block-data names; `#print axioms` for `H19.Theorem19_13.householder_paddedFinInput_full_block_data` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding `matMulRect_sub_left_square_right`, `commonR_difference_product_eq_perturbation_difference`, and `commonR_difference_eq_perturbation_difference_mul_right_inverse`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing `H19.Theorem19_13.commonR_difference_product_eq_perturbation_difference` and `H19.Theorem19_13.commonR_difference_eq_perturbation_difference_mul_right_inverse`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_common_r_probe.lean` | PASS | `#check` resolved the raw and `H19.Theorem19_13` common-`R` algebra names; `#print axioms` for the right-inverse form reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding `rectOpNorm2Le_sub`, `commonR_difference_rectOpNorm2Le_of_perturbation_difference_mul_right_inverse`, and `commonR_difference_rectOpNorm2Le_of_perturbation_bounds_mul_right_inverse`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing `H19.Theorem19_13.commonR_difference_rectOpNorm2Le_of_perturbation_difference_mul_right_inverse` and `H19.Theorem19_13.commonR_difference_rectOpNorm2Le_of_perturbation_bounds_mul_right_inverse`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_common_r_norm_probe.lean` | PASS | `#check` resolved the raw and `H19.Theorem19_13` common-`R` norm bridge names; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding `gramSchmidtOrthogonalityResidual_eq_close_expansion`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing `H19.Theorem19_13.gramSchmidtOrthogonalityResidual_eq_close_expansion`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_gram_residual_probe.lean` | PASS | `#check` resolved the raw and `H19.Theorem19_13` Gram-residual expansion names; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding `rectOpNorm2Le_add`, `opNorm2Le_of_rectOpNorm2Le_square`, `GramSchmidtOrthonormalColumns.rectOpNorm2Le_one`, and `gramSchmidtOrthogonalityResidual_opNorm2Le_of_close_orthonormal`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing `H19.Theorem19_13.orthonormalColumns_rectOpNorm2Le_one` and `H19.Theorem19_13.gramSchmidtOrthogonalityResidual_opNorm2Le_of_close_orthonormal`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_gram_norm_probe.lean` | PASS | `#check` resolved the raw and `H19.Theorem19_13` Gram-residual norm-conversion names; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing `H19.Theorem19_13.qrsensitivitySourceOutput_of_commonR_bounds`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_source_output_common_r_probe.lean` | PASS | `#check` resolved `opNorm2Le_mono`, `ModifiedGramSchmidtQRSensitivitySourceOutput.of_commonR_bounds`, and `H19.Theorem19_13.qrsensitivitySourceOutput_of_commonR_bounds`; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding the padded `P11`/`Q21` block-column Gram identities and economy-block residual identity. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing `H19.Theorem19_13.paddedEconomy_blocks_gram_sum_eq_id`, `H19.Theorem19_13.paddedEconomyQ_gram_eq_id_sub_P11_gram`, and `H19.Theorem19_13.paddedEconomyQ_orthogonalityResidual_eq_neg_P11_gram`; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_block_orthogonality_probe.lean` | PASS | `#check` resolved the raw and `H19.Theorem19_13` block-orthogonality names; `#print axioms` for the economy-block residual identity reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding `rectOpNorm2Le_neg`, `opNorm2Le_neg`, `rectangularGram_opNorm2Le_of_rectOpNorm2Le`, and `mgsPaddedEconomyQ_orthogonalityResidual_opNorm2Le_of_P11_rectOpNorm2Le`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt` | PASS | Built the updated Gram-Schmidt module so downstream imports see the new norm bridge. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Direct wrapper check after exposing `H19.Theorem19_13.paddedEconomyQ_orthogonalityResidual_opNorm2Le_of_P11_rectOpNorm2Le`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing the pre-repair economy-block norm bridge; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_block_orthogonality_norm_probe.lean` | PASS | `#check` resolved `opNorm2Le_neg`, `rectangularGram_opNorm2Le_of_rectOpNorm2Le`, the raw pre-repair norm theorem, and the `H19.Theorem19_13` wrapper; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding `right_factor_eq_product_mul_right_inverse`, `right_factor_rectOpNorm2Le_of_product_mul_right_inverse`, and the top-block/right-inverse `P11` and economy Gram-residual norm bridges. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt` | PASS | Built the updated Gram-Schmidt module so downstream imports see the top-block/right-inverse bridge. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Direct wrapper check after exposing `H19.Theorem19_13.paddedEconomyP11_rectOpNorm2Le_of_top_product_right_inverse` and `H19.Theorem19_13.paddedEconomyQ_orthogonalityResidual_opNorm2Le_of_top_product_right_inverse`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing the top-block/right-inverse norm bridge; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_top_block_right_inverse_probe.lean` | PASS | `#check` resolved the raw and `H19.Theorem19_13` top-block/right-inverse norm bridge names; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding `finiteVecNorm2_le_sumBothVec_left`, `mgsTopPerturbationColumnNorm_le_stacked`, `mgsTopPerturbation_frobNormRect_le_of_stackedColumnwiseBound`, and `mgsTopPerturbation_rectOpNorm2Le_of_stackedColumnwiseBound`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt` | PASS | Built the updated Gram-Schmidt module so downstream imports see the top-perturbation norm transport. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Direct wrapper check after exposing `H19.Theorem19_13.topPerturbationColumnNorm_le_stacked`, `H19.Theorem19_13.topPerturbation_frobNormRect_le_of_stackedColumnwiseBound`, and `H19.Theorem19_13.topPerturbation_rectOpNorm2Le_of_stackedColumnwiseBound`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing the top-perturbation norm transport; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_top_perturbation_norm_probe.lean` | PASS | `#check` resolved the raw and `H19.Theorem19_13` top-perturbation norm transport names; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding `mgsPaddedEconomyQ_orthogonalityResidual_opNorm2Le_of_stacked_bound_top_product_right_inverse`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt` | PASS | Built the updated Gram-Schmidt module so downstream imports see the stacked-bound top-right-inverse Gram bridge. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Direct wrapper check after exposing `H19.Theorem19_13.paddedEconomyQ_orthogonalityResidual_opNorm2Le_of_stacked_bound_top_product_right_inverse`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing the stacked-bound top-right-inverse Gram bridge; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_stacked_top_right_inverse_probe.lean` | PASS | `#check` resolved the raw and `H19.Theorem19_13` stacked-bound top-right-inverse Gram bridge names; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Direct wrapper check after adding `H19.Theorem19_13.householder_paddedFinInput_pre_repair_gram_bound_of_right_inverse_budget`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing the concrete Householder pre-repair Gram bridge; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_householder_prerepair_gram_probe.lean` | PASS | `#check` resolved `H19.Theorem19_13.householder_paddedFinInput_pre_repair_gram_bound_of_right_inverse_budget`; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Direct wrapper check after adding `H19.Theorem19_13.householder_paddedFinInput_pre_repair_gram_bound_of_det_ne_zero_inverse_budget`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing the determinant/nonsingInv pre-repair Gram bridge; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_householder_det_prerepair_probe.lean` | PASS | `#check` resolved `H19.Theorem19_13.householder_paddedFinInput_pre_repair_gram_bound_of_det_ne_zero_inverse_budget`; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Direct wrapper check after adding `H19.Theorem19_13.householder_paddedFinInput_pre_repair_gram_bound_of_upper_diag_inverse_budget`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing the upper-diagonal/nonsingInv pre-repair Gram bridge; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_householder_upper_diag_prerepair_probe.lean` | PASS | `#check` resolved `H19.Theorem19_13.householder_paddedFinInput_pre_repair_gram_bound_of_upper_diag_inverse_budget`; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Direct wrapper check after adding `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_repair` and `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_repair_of_small_unit_roundoff`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing the upper-diagonal repair-certificate source-output and `MGSQRBounds` assembly; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_mgs_upper_diag_repair_assembly_probe.lean` | PASS | `#check` resolved the upper-diagonal repair-certificate source-output and `MGSQRBounds` assembly theorem names; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| UTF-8 `pdfplumber` extraction of `References/1.9780898718027.ch19.pdf` and `References/1.9780898718027.appa.pdf` | PASS | Located Theorem 19.13/Problem 19.12 context in Ch.19 and Appendix A solution 19.12. The source route is the Bjorck-Paige CS decomposition/polar-factor correction map, not a local sensitivity-only argument. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding orthogonal-column preservation, rectangular/square operator-norm product helpers, and `mgsProblem1912_correctionMap_of_csOrthogonalAlgebra`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt` | PASS | Built the updated Gram-Schmidt module so downstream imports see the Problem 19.12 orthogonal-CS correction-map layer. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Direct wrapper check after exposing `H19.Theorem19_13.problem1912_correctionMap_of_csOrthogonalAlgebra`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing the Problem 19.12 orthogonal-CS correction-map wrapper; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_problem1912_cs_orthogonal_probe.lean` | PASS | `#check` resolved the raw helper, raw orthogonal-CS constructor, and `H19.Theorem19_13` wrapper names; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Latest aggregator import check after the Problem 19.12 orthogonal-CS correction-map layer and report refresh. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over touched QR/H19 Lean files | PASS, no matches | Latest placeholder/unsafe scan after the Problem 19.12 orthogonal-CS correction-map layer. |
| `rg -n "[^\x00-\x7F]"` over touched MGS/H19 Lean files and Split 3B reports | PASS, no matches | Latest ASCII hygiene scan after replacing the temporary Lean proof bullets with ASCII proof structure. |
| bundled Git `diff --check` over touched Lean/report files | PASS | Latest whitespace check after the Problem 19.12 orthogonal-CS correction-map layer plus report refresh. |
| `rg -n "[ \t]+$"` over touched Lean/report files | PASS, no matches | Latest trailing-whitespace scan over touched files. |
| `rg --files tmp \| rg "split3b_h19_problem1912_cs_orthogonal_probe\|split3b_h19_problem1912_cs_probe\|split3b_h19_problem1912_correction_map_probe\|split3b_h19_mgs_.*problem1912"` | PASS, no matches | Latest temp-file cleanup check for the Problem 19.12 CS/correction-map probes. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding diagonal CS scalar, diagonal operator-norm, diagonal `T*C=I-S`, and `mgsProblem1912_correctionMap_of_csDiagonalAlgebra`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt` | PASS | Built the updated Gram-Schmidt module so downstream imports see the Problem 19.12 diagonal-CS correction-map layer. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Direct wrapper check after exposing the Problem 19.12 diagonal-CS norm/identity wrappers and correction-map constructor. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing the Problem 19.12 diagonal-CS wrappers; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_problem1912_diagonal_probe.lean` | PASS | `#check` resolved the raw diagonal helpers, raw diagonal-CS constructor, and `H19.Theorem19_13` wrappers; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Latest aggregator import check after the Problem 19.12 diagonal-CS correction-map layer and report refresh. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over touched QR/H19 Lean files | PASS, no matches | Latest placeholder/unsafe scan after the Problem 19.12 diagonal-CS correction-map layer. |
| `rg --pcre2 -n "[^\x00-\x7F]"` over touched MGS/H19 Lean files and Split 3B reports | PASS, no matches | Latest ASCII hygiene scan after the Problem 19.12 diagonal-CS correction-map layer and report refresh. |
| bundled Git `diff --check` over touched Lean/report files | PASS | Latest whitespace check after the Problem 19.12 diagonal-CS correction-map layer plus report refresh. |
| `rg -n "[ \t]+$"` over touched Lean/report files | PASS, no matches | Latest trailing-whitespace scan over touched files. |
| `rg --files tmp \| rg "split3b_h19_problem1912_(diagonal\|cs_orthogonal\|cs_probe\|correction_map_probe)\|split3b_diagonal_probe"` | PASS, no matches | Latest temp-file cleanup check for the Problem 19.12 diagonal/CS probes. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Rechecked after adding `mgsProblem1912_repair_of_csDiagonalAlgebra`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt` | PASS | Built the updated Gram-Schmidt module so downstream imports see the Problem 19.12 diagonal-CS repair theorem. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Direct wrapper check after exposing `H19.Theorem19_13.problem1912_repair_of_csDiagonalAlgebra`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing the Problem 19.12 diagonal-CS repair wrapper; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_problem1912_diagonal_repair_probe.lean` | PASS | `#check` resolved the raw and H19 diagonal-CS repair theorem names; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Latest aggregator import check after the Problem 19.12 diagonal-CS repair theorem and report refresh. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over touched QR/H19 Lean files | PASS, no matches | Latest placeholder/unsafe scan after the Problem 19.12 diagonal-CS repair theorem. |
| `rg --pcre2 -n "[^\x00-\x7F]"` over touched MGS/H19 Lean files and Split 3B reports | PASS, no matches | Latest ASCII hygiene scan after the Problem 19.12 diagonal-CS repair theorem and report refresh. |
| bundled Git `diff --check` over touched Lean/report files | PASS | Latest whitespace check after the Problem 19.12 diagonal-CS repair theorem plus report refresh. |
| `rg -n "[ \t]+$"` over touched Lean/report files | PASS, no matches | Latest trailing-whitespace scan over touched files. |
| `rg --files tmp \| rg "split3b_h19_problem1912_(diagonal_repair\|diagonal\|cs_orthogonal\|cs_probe\|correction_map_probe)\|split3b_diagonal_probe"` | PASS, no matches | Latest temp-file cleanup check for the Problem 19.12 diagonal repair/CS probes. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Direct wrapper check after adding `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair` and `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_of_small_unit_roundoff`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after adding the concrete upper-diagonal diagonal-CS repair-data source-output and `MGSQRBounds` assembly; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_upper_diag_cs_repair_assembly_probe.lean` | PASS | `#check` resolved the upper-diagonal diagonal-CS source-output and `MGSQRBounds` assembly theorem names; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Latest aggregator import check after the upper-diagonal diagonal-CS repair-data assembly and report refresh. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over touched QR/H19 Lean files | PASS, no matches | Latest placeholder/unsafe scan after the upper-diagonal diagonal-CS repair-data assembly. |
| `rg --pcre2 -n "[^\x00-\x7F]"` over touched MGS/H19 Lean files and Split 3B reports | PASS, no matches | Latest ASCII hygiene scan after the upper-diagonal diagonal-CS repair-data assembly and report refresh. |
| bundled Git `diff --check` over touched Lean/report files | PASS | Latest whitespace check after the upper-diagonal diagonal-CS repair-data assembly plus report refresh. |
| `rg -n "[ \t]+$"` over touched Lean/report files | PASS, no matches | Latest trailing-whitespace scan over touched files. |
| `rg --files tmp \| rg "split3b_h19_upper_diag_cs_repair_assembly_probe"` | PASS, no matches | Latest temp-file cleanup check for the upper-diagonal diagonal-CS repair-data assembly probe. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Direct wrapper check after adding `H19.Theorem19_13.rectOpNorm2Le_nonsingInv_frobNorm`, the fallback Frobenius inverse-norm certificate for the common-`R` route. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after adding the fallback Frobenius inverse-norm certificate; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Direct wrapper check after adding `H19.Theorem19_13.qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_frobInv` and `H19.Theorem19_13.mgs_qr_bounds_of_householder_upper_diag_csDiagonalRepair_frobInv_of_small_unit_roundoff`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after adding the upper-diagonal diagonal-CS Frobenius-inverse fallback assemblies; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean tmp\split3b_h19_frob_inv_fallback_probe.lean` | PASS | `#check` resolved the fallback inverse certificate, source-output fallback assembly, and `MGSQRBounds` fallback assembly theorem names; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Latest aggregator import check after the upper-diagonal diagonal-CS Frobenius-inverse fallback assemblies and report refresh. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over touched QR/H19 Lean files | PASS, no matches | Latest placeholder/unsafe scan after the upper-diagonal diagonal-CS Frobenius-inverse fallback assemblies. |
| `rg --pcre2 -n "[^\x00-\x7F]"` over touched MGS/H19 Lean files and Split 3B reports | PASS, no matches | Latest ASCII hygiene scan after the upper-diagonal diagonal-CS Frobenius-inverse fallback assemblies and report refresh. |
| bundled Git `diff --check` over touched Lean/report files | PASS | Latest whitespace check after the upper-diagonal diagonal-CS Frobenius-inverse fallback assemblies plus report refresh. |
| `rg -n "[ \t]+$"` over touched Lean/report files | PASS, no matches | Latest trailing-whitespace scan over touched files. |
| `rg --files tmp \| rg "split3b_h19_frob_inv_fallback_probe\|split3b_h19_upper_diag_cs_repair_assembly_probe"` | PASS, no matches | Latest temp-file cleanup check after the upper-diagonal diagonal-CS Frobenius-inverse fallback assemblies. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Latest aggregator import check after the fallback Frobenius inverse-norm certificate and report refresh. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over touched QR/H19 Lean files | PASS, no matches | Latest placeholder/unsafe scan after the fallback Frobenius inverse-norm certificate. |
| `rg --pcre2 -n "[^\x00-\x7F]"` over touched MGS/H19 Lean files and Split 3B reports | PASS, no matches | Latest ASCII hygiene scan after the fallback Frobenius inverse-norm certificate and report refresh. |
| bundled Git `diff --check` over touched Lean/report files | PASS | Latest whitespace check after the fallback Frobenius inverse-norm certificate plus report refresh. |
| `rg -n "[ \t]+$"` over touched Lean/report files | PASS, no matches | Latest trailing-whitespace scan over touched files. |
| `rg --files tmp \| rg "split3b_h19_upper_diag_cs_repair_assembly_probe"` | PASS, no matches | Latest temp-file cleanup check after the fallback Frobenius inverse-norm certificate. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Final aggregator import check after the full-block-data, block-orthogonality, common-`R`, Gram-expansion, Gram-norm, and common-`R` source-output MGS route plus report refresh. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over touched QR/H19 files | PASS, no matches | Final placeholder/unsafe scan after the common-`R` source-output MGS route. |
| `rg -n "[^\x00-\x7F]"` over touched MGS/H19 Lean files and Split 3B reports | PASS, no matches | Final ASCII hygiene scan after the common-`R` source-output MGS route and report refresh. |
| bundled Git `diff --check` over touched Lean/report files | PASS | Final whitespace check after the common-`R` source-output MGS route plus report refresh. |
| `rg -n "[ \t]+$"` over touched Lean/report files | PASS, no matches | Final trailing-whitespace scan over untracked and ignored touched files as a companion to `git diff --check`. |
| `rg --files tmp \| rg "split3b_h19_mgs_(bridge\|action\|reflector\|padded_stage\|stage_self_dot\|step\|iter\|q_unit\|reverse\|reverse_iter\|blocks\|perturb\|eta\|reindex\|norm_bridge\|hh_bridge\|block_form\|economy_product\|full_block_data\|block_orthogonality\|common_r\|gram_residual\|sensitivity_bridge\|source_sensitivity\|small_unit_roundoff\|residual_budget\|valid_residual_budget\|coefficient_norm_budget\|coefficient_budget\|source_output_common_r)\|split3b_oracle_qr_sensitivity_prompt\|split3b_ch19\|ch19_p2\|ch19_qr_sensitivity"` | PASS, no matches | Final temp-file cleanup check; no current Split 3B MGS probes, ignored Oracle prompt copies, or rendered Ch.19 QR-sensitivity page artifacts remain. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Latest aggregator import check after the determinant/nonsingInv pre-repair Gram bridge and report refresh. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over touched QR/H19 Lean files | PASS, no matches | Latest placeholder/unsafe scan after the determinant/nonsingInv pre-repair Gram bridge. |
| `rg -n "[^\x00-\x7F]"` over touched MGS/H19 Lean files and Split 3B reports | PASS, no matches | Latest ASCII hygiene scan after the determinant/nonsingInv pre-repair Gram bridge and report refresh. |
| bundled Git `diff --check` over touched Lean/report files | PASS | Latest whitespace check after the determinant/nonsingInv pre-repair Gram bridge plus report refresh. |
| `rg -n "[ \t]+$"` over touched Lean/report files | PASS, no matches | Latest trailing-whitespace scan over touched files. |
| `rg --files tmp \| rg "split3b_h19_mgs_.*householder_det_prerepair"` | PASS, no matches | Latest temp-file cleanup check for the determinant/nonsingInv pre-repair Gram probe. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Latest aggregator import check after the upper-diagonal/nonsingInv pre-repair Gram bridge and report refresh. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over touched QR/H19 Lean files | PASS, no matches | Latest placeholder/unsafe scan after the upper-diagonal/nonsingInv pre-repair Gram bridge. |
| `rg -n "[^\x00-\x7F]"` over touched MGS/H19 Lean files and Split 3B reports | PASS, no matches | Latest ASCII hygiene scan after the upper-diagonal/nonsingInv pre-repair Gram bridge and report refresh. |
| bundled Git `diff --check` over touched Lean/report files | PASS | Latest whitespace check after the upper-diagonal/nonsingInv pre-repair Gram bridge plus report refresh. |
| `rg -n "[ \t]+$"` over touched Lean/report files | PASS, no matches | Latest trailing-whitespace scan over touched files. |
| `rg --files tmp \| rg "split3b_h19_mgs_.*upper_diag_prerepair"` | PASS, no matches | Latest temp-file cleanup check for the upper-diagonal/nonsingInv pre-repair Gram probe. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Latest aggregator import check after the upper-diagonal repair-certificate assembly and report refresh. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over touched QR/H19 Lean files | PASS, no matches | Latest placeholder/unsafe scan after the upper-diagonal repair-certificate assembly. |
| `rg -n "[^\x00-\x7F]"` over touched MGS/H19 Lean files and Split 3B reports | PASS, no matches | Latest ASCII hygiene scan after the upper-diagonal repair-certificate assembly and report refresh. |
| bundled Git `diff --check` over touched Lean/report files | PASS | Latest whitespace check after the upper-diagonal repair-certificate assembly plus report refresh. |
| `rg -n "[ \t]+$"` over touched Lean/report files | PASS, no matches | Latest trailing-whitespace scan over touched files. |
| `rg --files tmp \| rg "split3b_h19_mgs_.*repair_assembly"` | PASS, no matches | Latest temp-file cleanup check for the upper-diagonal repair-certificate assembly probe. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\Sylvester\SylvesterSpec.lean` | PASS | Focused Ch16 Sylvester specification candidate check. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\Sylvester\SylvesterBackward.lean` | PASS | Focused Ch16 Sylvester backward-error candidate check. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\Sylvester\SylvesterPerturbation.lean` | PASS | Focused Ch16 Sylvester perturbation candidate check. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\StationaryIteration.lean` | PASS | Focused Ch17 stationary-iteration candidate check. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\MatrixPowers.lean` | PASS | Focused Ch18 matrix-power candidate check. |
| `GramSchmidt.lean`, `Higham19.lean`, `split3b_complete_audit.md`, `split3b_startup_audit.md`, and `split3b_ch19_source_inventory.md` ASCII scan | PASS | New MGS bridge wrappers and report updates contain only ASCII text. |
| `pnpm dlx @steipete/oracle status higham-split3b-current` with bundled Node path | PASS | Oracle session completed; model line reports `gpt-5.5-pro`; browser selector verification unavailable. |
| `pnpm dlx @steipete/oracle ... higham-split3b-givens-route` | FAIL | Browser route reached ChatGPT but attachment upload timed out; superseded by inline session. |
| `pnpm dlx @steipete/oracle ... higham-split3b-givens-inline` | PASS | Browser run completed using inline attachments and current-model strategy; model evidence requested Pro, resolved unavailable, already-selected, verified=no. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Focused check after adding the repaired-perturbation operator/column budget lemmas and correction-map/diagonal-CS repair wrappers from separate top/bottom budgets. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt` | PASS | Built the updated Gram-Schmidt module so downstream imports see the separate-budget Problem 19.12 repair layer. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Direct wrapper check after exposing `problem1912_repairedPerturbation_*`, `problem1912_repair_*_of_perturbation_bounds`, and `qrsensitivitySourceOutput_of_householder_upper_diag_csDiagonalRepair_of_perturbation_bounds`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Rebuilt after exposing the separate-budget source-output assembly; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Latest aggregate import check after the separate-budget repair/source-output layer and report refresh. |
| `lake env lean tmp\split3b_h19_repaired_budget_probe.lean` | PASS | `#check` resolved the new raw and H19 repaired-budget wrappers; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. Temporary probe deleted. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over touched QR/H19 Lean files | PASS, no matches | Latest placeholder/unsafe scan after the separate-budget repair/source-output layer. |
| `rg --pcre2 -n "[^\x00-\x7F]"` over touched MGS/H19 Lean files and Split 3B reports | PASS, no matches | Latest ASCII hygiene scan after replacing the new proof bullets with ASCII proof structure. |
| `rg -n "[ \t]+$"` over touched Lean/report files | PASS, no matches | Latest trailing-whitespace scan over touched Lean and report files. |
| bundled Git `diff --check` over touched Lean/report files | PASS | Latest whitespace check after the separate-budget repair/source-output layer plus report refresh. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Final focused check after adding stacked-column top/bottom budget wrappers. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Final focused check after adding the concrete Householder-stacked diagonal-CS source-output and MGSQRBounds wrappers. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt` | PASS | Final module build after the stacked-column budget wrappers. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Final module build after the concrete Householder-stacked route; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Final aggregate import check after the new Ch19 wrappers. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Resolved the new stacked-budget and concrete Householder-stacked theorem names; `#print axioms` for the two concrete wrappers reported only `propext`, `Classical.choice`, and `Quot.sound`. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over touched QR/H19 Lean files | PASS, no matches | Final placeholder/unsafe scan after the concrete Householder-stacked route. |
| `rg --pcre2 -n "[^\x00-\x7F]"` over touched MGS/H19 Lean files and Split 3B reports | PASS, no matches | Final ASCII hygiene scan after the concrete Householder-stacked route and report refresh. |
| `rg -n "[ \t]+$"` over touched Lean/report files | PASS, no matches | Final trailing-whitespace scan over touched Lean and report files. |
| bundled Git `diff --check` over touched Lean/report files | PASS | Final whitespace check after the concrete Householder-stacked route plus report refresh. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Focused check after adding the Problem 19.12 source-shaped CS block-column Gram identity and transpose/factor-strip helpers. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt` | PASS | Module build after adding `mgsProblem1912_csDiagonal_gram_sum_eq_id`. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Direct wrapper check after exposing `H19.Theorem19_13.problem1912_csDiagonal_gram_sum_eq_id`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Module build after exposing the Problem 19.12 CS Gram wrapper; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Aggregate import check after the Problem 19.12 CS Gram identity and report refresh. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | The raw and H19 CS Gram theorem names resolve; both report only `propext`, `Classical.choice`, and `Quot.sound`. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over touched QR/H19 Lean files | PASS, no matches | Placeholder/unsafe scan after the Problem 19.12 CS Gram identity. |
| `rg --pcre2 -n "[^\x00-\x7F]"` over touched MGS/H19 Lean files and Split 3B reports | PASS, no matches | ASCII hygiene scan after the Problem 19.12 CS Gram identity and report refresh. |
| `rg -n "[ \t]+$"` over touched Lean/report files | PASS, no matches | Trailing-whitespace scan after the Problem 19.12 CS Gram identity and report refresh. |
| bundled Git `diff --check` over touched Lean/report files | PASS | Whitespace check after the Problem 19.12 CS Gram identity plus report refresh. |
| `rg --files tmp \| rg "split3b_h19_repaired_budget_probe"` | PASS, no matches | Temporary repaired-budget probe was removed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Focused check after adding `MGSProblem1912CSDiagonalFactorData` and its conversion/Gram/contraction consequences. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Focused check after exposing the H19 factor-data conversion wrappers and fixed-budget source-output/`MGSQRBounds` wrappers. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Built both touched QR modules after the factor-data route; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Aggregate import check after the factor-data wrapper route. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | New raw and H19 factor-data conversion plus fixed-budget explicit-`rho`/`frobInv` wrapper names resolve; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| placeholder/unsafe scan over touched QR/H19 Lean files | PASS, no matches | No `sorry`, `admit`, `axiom`, `unsafe`, or `opaque` matches after the factor-data route. |
| ASCII and trailing-whitespace scans over touched Lean/report files | PASS, no matches | No non-ASCII or trailing whitespace matches after the factor-data route and report refresh. |
| bundled Git `diff --check` over touched Lean/report files | PASS | No whitespace errors after the factor-data route plus report refresh. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Focused check after adding the explicit CS-witness factor-data builder and existential projection theorem. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Focused check after exposing the H19 explicit CS-witness factor-data builder. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Built both touched QR modules after the explicit CS-witness builder; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Aggregate import check after the explicit CS-witness builder. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Raw and H19 builder/existential names resolve; `#print axioms` for the existential wrappers reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| placeholder/unsafe scan over touched QR/H19 Lean files | PASS, no matches | No `sorry`, `admit`, `axiom`, `unsafe`, or `opaque` matches after the explicit CS-witness builder. |
| ASCII and trailing-whitespace scans over touched Lean/report files | PASS, no matches | No non-ASCII or trailing whitespace matches after the explicit CS-witness builder and report refresh. |
| bundled Git `diff --check` over touched Lean/report files | PASS | No whitespace errors after the explicit CS-witness builder plus report refresh. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Focused check after adding the raw `Nonempty` factor-data bridge. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Focused check after adding H19 `Nonempty` factor-data bridges and fixed-budget existence wrappers. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Built both touched QR modules after the payload-existence route; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Aggregate import check after the payload-existence route. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Raw/H19 nonempty bridge names and four `csDiagonalFactorDataExistsRepair` fixed-budget wrapper names resolve; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\GramSchmidt.lean` | PASS | Focused check after adding the raw nonempty-factor-data to pure correction-map-data existence bridge. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt` | PASS | Rebuilt the dependency so `Higham19` sees the new raw bridge. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Focused check after adding H19 pure correction-map-data existence bridge and four fixed-budget existence wrappers; an initial parallel check saw the old dependency before this rebuild. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Built both touched QR modules after the pure correction-map-data existence route; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Aggregate import check after the pure correction-map-data existence route. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` with `lean --stdin` | PASS | Raw/H19 pure-data existence names and four `correctionMapDataExistsRepair` fixed-budget wrapper names resolve; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over touched QR/H19 Lean files | PASS, no matches | Placeholder/unsafe scan after the pure correction-map-data existence route. |
| `rg --pcre2 -n "[^\x00-\x7F]"` over touched MGS/H19 Lean files and Split 3B reports | PASS, no matches | ASCII hygiene scan after the pure correction-map-data existence route and report refresh. |
| `rg -n "[ \t]+$"` over touched Lean/report files | PASS, no matches | Trailing-whitespace scan after the pure correction-map-data existence route and report refresh. |
| bundled Git `diff --check` over touched Lean/report files | PASS | Whitespace check after the pure correction-map-data existence route plus report refresh. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Focused check after adding the determinant-nonzero `R11` diagonal bridge and determinant-based pure-data/existence fixed-budget wrappers. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Built after the determinant-nonzero `R11` route; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| `lake env lean LeanFpAnalysis\FP\Algorithms.lean` | PASS | Aggregate import check after the determinant-nonzero `R11` route; rerun after an initial parallel race checked before the rebuilt `Higham19.olean` was available. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` with `lean --stdin` | PASS | Determinant helper, pure-data repair wrappers, and pure-data existence determinant wrappers resolve; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over touched QR/H19 Lean files | PASS, no matches | Placeholder/unsafe scan after the determinant-nonzero `R11` route. |
| `rg --pcre2 -n "[^\x00-\x7F]"` over touched MGS/H19 Lean files and Split 3B reports | PASS, no matches | ASCII hygiene scan after the determinant-nonzero `R11` route and report refresh. |
| `rg -n "[ \t]+$"` over touched Lean/report files | PASS, no matches | Trailing-whitespace scan after the determinant-nonzero `R11` route and report refresh. |
| bundled Git `diff --check` over touched Lean/report files | PASS | Whitespace check after the determinant-nonzero `R11` route plus report refresh. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Focused check after adding `H19.Theorem19_13.firstStoredPanelStep_eq_panelFromTopAndTrailing_applyMatrixRect`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Built after the first-pivot recursive/stored storage bridge; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | The first-pivot storage bridge resolves; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over `Higham19.lean` | PASS, no matches | Placeholder/unsafe scan after the first-pivot storage bridge. |
| bundled Git `diff --check` over `Higham19.lean` | PASS | Whitespace check after the first-pivot storage bridge; Git repeated line-ending notices for touched Lean files. |
| `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean` | PASS | Focused check after adding `H19.Theorem19_13.qrPanel_R_nonzero_eq_firstStoredPanelStep`. |
| `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | Built after the nonzero first-recursion stored-panel bridge; pre-existing `GivensSpec.lean` unused-simp warnings replayed. |
| stdin `#check`/`#print axioms` probe importing `LeanFpAnalysis.FP.Algorithms.QR.Higham19` | PASS | The nonzero first-recursion bridge resolves; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b"` over `Higham19.lean` | PASS, no matches | Placeholder/unsafe scan after the nonzero first-recursion bridge. |
| bundled Git `diff --check` over `Higham19.lean` | PASS | Whitespace check after the nonzero first-recursion bridge; Git repeated line-ending notices for touched Lean files. |

Not yet run for this complete audit:

- full `lake build`;
- `lake env lean examples/LibraryLookup.lean`;
- full placeholder scan over `LeanFpAnalysis`, `Main.lean`, and `examples`;
- `#print axioms` for the future final Theorem 19.13 source theorem;
  Theorems 19.4, 19.10, the Algorithm 19.12 wrapper/step-shape facts, and the
  `(19.28)` Householder-MGS vector-normalization and reflector-involution
  bridge have been checked.

## GitHub synchronization

- Local branch: `main`.
- Latest pushed proof/merge HEAD before this report-sync update: `0b55991`.
- Split-prefixed milestone commit: `2b1ef45`
  (`Split 3B: prove Ch19 actual-active two-column bridge`).
- Integration: local `main` and `origin/main` were equal at `575869c` before
  theorem design.  Remote `main` later advanced to `2e6c1ce`; it was merged
  cleanly as `0b55991` before pushing, preserving incoming Split 3A/library
  lookup work.
- Verification after implementation: `lake env lean LeanFpAnalysis\FP\Algorithms\QR\Higham19.lean`,
  `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19`, placeholder scan,
  `git diff --check`, and stdin `#print axioms` probe all passed.
- Pushed to `origin/main`: yes, `git push origin main` advanced
  `origin/main` to `0b55991`; this report-sync update records that push.
- Remaining local uncommitted files: pre-existing `.gitignore` modification and
  untracked `.codex/config.toml`.

## Documentation

- Audit/report path: `chapter_splitting/reports/split3b_complete_audit.md`.
- Legacy compatibility path: `chapter_splitting/reports/split3b_startup_audit.md`.
- Detailed Ch.19 source inventory path: `chapter_splitting/reports/split3b_ch19_source_inventory.md`.
- Prior Oracle prompt path: `chapter_splitting/oracle_prompts/higham_split3b_startup_plan.tex`.
- Givens QR Oracle prompt path: `chapter_splitting/oracle_prompts/higham_split3b_givens_qr_route.tex`.
- QR-sensitivity Oracle prompt path: `chapter_splitting/reports/split3b_oracle_qr_sensitivity_prompt.md`.
- Ch19 CS/polar bottleneck ledger path: `chapter_splitting/reports/split3b_ch19_cs_polar_bottleneck.md`.
- No theorem note or PDF was generated.
- The `Open selected-scope items` and `Foundation feasibility gate` sections remain the broad gate ledgers; the CS/polar bottleneck ledger is resolved and retained as a route record.

## Open issues

- The legacy `split3b_startup_audit.md` path may remain for continuity, but
  `split3b_complete_audit.md` is the canonical audit going forward.
- Exact rendered source extraction is still required before implementation for
  all selected rows.  Text extraction is not reliable enough for final theorem
  surfaces.
- The current local modules contain useful work but use stale/shifted chapter
  labels.  Do not count a local theorem as a source closure until its statement
  is compared to the current Ch16-Ch19 PDFs.
- No Split 4-facing outward QR name is currently absent: `H19.Theorem19_4.householder_qr_backward_error`,
  `H19.Theorem19_10.givens_qr_backward_error`, and
  `H19.Theorem19_13.mgs_qr_bounds` are exported.  The Theorem 19.13 export is
  conditional on explicit `R11` determinant and Frobenius-inverse/final-budget
  hypotheses rather than the fully printed source condition statement.
- MGS stability, especially source nonbreakdown, sharp right-inverse/condition
  estimates, recursive/stored reflector-data identification, final
  constant/radius bookkeeping, and exact printed-constant audits, is currently
  the largest remaining foundation in Ch19.
- Appendix A solution rows for 16.x-19.x are inventory-accounted but not yet
  source-audited for proof dependencies.
