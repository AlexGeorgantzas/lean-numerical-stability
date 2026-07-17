# Higham Chapter 5 Source Coverage Ledger

## Source and Scope

- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002).
- Chapter: 5, "Polynomials" (book pp. 93–104).
- Source of truth for this audit: extracted chapter text `ch05.txt` (full-chapter read).
- Mode: core.
- Split ownership: pre-split foundational chapter (Chapters 1–6 band); audited from the Split 3B/4 worktree
  (`formalize/split4-claude`, worktree `ch18-split3-claude-claude-ch18-split3-20260703044646`).
- Main Lean file: `LeanFpAnalysis/FP/Algorithms/Horner.lean` (single module, ~8760 lines; covers §5.1–§5.4
  and Problems 5.1–5.6 surfaces).
- Audit date: 2026-07-16. Audit type: statement-level verification (no new proofs, no edits to existing files).
- Axiom spot-check (9 load-bearing decls, throwaway `#print axioms`, deleted after): all
  `[propext, Classical.choice, Quot.sound]` — axiom-clean. Checked:
  `fl_hornerDesc_backward_error_coefficients`, `fl_hornerDesc_forward_error_bound`,
  `fl_hornerDesc_running_error_bound_of_inverseLocal`,
  `finiteRoundToEvenOp_hornerStep_inverseLocalError_of_finiteNormalRange`,
  `fl_hornerDerivativeDesc_first_derivative_error_bound`,
  `fl_dividedDifferenceFiniteCoeffs_abs_sub_exact_le_scalar_absLProduct_gamma3`,
  `dividedDifferenceResidual_error_bound`,
  `matrixPolynomialP3_horner_infNorm_error_bound_first_order_remainder`,
  `fl_rootProductEval_forward_error_bound`.

- **Selected-scope gate: FAIL** (see gate line at the bottom; the headline Horner and derivative results are
  closed at printed strength, but four precise body claims are MISSING and two numbered rows are honest
  PARTIALs whose residuals are recorded below).

## Primary Labels

| Label | Printed statement (summary) | Status | Lean decls | Scope notes |
|---|---|---|---|---|
| Algorithm 5.1 (Horner with running error bound, §5.1) | Evaluate `y = fl(p(x))` by Horner's rule and a quantity `mu = u*(2*mu' - \|y\|)` with `\|y - p(x)\| <= mu`; derivation via (5.4) and the `f_i`/`pi_i`/`mu_i` recurrences | **VERIFIED** (real data) | `fl_hornerRunningStep`, `fl_hornerRunningState`, `fl_hornerRunningBound`, `fl_hornerRunningState_fst_eq_fl_hornerDesc`, `fl_hornerDesc_running_error_bound_of_inverseLocal`; local model `hornerStepInverseLocalError` discharged concretely by `finiteRoundToEvenOp_hornerStep_inverseLocalError_of_finiteNormalRange` | The a posteriori bound `\|fl_hornerDesc - polyDesc\| <= fl_hornerRunningBound` is proved under the (5.4) inverse local step estimate, which is NOT smuggled: it is a named predicate, proved outright for the concrete round-to-even format under finite-normal-range side conditions (exactly the applicability domain of Higham's models (2.4)/(2.5)). The `mu` recurrence is carried in exact arithmetic over the rounded `y`-iterates, matching the printed derivation (the printed algorithm's own rounding of `mu` is not modeled — same idealization as the source analysis). Exact-arithmetic sanity reductions: `fl_hornerDesc_exactWithUnitRoundoff`. **Complex-data remark (Lemma 3.5 variant, `sqrt(2)*gamma_2` final line) NOT formalized** — real coefficients/argument only. |
| Algorithm 5.2 (polynomial and first k derivatives at alpha, §5.2) | `y_i = p^(i)(alpha)`, `i = 0:k`, by repeated synthetic division + factorial scaling; error analysis (5.5)–(5.7) for the first derivative | **PARTIAL** | Exact core: `hornerDerivativeStep/Desc`, `hornerDerivativeDesc_fst_eq_polyDesc`, `hornerDerivativeDesc_snd_eq_polyDescDeriv`, `hornerSyntheticDivisionDesc_spec`, `hornerSyntheticQuotientDesc_eval_eq_polyDescDeriv`; higher orders: `hornerTaylorFunctionStep/Desc`, `polyDescHigherDeriv`, `hornerHigherDerivativeOutput(s)`, `hornerTaylorFunctionDesc_zero/one_eq_...`; rounded: `fl_hornerDerivativeStep/Desc` + the (5.5)–(5.7) chain below | Value and FIRST-derivative components are proved exactly correct, and the rounded first-derivative analysis is closed at printed (5.7) strength (see equations table). Residual: for orders `i >= 2` the factorial-scaled outputs are only DEFINED by the differentiated recurrence — no theorem identifies `polyDescHigherDeriv alpha i` with the i-th derivative of `polyDesc` for `i >= 2`, and no rounding analysis exists there ("analogous bounds hold for all derivatives" prose not formalized). Derivatives are the FORMAL coefficient derivatives (`polyDescDeriv` etc.), which is the printed object. |

## Numbered Equations

| Eq. | Printed content | Status | Lean decls / notes |
|---|---|---|---|
| (5.1) | `p(x) = a_0 + a_1 x + ... + a_n x^n`; Horner recurrence; 2n flops | **VERIFIED** (definition row) | `polyDesc`, `hornerStep`, `hornerDesc`, `hornerDesc_eq_polyDesc` (descending-list convention documented in module header). Flop count not formalized (editorial). |
| (5.2) | Backward error: `qhat_0 = (1+theta_1)a_0 + (1+theta_3)a_1 x + ... + (1+theta_2n)a_n x^n`, `\|theta_k\| <= gamma_k` | **VERIFIED** (uniform-`gamma_2n` form) | `fl_hornerFold_backward_error_coefficients`, `fl_hornerDesc_backward_error_coefficients`: rounded Horner = exact evaluation of coefficientwise-perturbed polynomial, every perturbation `<= gamma fp (2*(len-1))`. This matches the prose conclusion ("relative perturbations of size at most gamma_2n"). The finer per-index ladder (`theta_{2i+1}` for `a_i`, `theta_{2n}` for `a_n`) is not separately stated — recorded as a sharpness note, not a gap (all printed consequences use the uniform form). Hypothesis `gammaValid` (= `2n*u < 1`) is the standard printed applicability condition. |
| (5.3) | Forward bound `\|p(x) - qhat_0\| <= gamma_2n * ptilde(\|x\|)` | **VERIFIED** | `fl_hornerDesc_forward_error_bound` with majorant `polyDescAbs` (= `ptilde(\|x\|)`); adapter `abs_polyDescPairsPerturbed_sub_polyDescPairs_le`. |
| ψ display (unnumbered, §5.1) | Relative bound `\|p-qhat\|/\|p\| <= gamma_2n * psi(p,x)`; `psi = 1` if `a_i >= 0, x >= 0` (or alternating signs, `x <= 0`) | **MISSING** | No `psi`-style relative-error decl and no sign-pattern lemma found. Trivial corollary of (5.3) for the first part; the `psi = 1` sign-pattern claim needs its own small lemma. |
| (5.4) | Local step model `(1+eps_i) qhat_i = x*qhat_{i+1}(1+delta_i) + a_i`, `\|delta_i\|,\|eps_i\| <= u` (models (2.4)+(2.5)) | **VERIFIED** | Forward form: `fl_hornerStep_unroll`, `fl_hornerStep_forward_local_error_bound`; inverse (source) form: `hornerStepInverseLocalError` + algebraic bridges `hornerStep_abs_error_le_of_mul_forward_add_inverse` / `..._of_mul_add_error_bounds` (underflow-tolerant variant); discharged concretely by `finiteRoundToEvenOp_hornerStep_inverseLocalError_of_finiteNormalRange` under finite-normal-range hypotheses (the printed domain of (2.5)). Abstract `FPModel` alone supplies only the forward form — honestly flagged in docstrings. |
| `f_i`/`pi_i`/`mu_i` recurrences (unnumbered, §5.1) | Majorizing sequences leading to Algorithm 5.1 | **VERIFIED** (as embedded invariants) | `fl_hornerRunningStep_error_bound_of_inverseLocal`, `fl_hornerRunningFold_error_bound_of_inverseLocal`, `fl_hornerRunningState_abs_fst_le_two_mu`, nonnegativity lemmas; exact-arithmetic mirror `hornerRunningStep/State/Bound` (Algorithm 5.1 shape). |
| Synthetic division displays (§5.2) | `p(x) = (x-alpha) q(x) + r`, `r = q_0 = p(alpha)`, `p'(alpha) = q(alpha)`, divided-difference remark | **VERIFIED** | `hornerSyntheticDivisionDesc_spec`, `hornerSyntheticQuotientDesc_eval_eq_polyDescDeriv`, `hornerSyntheticQuotientDesc_spec`-family; the `q(x) = (p(x)-p(alpha))/(x-alpha)` remark is an immediate rearrangement of the proved spec (not separately stated). Taylor-expansion display: output surface only (see Algorithm 5.2 PARTIAL). |
| (5.5) | Bidiagonal system `U_{n+1} q = a`; `(U+Delta_1)qhat = a`, `\|Delta_1\| <= u\|U\|`; `\|q-qhat\| <= u\|U^{-1}\|\|U\|\|q\| + O(u^2)` | **PARTIAL** | Matrix objects and the exact perturbation bridge are formalized: `highamBidiagonalU` (+ entry lemmas), `highamBidiagonalForwardErrorMajorant`, `highamBidiagonal_forward_error_from_backward` (exact bound with `\|qhat\|` in place of `\|q\| + O(u^2)` — a stronger, remainder-free form, honestly documented). Residual: the hypothesis `(U+Delta)qhat = a` with `\|Delta\| <= u\|U\|` is NOT instantiated from the concrete rounded Horner recurrence in matrix form; the proved route to (5.7) instead goes through the equivalent list-based quotient majorants (`fl_hornerSyntheticQuotient*` chain). |
| (5.6) | `\|r - rhat\| <= u\|U_n^{-1}\|\|U_n\|\|r\| + u\|U_n^{-1}\|\|U_n^{-1}\|\|U_n\|\|q\| + O(u^2)`; the three displayed `\|U\|`-product matrices | **PARTIAL** | The printed two-solve decomposition is formalized in exact list form: `fl_hornerDerivativeDesc_snd_backward_error_coefficients` (second solve = perturbed evaluation of the computed quotient, `gamma_2n` coefficientwise), `fl_hornerDerivativeDesc_snd_forward_error_bound_to_fl_quotient`, `fl_hornerDerivativeDesc_snd_error_bound_via_fl_quotient` (splits exactly into the (5.5) and (5.6) subproblems). Residual: the literal matrix displays `\|U_n^{-1}\|\|U_n\|` and `\|U_n^{-1}\|\|U_n^{-1}\|\|U_n\|` (entries `2\|alpha\|^k`, `(2k-1)\|alpha\|^{k-1}`) are not formalized; they are proof intermediates subsumed by the closed (5.7). |
| (5.7) | `\|p'(alpha) - rhat_0\| <= 2u * sum k^2\|a_k\|\|alpha\|^{k-1} + O(u^2) <= 2nu * ptilde'(alpha) + O(u^2)` | **VERIFIED** (final display, exact remainder) | Direct coupled route: `fl_hornerDerivativeDesc_snd_backward_error_coefficients_coupled` (derivative output = exact FORMAL derivative of a `gamma_2n`-perturbed polynomial), `fl_hornerDerivativeDesc_snd_forward_error_bound_coupled` (`gamma_2n * ptilde'`), and the printed first-order display `fl_hornerDerivativeDesc_first_derivative_error_bound` = `2n*u*ptilde'(x)` + named exact remainder `fl_hornerDerivativeDescFirstOrderRemainder` (provably 0 at `u = 0`, explicitly quadratic in `n*u`) — the `O(u^2)` is replaced by an exact closed-form remainder, which is stronger than printed. The intermediate `2u*sum k^2\|a_k\|\|alpha\|^{k-1}` display (k^2 weights) is not separately stated; the Lean constant `gamma_2n * k`-weights sits between the two printed displays. Alternative majorant-budget routes also present (`..._with_derivAbs_and_source_majorant`, `..._first_order_source_remainder`). |
| (5.8) | Newton form `p(x) = sum c_i prod_{j<i}(x - alpha_j)` | **VERIFIED** (definition row) | `newtonFormAux`, `newtonForm`, `newtonFormNested`, `newtonForm_eq_newtonFormNested`. |
| Divided-difference recurrence (boxed, §5.3) | `c_j^{(k+1)} = (c_j^{(k)} - c_{j-1}^{(k)})/(alpha_j - alpha_{j-k-1})`; 3n²/2 flops | **VERIFIED** (definition row) | `dividedDifferenceStep`, `dividedDifferenceCoeffs`, `dividedDifferenceFiniteCoeffs` (+ `L_k = D_k^{-1} M_k` structure via `dividedDifferenceLMatrix(Action)` and equivalence `dividedDifferenceLMatrixAction_eq_step`, `dividedDifferenceFiniteCoeffs_eq_LProductAction`). Flop count not formalized (editorial). |
| (5.9) | `chat^{(k+1)} = G_k L_k chat^{(k)}`, `eta_ij = (1+delta_1)(1+delta_2)(1+delta_3)` | **VERIFIED** | `fl_dividedDifferenceStep`, `fl_dividedDifferenceStep_entry_error_factors` (exact triple-factor form), `fl_dividedDifferenceStep_entry_gamma3`, `dividedDifferenceGMatrix(Action)`, `dividedDifferenceGMatrixAction_LMatrixAction_eq`, finite adapters `fl_dividedDifferenceStep_exists_GMatrixAction_gamma3`. Hypotheses: distinct nodes (printed) plus `fl_sub(nodes) != 0` (rounded denominators nonzero — an added no-degenerate-rounding side condition, honestly stated; automatic in the printed real-arithmetic idealization). |
| (5.10) | `chat = (L_{n-1}+DeltaL_{n-1})...(L_0+DeltaL_0) f`, `\|DeltaL_i\| <= gamma_3 \|L_i\|` | **VERIFIED** (equivalent `G*L`-product form) | `fl_dividedDifferenceFiniteCoeffs_eq_GLProductAction_of_row_factors`, `fl_dividedDifferenceFiniteCoeffs_exists_GLProductAction_gamma3` (`\|eta - 1\| <= gamma_3` per active row; `G_k L_k = L_k + DeltaL_k` with `\|DeltaL_k\| <= gamma_3\|L_k\|` is the same statement). |
| (5.11) | `\|c - chat\| <= ((1-3u)^{-n} - 1) \|L_{n-1}\|...\|L_0\| \|f\|` | **VERIFIED** | `fl_dividedDifferenceFiniteCoeffs_abs_sub_exact_le_absLProduct_gap_gamma3` (gap form) and the printed scalar-constant form `fl_dividedDifferenceFiniteCoeffs_abs_sub_exact_le_scalar_absLProduct_gamma3`: constant `(1+gamma_3)^m - 1` which equals `(1-3u)^{-m} - 1` exactly (`1 + gamma_3 = 1/(1-3u)`); majorant `dividedDifferenceAbsLProductAction ... \|f\|` = `\|L_{m-1}\|...\|L_0\|\|f\|`. Same node-distinctness + rounded-denominator hypotheses as (5.9)/(5.10). Monotone-ordering corollary (`alpha_0 < ... < alpha_n` implies `\|L_{n-1}\|...\|L_0\| = \|L\|`, "very satisfactory bound") **not formalized** — see gaps. |
| (5.12) | Residual unwind: `\|f - L^{-1} chat\| <= ((1-3u)^{-n} - 1)\|L_0^{-1}\|...\|L_{n-1}^{-1}\|\|chat\|` | **PARTIAL** | `dividedDifferenceLInvAction(Nat)`, `dividedDifferenceAbsLInvAction`, inverse identities `dividedDifferenceLInvAction_LMatrixAction_eq`, `dividedDifferenceLInvProductAction_finiteCoeffs_eq_data`, and the bound `dividedDifferencePerturbedLInvProduct_abs_le` / `dividedDifferenceResidual_error_bound` with the exact printed constant. Residual: the theorem takes the perturbed inverse steps (`L_k^{-1} + DeltaL_k^{-1}`, `\|DeltaL_k^{-1}\| <= gamma_3\|L_k^{-1}\|`) and `f = perturbed unwind of chat` as HYPOTHESES; the concrete discharge from the rounded recurrence (5.9) (i.e., `G_k^{-1}` absorbed into the inverse-step perturbation for the actual `fl_dividedDifferenceFiniteCoeffs`) is not present. Conditional at exactly the source's "unwind the analysis" step. |
| Newton-evaluation displays (unnumbered, §5.3 end) | Generalized Horner for the Newton form: `qhat_0 = c_0<1> + (x-alpha_0)c_1<4> + ... + (...)c_n<3n>`; forward bound `gamma_3n * sum \|c_i\| prod \|x - alpha_j\|` | **MISSING** | Only the EXACT Newton-form evaluators exist (`newtonForm`, `newtonFormNested`); no rounded (`fl_`) generalized-Horner Newton evaluation and no `<3n>`/`gamma_3n` backward/forward bound found anywhere in the repo. |
| (5.13a,b) | Leja ordering: `\|alpha_0\| = max`, prefix-product maximization | **VERIFIED** (definition + spec) | `lejaPrefixProduct` (+ lemmas), `IsLejaOrdering`, accessors `IsLejaOrdering.first_abs_max`/`step_product_max`; greedy construction certificate `LejaGreedyFirstChoice/StepChoice`, `IsLejaGreedyTrace`, `IsLejaGreedyTrace.isLejaOrdering`. |
| (5.14) | Matrix polynomials `P1`, `P2`, `P3(X) = A_0 + A_1 X + ... + A_n X^n` | **VERIFIED** (for `P3`, real square matrices) | `matrixPolyP3Desc`, `matrixHornerP3Step/Desc`, `matrixHornerP3Desc_eq_matrixPolyP3Desc`. `P1`/`P2` displays not separately defined (`P1` is the scalar-coefficient special case; `P2` evaluation is called "straightforward" in the source); coefficients/argument are real (`Fin n -> Fin n -> R`) whereas the book states `C^{m x m}` — real-entry restriction noted. Paterson–Stockmeyer discussion: editorial (SKIP-OK, cites [928], [509]). |

## Problems (optional in core mode)

| Problem | Status | Lean decls / notes |
|---|---|---|
| 5.1 (derive Algorithm 5.2 by differentiating Horner) | **PARTIAL** | Dedicated section: `hornerTaylorFunctionStep/Desc` (differentiated recurrence on unscaled Taylor coefficients), factorial rescaling `polyDescHigherDeriv`, and equivalence with ordinary Horner / the derivative recurrence at orders 0 and 1 (`hornerTaylorFunctionDesc_zero_eq_polyDesc`, `..._one_eq_polyDescDeriv`). Orders `i >= 2` not identified with derivatives (same residual as Algorithm 5.2). |
| 5.2 (error analysis of the "beginner's" power-building algorithm) | **VERIFIED** (budget form) | `beginnerPowerStep/EvalAsc` (+ exact correctness `beginnerPowerEvalAsc_eq_polyAsc`), `fl_beginnerPowerStep/EvalAsc`, recursive budget `beginnerPowerForwardBudget(From)`, bound `fl_beginnerPowerEvalAsc_forward_error_bound(_poly)`. The analysis is an exact a posteriori budget over all 3 rounded ops per term rather than a closed `gamma_k * ptilde` display — a genuine (indeed sharper) error analysis; closed-form display not extracted. |
| 5.3 (even/odd splitting error bound) | **VERIFIED** (budget form) | `evenCoeffsAsc`/`oddCoeffsAsc`, exact split `polyAsc_evenOdd_split`, `evenOddSplitEvalAsc(_eq_polyAsc)`, rounded evaluator `fl_evenOddSplitHornerEvalAsc`, budget `evenOddSplitForwardBudget`, bound `fl_evenOddSplitHornerEvalAsc_forward_error_bound` (includes the `y = x*x` argument-perturbation term via `polyAsc_arg_error_bound`). Same budget-form note as 5.2. |
| 5.4 (Leja ordering algorithm in n² flops) | **VERIFIED** (spec level) | Greedy-trace certificate (`IsLejaGreedyTrace`) proved to satisfy (5.13); flop budget `lejaGreedyFlopCount` with `lejaGreedyFlopCount_eq_square` (`= n^2` exactly). No executable/computable implementation of the ordering — recorded as a note, adequate for the "write down an algorithm + count flops" ask at spec level. |
| 5.5 (error analysis of root-product evaluation) | **VERIFIED** | `rootProductEval(From)`, `fl_rootProductEval(From)`, counter form `fl_rootProductEvalFrom_exists_relErrorCounter` (exactly `2n` relative-error factors, i.e. `phat = p*<2n>`), relative bound `fl_rootProductEval_forward_error_bound` (`gamma_2n * \|p(x)\|`) — the natural printed-strength answer. |
| 5.6 (Horner for `P3`: `\|P3 - P3hat\| <= n(m+1)u ptilde_3(\|X\|) + O(u^2)`, 1- and inf-norms) | **VERIFIED** (real entries; exact remainder) | Full chain: `fl_matAdd`/`fl_matMul` norm error bounds, majorants `matrixPolyP3{Inf,OneNorm}Majorant` (= `ptilde_3(\|X\|)`), budgets, geometric closure `matrixPolynomialP3_horner_{infNorm,oneNorm}_error_bound_geometric`, and the printed first-order display `matrixPolynomialP3_horner_{infNorm,oneNorm}_error_bound_first_order_remainder`: coefficient `degree * (m+1) * u` (Lean `(coeffsDesc.length - 1) * ((n:R)+1) * fp.u`, matrix dimension `n` = book's `m`) times `ptilde_3`, plus named exact remainder `matrixHornerP3GeometricFirstOrderRemainder` (0 at `u = 0`). Both norms as printed. Real entries vs the book's `C^{m x m}` — noted. |
| 5.7 (research problem: stability of fast evaluation schemes) | **SKIP-OK** (research problem; explicitly open in the source) | No formalization expected. |

## Honest-Strength Notes

1. **No hidden target-equivalent hypotheses found in the closed rows.** The two deliberately
   hypothesis-shaped devices are honestly flagged in-code: `hornerStepInverseLocalError` (the (5.4)
   inverse local estimate; discharged for the concrete round-to-even format under finite-normal-range,
   i.e. the printed domain of models (2.4)/(2.5)) and the (5.12) perturbed-unwind step (NOT discharged —
   that row is graded PARTIAL for exactly this reason).
2. **Constants are derived, not assumed**: `gamma_2n` in (5.2)/(5.3), `(1+gamma_3)^n - 1 = (1-3u)^{-n} - 1`
   in (5.11)/(5.12), `2nu + exact remainder` in (5.7), `n(m+1)u + exact remainder` in Problem 5.6. Where the
   book writes `O(u^2)`, the Lean statements carry named exact remainders that vanish at `u = 0` and are
   explicitly quadratic in the accumulated roundoff — stronger than printed.
3. **Conventions**: coefficient lists are descending `[a_n, ..., a_0]` (`polyDesc`) or ascending (`polyAsc`,
   Problems 5.2/5.3); `p'` is the formal coefficient derivative (`polyDescDeriv`), which is the printed
   object; divided differences use function-indexed nodes with `Fin (n+1)` finite columns.
4. **Real-only scope**: all of Chapter 5 is formalized over `R`. The book's complex remarks (Algorithm 5.1
   complex variant via Lemma 3.5; `C^{m x m}` in (5.14)) are not covered.
5. A docstring citation without an attached genuine theorem was NOT counted anywhere in this ledger; every
   VERIFIED row above names the theorem whose statement was read and matched against the printed row.

## Selected-scope gate: FAIL

Open rows blocking PASS (all concrete):

1. **Newton-form evaluation error analysis (§5.3 closing displays)** — MISSING: no rounded generalized-Horner
   evaluator for the Newton form and no `<3n>` backward / `gamma_3n * sum \|c_i\| prod \|x - alpha_j\|` forward
   bound. This is a precise body claim ("A straightforward analysis shows that (cf. (5.2)) ...").
2. **ψ(p,x) relative-error display and the `psi = 1` sign-pattern claim (§5.1)** — MISSING (small corollary
   of (5.3) plus a sign-pattern lemma).
3. **Monotone-ordering corollary to (5.11)/(5.12)** (`alpha_0 < ... < alpha_n` implies
   `\|L_{n-1}\|...\|L_0\| = \|L\|` and the "very satisfactory" bounds `((1-3u)^{-n}-1)\|L\|\|f\|`,
   `((1-3u)^{-n}-1)\|L^{-1}\|\|chat\|`) — MISSING.
4. **Algorithm 5.1 complex-data remark** (`sqrt(2)*gamma_2*(2*mu - \|y\|)` final line via Lemma 3.5) — MISSING.

Documented PARTIAL residuals (do not block a future PASS if the four rows above close, but must stay recorded):

- (5.12): concrete instantiation of the perturbed inverse-unwind hypotheses from the rounded recurrence (5.9).
- Algorithm 5.2 / Problem 5.1: identification of the order-`i >= 2` factorial-scaled outputs with the higher
  derivatives, and the "analogous bounds hold for all derivatives" prose.
- (5.5)/(5.6): literal matrix-form instantiation (`(U+Delta_1)qhat = a`, `\|Delta_1\| <= u\|U\|`) and the three
  displayed `\|U\|`-product matrices — currently subsumed by the equivalent list-form route that closes (5.7).

Headline verdict for the audit brief: **Algorithm 5.1 + (5.2)/(5.3) gamma_2n backward/forward Horner theorems
are genuinely formalized at printed strength (axiom-clean); the Algorithm 5.2 first-derivative analysis is
closed at the printed (5.7) display with exact remainders; the gate FAIL comes from the four unclosed body
claims above, chiefly the Newton-form evaluation bound.**

## Cross-Chapter Role

- **§1.17 (Rump/Kahan rational-function example)**: `kahanHorner*` decls (see README core-theory table) reuse
  the Horner surfaces for the nonrandom-rounding case study.
- **Chapter 3**: this chapter is the canonical consumer of Lemma 3.1/`gamma_k` algebra
  (`gamma_mul`, `gamma_eq_linear_plus_quadratic_remainder`) and of the §3.3 running-error-analysis pattern;
  the running-bound machinery here is the template later running bounds cite.
- **Chapter 22 (Vandermonde systems)**: divided differences, the Newton form (5.8), the `L_k` factorization,
  and the Leja ordering (5.13, §22.3.3) are the direct inputs to the ch22 primal/dual Vandermonde algorithms;
  the (5.9)–(5.12) machinery formalized here is the natural substrate for the ch22 error analyses.
- **Matrix-function chapters / P1 evaluation**: the (5.14)/Problem 5.6 matrix-Horner engine (norm-level matmul
  error propagation, `ptilde_3` majorants) is reusable wherever matrix polynomials are evaluated
  (Paterson–Stockmeyer contexts, cf. [509, Chap. 11] citations in the source).
- **Chapter 28.6 / zero-finding**: Algorithm 5.1's stopping-criterion use for polynomial zero-finders is
  editorial here; no ch28 consumer yet.
