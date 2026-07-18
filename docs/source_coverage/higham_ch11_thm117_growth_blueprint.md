# Theorem 11.7 bounded-growth derivation — blueprint (multi-session effort)

Goal: **derive** the tridiagonal Bunch bounded element-growth so that `hfactor`
(the factor-norm hypothesis of `higham11_7_bunch_tridiagonal_backward_error`) is
discharged *from the algorithm*, replacing the assumed `TriPivotData`. This turns
the CONDITIONAL 11.7 gate into a genuine closure.

Status legend: [DONE] already in repo · [NEW] to be built · [OPEN] the hard part.

## 1. The algorithm (Higham, Algorithm 11.6) — confirmed from the source

Symmetric tridiagonal `A ∈ ℝⁿˣⁿ`. Constants:
- `α = (√5−1)/2 ≈ 0.618`, with `α² = 1 − α` (`bunchTridiagonalAlpha_sq`). Note `1/α = φ = (√5+1)/2 ≈ 1.618`.
- **`σ = max{|aᵢⱼ|} = ‖A‖_M`, computed ONCE at the start** (this is the crux — a
  *fixed* scale used in every stage's pivot test). Call it `M₀`.

First-stage pivot test (recursed structurally): `if σ|a₁₁| ≥ α a₂₁²` then `s=1` else `s=2`.
Growth stays bounded **because σ is fixed**; a per-stage `σ_ℓ = ‖A^ℓ‖_M` would compound.

## 2. Why growth is bounded by the CONSTANT `K = (1+γ₃)(1+1/α) ≈ 2.618(1+γ₃)`

- **Off-diagonals never grow** beyond rounding: `flSchurCompl`/`flSchurCompl2`
  copy off-corner entries as `fl_sub(shifted, 0) = shifted·(1+δ)`
  (`fl_sub_zero_right`), so `|off-diag of A^ℓ| ≤ (1+u)^ℓ·M₀ ≤ 1.01 M₀` under `n·u ≤ 1/100`.
- **Only the leading corner `A^ℓ(0,0)` is genuinely modified** each stage; the rest
  of the reduced matrix is the shifted submatrix (× `(1+u)` per stage). Non-corner
  diagonals are therefore `≤ (1+u)^ℓ M₀`.
- **Each created corner draws on a non-corner diagonal**: after a 1×1 step the new
  corner is `A^ℓ(1,1) − corr`; after a 2×2 step it is `A^ℓ(2,2) − corr`. That fed
  diagonal is `≤ (1+u)^ℓ M₀`, NOT the (possibly large) old corner ⇒ **no compounding**.
- **The correction is `≤ M₀/α`** with the *fixed* scale:
  - 1×1 (`flSchurCompl_corner_bound` [DONE]): `corr = a₂₁²/a₁₁`; the test `σ|a₁₁| ≥ α a₂₁²`
    gives `corr ≤ σ/α ≤ M₀/α` (here `σ = M₀`). New corner `≤ (1+γ₃)(|A^ℓ(1,1)| + M₀/α)`.
  - 2×2 (`flSchurCompl2_corner_bound` [DONE]): `corr = anext²·(a₁₁/det)`; the test
    `σ|a₁₁| < α a₂₁²` makes the `a₂₁²/det²` factors cancel
    (`tridiag_twoByTwo_corner_correction_le_of_choice`), giving `corr ≤ anext²/(σα) ≤ M₀/α`.
    New corner `≤ (1+γ₃)(|A^ℓ(2,2)| + M₀/α)`.
- Hence every corner `≤ (1+γ₃)((1+u)^ℓ M₀ + M₀/α) ≤ K'·M₀`, and every entry `≤ K'·M₀`,
  with `K' = (1+γ₃)(1.01 + 1/α)` — a **constant** independent of `n`.

**Extra fact [NEW, easy]:** a 2×2 step is taken only when the corner is *small*:
`σ|a₁₁| < α a₂₁²` with `σ=M₀`, `a₂₁ ≤ M₀` ⇒ `|a₁₁| < α a₂₁²/M₀ ≤ α M₀ < M₀`. So a
large (grown) corner always forces a 1×1 step. (Useful for the per-stage `σ` bookkeeping.)

## 3. What already exists (reuse)

- [DONE] Per-step corner bounds: `flSchurCompl_corner_bound`, `flSchurCompl2_corner_bound`
  (`BunchTridiagonalGrowthCh11Closure`). Take `(σ, Amax)` params — instantiate `σ = M₀`.
- [DONE] Off-corner band control + tridiagonal preservation (Lemma T):
  `flSchurCompl(2)_isSymTridiagonal`, `flSchurCompl2_offcorner_bound`, `*_offcorner`.
- [DONE] **The "(F)" product-entry assembly**: `BunchTridiagonalFactorBoundCh11Closure`
  — `corner_quadform_core`, `pivotPath2Abs_corner_le` (the abs pivot-path product is a
  constant multiple of the local scale, via the `a₂₁²/det²` cancellation), and the
  banding-vanishing lemmas `pivotPath2Abs_eq_zero_of_ne_corner` etc.
- [DONE] **Schedule-level assembly**: `hfactor_bound` (`BunchTridiagonalHFactorCh11Closure`)
  turns `TriPivotData fp Amax s A` into `productEntry(L̂,D̂) ≤ hfactorConst·Amax` (= `hfactor`).
- [DONE] The conditional capstone `higham11_7_bunch_tridiagonal_backward_error` consumes `hfactor`.

## 4. The remaining gap and the two candidate routes

The ONLY missing link is a **derivation of the growth invariant** feeding `hfactor`.

### Route A — discharge `TriPivotData fp (K'·M₀) s A` (reuse `hfactor_bound`)
Prove, for the actual fixed-σ=M₀ Bunch run, that `TriPivotData` holds with `Amax = K'·M₀`
and per-stage `σ_ℓ = ‖A^ℓ‖_M`.
- 1×1 stages: `σ_ℓ ≥ M₀` and the 1×1 predicate is monotone up in σ ⇒ transfers. ✓
- **[OPEN] 2×2 stages — the technical crux.** `TriPivotData` needs
  `BunchTridiagonalPivotChoice σ_ℓ a₁₁ a₂₁ two`, i.e. `σ_ℓ|a₁₁| < α a₂₁²`, AND `σ_ℓ ≥ |A²²|`.
  The actual choice was at `M₀`. Because a 2×2 corner is small, `σ_ℓ ≈ (1+u)^ℓ M₀` (max is
  an off-diag/original), but the strict test can fail by the `(1+u)` slack:
  `σ_ℓ|a₁₁| ≤ (1+u)^ℓ M₀|a₁₁| < (1+u)^ℓ α a₂₁²`, which is not `< α a₂₁²`. Borderline 2×2
  choices are the obstruction. Resolving it needs either a margin in the accepted test or a
  decoupling of the test-scale from the entry bound — which `TriPivotData` does NOT provide.

### Route B — bypass `TriPivotData`; derive `hfactor` directly (RECOMMENDED)
Record the run with the **actual fixed-M₀ choices** (`BunchTridiagonalPivotChoice M₀ …` at
every stage — faithful to Alg 11.6). Then:
1. [NEW] Growth invariant by induction on the `PivotSchedule`: all entries of every
   `A^ℓ ≤ K'·M₀`, using the corner bounds at `σ = M₀` (decoupled from the entry bound) +
   off-corner band control. Needs a **decoupled 2×2 corner bound** `flSchurCompl2_corner_bound'`
   with separate scales `σ_test = M₀` (for `hchoice`) and `σ_a22 = (1+u)^ℓ M₀` (for `|A²²|`) —
   a short generalization of the existing proof via a decoupled
   `tridiag_twoByTwo_corner_correction_le_of_choice'`.
2. [NEW] Assemble `productEntry(L̂,D̂) I J ≤ c₀·M₀` from the growth invariant + the DONE
   factor-bound corner/ banding lemmas over the schedule (mirroring `hfactor_bound`'s
   structure but with the fixed-M₀ predicate).
3. [NEW] Feed `hfactor` into `higham11_7_bunch_tridiagonal_backward_error` ⇒ an
   unconditional `higham11_7_bunch_tridiagonal_backward_error_growth_derived`.

Route B avoids the `TriPivotData` scale conflation entirely and is the plan of record.

## 5. Session plan / progress

- **S1 (this session):** confirm model + constant + reusable pieces (done above); create
  module skeleton `BunchTridiagonalGrowthInvariantCh11Closure`; prove foundational lemmas —
  the `K'` constant + positivity, the "2×2 ⇒ small corner" lemma, the decoupled 2×2
  correction/corner bound, and the single-step corner-growth wrappers at `σ = M₀`.
- **S2+:** the schedule induction for the growth invariant (Route B step 1); then the
  product-entry assembly (step 2); then wire the capstone (step 3).

No result is to be faked; every lemma derived from the fl model + Alg 11.6 test, or left
explicitly `[OPEN]` in this blueprint. `TriPivotData` is NOT to be used as an input.
