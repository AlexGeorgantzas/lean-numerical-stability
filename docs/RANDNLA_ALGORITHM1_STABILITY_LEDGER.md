# RandNLA Algorithm 1 Stability Ledger

This ledger tracks the deterministic floating-point stability proof and the
probability-transfer corollary for Drineas--Mahoney Algorithm 1, element-wise
sampling, using

```text
p_ij = A_ij^2 / sum_{k,l} A_kl^2.
```

The Lean development now proves the complete deterministic entrywise
floating-point stability statement for Algorithm 1. It also proves explicit
Markov, pairwise-Chebyshev, and Chernoff-style concentration bounds for the
random counter
`q_ij = hitCount samples i j`: if each sample step hits `(i, j)` with marginal
probability `p_ij`, then

```text
Pr(q_ij <= Q) >= 1 - steps * p_ij / (Q + 1).
```

Specializing `p_ij` to `sqMagProb A i j` gives a high-probability stability
bound with deterministic budget `Q`.

## Target

For a deterministic trace of `s` sampled entries, prove an entrywise forward
error bound between the floating-point sketch and the exact Algorithm 1 sketch.
For each entry `(i, j)`, the exact increment simplifies to

```text
||A||_F^2 / (s * A_ij)
```

whenever `A_ij != 0`. If `(i, j)` is hit `q_ij` times, the desired bound should
reduce to the accumulated scalar theorem already proved for `q_ij` repeated
updates.

## Completed

| Status | Item | Lean artifacts |
|---|---|---|
| Done | Rectangular Frobenius squared norm | `frobNormSqRect`, `frobNormSqRect_nonneg`, `frobNormSqRect_eq_zero_iff`, `frobNormSqRect_ne_zero_of_entry_ne_zero` |
| Done | Squared-magnitude probability weights | `sqMagProb`, `sqMagProb_sum_eq_one`, `sqMagProb_ne_zero_of_entry_ne_zero` |
| Done | Exact sampled-entry simplification | `elementwiseIncrement_sqMag_eq` |
| Done | One-sample exact and FP updates | `elementwiseSampleUpdate`, `fl_elementwiseSampleUpdate` |
| Done | Local FP kernel bound | `fl_add_div_update_error_bound` |
| Done | One-sample Algorithm 1 stability | `fl_elementwiseUpdateEntry_error_bound`, `fl_elementwiseUpdateEntry_sqMag_error_bound` |
| Done | Deterministic trace vocabulary | `ElementwiseSample`, `ElementwiseTrace`, `sampleHits`, `elementwiseTraceSketch`, `fl_elementwiseTraceSketch` |
| Done | Hit counts for a trace entry | `hitCount`, `hitCount_succ_last_of_hit`, `hitCount_succ_last_of_not_hit` |
| Done | Exact trace reduction | `elementwiseTraceSketch_eq_repeat_of_hitCount` |
| Done | FP trace reduction | `fl_elementwiseTraceSketch_eq_repeat_of_hitCount` |
| Done | Accumulated repeated-hit scalar bound | `fl_repeatElementwiseUpdateEntry_error_bound`, `fl_repeatElementwiseUpdateEntry_sqMag_error_bound` |
| Done | General deterministic trace stability | `fl_elementwiseTraceSketch_error_bound` |
| Done | Squared-magnitude exact trace formula | `elementwiseTraceSketch_sqMag_eq` |
| Done | Complete squared-magnitude entrywise bound | `fl_elementwiseTraceSketch_sqMag_error_bound`, `fl_elementwiseTraceSketch_sqMag_error_bound_exact` |
| Done | Zero-initial-sketch Algorithm 1 corollary | `fl_elementwiseSketch_zero_init_sqMag_error_bound` |
| Done | Entrywise packaged theorem | `fl_elementwiseTraceSketch_entrywise_sqMag_error_bound` |
| Done | Deterministic budget with count upper bound | `sqMagTraceErrorBudget`, `sqMagTraceErrorBudget_mono`, `fl_elementwiseTraceSketch_sqMag_error_bound_of_hitCount_le` |
| Done | Random-trace event vocabulary | `hitCountAtMostEvent`, `sqMagTraceStabilityEvent` |
| Done | High-probability transfer corollary | `hitCountAtMostEvent_subset_sqMagTraceStabilityEvent`, `probability_sqMagTraceStability_of_hitCount_concentration`, `highProbability_sqMagTraceStability_of_hitCount_concentration` |
| Done | Finite-probability model | `FiniteProbability`, `FiniteProbability.eventProb`, `FiniteProbability.expectationNat`, `FiniteProbability.expectationReal` |
| Done | Markov inequality for natural counters | `FiniteProbability.eventProb_nat_ge_le_expectationNat_div`, `FiniteProbability.eventProb_nat_le_ge_one_sub_expectationNat_div_succ` |
| Done | Chebyshev from finite Markov | `FiniteProbability.eventProb_abs_sub_gt_le_expectationReal_sq_div`, `FiniteProbability.eventProb_abs_sub_le_ge_one_sub_of_second_moment` |
| Done | Chernoff from finite exponential Markov | `FiniteProbability.eventProb_nat_ge_le_exp_mul_mgf`, `FiniteProbability.eventProb_nat_ge_le_chernoff_of_mgf_bound`, `FiniteProbability.eventProb_nat_le_ge_one_sub_chernoff_of_mgf_bound` |
| Done | Hit-count expectation from step marginals | `hitCount_eq_sum_indicator`, `expectationNat_hitCount_eq_sum_step_hit_probs`, `expectationNat_hitCount_eq_steps_mul_hitProb` |
| Done | Proved upper-tail concentration for `hitCount` | `hitCount_concentration_markov_of_marginal_hitProb`, `hitCount_concentrates_of_marginal_hitProb`, `hitCount_concentration_sqMag_markov`, `hitCount_concentrates_sqMag` |
| Done | Proved around-mean concentration for `hitCount` under pairwise independent hits | `expectationReal_hitCount_centered_sq_eq_pairwise`, `hitCountDeviationEvent`, `hitCount_concentrates_around_mean_pairwise`, `hitCount_concentrates_sqMag_around_mean_pairwise` |
| Done | Canonical independent squared-magnitude trace distribution | `sampleHitIndicator`, `sqMagTraceProbMass`, `sqMagTraceProbability`, `sqMagProb_sum_samples_eq_one`, `sqMagTraceProbMass_sum_eq_one` |
| Done | Chernoff MGF bound proved from the product trace law | `sqMag_sampleHitIndicator_exp_sum`, `exp_hitCount_eq_prod_sampleHitIndicator`, `sqMagTraceProbability_expectationReal_exp_hitCount_eq`, `sqMagTraceProbability_chernoff_mgf_bound` |
| Done | Chernoff concentration for `hitCount`, both generic and canonical-product forms | `hitCountChernoffMGFBound`, `sqMagHitCountChernoffMGFBound`, `chernoffHitCountTail`, `hitCount_concentrates_sqMag_chernoff_of_mgf_bound`, `hitCount_concentrates_sqMag_chernoff_independent`, `hitCount_concentrates_sqMag_chernoff_optimized_independent` |
| Done | Stability with proved concentration location | `highProbability_sqMagTraceStability_of_marginal_hitProb`, `highProbability_sqMagTraceStability_of_marginal_hitProb_of_tail_budget` |
| Done | Stability from around-mean pairwise concentration | `probability_sqMagTraceStability_of_hitCount_deviation`, `highProbability_sqMagTraceStability_of_pairwise_hitCount_deviation` |
| Done | Chosen Markov budget in stability event | `markovHitCountBudget`, `sqMagMarkovHitCountBudget`, `highProbability_sqMagTraceStability_of_markov_budget` |
| Done | Chosen Chebyshev budget in stability event | `hitCountPairwiseCenteredMoment`, `chebyshevHitCountRadius`, `chebyshevHitCountBudget`, `sqMagChebyshevHitCountBudget`, `highProbability_sqMagTraceStability_of_pairwise_chebyshev_budget` |
| Done | Chosen Chernoff budget and optimized Chernoff stability event | `chernoffHitCountBudget`, `sqMagChernoffHitCountBudget`, `chernoffOptimizedHitCountTail`, `sqMagChernoffOptimizedHitCountTail`, `highProbability_sqMagTraceStability_of_independent_chernoff_budget`, `highProbability_sqMagTraceStability_of_independent_chernoff_optimized_tail_budget` |
| Done | Nonzero sampled-entry trace predicate | `TraceValidForSqMag`, `TraceValidForSqMag.entry_ne_zero_of_hit` |
| Done | Trace all-hit bridge | `elementwiseTraceSketch_all_hit_eq_repeat`, `fl_elementwiseTraceSketch_all_hit_eq_repeat`, `fl_elementwiseTraceSketch_all_hit_sqMag_error_bound` |

## Optional Follow-Up Work

| Priority | Item | Why it matters | Suggested Lean artifacts |
|---|---|---|---|
| P2 | Optional normwise consequence | Converts entrywise bounds into Frobenius or max-entry bounds. | Frobenius/max-entry lemmas over `fl - exact` |
| P3 | Optional spectral/normwise RandNLA theorem | Converts entrywise FP stability plus sampling concentration into matrix-level claims. | Sampling law, expectation/unbiasedness, matrix concentration |

## Proposed Main Theorem Shape

The main deterministic theorem is:

```lean
theorem fl_elementwiseTraceSketch_sqMag_error_bound
    (fp : FPModel) {m n steps : ℕ} (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps)
    (i : Fin m) (j : Fin n)
    (hs : (s : ℝ) ≠ 0)
    (hAij : A i j ≠ 0)
    (hsteps : gammaValid fp (hitCount samples i j))
    (hsteps1 : gammaValid fp (hitCount samples i j + 1)) :
    |fl_elementwiseTraceSketch fp s A Atilde samples i j
      - (Atilde i j + (hitCount samples i j : ℝ)
          * (frobNormSqRect A / ((s : ℝ) * A i j)))|
      ≤ |Atilde i j| * gamma fp (hitCount samples i j)
        + (hitCount samples i j : ℝ)
          * |frobNormSqRect A / ((s : ℝ) * A i j)|
          * gamma fp (hitCount samples i j + 1)
```

For the exact Algorithm 1 sample count, one may set `steps = s`, but keeping
them separate is useful: `s` is the scaling parameter in the update, while
`steps` is the length of a deterministic trace.

The high-probability transfer theorem is:

```lean
theorem highProbability_sqMagTraceStability_of_hitCount_concentration
    (fp : FPModel) {Ω : Type*} {m n steps : ℕ}
    (Pr : Set Ω → ℝ) (δ : ℝ) (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (Q : ℕ) (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0)
    (hQ : gammaValid fp Q) (hQ1 : gammaValid fp (Q + 1))
    (hPr_mono : ∀ {E F : Set Ω}, E ⊆ F → Pr E ≤ Pr F)
    (hprob : 1 - δ ≤ Pr (hitCountAtMostEvent X i j Q)) :
    1 - δ ≤ Pr (sqMagTraceStabilityEvent fp s A Atilde X i j Q)
```

This statement formalizes the user's observation: after all deterministic data
are fixed, the only random quantity in the stability budget is the counter
`q_ij`. The theorem replaces that counter in the error budget by any
deterministic concentration upper bound `Q`. The exact trace formula remains
centered at the actual `q_ij`; replacing the center by `Q` would add a separate
sampling error term.

The proved Markov concentration theorem is:

```lean
theorem hitCount_concentrates_sqMag
    {Ω : Type*} [Fintype Ω] {m n steps : ℕ}
    (P : FiniteProbability Ω) (A : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (δ : ℝ) (Q : ℕ)
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = sqMagProb A i j)
    (hQ : (steps : ℝ) * sqMagProb A i j / ((Q + 1 : ℕ) : ℝ) ≤ δ) :
    1 - δ ≤ P.eventProb (hitCountAtMostEvent X i j Q)
```

This gives an upper-tail location for the counter using only one-step
marginals:

```text
Pr(q_ij <= Q) >= 1 - steps * p_ij / (Q + 1).
```

The library now chooses the Markov budget directly:

```text
Q_M = ceil(steps * p_ij / δ).
```

The resulting stability corollary is:

```lean
theorem highProbability_sqMagTraceStability_of_markov_budget
    ...
    1 - δ ≤
      P.eventProb
        (sqMagTraceStabilityEvent fp s A Atilde X i j
          (sqMagMarkovHitCountBudget steps A i j δ))
```

The proved around-mean concentration theorem is:

```lean
theorem hitCount_concentrates_sqMag_around_mean_pairwise
    {Ω : Type*} [Fintype Ω] {m n steps : ℕ}
    (P : FiniteProbability Ω) (A : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (ε δ : ℝ) (hε : 0 < ε)
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = sqMagProb A i j)
    (hpairwise : ∀ t u : Fin steps, t ≠ u →
      P.eventProb
        {ω | sampleHits (X ω) t i j ∧ sampleHits (X ω) u i j} =
          sqMagProb A i j * sqMagProb A i j)
    (htail : ... / ε ^ 2 ≤ δ) :
    1 - δ ≤
      P.eventProb
        (hitCountDeviationEvent X i j
          ((steps : ℝ) * sqMagProb A i j) ε)
```

This theorem says `q_ij` lies within `ε` of
`steps * p_ij = steps * sqMagProb A i j` with probability at least `1 - δ`,
provided the distinct step-hit indicators are pairwise independent. The proved
second-moment identity behind it is
`expectationReal_hitCount_centered_sq_eq_pairwise`.

The corresponding stability theorem with the proved concentration location is:

```lean
theorem highProbability_sqMagTraceStability_of_marginal_hitProb_of_tail_budget
    ...
    (hQtail :
      (steps : ℝ) * sqMagProb A i j / ((Q + 1 : ℕ) : ℝ) ≤ δ) :
    1 - δ ≤
      P.eventProb (sqMagTraceStabilityEvent fp s A Atilde X i j Q)
```

There is also a pairwise-Chebyshev stability theorem:

```lean
theorem highProbability_sqMagTraceStability_of_pairwise_hitCount_deviation
    ...
    (hQreal : (steps : ℝ) * sqMagProb A i j + ε ≤ (Q : ℝ))
    ...
    (htail : ... / ε ^ 2 ≤ δ) :
    1 - δ ≤
      P.eventProb (sqMagTraceStabilityEvent fp s A Atilde X i j Q)
```

Here the deterministic stability budget uses any natural `Q` above the
high-probability location `steps * p_ij + ε`.

The library also chooses a conservative Chebyshev radius and budget directly:

```text
M = E[(q_ij - steps * p_ij)^2]
ε_C = M / δ + 1
Q_C = ceil(steps * p_ij + ε_C).
```

The `+1` avoids a square-root dependency and makes the radius strictly
positive. Lean proves `M / ε_C^2 <= δ`, so the chosen-budget stability corollary
is:

```lean
theorem highProbability_sqMagTraceStability_of_pairwise_chebyshev_budget
    ...
    1 - δ ≤
      P.eventProb
        (sqMagTraceStabilityEvent fp s A Atilde X i j
          (sqMagChebyshevHitCountBudget steps A i j δ))
```

The Chernoff route now has two layers. The generic concentration theorem still
accepts the standard exponential-moment condition for a Bernoulli hit-count sum:

```lean
def sqMagHitCountChernoffMGFBound ...
```

Mathematically, this says that for every `lam > 0`,

```text
E[exp(lam * q_ij)] <= exp(steps * p_ij * (exp(lam) - 1)).
```

For the canonical Algorithm 1 sampler, this condition is no longer an external
hypothesis. Lean defines the finite product trace law

```lean
sqMagTraceProbability (steps := steps) A hden
```

and proves the exact identity

```text
E[exp(lam * q_ij)]
  = (1 + p_ij * (exp(lam) - 1)) ^ steps
  <= exp(steps * p_ij * (exp(lam) - 1)).
```

The key artifacts are
`sqMagTraceProbability_expectationReal_exp_hitCount_eq` and
`sqMagTraceProbability_chernoff_mgf_bound`.

From the MGF bound, Lean proves the Chernoff tail

```text
Pr(q_ij <= Q)
  >= 1 - exp(steps * p_ij * (exp(lam) - 1) - lam * (Q + 1)).
```

The explicit fixed-parameter budget is:

```text
Q_Ch(lam) =
  ceil((steps * p_ij * (exp(lam) - 1) - log(δ)) / lam).
```

The corresponding chosen-budget stability corollary is:

```lean
theorem highProbability_sqMagTraceStability_of_independent_chernoff_budget
    ...
    1 - δ ≤
      (sqMagTraceProbability (steps := steps) A hden).eventProb
        (sqMagTraceStabilityEvent fp s A Atilde (fun samples => samples) i j
          (sqMagChernoffHitCountBudget steps A i j lam δ))
```

Lean also formalizes the optimized Chernoff exponent for a supplied natural
budget `Q`, choosing

```text
lam = log((Q + 1) / (steps * p_ij)).
```

The optimized stability theorem is:

```lean
theorem highProbability_sqMagTraceStability_of_independent_chernoff_optimized_tail_budget
    ...
    (htail : sqMagChernoffOptimizedHitCountTail steps A i j Q ≤ δ) :
    1 - δ ≤
      (sqMagTraceProbability (steps := steps) A hden).eventProb
        (sqMagTraceStabilityEvent fp s A Atilde (fun samples => samples) i j Q)
```

## Proof Design Used

The completed proof uses direct trace-fold bookkeeping rather than an explicit
filtered subtrace.

| Approach | Pros | Cons |
|---|---|---|
| Direct induction over trace steps | Avoids constructing a subtrace; proves exact and FP reductions to `hitCount`. | Requires two small `hitCount_succ_last` recurrence lemmas. |
| Filtered subtrace | Still possible as an alternative view. | Not needed for the completed proof. |

The final proof still keeps the floating-point accumulation concentrated in
`fl_repeatElementwiseUpdateEntry_error_bound`; the trace lemmas only prove that
the arbitrary trace reduces to that repeated-hit scalar computation.

## Verification Checklist

Before calling the deterministic stability proof complete:

- `lake build` succeeds.
- `lake env lean examples/LibraryLookup.lean` succeeds.
- Search confirms no new `sorry`, `admit`, top-level `axiom`, or `unsafe`.
- The final theorem is exported through `LeanFpAnalysis.FP`.
- The lookup docs list the theorem and its dependencies.
- The statement clearly separates deterministic stability, Markov hit-count
  concentration from marginals, pairwise-Chebyshev concentration, generic
  Chernoff concentration from an exponential-moment condition, and the
  canonical product-law theorem that proves that condition.
- The probability-transfer and proved concentration corollaries are listed and
  checked.

## Current Status

The deterministic entrywise floating-point stability proof for Algorithm 1 is
complete. The library proves Markov, pairwise-Chebyshev, and Chernoff-style
concentration theorems for the random hit counter, constructs the canonical
independent squared-magnitude trace distribution, derives the Chernoff MGF
bound from that product law, chooses concrete natural budgets for Markov,
Chebyshev, and fixed-parameter Chernoff, and composes those budgets with the
stability theorem. Matrix-level normwise/random-matrix infrastructure is the
next larger mathematical layer.
