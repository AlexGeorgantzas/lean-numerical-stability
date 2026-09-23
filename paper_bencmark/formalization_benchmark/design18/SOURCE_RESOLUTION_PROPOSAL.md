# Pilot 18 source-resolution proposal (historical; adopted into Pilot 19)

This was a prospective source-quality decision, **not** a measured result.
Pilot 19 adopted the two recommended source resolutions before any timed
R0/R1 pair existed. The original Pilot-18 draft and incident record remain
in the `codex/pilot-18-probabilistic` branch. The source-resolved manifest is
in `CORPUS_12.json`; see `PILOT19_STATUS.md` for its still-closed admission
gates. No candidate output was used to select these options.

## `HM19-3-4`: retain both conclusions with one disclosed indexing correction

Higham and Mary Theorem 3.4 declares `A : m × n`, `B : n × p`, and states a
per-column representation in (3.11). The displayed range says `j = 1:n`, but
the proof says that (3.12) combines the **p** instances of (3.11), with failure
probability `Q(lambda,m*n*p)`. For arbitrary rectangular `B`, the printed
range cannot describe all and only its columns. The intended range is
`j = 1:p`.

Recommended resolution: keep the full Theorem 3.4 target, including the
per-column backward representation, its `Q(lambda,m*n)` probability, and the
whole-matrix forward bound with `Q(lambda,m*n*p)`; mark `j = 1:p` as a disclosed
editorial correction. Both R0 and R1 receive exactly the same correction in
their common source packet. The candidate-specific auditor sees the original
PDF plus this correction note. It must still reject a candidate that covers
only the forward inequality if the selected task is the full theorem.

Alternative: select (3.12) alone as a separate target. That is mathematically
clean but changes the scope more substantially, so the full-theorem correction
is preferred.

## `CASTRO24-4-1`: replace, do not narrow the source domain

Castro et al. Theorem 4.1 prints `h = floor(log2 n)` in a bound for a
ceiling-split pairwise tree. Some non-power-of-two trees have depth
`ceil(log2 n)`. This observation does not itself prove the printed bound false,
but replacing `floor` by `ceil` or restricting to powers of two would change
the selected source claim. The later author-hosted version retains the same
height wording. Keep this as an unresolved source incident, not a benchmark
failure of either condition.

Recommended prospective replacement: Hallman and Ipsen,
[*Deterministic and Probabilistic Error Bounds for Floating Point Summation
Algorithms*](https://arxiv.org/pdf/2107.01604), Theorem 2.6 (PDF page 6,
printed page 6), provisionally `HI21-2-6`. The source PDF inspected locally has
SHA-256 `cce25923a86d5d2051a079ad4ae7ea965f1dde97ffb6d3bf6462d069968fd1c6`.
The paper explicitly defines a computational-tree height `h` (Definition 2.1)
and states, under independent mean-zero local roundoffs bounded by unit
roundoff, an all-orders high-probability forward-error bound for general
summation. For `delta, eta ∈ (0,1)` and
`lambda = sqrt(2*log(2*n/eta))`, the event has probability at least
`1-(delta+eta)` and bounds the absolute output error by
`u * exp(lambda*sqrt(h)*u) * sqrt(sum of squared exact internal sums)
 * sqrt(2*log(2/delta))`. Its source text also requires exactly represented
floating-point inputs and no overflow/underflow. The general-tree theorem
covers pairwise trees without an off-by-one height convention; a target packet
must preserve the *general* tree domain rather than silently specializing it.

NumStability has `SumTree`, tree evaluation and internal-sum machinery, plus
statistical running-error contribution bounds, but a source-specific
high-probability theorem has not been found. That is promising component
coverage, **not** yet a semantic non-leakage certificate. The replacement
would need a fresh independent source-contract screen and a complete
declaration-collision check before admission.

The source PDF is now retained in `sources/HALLIPS21.pdf` at the hash above.
Direct visual inspection of PDF page 2 (Model 1.1), pages 3–4 (Algorithm 2.1
and tree height), and page 6 (Theorem 2.6) confirms the proposed packet's
independence, domain, coefficient, two failure parameters, and all-orders
claim. A scoped pre-candidate library inspection found the SumTree evaluation,
RMS, and deterministic bounds in `Summation/Tree/Core.lean`, but no
tree-specific high-probability bound there; the probability-bearing algorithm
modules inspected concerned other algorithms. This is evidence of component
support, **not** a complete semantic non-leakage certificate or an independent
source-contract judgment.

Both this packet and the corrected `HM19-3-4` packet passed a proposal-only
controller compilation on Titan in R0 and R1. The check validated retrieved
signature interfaces, OLean closure, and one-`sorry` templates; it created no
candidate, timer, or audit and did not add either proposal to the measured
corpus. Its immutable report is
`/hdd/alexgeorgantzas/highambench/pilot18-compile-preflight-proposals-v1/compile-preflight.json`
(SHA-256 `53f59e0975e11b68d73b7b39cbb8536b8c1d895bd1be592fe16442e1a6f8f160`).
The HI21 route exposed `SumTree` and its statistical RMS bridge in R1,
alongside generic FP/probability components; R0 exposed only Mathlib
probability foundations. Those are static route observations, not evidence
that the theorem is easy or that treatment helps.

The authors' [2024 pairwise BC bound](https://arxiv.org/pdf/2304.05177),
Theorem 3.2, is another plausible replacement. It directly matches the
SumTree/RMS components, but its `log(n)` notation says "smallest integer
greater than log2(n)" while its power-of-two proof uses the exact tree
height. Because avoiding source ambiguity is the reason for replacement,
Theorem 2.6 above is the cleaner first choice.

## Model gate is independent

No source decision permits changing the formalizer from `gpt-6-sol`/`xhigh`.
Titan's ChatGPT-account route rejected the model twice, with zero model
tokens. An API-key route or another formalizer is a separate user choice with
different billing or scientific conditions.
