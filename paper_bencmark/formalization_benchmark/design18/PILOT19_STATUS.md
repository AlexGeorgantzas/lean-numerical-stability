# Pilot 19 source-resolved prerelease — no measured task yet

Pilot 19 is a separate, prospective release of the Design-18 benchmark
architecture. It is **not admitted for measurement**. The previous Pilot-18
draft, its source incidents, and all off-benchmark reports remain in the
`codex/pilot-18-probabilistic` branch through commit `d73bbff01`. Neither
pilot has generated a timed R0/R1 task pair. Do not pool either with Design 17.

## Source decisions made before seeing any candidate

- `HM19-3-4` retains both the per-column backward and whole-matrix forward
  conclusions, their separate probability bounds, the rectangular domain,
  and the six legal matrix-product orderings. The common packet discloses the
  paper's printed `j=1:n` indexing error and uses `j=1:p`, as required by
  `B : n × p` and the proof's explicit combination of `p` instances. Both
  conditions and the candidate-specific auditors receive the same note.
- The source-uncertain `CASTRO24-4-1` is prospectively replaced by
  `HI21-2-6`, Hallman–Ipsen Theorem 2.6, before any measured result. The
  selected target covers **arbitrary general summation trees**, not just
  pairwise trees, under the paper's independent mean-zero bounded-roundoff
  model. Both failure parameters, exact all-orders coefficient, and source
  height definition are retained. The original Castro packet is preserved
  in `proposals/CASTRO24-4-1-superseded.json`.

The two adopted packets were previously tested without a formalizer in
`pilot18-compile-preflight-proposals-v1`; both conditions compiled their
signature interfaces, OLean closure, and one-`sorry` controller templates.
The immutable report SHA-256 is
`53f59e0975e11b68d73b7b39cbb8536b8c1d895bd1be592fe16442e1a6f8f160`.
This is an infrastructure result, not evidence of contestant faithfulness or
a treatment benefit. The new corpus passed a full twelve-task Titan routing
preflight with exact prompt-prefix identity and no R0 treatment exposure.
Under the fixed Titan envelope, the two changed packets passed a new
corpus-mode static compile preflight in R0 and R1. Its immutable report is
`/hdd/alexgeorgantzas/highambench/pilot19-compile-preflight-source-resolved-v1/compile-preflight.json`
(SHA-256 `2f962fcff4f0655abbeec2700a6d6946011a9b1d4215d3406fe1314eaf48fe58`).
The other ten packet files and the router/compiler code are byte-identical
to the Pilot-18 prerelease that already passed static compilation; only the
manifest and two selected packet files changed. No candidate or audit ran.

## Gates still closed

1. The corpus has status
   `SOURCE_AND_LEAKAGE_REVIEWED_MODEL_GATE_PENDING_NOT_RUN`. Both the campaign
   and direct matched-pair entry points reject any status other than
   `ADMITTED_FOR_MEASUREMENT` **before** creating an output directory or
   calling a model. `PILOT19_LEAKAGE_SCREEN.md` records a bounded
   pre-candidate content review that found components but no selected result.
   It is an expert negative search, not a mathematical certificate against
   every disguised declaration; discovered leakage remains an incident.
2. Titan's ChatGPT-account Codex login rejected `gpt-6-sol`/`xhigh` twice
   with HTTP 400 and zero model tokens. No API credential is configured.
   Switching to API billing or a different formalizer is a user decision,
   never an automatic fallback.
   A third off-benchmark, one-shot qualification used the **exact**
   Design-17-v3 deployment that the Pilot-19 compiler uses. It again returned
   HTTP 400, “The 'gpt-6-sol' model is not supported when using Codex with a
   ChatGPT account,” in 3.02 seconds with zero tokens and no contestant work.
   Its immutable record is
   `/hdd/alexgeorgantzas/highambench/pilot19-model-gate-v1/qualification.json`
   (SHA-256 `36f673d66264474eaaa6bc9f2de05886b84cf72c13505df324ce9642d1eb6ce2`).
3. Once the model gate clears, run a successful provider qualification and
   one-time R1 warm root before any timed pair. The frozen early-review order
   remains `HM19-3-2`, `HALL21-3-3`, `CASTRO24-4-2`; inspect each early pair
   before proceeding through the other nine.
