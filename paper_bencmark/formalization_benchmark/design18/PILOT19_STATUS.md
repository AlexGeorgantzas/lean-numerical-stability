# Pilot 19 source-resolved release — admitted; no measured task yet

Pilot 19 is a separate, prospective release of the Design-18 benchmark
architecture. It is **admitted for measurement**. The previous Pilot-18
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

## Admission record

1. The corpus has status `ADMITTED_FOR_MEASUREMENT`. Both the campaign and
   direct matched-pair entry points reject any other status **before** creating
   an output directory or calling a model. `PILOT19_LEAKAGE_SCREEN.md` records a bounded
   pre-candidate content review that found components but no selected result.
   It is an expert negative search, not a mathematical certificate against
   every disguised declaration; discovered leakage remains an incident.
2. The original Titan Codex CLI 0.154.0 deployment rejected
   `gpt-6-sol`/`xhigh` through ChatGPT sign-in three times with HTTP 400 and
   zero model tokens. The final original-deployment incident is retained at
   `/hdd/alexgeorgantzas/highambench/pilot19-model-gate-v1/qualification.json`
   (SHA-256 `36f673d66264474eaaa6bc9f2de05886b84cf72c13505df324ce9642d1eb6ce2`).
   This did **not** establish that an API key was necessary. An isolated Titan
   installation of official Codex CLI 0.156.0, using the same ChatGPT-account
   credential, successfully returned an off-benchmark `gpt-6-sol`/`xhigh`
   response with usage. The pinned benchmark driver's full tool/usage
   qualification then **passed** using a new deployment record that changes
   only the Codex executable and Code Mode host identities. Its immutable
   record is `/hdd/alexgeorgantzas/highambench/pilot19-qualify-cli0156/qualification.json`
   (SHA-256 `37c17bcf2a5918ae289d216aacf29d4f5b612c3440aa5a4f4613d41f1deca69a`;
   19,632 input tokens, 188 output tokens, 8.17 active seconds). No API
   credential or contestant work was involved. The differing client versions
   are the leading explanation for the earlier rejection, not proof of its
   precise server-side cause.
3. The one-time R1 orientation fork is **READY** at
   `/hdd/alexgeorgantzas/highambench/pilot19-warm-root-cli0156/warm-root.json`
   (SHA-256 `e30fa338dd2b0a63cf43f47e3474478506a40a4d72c55e9dc2ae9eda6147cc8c`).
   It used 173.02 seconds, 1,449,470 input tokens (1,335,680 cached), and
   7,319 output tokens, all excluded from per-task contestant-active metrics.
   Its input contained no task list, source paper, or candidate. An isolated
   ChatGPT-signed-in `gpt-6-astra`/`high` availability probe also succeeded
   on Titan before measurement. The frozen early-review order is `HM19-3-2`, `HALL21-3-3`,
   `CASTRO24-4-2`; inspect each early pair before proceeding through the other
   nine.
