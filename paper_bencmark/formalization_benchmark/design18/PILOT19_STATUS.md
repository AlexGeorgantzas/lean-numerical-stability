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
a treatment benefit. The new corpus/packet hashes require a fresh full-corpus
route and compile preflight before admission.

## Gates still closed

1. The corpus has status
   `SOURCE_RESOLVED_MODEL_AND_LEAKAGE_GATE_PENDING_NOT_RUN`. Both the campaign
   and direct matched-pair entry points reject any status other than
   `ADMITTED_FOR_MEASUREMENT` **before** creating an output directory or
   calling a model. A task-neutral semantic leakage review of the frozen
   library is still needed; existing lexical/scoped screens are not a
   certificate against a disguised target result.
2. Titan's ChatGPT-account Codex login rejected `gpt-6-sol`/`xhigh` twice
   with HTTP 400 and zero model tokens. No API credential is configured.
   Switching to API billing or a different formalizer is a user decision,
   never an automatic fallback.
3. Once the two gates clear, run a successful provider qualification and
   one-time R1 warm root before any timed pair. The frozen early-review order
   remains `HM19-3-2`, `HALL21-3-3`, `CASTRO24-4-2`; inspect each early pair
   before proceeding through the other nine.
