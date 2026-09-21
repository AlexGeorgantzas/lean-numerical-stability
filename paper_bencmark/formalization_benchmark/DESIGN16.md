# Design 16: bounded composition packets

Status: engineering design, not a frozen scientific pilot.

## Why Pilot 15 failed

The first three completed development pairs have three different failure modes.

| Task | L/N active time | L/N net-new tokens | Diagnosis |
|---|---:|---:|---|
| H5-5 | 0.75 | 1.42 | Useful root-product results exist, but discovery and the `gamma (2*n)` to `gamma (2*n+1)` bridge consumed the token saving. |
| H7-12 | 1.18 | 1.45 | No matching symmetric linear-system backward-error result exists in the frozen library; search was pure overhead. |
| H10-7 | 2.83 | 3.48 | A useful tail-bound theorem exists, but nearby source labels led to a semantically wrong first statement and an expensive repair. |

The median is 1.18 times N in time and 1.45 times N in tokens. Reaching the old
0.80 gate would require roughly 32% less time and 45% fewer tokens than the
current median L behavior. A warmer prompt cannot plausibly supply that entire
reduction while full source and atlas search remain available.

Pilot 15 remains immutable and is reported as the **cold/unbounded-adaptation**
result. H5-5, H7-12, and H10-7 are consumed development cases from now on.

## New estimand

The primary successor comparison is a matched retrieval system over different
corpora:

- **R0:** Mathlib corpus.
- **R1:** the same Mathlib corpus plus the frozen NumStability snapshot.

Both sides receive the same deterministic query generator, ranker, route
threshold, packet format, byte limit, fresh stateless formalizer, prompt,
hardware, time limit, and audit. The only treatment difference is whether
NumStability declarations and OLean files are present. This estimates the
marginal value of adding NumStability to an otherwise identical agent-facing
formalization system.

Task-specific retrieval is counted as part of the system. Primary active time is
retrieval plus formalizer active time. Formalizer-only time is a secondary
mechanism measure. One-time corpus indexing/build cost is reported separately,
with an amortized sensitivity calculation.

## Treatment architecture

Before the charged formalizer turn, a deterministic controller reads only the
semantic fields already supplied to the contestant:

- `selected_result`;
- `task_clarification`;
- `scope_constraints`;
- any frozen `faithfulness_contract` added by independent source extraction.

It never ranks on task ID, paper filename, page number, bibliography, PDF hash,
chapter/problem number, or a human declaration mapping. It emits a protected
`LIBRARY_API.md` capped at 48 KiB. Each exposed card contains:

- exact narrow import and full signature;
- at most five signature dependencies or conventionally named bridge lemmas;
- matched semantic concepts;
- source locator for provenance;
- conservative contract-surface warnings.

The measured formalizer receives compiled OLean files but no source tree, atlas,
query script, warm conversation, or search fallback. If the automatic router
returns `NO_ROUTE`, the packet exposes no misleading declarations and instructs
the model to work locally. Otherwise the model tries the first route and at most
one fallback before working locally.

This replaces a 4.58-million-token inherited scout context, a roughly 39 MiB
interactive index, unrestricted repeated queries, and full source browsing with
one 1–48 KiB authenticated packet and a fresh conversation.

## Development gate

Development uses consumed tasks only and produces no scientific observations.

1. **Provider-free retrieval gate**
   - H5-5 must expose the root-product forward-error theorem and gamma
     monotonicity bridges.
   - H10-7 must expose `psd_pivoted_cholesky_exists_tail` before misleading
     nearby declarations.
   - H7-12 must return `NO_ROUTE`.
   - Every packet must be deterministic and under 48 KiB.
2. **Two L-only paid smokes**
   - fresh conversation;
   - one submission;
   - 45-minute ceiling;
   - compilation/integrity validation;
   - a cheap fresh condition-blind faithfulness screen;
   - no full multi-agent audit.
3. **Advance rule**
   - both candidates compile;
   - both visibly use a retrieved NumStability route;
   - neither has a substantive source mismatch;
   - each improves either time or net-new tokens by at least 20% relative to its
     sealed Pilot-15 L result, without worsening the other by more than 10%.

One ranker/packet revision is allowed after these smokes. If the second design
fails, the end-to-end paper-formalization experiment stops and the thesis pivots
to a common-statement proof-completion experiment. That fallback gives both
conditions the same independently audited Lean statement and measures only the
proof-engineering value of NumStability.

## Official successor gate

Only after the development gate passes:

1. Freeze the ranker, corpus hashes, limits, tie-breaking, prompt, and source
   contracts.
2. Select untouched tasks by an outcome-blind coverage rule: useful building
   blocks may exist, but the target result itself must not already be present.
3. Counterbalance R0/R1 order and use fresh conversations in both conditions.
4. Run three pairs first. Stop for redesign if fewer than two R1 candidates
   compile/use NumStability, or if R1 wins neither time nor tokens in at least
   two of three pairs.
5. Run the full paper-derived faithfulness audit only after compilation and a
   cheap blind screen pass. Scientific inclusion still requires the complete
   audit.

Timed contestants do not run concurrently on the same eight-core Titan host.
Corpus indexing, packet generation, compilation, dossier extraction, and
independent audit roles can run in parallel when they do not contend with a
timed contestant or shared provider limit.

## Current provider-free result

The first bounded implementation passes its intended three-case regression:

- H5-5: `DIRECT_OR_COMPOSITION`, 10,325-byte packet; the first two routes are
  the root-product forward-error theorems, with `gammaValid_mono`, `gamma_mono`,
  and `gamma_nonneg` included as bridges.
- H10-7: `DIRECT_OR_COMPOSITION`, 11,269-byte packet;
  `NumStability.psd_pivoted_cholesky_exists_tail` is ranked first.
- H7-12: `NO_ROUTE`, 1,089-byte packet; no distracting cards are exposed.

These are engineering checks, not benchmark results. The next permitted cost is
two bounded L-only development smokes, not another complete N/L task campaign.
