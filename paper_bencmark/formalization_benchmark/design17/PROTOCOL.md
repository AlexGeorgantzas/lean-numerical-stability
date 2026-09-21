# Design-17 statement-only matched benchmark

Status: `UNSCORED_ENGINEERING_EXPLORATORY` until frozen on untouched tasks.

## Scientific object

The measured object is the faithful Lean statement, not its proof. Each
candidate must contain exactly one final theorem named
`HighamBenchCandidate.target`. Its entire proof is exactly one `sorry`. No
other `sorry`, `admit`, axiom, constant, opaque declaration, unsafe escape,
metaprogramming, or checker bypass is permitted.

Definitions and hypotheses needed to express the source result must be genuine.
The contestant may not move the desired conclusion into a structure field or
assumption merely to make the target tautological. Faithfulness, full-domain
coverage, and nonvacuity are decided by the independent semantic audit.

## Matched conditions

- R0 receives Lean, Mathlib, and a bounded deterministic packet retrieved from
  the frozen Mathlib declaration atlas.
- R1 receives the identical prompt, task packet, PDF, retriever, ranking rule,
  packet limits, and formalizer model, but retrieval ranges over the union of
  Mathlib and the frozen NumStability atlas and the NumStability OLean tree is
  mounted.
- The contestant does not browse either library or run an open-ended search.
  `LIBRARY_API.md` is the complete retrieval interface.
- Each condition uses a fresh stateless `gpt-5.6-sol` xhigh conversation.
- Conditions run sequentially in the predeclared counterbalanced order.

The treatment is therefore access to reusable NumStability declarations under
a matched retrieval budget, rather than prior knowledge of an undocumented
library or time spent learning its directory structure.

## Measurement

Primary system time is deterministic packet retrieval plus the formalizer turn
through candidate freeze. Net-new tokens are uncached input plus output. Raw
provider usage remains recorded. Compilation, integrity validation, dossier
construction, and faithfulness auditing are timed and logged separately but do
not enter contestant metrics.

Every condition runs inside the authenticated Titan envelope:

- CPUs 0--7 only;
- 32 GiB outer memory limit, no swap, and 512 tasks;
- 24 GiB generated-command sub-cgroup, no swap, and 384 tasks; and
- resource-limit events and a fresh hardware snapshot recorded for each
  condition.

## Semantic gate

Candidates compile with the one explicitly permitted target `sorry`, then enter
the canonical condition-blind audit:

1. pseudonymized recursive semantic dossier;
2. fresh blind-translation agent with one record for every dependency;
3. fresh direct judge with the full 16-item checklist;
4. fresh round-trip judge with the full 16-item checklist;
5. explicit candidate-implies-source and source-implies-candidate judgments;
6. fresh adjudication whenever the frozen triggers fire; and
7. final binary verdict `faithful` or `unfaithful`.

Proper-subdomain and partial case-split coverage fail. A genuinely stronger
full-domain proposition may pass. Auditor time and tokens are reported but
excluded from benchmark measurements.

## Development policy

Consumed tasks may be used to engineer this protocol, but their observations
remain development evidence. The initial diagnostic wave is H5-5 and H10-7
(building-block treatment routes) plus H7-12 (negative control). The five tasks
identified as direct-result collisions or router errors are never pooled with
the primary engineering stratum. No task is rerun silently and every incident
is retained in the hash-chained campaign journal.
