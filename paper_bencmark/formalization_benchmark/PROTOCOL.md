# Source-first formalization protocol

## Purpose

This pilot measures whether access to, and explicit encouragement to use, a
frozen NumStability library helps Codex construct a faithful Lean formalization
of a paper result. It does not measure proof construction.

## Frozen pilot

- Tasks: P01-T2, P02-T2, P03-T2, P13-T2, and P14-T2.
- Replication count: one N/L pair per task.
- Formalizer model and reasoning effort are frozen in `config.json`.
- Maximum submissions per condition: four (initial plus three repairs).
- Cumulative contestant-active limit per condition: 18,000 seconds.
- Benchmark token cap: none. Provider usage is still measured at every turn.
- Hardware envelope: the complete condition process tree runs in an outer
  cgroup restricted to exactly eight logical CPUs, 32 GiB RAM, 512 tasks, and
  no swap. Model-generated command trees enter a delegated child cgroup capped
  at 24 GiB RAM, 384 tasks, and no swap; the trusted control child has an 8 GiB
  `memory.low` reservation. Setup freezes the Titan host identity, CPU model,
  and exact eight-CPU set; the controller verifies that identity at admission
  and at both ends of every attempt.
- Pair concurrency: one measured N/L pair at a time on Titan, enforced by a
  deployment-wide nonblocking lock so pilot runs cannot contend with each other.

The existing 51 accepted HighamBench tasks establish only that the selected
paper results can be formalized faithfully. They do not pre-approve any
candidate generated in this pilot.

## Conditions

Both conditions receive the identical hash-verified PDF, task packet, Lean
toolchain, Mathlib snapshot, and common prompt.

Condition N has no NumStability source, compiled objects, documentation,
declaration names, search index, cache, Git history, old benchmark target, or
prior condition output.

Condition L receives the same environment plus a read-only NumStability
snapshot at commit `45813a95dacf577461bae13f033af0dbc985a225`. Its prompt is
the byte-identical common prompt followed by the frozen L-only appendix. That
appendix explicitly encourages the formalizer to inspect, import, reuse, adapt,
or draw inspiration from related library material. It identifies the source
tree `/library/NumStability`, the root module
`/library/NumStability.lean`, and compiled declarations on `LEAN_PATH`; it also
provides concrete `find`, `rg`, and `import NumStability` guidance. This combined
access and encouragement is the intended treatment.

## Candidate contract

The candidate is a single `Candidate.lean` file. Its audited root must be the
unique declaration:

```lean
namespace HighamBenchCandidate

-- definitions needed to state the result

theorem target : <the generated proposition> := by
  sorry

end HighamBenchCandidate
```

Exactly this root proof hole is permitted. Every other `sorry`, `admit`, new
`axiom` or `constant`, `opaque`, `unsafe`, or equivalent integrity escape is a
validation failure. The proposition is not compared to an old Lean target.

## Per-condition state machine

```text
admitted
  -> model-active interval through terminal cleanup/quiescence
  -> telemetry settle and artifact bookkeeping (off-clock)
  -> candidate copy/hash (separately timed and charged)
  -> compilation/integrity validation (off-clock)
       -> neutral repair feedback -> same conversation, or
       -> fresh blind faithfulness audit (clock paused)
            -> accepted faithful, or
            -> neutral repair feedback -> same conversation
```

A complete immutable submission consumes one of the four submission slots even
when compilation fails. Audit infrastructure failures do not consume an
additional slot and are retried off-clock. The condition terminates on faithful
acceptance, the fourth rejected submission, the 18,000-second cumulative active
limit, or a fail-closed infrastructure outcome.

## Clock and usage boundaries

The model-active interval begins immediately before the `turn/start` RPC that
publishes the common prompt or frozen repair feedback to the persistent
formalizer conversation. It contains the model turn, post-terminal cleanup,
and verification that no contestant background terminal remains. The runner
then pauses that interval while it settles ordered telemetry and writes trusted
bookkeeping. It separately times and charges the stable candidate copy/hash.
The contestant-active total is the sum of the model-active and candidate-freeze
components, not the intervening off-clock work. App-server teardown, transcript
writing, compilation, and auditing are off-clock. The submitted artifact is the
single `Candidate.lean`; mutable scratch and object files are not submissions.

One raw-event-enabled app-server process remains alive for all submissions in a
condition. Repair prompts therefore continue the exact same conversation and
each upstream response has exact, deduplicated input, cached-input,
cache-write-input, output, reasoning-output, and total usage. A timeout keeps
observed usage as a labeled lower bound and remains an `ACTIVE_TIME_LIMIT`
outcome. Because a cold `thread/resume` cannot preserve that raw event stream,
an interruption after a submission is fail-closed; recovery is supported only
before the first turn or between sealed condition records.

Compilation, semantic-dossier construction, faithfulness auditing, and feedback
rendering are recorded separately and excluded from contestant-active time and
tokens. Ordered post-terminal telemetry settling and trusted artifact
bookkeeping are likewise excluded. End-to-end wall time is also reported.

The controller stores observable Codex JSONL events, prompts, final messages,
tool calls, usage records, file hashes, line counts, validation output, audit
outputs, and concise API-exposed reasoning summaries. Hidden chain-of-thought is
neither available nor requested or claimed.

## Faithfulness audit

Every new semantic statement hash receives a new audit. An exact duplicate may
reuse the already frozen verdict for that same pair run.

The audit uses fresh ephemeral agents for blind translation, direct comparison,
round-trip comparison, and conditional adjudication. Auditor workspaces expose
neither condition nor submission number. Candidate and local-library identifiers
and module provenance are pseudonymized in the semantic dossier before any
auditor sees it.

The dossier recursively expands reached declarations generated in the
candidate and, for condition L, reached NumStability declarations. Reached
Lean/Mathlib declarations form a recorded one-level type/body frontier. Lean
and Mathlib are the hash-frozen trusted semantic foundation, so faithfulness
claims are relative to their ordinary semantics; the benchmark does not claim
an unbounded transitive unfolding of that foundation.

An audit acceptance means the generated proposition faithfully captures the
selected paper statement. A rejected candidate receives only a fixed neutral
schema containing:

1. the missing or distorted paper requirement; and
2. the corresponding candidate mismatch.

Feedback contains no gold Lean theorem, proof code, NumStability module, or
NumStability declaration name.

## Pair integrity

The pair controller admits both conditions against one frozen task manifest
before either begins. It runs the conditions in the precommitted order, never
shares their workspaces, and publishes a pair result only after both terminal
records and their hashes are sealed. Reissuing the same task command returns the
existing terminal run or continues between sealed conditions rather than
silently creating a duplicate. It never cold-resumes an in-progress condition.
