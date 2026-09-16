# Source-first formalization protocol

> Pilot-6 release policy: a valid candidate has exactly two semantic audit
> verdicts, `faithful` and `unfaithful`. Pilot-5 and its sealed runs remain
> governed by the original three-way audit and must not be reinterpreted or
> resumed under this policy. The pilot-6 identity must be frozen, deployed,
> and qualified before any official pair starts.

## Purpose

This pilot measures whether access to, and explicit encouragement to use, a
frozen NumStability library helps Codex construct a faithful Lean formalization
of a paper result. It does not measure proof construction.

## Frozen pilot

- Release identity: `formalization-benchmark-t2-pilot-6`, one exact Git commit,
  manifest-file SHA-256, and manifest-payload SHA-256. Earlier pilots and their
  sealed incidents are predecessor provenance, not scored pilot-6 observations.
  Pilot-2 P01-T2 (`P01-T2-20260916T084145Z-6dad064a`) had one compiling N
  candidate but no faithfulness verdict because the provider rejected an audit
  response schema; L did not start. Pilot-3 P01-T2
  (`P01-T2-20260916T150151Z-40b3a1dd`) submitted the unchanged placeholder:
  its formalizer and paper-facing auditors could not access the workspace
  because `/codex-code-mode-host` was absent inside the sandbox. No
  faithfulness verdict or L run exists. Pilot-4 completed a clean library build
  in 1307.425 seconds under eight logical CPUs and 32 GiB RAM, and an isolated
  one-turn workspace-tool probe passed. Its six-role, one-shot qualification
  nevertheless failed after the formalizer completed with exact output and a
  checked workspace write, before any auditor role, because an overly broad
  warning detector matched unrelated truncated tool-catalog text. It created
  no official pair or task index. Pilot-5 then created sealed P01-T2 and
  P02-T2 pairs under its three-way policy; P02-T2 stopped when L's audit
  returned `unclear`. Those pairs retain their original disposition. All five
  pilot-6 task slots are fresh; no cross-pilot pooling or replacement within an
  older pilot.
- Tasks: P01-T2, P02-T2, P03-T2, P13-T2, and P14-T2.
- Replication count: one N/L pair per task.
- Formalizer model and reasoning effort are frozen in `config.json`.
- Maximum submissions per condition: four (initial plus three repairs).
- Cumulative contestant-active termination threshold per condition: 18,000
  seconds. Actual timer or final-freeze overshoot is retained and makes the
  condition unscored `ACTIVE_TIME_LIMIT`; it is never clamped or accepted.
- Benchmark token cap: none. Provider usage is still measured at every turn.
- Hardware envelope: the complete condition process tree runs in a transient
  user service with systemd-enforced affinity to exactly eight logical CPUs and
  cgroup limits of 32 GiB RAM, 512 tasks, and no swap. Model-generated command
  trees enter a delegated child cgroup capped at 24 GiB RAM, 384 tasks, and no
  swap; the trusted control child has an 8 GiB `memory.low` reservation. The
  outer service denies affinity changes for its complete descendant tree, and
  the generated-command seccomp policy repeats the denial. Every strict
  snapshot verifies that syscall denial. Setup freezes the Titan host identity,
  CPU model, and exact eight-CPU set; the controller verifies that identity at
  admission and at both ends of every attempt.
- Pair concurrency: one measured N/L pair at a time on Titan, enforced by an
  account-global nonblocking lock and all five predecessors' existing locks.
  An account-global registry reserves each `(pilot_id, task_id)` exactly once.
- Library provisioning: setup runs `lake clean`, rehydrates the frozen
  dependency cache off-clock, proves that the root project build tree is still
  empty, and fully builds the frozen NumStability target once inside the same
  outer eight-CPU/32-GiB/512-task/no-swap envelope. Its wall/CPU/resource data
  and complete output are authenticated deployment evidence and are never
  charged to a contestant.

The existing 51 accepted HighamBench tasks establish only that the selected
paper results can be formalized faithfully. They do not pre-approve any
candidate generated in this pilot.

Before a new official pair is created, the provider is qualified outside the
contestant clock and task slot using the exact frozen role/model/effort and
single-agent capability contract. The effective app-server configuration must
report `agents.enabled=false`, `multi_agent=false`, and
`multi_agent_v2=false` globally and for each thread. Collaboration tool events
or foreign-thread notifications are infrastructure incompatibilities, never
contestant rule violations. The same paid, off-benchmark qualification must
also submit each exact frozen audit output schema (blind translation, direct
judgment, round-trip judgment, and adjudication) to the provider and verify
checkable synthetic outputs. It must exercise real workspace tools on
synthetic files inside the same sandbox, with trace-backed reads for both
role types, a checked formalizer write, and no actual Code Mode startup warning.
The warning check examines diagnostic events and stderr, not arbitrary
tool-catalog text; this avoids the pilot-4 false failure without accepting a
real host-startup failure.
The deployment authenticates the same-package Code Mode host and mounts it
read-only beside the Codex executable. Local schema validation or a generic auditor
probe is insufficient: pilot-2 passed the latter but the real blind auditor
was rejected before inference. Provider-free doctor and dry-run remain free of
model inference; qualification usage is never included in contestant metrics.
The deprecated `multiAgentMode` response is not capability evidence.

Repair and qualification do not consume an official task slot and do not
authorize an official pair. Launch one only on an explicit task-run request.

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
  -> single-agent configuration and feature attestation (off-clock)
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
additional slot and are retried off-clock, except a provider capability
incompatibility, which blocks the release. The condition terminates on faithful
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
components, not the intervening off-clock work. The 18,000-second value is the
termination threshold rather than a claim that operating-system timer delivery
has zero latency: any measured overshoot is retained in full and terminates the
condition unscored before validation or auditing. App-server teardown,
transcript writing, compilation, and auditing are off-clock. The submitted
artifact is the single `Candidate.lean`; mutable scratch and object files are
not submissions.

One raw-event-enabled app-server process remains alive for all submissions in a
condition. Repair prompts therefore continue the exact same conversation and
each upstream response has exact, deduplicated input, cached-input,
cache-write-input, output, reasoning-output, and total usage. A timeout keeps
observed usage as a labeled lower bound and remains an `ACTIVE_TIME_LIMIT`
outcome. Because a cold `thread/resume` cannot preserve that raw event stream,
an interruption after a submission is fail-closed; recovery is supported only
before the first turn or between sealed condition records.

If the controller or host stops before a complete turn record or candidate-
freeze duration becomes durable, the pair is sealed as an unscored incident.
The recorded contestant time and token totals remain useful lower bounds, but
their completeness fields explicitly label whichever measurements are no
longer exact.

Compilation, semantic-dossier construction, faithfulness auditing, and feedback
rendering are recorded separately and excluded from contestant-active time and
tokens. Ordered post-terminal telemetry settling and trusted artifact
bookkeeping are likewise excluded. End-to-end wall time is also reported.

The controller stores observable Codex JSONL events, prompts, final messages,
tool calls, usage records, file hashes, line counts, validation output, audit
outputs, and concise API-exposed reasoning summaries. Hidden chain-of-thought is
neither available nor requested or claimed.

## Faithfulness audit

### Binary verdict policy

For a compiling, integrity-valid candidate with an admissible source task, the
semantic verdict has exactly two values: `faithful` or `unfaithful`. Accept as
`faithful` only when the candidate's elaborated proposition and reached
definitions establish every material requirement of the selected paper result,
including the full paper-permitted domain. The burden is on the candidate to
encode any equivalence on which its scope depends. If, for example, the
candidate assumes successful partial operations but the paper assumes no
overflow, and the candidate does not establish that the former covers every
no-overflow execution, classify it `unfaithful` and identify that domain gap as
a concrete mismatch. Do not accept a narrower theorem merely because its
conclusion is true on the restricted domain.

An `unfaithful` verdict requires a concrete paper requirement and corresponding
candidate mismatch in condition-neutral language. It triggers the ordinary
frozen feedback and same-conversation repair loop if a submission slot remains.
Auditor disagreement is resolved against the paper and candidate semantics,
not by majority vote or a third semantic verdict. Provider failures, malformed
auditor responses, unavailable tools, and dossier failures remain unscored
operational incidents, not faithfulness tags. A genuinely underdetermined
paper/source contract must be resolved or excluded at source-admissibility
review before a candidate is scored; it must not be silently labeled a
contestant error. This binary rule applies to pilot-6 only; pilot-5 remains
sealed under its frozen policy.

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
