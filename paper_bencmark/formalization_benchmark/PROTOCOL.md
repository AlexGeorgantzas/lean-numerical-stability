# Source-first formalization protocol

> Pilot-9 is a new frozen release. Pilot-8 and every earlier run remain sealed
> under their original software, prompts, task set, and audit policy. No
> observation is copied, resumed, or pooled across pilot identities.
> Pilot-8's H22-11 attempt is sealed as an infrastructure incident: its direct
> judges returned complete, ordered dependency records, but the controller
> rejected their human-readable dependency labels as if those labels were
> identities. Pilot-9 corrects that interface mismatch. It does not reinterpret
> Pilot-8 evidence or retry under the Pilot-8 identity.

## Purpose

Pilot-9 measures whether access to, and explicit encouragement to use, a frozen
NumStability library helps Codex construct a faithful Lean formalization of a
selected numerical-analysis result. It measures statement construction, not
proof construction.

## Frozen release

- Pilot ID: `formalization-benchmark-pilot-9`.
- One exact Git commit, manifest-file SHA-256, and self-hashed manifest payload
  define the release.
- Formalizer: `gpt-5.6-sol` at `xhigh`, frozen in `config.json`.
- One N/L pair per task, one official pair slot per `(pilot_id, task_id)`.
- Four submissions per condition: one initial statement and at most three
  same-conversation repairs.
- Cumulative contestant-active threshold: 18,000 seconds per condition.
- No benchmark token cap. Exact provider usage is still recorded.
- Fixed Titan envelope: eight logical CPUs, 32 GiB RAM, 512 tasks, and no swap.
  Generated command trees have a 24-GiB/384-task/no-swap child cgroup; trusted
  control has an 8-GiB `memory.low` reservation.
- A clean full build of the frozen NumStability snapshot is measured once
  off-clock during installation. Wall/CPU/resource metrics and complete build
  output are authenticated deployment evidence.

The task order is frozen as follows:

1. `P01-T2`, `P02-T2`, `P03-T2`, `P13-T2`, `P14-T2`
2. `H22-11`, `H22-5`, `H20-6`, `H7-12`, `H20-9`, `H20-8`
3. `H23-6`, `H5-5`, `H10-7`, `H12-4`, `H19-5`, `H7-14`, `H15-3`

The condition order is precommitted per task in `config.json`, with nine
N-first and nine L-first pairs. Pilot-9 creates fresh slots for all 18 tasks.

The five `P..-T2` entries are paper tasks retained from Pilot-6. The thirteen
`Hchapter-problem` entries are Higham textbook problems. Their source packets
fix the exact selected conclusion before a formalizer runs. Open-ended exercise
wording is not delegated to the contestant: H5-5 uses the book's Appendix A
`gamma_(2n+1)` result; H7-14 selects part (a); H12-4 selects the cited
Demmel--Higham first-order residual bound; H15-3 includes every stated
conclusion in the exercise; and H23-6 freezes the coefficient reading
`6*c_Strassen + 4`.

## Conditions

Both conditions receive byte-identical, hash-verified versions of:

- the source PDF and task packet;
- the common formalizer prompt;
- the Lean toolchain and Mathlib snapshot;
- the candidate contract, limits, and validation rules.

Condition N has no NumStability source, compiled objects, documentation,
declaration names, search index, cache, Git history, old benchmark target, or
prior condition output.

Condition L receives the same base environment plus the read-only NumStability
snapshot at commit
`45813a95dacf577461bae13f033af0dbc985a225`. The common prompt is followed by
one frozen L-only appendix. It explicitly encourages the model to inspect,
import, reuse, adapt, or draw inspiration from the library and gives concrete
discovery/import guidance. This encouragement is part of the treatment.

## Candidate contract

The single submitted artifact is `Candidate.lean`. Its final declaration must
be:

```lean
namespace HighamBenchCandidate

-- definitions needed to state the selected result

theorem target : <generated proposition> := by
  sorry

end HighamBenchCandidate
```

Exactly this proof hole is permitted. Every other `sorry`, `admit`, new
`axiom` or `constant`, `opaque`, `unsafe`, or equivalent integrity
escape fails validation. The candidate is never compared with an old Lean
target.

## Per-condition loop

```text
same persistent formalizer conversation
  -> model-active interval and token metering
  -> immutable Candidate.lean submission, freeze, and hash
  -> off-clock compilation and proof-integrity validation
  -> off-clock semantic-dossier extraction
  -> fresh blind/direct/round-trip audit roles
  -> faithful: stop
  -> unfaithful: neutral feedback to the same formalizer conversation
```

A complete immutable submission consumes one of four slots even when
compilation fails. Audit infrastructure retries are off-clock and do not
consume another submission; a provider-capability incompatibility blocks the
release. A condition terminates on faithful acceptance, four rejected
submissions, the active-time threshold, or a fail-closed infrastructure
outcome.

## Measurement

Contestant-active time starts immediately before the `turn/start` request that
delivers the common or repair prompt and continues through contestant-process
cleanup and quiescence. Ordered telemetry settling and trusted bookkeeping are
off-clock. Stable candidate copy/hash is timed separately and charged. The
active total is the sum of model-active and candidate-freeze durations.

Compilation, semantic extraction, auditing, feedback rendering, app-server
teardown, and transcript writing are excluded from contestant time and tokens.
End-to-end and audit overhead are reported separately. Any measured timeout or
freeze overshoot is preserved in full and makes the condition unscored
`ACTIVE_TIME_LIMIT`; it is never clamped.

One raw-event-enabled app-server process remains alive for all attempts in a
condition. Repair prompts therefore continue the exact same conversation.
Input, cached-input, cache-write-input, output, reasoning-output, and total
usage are deduplicated and cross-checked against cumulative thread telemetry.
An interruption after a submission is fail-closed because cold resume cannot
preserve this exact raw event stream.

Artifacts retain observable prompts, final messages, tool events, concise
API-exposed reasoning summaries, hashes, line counts, validation output, audit
output, hardware observations, and usage. Hidden chain-of-thought is neither
available nor requested.

## Faithfulness audit

### Source authority

The primary PDF and frozen source packet define the selected result. The packet
may clarify which part of an exercise is selected, but the PDF controls if they
conflict. Unlike the method paper's full audit, Pilot-9 omits a separate
source-contract model call because the source side is frozen and validated
before release. This deliberate deviation is recorded; every generated
candidate still receives a fresh candidate-side audit.

### Candidate semantic dossier

Lean elaborates the root proposition. The controller recursively expands types
and bodies of candidate-local declarations and reached NumStability
declarations. Reached Lean/Mathlib declarations form a one-level external
semantic frontier. Every dependency receives a stable `Dxxx` ID. Candidate
and NumStability names and module provenance are pseudonymized before auditors
see them. The ordered `Dxxx` value is the dependency identity. The accompanying
`name` is a required human-readable semantic label and is not an identity;
judges may render it differently without invalidating an otherwise complete
record.

The blind translator and direct judge must each return exactly one record for
every `Dxxx` ID, in order. Missing, duplicate, or renamed records invalidate
the role response. Supplying the dossier is not treated as a substitute for
this explicit dependency accounting.

### Fresh roles

Each role is a fresh, stateless, memoryless, condition-blind conversation:

1. blind Lean-to-mathematics translator;
2. direct PDF-versus-dossier judge;
3. round-trip PDF-versus-blind-translation judge;
4. adjudicator only when the frozen triggers require it.

All roles currently use the frozen audit model in `config.json`. This differs
from the method paper's use of a different model family for one role; role
freshness, state isolation, condition blindness, and evidence separation remain
mandatory.

### Mandatory 16 checks

Both judges must complete exactly `S01`--`S16`, in order:

1. source selection;
2. binders and types;
3. quantifier scope;
4. hypotheses;
5. conclusion completeness;
6. operators and imported definitions;
7. exact versus computed quantities;
8. algorithm linkage;
9. norm semantics;
10. constants and indexing;
11. floating-point model and exceptional values;
12. relation strength;
13. error notion;
14. higher-order terms;
15. specialization or generalization;
16. nonvacuity.

Each record includes source evidence, candidate or translation evidence, and
reasoning. `not-applicable` still requires an explanation.

### Implications and classification

Each judge answers both directions independently:

| Candidate implies source | Source implies candidate | Classification |
| --- | --- | --- |
| yes | yes | `faithful-equivalent` |
| yes | no | `faithful-stronger`, only for genuine added strength |
| no | yes | `unfaithful-weaker` |
| no | no | `unfaithful-different` |
| unclear | either | `undetermined`, mandatory adjudication |

Extra assumptions, restricted domains, impossible premises, or vacuity are not
strengthening. A genuinely stronger candidate is faithful because it still
implies the complete selected source result.

The method paper permits a score-2 exception for multiple declarations that
cover only a proper subset of the source domain. Pilot-9 deliberately rejects
that exception: partial case-split coverage is `unfaithful`. This deviation is
frozen and must not be inferred ad hoc during an audit.

The only final candidate verdicts are `faithful` and `unfaithful`.
`undetermined` is an intermediate judge classification that must be resolved
by a fresh adjudicator; it is never a candidate outcome. Operational failures
are sealed infrastructure incidents, not semantic verdicts.

Adjudication is mandatory when classifications differ, a judge requests it, or
a dependency or semantic check remains unclear. The adjudicator resolves
evidence item by item and returns both implication directions, a four-way
classification, and the binary final verdict. When judges agree conclusively
and no trigger remains, the controller derives the binary verdict without an
extra model call.

### Repair feedback

An unfaithful verdict must include a concrete source requirement and candidate
mismatch. Repair feedback contains only those condition-neutral prose fields.
It contains no gold Lean statement, proof code, library/module name, or
NumStability declaration identifier. A new semantic statement hash receives a
fresh audit; an exact duplicate may reuse only its already frozen decision in
the same pair.

## Admission and integrity

Before any official pair, provider-free doctor verifies the frozen release,
private PDFs, toolchain, Mathlib, NumStability build evidence, executables,
hardware, and N/L isolation. A paid off-benchmark qualification exercises the
exact formalizer and audit models/efforts, every frozen output schema, real
workspace reads, and the formalizer write path. It consumes no official task
slot and is excluded from contestant measurements.

The app-server globally and per thread disables agent delegation. Collaboration
events or foreign-thread notifications are provider incompatibilities, not
contestant errors.

The pair controller stages both conditions against one manifest before either
starts, runs the precommitted order, never shares workspaces, and publishes only
after both terminal records are sealed. Reissuing a task command returns the
existing terminal pair or resumes only at a safe boundary between conditions.
