# Source-first formalization operations

Paths in this reference are relative to the repository root. The spelling
`paper_bencmark` is intentional.

The active release is pilot-3. Pilot-1 and pilot-2 are sealed, unscored
predecessor evidence, not observations or runs to resume. Pilot-2 P01-T2
(`P01-T2-20260916T084145Z-6dad064a`) stopped after N submitted one compiling
candidate because the provider rejected the blind-translation response schema;
there was no faithfulness verdict and L never started. Do not pool data across
pilots. Pilot-3 has distinct deployment, launcher, task indices, and
account-global pilot/task reservations; all five task slots are fresh.

## Canonical surfaces

| Purpose | Path |
| --- | --- |
| Protocol | `paper_bencmark/formalization_benchmark/PROTOCOL.md` |
| Runner | `paper_bencmark/formalization_benchmark/tools/run_benchmark.py` |
| Frozen config | `paper_bencmark/formalization_benchmark/config.json` |
| Frozen release manifest | `paper_bencmark/formalization_benchmark/manifest.json` |
| Task packet | `paper_bencmark/formalization_benchmark/packets/<TASK-ID>.json` |
| Common prompt | `paper_bencmark/formalization_benchmark/prompts/formalizer.md` |
| L-only encouragement | `paper_bencmark/formalization_benchmark/prompts/condition_L.md` |
| Repair prompt | `paper_bencmark/formalization_benchmark/prompts/repair.md` |
| Repair-feedback schema | `paper_bencmark/formalization_benchmark/schemas/repair_feedback.schema.json` |

These are source-first surfaces. File presence alone is not admission evidence;
the runner must hash-authenticate their complete transitive release closure.

## Compatibility boundary

The existing `paper_bencmark/highambench/tools/runner.py`,
`paper_bencmark/highambench/tools/run_matrix.py`, and their campaign managers
implement the legacy fixed-target proof experiment. They are
incompatible with this pilot because they expose a prewritten target/common
scaffold, score proof completion, use the old one-shot submission boundary, use
legacy time/token stopping rules, and do not implement candidate-specific
faithfulness repair.

Never call `runner.py`, `run_matrix.py`, a P01/P11 campaign manager, a pair-shard
launcher, or a legacy canary launcher for a source-first request. Never translate a
source-first task into an old pair ID. If the canonical source-first runner,
metadata, task packet, validator adapter, or audit adapter is missing or its
`doctor` gate is unavailable, report `source_first_runner_not_ready` and stop
before a provider call. Do not invent flags or manually reproduce the loop.

The repository's existing `paper_bencmark/faithfulness_audit/` workflow was
written for fixed task targets. It may supply audited methodology and reusable
components only through the source-first adapter authenticated by the runner.
Do not point it at a generated candidate by overwriting an old `Target.lean` or
task-local audit directory.

## Natural-language dispatch

Normalize harmless separators and case, but require the canonical result to be
one of:

```text
P01-T2
P02-T2
P03-T2
P13-T2
P14-T2
```

`Run benchmark for P01-T2` means:

1. select only `P01-T2`;
2. authenticate one immutable pair manifest;
3. run exactly one N condition and one L condition in the frozen order; and
4. stop after both have a terminal, authenticated result or the pair reaches a
   hard-stop incident.

It does not authorize additional repetitions, the other pilot tasks, metadata
refresh, controlled-file edits, publication, commit, push, or deletion of an
existing result.

The earlier accepted HighamBench tasks establish only that these source results
can be formalized faithfully. They never pre-approve a generated candidate;
every distinct semantic candidate still needs its own audit.

## Admission

On Titan, authenticate the installed release through its location-independent
launcher:

```bash
~/.local/bin/run-highambench-formalization-pilot-3-r1 verify-release
```

Then run the canonical non-provider gate through the same installed hardware
envelope:

```bash
~/.local/bin/run-highambench-formalization-pilot-3-r1 doctor \
  --task-id P01-T2
```

Do not proceed unless `verify-release` and `doctor` both exit successfully and
their authenticated outputs jointly confirm all of the following:

- the task is pilot-allowlisted and the requested manifest resolves uniquely;
- the exact PDF, cited source locations, neutral source contract packet, and
  result ID match their recorded SHA-256 values;
- the common prompt is byte-identical between conditions and only L receives
  the separately hashed encouragement appendix;
- N has no tool-visible NumStability bytes or metadata, while L has exactly the
  frozen authenticated source and compiled snapshot;
- the NumStability snapshot includes an authenticated clean-build record,
  complete build output, raw GNU `time` output, and admitted start/end hardware
  observations, all classified as uncharged deployment evidence;
- the prior target, shared task scaffold, gold Lean, proof, and prior audit
  artifacts are absent from both contestant and candidate-auditor views;
- the frozen Lean, Mathlib, model, reasoning effort, tool allowlist, runner,
  validator, audit policy, and feedback schema agree;
- the candidate contract requires one designated root theorem with `by sorry`
  and prohibits every other `sorry`, `admit`, new axiom, or unsound substitute;
- the run contract is four total submissions, an 18,000-second cumulative
  active-time termination threshold, no benchmark token cap, and separate
  off-clock validator/audit ledgers;
- the outer allocation enforces 32 GiB RAM, 512 tasks, no swap, and exactly
  eight assigned logical CPUs; the generated-command child enforces 24 GiB,
  384 tasks, no swap, and its frozen CPU weight, while the trusted-control child
  retains its configured reservation; all of these match the setup-frozen host,
  CPU model, exact CPU set, and isolation scope;
- the task index is either fresh or names an authenticated resumable/terminal
  pair; official staging performs the final byte-for-byte N/L check before any
  provider call; and
- the private authentication file is present and the frozen Codex app-server
  interface starts through the exact sandbox, attests effective
  `agents.enabled=false`, `multi_agent=false`, and `multi_agent_v2=false`,
  and stops without model inference or writing secrets to logs;
- the sealed pilot-1 and pilot-2 predecessor incident lineage and the
  account-global campaign lock/registry match the pilot-3 deployment record.

CLI arguments may assert frozen values but may not override them. A mismatch is
a hard stop. Do not auto-refresh hashes, amend prompts, weaken isolation, change
the task order, or use a force flag during admission.

## Pair invocation

After successful admission, invoke exactly one pair:

```bash
~/.local/bin/run-highambench-formalization-pilot-3-r1 run \
  --task-id P01-T2
```

Replace `P01-T2` only with the single allowlisted task requested by the user.
Do not add a repetition count. The runner, not the operator, selects the frozen
N/L order and creates the pair/run identities.

Before creating a fresh official pair ID or task index, the runner must pass
the exact-model/effort provider-backed single-agent capability probes and live
output-schema probes for every frozen audit role: blind translation, direct
judgment, round-trip judgment, and adjudication. The latter use the exact
schemas that production auditing will submit, with synthetic checkable
outputs. Static JSON-schema checks or a generic auditor probe do not establish
provider acceptance of those schemas. Qualification is outside the contestant
clock and task slot; its separate time and tokens are retained as overhead. A
failed or missing qualification stops without consuming a slot. The deprecated
`multiAgentMode` response is not an attestation. Collaboration or
foreign-thread events are provider infrastructure incompatibilities, never
contestant rule violations.

The explicit `qualify-provider --task-id P01-T2` command may establish this
readiness without starting a benchmark. After setup or repair, inspect all
five task statuses with provider-free `status`. Do not invoke official `run`
until the user explicitly asks to start that task.

Use the provider-free `status --task-id P01-T2` command to inspect a task. Do
not reissue `run` merely to inspect it. Reissue the same authenticated `run`
command only when intentionally continuing an advertised resumable transition
or retrieving the already terminal result. Recovery is supported before a
condition's first turn and between terminal, hash-sealed condition records. A
frozen-feedback transition continues automatically only while that condition's
original app-server process remains alive. A controller or process interruption
after any submission cannot be cold-resumed without losing exact raw usage and
therefore becomes a fail-closed pair incident. Never edit the event stream or
state files to advance a run.

## Condition construction

The runner must construct both conditions from the same authenticated neutral
base:

| Surface | N | L |
| --- | --- | --- |
| Frozen paper packet and source contract | identical | identical |
| Common base prompt | identical | identical |
| Lean and Mathlib | frozen | same frozen versions |
| NumStability source/object/index | absent | frozen authenticated snapshot |
| Prompt treatment appendix | absent | explicit frozen encouragement |

The L appendix must encourage active library discovery and reuse, import,
adaptation, or inspiration. It must also say that library material is not
automatically source-faithful. Do not dilute this message, inject a neutralized
version into N, or add condition-specific tips elsewhere. The frozen appendix
must identify `/library/NumStability`, `/library/NumStability.lean`, compiled
declarations on `LEAN_PATH`, and concrete `find`, `rg`, and
`import NumStability` discovery/import options.

The common prompt must require the exact selected result, say that faithful
formalization is known to be achievable and has been achieved before, explain
the independent audit, and direct the formalizer to inspect the target and all
supporting definitions before submitting.

Use fresh workspaces, caches, process namespaces, Codex homes, and formalizer
conversations for N and L. Nothing learned from one condition, task, or run may
enter another. Keep both conditions of the pair on the same authenticated
hardware allocation. The account-global and predecessor locks must admit only one pilot pair
at a time; do not bypass it to run separate tasks concurrently.

## Candidate state machine

Each condition follows this trusted state machine:

```text
READY
  -> MODEL_ACTIVE through contestant-process quiescence
  -> OFF_CLOCK_TELEMETRY_AND_BOOKKEEPING
  -> CANDIDATE_FROZEN (separately timed and charged)
  -> VALIDATING
  -> AUDITING
  -> ACCEPTED
     or FEEDBACK_FROZEN -> MODEL_ACTIVE
     or TERMINAL_LIMIT
```

The runner publishes the initial prompt or a repair-feedback packet only after
recording its hash. It starts or resumes the model-active monotonic interval
immediately before the `turn/start` RPC. The formalizer can inspect only its
assigned environment, create the formalization, run Lean, and submit through
the authenticated nonterminal candidate boundary.

At submission, require the contestant process tree to become quiescent. This
ends the model-active interval. After off-clock ordered telemetry settling and
trusted bookkeeping, separately time and charge the stable copy/hash of the
single submitted `Candidate.lean`. Scratch files and object files in the
mutable workspace are not part of the submission. The contestant-active total
is the sum of the model-active and candidate-freeze components. App-server
teardown, artifact-log writing, validation, and auditing are off-clock. Every
candidate snapshot consumes one of four slots, even when compilation or
integrity fails.

The root theorem must formalize the exact source result and have proof body
`by sorry`. Supporting definitions, structures, instances, notation and lemmas
are permitted and charged. No other `sorry`, `admit`, new axiom, hidden target,
unsafe escape, prohibited import, binary substitution, or undeclared external
dependency is allowed.

The run terminates at the first faithful candidate, the fourth submitted
candidate, or the 18,000-second cumulative contestant-active termination
threshold. The active-time threshold never resets after feedback. Any timer or
final-candidate-freeze overshoot is measured rather than clamped and produces
the unscored `ACTIVE_TIME_LIMIT` outcome; an accepted or otherwise scored
condition can never exceed the threshold. There is no contestant-token
termination rule.

## Validation, audit, and repair

Trusted compilation and integrity validation begin after the candidate is
frozen and remain off-clock. A compile- or integrity-invalid candidate does not
receive a semantic audit. If another slot remains, the runner produces only
frozen, categorical, fixed-schema validator feedback and returns it to the same
formalizer conversation; raw compiler output is never included in repair
feedback.

For each compiling candidate, record:

1. the submitted `Candidate.lean` SHA-256; and
2. a semantic-statement SHA-256 over the elaborated root theorem type and the
   recursive closure of reached generated/NumStability declarations plus the
   recorded one-level type/body frontier of reached Lean/Mathlib declarations.

Lean and Mathlib are a frozen, trusted semantic foundation. Their frontier is
not recursively unfolded to foundational primitives: doing so would make the
dossier unbounded and obscure standard-library meaning. Audit claims are
therefore relative to the ordinary semantics of that hash-frozen foundation;
the dossier records its exact frontier rather than claiming a complete
transitive expansion of it.

Every distinct semantic hash requires a fresh audit. Auditors must be fresh,
stateless, blind to condition and attempt number, and unable to see the
formalizer transcript, other candidates, timing, tokens, the legacy target, or
library provenance wherever de-identification is reliable. The dossier
contains candidate semantics under the explicit closure/frontier policy; paper
and packet are supplied separately only to paper-facing roles.

Acceptance requires the frozen audit's `faithful` verdict: every material
binder, premise, restriction, quantifier dependency, and conclusion must match
the selected paper result without vacuity, unsupported assumptions, or narrower
applicability. An evaluator failure, unresolved evaluator disagreement, or
source ambiguity not caused by the candidate is an unscored audit-system
incident; it does not consume a new contestant slot.

For an unfaithful candidate with a slot remaining, render feedback only through
the frozen condition-neutral schema. It identifies each missing paper
requirement, the candidate mismatch, and the required direction of repair. It
must not contain a gold theorem, Lean code, tactics, proof steps, adapters,
NumStability names, condition/attempt labels, or raw auditor reasoning. Freeze
and hash the feedback before returning it to the same conversation. Resume the
active clock immediately before it is delivered.

Never reuse an audit verdict for a candidate whose semantic closure changed.
Never send raw role outputs or deliberations to the formalizer.

## Metering and logging

The contestant ledger sums each model-active interval and the separately timed
candidate-freeze component. Model-active time includes provider latency,
visible generation, tool calls, library search, shell work, contestant-initiated
Lean builds, background-terminal cleanup/quiescence, and all descendants.
Ordered telemetry settling and trusted bookkeeping between quiescence and
freeze are excluded. Multi-agent execution is disabled for this pilot.

The contestant token ledger measures, without imposing a cap, every raw
provider response in the formalizer conversation. One raw-event-enabled
app-server process stays alive across all repairs. Usage is deduplicated by
response ID and cross-checked against the cumulative thread delta for input,
cached input, cache-write input, output, reasoning output, and total tokens.
Missing completed-turn usage is `telemetry_invalid`, never zero. Usage observed
before an active-time interruption is retained as a clearly labeled lower
bound; it does not replace the valid `ACTIVE_TIME_LIMIT` endpoint.
If the controller or host dies before a complete turn or final-freeze duration
is durably journaled, seal an unscored pair incident and label the affected
token and/or active-time totals as incomplete observed lower bounds. Never
present those partial totals as exact.

Validation, audit, adjudication and feedback-rendering durations and tokens are
recorded separately and excluded from contestant time/tokens. End-to-end
elapsed time is still reported.

Record observable evidence: frozen prompts and feedback, visible messages and
reasoning summaries when exposed, provider-reported input, cached-input,
cache-write-input, output, reasoning-output, and total token counts, tool calls,
commands, executable/script hashes, outputs, candidate snapshots, imports,
dependency evidence for reached L-library declarations, line counts, validator
results, audit classifications, hardware observations, and all ledger
transitions.

Record the effective CPU set, memory and swap limits, CPU/host identity, and
isolation identity at the start and end of every condition attempt. The outer
service enforces affinity to eight CPUs plus cgroup limits of 32 GiB, 512 tasks,
and no swap. Generated command trees are additionally limited to 24 GiB, 384
tasks, and no swap, while the trusted controller has an 8-GiB `memory.low`
reservation. A service-wide syscall filter denies affinity changes for the
controller, Codex, build tools, auditors, and descendants; the command seccomp
policy independently repeats that denial. Every strict hardware snapshot runs
a no-op affinity syscall canary and fails unless the kernel rejects it.
Command-child limit events are terminal evidence. Other operating-system
resource counters that are reported are observations, not frozen admission
criteria.

Never request or log hidden chain-of-thought. Never describe visible reasoning
summaries or ordinary token counts as chain-of-thought. Keep system
and developer prompts, credentials, authentication material, and restricted
provider records out of publishable artifacts.

## Results, resume, and reporting

Preserve immutable run directories and their event streams. Do not delete,
overwrite, merge, rename, or reuse an existing run ID. A hard-stop or
interrupted run remains evidence. Continue only when the source-first CLI
verifies its hash chain and advertises a pre-first-turn or between-condition
transition; never cold-resume a submitted condition. Inspect with `status`;
reissue `run` only to intentionally continue such a transition or retrieve the
terminal result.

For each condition report:

- terminal classification and accepted semantic hash, if any;
- number of submissions and failure class for each;
- first-submission and cumulative contestant-active time;
- first-submission and cumulative contestant tokens;
- completeness/interpretation labels for both time and token totals, especially
  for an unscored interrupted pair;
- formalization size and dependency profile;
- separate validation/audit time and token overhead;
- end-to-end elapsed time and hardware/resource observations; and
- immutable artifact and ledger paths.

For the pair, report the frozen order and manifest identifiers and make only a
descriptive N/L comparison. With one pair per task, this pilot evaluates
pipeline behavior and does not support a precise stochastic-effect estimate.

Do not publish, commit, push, upload, or expose raw result material unless the
user separately authorizes that action.
