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
  `LIBRARY_API.md` is the complete declared retrieval interface. The contestant
  sandbox exposes source-stripped Mathlib package runtimes. R1 receives only
  the packet-selected NumStability modules and their compiled import closure,
  not the full library tree. The closure is necessarily compiler-visible, so
  the prompt forbids treating it as a search interface; command telemetry is
  screened for probing. Both declaration atlases are schema-v3 artifacts built
  after position-preserving removal of Lean line comments and nested block/doc
  comments; documentation examples therefore cannot become declaration cards.
  The frozen Lean helper also requires each card's claimed module to equal
  Lean's compiled declaration owner, failing closed on any atlas/source
  disagreement. Design-17 derives fresh schema-v3 Mathlib and NumStability
  atlases and a fresh deployment identity layered over the immutable Pilot-15
  runtime; it never mutates or relabels the historical schema-v2 artifacts.
  Before the clock, that helper reads only the
  elaborated `ConstantInfo.type` of each visible card declaration. The packet
  interface is exactly the visible declarations plus the one-hop NumStability
  constants occurring in those types; it never reads declaration values/bodies
  and never recurses through the newly found prerequisites. This makes necessary
  signature constants such as `FPModel`, `gamma`, and `gammaValid` legal even
  when they are not separate dependency cards, without admitting proof-body or
  same-module neighbors. Separately, the controller generates a framed Lean
  command file that imports the visible card modules and runs ordinary `#check`
  commands for the exact seed names. Their command-frontend output replaces
  every model-visible atlas snippet, so malformed source snippets cannot
  disclose names that the semantic interface rejects and the contestant sees
  normal Lean notation rather than internal elaborator names. No textual
  rewriting of signatures is permitted. Prerequisite owner modules must already
  belong to the trusted import closure of visible card modules: they are not
  added as runtime roots or permitted explicit imports. The controller rejects
  every direct target dependency or explicit NumStability import outside this
  frozen surface. Helper, seed, render-source, output, and execution hashes are
  retained. This is a logged compliance boundary, not a claim of cryptographic
  noninterference.
- Before a paid campaign begins, `tools/design17_preflight.py` reproduces the
  retrieval, canonical Lean signature rendering, strict compiled-owner check,
  one-hop type-interface derivation, and packet-scoped R1 OLean runtime build
  for both conditions of every scheduled task. Independent task-condition
  checks may run concurrently because they use disjoint output roots and make
  zero provider calls. Any failure blocks the campaign and remains preserved as
  a preflight incident; it is never converted into a contestant result.
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

A non-dry statement campaign is rejected unless this envelope is requested and
verified. The campaign manifest freezes a random campaign nonce and hashes the
deployment record, formalizer/repair/audit prompts and schemas, controller and
runner Python dependency closure, source packets, optional contract overlays,
source PDFs, readiness/configuration records, snapshot records, and both
declaration atlases. Resume recomputes this closure and fails if an input moved
or changed.

## Submission and repair loop

Each condition receives an initial turn and at most three repair turns in one
persisted contestant conversation. The contestant clock covers only model-active
time and candidate freezing, accumulated across all submissions; retrieval is
recorded as a separate deterministic component. Compilation, dossier
construction, auditing, and feedback generation remain excluded.

Every returned `Candidate.lean` is copied immediately into a mode-0400 numbered
submission and hash-verified. Validation and audit operate only on that frozen
copy. An invalid or unfaithful submission receives the fixed condition-neutral
feedback schema containing only the missing source requirement and candidate
mismatch. The repair turn sees no gold Lean statement, proof, condition label,
attempt label, or NumStability declaration name.

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

The blind translator and direct judge start concurrently in separate fresh
drivers and disjoint read-only workspaces. The round-trip judge starts only
after the blind translation has validated and been frozen; it may overlap a
still-running direct judge. Adjudication remains sequential and starts only
after both judgments validate. Every started role is drained before an audit
decision or incident is sealed, and per-role schedule, usage, and thread
telemetry are retained in deterministic logical order. Formalizers, benchmark
conditions, and tasks remain sequential.

Proper-subdomain and partial case-split coverage fail. A genuinely stronger
full-domain proposition may pass. Auditor time and tokens are reported but
excluded from benchmark measurements.

## Outcome and analysis policy

- `AUDITED_FAITHFUL_PAIR` requires both condition candidates to pass the
  canonical binary audit. Only such pairs are eligible for paired time, token,
  and line-count effect estimates.
- If either side exhausts four submissions, reaches the cumulative active-time
  cap, fails compilation, or ends unfaithful, the pair is retained as
  `AUDITED_PAIR_INELIGIBLE`. It is a benchmark outcome, not silently censored or
  reported as a treatment win.
- Infrastructure and audit-system incidents are separate from contestant
  failures and are retained with their evidence. They may be rerun only under a
  predeclared incident-recovery rule.
- The primary descriptive quantities are the paired R1/R0 ratios of cumulative
  active seconds and net-new tokens among faithful pairs. Submission count and
  source lines are secondary. Success rates and ineligible-pair reasons are
  always reported alongside success-conditioned ratios.
- Building-block tasks and negative controls remain separate strata. Direct
  result collisions and router errors are excluded by the frozen readiness
  decision, never post hoc because their numbers are inconvenient.

Compilation is never recorded as scientific completion. Before a paid pair can
become terminal, the campaign controller writes
`tasks/<task>/campaign-pair-attestation.json`. It binds the campaign identity
and nonce, a per-pair nonce, mode, condition order, runner return code and log
hashes, pair-report hash, and the exact hash closure of every pair artifact.
Recovery accepts an existing pair only when the hash-chained `TASK_STARTED`
record, manifest, attestation, pair/condition reports, frozen submissions,
validation records, source artifacts, and artifact closure all agree. Missing
attestation, an unattributed output tree, or any mutation is retained as an
incident and is never silently rerun.

## Development policy

Consumed tasks may be used to engineer this protocol, but their observations
remain development evidence. The initial diagnostic wave is H5-5 and H10-7
(building-block treatment routes) plus H7-12 (negative control). The five tasks
identified as direct-result collisions or router errors are never pooled with
the primary engineering stratum. No task is rerun silently and every incident
is retained in the hash-chained campaign journal.
