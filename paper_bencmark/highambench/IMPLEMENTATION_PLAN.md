# Implementation plan for the current construction corpus

## 1. Read and classify before writing code

The benchmark specification, all 17 pages of P01, and all 34 pages of P02 were
read before selecting the new tasks. P01 has no numbered theorem blocks. P02
has numbered theorem, lemma, proposition, corollary, algorithm, and equation
blocks.

The selection rule was:

1. Use a claim that is made or derived in this paper.
2. Avoid claims whose proof is mainly delegated to another paper.
3. Avoid experimental tables because they are observations, not proof targets.
4. Avoid first-order `O(u^2)` statements unless they can be replaced by a clear,
   exact bound with all assumptions shown.
5. Do not choose a theorem whose exact fixed Lean statement already exists in
   mathlib or NumStability.

Every selected task also receives a source-presentation tag under the policy in
`../TASK_SOURCE_TAGS.md`. The tag records how the paper presents the selected
result; it is independent of the T1/T2/T3 library-relationship tier. Every
paper entry uses the same validator and construction-state rules. Tasks remain
editable until the complete corpus is made measurement-ready.

For P01 this produced one target for every tier:

- T1 specializes the existing pairwise bound to nonnegative inputs.
- T2 combines the pairwise bound, recursive bound, and the comparison between
  their bound factors.
- T3 asks for the no-guard recursive-summation running-error bound in equation
  (5.3). Its right side uses the actual computed prefix sums. NumStability has
  no accumulated no-guard running-budget theorem. Condition L has a one-step
  no-guard identity and a generic local-error recurrence scaffold, but still
  needs new no-guard state, witness, indexing, and budget bridges or a fresh
  full induction.

P02 also supports every tier:

- T1 is the exact-sum invariant for `VecSum` in equation (4.7)(i), a direct
  iteration of the error-free `TwoSum` identity and close to the library's
  compensated-prefix exactness results.
- T2 is Proposition 4.5, equation (4.8). It combines the `VecSum` invariant,
  Lemma 4.2, ordinary recursive summation, final rounding, and a gamma
  inequality specific to the paper's proof.
- T3 is the no-multiplication-underflow absolute bound in Proposition 5.11.
  It requires an iterated `VecSum`/`SumK` analysis, an error-free product
  transform, its absolute-mass estimate, and new gamma comparisons. The exact
  `DotK` result is absent from NumStability.

Theorem 3.4 was not selected because its central exactness proof is delegated
to earlier work. Relative-error corollaries, experiments, operation counts,
and the larger underflow/error-estimator branches were also not selected.

## 2. Record the meaning of each statement

Each paper-owned definitions module must be usable without importing
NumStability or another HighamBench module. It contains only the small semantic
setting required by that paper's targets:

- a standard rounded-addition model;
- a no-guard-digit rounded-addition model, where the left and right inputs may
  receive separate small errors;
- exact finite sums and sums of absolute values;
- recursive summation;
- power-of-two pairwise summation;
- the computed-prefix running budget from equation (5.3);
- `gamma u k = (k * u) / (1 - k * u)` in a suitable real-number form;
- the validity assumption `k * u < 1`.
- an abstract error-free `TwoSum` contract;
- `VecSum`, iterated `VecSum`, `SumK`, and `Sum2`;
- the no-multiplication-underflow error-free `TwoProduct` contract; and
- the transformed vector and `DotK` definitions used by Algorithm 5.10.

The word *model* means a small list of rules that an operation must follow. It
does not claim to describe every detail of a physical IEEE-754 machine.

The fixed target declarations are:

- `p01_t1_pairwise_nonnegative`;
- `p01_t2_pairwise_vs_recursive_bounds`;
- `p01_t3_noGuard_recursive_running_error_bound`.
- `p02_t1_vecSum_preserves_sum`;
- `p02_t2_sum2_error_bound`;
- `p02_t3_dotK_error_bound`.

Their current files are under `tasks/P01/` and `tasks/P02/`, with one
`Target.lean` per tier. Every custom semantic declaration required by P01 is in
`P01Definitions.lean`; P02 independently owns its analogous declarations in
`P02Definitions.lean`. Similar mathematics is deliberately duplicated under
paper-specific names. Neither module imports `Core`, `SemanticCore`, or the
other paper. A staged task and `shared_olean/P0X/` bundle receive only that
paper's definitions.

Every target must compile in clean N and L before its paper is registered. The
paper finalizer regenerates only its controlled manifests and atomically writes
`metadata/papers/P0X/registration.json`; no corpus-wide resnapshot or later
serialized merge is part of paper extraction.

## 3. Keep the statement neutral between conditions

The target statement and every name in it must come from mathlib or the shared
task files. No target statement may mention a NumStability declaration.

Condition L may use a separate adapter in the submitted proof. An adapter is a
small piece of code that connects the shared model to the library's model. The
fixed target file itself stays unchanged. Condition N must not contain that
adapter if it exposes a library name or artifact.

Prompt protocol `signposted-library-v1` keeps `agent_prompt.md` common and adds
the controlled `condition_prompts/L.md` supplement only for condition L.
Condition N receives no condition supplement. The L supplement identifies the
frozen NumStability commit
`45813a95dacf577461bae13f033af0dbc985a225`, the read-only source tree
`/library/NumStability`, root source file `/library/NumStability.lean`, and
compiled tree `/library-olean`. It says that `/library-olean` is already on
`LEAN_PATH` and gives neutral local discovery, import, and `#check` templates.
It must never name or recommend a target-relevant theorem, module, declaration,
search term, adapter, or private-proof fact.

This supplement is an evaluation treatment, not task content. It must not
change any `context.md`, `Target.lean`, task statement, or paper-owned
definition. The adapter composes L input as common prompt, L-only
supplement, context, then target; N composes common prompt, context, then target.

Before release, build every fixed statement in both clean environments. Hash the
controlled files and have the validator reject any changed hash.

## 4. Build the validator

The validator must run in a fresh hidden copy of the frozen project and check:

1. The exact target declaration is present and Lean accepts it.
2. Controlled statement and task files have their recorded SHA-256 values.
3. The proof has no `sorry`, `admit`, new axiom, unsafe checking bypass, hidden
   answer, or forbidden import.
4. Only allowed local tools were used and no network request was attempted.
5. Condition N exposes no NumStability source, compiled file, documentation,
   name list, search index, or cache.
6. A condition-L pass records the NumStability declarations in the checked
   proof's full dependency chain. A dependency chain is the list of definitions
   and theorems on which a proof ultimately relies.

A text search for a library name is not enough for step 6. The check must inspect
Lean declarations reached by the proof and by any local helper declaration.

## 5. Freeze evaluation inputs

The current fixed items are recorded in `metadata/config.json`:

- Lean toolchain;
- mathlib commit;
- NumStability baseline commit;
- 1,800-second wall-clock limit;
- 5,000,000-total-token limit, the current user-authorized deviation from the
  earlier 2,000,000-token project freeze, applied identically to N and L;
- three repetition IDs;
- deterministic pair order;
- model-tool network isolation requirement.

The exact agent version, model version, common-prompt hash, L-supplement hash,
prompt protocol and composition order, allowed-tool list, and machine class are
frozen in `metadata/config.json` and `metadata/environment.json`.
The model preset is `gpt-5.6-sol`/`ultra`, including full V2 automatic task
delegation. The strict Codex configuration permits at most four concurrent
root/subagent inference threads in a session, locks every child to the same
model and Ultra effort, and hides spawn-time model, effort, and agent metadata
overrides. The root thread is materialized only inside a unique per-attempt
temporary state directory because the frozen Codex 0.146 MultiAgentV2 runtime
cannot resolve an ephemeral coordinator when spawning a child.
`history.persistence=none` remains fixed. The temporary state directory is
deleted on normal adapter exit and is never reused or mounted by another
attempt, including after an abnormal stop.
The configuration also freezes the exact `fork_turns` usage hint and a
synchronous pre-tool-use policy hook. Only omitted, `"all"`, and `"none"` are
available; positive integers and malformed values are blocked before child
creation. Generate the helper and `hooks.json` under the private attempt state
root, mount them read-only into the temporary Codex home, and authenticate both
hashes. Freeze the CLI hook-trust-bypass flag separately from the effective
`thread/start.params.config={"bypass_hook_trust":true}` setting; the latter is
the pinned app-server's effective trust source.
The selected backend has no demonstrated random-seed control, and the runner
uses fresh bubblewrap namespaces rather than a frozen OCI container image. An
OCI image is a packaged operating-system environment. These two differences are
recorded explicitly with the private measurements. They do not authorize a
public release.

The buffering/reservation provider gate and its call-atomic exclusive token
endpoint are also an explicit HighamBench execution-protocol amendment, not a
feature enforced by the frozen Codex binary. Apply the identical gate source,
configuration, model catalog, transport provenance, and endpoint checks to N
and L. Together with the `signposted-library-v1`, unavailable-seed, and
non-containerized execution deviations above, this means the measurements must
not be labeled strict reference-PDF HighamBench 0.2 results; report them as an
amended HighamBench-derived protocol.

## 6. Run the two conditions fairly

The signposted comparison deliberately estimates the effect of explicit,
neutral NumStability availability, not silent library discovery. L is told the
snapshot identity, paths, and generic search/import mechanics; N receives no
supplement and no library mount. No target-specific retrieval hint is allowed.
All other prompt text and all task/context bytes remain fixed between the pair.

For each task and repetition:

1. Start the first condition shown in `metadata/run_order.json` in a new
   bubblewrap namespace and new conversation.
2. Require all descendants to be quiescent. The root coordinator writes and
   locally checks `Candidate.lean`, then emits one sole/final outer custom `exec`
   item whose exact 104-byte program is
   `// @exec: {"yield_time_ms": 2400000}` followed by a newline and
   `text(await tools.submit_proof({candidate_path:"Candidate.lean"}));` followed
   by a newline. The `text` wrapper exposes a rejection for repair and retry.
   App-server
   starts the nested root-only `submit_proof` dynamic call. Direct creation of
   the runner-owned `Submission.lean` is forbidden.
3. At the authenticated inner call, snapshot `Candidate.lean` and bind its hash
   to the outer raw-item/exec identities, inner call identity, their observed
   ordering, run nonce, validator contract, response, and exact rooted-tree usage
   ledger. Validate those immutable bytes in a pristine hidden workspace. On
   acceptance, leave the inner call blocked: send no inner tool response, emit
   no outer exec output, and terminate the app-server out of band, making later
   model work impossible. Record first-valid time from the authenticated RELEASED
   pre-write timestamp to nested-boundary publication after the same outer raw
   response completes, not to the earlier candidate-capture event. Authenticate
   that the exec timer starts no earlier than prompt release and that its exact
   2,400,000-ms yield exceeds the 1,800-second measured limit plus the 369-second
   validation/teardown reserve by 231 seconds. Treat any outer progress output
   as forbidden post-boundary activity, never as ignorable transport noise.
4. Independently bind every child to
   `raw_function_call.call_id = subAgentActivity.id`. Recompute projection-v6
   expected inherited baselines, raw sums, full/exception-adjusted cumulative
   projections, observations, spawn-ID sets, and completeness Booleans. Require
   exactly one authenticated hook start/completion pair for every raw spawn,
   independently rederive allow/block decisions, and require every blocked call
   to be failed with no activity, collaboration record, or child. Only
   the accepted root outer response at the authenticated nested boundary may be
   exempted; a natural outcome requires every thread's full projection.
   Additionally use the authenticated provider-gate ledger as the authoritative
   response count and token total. Reconcile every gate call to either a direct
   app-server delivery, the narrow suppressed collaboration-wait case with
   successor child-result evidence, a collaboration-message supersession, or
   a completed child response discarded after an authenticated explicit parent
   interrupt. Count every provider response without changing the raw app-server
   ledger.
5. Authenticate each accepted or rejected validation record to the exact
   candidate, run/task/theorem, controlled manifest, validator contract, and
   Ultra request hash/sequence. Record both its canonical self-hash and the
   validation file's byte hash.
6. Route every counted `POST /responses` request through
   `highambench-provider-token-gate-v6`. Admit concurrent requests only while
   the frozen worst-case reservation is strictly below the cap; otherwise drain
   them and admit one exclusive response. A token crossing must be that sole
   in-flight response, expose no action-capable output, close the gate with
   reason `token_limit`, and produce an authenticated mode-0444 final artifact
   plus clean adapter teardown. Require status 200, request
   `Accept: text/event-stream`, and accept only absent/single identity content
   encoding plus absent/single `text/event-stream` content type with optional
   UTF-8 charset. A missing content type is compatible only after the complete
   body passes the frozen strict byte-level SSE parser; bind its body hash/size,
   response identity, event/completion/`[DONE]` counts, header bases, and the
   downstream synthesized-content-type flag. Do not infer SSE validity from the
   endpoint or request headers. Apply this same compatibility rule to N and L;
   it does not change the gate amendment's condition symmetry. For an explicit
   child-interrupt discard, do not order the two provider admissions relative
   to each other: require both before the parent interrupt response commits,
   require its direct bind before the child response commits, and require the
   child admission before the first authenticated interrupt lifecycle event
   with every full millisecond event interval before the child commit. This
   exact endpoint is the only failure that
   need not naturally drain the model tree. Every other failure with no accepted
   boundary requires a natural exact tree drain.
7. Save the raw log without showing it to the paired run.
8. Destroy the namespace, temporary agent state, and generated caches.
9. Start the second condition in another new namespace and conversation.

Before each model turn, require the authenticated
`highambench-prompt-release-v1` READY/GO/RELEASED handshake. READY proves that
the adapter is prepared but has not sent the prompt. The runner issues GO only
with at least five seconds left in the separate 120-second startup window.
RELEASED records monotonic and Unix timestamps immediately before the exact
`turn/start` write and a post-flush timestamp. Reauthenticate the three
canonical, mode-0444 artifacts, their self/file hashes, the prompt and request
wire, nonce, identities, and command paths. Derive the 1,800-second measured
deadline only from RELEASED. A pre-GO timeout has no useful work; any post-GO
handshake ambiguity is an unscored SYSTEM_ERROR incident and is not retried.

Before starting either member of a pair, reserve the full bounded tail for
every unfinished run. The frozen per-run post-submission reserve is 369 seconds:
two 120-second compilations, one 120-second dependency audit, a five-second
accepted-adapter close, and two two-second termination grace windows. The
allocation requirement is
`unfinished * (1800 + 2*120 + 369) + 600`; therefore an untouched N/L pair
requires 5,418 seconds. The 600-second term remains general overhead rather
than absorbing known validation work.

For the current private P01 completion campaign, apply the temporary
`same-authenticated-slurm-allocation-within-pair-v1` hardware policy. Request a
singleton allocation on exactly one of `watgpu108`, `watgpu508`, or `watgpu808`
with one task, four CPUs, 32 GiB, and no GPU. Bind both N and L for a
task/repetition pair to the exact same authenticated Slurm job/allocation
descriptor. A later allocation may resume only at a complete pair boundary;
never finish the second member of a pair under a different allocation. Complete
pairs may use different vetted nodes, so paired L-minus-N timing differences are
the principal estimand and absolute/cross-pair times remain descriptive. Record
this relaxation as a private protocol deviation rather than a strict
reference-PDF HighamBench 0.2 measurement.

Implement each N/L pair as one path-stable transaction. Create each attempt at
its permanent campaign path before invoking the provider; never rename it.
Commit it only after both finals and the immutable pair commit authenticate.
Index every deadline, setup-error, terminal, and interrupted attempt as retained
audit evidence. Any later attempt at an uncommitted pair starts both N and L
fresh; never reuse only the successful condition from an incomplete attempt.
The final report must authenticate and disclose all failed pair attempts. This
pair-level resampling rule is an additional private protocol amendment.

Keep the batch script node-agnostic and select exactly one vetted host in the
submission command, for example:

```text
sbatch --nodelist=watgpu108 \
  paper_bencmark/scratch_pad/run_highambench_p01_actual_ultra.sh
```

Substitute `watgpu508` or `watgpu808` only as a singleton. Do not supply a
three-host `--nodelist` to a one-node job. A later four-hour job may use another
vetted node because the campaign resumes only after a complete authenticated
pair.

Authenticate all saved retry incidents before any later provider subprocess.
Each incident carries a canonical `matrix_incident_sha256` plus exact source
attempt, transcript, assignment, attempt number, freeze, agent, environment,
hardware, and immutable attempt-log bindings. Only a resolved attempt-1
pre-prompt SYSTEM_ERROR followed by an authenticated attempt-2 final may
coexist with continued measurements. Terminal, unscorable, and incomplete
retry records block resume.

Do not pass messages, files, build output, searches, caches, or knowledge from
one condition to the other.

The earlier raw-access P01 measurements predate `signposted-library-v1` and
answer a different question. Preserve them under their existing result root,
but never pool them with, overwrite them by, or count them as repetitions of a
signposted P01 run. Every signposted rerun starts fresh and receives distinct
prompt and environment provenance while retaining the exact same P01 target
statements and contexts.

## 7. Record measurements

For every run record:

- pass or fail;
- real wall-clock stop time;
- scored time, using 1,800 seconds for a failure;
- input, output, cached-input, and total model-token counts;
- the deduplicated completed-response count and rooted Ultra thread-tree
  accounting status, exact spawn bindings, inherited cumulative baselines, and
  projection-v6 policy, provider-delivery reconciliation, and accounting completeness;
- whether a passed L proof truly depends on NumStability;
- the library declaration names used;
- one failure code and a short explanation when the run fails.

Use the failure-code order from HighamBench 0.2. A timeout remains
`TIME_LIMIT` even when the last Lean file also has an error.
A denied socket call is recorded outside the evaluated process and prevents a
pass, including when the proof passes Lean validation. It becomes
`RULE_VIOLATION` unless `TIME_LIMIT`, `TOKEN_LIMIT`, or `NO_SUBMISSION` has the
higher-priority label. A clean agent exit with no proof remains
`NO_SUBMISSION`; failure to start the agent is a measurement-system error
rather than an agent omission.

The trusted token ledger uses app-server `rawResponse/completed` events for the
root and every recursively linked child. It deduplicates by response ID and
counts cached input once. A passing run is exact at the accepted schema-v5
nested boundary: the model's sole/final raw tool item is the frozen outer custom
exec, app-server has observed the exact inner `submit_proof` call, and the same
outer raw response has completed. Asynchronous delivery may expose either
`inner_dynamic_call_before_raw_response_completed` or
`raw_response_completed_before_inner_dynamic_call`; schema v5 requires exactly
one matching Boolean order flag, timestamps consistent with the enum, and both
events no later than boundary publication. `drain_complete=false`, the inner call and root
remain blocked, descendants are quiescent, no inner result or outer exec output
is emitted, and no later response is possible. The retained challenge, call,
request, acknowledgement, and candidate snapshot are sealed mode 0444 and
reauthenticated during result checking. A natural failed run instead requires
`drain_complete=true` and rooted-tree quiescence. The explicit `TOKEN_LIMIT`
exception is exact at the sealed gate-v4 endpoint: the crossing is the sole
in-flight response, its action-capable output is suppressed, the gate is closed
and quiescent, its final artifact is mode 0444, and adapter teardown completes
immediately. The tree may remain active and cumulative projection may remain
incomplete. Because admission becomes exclusive before the cap crossing, no
concurrent tail is possible and overshoot is bounded by one 272,000-token
provider response. Missing or inconsistent endpoint evidence produces an
unscored `unscorable_useful_work` incident with no retry. A real Ultra
boundary canary must pass under the frozen compatible-host policy before any
scored run.
That synthetic canary completes a root response, proves that a root
`fork_turns="3"` call is denied with no child, then performs one allowed
`fork_turns="all"` delegation. The allowed child must prove a second
`fork_turns="3"` denial with no grandchild before returning its marker. Replay
must authenticate both hook denials and rederive a positive child baseline. Its
synthetic proof also passes the production hidden semantic/dependency audit;
the exact audit argv is part of the validator contract and the frozen
`dependency_audit.lean` helper is retained and hashed. The separate 14-artifact
canary is `TOKEN-CONTROL-SYNTHETIC-PROVIDER-GATE-V8` under protocol
`synthetic-inert-sanitized-provider-gate-compaction-crossing-v8`. It uses only a
synthetic non-matrix target and inert prompt. At its fixed 180,000-token cap, a
first normal root response must finish below the cap and be released
byte-for-byte; the adapter then sends `thread/compact/start`, and a distinct
compaction-turn response must be the sole crossing. Only the canonical inert
`Compaction` completion and minimal completed event may cross. Its projection-v6
ledger authenticates the event-ordered two-response sequence, both gate-call
direct deliveries, provider-authoritative totals, the closed endpoint, final
mode-0444 artifact, and immediate
teardown. Spawn/hook sets are empty, while tree drain and cumulative projection
completion are intentionally false. Its attestation fixes
`scored=false`, `matrix_assignment=false`, `synthetic_input=true`, and
`benchmark_task_bytes_used=false`; neither canary may expose a benchmark task,
context, target, or proof prefix.

Canaries authenticate the frozen control protocol, not benchmark performance.
Do not build a per-node result cache: reauthenticate the promoted evidence on
every allocation, require fresh live canaries after any frozen software or
protocol change, and authenticate the actual transport evidence for every
scored run. The exact within-pair allocation binding then also binds N and L to
one node-local transport fingerprint.

This is private pre-publication measurement work. Passing construction,
canary, and measurement gates does not authorize publishing or releasing any
artifact.

## 8. Analyze without hiding runs

Report all 36 assignments. Do not choose the best repetition.

For N and L, report overall and by T1, T2, and T3:

- scored runs, passes, and pass rate;
- median scored time;
- median token count;
- each failure-code count;
- for L, passed runs that actually use NumStability.

For each matching task and repetition, calculate L minus N. Report the pass-rate
change and the median of paired time and token changes. Do not combine these
different measures into one score.

The full specification asks for a 95 percent range by resampling whole papers.
With only P01 and P02, this range has extremely limited resolution. Keep all
three tiers from a paper together and label the two-paper limitation plainly.

## 9. Complete two reviews

Two separate review records cover every task:

- Reviewer 1 checks the paper citation, meaning, proof context, and tier choice.
- Reviewer 2 checks the neutral Lean interface, existing-library overlap,
  condition isolation, hashes, and validator readiness.

The first records were preliminary reviews. After the build, isolation, search,
and construction evidence is frozen, two separate final review passes must
replace them. A status changes to `pass` only when saved evidence supports it.

## 10. Completion checklist

- [x] The current manifest contains P01 and P02; the construction corpus may
  grow before measurement.
- [x] T1, T2, and T3 are selected for both papers before evaluation.
- [x] Source and specification PDFs are hashed.
- [x] Lean, mathlib, and NumStability source versions are frozen.
- [x] Limits and three repetition IDs are fixed.
- [x] Pair order is fixed by a repeatable rule.
- [ ] Two review records cover all six tasks against current evidence.
- [x] All six final fixed Lean statements compile in both clean conditions.
- [x] Exact controlled task hashes and the construction-package hash describe
  the current regenerable construction snapshot.
- [x] N is rechecked to contain no NumStability artifact for every task.
- [ ] L dependency checking finds real declarations in all six private L construction proofs.
- [x] Agent, model, prompt, tools, and machine class are frozen.
- [x] The lack of a backend seed and OCI image is recorded as a concrete limitation.
- [ ] Two final independent review records pass for every task against one
  measurement-ready snapshot.
- [ ] All 36 isolated runs are complete.
- [ ] Raw logs, result tables, and the final plain-language PDF report are built.
