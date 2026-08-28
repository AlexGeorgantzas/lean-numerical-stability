# HighamBench construction corpus

This directory contains a 20-paper construction corpus for testing whether
access to the NumStability Lean library helps an agent finish fixed Lean proofs.
A fixed proof means that the theorem statement is chosen before a run and the
agent may change only the proof.

The working corpus contains 61 task packages drawn from papers P01--P20: the
legacy T1--T3 selection contributes 60, and P01 additionally contains one T4
whole-paper task. The current paper/task records are in construction phase, not
measurement-ready. Earlier 60-task construction/review evidence belongs to the
legacy T1--T3 snapshot and does not attest the current 61-task paper-local
architecture. Current readiness is established independently by authenticated
bundle, construction, and, where T4 applies, review receipts under
`metadata/papers/P0X/`.

## Task types

Each paper contributes one task of each type used by the HighamBench 0.2
specification:

- T1, direct use: apply or specialize a close existing NumStability result.
- T2, combine: join multiple existing results with additional reasoning.
- T3, extend: prove a result requiring material not already supplied as a
  complete NumStability theorem.
- T4, whole paper: represent the paper's complete precise-claim inventory with
  designated proof holes, private N/L solvability, and faithfulness review.

Every paper has T1--T3; P01 currently also has T4.

The manifest and per-task records contain each selected result, source tag,
paper location, fixed Lean statement, and task-specific rationale.

## Papers

| ID | Authors | Paper | Year |
| --- | --- | --- | --- |
| `P01` | Nicholas J. Higham | [The Accuracy of Floating Point Summation](https://doi.org/10.1137/0914050) | 1993 |
| `P02` | Takeshi Ogita, Siegfried M. Rump, and Shin'ichi Oishi | [Accurate Sum and Dot Product](https://doi.org/10.1137/030601818) | 2005 |
| `P03` | Erin Carson and Nicholas J. Higham | [Accelerating the Solution of Linear Systems by Iterative Refinement in Three Precisions](https://doi.org/10.1137/17M1140819) | 2018 |
| `P04` | Pierre Blanchard, Nicholas J. Higham, Florent Lopez, Theo Mary, and Srikara Pranesh | [Mixed Precision Block Fused Multiply-Add: Error Analysis and Application to GPU Tensor Cores](https://doi.org/10.1137/19M1289546) | 2020 |
| `P05` | Siegfried M. Rump and Claude-Pierre Jeannerod | [Improved Backward Error Bounds for LU and Cholesky Factorizations](https://doi.org/10.1137/130927231) | 2014 |
| `P06` | Michael P. Connolly and Nicholas J. Higham | [Probabilistic Rounding Error Analysis of Householder QR Factorization](https://doi.org/10.1137/22M1514817) | 2023 |
| `P07` | Maike Meier, Yuji Nakatsukasa, Alex Townsend, and Marcus Webb | [Are Sketch-and-Precondition Least Squares Solvers Numerically Stable?](https://doi.org/10.1137/23M1551973) | 2024 |
| `P08` | Robert D. Skeel | [Iterative Refinement Implies Numerical Stability for Gaussian Elimination](https://www.jstor.org/stable/2006197) | 1980 |
| `P09` | George U. Ramos | [Roundoff Error Analysis of the Fast Fourier Transform](https://doi.org/10.1090/S0025-5718-1971-0300488-0) | 1971 |
| `P10` | James Demmel, Ioana Dumitriu, and Olga Holtz | [Fast linear algebra is stable](https://doi.org/10.1007/s00211-007-0114-x) | 2007 |
| `P11` | Alicja Smoktunowicz, Jesse L. Barlow, and Julien Langou | [A note on the error analysis of classical Gram–Schmidt](https://doi.org/10.1007/s00211-006-0042-1) | 2006 |
| `P12` | Marko Lange and Shin'ichi Oishi | [A note on Dekker's FastTwoSum algorithm](https://doi.org/10.1007/s00211-020-01114-2) | 2020 |
| `P13` | Nicholas J. Higham | [The numerical stability of barycentric Lagrange interpolation](https://doi.org/10.1093/imanum/24.4.547) | 2004 |
| `P14` | Pierre Blanchard, Desmond J. Higham, and Nicholas J. Higham | [Accurately computing the log-sum-exp and softmax functions](https://doi.org/10.1093/imanum/draa038) | 2021 |
| `P15` | Nicholas J. Higham and Theo Mary | [Solving block low-rank linear systems by LU factorization is numerically stable](https://doi.org/10.1093/imanum/drab020) | 2022 |
| `P16` | Alfredo Buttari, Nicholas J. Higham, Theo Mary, and Bastien Vieublé | [A modular framework for the backward error analysis of GMRES](https://doi.org/10.1093/imanum/draf049) | 2026 |
| `P17` | El-Mehdi El Arar, Massimiliano Fasi, Silviu-Ioan Filip, and Mantas Mikaitis | [Probabilistic Error Analysis of Limited-Precision Stochastic Rounding](https://doi.org/10.1137/24M1681458) | 2025 |
| `P18` | Zachary J. Grant | [Perturbed Runge–Kutta Methods for Mixed Precision Applications](https://doi.org/10.1007/s10915-022-01801-2) | 2022 |
| `P19` | Alfredo Buttari, Xin Liu, Theo Mary, and Bastien Vieublé | [Mixed precision strategies for preconditioned GMRES: a comprehensive analysis](https://hal.science/hal-05071696v2) | 2026 |
| `P20` | Theo Mary and Mantas Mikaitis | [Error Analysis of Matrix Multiplication with Narrow Range Floating-Point Arithmetic](https://doi.org/10.1137/24M1685109) | 2025 |

The local paper PDFs are recorded source copies and remain subject to their
publishers' terms. The benchmark metadata records source locators and hashes and
uses short paraphrases instead of copying long passages from the papers.

## Independent construction workflow for every paper

Each paper is a complete construction shard. Its only custom Lean dependency is
`shared/HighamBench/P0XDefinitions.lean`, which imports frozen upstream
`Std`/`Mathlib` modules directly and contains every custom semantic declaration
needed by that paper. Targets import exactly their own definition module. They
do not import `Core`, `SemanticCore`, or another paper, and each trusted bundle
contains only its own compiled definition module.

Distinct paper IDs can therefore be extracted, proved, reviewed, bundled, and
registered concurrently. A paper session validates only its own task records
and finishes by atomically publishing
`metadata/papers/P0X/registration.json`; it never rewrites the central manifest,
environment, run order, release list, or another paper's controlled manifest.
Consumers discover valid receipts in paper-ID order and compose a deterministic
catalog in memory, so no later merge or serialized refresh is required.

For T4, claim the paper-local writer lease into an owner-only credential file,
then initialize the generic paper-local workspace before any other write. Its
descriptor hash-binds the source PDF and the shared read-only schemas and
pending templates under `schemas/` and `templates/T4/`:

```bash
lease_credential_dir="$(mktemp -d /tmp/highambench-P0X-lease.XXXXXXXX)"
lease_credential_file="$lease_credential_dir/credential.json"
python3 paper_bencmark/highambench/tools/t4_writer_lease.py claim \
  --scratch-root paper_bencmark/scratch_pad --paper-id P0X \
  --credential-out "$lease_credential_file"
python3 paper_bencmark/highambench/tools/t4_workspace.py init \
  --benchmark-root paper_bencmark/highambench \
  --reference-root paper_bencmark/reference_papers \
  --scratch-root paper_bencmark/scratch_pad --paper-id P0X \
  --lease-credential-file "$lease_credential_file"
```

Pass the same file to later lease-guarded writes. Workspace `check` is
read-only and verifies bindings, not metadata or stage readiness. Release the
lease after the final write; successful release removes the credential file.

After synchronizing the canonical external inventory with the embedded task
view, freeze and check only that paper's T4 metadata:

```text
python3 paper_bencmark/highambench/tools/t4_metadata.py write-set \
  --benchmark-root paper_bencmark/highambench --paper-id P0X
python3 paper_bencmark/highambench/tools/t4_metadata.py freeze \
  --benchmark-root paper_bencmark/highambench --paper-id P0X
python3 paper_bencmark/highambench/tools/t4_metadata.py check \
  --benchmark-root paper_bencmark/highambench --paper-id P0X
```

During construction, validate the paper shard and preview the finalizer's exact
paper-local write set:

```text
python3 paper_bencmark/highambench/tools/task_tags.py \
  --benchmark-root paper_bencmark/highambench --paper-id P0X
python3 paper_bencmark/highambench/tools/finalize_paper.py \
  --benchmark-root paper_bencmark/highambench \
  --paper-id P0X --phase construction --dry-run
```

A construction-phase finalizer receipt is a draft until the paper-local
construction checker authenticates the private N/L proofs. T4 additionally
requires authenticated faithfulness-review evidence. Only then may the same
paper be switched to measurement-ready; `classification_frozen_before_runs`
remains `false` before that point. Corpus-wide JSON files are legacy
compatibility views, not construction-session write targets.

## Two conditions

- `N` means no NumStability library. No source, compiled library file,
  documentation, search index, declaration-name list, or cache from the library
  may be visible.
- `L` means the frozen NumStability source and compiled files are available for
  local use and local search.

Both conditions for a task use the same fixed statement, source material,
paper-scoped task definitions, Lean version, mathlib revision, common agent
prompt, tools, time limit, token limit, and machine class. The controlled
condition-L supplement described below is the only intended prompt difference.
Each attempt starts in a new bubblewrap
namespace, meaning a fresh restricted view of files and processes, and a new
conversation. Model-generated shell commands cannot create network sockets.
The shell supervisor records denied socket activity in a per-run marker. The
outer runner watches that marker with a separate kernel event queue, so deleting
or clearing the file cannot hide an earlier change. Any recorded attempt is a
failure, even when the Lean proof itself is valid. It is labeled
`RULE_VIOLATION` unless a time limit, token limit, or missing submission has the
higher-priority failure label. The launcher also blocks attempts to signal its
supervisor and closes inherited file handles before starting Bash.
Both conditions see the same separately staged package runtime: mathlib Lean
source files plus each package's base `.olean` files and the matching
`.olean.server`, `.olean.private`, and `.ir` support files needed by Lean 4.29.
No other package-build files are staged. The original `.lake/packages`
checkout, its Git data, build traces, and caches are not mounted in an attempt.

### Frozen condition-L prompt supplement

Prompt protocol `signposted-library-v1` uses `agent_prompt.md` as the common
prompt and appends the byte-frozen `condition_prompts/L.md` only in condition
L. Condition N receives no condition supplement: the L file is not passed to
its adapter and is not staged or mounted in its namespace.

The L supplement explicitly says that the agent may search and use the frozen
NumStability snapshot at commit
`45813a95dacf577461bae13f033af0dbc985a225`. Inside the L namespace its exact
read-only locations are:

- source tree: `/library/NumStability`;
- root source file: `/library/NumStability.lean`;
- compiled Lean tree: `/library-olean`.

The supplement explains that `/library-olean` is already on `LEAN_PATH`, that
only modules with a corresponding `.olean` below that tree are importable, and
how a compiled path maps to a dotted Lean import. It gives generic local
`find`, `rg`, `import`, `#check`, and `#print` command templates. It supplies no
target-relevant theorem, module, declaration, search term, adapter, or private
proof hint; the agent must discover relevance itself. Source-only files may be
searched but are not added to the importable object set.

The trusted adapter composes the L request in this order: common prompt, L-only
supplement, task context, fixed target. The condition supplement changes
neither `context.md` nor `Target.lean`, and it changes no task statement or
shared definition. An L submission may add a NumStability import, but the
controlled target remains byte-identical to N. Any supplement edit changes the
controlled hashes and environment identity and requires a fresh measurement.

The Codex control process still needs its provider connection, and this setup
uses fresh bubblewrap namespaces rather than a frozen OCI container image.
Those concrete limitations are recorded with the measurements. All results are
private preparation artifacts and are not approved for public release.

The frozen agent preset is `gpt-5.6-sol` with reasoning effort `ultra`. Full
Ultra V2 automatic task delegation is enabled. At most four root/subagent
inference threads may run concurrently in one attempt. Every child is locked
to `gpt-5.6-sol`/`ultra`; the model and reasoning-effort override fields are
hidden from `spawn_agent`, as is spawn-agent metadata. These locks are part of
the environment identity, not choices left to an evaluated agent.

The same configuration presents an exact usage hint: `fork_turns` must be
omitted (the full-history default), `"all"`, or `"none"`; positive integers
and every other value are unavailable. A synchronous pre-tool-use hook enforces
that rule before child creation. Its generated helper and `hooks.json` are
SHA-256-frozen, staged under the private per-attempt state root, and mounted
read-only at their recorded paths in the temporary Codex home. The CLI carries
the frozen hook-trust-bypass flag, while the pinned app-server obtains the
effective bypass from `thread/start.params.config={"bypass_hook_trust":true}`.
Those two trust inputs and the effective source are separate frozen fields.

The fixed measured limit is 1,800 seconds and 5,000,000 total model tokens per
run. The 5,000,000-token cap is the current user-authorized protocol deviation
from the earlier 2,000,000-token project freeze and is applied identically to N
and L. A separate 120-second prompt-startup timeout does not consume that measured
wall-clock allowance. A model token is a small piece of text counted by the
model service. Failed runs receive 1,800 seconds in the main time comparison,
while their real stop time is also kept.

Every attempt uses the authenticated `highambench-prompt-release-v1` READY/GO/
RELEASED handshake. The isolated adapter first seals a READY record before it
starts the model turn. The runner verifies READY and authorizes GO only when at
least five seconds of the startup window remain. Immediately before writing the
exact `turn/start` request, the adapter records RELEASED with a monotonic
timestamp, then records the post-flush timestamp. The runner reconstructs and
hash-checks the request wire, identities, prompt bytes, nonce, and command-line
paths, and re-reads all three canonical JSON artifacts as regular, non-symlink,
mode-0444 files. The measured 1,800-second deadline is derived only from the
authenticated RELEASED pre-write timestamp. A timeout before GO starts no useful
work; missing or invalid evidence after GO is retained as an unscored system
incident rather than retried as if no work occurred.

The only automatic retry is one failure proven to occur before prompt release.
Its incident record is canonically self-hashed and binds the exact normalized
attempt record, raw transcript, frozen assignment/environment/hardware, and
attempt-specific immutable log copies. On every resumption these records are
replayed before any provider subprocess starts. A terminal, unscorable, or
incomplete retry incident remains a hard stop even if an active-run marker was
removed.

The adapter consumes `rawResponse/completed` events from Codex app-server and
sums the provider usage of every completed response in the rooted attempt
thread tree. Response IDs are deduplicated across the root and all recursively
linked Ultra children. A response's input total already includes its cached
input portion, so cached input is charged once rather than added a second time.
Projection schema v4 binds each child to the exact raw `spawn_agent` function
call by requiring `raw_function_call.call_id = subAgentActivity.id`. For a
`fork_turns=all` child, the expected inherited cumulative baseline is the
parent's expected baseline plus all completed parent responses preceding the
spawn response; `fork_turns=none` has the exact zero baseline. The runner, the
result-set checker, and the report renderer separately recompute the expected
baseline, full and boundary-adjusted projection, final cumulative observation,
spawn-ID sets, and graph-completeness Booleans. It also requires exactly one
authenticated `hook/started` and one authenticated `hook/completed` event for
every raw spawn call. Omitted, `"all"`, and `"none"` calls must be allowed;
positive-integer or malformed calls must be policy-blocked, recorded as failed,
and have no activity, collaboration record, or child. The adapter, runner,
result-set checker, and both report renderers independently authenticate the
policy fingerprint and rederive those per-call decisions. Every naturally
drained thread must match its full app-server projection. Schema v4 uses the
authenticated provider-gate response ledger as the authoritative token total
and reconciles every response either to a direct app-server delivery or to the
narrow suppressed collaboration-wait case with successor child-result evidence.
The raw app-server response and cumulative ledgers remain unchanged structural
evidence; suppressed-response tokens are not folded into them. Only the accepted
root response may use the narrow
authenticated nested-submission exception; a token-limit endpoint uses the
separate sealed provider-gate crossing described below.
The adapter atomically writes the live cumulative ledger to a trusted result-log
path outside the model's workspace. For an Ultra pass, the coordinator first
waits until every descendant is quiescent, develops and checks the fixed
`Candidate.lean`, and then emits one sole/final outer custom `exec` item with the
exact 104-byte program
`// @exec: {"yield_time_ms": 2400000}` followed by a newline and
`text(await tools.submit_proof({candidate_path:"Candidate.lean"}));` followed by
a newline. The `text` wrapper exposes a rejected inner call to the model so it
can repair and retry. App-server starts
the nested root-only `submit_proof` dynamic call while that outer exec remains
unresolved. The adapter snapshots the candidate bytes at the inner call and
authenticates both the outer and inner identities, their ordering, the run nonce,
validator contract, root thread, response, and current deduplicated usage ledger.
Only the root coordinator may submit. The hidden runner validates that immutable
snapshot in a pristine frozen workspace.

Every accepted or rejected hidden-validation record is bound to the run, task,
candidate bytes, target theorem, controlled manifest, validator contract, and,
for Ultra, the authenticated request hash and sequence. The record has a
canonical self-hash, while the run separately records the validation file's
byte hash. Passing records therefore authenticate the exact immutable candidate
that reached the blocked boundary; a rejected candidate remains auditable even
when the attempt later ends without an accepted proof.

On acceptance, the runner deliberately leaves the inner dynamic call blocked:
it sends no inner tool response, emits no outer exec output, and terminates the
app-server out of band. The root turn therefore remains blocked, all descendants
remain quiescent, and no later model response is possible. The exact passing
total includes the completed outer response containing that custom exec item and
stops there. `drain_complete=false` is therefore expected for a pass: exactness
comes from the authenticated schema-v5 nested boundary, not a natural tree drain.
Schema v5 records exactly one of two asynchronous observation orders:
`inner_dynamic_call_before_raw_response_completed` or
`raw_response_completed_before_inner_dynamic_call`. The matching two Boolean
flags must be exclusive, the monotonic timestamps must agree with that enum,
and both the inner-call observation and raw-response completion must precede
boundary publication.
The exact 2,400,000-ms yield is transport-only: it does not extend the measured
deadline. Its timer begins no earlier than authenticated prompt release, and it
strictly exceeds the 1,800-second measured interval plus the 369-second
validation/teardown reserve by 231 seconds. Any outer progress output remains
forbidden and invalidates the boundary.
First-valid time is the interval from the authenticated RELEASED pre-write
timestamp to publication of that boundary after completion of the same outer raw
response. The retained request record is self-hashed and its publication
timestamp is cross-bound to the usage-boundary summary; the earlier candidate
capture at inner-call start is not the scored endpoint. Hidden validation time
is recorded separately.
The allocation gate reserves a separate, non-scored 369 seconds for every
unfinished run: two 120-second Lean compilations, one 120-second dependency
audit, the five-second accepted-boundary close, and two two-second forced-stop
grace windows. Together with two possible 120-second pre-prompt startup
windows and the 1,800-second measured interval, an untouched N/L pair requires
5,418 seconds including the separate 600-second general-overhead guard. The
matrix stops before starting the pair when the enclosing Slurm allocation has
less time remaining.

The private P01 completion campaign temporarily uses
`same-authenticated-slurm-allocation-within-pair-v1`. Its launcher requests one
node from the exact vetted set `watgpu108`, `watgpu508`, and `watgpu808`, then
authenticates that the actual grant is a singleton allocation with one task,
four CPUs, 32 GiB, and no GPU. Both conditions of a task/repetition pair must
carry the same authenticated Slurm allocation descriptor; a half-finished pair
cannot continue in a later allocation. Complete pairs may use different vetted
nodes. Thus the within-pair L-minus-N contrasts are the principal timing
estimand, while absolute and cross-pair elapsed times are descriptive under
heterogeneous hardware. This is a private protocol deviation and is not a
strict reference-PDF HighamBench 0.2 score.

Campaign execution treats a whole N/L pair as the transactional sampling unit.
Every attempt is created at a permanent path before provider work and is never
moved. Only an attempt with both authenticated finals and one immutable pair
commit enters the measured set. Deadline, terminal, setup-error, and interrupted
attempts remain self-hashed and indexed for audit; an incomplete or failed pair
is never completed piecemeal, and a later attempt reruns both N and L freshly.
The final private report lists and authenticates every retained failed attempt,
making this pair-level resampling amendment explicit rather than silently
selecting successful conditions.

The generic batch script intentionally has no `#SBATCH --nodelist` directive.
Choose one currently available vetted node and pass exactly that singleton at
submission time, for example:

```text
sbatch --nodelist=watgpu108 \
  paper_bencmark/scratch_pad/run_highambench_p01_actual_ultra.sh
```

`watgpu508` or `watgpu808` may replace `watgpu108`; never pass all three names
in one `--nodelist`, because Slurm may interpret the list as required hosts for
the one-node job. If the four-hour allocation ends before all nine pair commits,
submit the same command again on any one vetted node. The stable campaign index
retains completed pairs and resumes only at an authenticated pair boundary.

Every counted `POST /responses` request passes through the frozen loopback
provider gate under `highambench-provider-token-gate-v6`. The gate authenticates
the model catalog, Ultra effort, 272,000-token response bound, request metadata,
direct TLS transport, and each app-server usage notification. It admits
concurrent work only while
`completed_tokens + (open_request_count + 1) * response_bound < token_limit`.
When that reservation would reach the cap, it first drains existing provider
requests and then admits at most one exclusive response.

Gate v6 requests `Accept: text/event-stream`, requires status 200 and identity
content encoding, and accepts at most one `Content-Type` and one
`Content-Encoding` occurrence. A declared content type must be exactly
`text/event-stream` with at most an optional UTF-8 charset. A missing
`Content-Type` is compatible only after the complete upstream body passes the
frozen strict byte-level SSE parser; the receipt binds the parser, event counts,
completion position, optional `[DONE]`, body byte count/hash, response ID,
header-presence bases, and downstream synthesized-content-type flag. Endpoint
or request headers alone never authenticate an untyped body. This transport
compatibility amendment and every gate check remain identical for N and L.

At the first completed total greater than or equal to 5,000,000, that response
must therefore be the sole in-flight request. The gate seals the exact crossing
and releases no action-capable model output: an ordinary turn receives only a
minimal sanitized completion, while a compaction request receives exactly one
inert `Compaction` completion item followed by the minimal completion needed by
the pinned app-server collector. It then closes with reason `token_limit`.
Projection v6 authenticates each gate call's response-output manifest and
delivery record, then reconciles provider-authoritative totals against direct
app-server responses, authenticated suppressed collaboration waits,
collaboration-message supersessions, and child responses discarded only after
an exact parent `interrupt_agent` sequence. It also authenticates the
interrupt chronology without assuming which provider request was admitted
first: both the child and interrupting parent requests must be admitted before
the parent response commits, that response must be directly bound before the
child response commits, the child must have been admitted before the first
interrupt lifecycle event, and every such event's full millisecond interval
must precede the child commit. It also authenticates the
event-ordered response IDs, final mode-0444 gate artifact, and immediate clean
adapter teardown. A scoreable `TOKEN_LIMIT`
endpoint need not claim a natural tree drain;
provider requests and handlers are quiescent even though the model tree remains
active. Overshoot is bounded by the one frozen-bound exclusive response, and no
concurrent response tail is possible. Other unsuccessful outcomes still require
the exact natural-drain endpoint; missing or inconsistent gate evidence is an
unscored system incident.

The frozen Codex binary also lists `rollout_budget`. Strict configuration enables
it with the same limit and weights input and generated tokens by 1, but this is
only an advisory provider-side guard. Cached-inclusive benchmark enforcement
comes from the authenticated provider gate and its completed-response ledger;
runner polling is an independent fail-closed observer.

Each run also starts a new materialized Codex root thread in a unique temporary
state directory with `history.persistence=none`, memories disabled, and no
thread resume or fork. Materialization is required because the frozen Codex
0.146 MultiAgentV2 runtime cannot resolve an ephemeral coordinator during child
spawn. The state directory is deleted on normal adapter exit and is never
reused or mounted by another attempt, including if abnormal termination leaves private
rollout bytes behind. Thus Ultra children and stored history cannot enter a
later attempt.
The workspace contains no prior submission or result. Provider prompt caching,
when reported as cached input tokens, reuses computation for an exact input
prefix; it does not retrieve a previous answer or proof and carries no
conversation history between runs. Cached input is nevertheless charged at full
weight against the 5,000,000-token benchmark limit.

Two independent private live canaries are required before a scored run. The
synthetic Ultra orchestration canary has ID
`ULTRA-ORCHESTRATION-SUBMISSION-CANARY-V12`; it is not a matrix assignment and does not use
or edit a benchmark task: its authenticated prompt first requires a completed
root response, a deliberately denied root `fork_turns="3"` call, and then one
allowed `fork_turns="all"` delegation. That child deliberately attempts one
`fork_turns="3"` grandchild, which must also be denied before it returns its
marker. Offline replay must authenticate both denials with no corresponding
child activity, match the one allowed raw spawn call to its subagent activity,
rederive a positive inherited child baseline and a complete projection-v6
ledger, and prove the same exact
authenticated submission boundary used by a passing run. Its root remains
blocked (`drain_complete=false`) while descendants are quiescent and the retained
challenge/call/request/ack/snapshot chain is read-only and authenticated. The
synthetic candidate must also pass the real hidden semantic/dependency audit
through the frozen `tools/dependency_audit.lean` helper; the exact audit command
is bound into the validator contract and the retained helper copy is hashed.
The separate 14-artifact token canary has ID
`TOKEN-CONTROL-SYNTHETIC-PROVIDER-GATE-V8` and prompt protocol
`synthetic-inert-sanitized-provider-gate-compaction-crossing-v8`. It uses a
private synthetic non-matrix target and inert prompt, so it tests the production
gate without exposing any benchmark task, context, target bytes, or proof
prefix. At the fixed 180,000-token cap its first root-turn response must finish
below the cap and be released byte-for-byte. The adapter then explicitly sends
`thread/compact/start`; the second, distinct compaction-turn response must be the
sole crossing and may release only the canonical inert `Compaction` item and
minimal completed event. Its event-ordered projection-v6 evidence authenticates
both responses, the gate calls and direct app-server deliveries, the closed
`token_limit` endpoint, and the mode-0444 final gate artifact. Tree drain and
cumulative projection completion are deliberately false at this endpoint;
spawn/hook sets remain empty and the independent gate endpoint makes token
measurement exact. Its attestation states `scored=false`,
`matrix_assignment=false`, `synthetic_input=true`, and
`benchmark_task_bytes_used=false`. Both frozen
canaries must independently reauthenticate the same READY/GO/RELEASED protocol
and derive their timing deadlines from RELEASED. Matrix startup fails closed
unless both frozen descriptors have status `passed` and their evidence
reauthenticates.

Run `tools/run_ultra_orchestration_canary.py` first with a host admitted by the
frozen hardware policy and the same binary, authentication, toolchain, and mount
arguments used by `run_matrix.py`.
Explicitly promote its generated `ultra_orchestration_canary_attestation.json`
with `tools/promote_live_canary.py --ultra-orchestration-attestation ...`; mere
file presence never changes a descriptor to `passed`. Next run
`tools/run_token_control_canary.py` and explicitly promote its
`token_control_canary_attestation.json` with
`--token-control-attestation ...`. Promotion authenticates every referenced
artifact, updates only the named evidence/descriptors and frozen hashes, and
does not rewrite task, target, context, or shared files. This repository and all
resulting measurements remain private pre-publication work; nothing is
authorized for public release yet.

The canaries attest the frozen orchestration, accounting, and token-control
protocol rather than benchmark performance, so the P01 launcher does not keep a
per-node canary cache. A passed promoted descriptor is reauthenticated on every
allocation. Each scored run separately records and authenticates its actual
provider-transport evidence, and the pair-local allocation binding prevents an
N/L pair from crossing hardware or node-local transport fingerprints. A frozen
software/protocol change still marks the descriptors `replacement_required` and
requires new live canaries before any scored pair.

## Protocol-governance disclosure

These measurements must not be labeled a strict implementation of the
reference-PDF HighamBench 0.2 protocol. They use the previously disclosed
`signposted-library-v1` condition-L prompt, lack a demonstrated backend random
seed, and do not run from a frozen OCI image. They also add a HighamBench
execution-protocol amendment: an external trusted provider gate buffers
responses, reserves the frozen worst-case response bound, and makes the token
endpoint call-atomic by switching to one exclusive request before a possible
crossing. This is not behavior supplied by the frozen Codex binary. The same
gate, configuration, and verification rules are applied to N and L, so the
paired comparison remains symmetric, but results must be described as produced
by this explicitly amended HighamBench-derived protocol.

For the private P01 completion campaign, hardware equality is also relaxed from
one host class for the whole result root to one exact authenticated allocation
per N/L pair. Different complete pairs may run on different members of the
three-node vetted set. Reports must expose the allocation and host provenance,
must not pool absolute elapsed times as if the hardware were homogeneous, and
must identify paired L-minus-N measurements as the primary timing comparison.

## Repetitions and run order

Each task-condition pair is repeated three times. The IDs `rep-01`, `rep-02`,
and `rep-03` are repetition IDs, not model random seeds. No backend seed is
claimed because this repository does not currently have proof that the selected
agent backend accepts and obeys a seed. If a backend with real seed support is
used later, its seed values must be added to the raw run record before evaluation.

The legacy T1--T3 matrix records 360 planned runs:

`60 T1--T3 tasks x 3 repetitions x 2 conditions = 360 runs`.

That historical run order does not include T4 and is not a readiness record for
the current 61-package construction corpus. Any future measurement freeze must
derive its matrix from authenticated paper registrations.

The first condition in each pair was selected by the fixed SHA-256 rule recorded
in `metadata/run_order.json`. SHA-256 is a repeatable text-to-number calculation.
It makes the order reproducible without presenting repetition IDs as random
seeds.

### Separation from the raw-access P01 measurements

The completed P01 measurements made before `signposted-library-v1` used the
earlier raw-access protocol, in which the L mount was available without this
explicit library notice. Those records remain preserved as a separate
experiment. They must not be overwritten, pooled with, or used
as repetitions of a signposted run. A signposted P01 measurement uses fresh
agent contexts and its own prompt hash, environment identity, result root, and
report; the task statements and task contexts stay unchanged.

## Files

- `../TASK_SOURCE_TAGS.md` defines the mandatory source-presentation tags for
  every task. `../AGENTS.md` makes that policy persistent across Codex
  sessions, and `tools/task_tags.py` checks every current task record.
- `tools/finalize_paper.py` validates and atomically registers one independent
  paper; `tools/paper_registry.py --discover` composes receipts in memory.
  `tools/refresh_snapshot.py` is retained only as a legacy corpus-view exporter.
- `shared/HighamBench/P*Definitions.lean` files are self-contained custom
  semantic surfaces with direct upstream imports. `Core.lean` and
  `SemanticCore.lean` are not controlled dependencies of any paper.
- `IMPLEMENTATION_PLAN.md` explains the construction decisions and the checks
  required before measured runs.
- `metadata/manifest.json` is the legacy compatibility view of all 20 papers,
  their source hashes, the specification hash, the current 61 task packages,
  and their exact source locations. Paper extraction does not write it.
- `metadata/config.json` freezes the environment and run limits.
- `metadata/run_order.json` fixes the order of N and L for every paired
  repetition.
- `metadata/reviews/` contains construction-stage review records. They are
  evidence from earlier snapshots, not final immutable approvals; final review
  records must be regenerated for every task before measurement.

The review files distinguish completed checks from pending or rejected checks;
pending and rejected checks are not rewritten as passes. The former 60-task
T1--T3 snapshot recorded 120/120 private N/L checks and two fresh-context review
passes, but those shared-core-era hashes do not attest the current paper-local
files or P01 T4. Preserve that evidence as historical. Current construction and
T4 review acceptance must be regenerated per paper and authenticated by its
registration receipt before any new measurement freeze.

## Frozen source versions

- Lean: `leanprover/lean4:v4.29.0-rc3`
- mathlib: `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b`
- NumStability source baseline:
  `45813a95dacf577461bae13f033af0dbc985a225`
- Paper PDF SHA-256 values and lawful source locators are recorded for every
  corpus paper in `metadata/manifest.json`.
- Specification PDF SHA-256:
  `59dfc314d4f9afecbbc6131c3c693624b09cc9e908f0e157efa468675ff56915`

## What a result may say

For a future authenticated measurement-ready freeze, the experiment may show
whether library access changed proof success, time, token use, or actual library
use for its precisely registered tasks and one fixed agent setup. The historical
360-run statement applies only to the 60 T1--T3 tasks. It does not test human
proof development, and T4 construction additionally includes a separately
reviewed paper-to-Lean translation stage. Uncertainty intervals must respect the
registered paper clusters and must not be presented as certainty beyond that
corpus and setup.
