# Formalization benchmark architecture

## Operator path

```text
"Run benchmark for P01-T2"
        |
        v
installed run-highambench-experiments skill
        |
        +--> verify-release (complete frozen-file closure)
        +--> Titan doctor (PDF/runtime/executable/hardware identities)
        +--> off-benchmark provider capability and exact audit-schema
        |    qualification (before a new pair ID)
        |
        v
transient systemd user service: fixed 8 CPUs / 32 GiB / 512 tasks / no swap
        |
        +--> trusted-control child: 8-GiB memory.low reservation
        `--> generated-command child: 24 GiB / 384 tasks / no swap
        |
        v
one authenticated pair controller
        |
        +--> condition N: paper + packet + Lean/Mathlib
        `--> condition L: identical base + frozen NumStability + L appendix
```

The pair controller pre-stages and byte-compares both condition inputs before
the first contestant provider call. It then follows the condition order frozen per task in
`config.json`. A task index permits one official pair only. Reissuing the same
run command returns a terminal pair or continues before the first turn or
between sealed conditions. An interruption after a condition has submitted is
not cold-resumed, because that would lose its exact raw-event stream; it fails
closed as an incident. An account-global pilot/task reservation and campaign
lock prevent duplicates across deployment roots. Pilot-3 also acquires its
predecessors' launcher locks to avoid contending for Titan's fixed allocation.
The sealed pilot-1 and pilot-2 P01 incidents remain unscored predecessor
evidence and are never pooled with pilot-3. Pilot-2 P01 stopped after one
compiling N candidate when the provider rejected the blind-auditor response
schema; no audit verdict or L run exists for that pair. All five pilot-3 task
slots are fresh.

## Per-condition loop

```text
persistent formalizer conversation
        |
        | model-active clock ON; formalizer response tokens metered
        v
Candidate.lean produced --> clean/list background terminals --> workspace bounded
        | model-active interval OFF
        v
ordered telemetry settle + trusted bookkeeping (off-clock)
        |
        v
stable Candidate.lean copy + SHA-256 (separately timed and charged)
        | all contestant charging OFF
        v
no-network Lean compilation + integrity checks
        |
        v
pseudonymized semantic dependency dossier
        |
        v
fresh blind translator + direct judge + round-trip judge
        |
        +--> faithful: accept and stop
        +--> unclear: unscored audit-system incident
        `--> unfaithful: fixed neutral feedback
                              |
                              `--> same conversation; next turn restarts metering
```

There are at most four immutable submissions: one initial submission and three
repairs. One app-server process remains alive through the condition, including
the validation/audit pauses, so repairs use the same conversation and raw
per-response metering remains enabled. The model-active interval through
background-terminal quiescence and the separately timed candidate copy/hash are
charged. Ordered telemetry settling, trusted bookkeeping, validation, and
auditing are outside contestant measurement. Auditor usage is retained in a
separate overhead ledger.

## Isolation boundary

Each formalizer gets a fresh Codex state and workspace inside a minimal
Bubblewrap filesystem. The provider control process may reach the model
provider; model-selected shell descendants are forced through the frozen
Landlock/seccomp launcher, cannot read `/proc` or the Codex control tree, and
cannot create or use sockets. Security-sensitive Codex configuration generated
during provider-free startup is hash-sealed, then mounted read-only for the
complete measured app-server session. Refreshable authentication remains only
inside the private tmpfs-backed control state used by that live app-server; it
is inaccessible to generated commands, excluded from the control manifest, and
redacted from persisted artifacts. Refresh rotations are synchronized under a
lock to the deployment-private auth store, and the tmpfs copy is destroyed when
the driver closes. Host `/usr/local`, home trees, and documentation trees are
absent; the narrow common system-runtime mounts are treatment-scanned, hashed,
and rechecked by the doctor. The N filesystem has no NumStability source,
objects, cache, index, documentation, Git history, or prior outputs. The L
filesystem adds only the frozen read-only source and compiled tree. Its L-only
prompt appendix points to `/library/NumStability` and
`/library/NumStability.lean`, notes that compiled declarations are on
`LEAN_PATH`, and gives concrete `find`, `rg`, and `import NumStability`
discovery/import examples.

The app-server launch and thread configuration both disable agent delegation
with `agents.enabled=false`, `multi_agent=false`, and `multi_agent_v2=false`.
The driver checks effective configuration and global/thread features before
any model turn and rechecks thread features before repairs. Any collaboration
event, foreign-thread event, or failed attestation is a release-blocking
provider infrastructure incident. An off-benchmark provider canary exercises
the exact formalizer and auditor models/efforts and sends the exact frozen
blind-translation, direct-judge, round-trip-judge, and adjudicator response
schemas in live calls with checkable synthetic outputs before a new pair
consumes its slot; its usage is logged separately. Static schema checks alone
would not have caught the pilot-2 provider rejection. The app-server has no
generic pre-execution built-in-tool allowlist, so event rejection is an
additional fail-closed check, not a claim that every unused tool was impossible
to call.

The waited, piped transient systemd user service applies the frozen eight-CPU
affinity and limits the whole benchmark process tree to 32 GiB, 512 tasks, and
zero swap. A service-wide syscall filter prevents the controller, Codex, build
tools, auditors, and all descendants from changing their inherited CPU
affinity; each strict snapshot proves the denial with a no-op syscall canary.
It delegates separate cgroup-v2 children for the trusted controller and
model-generated commands. The generated-command seccomp policy repeats the
affinity denial. Commands are migrated
into a 24-GiB, 384-task, zero-swap child with CPU weight 100; the control child
uses CPU weight 10000 and an 8-GiB `memory.low` reservation. The controller
checks resource identities and command-child limit events at every attempt.
Workspace traversal is capped at 10,000 entries and 1 GiB total, with a 256-MiB
per-written-file limit. Protocol lines, event traces, event counts, and stderr
archives are also bounded; a limit breach is a recorded fail-closed outcome.

Untrusted `Candidate.lean` is never compiled directly on the host. Validation
and semantic extraction run in a separate no-network Bubblewrap namespace that
mounts only a fresh candidate scratch directory, the frozen Lean toolchain,
the frozen package closure, and—only for L—the frozen library objects.

## Trusted scripts

| Script | Responsibility |
| --- | --- |
| `tools/setup_titan.py` | Build and hash the private Titan deployment in an atomically published transaction with authenticated finalization resumption and no paid model calls. |
| `tools/measure_library_build.py` | Clean and measure the full NumStability build under the fixed outer resource envelope, retaining authenticated build output and resource evidence. |
| `tools/runtime_canary.py` | Prove the N/L import boundary with provider-free sandboxed compilations. |
| `tools/provider_capability_canary.py` | Qualify the exact single-agent provider roles and frozen audit output schemas off-benchmark before a new official pair. |
| `tools/titan_envelope.py` | Enter the exact CPU, RAM, and swap cgroup. |
| `tools/run_benchmark.py` | Expose `verify-release`, `doctor`, `qualify-provider`, `run`, and `status`. |
| `tools/pair_controller.py` | Own pair uniqueness, ordering, state transitions, clocks, freezing, and repair continuation. |
| `tools/codex_driver.py` | Own fresh/persistent Codex conversations, tool isolation, raw events, and provider usage. |
| `tools/formalization_validator.py` | Enforce the one-root/one-`sorry` source contract. |
| `tools/lean_sandbox.py` | Compile untrusted Lean in the no-network filesystem. |
| `tools/prepare_candidate_audit.py` | Extract and pseudonymize the generated/NumStability recursive closure and frozen Lean/Mathlib frontier. |
| `tools/audit_controller.py` | Run fresh condition-blind audit roles and emit neutral feedback. |
| `tools/freeze_manifest.py` | Release-authoring only: regenerate the frozen manifest before commit. |

The historical `paper_bencmark/highambench/tools/runner.py` and
`run_matrix.py` are not part of this architecture.

## Artifact layout

```text
runtime/library/
  snapshot.json
  source/...
  olean/...
  build/
    build-record.json
    build-output.log
    gnu-time.txt
runs/
  qualifications/<manifest-sha256>/... off-benchmark provider evidence
  index/P01-T2.json
  pairs/<run-id>/
    admission.json
    pair_staging.json
    pair_state.json
    pair_report.json
    conditions/N|L/
      prompt.txt
      condition_state.json
      codex-state/
      workspace/Candidate.lean
      formalizer-session-close/
        shutdown.json
        stderr-after-last-turn.log
      attempts/01..04/
        Candidate.lean
        hardware.json
        hardware_after.json
        formalizer/{prompt.md,events.jsonl,last_message.txt,turn.json,network_violations.bin}
        validation.json
        dossier/{blind_semantic_dossier.json,private_semantic_manifest.json}
        repair_feedback.json
    audits/<semantic-sha256>/
      roles/... fresh auditor transcripts and usage
      decision.json
~/.local/share/highambench-formalization-registry/
  locks/campaign.lock
  index/formalization-benchmark-t2-pilot-3/P01-T2.json
```

At the end of each condition, the driver closes the one persistent formalizer
app-server and records `formalizer-session-close/shutdown.json` plus the
credential-redacted `stderr-after-last-turn.log`. The shutdown record binds the
stderr hash, return code, forced-signal state, stdout EOF drain, and count/hash
of any protocol lines emitted after the final telemetry boundary. The pair
controller authenticates both files and requires a graceful zero-exit shutdown,
a fully drained protocol stream, and no late protocol lines before a
non-incident condition is scoreable. A close failure preserves measured
evidence in a fail-closed incident but cannot be promoted to a scored result.
Likewise, a host/controller interruption before a complete turn or final-freeze
duration is journaled seals an unscored partial incident; condition and pair
records mark the affected active-time and/or token totals as incomplete
observed lower bounds rather than exact measurements.

Normal authenticated setup finalization can resume after interruption without
rebuilding. That recovery is deliberately bounded: if the separate atomic skill
installer retains a `skill-install-state.json` journal because exact restoration
could not be established, later setup attempts fail closed and require exact
manual recovery of the named transaction before retrying.

The library build record is provisioning evidence and is never added to either
condition's contestant clock. It identifies the clean project build after a
workspace clean, off-clock dependency-cache rehydration, and proof that the
root build tree remains empty, together with the exact toolchain and source commits,
all dependency commits and compiled OLean cache digests, clean source and
project-configuration digests before and after, and the complete sanitized
subprocess environment. It also records the enforced
eight-CPU/32-GiB/512-task/no-swap service, monotonic and UTC time, GNU `time`
resource metrics, strict cgroup counter deltas, source/object size counts, and
hashes of the retained raw outputs. The library snapshot and deployment record
bind the complete build-evidence tree so a later doctor detects any change.

The records contain exact prompt and candidate hashes, source line counts,
observable messages/reasoning summaries, tool events and commands, exact
deduplicated provider input/cached/cache-write/output/reasoning/total token
counts, active, excluded, and end-to-end wall durations, executable/runtime
identities, and start/end hardware observations. Terminal condition hashes bind
the attempt telemetry into the pair report. Hidden chain-of-thought is neither
available nor requested; it is never represented as a benchmark artifact.
