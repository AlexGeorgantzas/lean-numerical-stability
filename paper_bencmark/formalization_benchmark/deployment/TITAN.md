# Titan deployment

The benchmark must be installed from the `formalization_benchmark` branch at an
exact commit. Do not run it from a moving checkout or from the historical
`benchmark` branch.

Pilot-11 is a side-by-side warm-start successor. The pilot-1 through pilot-10
deployments, launchers, and sealed runs must remain unchanged. Pilot-2 P01-T2
(`P01-T2-20260916T084145Z-6dad064a`) reached one compiling N candidate but
stopped before a faithfulness verdict because the provider rejected the
blind-translation audit response schema; L never started. Pilot-3 P01-T2
(`P01-T2-20260916T150151Z-40b3a1dd`) stopped after its formalizer could not
access the workspace because `/codex-code-mode-host` was missing inside the
sandbox; no faithfulness verdict or L run exists. Pilot-4's clean full-library
build took 1307.425 seconds under eight logical CPUs and 32 GiB RAM. An
isolated one-turn workspace-tool probe passed. Its six-role, one-shot
qualification then failed after the formalizer completed with exact output
and a checked workspace write, before any auditor role, because a broad
warning detector mistook unrelated text in a giant truncated tool catalog
for a Code Mode startup warning. Pilot-4 created no official pair or index.
Pilot-5 narrowed that warning check and produced sealed P01-T2 and P02-T2
pairs under its original three-way audit policy. P02-T2 ended after L received
`unclear`; N did not start. Pilot-6 introduced the binary verdict policy for
five paper tasks; its evidence remains sealed under its own release. Pilot-7
expanded the release to 18 tasks, installed successfully, and completed no
official task. Its one-shot live qualification failed before any role completed
because its copied ChatGPT refresh token was stale; that failure is sealed.
Pilot-8's H22-11 attempt ended as a sealed audit-interface incident after its
direct judges returned complete ordered dependency records whose descriptive
labels differed from hidden controller expectations. It has no semantic
verdict. Pilot-9 then completed a cold-start H22-11 L condition but sealed the
pair as an incident when N's final adjudicator combined a faithful verdict with
remaining uncertainty. Pilot-10 installed and qualified the first warm-start
release, then consumed its single permitted scout. The scout itself completed,
but its controller failed closed because an automatic Codex context-compaction
response appeared in exact raw usage while app-server thread-cumulative usage
excluded it. No official Pilot-10 task started, and that scout is never retried
or reused. Pilot-11 recognizes only explicitly classified compaction responses
when reconciling the two usage views and gives each of the 18 tasks a fresh
warm-start slot under a binary `faithful`/`unfaithful` semantic policy; it
neither relabels nor resumes any earlier-pilot evidence. Never combine
observations across pilots. Setup authenticates the direct Pilot-10 deployment,
qualification, build, failed scout, untouched task set, and retained
pilot-9/8/7/5/4/3/2/1 lineage before publication.

The sealed Pilot-10 deployment SHA-256 is
`18c67fd64df4ee5ef1c3802ab6399869fda273064be37de917243757eb8b876a`;
its qualification record is
`ba26624b9e4dba410c1d133667656967afe7508302a02168e8b3ca87709ed711`,
its library build record is
`3d9a00ac37216feaab03010538b992b9738d19b6ec3de53db35b32b62a0e6794`,
and its failed warm-root record is
`1f532db6810812309a8f36f6963fadd038851d95daa8a80cfa6540ede4399e08`.

The sealed Pilot-9 deployment SHA-256 is
`cf84e8cfeb47447be38055cb8cd2758c50ccb7ff98d6afe8bdf531e9ab480863`;
its qualification record is
`54efe6d01d9ef0a50235c905298779876a338e1f12806432a0f4f6b16ea2ca2a`,
its library build record is
`7f12698294c2e10f68431d86a959bccf34698bda1dbf3fd236a7993349ae80fa`,
and its H22-11 pair report is
`14df6656ebbaeb861447bb4eeebf162660d72e8cbb438edfc87c900440698de7`.

The sealed Pilot-8 deployment SHA-256 is
`3c680b39563e3e7c66e2892a16d7cb72f541ed04631d4b134cee101acda04588`;
its qualification record is
`e8e90208a08dfcf60ca336fab3e82edc1b240701df4ab0ff6e1ec31ce6165a2e`,
its library build record is
`94a3cec672a8c67ef1f5ffeb842320b56b68f49df2d5bfc7daaa96e545b31584`,
and its H22-11 audit-incident record is
`4363f8fde6b0121ab33372364bb0806967e43ff814b010b5fcc89f1e16195469`.

The sealed Pilot-7 deployment SHA-256 is
`8258440ac97ec55a4775839fa2e5cd25e1e90d62005c4e9de2b29a037be9ec8e`;
its failed qualification record is
`93e26b4e45f0eea423967a77083c95b0a708caaa361bd2f573e57ba598f9c8fd`
and its library build record is
`af3ad72d084743adecabcc9b5a1ebca09b89dd1ff28ee440a317dd2eab0e073a`.

The sealed pilot-5 deployment SHA-256 is
`41632d90da27b5d5edda4bcaad6648264bfb2d042d551858c0d62f89a363404f`;
its qualification record is
`0c0c4ccb252b432e41025fa1f4e17dfa1df78c1f6f8c9a54801a32bd5ee97e16`
and its library build record is
`d9abf28dfa5444a78fc88ce6818fc4c0e4ed166296d922f5b53b46476f4316db`.
These identify retained older installation lineage, not Pilot-11 measurements.

Pilot-11 must not be treated as ready merely because these repository files
exist. Its own clean release, separate installation, provider-free gates, and
live provider qualification must pass before an official pair starts. An
integrity-valid candidate receives exactly one semantic verdict, `faithful`
or `unfaithful`: unsupported candidate-added restrictions on the paper's
domain receive a concrete mismatch and same-conversation repair feedback.
Provider, tool, or malformed-output failures remain unscored operational
incidents, not a third faithfulness verdict.

The sealed pilot-4 deployment SHA-256 is
`bd9dbc1c1f7576399c767d9dc7cae19732965e5e21989d195720bb884b31a749`;
its failed qualification record is
`930a69c9a059f8e00590a6689ea9d15177e27b435e901e724e57861a1db79c9a`
and its library build record is
`42d1a09980a908d4b4757b174dff0239d20f9cc35e0e67dd7499a0bec60580ec`.
These authenticate older predecessor evidence, not pilot-11 measurements.

## Security first

Use SSH key authentication and verify Titan's host-key fingerprint out of band.
Never put an SSH password in this repository, a shell command, an environment
variable, `sshpass`, a process argument, or a log. Rotate any password that has
already been shared in a chat.

## Required host facilities

Titan must provide Linux x86-64, cgroup v2, a functioning per-user systemd
manager, Bubblewrap, seccomp user notification, Landlock ABI 3 or newer, Git,
a C compiler, Poppler, Python 3.11 or later, Elan/Lake, `/usr/bin/rg`, GNU
`/usr/bin/time`, and an authenticated standalone Codex CLI with its matching
`codex-code-mode-host` executable beside the resolved CLI binary. The system manager
must delegate `cpu`, `memory`, and `pids` to the per-user manager.
User-manager lingering must be enabled so a multi-hour run is not killed solely
because its SSH login ends.
The setup and doctor commands fail closed instead of silently weakening
isolation. Titan's systemd 252 runs the benchmark in a waited, piped transient
`Type=exec` user service; it does not use the unsupported `--scope --wait`
combination.

The complete benchmark process tree is admitted only inside a transient user
service with:

- exactly eight effective logical CPUs;
- `memory.max = 34359738368` bytes (32 GiB);
- `pids.max = 512`; and
- swap disabled for the benchmark process tree.

Systemd applies the exact eight-CPU process affinity and the cgroup applies the
memory, swap, and task limits. `AllowedCPUs` adds a cpuset restriction when the
host delegates that optional controller. A service-wide seccomp filter denies
`sched_setaffinity` to the controller, Codex, build tools, auditors, and every
descendant, and every strict hardware snapshot fails unless a no-op affinity
syscall receives `EPERM`. The frozen command wrapper independently repeats the
denial for model-generated commands.

That service delegates a trusted-control child and a generated-command child. The
trusted-control child retains the same 32-GiB/512-task hard ceilings, has
`memory.low = 8589934592` (8 GiB), and uses CPU weight 10000. Every generated
shell-command tree is migrated to a child with
`memory.max = 25769803776` (24 GiB), `pids.max = 384`, swap disabled, and CPU
weight 100. Any command-child memory or PID limit event makes the attempt fail
closed. These nested limits reserve capacity for the controller while keeping
the requested eight-CPU/32-GiB host envelope fixed.

`taskset` alone is not treated as sufficient evidence. Every attempt records
both systemd-enforced process affinity and effective cgroup values, including the generated-
command child and its limit-event counters. The installer also freezes the
Titan hostname, platform, CPU model, and exact selected CPU IDs; a later doctor
or attempt fails closed if any of those identities changes.

Keep the benchmark account dedicated while a measured pair is active. The
campaign lock prevents two benchmark pairs from contending, but software inside
the user service cannot prevent a separately launched same-UID process from
competing for CPU, memory, or I/O.

## Install

From the exact release checkout:

```bash
python3 paper_bencmark/formalization_benchmark/tools/setup_titan.py \
  --pdf-source-dir /private/path/to/reference_papers \
  --predecessor-deployment-root /hdd/alexgeorgantzas/highambench/deployment-pilot-10-r1 \
  --deployment-root /hdd/alexgeorgantzas/highambench/deployment-pilot-11-r1
```

The installer creates a user-private pilot-11 deployment below
`~/.local/share/highambench-formalization-pilot-11-r1`, unless `--deployment-root` says
otherwise. A fresh install is built in a uniquely named sibling transaction and
atomically renamed into the final path only after its deployment record is
ready. An authenticated published transaction interrupted during finalization
normally resumes on the next invocation. This is not a universal automatic-
recovery promise: if skill installation retains a `skill-install-state.json`
recovery journal because exact rollback could not be proved, subsequent setup
fails closed and reports the transaction that requires exact manual recovery
before retrying. Incomplete or malformed sibling deployment transactions are
quarantined under unique names; an unrecognized existing destination or
launcher is never overwritten. It:

1. verifies the release and all 18 task PDF identities (with reused chapter PDFs deduplicated by hash);
2. prepares the frozen Lean 4.29.0-rc3 and Mathlib environment using the
   private `tooling/{cache,tmp}` directories beside the deployment on `/hdd`,
   not the account's small home filesystem;
3. checks out NumStability commit `45813a95...` separately, runs `lake clean`,
   rehydrates only the frozen dependency cache, verifies the root build tree is
   empty, and measures a full `lake build NumStability` inside the same
   eight-CPU/32-GiB/512-task/no-swap outer envelope before publishing read-only
   source/object snapshots;

4. compiles the no-network shell wrapper;
5. hashes and treatment-scans every non-frozen host runtime mount visible in N;
6. runs provider-free command canaries proving the shell can edit and compile
   the workspace but cannot read, truncate, rename, link, or write the Codex
   control/authentication tree or `/proc`, and that a socket attempt is blocked
   and logged;
7. runs provider-free compiler canaries proving Mathlib works in N,
   NumStability fails to import in N, and succeeds in L;
8. starts the exact sandboxed Codex app-server through `thread/start`, attests
   effective `agents.enabled=false` and both disabled multi-agent features,
   verifies the same-package Code Mode host is hash-pinned and mounted read-only,
   then stops before `turn/start` without model inference;
9. writes the private deployment record and a source-only, read-only copy of
   the exact release in the sibling transaction;
10. atomically publishes that ready transaction at the deployment path;
11. runs a provider-free doctor check inside the fixed hardware service; and
12. installs the launcher and atomically installs or restores the operator skill
    only after the doctor passes, then seals the transaction complete.

The one-time library compilation is deployment evidence, not contestant time.
Its immutable `runtime/library/build/build-record.json` records UTC and
monotonic wall time, GNU `time` CPU/peak-RSS/fault/context-switch/I/O metrics,
start/end hardware and cgroup snapshots, resource-event deltas, tool versions
and hashes, filesystem capacity, the complete sanitized build environment,
clean source/configuration fingerprints before and after, every dependency Git
revision and compiled OLean-cache digest, generated object counts/digests, and
the exact logical command. The complete combined build output and raw GNU
`time` output are retained beside it as `build-output.log` and `gnu-time.txt`.
Their hashes and sizes are bound into the build record, the library snapshot,
and the deployment record; every doctor invocation rejects missing or changed
build evidence.

No PDF, authentication file, run transcript, or NumStability snapshot is
committed to Git.

## Run

Once pilot-11 is installed and authenticated, its operator commands are:

```bash
~/.local/bin/run-highambench-formalization-pilot-11-r1 verify-release
~/.local/bin/run-highambench-formalization-pilot-11-r1 doctor --task-id H22-11
~/.local/bin/run-highambench-formalization-pilot-11-r1 qualify-provider --task-id H22-11
~/.local/bin/run-highambench-formalization-pilot-11-r1 prepare-warm-root
~/.local/bin/run-highambench-formalization-pilot-11-r1 run --task-id H22-11
```

It enters the fixed systemd hardware envelope, then invokes the authenticated
pair controller. Before a fresh official pair ID or index exists, the exact
formalizer and auditor roles pass off-benchmark provider-backed single-agent
qualification. The same qualification submits the exact frozen response
schemas for blind translation, direct judgment, round-trip judgment, and
adjudication through live provider calls and verifies checkable synthetic
outputs, then proves workspace-tool availability through trace-backed reads
and a checked formalizer write under the real sandbox. Code Mode startup
warnings in diagnostic events or stderr fail the qualification; unrelated
tool-catalog text does not. This guards against both the pilot-2 schema
rejection and pilot-3 missing-command-host incidents. Its sealed, one-shot usage is separately recorded
and never charged to N or L. A missing or failed qualification blocks the
release without consuming that task's official slot. The repository skill maps
requests such as `Run benchmark for H22-11` or `Run benchmark for P01-T2` to
the corresponding command.
Repeating the request returns the existing pilot run for that task rather than
creating a repetition.
The explicit `qualify-provider` command can be run immediately after setup to
establish live provider readiness without starting a benchmark. The separate
`prepare-warm-root` command then runs the one task-neutral library exploration,
freezes its conversation checkpoint, and records its time/tokens as off-task
overhead. A later fresh
`run` authenticates and reuses the sealed qualification record. A failed live
probe remains failed evidence for this release; do not silently retry it or
bypass the gate.

Installation and qualification are preparation only. Check all 18 statuses
after setup; do not start an official `run` as part of repair. A separate,
explicit task-run request is required.

The accepted task IDs are the five paper tasks `P01-T2`, `P02-T2`, `P03-T2`,
`P13-T2`, and `P14-T2`, plus `H22-11`, `H22-5`, `H20-6`, `H7-12`,
`H20-9`, `H20-8`, `H23-6`, `H5-5`, `H10-7`, `H12-4`, `H19-5`,
`H7-14`, and `H15-3`. Each task has exactly one official N/L pair. Every condition uses one
persistent formalizer conversation for up to four submissions, with 18,000
cumulative contestant-active seconds as its termination threshold and no
contestant token cap. Any timer or final-candidate-freeze overshoot is recorded,
not clamped, and yields an unscored `ACTIVE_TIME_LIMIT`; no scored condition can
exceed the threshold.

Status is provider-free:

```bash
~/.local/bin/run-highambench-formalization-pilot-11-r1 status --task-id H22-11
```

## Storage separation

The installation keeps these roots separate and mode-private:

- common Lean/Mathlib runtime;
- condition-L NumStability source and objects;
- source PDFs;
- Codex authentication state;
- contestant workspaces;
- de-identified auditor workspaces;
- immutable attempt artifacts; and
- redacted pair reports.

Condition N is launched in a Bubblewrap filesystem that does not mount the
library tree, control checkout, `.git`, old targets, or any other condition's
workspace. Condition L adds only the frozen source/object mounts. Model-chosen
shell commands enter inherited Landlock filesystem and seccomp no-network
filters. Codex's own workspace-write policy independently confines native file
tools. The writable Codex control state is mounted at `/control/codex`, outside
the command allowlist; security-sensitive contents are baseline-sealed before
model activity and mounted read-only on later turns, while the control process
retains only the provider
connection it needs.
