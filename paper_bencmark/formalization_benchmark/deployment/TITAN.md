# Titan deployment

The benchmark must be installed from the `formalization_benchmark` branch at an
exact commit. Do not run it from a moving checkout or from the historical
`benchmark` branch.

## Security first

Use SSH key authentication and verify Titan's host-key fingerprint out of band.
Never put an SSH password in this repository, a shell command, an environment
variable, `sshpass`, a process argument, or a log. Rotate any password that has
already been shared in a chat.

## Required host facilities

Titan must provide Linux x86-64, cgroup v2, a functioning per-user systemd
manager, Bubblewrap, seccomp user notification, Landlock ABI 3 or newer, Git,
a C compiler, Poppler, Python 3.11 or later, Elan/Lake, `/usr/bin/rg`, GNU
`/usr/bin/time`, and an authenticated standalone Codex CLI. The system manager
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
  --pdf-source-dir /private/path/to/reference_papers
```

The installer creates a user-private deployment below
`~/.local/share/highambench-formalization`, unless `--deployment-root` says
otherwise. A fresh install is built in a uniquely named sibling transaction and
atomically renamed into the final path only after its deployment record is
ready. An authenticated published transaction interrupted during finalization
is resumed on the next invocation. Incomplete or malformed sibling transactions
are quarantined under unique names; an unrecognized existing destination or
launcher is never overwritten. It:

1. verifies the release and all five private PDF hashes;
2. prepares the frozen Lean 4.29.0-rc3 and Mathlib environment;
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
8. starts the exact sandboxed Codex app-server through `thread/start`, then
   stops before `turn/start`, proving interface compatibility without model
   inference;
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

The installed operator command is:

```bash
~/.local/bin/run-highambench-formalization run --task-id P01-T2
```

It enters the fixed systemd hardware envelope, then invokes the authenticated
pair controller. The repository skill maps the natural-language request
`Run benchmark for P01-T2` to this command. Repeating the request returns the
existing pilot run for that task rather than creating a repetition.

The five accepted task IDs are `P01-T2`, `P02-T2`, `P03-T2`, `P13-T2`, and
`P14-T2`. Each task has exactly one official N/L pair. Every condition uses one
persistent formalizer conversation for up to four submissions, with a
five-hour cumulative charged-time limit and no contestant token cap.

Status is provider-free:

```bash
~/.local/bin/run-highambench-formalization status --task-id P01-T2
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
