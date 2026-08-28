# Paper-local independence

Read this reference before the first write for a paper and again before final
registration. One invocation owns one `P0X`; distinct paper IDs may proceed
concurrently, while two invocations must never edit the same paper.

For T4, enforce that ownership with
`paper_bencmark/highambench/tools/t4_writer_lease.py`. Claim the `P0X` lease
before `t4_workspace.py init` or any other write. Let the claim command create
the invocation UUID and bearer inside an owner-only credential file below a
system-created private temporary directory. That ephemeral credential file is
active control state, not metadata or a durable hand-off artifact; pass it
directly to lease-guarded tools and never print, copy, or inspect its bearer.
Renew before expiry and release when the invocation is terminal. Successful
release removes the credential file. The stored lease contains only the token
digest. An expired lease may be replaced only with the explicit
`--takeover-expired` action, which archives the prior record. Never bypass an
active lease or expose its bearer token in metadata, prompts, logs, or hand-off
artifacts.

## Ownership

The invocation may write only:

- `paper_bencmark/highambench/tasks/P0X/**`;
- `paper_bencmark/highambench/shared/HighamBench/P0XDefinitions.lean`;
- `paper_bencmark/highambench/metadata/papers/P0X/**`;
- paper-local private proof, source-evidence, packet, campaign, and report paths
  below `paper_bencmark/scratch_pad/**/P0X/**`; and
- the paper's trusted bundle below
  `paper_bencmark/scratch_pad/highambench_environment/shared_olean/P0X/**`.

Treat all other paper paths, corpus-wide metadata and aggregates, generic
schemas and tools, `HighamBench.Core`, and `HighamBench.SemanticCore` as
read-only. Use a unique `P0X`-scoped or system-created temporary directory for
every build and campaign attempt. Never share a mutable temporary path, cache,
checkpoint, counter, or campaign ledger between papers.

## Semantic boundary

`P0XDefinitions.lean` owns every custom semantic declaration used by that
paper. It imports only minimal frozen upstream `Std` or `Mathlib` modules and
uses paper-specific names or a paper-specific namespace. It never imports a
custom module belonging to the corpus or another paper. Proof-only helpers and
private solutions remain outside the controlled target and definitions file.

Changing one paper's target or definitions invalidates only that paper's
private N/L and faithfulness evidence. Hash the frozen upstream configuration
and generic toolchain used by the invocation; if either changes during the
run, stop before publishing a registration receipt.

## Construction-stage solvability

Use the direct exact-byte N/L gate in
[T4 private solvability](t4-private-solvability.md) to establish that the
current paper is solvable and ready for faithfulness review. That check and its
small paper-local record belong entirely to the selected paper and may run in
parallel with other paper extractions. It does not depend on the finalizer,
registry, or locked measurement workspace.

## Paper-local measurement-ready registration

For final measurement-ready registration only, use the generic tool named the
construction checker with exactly one `--paper-id P0X` and
`--paper-local-evidence`. It first invokes the generic finalizer for that
paper's exact one-file definitions bundle and controlled manifests, then checks
the paper-owned task matrix and atomically publishes
`metadata/papers/P0X/construction.json`. The construction receipt contains the
complete checker certificate and is bound to the current paper, task,
definition, controlled-manifest, tool, environment, and compiled-bundle
identity. The checker and finalizer may write or lock only that paper's shard;
they do not read or copy the legacy corpus-global controlled-manifest view.

The finalizer verifies receipts but does not manufacture private-solvability or
faithfulness attestations. Every measurement-ready paper requires authenticated
bundle and construction receipts. An authenticated review receipt is required
only for papers containing T4; registration records it as `not-applicable` for
T1--T3-only papers. After all applicable receipts exist, the same paper session
may switch its paper/task records to measurement-ready and run the finalizer's
measurement-ready phase.

A construction-phase `registration.json` produced before the checker receipt is
a truthful draft with pending gates, not a completion claim. The authenticated
construction receipt plus the refreshed registration is the terminal
measurement-ready construction attestation; the earlier direct record already
establishes private solvability and permits T4 review. T4 still requires its
applicable review receipt before measurement-ready publication.

Run this hardened registration only when preparing measurement-ready release
or when the user explicitly asks for that final registration. If the generic
checker cannot start because the host lacks a required isolation permission,
do not write a paper-specific runner, stack Bubblewrap under another wrapper,
change the paper, move stale receipts, or edit shared infrastructure as an
extraction workaround. Leave measurement-ready registration pending and run
the unchanged final check later on a compatible executor. This does not undo a
passing direct private-proof check or force completed faithfulness work to be
repeated unless semantic bytes changed.

Paper extraction never rewrites `metadata/manifest.json`,
`metadata/environment.json`, `metadata/run_order.json`,
`metadata/release_files.json`, or another paper's controlled manifest.
Corpus-level consumers discover valid paper registrations, sort them by paper
ID, and derive any aggregate view in memory. No later merge, snapshot refresh,
or serialized registration step is required.
