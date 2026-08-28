# HighamBench operations map

In this reference, `tools/` and `metadata/` are relative to
`paper_bencmark/highambench/`, while `scratch_pad/` is relative to
`paper_bencmark/`. Before invoking an entrypoint, inspect its current `--help`
or shell header and its selected manager contract; frozen metadata and code
take precedence over this map.

## Route by requested operation

| Operation | Canonical entrypoints | Boundary |
| --- | --- | --- |
| Protocol/status audit | `paper_bencmark/highambench/README.md`, `metadata/*.json`, `tools/task_tags.py`, `tools/validator.py` | Read-only unless the user explicitly requests a controlled refresh. Require all status surfaces to agree. |
| Zero-provider admission rehearsal | `tools/run_matrix.py --only-pair-id ... --allocation-end-epoch 1` | Provider-free, not read-only: it creates result and status artifacts. Use only when local rehearsal writes are authorized. Accept only exit 75, `stopped_before_allocation_deadline`, and empty records/attempts/runs. Do not run `tools/preflight.py` against the repository root; the runner invokes it inside staged N workspaces. |
| Host probe and inventory | `scratch_pad/probe_highambench_pair_node.sh`, `scratch_pad/inventory_highambench_host.py` | Require both host-class and provider-gate matches; record exact interpreter, runtime, hardware, and time-envelope evidence without starting a provider. |
| Live-canary bootstrap | `scratch_pad/run_highambench_canary_bootstrap_actual_ultra.sh`, `tools/run_ultra_orchestration_canary.py`, `tools/run_token_control_canary.py`, `tools/promote_live_canary.py` | Provider calls and each promotion require authorization. Launcher pins must exactly match the current snapshot. Run, promote, and verify Ultra before token control. |
| Legacy provider-gate script audit | `scratch_pad/run_highambench_provider_gate_canaries_v7_v3.sh` | Historical token-limit launcher; inspect only. Do not use for the current scored protocol when its frozen limit or manifest pin differs. |
| P01 checkpoint campaign | `tools/manage_p01_campaign.py`, `scratch_pad/run_highambench_p01_actual_ultra.sh`, `tools/render_p01_report.py` | Exactly the declared P01 signposted scope; require current pins and keep older raw-access results separate. |
| P11 campaign | `scratch_pad/manage_highambench_p11_campaign.py`, `scratch_pad/run_highambench_p11_actual_ultra.sh` | Require current pins and use its immutable begin/run/record/commit transaction. |
| Reviewed pair shards | `scratch_pad/manage_highambench_pair_shard.py`, `scratch_pad/run_highambench_pair_shard_actual_ultra.sh` | Use only paper IDs accepted by the manager and prefer one `--only-pair-id`; no force or ad hoc pair order. |
| Shard aggregation | `scratch_pad/aggregate_highambench_pair_shards.py` | Create, then independently verify the aggregate without changing source shards. |
| Shard report | `scratch_pad/report_highambench_pair_shards.py` | Create, then verify; report only its declared paper/pair scope. |
| Full result verification and reporting | `tools/result_set.py`, `tools/analyze.py`, `tools/render_report.py` | Require the complete authenticated matrix; renderers must refuse partial or stale input. There is currently no reviewed whole-corpus Slurm runbook to improvise. |

All current campaign/bootstrap launchers carry explicit frozen pins. Compare
them to the authenticated current metadata and stop on disagreement; never
auto-edit a pin as part of admission. The generic pair-shard manager also has a
reviewed paper allowlist. Read that allowlist rather than broadening it.

The scratch-pad directory contains large ignored private artifacts. Only the
allowlisted scripts above and their focused tests are repository code. Do not
delete or ingest logs, results, PDFs, credentials, compiled environments, or
provider transcripts merely because they share that directory.

## Pair transaction and time admission

`tools/run_matrix.py` is the canonical executor. Use atomic pair selection and
let frozen metadata assert model, effort, time, token, prompt, and environment
values. Pair order comes only from `metadata/run_order.json`.

Both conditions of a pair must complete in the same authenticated allocation
and node. Parallel scheduling may distribute whole pairs, never conditions.

Admit a pair only when the manager and runner prove the full configured pair
envelope is available. This includes both attempts, startup/retry allowances,
validation allowances, and the guard interval; do not replace that calculation
with an informal wall-time estimate.

Managers own permanent, staging, active, failed, and checkpoint paths. Follow
their state machine rather than moving files manually:

1. authenticate or create the campaign index before useful work;
2. begin exactly one pair transaction;
3. invoke `run_matrix.py` for that pair;
4. record the exact exit and artifacts;
5. manager-commit only a complete authenticated terminal pair;
6. archive exit 75 as a zero-work deadline checkpoint and resubmit it;
7. archive every other nonzero exit as failed and stop for audit.

## Canary order

When replacement is required and authorized:

1. run the synthetic Ultra orchestration canary;
2. explicitly promote its attestation;
3. run its verify-only path;
4. run the synthetic token-control canary;
5. explicitly promote its attestation;
6. run its verify-only path;
7. rerun release/runner admission before campaign-index creation.

Mere attestation-file presence never changes a descriptor to passed. Do not
promote stale, copied, partial, task-bearing, or unauthenticated evidence.
Run bootstrap serially under its lock. Concurrent shards may verify already
frozen canaries but must never promote them.

## Results and recovery

Do not invent retries. A useful-work attempt without the exact authenticated
submission boundary and natural drain is retained as unscored and stops the
pair. An interrupted active marker or terminal incident remains a hard stop
until the existing manager's audit/recovery path authenticates it.

Use the runbooks' private umask and ignored result roots. Preserve successful,
failed, checkpoint, and unscored roots plus their read-only ledgers; never stage
or publish raw authentication, provider, transcript, or rollout artifacts.

For a complete campaign, run result authentication before analysis and analysis
before rendering. Preserve raw records and report failure categories exactly:
`TIME`, `TOKEN`, `NO_SUBMISSION`, `RULE_VIOLATION`, syntax/elaboration, proof,
and system incidents are not interchangeable.

## Tooling checks

After changing experiment tooling or launchers, run the focused Python tests
under `paper_bencmark/highambench/tools/tests/`, the two allowlisted pair-shard
test files in `paper_bencmark/scratch_pad/`, and `bash -n` on every changed
launcher. Unset a forbidden inherited `LD_LIBRARY_PATH` for the authenticated
runtime tests. Do not substitute the broad historical-host suite when its
frozen interpreter is unavailable; report that host gate separately.
