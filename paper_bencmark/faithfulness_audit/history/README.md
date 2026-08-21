# Faithfulness audit history

This directory records corpus-level snapshots of HighamBench faithfulness
audits. Task-local `faithfulness/` directories remain the authoritative source
for complete inputs, agent outputs, decisions, reports, and hash manifests.

Each history entry preserves the aggregate result, identifies every task
artifact, and pins the repository commit containing those artifacts. This
avoids duplicating the full evidence bundles while keeping earlier audit states
recoverable.

## Entries

| Audit | Scope | Status | Accepted | Repository snapshot |
|---|---|---|---:|---|
| [`audit_002`](audit_002/summary.md) | 59 eligible; 57 validated, 2 pending | in progress | 32/57 validated | per-task commits through `d1ca8c6b6626ed750fec1eec727f02282344ae34` |
| [`audit_001`](audit_001/summary.md) | P01-P20, T1-T3 | completed | 17/60 | `df483a11408fa7b7440bbc1907c93bb9b3e610fa` |

## Update rules

- Allocate sequential IDs: `audit_001`, `audit_002`, and so on.
- Never overwrite a completed entry.
- Validate every included task bundle before recording a completed snapshot.
- Record the exact target, paper, decision, report, protocol, and repository
  provenance in the machine-readable results.
- A changed target or rerun creates a new entry. Task-local artifacts may be
  refreshed only through the audit protocol's own archival mechanism.
