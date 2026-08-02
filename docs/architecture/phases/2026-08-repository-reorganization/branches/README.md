# Branch registry

One JSON record is tracked per phase branch. A planned branch must start from
the current accepted checkpoint and use an active lane baseline projection.
Delivery, integration, ancestry, and retirement fields are updated rather than
replaced by prose-only status messages.

[`B0001`](B0001.json) is retired: W01 delivery
`d30fecc70a1d2066e2d147b79d9e6b9d743a21e5` is an ancestor of green checkpoint
C0002.

The active handoffs are:

- [`B0002`](B0002.json): W02, branch
  `codex/reorg-2026-08-w02-foundations`, 73 exact owners and 67 destination
  roots from C0002.
- [`B0003`](B0003.json): W12, branch
  `codex/reorg-2026-08-w12-ch01-ch02-ch05`, 42 exact owners and 65 destination
  roots from C0002.

Both branch refs are created at the recorded base SHA. Workers may change only
the exact owned paths and vacant destination roots in their record. Focused
tests and delivery evidence must stay below the recorded W02 or W12 prefixes;
phase controls, global aggregates, root tests, and architecture manifests are
forbidden. Workers never edit the registry or mark their own delivery
accepted.

W02 is integrated before W12. The hash-pinned overlap reviews record the
integrator-only compatibility and umbrella rewrites that cannot legally be
performed on either worker branch.
