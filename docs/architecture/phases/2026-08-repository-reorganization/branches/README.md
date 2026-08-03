# Branch registry

One JSON record is tracked per phase branch. A planned branch must start from
the current accepted checkpoint and use an active lane baseline projection.
Delivery, integration, ancestry, and retirement fields are updated rather than
replaced by prose-only status messages.

[`B0001`](B0001.json) is retired: W01 delivery
`d30fecc70a1d2066e2d147b79d9e6b9d743a21e5` is an ancestor of green checkpoint
C0002. [`B0002`](B0002.json) is retired after acceptance at C0003: W02 delivery
`799d781971eed851cd90152c0d9acb0e828f9341` is an ancestor of checkpoint commit
`bb80c95a4625e07535dacdda12d246ee1a5795b3`, and its remote ref was deleted at
`2026-08-02T23:32:59Z` after the C0003 control record was published green.

No phase branch remains live or awaits retirement. The final retired branch is:

- [`B0003`](B0003.json): W12, branch
  `codex/reorg-2026-08-w12-ch01-ch02-ch05`, 42 exact owners and 65 destination
  roots from C0002. Delivery
  `380d3cba83bb9e3704232720f371f28cbbc673da` is an ancestor of accepted C0004
  commit `b56f609f3bf66b5d7d0b677567cce82fee0c275b`. Its remote ref was deleted at
  `2026-08-03T01:04:19Z` after the C0004 acceptance-control commit passed CI.

Workers may change only the exact owned paths and vacant destination roots in
their record. Focused tests and delivery evidence must stay below the recorded
wave prefixes; phase controls, global aggregates, root tests, and architecture
manifests are forbidden. Workers never edit the registry or mark their own
delivery accepted.

W02 was integrated before W12. The C0003 refresh recorded seven import-only
same-path overlaps and preserved the delivered branch's 17 direct W12-to-W02
dependency pairs for integrator reconciliation. The C0004 integration rewrote
those pairs to accepted W02 canonical leaves, preserved the reviewed C0003
imports, updated the shared wiring, and passed every global gate. After the
C0004 control commit became green, B0003 was deleted remotely and recorded
retired.
