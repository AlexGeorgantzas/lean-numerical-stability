# R07 private closure

The reviewed declaration projection selected 44 private declarations. The
complete reverse-dependency calculation adds 33 public boundary declarations,
so the frozen private closure contains 77 declarations in total. Every private
seed and every boundary witness is copied byte-for-byte in `PRIVATE_CLOSURE.tsv`.

All 44 private names are normalized only because their owning module changes.
`PRIVATE_NORMALIZATION.tsv` is a total, injective old-name to new-name map and
also pins each destination owner. Public declaration names are unchanged. The
P0010 replay checker uses this map as part of the semantic comparison, and the
isolated `PrivateNormalization` test exercises the realized destination set.

No internal private-support destination is placed in a public umbrella or in a
compatibility wrapper. That boundary is checked both in the raw worker graph and
again after the disposable R0011 overlay.
