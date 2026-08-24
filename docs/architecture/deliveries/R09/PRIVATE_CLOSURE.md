# R09 private closure

The reviewed declaration projection selected 165 private declarations. The complete reverse-dependency calculation adds
258 public boundary declarations, so the frozen private closure contains 423 declarations in total. Every private
seed and every boundary witness is copied byte-for-byte in `PRIVATE_CLOSURE.tsv`.

All 165 private names are normalized only because their owning module changes. `PRIVATE_NORMALIZATION.tsv` is a total, injective
old-name to new-name map and also pins each destination owner. Public declaration names are unchanged. The
P0011 replay checker uses this map as part of the semantic comparison, and the isolated `PrivateNormalization` test exercises the realized
destination set.

The closure was recomputed from the frozen `benchmark-results/C0006-combined.tsv` format-2 graph, restricted to the 570 declarations owned by this
wave's selected owners. A boundary row is a routed public declaration that reaches at least one private seed; `minimum_depth` is the shortest such
distance, `membership_witnesses` records one shortest-path witness per seed, and `signature_edge_span` / `body_edge_span` are the declaration's outgoing
signature and body edge counts inside that subgraph. `co_route_component` names the lexicographically first member of the co-routed group when the row shares
a destination with a private seed, and `-` otherwise.

No internal private-support destination exists in this wave: the 41 destinations are 6 reusable, 35 source, so the
public-umbrella and compatibility-wrapper boundary is vacuous for internal tiers and is still checked in the raw worker graph.

