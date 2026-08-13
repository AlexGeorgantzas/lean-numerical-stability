# R12 projection replay

P0004 is replayed against the final full format-2 candidate with its exact 14
recorded checker arguments. Only the candidate placeholder is substituted; the
checker, graph, selector, private map, allow-list, and their hashes remain
frozen at active control.

Required projection results are 34 selected and relocated declarations, 80
signature edges, 133 body/proof edges, and 139 union edges, with zero private
normalizations. CHECK_PROJECTION.py independently verifies the projection graph
union count as well as the official checker output and global candidate totals.

The full candidate TSV/JSON/Markdown hashes and byte-identical deterministic
summary replay are recorded in GATE_RESULTS.tsv.
