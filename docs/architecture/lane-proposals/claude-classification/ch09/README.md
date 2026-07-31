# Chapter 09 migration contract

This semantic contract was used for the completed Chapter 9 migration. The 11
frozen owners account for exactly 4,420 format-2 declarations (4,392 public,
28 private), now routed to 20 canonical destinations.

Every declaration has one authoritative source-span route and one canonical
owner. Compiler-generated declarations follow their longest authored `.ilean`
root. Private authored roots have explicit rewrites. `owner-dag.tsv` is
acyclic; `direct-imports.tsv` records canonical dependencies plus the imports
needed by historical wrappers; and downstream consumers are enumerated.

Implementation status: `INTEGRATED_POST_PASS`.

The final integration ran `check_ch09_contract.py --mode post` against a fresh
format-2 graph and the frozen baseline. All 4,420 declarations, 23,898 typed
internal edges, 56 destination-DAG edges, 280 exact imports, and 28 authored
private rewrites passed.
