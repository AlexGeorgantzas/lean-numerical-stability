# Chapter 11 migration contract

This semantic contract was used for the completed Chapter 11 migration. The 66
frozen owners account for exactly 6,385 format-2 declarations (6,239 public,
146 private), now routed to 73 canonical destinations.

Every declaration has one authoritative source-span route and one canonical
owner. Compiler-generated declarations follow their longest authored `.ilean`
root. Private authored roots have explicit rewrites. `owner-dag.tsv` is
acyclic; `direct-imports.tsv` records canonical dependencies plus the imports
needed by historical wrappers; and downstream consumers are enumerated.

Implementation status: `INTEGRATED_POST_PASS`.

The final integration ran `check_ch11_contract.py --mode post` against a fresh
format-2 graph and the frozen baseline. All 6,385 declarations, 81,069 typed
internal edges, 289 destination-DAG edges, 537 exact imports, 61 Chapter 9
dependency rows, and 146 authored private rewrites passed.
