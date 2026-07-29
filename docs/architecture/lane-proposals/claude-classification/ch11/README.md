# Chapter 11 migration contract

This is a proposal-only semantic contract. It moves no production declaration
and changes no shared manifest. The 66 frozen owners
account for exactly 6385 format-2 declarations
(6239 public, 146 private).

Every declaration has one authoritative source-span route and one proposed
owner. Compiler-generated declarations follow their longest authored `.ilean`
root. Private authored roots have explicit rewrites. `owner-dag.tsv` is
acyclic; `direct-imports.tsv` records canonical dependencies plus the imports
needed by historical wrappers; and downstream consumers are enumerated.

Implementation status: `BLOCKED_ON_CH09_INTEGRATION`.

Run `check_ch11_contract.py --mode pre` before using the
contract. Post/stage comparison requires a fresh candidate format-2 graph and
is intentionally not claimed by this preparation lane.
