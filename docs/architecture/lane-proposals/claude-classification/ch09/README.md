# Chapter 09 migration contract

This is a proposal-only semantic contract. It moves no production declaration
and changes no shared manifest. The 11 frozen owners
account for exactly 4420 format-2 declarations
(4392 public, 28 private).

Every declaration has one authoritative source-span route and one proposed
owner. Compiler-generated declarations follow their longest authored `.ilean`
root. Private authored roots have explicit rewrites. `owner-dag.tsv` is
acyclic; `direct-imports.tsv` records canonical dependencies plus the imports
needed by historical wrappers; and downstream consumers are enumerated.

Implementation status: `READY_AFTER_QR_INTEGRATION`.

Run `check_ch09_contract.py --mode pre` before using the
contract. Post/stage comparison requires a fresh candidate format-2 graph and
is intentionally not claimed by this preparation lane.
