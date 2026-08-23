# R07 semantic routing

R07 covers 45 historical owners: 43 modules that were unclassified at C0005 and
the two reviewed naming-only owners already assigned to this scope. Routing was
performed from declarations and imports, not from filenames.

The 194 declarations split into 64 whole-owner routes and 130 split-owner routes.
They land in 30 destinations: 26 reusable mathematics leaves, three internal
support leaves, and one exact Higham Chapter 18 source-correspondence leaf.
`DECLARATION_ROUTES.tsv` is the exact reviewed declaration ledger;
`REALIZED_IMPORTS.tsv` is the exact 760-row post-move import contract for 87
modules.

All 13 declaration-bearing historical owners retain their public import surface
as import-only compatibility wrappers. The other 32 historical owners had no
format-2 declarations and remain byte-identical to C0005. `RETENTION.tsv`
records this owner-by-owner result, including base blobs and postimage hashes.

The raw worker tree intentionally exposes a five-destination transitive frontier
through integrator-owned shared consumers of the two naming-only historical
owners. It has no direct canonical-to-historical edge and no reusable/internal-
to-Source reachability. After exact R0011 replay, the five transitive paths
disappear; the disposable overlay checker requires the resulting frontier to be
empty.
