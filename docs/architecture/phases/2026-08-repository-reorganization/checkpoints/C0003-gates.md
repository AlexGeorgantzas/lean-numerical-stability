# C0003 acceptance evidence

Checkpoint commit: `bb80c95a4625e07535dacdda12d246ee1a5795b3`

Accepted at: `2026-08-02T23:16:46Z`

## Remote gate

[GitHub Lean CI run 30769033575](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/30769033575) completed successfully at the exact checkpoint commit. The architecture/contract source-graph step and `lake build NumStability NumStabilityTest` both passed. The job ran from `2026-08-02T21:57:48Z` to `2026-08-02T23:15:39Z`; the architecture step completed at `2026-08-02T22:01:00Z` and the full build completed at `2026-08-02T23:15:37Z`.

## Local gates

The exact checkpoint tree passed the phase self-tests and live contract, layout, compatibility, provenance, strict source graph, focused W02 build, full `lake build NumStability NumStabilityTest`, and `lake test`. The full local build exited zero after 3,222 seconds; `lake test` exited zero after 7.8 seconds. The W02-focused aggregate covers all 142 import tests. Separate canonical-only and old-only builds passed for 123 canonical modules and 19 compatibility modules, respectively.

Layout passed over 1,600 production modules with 338 unclassified modules, 9 mixed modules, 191 missing module docstrings, 277 noncanonical names, 14 declaration-bearing umbrellas, and zero unsorted aggregates. Compatibility passed with 308 forwarding modules and 605 canonical targets. Provenance passed with 207 Apache-marked production files and 5 evidenced upstream modules. Strict-source generation found zero forbidden reusable reachability.

The fresh combined extractor completed `lake build NumStability` and generated a clean format-2 graph at commit `bb80c95a4625e07535dacdda12d246ee1a5795b3`: 56,903 declarations in 1,103 declaration-bearing modules, 266,387 signature edges, 382,872 body/proof edges, and 424,082 union edges. The dependency TSV has SHA-256 `16CD7D4421007F75E479F92F34C461ACA0D89BFE41BC121089BC02C69A9E40F2`.

## W02 projection and scope

The frozen P0002 graph replay passed against the fresh full stream: 4,195 declarations, 18,256 signature edges, 30,343 body/proof edges, and 32,459 union edges. Exactly 2,220 declarations moved to allowed canonical owners; names, kinds, visibility, and every incident typed edge were preserved.

The delivered commit `799d781971eed851cd90152c0d9acb0e828f9341` is an ancestor of the checkpoint. Its hash-pinned inventory contains exactly 386 worker paths, all covered by B0002's 73 exact owners or 65 destination prefixes, with zero forbidden or shared worker writes. The integrator applied the requested shared tier, aggregate, compatibility, root-test, and import-retargeting changes before running the global gates.

## W12 refresh

The frozen P0003 graph also replayed against C0003: 4,197 declarations, 10,175 signature edges, 23,388 body/proof edges, and 24,179 union edges, with zero declarations relocated before W12 integration. P0004 therefore refreshes the same byte-identical projection onto C0003. B0003 records the seven import-only same-path overlaps and reserves the delivered 17 dependency pairs for resolution during C0004 integration; W12 remains delivered and unaccepted at this checkpoint.
