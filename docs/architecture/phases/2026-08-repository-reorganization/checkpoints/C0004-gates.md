# C0004 acceptance evidence

Checkpoint commit: `b56f609f3bf66b5d7d0b677567cce82fee0c275b`

Accepted at: `2026-08-03T00:51:53Z`

## Remote gate

[GitHub Lean CI run 30774901719](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/30774901719) completed successfully at the exact checkpoint commit. The architecture/contract source-graph step and `lake build NumStability NumStabilityTest` both passed. The job ran from `2026-08-03T00:37:12Z` to `2026-08-03T00:51:20Z`; the architecture step completed at `2026-08-03T00:40:25Z` and the full build completed at `2026-08-03T00:51:18Z`.

## Local gates

The exact checkpoint tree passed the phase self-tests and live contract, layout, compatibility, provenance, strict source graph, focused W12 build, full `lake build NumStability NumStabilityTest`, and `lake test`. The full local build completed successfully with 5,743 jobs after 369.3 seconds; `lake test` exited zero after 7.0 seconds. The W12-focused aggregate passed with all 109 import tests. Separate canonical-only and old-only builds passed for 67 canonical modules and 42 compatibility modules, respectively.

Layout passed over 1,669 production modules with 319 unclassified modules, 9 mixed modules, 190 missing module docstrings, 265 noncanonical names, 14 declaration-bearing umbrellas, and zero unsorted aggregates. Compatibility passed with 327 forwarding modules and 643 canonical targets. Provenance passed with 204 Apache-marked production files and 5 evidenced upstream modules. Strict-source generation found zero forbidden reusable reachability.

The fresh combined extractor completed `lake build NumStability` and generated a clean format-2 graph at commit `b56f609f3bf66b5d7d0b677567cce82fee0c275b`: 56,903 declarations in 1,151 declaration-bearing modules, 266,387 signature edges, 382,872 body/proof edges, and 424,082 union edges. The dependency TSV has SHA-256 `F4902E7AA53CFA483F6DA7467541AC0774B942C68BD064A56353E1CB7A85DB58`.

## W12 projection and scope

The frozen P0004 graph replay passed against the fresh full stream: 4,197 declarations, 10,175 signature edges, 23,388 body/proof edges, and 24,179 union edges. Exactly 2,647 declarations moved to allowed canonical owners; names, kinds, visibility, and every incident typed edge were preserved.

The delivered commit `380d3cba83bb9e3704232720f371f28cbbc673da` is an ancestor of the checkpoint. Its hash-pinned scope evidence covers all 42 exact owners and 65 destination prefixes with zero forbidden worker writes. The integrator reconciled the recorded W12-to-W02 imports, applied the authorized shared tier, aggregate, compatibility, and root-test changes, and repaired seven ambient import boundaries with narrow canonical or reusable imports before running every global gate.

## Retirement state

W12 is accepted at C0004 and P0004 is retired as immutable evidence. B0003 remains recoverable with retirement due until this acceptance-control commit itself is green on `main`; only then may its remote branch be deleted and the deletion recorded. B0002's remote branch was deleted at `2026-08-02T23:32:59Z` after C0003 acceptance and is recorded retired here.
