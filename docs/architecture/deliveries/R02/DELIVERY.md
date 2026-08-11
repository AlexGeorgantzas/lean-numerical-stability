# R02 delivery — residual norm estimation and Chapter 15

Successor wave R02 of the August 2026 repository-reorganization **completion** phase.
Routes the 142 declarations of the 28 residual owners to the 14 canonical destinations
frozen by P0002, leaving every historical owner an import-only compatibility wrapper.

Base: C0000 `b1b18772d80185ec08f49c818919558645c330a1`.
Branch: `codex/reorg-completion-2026-08-r02-norm-estimation-ch15`.
Authority: B0002 / P0002. Operator: `claude-local`.

## Scope

| quantity | value |
| --- | ---: |
| owners (selector rows) | 28 |
| declaration-bearing / declaration-free | 14 / 14 |
| declarations | 142 |
| private / public | 76 / 66 |
| kinds | 122 theorem, 20 definition |
| relocated / retained | 142 / 0 |
| canonical destinations | 14 (all populated) |
| private reverse closure | 123 = 76 private + 47 public |
| private normalizations executed | 76 |
| test modules | 63 |
| changed paths | 113 |

## Frozen mapping executed, not derived

B0002 ships the reviewed route map, so R02's job was faithful execution plus proof of
faithfulness. Verified against P0002 before emit:

* route map covers the 142 declarations exactly, and agrees with the graph on kind,
  visibility and owner for all 142;
* `normalization_decision` is `approved_owner_block_route` for all 142, and **no owner fans
  out** — each bearing owner routes its whole block to exactly one destination;
* the private normalization covers the 76 privates exactly, all 76 targets distinct, and
  every destination agrees with the route map;
* the recomputed private reverse closure (123) is **identical** to B0002's reviewed sheet.

Because each bearing owner routes as a whole block, the destination takes the owner's body
**verbatim** — namespaces, `variable`/`open` ambient context, `noncomputable section`,
attributes and proof text all move untouched, so no signature or proof can drift. All 76
private renames are module-prefix-only with **zero** logical-name collisions, so every
ordinal stays `0` and no source identifier is rewritten anywhere in this wave.

## Gates

All exit codes are `subprocess.run` return codes with output captured beside them.

| gate | exit | jobs |
| --- | ---: | ---: |
| `lake build NumStability` | 0 | 2,116 cold / 182 incremental |
| `lake build NumStability NumStabilityTest` | 0 | 2,772 cold / 2,355 incremental |
| 14 canonical-only test modules | 0 | 28 |
| 28 old-path-only test modules | 0 | 45 |
| 14 focused test modules | 0 | 28 |
| 7 protected-consumer test modules | 0 | 156 |
| `lake test` | 0 | 2,353 |
| `check_compatibility.py` | 0 | — |
| `check_provenance.py` | 0 | — |
| `generate_baseline --strict-source` | 0 | — |
| full format-2 candidate | 0 | — |
| **P0002 replay** | **0** | — |
| `check_layout.py` | **1** | 3 errors, all integrator-owned |

Static checks: B0002 scope guard 42/42 authorized and 0 forbidden touched; 0 import cycles;
0 owner wrappers containing a declaration; 0 reusable destinations reaching Source; 0
destinations importing an owner; 0 unreached owners and 0 unreached destinations under
`NumStability.Algorithms`.

`check_layout`'s three residual errors are the two aggregation gaps in integrator-owned
files (requests 6–7). With those applied it returns **exit 0, 0 errors**; the change was
then reverted, so the worker branch ships none of it.

## Findings

1. **Wrapper reachability is a graph property, not a per-edge one.** `NumStability/Algorithms.lean`
   imports only 21 of the 28 owners directly; the other 7 were reachable at C0000 solely
   through owner-to-owner chains. Rewriting any such edge breaks the aggregate's reach —
   expanding declaration-free imports orphaned 1 wrapper, and rewriting bearing imports
   orphaned 5. Keeping wrapper imports **verbatim** reproduces C0000 reachability exactly and
   is legal because wrappers are compatibility tier. Destinations still import no owner.
   A static reachability assert now runs before any build.
2. **The frozen projection cannot see the consumer boundary.** R02's in-wave tier counts are
   zero, yet five canonical destinations reach a historical owner repository-wide, carried
   exclusively by five integrator-owned modules. Proven by shortest path, and driven 5 → 0
   by the postimage in requests 1–5.
3. **Three harness faults were caught rather than shipped**, each of which would have put a
   false PASS in this file: a detached battery that silently no-opped because bare `python`
   did not resolve; `lake test` swallowed by an over-broad skip guard; and the replay
   "failing" because the completion phase pins its own checker, absent from the C0000
   checkout. Silence is not success, so every gate row here comes from a real return code.

## Artifacts

`CHANGED_PATHS.md`, `TEST_MATRIX.tsv`, `INTEGRATOR_REQUESTS.md`, `GATE_RESULTS.tsv`,
`DECLARATION_ROUTES.tsv` (142), `RETENTION.tsv` (28), `PRIVATE_CLOSURE.tsv` (123) / `.md`,
`ROUTING.md`, `PROJECTION.md`, and the executable auditors (`baseline.py`, `spans.py`,
`emit.py`, `cycles.py`, `statics.py`, `apply.py`, `gen_tests.py`, `postimage.py`,
`projection.py`, `gates.py`, `replay.ps1`).
