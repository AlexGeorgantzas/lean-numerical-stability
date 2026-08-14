# C0003 acceptance evidence

Checkpoint code commit: `e20de2f931caa12221e708c341e9cb4f64d29b25`

Accepted at: `2026-08-14T19:02:24Z`

## Exact green code run

[GitHub Lean CI run 31799323377](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/31799323377)
completed successfully for the exact checkpoint code commit on the `main` push
event. The run was created at `2026-08-14T12:12:07Z` and completed at
`2026-08-14T14:40:22Z`. Build job
[94763319735](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/31799323377/job/94763319735)
ran from `12:12:11Z` through `14:40:22Z`. Its architecture and source-graph
step passed from `12:12:40Z` through `12:16:30Z`; its clean library and
smoke-test build passed from `12:16:30Z` through `14:40:18Z`.

## Immutable delivery, true merge, and controls

R03 delivery `1f8ff4ca5b0b136901a2f47d43e1064dc09aa556` is a direct child of
exact C0002 code commit `9d2334d77f1a38f8a4caa81fe53eeb11a8e3e7cd`.
True merge `0ee06b61ca1c12e8f9492d79b85d1a515c652f09` has parents exact route
amendment control `09b3962dc6ed18b6de6eea5dc4a0e0e7c8ba4bb7` and the immutable
delivery. Integration commit `e20de2f931caa12221e708c341e9cb4f64d29b25`
is the direct child of that merge. The planned, activation, authority, and
route-amendment controls are all ancestors of the integration commit and each
has its own green Lean CI:

| Control | Commit | CI run |
| --- | --- | ---: |
| planned | `fb5a021b4640dd595a99f7560ce252ad9836a5b6` | 31691727184 |
| activation | `1166874cb986d09f357d092f1171a31d7f8b2332` | 31697060516 |
| second-operator authority | `c4f66cbdfdce6cf64d484be13290e7d2e60547f5` | 31719287142 |
| route amendment | `09b3962dc6ed18b6de6eea5dc4a0e0e7c8ba4bb7` | 31732612464 |

The authority review SHA-256 is
`F3ECCDACCB5762DD65C7020597F7BDC67990BC9CDB452103EB4B351ABF7E8E89`;
the route-amendment review SHA-256 is
`157A09272E3AD7DF1BC07059F9540A4F404005F56B5ED7361AADC3E39BF4E013`.
Both values are pinned in B0005 refresh evidence.

The route amendment is necessary and minimal. In the exact C0002 blob of
`NumStability.Algorithms.HighamChapters1To9SourceClosure`, private helper
`higham8_18_fanIn7AbsApply_nonneg` supplies both public theorems, so the
original Equation15/Equation18 split was not compilable. Exactly one
declaration-route cell, one module-route row, and one test-plan row changed.
The delivered Equation15 module is a documented declaration-free bridge.

## Delivery and replay audit

The independent delivery audit confirmed 47 historical owners and 2,389
selected declarations: 2,132 relocated and 257 retained across 11 retained
owners. All 36 historical wrappers are declaration-free and preserve the
retargeted original import surface. Relocated bodies match their exact C0002
blobs; all 398 frozen private normalizations are present and every retired
private name is absent. `Higham726Rump` lands under Chapter07/Equation26 and
`Chapter72` appears nowhere.

P0005 replayed against a freshly regenerated candidate with the complete
398-row private map and preserved exactly 2,389 selected declarations, 2,132
relocations, 28,180 signature edges, and 42,404 body/proof edges. The raw
candidate and official C0003 dependency TSV have identical SHA-256
`98199873425E068D3B74F8595A6CFB9AFE5532974186FD760DFD122B0D273626`.

R0005 replay from the exact merge commit with `git apply --unidiff-zero`
produced expected postimage tree
`11b2a268de2a65d87da5d2681e2482e87e989494`; reverse replay restored all
121 preimages. The final integration tree has exactly the corrected result:
115 request paths remain byte-identical to the expected postimage tree and
exactly six have reviewed bounded follow-ups:

- `NumStability/Algorithms.lean`: import-only canonical aggregate sorting;
- `NumStability/Analysis.lean`: import-only canonical aggregate sorting;
- `NumStability/Source/Higham/Chapter27/SoftwareEnvironment.lean`: the one
  restored `Chapter02.FloatingPointArithmetic.Environment` supply import;
- `docs/architecture/COMPATIBILITY.md`: wrapper rows reconciled in file order;
- `docs/architecture/layout-exceptions.json`: the exact ceiling and baseline
  ratchets;
- `docs/architecture/tiers.json`: the exact two source reclassifications, two
  entrypoint removals, and two compatibility reclassifications.

The expected-postimage-to-integration diff has exactly 27 paths: those six
request deviations plus 21 documented extras. The merge-to-integration diff
has exactly 142 paths: all 121 request paths plus the same 21 extras. The
Counterexample/Results cycle is absent. The milestone DAG quotient refresh is
exactly R05→R03 `25`, R06→R03 `1`, R08→R03 `7`, and R10→R03 `4`; its SHA-256
`D74D1D36353117A6931AAFA3ED9EEC026F892BA51C4490C492DE21A6A6D208B8`
is identically re-pinned in B0001 and B0002.

## Route-to-integration scope ledger

The required range
`09b3962dc6ed18b6de6eea5dc4a0e0e7c8ba4bb7..e20de2f931caa12221e708c341e9cb4f64d29b25`
contains 2,393 unique paths: 2,209 additions and 184 modifications, with no
deletion or rename. The ordinal path-set digest is
`1CB0EC11B0FC86B2F3BA74FCBDC11A9B14C9DE47458F7303028B6A5D968850FF`.
`C0003-integrator-paths.tsv` classifies every path exactly once:

| Category | Paths |
| --- | ---: |
| immutable delivery only | 2,251 |
| byte-exact reviewed R0005 request | 115 |
| six request-path bounded follow-up categories | 6 |
| bounded aggregate follow-up | 11 |
| bounded R03 test follow-up | 3 |
| integration documentation | 4 |
| milestone-DAG refresh and evidence re-pins | 3 |

The ledger has SHA-256
`FFD53CFFDC406EA62F2CB0380BD538CB5FE15DCBF4842377E01D990336030888`.

## Static architecture and Lean gates

All repository-owned commands below exited zero against the exact integrated
code commit before acceptance-control edits:

- `python -m py_compile` over the architecture tools;
- `python -B tools/architecture/check_phase.py --self-test`;
- both projection checker self-tests;
- `python -B tools/architecture/check_completion_phase.py --self-test`;
- `python -B tools/architecture/check_phase.py --all-phases`;
- `python -B tools/architecture/check_phase.py`;
- `python -B tools/architecture/check_completion_phase.py`;
- `python -B tools/architecture/check_layout.py`;
- `python -B tools/architecture/check_compatibility.py`;
- `python -B tools/architecture/check_provenance.py`;
- the layout checker's own placeholder and tracked-generated scans;
- `git diff --check`.

Measured static results are 2,690 production modules, 2,436 classified
modules (90.558%), 254 unclassified modules, zero mixed modules, zero missing
module docstrings, 217 noncanonical names, 15 declaration-bearing umbrellas,
and zero unsorted aggregate imports. Tier counts are 1,088 source, 377
aggregate, 420 compatibility, 544 reusable, 2 internal, 5 upstream, and zero
mixed. Compatibility reports 420 forwarding modules, 1,171 canonical targets,
and two exact retained-import exceptions. Provenance reports 137 Apache-marked
production files and five evidenced upstream modules. Placeholder/axiom files
and tracked generated artifacts both count zero.

All local Lean operations held Windows named mutex
`Local\lean-reorganization-2026-08`; checkpoint JSON normalizes the lock name
to `lean-reorganization-2026-08`.

- `lake build NumStability NumStabilityTest` exited zero in 42.1 seconds;
- `lake test` exited zero in 9.079 seconds, with a final 11,340-job denominator
  and zero error lines.

The exact main worktree was clean before and after the gates. A separate cold
disposable build remained healthy but was intentionally superseded after
87.8 minutes once the exact main tree's complete cache was verified; all of
its Lake/Lean processes were stopped before the required main-tree build.

## Official C0003 combined baseline

The official extractor ran from the clean integration code tree under the
named mutex:

`python -B tools/architecture/generate_baseline.py --output-dir docs/architecture/phases/2026-08-repository-reorganization-completion/baselines --name C0003-combined --keep-dependency-tsv benchmark-results/C0003-combined.tsv`

It completed 6,155 jobs in 169.5 seconds. A separate deterministic
`--dependency-tsv benchmark-results/C0003-combined.tsv --check` replay exited
zero in 23.0 seconds. The baseline records exact commit
`e20de2f931caa12221e708c341e9cb4f64d29b25`,
`library_source_clean: true`, and an empty source dirty-path list. It contains
2,690 production modules, 3,985,082 source lines, 1,454,099 nonblank lines,
74,663,808 bytes, 28,305 direct imports (17,193 internal and 11,112 external),
56,903 declarations, 266,387 signature edges, 382,872 body/proof edges, and
424,082 union edges.

- JSON SHA-256: `692A6834644BECABA4DB1C16FEB9B89CEB2DE1A2A5B8A1AF304F63F873433A5E`
- Markdown SHA-256: `27456CE0FB150FF6B5D6ED3007FC8A9832F6170D6894755B901CA9FF74E9E910`
- raw dependency TSV SHA-256: `98199873425E068D3B74F8595A6CFB9AFE5532974186FD760DFD122B0D273626`
- raw dependency TSV bytes: 117,090,975
- C0003 inventory SHA-256: `2FC73310A40763AA16AAC3D9EC1A0F3F6DF94AAEE188C4C4DB9BF62A34C67B33`
- C0003 integrator ledger SHA-256: `FFD53CFFDC406EA62F2CB0380BD538CB5FE15DCBF4842377E01D990336030888`

The inventory has 2,356 already-complete rows, 334 remaining in-scope rows,
and 310 distinct rows carrying residual architecture debt. All 47 exact R03
selector members are debt-free and complete; 48 new production modules are
debt-free and complete. The sole new debt is the pre-existing
`Problem09.DoubleRounding.Counterexample` module, whose cycle repair leaves a
declaration-bearing umbrella assigned to the already-planned final integrator
wave I01. This assignment does not activate or plan a successor wave.

The strict-source extraction
`python -B tools/architecture/generate_baseline.py --skip-declarations --strict-source --output-dir benchmark-results/C0003-strict-source --name source`
exited zero in 17.7 seconds and found zero unresolved project imports, import
cycles, reusable-to-Source paths, reusable-to-Mixed paths, or forbidden
reusable edges. Its ignored JSON and Markdown SHA-256 values are
`5F25DFB44E3AA2DCCE01B3DBCB639B6C89D20F0D02039B6320069DE9A80F26A5`
and `04AF9462C212C195CFBC2C651B0B65F03C6C4455227B60209B33B2A93B4FA6B0`.

## Final gates and bounded-phase decision

| Final gate | Status | Evidence |
| --- | --- | --- |
| architecture | PASS | phase, delivery, request, replay, scope, ancestry, and validators pass |
| build profiles | PASS | exact full production/test build and `lake test` pass |
| canonical layout | FAIL | 217 noncanonical and 15 declaration-bearing umbrella modules remain |
| classification complete | FAIL | 254 production modules remain unclassified |
| compatibility | PASS | 420 wrappers, 1,171 canonical targets, and two exceptions pass |
| documentation current | PASS | checkpoint and migration controls are updated at C0003 acceptance |
| entrypoint reachability | PASS | layout reports zero supported-entrypoint reachability failures |
| forbidden reachability zero | PASS | strict-source reports zero forbidden paths |
| full build | PASS | local and exact green remote full builds pass |
| full tests | PASS | full test root and `lake test` pass |
| generated artifacts absent | PASS | zero tracked generated artifacts |
| module documentation | PASS | every production module has a module docstring |
| outlier review | PASS | corrected six-path and 21-extra bounded audit is exact |
| provenance | PASS | 137 Apache-marked and five evidenced upstream modules pass |

Because canonical-layout and classification-complete gates still fail and 310
residual-debt rows remain, bounded-phase and repository-wide completion stay
`incomplete`. C0003 accepts M03/R03 only. M05 and M06 become dependency-ready;
M07/R07 and every other unaccepted milestone remain planned. No successor wave
is authorized or activated.

## Acceptance and retirement boundary

C0003 accepts M03 at the exact green integration code commit. B0005 becomes
accepted with retirement due; P0005 becomes retired immutable evidence; R0005
becomes applied. The temporary `claude-local` authority on `codex-lane` expires,
while B0005 retains its historical two-operator attribution. The 91 R0005-only
shared reservations are released; all 30 pre-existing permanent controls
remain reserved. The remote delivery ref and worker worktree remain present
until the acceptance-control commit itself passes Lean CI. Only then may
evidence be archived, the ref be deleted with its exact-tip lease, and the
worktree be removed without force in a separate retirement control.
