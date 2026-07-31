# Lane delivery report

## Identity

- Lane: `classification-ch09-ch11`
- Engine/subscription: `Claude subscription 4`
- Repository/remote: `https://github.com/AlexGeorgantzas/lean-numerical-stability.git`
- Frozen base SHA: `6487fc33088523b8f27ecde9ad613515b78f9977`
- Branch: `codex/org-classification-prep`
- Final implementation HEAD (parent of report commit): `73390d325d0a88957f9e5a7a8416a19e2396cf8a`

## Ordered commits

1. `c89b74daa1ecec2629d89585f2d083943d549565` — Workstream A: the byte-frozen 386-module inventory copy, the reviewed tier proposal (313 source, 68 reusable, 4 mixed_pending_split, 1 aggregate), the generated summary, and the three deterministic checkers plus the review-safe apply tool.
2. `e144534a3ea469c2b60de36fdf5362a6fc4fb664` — Workstream B: the Chapter 9 format-2 preparation contract -- 36 routes, 4,420 owned declarations across 35 destinations, owner DAG, 252 planned imports, 28 private rewrites, 29 consumers, frozen acceptance record -- and its checker.
3. `62256cf64d83d2a8064d8db05bb715c0a98fdbb1` — Workstream C: the Chapter 11 format-2 preparation contract over exactly the 66 candidate rows -- 75 range plus 3 exact routes, 6,385 owned declarations across 74 destinations, 146 private rewrites, 60 consumers, 11 recorded Chapter 9 edges -- and its checker.
4. `73390d325d0a88957f9e5a7a8416a19e2396cf8a` — Isolated worker smoke and axiom-probe modules, the deterministic validation evidence, the read-only refresh appendix against origin/main, and the validation runner.

## Scope

- Scope-check command/result: `python scripts/check_scope.py --repo workspace/lean-numerical-stability --owned OWNED_PATHS.txt --forbidden FORBIDDEN_PATHS.txt --allowed-new ALLOWED_NEW_PREFIXES.txt --base-file BASE_SHA.txt` — passed; 4 commits inspected, 52 touched paths, all 52 new, none forbidden or unowned`
- Changed paths: `52 new files, all under the three owned prefixes: docs/architecture/lane-proposals/claude-classification/ (28), tools/architecture/lane_claude_classification/ (9), NumStabilityTest/Worker/ClassificationAudit/ (19). Full list in delivery/GIT_METADATA.txt`
- Forbidden/shared paths changed: `none — git diff over base..HEAD restricted to everything outside the three owned prefixes is empty, so no production Lean file, aggregate, manifest, existing test, report, example, or root file differs from the frozen base`
- Integrator-only patch requests: `one, at PACKET_ROOT/INTEGRATOR_REQUEST.md — create the declaration-free NumStabilityTest/Worker/ClassificationAudit.lean aggregate and add its single import to NumStabilityTest.lean, so the 19 isolated worker modules become reachable from the root test aggregate; both paths are outside this lane's allowlist`

## Semantic evidence

- Pristine source/blob/.ilean hashes: `/home/mymel/lean/reorg/claude-classification/runtime/pristine-baseline (external, non-repository); 77 candidate modules with source, .ilean and .olean SHA-256 recorded in SOURCE-HASHES.json, manifest SHA-256 8074D81614187939FD6886DE37F9A9D137F570CF7F2A676414EE909EC660321A`
- Baseline declaration TSV: `packaged immutable format-2 stream baseline/parallel-base-declarations-v2.zip, SHA-256 1C2538B428B8EC3610B3C09BBB6A4CF23ECA9F0DB17EE4AE5B63E4F371AECDED; Chapter 9 slice 4420 declarations (normalized SHA-256 311844A5A4603D8F70831746F566D63E645F1AB37F002B8EB18861D10ACA58C5), Chapter 11 slice 6385 declarations (normalized SHA-256 09641A56F129CD1871B51A9536C71F62B785F4E32B96403F130CF4197BCE20C9)`
- Candidate declaration TSV: `not applicable in a preparation-only lane — no declaration is moved, so there is no migrated tree to extract; check_ch09_contract.py and check_ch11_contract.py --mode post refuse to run rather than fabricate one, and the integrator generates it after the waves are implemented`
- Ownership/signature comparison: `exact against the frozen baseline — every one of the 4420 Chapter 9 and 6385 Chapter 11 baseline declarations is owned exactly once, with kind and visibility preserved; both pre gates pass`
- Signature typed-edge comparison: `Chapter 9 20081 edges, SHA-256 766C39099C4FBCC11D7F9365F5F43F85E5EDBABA31A626B6F35E5AC2825CB415; Chapter 11 61653 edges, SHA-256 8C2F935B94B1A3EB57517312335D5FC7FCEEC173239970B06BCE680E2504D626; both destination graphs proved acyclic`
- Body/proof typed-edge comparison: `Chapter 9 26737 edges, SHA-256 70055A704124A763F9CF1146D97A949804A940EB7390F3940B1B59F7E98E3143; Chapter 11 69376 edges, SHA-256 F735C281C278BF9788FD5740E9D7F34B7333B3DDCE7F2D9FF045E9250EDC1010; kept strictly separate from the signature graph and proved acyclic independently`
- Reviewed private-owner normalization: `28 Chapter 9 and 146 Chapter 11 rewrites, one per private declaration, in ch09/private-rewrites.tsv and ch11/private-rewrites.tsv; every candidate name differs from its historical name and no other normalization is permitted`

## Verification

- Ownership checker negative self-tests: `all four self-tests pass — proposal checker exit 0 (pass), apply tool exit 0 (pass), Chapter 9 exit 0 (pass), Chapter 11 exit 0 (pass); each rejects every mutation of a valid table, including route gaps, overlaps, cycles, unchanged private names, and undeferred reusable-to-source rows`
- Pre/stage/post ownership gates: `pre passes for both chapters (Chapter 9 exit 0 (pass), Chapter 11 exit 0 (pass)); stage and post are documented interfaces that deliberately refuse to run in this preparation-only lane because they require a freshly generated candidate stream`
- Canonical-only tests: `exit 0 (pass) — the existing canonical Chapter 11 source aggregate and its Theorem 11.7 leaf compile in isolation; the 15 already-existing proposed canonical families each compile in their own import-only module, all passing`
- Isolated old-only tests: `Chapter 9 historical imports exit 0 (pass), Chapter 11 historical imports exit 0 (pass) — all 11 and all 66 historical candidate paths compile standalone, with no root test aggregate in scope`
- Focused leaf builds: `Chapter 9 eleven-module build exit 0 (pass), Chapter 11 historical plus canonical build exit 0 (pass)`
- Downstream builds: `every command in DOWNSTREAM_BUILDS.txt ran; 34 of 35 recorded gates pass and the one failure is the layout reachability finding below`
- Layout/compatibility/provenance/strict-source gates: `compatibility exit 0 (pass) (108 forwarding modules, 208 targets), provenance exit 0 (pass) (207 Apache-marked files, 5 evidenced upstream modules); layout exits 1 solely because the 19 isolated worker modules are not reachable from NumStabilityTest, which needs the integrator-only patch in INTEGRATOR_REQUEST.md — all six legacy-debt counters are byte-identical to the frozen base (603 unclassified, 0 mixed, 216 missing docstrings, 399 naming exceptions, 0 declaration-bearing umbrellas, 0 unsorted aggregate imports). No strict-source baseline was regenerated: this lane must not touch shared baselines`
- `lake test`: `exit 0 (pass)`
- `lake build NumStability NumStabilityTest`: `exit 0 (pass) — Build completed successfully (5,376 jobs)`
- Axiom probes: `all four representative public declarations depend on exactly [propext, Classical.choice, Quot.sound] — NumStability.higham9_1_exists_partialPivotChoice, NumStability.higham11_3_oneByOne_step_factorization, NumStability.dotProduct_factor_expansion_succ, and NumStability.Ch11Closure.TriGrowthInv.higham11_7_bunch_tridiagonal_actual_schedule_middle_solve; recorded by NumStabilityTest/Worker/ClassificationAudit/AxiomProbe.lean`
- `git diff --check`: `exit 0 (pass); also clean over 6487fc3..HEAD`
- Final clean status: `git status --porcelain=v1 is empty and the frozen base is an ancestor of HEAD`

## Cross-lane notes

### Ordering constraints the integrator must honour

1. **BlockLU/Chapter 13 before Chapter 9.** `HighamChapter9.lean` imports
   `Algorithms.LU.BlockLU` and `Algorithms.LU.GrowthFactor`
   (`KNOWN_CROSS_LANE_EDGES.tsv`, `CH9_TO_BLOCKLU`). `ch09/acceptance.json`
   records `BLOCKED_ON_BLOCKLU_INTEGRATION`.
2. **Chapter 9 before Chapter 11, never in parallel.**
   `ch11/acceptance.json` records `BLOCKED_ON_CH09_INTEGRATION` and lists all
   eleven destination-level Chapter 9 edges; each must be retargeted onto the
   Chapter 9 canonical destination that owns the referenced declaration before
   Chapter 11 is implemented.
3. Within each chapter, implement in `owner-dag.tsv` topological order using the
   exact import list in `direct-imports.tsv`.

### The three provisional BlockLU rows

`Ch14Problem142`, `HighamChapter9`, and `MatrixInversionMethod2BInstance` carry
`BLOCKLU_REFRESH_REQUIRED`. `REFRESH-APPENDIX.md` verifies against
`origin/main` at `48242807` that the first two differ from the frozen base by
**imports only**, with a zero non-import diff (`direct_project_imports` moves
3 → 5 and 5 → 8 respectively), and that `HighamChapter9.lean` is now a 16-line
facade. `check_classification_proposal.py --check` recomputes those columns from
the working tree, so re-running it on integrated `main` reports exactly those
mismatches until the rows are refreshed. That is the intended signal.

### What the integrator must rerun

1. `check_read_only_inventory.py` and `check_classification_proposal.py --check`
   on integrated `main`; expect mismatches confined to the 31 frozen rows listed
   in `REFRESH-APPENDIX.md` §2.
2. `apply_tier_proposal.py` against a lane-owned review copy, then the real
   manifest. Applying the 372 non-deferred rules leaves **zero** forbidden
   `reusable -> source/mixed` reachable pairs and raises coverage from 451/1054
   to 823/1054 production modules. It then makes
   `docs/architecture/layout-exceptions.json` stale in both directions —
   `unclassified_modules` shrinks by up to 372 and `mixed_modules` gains 4 — so
   `check_layout.py --write-baseline` is required after review.
3. The `INTEGRATOR_REQUEST.md` test-wiring patch, after which
   `check_layout.py` passes on this branch.
4. `check_ch11_contract.py --mode pre` after retargeting the Chapter 9 edges.

### Deliberate non-actions

This lane created no canonical production module, moved no declaration,
rewrote no proof, edited no import, added no wrapper, regenerated no shared
baseline, and touched no shared manifest. `ch09/` reconciles against the Chapter
9 split already landed on `main`: the declaration, command-group, private, and
facade totals match exactly (4,420 / 4,108 / 28 / 11), while the destination
granularity and leaf naming differ and are offered as a reviewed alternative —
notably `Theorem14.Actual`, `Theorem14.DiagonallyDominant`, and
`Theorem14.Primitive`, which satisfy the two-digit locator rule where main's
`Theorem914*` names sit in its noncanonical debt baseline.

### Reviewer entry points

`classification/README.md` states the tier discriminator, the derived-column
policy, the three structural gates, and the four-module split queue.
`ch09/README.md` and `ch11/README.md` state the mathematical seams, the
compatibility policy, and the dependency order. `VALIDATION.md` is rendered from
`VALIDATION.json`, so the human and machine records cannot disagree.
