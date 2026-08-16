# C0004 acceptance evidence

Checkpoint code commit: `783ae9a4951407ece046adb8631d5a8ff1795a18`

Accepted at: `2026-08-16T18:23:52Z`

## Exact green code run

[GitHub Lean CI run 31962707569](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/31962707569)
completed successfully for the exact checkpoint code commit on the `main` push
event. The run was created at `2026-08-16T17:48:31Z` and completed at
`2026-08-16T18:20:48Z`. Build job
[95203051003](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/31962707569/job/95203051003)
ran from `17:48:34Z` through `18:20:48Z`. Its architecture and source-graph
step passed from `17:49:04Z` through `17:52:58Z`; its clean library and
smoke-test build passed from `17:52:58Z` through `18:20:46Z`.

## Immutable deliveries, true merges, and controls

R05 delivery `26e89100b3c7c8a64a41426d517cbd563a40db72` and R06 delivery
`bfaf2ae917ed79165caa6cc58b3782984aa8d3d9` are direct children of exact
C0003 code `e20de2f931caa12221e708c341e9cb4f64d29b25`. True merge
`538c7d248a0ccaec407a082ecb73b92d7c3faec2` has parents exact private-map
control `d6a241de6c2af12439bc48885461c7190fc751d6` and the immutable R05
delivery. True merge `deee8e7ea0aeac7cfbd9fc2582eaf1f5b841fd0c` has parents the R05
merge and the immutable R06 delivery. Integration commit
`783ae9a4951407ece046adb8631d5a8ff1795a18` is the direct child of the R06
merge.

| Control | Commit | CI run |
| --- | --- | ---: |
| planned | `b6794f326313f8077c0c3433bb9c76b6e2ed5361` | 31844203563 |
| activation | `405e76f36a342a5d7d31a8e094cc7c580dcb250f` | 31845432265 |
| private-map totality amendment | `d6a241de6c2af12439bc48885461c7190fc751d6` | 31893563259 |

B0006 pins R05 delivery report SHA-256
`D2312C4F659D28FE8F3F71AB00197AEC142DB9BF2C0212C237AC5ABBDC229D92`
and changed-path evidence SHA-256
`75E134DF96BC611B96097C1337F995AEC75FA75AB953745BABCB5F44D6AAD608`.
B0007 pins the corresponding R06 values
`A698EA26FB8E99507291515013D74DE2EBB0E57669C1AE96A1CA71ED772E97FB`
and `DF6E279A0CB17B7B315E45CD024923DE8384E43AC6AAAC19E2BE5B36A8DBE9E3`.

## Delivery, union, and amendment audit

R05 covers 48 historical owners and 3,171 selected declarations: 574 relocate
to 28 destinations and 2,597 remain across seven reviewed outlier owners. It
creates 21 declaration-free wrappers and seven declaration-free umbrellas.
R06 covers 75 historical owners and 9,415 selected declarations: 2,094
relocate to 48 destinations and 7,321 remain across six reviewed owners. It
creates 48 declaration-free wrappers and preserves 21 already
declaration-free compatibility owners. No historical path was deleted or
Git-renamed.

R0006 (23 paths) and R0007 (49 paths) intersect on five integrator-owned
paths. Their 67-path reviewed zero-context union patch has SHA-256
`639DA03437C3FBAA6934E71B55EFE7D85DF51835D94978790C59162585690D4E`;
the immutable union postimage ledger has SHA-256
`D36AEB47BF5F09AF693CEC2EBACDB1566EC4ED91D0F301F6F11BC7603311BDB8`.
Freeze-time disposable-index replay verified the union 67/67 and the two
requests 23/23 and 49/49. The union was applied exactly once after both true
merges, never as sequential whole-file request replacement.

The terminal integration tree accounts for all 67 union paths exactly:

- 61 remain byte-exact to their union postimages;
- four are superseded by exact R0008 postimages, with each immutable union
  `postimage_sha256` equal to its R0008 `preimage_sha256`;
- two, `NumStability/Algorithms/LinearSystems.lean` and
  `NumStability/Source/Higham/Chapter21.lean`, contain only their reviewed
  aggregate follow-ups.

The four chained amendment paths are `NumStability/Algorithms.lean`,
`NumStability/Algorithms/Sylvester.lean`, `NumStability/Analysis.lean`, and
`docs/architecture/COMPATIBILITY.md`. R0008's 27-path, 36-hunk patch has
SHA-256 `2FB6F4D07E8EBB270BF710D972958F20F1F53452A52DB081D953B231742D66D4`;
its postimage ledger has SHA-256
`F23881D337127F0F408105512222F8EB10DDD671F186291F932659D1A77C25E7`.
Independent custody replay and the committed-tree audit both verify 27/27
postimages. The immutable approval addendum has SHA-256
`228565D2C26E5610C36CC94B51B15E02C29EFABEA339F08A88E09355A7488D38`
and pins the reviewed draft SHA-256
`7A4529D9994506AD3EEBD17504BDE331DC95F42CBF3B5307643D44F97D726338`.

R0008 replaces 59 production imports of declaration-free historical facades
and corrects 36 compatibility-table rows. Its approved Source-trim decision
keeps the `NumStability.Algorithms` `NumStability.Source.` direct-import
ceiling at 49 without changing `layout-exceptions.json`; the facade-to-facade
exemption and the five production retained-closure files remain intentional.
The predecessor union ledger remains untouched.

## Merge-to-integration scope ledger

The required range
`deee8e7ea0aeac7cfbd9fc2582eaf1f5b841fd0c..783ae9a4951407ece046adb8631d5a8ff1795a18`
contains exactly 111 unique paths: 106 modifications and five additions, with
no deletion or rename. The ordinal path-set digest is
`1A74FDA432A9A55BC1026DB46E1A17018FF7F783149375C85C1F7DCE625621BE`.
`C0004-integrator-paths.tsv` classifies every path exactly once:

| Category | Paths |
| --- | ---: |
| reviewed R0006/R0007 union postimage | 61 |
| reviewed R0008 integration amendment | 27 |
| aggregate follow-up | 6 |
| milestone-DAG refresh | 3 |
| integration documentation | 4 |
| integration-amendment artifact | 5 |
| delivery control | 2 |
| validator follow-up | 2 |
| bounded Algorithms smoke-test follow-up | 1 |

The ledger has SHA-256
`E5F12E1834F848C7A2FAAD674BBDEEC0B3760B44BE17D073460E87F3E437F378`.

## Static architecture and Lean gates

Fresh evidence directory `.lake/integration-r05-r06-20260816T172806Z`
records all 11 candidate gates as passed. Its authoritative preflight held
`main` at `deee8e7ea0aeac7cfbd9fc2582eaf1f5b841fd0c`, exactly 111 staged
paths, and index fingerprint
`42B668934F795A4D1BDD5D43ECB935C2894AE248A7FF56F31C0C007F18E3F2EC`.
The final HEAD and index fingerprint were identical, `stable_tree` is true,
and no step failed. `DONE.json` has SHA-256
`A5DA29ED1EE40AF2A4B3967EDB1981ECB041A5821D61EDD117F3F8A55735C166`.

The following candidate gates exited zero under Windows named mutex
`Local\lean-reorganization-2026-08`:

- completion-phase self-test and full completion check;
- all-phase contract check;
- layout, compatibility, and provenance checks;
- strict-source extraction;
- placeholder scan over `NumStability` and `NumStabilityTest`;
- committed-basis `git diff --check`;
- `lake build NumStability NumStabilityTest`;
- `lake test`.

The exact-code CI architecture step additionally passed Python compilation,
the phase-checker self-test, and both projection-checker self-tests. Measured
static results are 2,766 production modules, 2,575 classified modules
(93.095%), 191 unclassified modules, zero mixed modules, zero missing module
docstrings, 125 noncanonical names, eight declaration-bearing umbrellas, and
zero unsorted aggregate imports. Tier counts are 1,124 source, 377 aggregate,
523 compatibility, 544 reusable, two internal, five upstream, and zero mixed.
Compatibility reports 523 forwarding modules, 1,425 canonical targets, and
two exact retained-production-import exceptions. Provenance reports 137
Apache-marked production files and five evidenced upstream modules. The
placeholder scan reports zero findings.

The full candidate build completed 11,687 jobs in 231.811 seconds with zero
error lines. `lake test` exited zero in 14.130 seconds with a final 11,685-job
denominator and zero error lines. The exact-code GitHub run then independently
proved the committed integration tree on a clean runner.

## Official C0004 combined baseline

The official extractor ran against the exact integration code tree under the
named mutex:

`python -B tools/architecture/generate_baseline.py --output-dir docs/architecture/phases/2026-08-repository-reorganization-completion/baselines --name C0004-combined --keep-dependency-tsv benchmark-results/C0004-combined.tsv`

It completed 6,128 jobs. A separate deterministic
`--dependency-tsv benchmark-results/C0004-combined.tsv --check` replay exited
zero. The baseline records exact commit
`783ae9a4951407ece046adb8631d5a8ff1795a18`, `library_source_clean: true`,
and an empty source dirty-path list. It contains 2,766 production modules,
3,986,088 source lines, 1,454,947 nonblank lines, 74,712,781 bytes, and 28,456
direct imports (17,344 internal and 11,112 external). Its declaration graph
contains 56,903 declarations, 266,387 signature edges, 382,872 body/proof
edges, and 424,082 union edges.

- JSON SHA-256: `D3F30A410903B1CA2858951CB26107B94B62630BC424723A0EC9EDF484AEDDDF`
- Markdown SHA-256: `E6D14B92A4D310BB64EF4DBE9F378BB8E0EA5A58B5BBC058AAA43181300F3BB1`
- raw dependency TSV SHA-256: `98C9C0CA7266A7CF295A27D5D119903F0EF239349F3FBC6C57F29BE9FBF602AB`
- raw dependency TSV bytes: 117,096,952
- C0004 inventory SHA-256: `08FA3E41DA0C72E7F5D4ECFD315F0CC6C73EB0F45089CF1DAC6AB04A81A1E326`
- C0004 integrator ledger SHA-256: `E5F12E1834F848C7A2FAAD674BBDEEC0B3760B44BE17D073460E87F3E437F378`

The deterministic inventory has 2,555 already-complete rows, 211 remaining
in-scope rows, and 200 distinct rows carrying residual architecture debt. The
123-member R05/R06 selector union and all 76 new production modules are now
complete. The inventory is LF/no-BOM, contains 2,766 unique ordinal module
rows, and has 625,733 bytes.

Fresh exact-C0004 strict-source extraction exited zero and found zero
unresolved project imports, cyclic strong components, reusable-to-Source
paths, reusable-to-Mixed paths, or forbidden reusable edges and reachability.
Its ignored JSON is 82,796 bytes with SHA-256
`B61E185D8D26A22583991FA82B06E8CFC98C9CA8EC5466F272132CD7BF227B79`;
its ignored Markdown is 4,873 bytes with SHA-256
`F3A3EB2CA4913A7E82019B2294B61B9D33B92DCF96D90DF1BB2EDFC4873A681C`.

## Final gates and bounded-phase decision

| Final gate | Status | Evidence |
| --- | --- | --- |
| architecture | PASS | phase, deliveries, requests, amendment chain, replay, scope, ancestry, and validators pass |
| build profiles | PASS | exact full production/test build and `lake test` pass |
| canonical layout | FAIL | 125 noncanonical and eight declaration-bearing umbrella modules remain |
| classification complete | FAIL | 191 production modules remain unclassified |
| compatibility | PASS | 523 wrappers, 1,425 canonical targets, and two exceptions pass |
| documentation current | PASS | C0004 checkpoint and migration controls are current at acceptance |
| entrypoint reachability | PASS | layout reports zero supported-entrypoint reachability failures |
| forbidden reachability zero | PASS | strict-source reports zero forbidden paths |
| full build | PASS | local candidate and exact green remote full builds pass |
| full tests | PASS | full test root and `lake test` pass |
| generated artifacts absent | PASS | zero tracked generated artifacts |
| module documentation | PASS | every production module has a module docstring |
| outlier review | PASS | exact 61/4/2 union terminal audit and 27/27 amendment audit pass |
| provenance | PASS | 137 Apache-marked and five evidenced upstream modules pass |

Because canonical-layout and classification-complete gates still fail and 200
residual-debt rows remain, bounded-phase and repository-wide completion stay
`incomplete`. C0004 accepts M05/R05 and M06/R06 only. M04/R04 and M08/R08
become dependency-ready; M07/R07 and every other unaccepted milestone remain
planned. No successor wave is authorized or activated.

## Acceptance and retirement boundary

C0004 accepts M05 and M06 at the exact green integration code commit. B0006
and B0007 become accepted with retirement due; P0006 and P0007 become retired
immutable evidence; R0006, R0007, and R0008 become applied. The temporary
`claude-local` second-operator authority on `codex-lane` expires, restoring
the lane to `codex-local` alone.

The two exact remote delivery refs and named worker worktrees remain present
until the acceptance-control commit itself passes Lean CI. Only then may
ignored delivery evidence be hash-verified and archived, each remote ref be
deleted with its exact-tip lease, and each clean worker worktree be removed
without force in a separate retirement control. Local delivery branches
remain preserved at their immutable tips.
