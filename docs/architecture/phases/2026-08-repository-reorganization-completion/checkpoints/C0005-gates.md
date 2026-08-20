# C0005 final acceptance evidence

Checkpoint code commit: `ad92bbfae62d538f3e52829a269a846688a8e213`

Acceptance status: **accepted**

At `2026-08-20T16:23:16Z`, `primary-human` accepted C0005 for the already
integrated R04/R08 epoch. M04, M08, B0008, and B0009 are accepted at exact code
commit `ad92bbfae62d538f3e52829a269a846688a8e213`. M07 is ready, but R07 remains
blocked until the exact acceptance-control commit receives its own green CI
attestation. Branch retirement is a separate later control and has not been
performed.

## Exact green code run

[GitHub Lean CI run 32336207465](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/32336207465)
completed successfully for exact code commit
`ad92bbfae62d538f3e52829a269a846688a8e213` on `main`. The run was created
at `2026-08-20T05:35:56Z` and updated at `2026-08-20T05:47:53Z`. Build job
[96326170176](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/32336207465/job/96326170176)
ran from `05:36:00Z` through `05:47:52Z`. Its architecture and source-graph
step passed from `05:36:27Z` through `05:40:22Z`; its library and smoke build
passed from `05:40:22Z` through `05:46:35Z`.

This successful run proves the integrated code checkpoint and its code gates.
The exact acceptance-control commit SHA and CI run/job attestation necessarily
arise after this report is committed and pushed, so they are deferred to the
later separate CI-attestation/retirement control.

## Delivery ancestry and reviewed integration

R04 delivery `e92d0fa270b1113ea630f41c4c797051e68e5d26` and R08 delivery
`e9a09b17deabe14baaa56036e55eeb6ac67b04fb` remain immutable. True merge
`2acb84e0d6f8c9a0db24598f888f434a9c1a62e3` has parents control commit
`bccfa46a3f7b711e867d6db3e548afdc9d8804a0` and the R04 delivery. True
merge `8fc86ff0a1b1c36d840164e1ea4ee5512f3a417e` has parents the R04 merge
and the R08 delivery. Reviewed union integration commit
`7beb0e7985f2a884c2462acc12055bf4db38a9c0` is the direct child of the R08
merge; the exact code checkpoint is its README-only direct child.

B0008 pins R04 delivery report SHA-256
`7BF2595C90D0EF596E775551E6720CEBD7E0B0EC4771E4301D4487096FE56B5A`
and changed-path evidence SHA-256
`7E8DDFF03575A1FE0A06BFFA6ED0179704C0719008D07C9476486497B8A69B59`.
B0009 pins the corresponding R08 values
`075999311C84BB0D5840FC404E037FCBAC7F30448A18CA4B4D231EEF9AC3CB07`
and `2DECA01F09462F4259533447CF580640D67A32A78C84AF90C4C20780451F6A1F`.

R0009 has 28 paths and R0010 has 14 paths. Their exact intersection is five
paths and their reviewed common-base union is 37 paths. The historical union
patch remains SHA-256
`0D646D4658D0AEDBEDCDE397553B1AEF31662130545750DA27061299BD11545B`.
The reviewed one-row MIGRATION preimage amendment leaves that patch unchanged
and pins the live union postimage ledger at SHA-256
`5863BBC2098493D221F3EF0DD50EA82874E50D1A2E7F720DDA4D340985FF67FE`.
The union review is SHA-256
`8D7085A7335E6B73C7A201DAA6C2FE5A2A557F19957B2F1EAED44AAFFD829CEA`.

The required merge-to-checkpoint range
`8fc86ff0a1b1c36d840164e1ea4ee5512f3a417e..ad92bbfae62d538f3e52829a269a846688a8e213`
contains exactly 45 paths: 44 modifications and one addition, with no
deletion or rename. Its ordinal newline-terminated path-set digest is
`F490D275D8F715279AC1C351FF103CC059C6B7B0879D1AA53D45CC2D34E5B9B7`.
`C0005-integrator-paths.tsv` classifies every path exactly once:

| Category | Paths |
| --- | ---: |
| reviewed R0009/R0010 union | 37 |
| aggregate follow-up | 1 |
| bounded test follow-up | 1 |
| integration documentation | 1 |
| delivery control | 2 |
| integration-amendment artifact | 2 |
| validator follow-up | 1 |

## Projection replay

Both immutable format-2 projections replay against the fresh C0005 acceptance
graph, whose raw SHA-256 is
`85C7B3D06019C92B7234EF5422681E46A9825F733A1AC4AB58A3F8B9B91C345B`.
The candidate scan contains 56,903 declarations and 649,259 typed
signature-plus-body graph edges.

| Projection | Frozen graph SHA-256 | Result |
| --- | --- | --- |
| P0008 / R04 | `5207DDA1BBA72F0802ACDA0A286611B62A07A72C9DF4E50E0E5F1EC048887540` | PASS: 289 selected, 252 relocated, 990 signature edges, 2,239 body edges, 50 exact allowed owners |
| P0009 / R08 | `CE770EBE7B3170BA808D22D2AD603B7266A8AADC550864902423FD33162FA1FF` | PASS: 211 selected and relocated, 1,229 signature edges, 2,886 body edges, 66 exact allowed owners |

P0008 also verifies all 115 private normalizations against
`B0008-private-normalization.tsv` SHA-256
`2349DFA9F94EEB183359B57A870E8F2CC5068662FB69EC4799FE7D99914858C1`.
P0009 verifies all 48 private normalizations against
`B0009-private-normalization.tsv` SHA-256
`335C3FE17716B3391962CC68EFAD81673E1BAE0E4B4C2F0720C0906703786FC0`.
Both replays report zero mismatch.

## Fresh baseline, inventory, and strict-source evidence

The combined extractor ran against the exact clean code tree:

`python -B tools/architecture/generate_baseline.py --output-dir docs/architecture/phases/2026-08-repository-reorganization-completion/baselines --name C0005-combined --keep-dependency-tsv benchmark-results/C0005-combined.tsv`

A separate deterministic `--dependency-tsv benchmark-results/C0005-combined.tsv
--check` replay passed.

| Artifact | Bytes | SHA-256 |
| --- | ---: | --- |
| `C0005-combined.json` | 93,696 | `2FC0C95FFECF114A2EDB8C14DB8C2874BDBB85FCEBA722C345AA084B3E97C02A` |
| `C0005-combined.md` | 16,373 | `69FF97AF03CD489AAA9A47240169217628293CD1DB33AAB02D174BF501B0EB49` |
| raw `benchmark-results/C0005-combined.tsv` | 117,155,707 | `85C7B3D06019C92B7234EF5422681E46A9825F733A1AC4AB58A3F8B9B91C345B` |
| `C0005-inventory.tsv` | 629,256 | `7C383B1AF57F65F9559C81402013412172CC93B623F7ED2E26968B9C7AFB4172` |
| `C0005-integrator-paths.tsv` | 3,697 | `58A5A2DB792912CA44C915F776CC1152EC0096BDA63ACB85AF88D752823C28E1` |
| strict `source-check.json` | 80,344 | `9274DCB026787683A1CB9859A7456B01B0D8CDDFDB3D6C2CBC65502EB108DF6B` |
| strict `source-check.md` | 4,830 | `7412118265C9198547E220F197F1DA1A6454032F579AA978312C19FF7C4525B6` |

The baseline records `library_source_clean: true` and an empty source
dirty-path list. It contains 2,818 production modules, 3,988,413 source lines,
1,457,120 nonblank lines, 74,852,110 source bytes, and 30,211 direct imports
(18,736 internal and 11,475 external). Its declaration graph contains 56,903
declarations, 266,387 signature edges, 382,872 body/proof edges, and 424,082
union edges.

The inventory has 2,818 unique ordinal module rows: 2,671 already complete and
147 still in scope. Remaining assignments are I01=12, R07=45, R09=72, and
R10=18. Its live classification values are exactly 2,818 production, 2,685
classified, 133 unclassified, and zero mixed.

## Static architecture and local Lean gates

Fresh live measurements are:

- tiers: 1,165 source, 383 aggregate, 577 compatibility, 553 reusable, two
  internal, five upstream, 133 unclassified, and zero mixed;
- layout: zero missing module docstrings, 76 noncanonical modules, one
  declaration-bearing umbrella, and zero unsorted aggregate imports;
- compatibility: 577 forwarding modules, 1,787 canonical targets, and two
  exact retained-production-import exceptions;
- provenance: 137 Apache-marked production files and five evidenced upstream
  modules;
- strict source: zero unresolved project imports, cyclic strong components,
  reusable-to-Source paths, reusable-to-Mixed paths, forbidden reusable
  edges, or forbidden reusable reachability.

The following local integrated-code checks passed:

- `python -B tools/architecture/check_completion_phase.py --self-test`;
- `python -B tools/architecture/check_phase.py --self-test`;
- `python -B tools/architecture/check_completion_phase_projection.py --self-test`;
- `python -B tools/architecture/check_phase.py --all-phases`;
- `python -B tools/architecture/check_layout.py`;
- `python -B tools/architecture/check_compatibility.py`;
- `python -B tools/architecture/check_provenance.py`;
- `python -B tools/architecture/generate_baseline.py --skip-declarations --strict-source --output-dir benchmark-results/architecture --name source-check`;
- `git diff --check`;
- `lake build NumStability NumStabilityTest`, 11,894 jobs, exit zero;
- `lake test`, exit zero with a final 11,892-job denominator.

The phase-specific checker patch passes its adversarial self-test and validates
the authority-materialized C0005 postimages. Its accepted path requires one
19-path acceptance-control commit whose direct parent is exact code checkpoint
`ad92bbfae62d538f3e52829a269a846688a8e213`, final authority-complete gate
evidence, refreshed lifecycle hashes, and current acceptance narratives. The
exact acceptance-control commit SHA and CI run/job are intentionally not inputs
to that commit; their attestation is deferred to the later separate control.

## Acceptance gate decision

| Gate | Acceptance status | Evidence |
| --- | --- | --- |
| R04/R08 architecture and scope | PASS | ancestry, immutable delivery pins, common-base union, 45-path ledger, and both projection replays agree |
| compatibility | PASS | 577 wrappers, 1,787 targets, two exceptions |
| layout contract | PASS | checker passes with measured residual queue |
| provenance | PASS | 137 Apache-marked files and five upstream modules |
| strict source | PASS | zero unresolved, cyclic, or forbidden paths |
| full code build | PASS | local 11,894-job build and exact-code GitHub run |
| full tests | PASS | local `lake test` and exact-code GitHub run |
| classification complete | FAIL | 133 modules remain unclassified |
| canonical layout complete | FAIL | 76 noncanonical modules and one declaration-bearing umbrella remain |
| documentation current at acceptance | PASS | C0005 checkpoint, phase, lifecycle, and five acceptance narratives agree |
| prepared acceptance checker | PASS | adversarial self-test and live C0004/delivered evidence-prepared state pass |
| accepted-C0005 evidence checker | PASS | authority timestamp, final gates, lifecycle postimages, and narratives agree |
| acceptance-control CI | DEFERRED | exact commit SHA and CI run/job attestation belong to the later separate control |

Repository-wide and bounded-phase completion therefore remain `incomplete`.
This acceptance is limited to M04/R04 and M08/R08; it is not honest
100% reviewed-module completion.

## Authority-materialized acceptance

Tracked authority assigns integration, shared-path, branch-registry,
release-manager, and `main`-push authority only to `primary-human`. The
temporary operator grant for the R04/R08 epoch explicitly grants no
checkpoint-acceptance, shared-path, integration, or main-push authority and
expires at C0005.

The `primary-human` acceptance action occurred at the single RFC3339 UTC
timestamp `2026-08-20T16:23:16Z`. The final controls fix `accepted_by` and both
`resolved_by` values to `primary-human`, and reuse the checkpoint `accepted_at`
value for both request `resolved_at` values. The resulting acceptance-control
commit SHA and its successful CI run/job are outputs that necessarily arise
only after that commit is materialized and pushed; they are not acceptance-
commit inputs and are deferred to the later separate CI-attestation/retirement
control.

The authority-materialized acceptance-control transitions are:

1. C0005 records parent C0004, commit
   `ad92bbfae62d538f3e52829a269a846688a8e213`, the generated artifact pins
   above, `accepted_by: primary-human`, accepted time
   `2026-08-20T16:23:16Z`,
   and ordered `milestones_satisfied` exactly
   `[M01, M02, M03, M04, M05, M06, M08, M11, M12]`. Its gate array contains
   every and only `architecture`, `canonical_import`, `combined_baseline`,
   `compatibility`, `focused_build`, `full_build`, `full_tests`, `layout`,
   `old_import`, `provenance`, `scope`, and `strict_source`, all passing and
   all linking the final `C0005-gates.md` digest.
2. `phase.current_checkpoint_id` changes from C0004 to C0005; M04 and M08
   change from `ready` to `accepted` with `accepted_checkpoint_id: C0005`;
   M07 changes from `planned` to `ready` but is not activated. Both
   completion statuses `incomplete`.
3. Restore `claude-lane.operator_ids` to only `claude-local` by removing the
   temporary `codex-local` grant. Release exactly 32 temporary R0009/R0010
   exact shared reservations, reducing exact reservations from 187 to 155
   while retaining all five prefix reservations.
4. Change B0008 and B0009 from `delivered` to `accepted`; set integration to
   method `merge`, accepted checkpoint C0005, and accepted SHA
   `ad92bbfae62d538f3e52829a269a846688a8e213`. Change retirement from
   `not_due` to `due`; keep `ancestry_checkpoint_id`, `retired_at`, and
   `retired_by` null. Refresh each branch's evidence hashes for the final
   status-only projection JSON and authority-materialized request JSON
   postimages. C0005 ancestry is recorded only by the later, separate
   retirement control.
5. Retire P0008 and P0009 by status only. Do not alter either projection
   graph, checker contract, selector, expected counts, or other immutable
   projection content.
6. Change R0009 and R0010 from `active` to `applied`; resolve them at C0005
   and the exact code SHA, with `resolved_by: primary-human`, `resolved_at`
   equal to C0005 `accepted_at`, the final gate-report digest, and reason
   exactly: "Applied as the independently replayed and reviewed R0009/R0010
   shared-file union after both immutable delivery merges, with the reviewed
   migration-ledger re-anchor and two bounded integration follow-ups." Do not
   alter either request payload, patch, postimage evidence, or union artifact.
7. This final gate evidence records
   C0005 accepted by `primary-human`, the acceptance time, exact integrated
   code SHA, and the successful generated/code gates above. It must explicitly
   defer the not-yet-existing acceptance-control commit SHA and CI run/job to
   the later separate CI-attestation/retirement control. Update root README,
   `docs/README.md`, migration, phase-index README, and completion-phase README
   only to report C0005, exact code SHA, 2,818/2,685/133/0, M04/M08 accepted,
   M07 ready, and R07 still blocked.
8. Commit every and only the 19 bounded acceptance paths as one direct child
   of `ad92bbfae62d538f3e52829a269a846688a8e213`: the five narratives; the two
   baseline files; inventory, integrator ledger, final gates, and C0005 JSON;
   phase JSON; B0008/B0009, P0008/P0009, R0009/R0010 JSON; and the completion
   checker. No naming, umbrella, outlier, production, or test path is allowed.

The following evidence must not change during finalization:

- both delivery commits and every file under
  `docs/architecture/deliveries/R04/` and
  `docs/architecture/deliveries/R08/`;
- `P0008.tsv.gz` and `P0009.tsv.gz` at the hashes above, and every non-status
  field of P0008/P0009;
- `R0009.patch`
  (`3277A434AEA678551274D55953FDBA72A44A46DE1235C1B747126A39DC0E1BCA`),
  `R0010.patch`
  (`DE6D0A2217D3644D8957830C02F91C99FB44E863FA973CAA698794A498D19A2B`),
  their postimage ledgers, the historical union patch, the reviewed amended
  union ledger, and their review evidence;
- both complete private-normalization maps and all other frozen branch
  planning/delivery evidence;
- the exact code checkpoint and the generated baseline, inventory, integrator
  ledger, and strict-source bytes recorded above.

This is the acceptance handoff boundary. C0005 was accepted by `primary-human`
at `2026-08-20T16:23:16Z`; the exact acceptance-control commit SHA and CI
run/job attestation are deferred to the later separate control. Only after that
green run may a separate, acceptance-SHA-pinned checker/control ratchet record
branch retirement, C0005 ancestry, retirement time, and ref evidence. The
checker intentionally rejects premature B0008/B0009 `retired` state. R07 must
not begin until that exact acceptance-control CI is green.
