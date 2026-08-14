# Fresh exact-C0003 successor review: R05 and R06 pair selection

Authority: `primary-human`, delegated for this review to `claude-local`.
Exact code checkpoint: C0003 `e20de2f931caa12221e708c341e9cb4f64d29b25`
(Lean CI run 31799323377). Control chain verified: acceptance-control
`3ea3efc914b0243673c316f11eda3cba576bebad` (CI 31833161196 failed) cured by
`a61438448beb02773ef6b0f4f50cbedf8d675d29` (CI 31833811860 success at
2026-08-14T19:42:15Z) before retirement
`14f69f0d3a2ce6ae7bee801eef0859f04144bc9a` (CI 31835422242 success,
retired 2026-08-14T19:54:32Z); the R03 remote delivery ref is deleted and
verified absent; B0005 is retired; no C0002-based selector, projection, or
preimage is reused anywhere in this review.

Graph: `benchmark-results/C0003-combined.tsv` SHA-256
`98199873425E068D3B74F8595A6CFB9AFE5532974186FD760DFD122B0D273626`
(the audited R03 delivery candidate, byte-identical declaration content to
the C0003 tree). Module-import truths were recomputed from the pristine
C0003 blobs (production content at the control tip is verified
byte-identical to exact C0003 code).

Owner lists (newline-delimited module-name SHA-256):

| Wave | Owners | Declarations | Owner-list SHA-256 |
| --- | ---: | ---: | --- |
| R05 (least-squares-underdetermined-ch20-ch21) | 48 | 3,171 | `58B40E2DF08D75C722CCC5DAC207CA93C2271256AB14E4845CA495881D6C1DDF` |
| R06 (schur-sylvester-pivoting-ch09-ch11-ch16) | 75 | 9,415 | `04263170A0BF31877610C3A8FB20C5A8C80A9F74861D93B7648C4F7EA7FA546A` |
| R07 (matrix-functions-powers-ch18) | 45 | 194 | `69DC952AB3D29EA7638019137E1AABCF971564444752F833534BAE8421D514E8` |

Pairwise seven-dimension counts at exact C0003 (A→B / B→A where directed):

| Dimension | R05×R06 | R05×R07 | R06×R07 |
| --- | --- | --- | --- |
| owner exact / ancestor overlap | 0 / 0 | 0 / 0 | 0 / 0 |
| destination overlap (proposed, casefold) | 0 | - | - |
| direct owner-import edges | 0 / 0 | 0 / 0 | 0 / 0 |
| transitive owner-reachability pairs | 0 / 0 | 1 / 0 | 1 / 0 |
| typed signature edges | 0 / 0 | 0 / 0 | 0 / 0 |
| proof-body edges | 0 / 0 | 0 / 0 | 0 / 0 |
| shared direct outside production consumers | 0 | 0 | 2 |

Raw shared direct importers before the R11/R12 umbrella exclusion: R05×R06
has exactly `NumStability.Algorithms`; R05×R07 has exactly
`NumStability.Algorithms`; R06×R07 has `NumStability.Algorithms`,
`NumStability.Analysis`, and the two genuine production consumers
`NumStability.Source.Higham.Chapter28.Section06.Companion.Companion` and
`...Companion.CompanionSpectral`. Global umbrella aggregates are
integrator-owned shared paths and are excluded exactly as the accepted
R11/R12 review excluded its "harmless common transitive umbrella set";
they are handled by the reviewed R0006/R0007 union.

Decision: **R05+R06 is the only authorizable pair** (zero on all seven
dimensions). R05×R07 and R06×R07 each have a transitive owner-reachability
crossing, and R06×R07 additionally has two genuine shared production
consumers, so no R07 pair is authorized; M07/R07 remains planned.

Design facts frozen with this selection:

* Every route in both waves is a whole-owner route (one owner, one
  destination). No owner splits across destinations, so no private-sharing
  component can separate: the R03 fanIn7 defect class is impossible by
  construction. Private closure is recorded per declaration in
  `branches/B0006-private-closure.tsv` and `branches/B0007-private-closure.tsv`.
* R05: 21 whole-owner relocations, 7 Chapter 20 declaration-bearing
  umbrellas extracting their whole declaration sets to new `.Core` leaves,
  13 declaration-free legacy modules classified `compatibility` in place,
  and 7 retained outlier-review owners. 574 relocated declarations,
  61 private normalizations, 19 retargeted outside consumers.
* R06: 48 whole-owner relocations, 21 declaration-free legacy modules
  classified `compatibility` in place, and 6 retained outlier-review
  owners (including the five largest chapter-9/11 section modules, which
  do not move). 2,094 relocated declarations, 195 private normalizations,
  45 retargeted outside consumers.
* Retargeted consumers cannot lose transitive supply: every destination
  carries its owner verbatim with the owner's complete original import
  list, and the dot-notation field-projection scans
  (`branches/B0006-field-projection-scan.tsv`,
  `branches/B0007-field-projection-scan.tsv`) record every candidate
  field-notation reference (Chapter27.SoftwareEnvironment lesson).
* The frozen scope binds R05 and R06 to `codex-lane`. Parallel execution
  is authorized by the reviewed temporary second-operator expansion in
  `reviews/R05-R06-operator-authorization.md` (claude-local, scoped to
  B0006/R05 only, expiring at C0004), mirroring the accepted R12 and R03
  expansions; the frozen scope assignment itself is unchanged.
