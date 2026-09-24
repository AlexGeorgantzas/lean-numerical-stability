# Pilot 29 prospective admission screen (not a measured outcome)

As of 2026-09-24 00:14 UTC, the ten-task **draft** schedule passed the
fail-closed admission builder on Titan. Its record is
`/hdd/alexgeorgantzas/highambench/pilot29-private-admission/ADMISSION_10_DRAFT.json`
(SHA-256 `503fbe455447ea81569825b5f1649123fe8c7784d32b45d85ad939fc758ecb1c`).
This does not launch a pilot or establish that a formalizer will actually
reuse the library or complete a proof. Nine tasks inherit independently
audited faithful Pilot 26 L statements with direct declaration reach; the
tenth, CAST08-PROP3.1, has newly checked private evidence. The improved
CAST08-PROP3.2 candidate replaces the weaker prior FPModel-only uptake
screen with direct `fl_dotProduct` reach.

| New private screen | Exact Titan result |
| --- | --- |
| CAST08-PROP3.1 source | First review was `needs_correction` solely because the packet omitted a discrepancy in printed Figure 3.1(a). The packet now explicitly selects the prose/diagram/proposition algorithm and discloses the defective propagation loop. A fresh paper-only GPT-6 Astra/high review of that revised packet returned `faithful`; record SHA-256 `d85576526f16dba08f656343b5d25c4ceb37c811b4a1d1167baaf77516f3dfb9`. |
| CAST08-PROP3.1 candidate | The unchanged private Lean source SHA-256 `4fcc84a2aabc63534fa96dccf11bd7d09caccdd031bbd4f842152c06c10b408c` compiles with one permitted target `sorry`; the exact-snapshot semantic closure reaches `NumStability.fl_recursiveSum`. A fresh multi-role, condition-blind audit against the revised packet returned faithful-equivalent; result SHA-256 `c4e191e0a1652d6a0f94e92fecde14ea6303d67ae9ce49e703f1e8b286d3723c`. The earlier audit against the superseded packet was not used for admission. |
| CAST08-PROP3.2 candidate | The improved private source SHA-256 `0030d21b33ea9652ef47594c1e80e3284f9b2ff55c4879ad76dd61bd49f2b209` compiles and directly reaches `NumStability.fl_dotProduct`; a fresh multi-role, condition-blind audit returned faithful-equivalent. Result SHA-256 `012b384c99d2c1801111a19bc7146ca84c9a5207dd1ef91c4ecd6d35f6249469`. Its previously accepted source-only packet review remains unchanged. |

The admission verifier checks packet and PDF hashes, source-only review,
candidate and semantic-manifest hashes, prior campaign/pair hashes, accepted
candidate-specific audit, exact direct-reach names, and target-collision
attestation. The collision screens are manual source/signature scans, not
formal proofs of absence. Private skeletons are not copied into contestant
workspaces.

**Remaining before a full run:** seal and review all Pilot 28 canaries, decide
whether its proof-stage behavior exposes a fixable protocol flaw, then mint a
final corpus/admission/controller snapshot with a new Pilot 29 identity. The
draft ten are outcome-aware. Four use foundational finite-format/polynomial
declarations rather than task-specific algorithm/error results, and H20-8
does not require FPModel; these strata must remain explicit in the thesis.
