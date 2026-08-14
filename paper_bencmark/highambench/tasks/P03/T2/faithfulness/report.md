# Faithfulness audit: P03-T2

- Classification: `faithful-equivalent`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `c1a51572740227518bfd522a791529384858f6e65f0ba1a97c276a3ff651db85`
- Paper SHA-256: `952c6827db21fb2a9362b5aa4d38a1b2c75361f2cc7a3badbb7cd4a232d7b7bc`

## Decision

The declaration faithfully packages the theorem-relevant semantics of Algorithm 1.1 as exact real equations and perturbation bounds. This is the same abstraction used by the paper after deriving (3.3) and (3.6), not an unrelated axiomatic recurrence. The source explicitly supports iteration-dependent solver coefficients, and the complete alpha_i and beta_i formulas match pointwise. The claimed stronger theorem is therefore not a genuine additional result: it arises only from treating the paper's relational error model as though it had required an unformalized bit-level execution predicate. Both implication directions hold, so the final classification is faithful-equivalent.

## Implications

- **Lean implies paper:** `yes`. Every Algorithm 1.1 execution covered by the paper supplies a P03NormwiseIRRun through equations (3.3), (2.4), and (3.6), the precision and gamma conditions, and Ainv=A^{-1}. Restricting the Lean universal statement to those certificates gives exactly Theorem 4.1.
- **Paper implies lean:** `yes`. At the standard real error-model level used in the PDF, an arbitrary P03NormwiseIRRun contains exactly the hypotheses invoked in the A824-A825 derivation. That derivation is relational and uses no additional representability, primitive-rounding, initial-solve-accuracy, or solver-implementation premise. It therefore yields the Lean recurrence for every bundled run.

## Findings

No findings were recorded.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `pass` | `unclear` |
| `S04` | `pass` | `pass` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `unclear` |
| `S11` | `pass` | `fail` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `pass` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `86` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `86` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/agent_outputs/adjudicator.json` (`4babaf55f846c1ac98a9664188c49593bdec295610329dba2c398be88ab52374`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/agent_outputs/blind_translation.json` (`57edd17f93741207b0541606237efb76e23820ac3950d8ebe2120c13f8172cc8`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/agent_outputs/direct_judge.json` (`3b339ee1224e39771b0f282efe2beeedd369bc1ddaa0c3b4a5ef3386ede89562`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`b3cc11ba900435d88cf7ef1319e83fbe08b2565dd47c617a404f04aca0ef17a6`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/agent_outputs/source_contract.json` (`44b6c1379e2def7538a19a88c5342fa8bbd73b1b5908742040d7b9be32f6a439`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/decision.json` (`d2e88990198546ce4a2a574130b8e18a799107bb03554eed70ccd6f8b2612306`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/history/20260814T130941Z/agent_outputs/adjudicator.json` (`9540bd24ff65eca1686973fba10b0d43d05706e540cf98b6652c48915f75e413`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/history/20260814T130941Z/agent_outputs/blind_translation.json` (`7a709e23b4d0b6f0acf85e23575101b8c089346d402ad1f5fbde4d703a78ba1b`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/history/20260814T130941Z/agent_outputs/direct_judge.json` (`b718c55bc841cc60d22c2ebc3c1a414317ab65531ebe388351fdab49ba8d9139`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/history/20260814T130941Z/agent_outputs/paper_source_contract.json` (`cc0f2d27697c7df47ddee702a54285359037d701ffa45ec71a92ca67f9cf3902`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/history/20260814T130941Z/agent_outputs/roundtrip_judge.json` (`f4367e675e64d5be771c53f61529f3c9fc7e0795d192d58520031757d8c5f680`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/history/20260814T130941Z/agent_outputs/source_contract.json` (`6238c3e81bd12967d34f9ac792d05105850a9bb827e4afefb13a74d5fde55e36`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/history/20260814T130941Z/decision.json` (`07a980e9fb4fb58477cd353d3beb542ea1633e5fc776d1510bc98150505f1a30`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/history/20260814T130941Z/inputs/blind_dependency_inventory.json` (`2da72aa9ce5b39d1706de5df7e7a62e27855215427f3d9f7f40b68b42c869fc9`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/history/20260814T130941Z/inputs/blind_dossier.md` (`09cd89ee345fe1154ed27672fe5f47d98e7c78d20adf508cff044d8eb9353717`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/history/20260814T130941Z/inputs/blind_review_packet.md` (`09cd89ee345fe1154ed27672fe5f47d98e7c78d20adf508cff044d8eb9353717`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/history/20260814T130941Z/inputs/declaration_dossier.md` (`a43d3c2fe615c196388643076bfeb43459ca5404bc43b691ec0451551ca8541a`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/history/20260814T130941Z/inputs/dependency_inventory.json` (`2da72aa9ce5b39d1706de5df7e7a62e27855215427f3d9f7f40b68b42c869fc9`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/history/20260814T130941Z/inputs/dependency_reuse_direct.json` (`8307a591e1b18f2ed5f23349b7779ed27235b8b1296facab38ecf7440bc5b3b5`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/history/20260814T130941Z/inputs/direct_review_packet.md` (`ac4210aaaa538ef44ad2f115c9970f6be4e01a2bcd3963cbec70c50be01e5a62`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/history/20260814T130941Z/inputs/paper_source_locator.json` (`d325b31e2cf1ecac253237196c87cfb8e169960305af1f36083a03802a8829df`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/history/20260814T130941Z/inputs/source_locator.json` (`ebfbaab25c5c2277850ce5b8f18e0b77c6e84a171076b966702c91d34ec092ae`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/inputs/blind_dependency_inventory.json` (`9c4909c9303de12e3ba22cff8e5b759e34d1d7f7d82c94adfe3ee51ebbf91d92`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/inputs/blind_dossier.md` (`679e8d041812bb0e91de004d9c850f21905430b5ffaa2b90054226ff0e85ab5e`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/inputs/blind_review_packet.md` (`679e8d041812bb0e91de004d9c850f21905430b5ffaa2b90054226ff0e85ab5e`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/inputs/declaration_dossier.md` (`01d325c6bee046df9e6749f27839381cb491e734df2c04e778abb688c428b08a`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/inputs/dependency_inventory.json` (`78d1820c56d648c38ecf2eb98efeda861ebac3056922253913e7c16ce6dc91c3`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/inputs/direct_review_packet.md` (`edf75f0188db5826d3c58fe981fc713f6de1bdb397e78d3607e8b3d0cb1c1194`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/inputs/source_locator.json` (`109d6591f0cbefe26d79e813ebc1b7b912bc06a80cf00d957b438e0a37a467ce`)
