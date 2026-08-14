# Faithfulness audit: P03-T2

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `66d46e86e70b37c6e4436debab03f0701acef350c440deeace177e718b6433a9`
- Paper SHA-256: `952c6827db21fb2a9362b5aa4d38a1b2c75361f2cc7a3badbb7cd4a232d7b7bc`

## Decision

The paper's one-step analysis is intrinsically about Algorithm 1.1: equations (3.3), (3.6), and (4.1), together with solver condition (2.4), establish three compatible estimates for the same indexed computation and then produce Theorem 4.1. The declaration accurately reproduces their final algebraic sum, but it promotes those estimates to independent hypotheses over arbitrary real scalars and erases every condition connecting them to an algorithmic execution. Consequently the declaration cannot yield the paper theorem. Conversely, the paper yields the scalar conclusion only under the intended algorithmic instantiation; it does not entail the declaration's universal implication for all real assignments. Since neither full proposition implies the other, the correct classification is not-faithful-different.

## Implications

- **Lean implies paper:** `no`. The declaration assumes hid, hres, hsolve, and hupdate and merely adds their scalar upper bounds. It contains no matrix, vector, infinity norm, nonsingularity condition, iteration index, Algorithm 1.1 execution, correction equation, or floating-point model from which those estimates could be obtained. Therefore it cannot establish Theorem 4.1.
- **Paper implies lean:** `no`. For quantities arising from Algorithm 1.1, the paper's derivation supplies intended instances of hid, hres, hsolve, and hupdate and yields the same final formula. That establishes only paper-realizable instances. The Lean declaration asserts the implication for every assignment of thirteen real scalars, including assignments with no matrix, norm, precision, or algorithmic realization. The paper neither quantifies over that enlarged domain nor proves that every such assignment is realizable, so an intended instance is insufficient to entail the universal declaration.

## Findings

- **critical / incomparable-quantifier-domains:** The paper does not imply the declaration's universal scalar theorem, ruling out not-faithful-weaker.
- **critical / algorithmic-estimates-assumed:** The declaration proves an order-arithmetic aggregation lemma and does not imply the numerical-analysis result.
- **major / semantic-erasure:** The declaration's broader scalar applicability is a change of mathematical subject, not genuine strengthening of the paper theorem.
- **note / algebraic-formula-preserved:** The disagreement is not caused by a coefficient or inequality-direction transcription error.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `pass` |
| `S06` | `fail` | `fail` |
| `S07` | `fail` | `fail` |
| `S08` | `fail` | `fail` |
| `S09` | `fail` | `fail` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `fail` | `fail` |
| `S14` | `pass` | `pass` |
| `S15` | `fail` | `fail` |
| `S16` | `fail` | `pass` |

## Dependency coverage

- Blind translator covered `21` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `21` dependencies (`10` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/agent_outputs/adjudicator.json` (`9540bd24ff65eca1686973fba10b0d43d05706e540cf98b6652c48915f75e413`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/agent_outputs/blind_translation.json` (`7a709e23b4d0b6f0acf85e23575101b8c089346d402ad1f5fbde4d703a78ba1b`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/agent_outputs/direct_judge.json` (`b718c55bc841cc60d22c2ebc3c1a414317ab65531ebe388351fdab49ba8d9139`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/agent_outputs/paper_source_contract.json` (`cc0f2d27697c7df47ddee702a54285359037d701ffa45ec71a92ca67f9cf3902`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`f4367e675e64d5be771c53f61529f3c9fc7e0795d192d58520031757d8c5f680`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/agent_outputs/source_contract.json` (`6238c3e81bd12967d34f9ac792d05105850a9bb827e4afefb13a74d5fde55e36`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/decision.json` (`07a980e9fb4fb58477cd353d3beb542ea1633e5fc776d1510bc98150505f1a30`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/inputs/blind_dependency_inventory.json` (`2da72aa9ce5b39d1706de5df7e7a62e27855215427f3d9f7f40b68b42c869fc9`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/inputs/blind_dossier.md` (`09cd89ee345fe1154ed27672fe5f47d98e7c78d20adf508cff044d8eb9353717`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/inputs/blind_review_packet.md` (`09cd89ee345fe1154ed27672fe5f47d98e7c78d20adf508cff044d8eb9353717`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/inputs/declaration_dossier.md` (`a43d3c2fe615c196388643076bfeb43459ca5404bc43b691ec0451551ca8541a`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/inputs/dependency_inventory.json` (`2da72aa9ce5b39d1706de5df7e7a62e27855215427f3d9f7f40b68b42c869fc9`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/inputs/dependency_reuse_direct.json` (`8307a591e1b18f2ed5f23349b7779ed27235b8b1296facab38ecf7440bc5b3b5`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/inputs/direct_review_packet.md` (`ac4210aaaa538ef44ad2f115c9970f6be4e01a2bcd3963cbec70c50be01e5a62`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/inputs/paper_source_locator.json` (`d325b31e2cf1ecac253237196c87cfb8e169960305af1f36083a03802a8829df`)
- `paper_bencmark/highambench/tasks/P03/T2/faithfulness/inputs/source_locator.json` (`ebfbaab25c5c2277850ce5b8f18e0b77c6e84a171076b966702c91d34ec092ae`)
