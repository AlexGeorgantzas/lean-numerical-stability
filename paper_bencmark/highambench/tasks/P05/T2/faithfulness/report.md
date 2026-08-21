# Faithfulness audit: P05-T2

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `429892a33ec0d2a62b6d40e3e4ca373ffe338533fe8d951823a298b483395182`
- Paper SHA-256: `dd8b525c0eabc509a68b325ee5008cf6f1d4ef262bef8ba54e1947fe3cdb3db6`

## Decision

The direct judgment correctly noticed that the trace is not structurally indexed by the actual sum tree and that the format record has extra models, but it incorrectly treated both facts as reduced applicability. Equation (2.4) is an explicit prior source result used inside the proof of Theorem 3.1, and every paper-valid tree can furnish the required trace. The trace assumes only those sibling bounds, not Lemma 4.1 or (4.3). Likewise, the paper explicitly licenses Doolittle as a sufficient mathematically equivalent formulation. Consequently the Lean theorem covers the paper result. Its abstract format additionally supports inhabited, certificate-bearing sparse models with substantive nonzero residuals that are not instances of the paper's full F. That extra universal domain prevents the converse implication and yields the accepted classification faithful-stronger.

## Implications

- **Lean implies paper:** `yes`. A paper-standard round-to-nearest format instantiates D019; every completed exception-free Doolittle evaluation supplies D032's tree data, and equation (2.4) constructs its protected trace. The PDF explicitly licenses Doolittle as a mathematically equivalent representative, so the Lean local and global conclusions specialize to Theorem 4.2 and equations (4.2)-(4.3).
- **Paper implies lean:** `no`. The paper quantifies over its standard finite floating-point set F, whereas D019 admits additional inhabited sparse representable sets and abstract safe ranges. The certificate-bearing 2-by-2 example has nonzero error and rounding behavior unavailable in the corresponding full paper format, so the extra formal domain is genuine.

## Findings

- **note / source-licensed-intermediate-certificate:** The trace does not preload (4.3) and does not narrow applicability to paper-valid executions.
- **note / algorithm-representation:** DoolittleRun is a licensed representation of the selected result rather than an unsupported algorithm specialization.
- **minor / broader-format-domain:** The formal declaration proves a nonvacuous extension beyond the paper's stated standard-format domain, making it faithful-stronger rather than equivalent.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `pass` | `pass` |
| `S04` | `fail` | `pass` |
| `S05` | `pass` | `pass` |
| `S06` | `fail` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `fail` | `pass` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `fail` | `pass` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `fail` | `pass` |
| `S16` | `fail` | `pass` |

## Dependency coverage

- Blind translator covered `142` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `142` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D013, D014, D019, D025, D032, D034, D035, D041`.

## Remaining uncertainties

- The selected paper passage does not enumerate all Gaussian-elimination variants or specify pivoting. The equivalence determination is therefore limited to the unpermuted mathematically equivalent formulations expressly invoked on printed page 694; it does not extend the target to arbitrary pivoted algorithms.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/agent_outputs/adjudicator.json` (`f9ffc8553f75f1198f736ff577cb389ec5ef92ffb00e6afc4d46407fc9e69ae3`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/agent_outputs/blind_translation.json` (`27fb3e53974ab7ec2fbc664d8455dd91ba8474f1f953a685ff293961d4036cc8`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/agent_outputs/direct_judge.json` (`5bb6c9d47d93ce7992d3bcc72ca87f7549fcadb428e04b4b6b5ca40c93d250f5`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`91b5d69ca365990966bc24c524a2466c399e5508b2d0aeaca3e5143525905533`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/agent_outputs/source_contract.json` (`b90661268c3aed1c83d760fa961d5959dda9781ecd69463565ffac2371bc931e`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/decision.json` (`e798fa9d7288559f982536425773c92e583b2d5fb70169427c00f6b486da5cb7`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/agent_outputs/blind_translation.json` (`36fa2ad1734a9feea8493c522b1daa289e652077460a92100b12fff0c6a26383`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/agent_outputs/direct_judge.json` (`8e2dfc0a93151547e3c42f974b4b6af6553d13ed26d2c4b6390435d95045e939`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/agent_outputs/paper_source_contract.json` (`90bcb3f32112e46567a1fde6c0c742ef1d157d1829c1eb2b2cb5ebb4d58d4c1d`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/agent_outputs/roundtrip_judge.json` (`4e81ded2b048c61b2114e49b98832b3b851402ee75492b3158027f8052dc8531`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/agent_outputs/source_contract.json` (`e2e2fd479d2d1c03cabe0f8baef74c7bd8c9da70a251d4a3093a17877090f718`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/decision.json` (`7997e5e5958e59ea1afd99867c7becc8264f1c83af8cfb21141d0516c2dc6ba5`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/inputs/blind_dependency_inventory.json` (`c56549ba28c0a6dc92dc0edf5d686405ed884820822811e6a5adfd3ec01f7937`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/inputs/blind_dossier.md` (`2000282daaa2678d82e662c5f674a4e653a2b8587cd8bae85039f503d083f00e`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/inputs/blind_review_packet.md` (`2000282daaa2678d82e662c5f674a4e653a2b8587cd8bae85039f503d083f00e`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/inputs/declaration_dossier.md` (`f0232a3af8da7802bb6b66afc07fd0779ee87c762c41571c1d999615ea10af8b`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/inputs/dependency_inventory.json` (`c13980e3175f6606ab215fcb97d5a9d5a0bdce8dc5b5a3f268349f4403ceb810`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/inputs/dependency_reuse_direct.json` (`1b65ef5194934195e90c3d73c982f7127d2a4ac67aa9bbbd5f84c5d5123afb9d`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/inputs/direct_review_packet.md` (`f6d7622f8a53de126a8ab2a435148c8f81cd2a30c3989d70ac37b0069d129121`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/inputs/paper_source_locator.json` (`417f8e6a6ff934c35d3c2379d9faefe1c21d44b1f14a69f7674c0ef303123327`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/inputs/source_locator.json` (`9fb63ab1035cdbe5b25034bf13d2341b0813504a3fb962b5ac3a1801f93c4fd3`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260821T152838Z/agent_outputs/adjudicator.json` (`4f65f5233d767feed87278a5de82706ea0a7c9235150f0f1f1ea0a3fe7a99d2e`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260821T152838Z/agent_outputs/blind_translation.json` (`61ef2692b2f2d08e242053b56cab9409355c1257620a14b7628b52f2de03bfe3`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260821T152838Z/agent_outputs/direct_judge.json` (`6bab140ca101e1898b6d55a6826d23789c31ed873c1ffe9a25a21f7c7776f653`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260821T152838Z/agent_outputs/roundtrip_judge.json` (`94d8d0609a4adaddee8d75b004da6abaaa4be95764e221645bed0febc7af5c12`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260821T152838Z/agent_outputs/source_contract.json` (`0d2c8bf046d1dc30558903c298899e2e50885e73d5ec83ae585beb8d866cfa12`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260821T152838Z/decision.json` (`aabf832c0a45d784a5f98c6ce32010a84221374f56449ed285b3c0e6c5bf1ff4`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260821T152838Z/inputs/blind_dependency_inventory.json` (`6ea3b72da834eb0ccd1ddf3206f8ef037c87fbf8d33681afe6a3e574a5f23ce3`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260821T152838Z/inputs/blind_dossier.md` (`1f736ce5e0ea214f9f06802949e3b1820d5b713f544cadc83bfd7b12690fc3bf`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260821T152838Z/inputs/blind_review_packet.md` (`1f736ce5e0ea214f9f06802949e3b1820d5b713f544cadc83bfd7b12690fc3bf`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260821T152838Z/inputs/declaration_dossier.md` (`6b14d0f97ee4c68d675fcb5cf33b9a5866cd7827df015f9c2b13110bcc5c2a10`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260821T152838Z/inputs/dependency_inventory.json` (`cd658e6379f43db6070f2be533c925334ed64d1efeae1cec678b9fe84606ccd4`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260821T152838Z/inputs/direct_review_packet.md` (`969325ea2447cafdd902d1197a52d7eb950e038a62f07ed37a8a69b998427d5f`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260821T152838Z/inputs/source_locator.json` (`40669d19b199673463bcdaf61468d8a1461f341bcdc7c10e62c3da90f0d46c08`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/inputs/blind_dependency_inventory.json` (`91c9d84116dca3591b1513b11a24a97fd3435d28cc111fe0713d1ab3ef924e19`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/inputs/blind_dossier.md` (`3b1aade16bf66e3f8bba80589dec5722e05d09ad5e365e18b7e44f16bf5fc3d8`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/inputs/blind_review_packet.md` (`3b1aade16bf66e3f8bba80589dec5722e05d09ad5e365e18b7e44f16bf5fc3d8`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/inputs/declaration_dossier.md` (`a18c79910cc1c850b1644cacd16152caf06496f4b86b3dcc17627a632331b8ca`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/inputs/dependency_inventory.json` (`9d28d46bb19fd32d924efebc6b51a8b8224b470cc9490499bf451aee9ba5e24d`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/inputs/direct_review_packet.md` (`4134bae0352733dab5cc89bbc3828cb5a9f3a47598a5139f2c062d183287189a`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/inputs/source_locator.json` (`40669d19b199673463bcdaf61468d8a1461f341bcdc7c10e62c3da90f0d46c08`)
