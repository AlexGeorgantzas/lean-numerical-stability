# Faithfulness audit: P04-T2

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `deb0f26432dfea38fe73fc819a18b6a5d879b13481f4f21eedf99ee14d3942c7`
- Paper SHA-256: `7ad9ebb7eef9864c58e9a3760ee308be48060647286f8e16cdc740ed4be5b862`

## Decision

Primary evidence resolves the disagreement in favor of faithful-stronger, with a qualification to the round-trip judge's exceptional-value rationale. The final coefficient and all theorem-level dimensions, precision roles, higher-order terms, and componentwise semantics match exactly. Nevertheless, equality of the final gamma_n envelope is not equality of execution domains. The Lean constructors promote conservative aggregate bounds from the paper's proof into admissibility conditions for arbitrary real traces and omit the operation-level correlations and positional theta restrictions of Algorithm 3.1. The explicit q=1, b=n=3 positive-data construction satisfies those Lean conditions, has nonzero error, and cannot satisfy the source's position-indexed recurrence. Hence the extension is genuine and nonvacuous, Lean implies the paper theorem, and the converse implication fails.

## Implications

- **Lean implies paper:** `yes`. A source execution satisfying the no-underflow/no-overflow standard model supplies the Lean recurrence factors from its elementary rounding errors. Its position-dependent theta bounds imply the Lean aggregate bounds, and its operation paths supply the n-factor witnesses, padded by zero errors where necessary. Input conversions similarly supply inputErrorA and inputErrorB. Applying the Lean theorem then yields exactly equation (3.6).
- **Paper implies lean:** `no`. The paper proves the bound only for C_hat computed by Algorithm 3.1. It does not establish the conclusion for every independently witnessed real recurrence satisfying the coarser gamma_n path envelope. The q=1, b=n=3 construction gives a nonzero Lean run allowed by D026 but excluded by equation (3.2)'s positional theta constraints.

## Findings

- **minor / S10/S12 execution-domain strengthening:** The exact paper result remains a corollary, but the Lean theorem also covers nonrealizable aggregate traces, making it genuinely stronger rather than equivalent.
- **note / S04/S11 exceptional-value scope:** The strengthening concerns finite abstract traces. It must not be interpreted as a verified extension of Theorem 3.2 to NaNs, infinities, underflow, overflow, or concrete IEEE behavior.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `pass` | `pass` |
| `S04` | `pass` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `pass` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `fail` |
| `S11` | `pass` | `fail` |
| `S12` | `pass` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `pass` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `105` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `105` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

- The paper describes validity for all evaluation orders without formally defining the complete implementation-level set of such orders. This does not affect the classification because the explicit left-to-right theta indexing already supplies a strict counterexample to execution-domain equivalence.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/agent_outputs/adjudicator.json` (`14ece18f9532ac8eb7eedef0603db0bc2c6e172f30dd6cf08595bdd079031182`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/agent_outputs/blind_translation.json` (`8dac33c2d57194ce9afbcc5a1170d2bef51ed81dc60ec35fc6eb51626e7fafe4`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/agent_outputs/direct_judge.json` (`5e2e9f1960c8e7a8621b86b589374d9008389a7e3e806cabb73521c7288675b6`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`6541563064d5a1c0770a89ffe98afcc0a0353b15aa465b7fec51fb8051e23e74`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/agent_outputs/source_contract.json` (`72afc8bc774b6e24478e7611931b79d72cd8678c161ea20c996ab89e10e1f433`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/decision.json` (`0addb04091c6bfdf3a50225582207a6a5f429e378d6375d56fcc64831a811554`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/agent_outputs/blind_translation.json` (`4d71a7009e4cb29d27a134339ecf7b18c5220d2507c972f2cd793f26b9d8fbf8`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/agent_outputs/direct_judge.json` (`c8550401e7f9caa5c9bbf71dad5391d07dcd6eba65821665baffbe8e0209771b`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/agent_outputs/paper_source_contract.json` (`f23d1d2864ab683fc44d7b4dd917ebb13c36417400d3ee09d7d5a642c3a0d785`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/agent_outputs/roundtrip_judge.json` (`01403dc737c6f8c804399734fccc14badb310c8df096ee83e4f7f0708e9e25d3`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/agent_outputs/source_contract.json` (`f91ab8283eea97a3263327b17be4b438564672ac842266b86621054c130df589`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/decision.json` (`bf585cec6a7195053b93f6fd066a68369c59615714a743e5921b141fbaef45fc`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/inputs/blind_dependency_inventory.json` (`62f92733f1d6bd164114aabb88151cf1bfff522262475a1a60228bd73020c5b0`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/inputs/blind_dossier.md` (`96abb59a7a2442174b606f193289f5d5c707fc22ba390a60dd00ae71a96c4955`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/inputs/blind_review_packet.md` (`96abb59a7a2442174b606f193289f5d5c707fc22ba390a60dd00ae71a96c4955`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/inputs/declaration_dossier.md` (`f5c48f188222a2480238b2c40d27f75ef228c4b2d7c6217d68ebe1fc49508119`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/inputs/dependency_inventory.json` (`edb46564cba8406b42c6d333c68e9518d67704cf7da44fe676ccf5f6f989e7af`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/inputs/dependency_reuse_direct.json` (`f69ef14afab568cfc4bcce54833be6807beba992d2a39b6f51af29e604fa6a7c`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/inputs/direct_review_packet.md` (`89ea80907b3d9155fd60c79a2d5db9e0ae3b17f16e1514dd17f5ff2cf20b716e`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/inputs/paper_source_locator.json` (`609fbccbf417b9661d911f32e2ac6e1c09c3fa4c980c82c53b5c0edd480437f7`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/inputs/source_locator.json` (`8bf362e8f7f6f69a831e5593e1218ef3d7a2b716196afed0f070400ab36bf4b1`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260821T140951Z/agent_outputs/adjudicator.json` (`1dc2e89e4ddaee0e5945b74d29f9661def3def3529fbb1102c0d24b62ed08af9`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260821T140951Z/agent_outputs/blind_translation.json` (`0864f3b2a58a95e353041fbad8db5e8cb9111fb725da2fb9d4e46df9c5667936`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260821T140951Z/agent_outputs/direct_judge.json` (`436e83475d4746df8fdf7708ce78ff4cdeb4463070023f82e0c7b233d499b178`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260821T140951Z/agent_outputs/roundtrip_judge.json` (`1677c6d4ee5a461d9acb092277b1ab8048699b3365e0fc74ced8b36d0a58629f`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260821T140951Z/agent_outputs/source_contract.json` (`152fbe2a3c2c5cc867f5835cd15808f82524547ee43b09d2c89fc6f1419dace5`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260821T140951Z/decision.json` (`54d4735b9279e0e0be987304f5479bfe8da04f4d8cb0fff88a5f3ade74eed3f7`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260821T140951Z/inputs/blind_dependency_inventory.json` (`d6a132052a35dfd240d1b71075b8fb6810e281bc9a9f75d4fb16d27a88a35c51`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260821T140951Z/inputs/blind_dossier.md` (`213f7205321b63196e02a0778bbc31c8fc5576cbb4ed850163345bc3fed85df3`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260821T140951Z/inputs/blind_review_packet.md` (`213f7205321b63196e02a0778bbc31c8fc5576cbb4ed850163345bc3fed85df3`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260821T140951Z/inputs/declaration_dossier.md` (`3527b5c8664f6a6ad1c778d4195f384b081639e9c6053dd2e45607524f06472e`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260821T140951Z/inputs/dependency_inventory.json` (`5b00364951e70e2edc52f1f143cc15eedc6dcb8dbc2c5e7aa1ef62e2c89cca68`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260821T140951Z/inputs/direct_review_packet.md` (`3b0a564479bea029c245241173fc00c4777d2dce721cc9a7bba453f72a52932d`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260821T140951Z/inputs/source_locator.json` (`e714f534dcc931ee4d94fdf815cba6d3e12fea743ec32896003bfe143cd8d351`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260822T090159Z/agent_outputs/blind_translation.json` (`683ec9ad4674924464828bc08e1e76cc657fe7d6df3a10cbd14d085f729f7390`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260822T090159Z/agent_outputs/direct_judge.json` (`142c4dc00b09d81402c3b28c9dcbf5e4fba4262db6cf2333295ef45ad90378f5`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260822T090159Z/agent_outputs/roundtrip_judge.json` (`6b3feecdee8420d1f787f4af319103d85adec14769269996f9cecfc5c27fb1e0`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260822T090159Z/agent_outputs/source_contract.json` (`f5fc03471e96e2ee5d5bbed2747eb72cbd82cf771f21f7dcf99117510b28dd88`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260822T090159Z/decision.json` (`0aa0ecefd34adb9b1ca878511d9f67b1b466fddf636042ed63d5d32bebbde72b`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260822T090159Z/inputs/blind_dependency_inventory.json` (`ac15414f91e5844d2557ed0befb695782629182dd968cf4e50b4904c33fb9d75`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260822T090159Z/inputs/blind_dossier.md` (`a37473ecf2fdbcefce480cc5aa959ea3fd424b4e365aff74c718485c394e729a`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260822T090159Z/inputs/blind_review_packet.md` (`a37473ecf2fdbcefce480cc5aa959ea3fd424b4e365aff74c718485c394e729a`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260822T090159Z/inputs/declaration_dossier.md` (`4dbe401e4f26d298bad5ae5561fbff2126f91f8269bd53f428a1d18dacc5eef2`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260822T090159Z/inputs/dependency_inventory.json` (`02892736c3478bc2966dd3c31637046adb60e876792b4da5c2d559e386ed0170`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260822T090159Z/inputs/direct_review_packet.md` (`2fd7f08390c54327d9f79b20a3131932b3ce09cfde3b37c301be54c2da320ce1`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260822T090159Z/inputs/source_locator.json` (`e714f534dcc931ee4d94fdf815cba6d3e12fea743ec32896003bfe143cd8d351`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/inputs/blind_dependency_inventory.json` (`e588dbb83b5c66bfb556e07e67929233985c6f266a9fee2ec2238945ae2ac434`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/inputs/blind_dossier.md` (`188c5208249e058a9eeac8c46dc6d84f6152b1ef7f3843cc816f35cc5038a94c`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/inputs/blind_review_packet.md` (`188c5208249e058a9eeac8c46dc6d84f6152b1ef7f3843cc816f35cc5038a94c`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/inputs/declaration_dossier.md` (`04cffba405f88a17766971c0a5bc5aaaa190b729dae5803053ae316e42d281b1`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/inputs/dependency_inventory.json` (`97760f26abf7b433c29ff06fc0aa6e67927c28d1d7e0bd3bd6f570c9c4ceea1b`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/inputs/direct_review_packet.md` (`455324a8189643c0cef8b720906af4ec17c03a0054bca4d23ab6859365af8070`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/inputs/source_locator.json` (`e714f534dcc931ee4d94fdf815cba6d3e12fea743ec32896003bfe143cd8d351`)
