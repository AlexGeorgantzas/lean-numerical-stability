# Faithfulness audit: P19-T3

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `951ad8781d52c26a79b0619673bc81478be3e31afa80728ae045070b69bf2867`
- Paper SHA-256: `67af427c72ae891b7863e386db542ef775b1e3eb306f812bb1a78bdbef86aaad`

## Decision

The declaration preserves the visible three-term and two-term envelopes, all five entries of (3.16), fixed M_R with M_L=I, the exact rho_A^R numerator, relative 2-norm forward error, and independent right and flexible witnesses. Those formula-level successes do not overcome the statement-level changes. The Appendix C/D results are premises rather than derived dependencies, c(n,k) is replaced by an arbitrary real, the two uses of u_g are disconnected, first-order semantics are unrestricted, and the reciprocal well-conditioning test admits sigmaMin=0. The unresolved scope of (3.16) and unqualified kappa are genuine source ambiguities but do not affect the fixed classification. The exact envelope identity is only a true algebraic supplement, not evidence that the conditional Lean result is stronger than the paper theorem.

## Implications

- **Lean implies paper:** `no`. The Lean declaration does not establish Appendix C/D packages or uniform applicability for computations satisfying the paper's stated hypotheses. Its conclusion can also be weakened by arbitrary dimensionFactor and secondOrder semantics, and its selected k may pass well-conditioning through sigmaMin=0. Therefore it does not yield Theorems 3.3 and 3.4 for the intended executions.
- **Paper implies lean:** `no`. The PDF does not entail a proposition universally parameterized by unrestricted small and secondOrder predicates, disconnected u_g fields, arbitrary per-iteration dimension factors, totalized reciprocal semantics, and supplied appendix structures. The exact envelope identity is algebraically true but does not bridge those differences.

## Findings

- **critical / proof-derived results assumed:** The main existential bounds are conditional on much of their mathematical substance and may hold vacuously when those structures are unavailable.
- **major / uncontrolled constants and semantics:** The low-degree c(n,k) restriction is lost, and the approximate inequality can range from exact to trivial while applicability can become uninhabited.
- **major / precision disconnection:** Selection and the attainable-error conclusion can refer to different values despite the paper using one u_g.
- **major / totalized reciprocal:** A rank-deficient computed basis can satisfy the encoded well-conditioning condition.
- **minor / Remark 4 exactness:** The identity is algebraically valid but must not be interpreted as exact equality of attainable errors or complete theorem bounds.
- **note / condition scope ambiguity:** The target's uniform applicability scope is conservative but cannot be declared either equivalent or contradictory from the PDF alone.
- **note / condition-number interpretation:** This remains an explicit interpretive uncertainty and is not needed for the rejection.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `unclear` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `fail` | `fail` |
| `S07` | `pass` | `pass` |
| `S08` | `fail` | `fail` |
| `S09` | `unclear` | `unclear` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `fail` | `fail` |
| `S15` | `pass` | `pass` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `222` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `222` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D003, D004, D008, D011, D012, D018, D019, D025, D032, D034, D035, D038, D039, D041, D044, D045, D046, D053, D054, D057, D058, D061, D062, D075, D076, D077, D079, D084, D086, D087, D090, D117, D118, D119, D130`.

## Remaining uncertainties

- The PDF does not settle whether condition (3.16) is required only at the selected MGS witness, existentially together with that witness, or uniformly over all admissible candidates.
- The PDF does not select one exact condition-number norm for every displayed kappa; the target's uniform two-choice interpretation is plausible but not source-determined.
- The PDF supplies no quantitative threshold, comparison constant, or remainder semantics for its qualitative much-less-than and first-order symbols.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/agent_outputs/adjudicator.json` (`ff00aff8e8faeea875cc476736426c26c7c770ed57ed281061f8f2e2a8ebdce2`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/agent_outputs/blind_translation.json` (`c009d1b012c9216cec4f145407026468168bb047c1225b372f44625ef349ed17`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/agent_outputs/direct_judge.json` (`eece72b9eee6dd1425e9dfde9bc99c6d169bf5230fffec42862308956d41b101`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`0e546165ef31b263c6369dab6b96df2f1f5487a57423b3aad9b9b9ddf93019f7`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/agent_outputs/source_contract.json` (`a43d9f399ec4ba54452bfdeb5ee55c27b023ae8a92a374fa4edd4a8293de71be`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/decision.json` (`192c28872fadc73c8673516ba10bf509d18c84ca68d7be60124d50eba45e3fb2`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260821T040927Z/agent_outputs/adjudicator.json` (`d9f37b0d1114d356317a32913d7e97f57d1bbd7b628295b20042ab6314bce836`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260821T040927Z/agent_outputs/blind_translation.json` (`c4e2a0efe45f5d2d9dc61e0849a741c76dbf2482ab77ccdf3af3c9cc2f432f20`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260821T040927Z/agent_outputs/direct_judge.json` (`9bf5ff61131ec949d3c0999fa070be292e3ad530f63bd7baa0563d70ab385993`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260821T040927Z/agent_outputs/paper_source_contract.json` (`282bdf4dba3e70c740465a2c4663b96debd1a66ef82c3debf273ad41cdbf76e0`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260821T040927Z/agent_outputs/roundtrip_judge.json` (`920bf500fc1a78ba18a5b61d94ca78940ed698706032649d63bedd1eb62a2c55`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260821T040927Z/agent_outputs/source_contract.json` (`d9b9b728d225b77628508b1574bf70a411d50227b8120711d3b1921cd6596330`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260821T040927Z/decision.json` (`c5d12aac529f8247a8899a3ceef9730c4b8e1d96490770c9e649b5cec5a42cfd`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260821T040927Z/inputs/blind_dependency_inventory.json` (`cf0938f317757deff1412d59d70fd1bd3995ab59459c83182690a781a969eb8c`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260821T040927Z/inputs/blind_dossier.md` (`b0d8714567f59fb874f4b2f9bf543b6466b3795d176c7c31897c2b0f22aa5800`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260821T040927Z/inputs/blind_review_packet.md` (`b0d8714567f59fb874f4b2f9bf543b6466b3795d176c7c31897c2b0f22aa5800`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260821T040927Z/inputs/declaration_dossier.md` (`03ab3c80a4baf92982c261f9384a5c3ac84e79307614209f0bf05a9f7d463f89`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260821T040927Z/inputs/dependency_inventory.json` (`d5985e67c4c363c499dd39dde7b0dda9eda6996147c22d7c43473c8e5c1291dd`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260821T040927Z/inputs/dependency_reuse_direct.json` (`18d04c541cef26b01d303550c587f2ffb9a973ae6035cb1fd28047ce7c4c0510`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260821T040927Z/inputs/direct_review_packet.md` (`5dd422ef13089cd2fe52aa06ad2faa961e844c7eae45cc6d1fba7f46b293ecaa`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260821T040927Z/inputs/paper_source_locator.json` (`b2b71745c3ba0bc98613f67b2d754faf971558a1974b0f22e4456d4b88500ba1`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260821T040927Z/inputs/source_locator.json` (`3e3d8c11da1f2b05a3531b569c750e51a42f25f0a791458ece345cbbe7927cb9`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260822T011918Z/agent_outputs/adjudicator.json` (`1d071a1128983c6ecb5aa0535b1f7fa751e24ce15e2e6e2b165d6017909c682f`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260822T011918Z/agent_outputs/blind_translation.json` (`d60e179319dc002bb75a5b551f196654883df492c0f325619672988828573729`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260822T011918Z/agent_outputs/direct_judge.json` (`5818bd53fd25cb6c5ac09403dc782e2a104dc95ad314e80ca458c4e03db18a6b`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260822T011918Z/agent_outputs/roundtrip_judge.json` (`c7f14a73d5040581aeb8e176248811131e6f64eb3283a4fd6d677244c8f8c603`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260822T011918Z/agent_outputs/source_contract.json` (`a3b63cf761592a054eadebd83f967c657efa9cab85bf9ee56ffaea96dc828c76`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260822T011918Z/decision.json` (`ab7bc9255a0bb9aa149f96c4a67167c02c104f11c7f9f62e8ed20e869fbf2afb`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260822T011918Z/inputs/blind_dependency_inventory.json` (`c3a431f7e790874d5bb563525d220d538e52a8e0b8921ec76661edc3af21ff19`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260822T011918Z/inputs/blind_dossier.md` (`d525b31f2874d3b228aec6bcad849e1a9201cababb5e35510a7c88ef7d20db6d`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260822T011918Z/inputs/blind_review_packet.md` (`d525b31f2874d3b228aec6bcad849e1a9201cababb5e35510a7c88ef7d20db6d`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260822T011918Z/inputs/declaration_dossier.md` (`c56f41c837b7be9911545d5837ba0e028c2d2a7a93952fdb8e40896749b7930a`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260822T011918Z/inputs/dependency_inventory.json` (`27a17c2f471e14d52096beeebbca4f70f98aeac7113e35d939a10938662db193`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260822T011918Z/inputs/direct_review_packet.md` (`c9000e7763181b2645f0239da5602a3ec3eed165ee297d1f094364cf77efc6cf`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/history/20260822T011918Z/inputs/source_locator.json` (`86e602b27d591666b3938bffab9b2edc7328d40a89cf6835de08ad79b4a9bdb5`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/inputs/blind_dependency_inventory.json` (`d0736fa2c535180cef9897cda8127ac58dbc7424be2c102ea57d05ef5b5a123b`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/inputs/blind_dossier.md` (`ad2bacc514dc3c1df3263e6b4038afcf0611fa9a4b43e7a8cc9416ccc0dfef70`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/inputs/blind_review_packet.md` (`ad2bacc514dc3c1df3263e6b4038afcf0611fa9a4b43e7a8cc9416ccc0dfef70`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/inputs/declaration_dossier.md` (`3be68b458674557d3f05b9aad005204f8544639dc0bf1c2af6ff2e2f2187f1e4`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/inputs/dependency_inventory.json` (`f002ce8746341bbb5a91e516afcbd630022e6a66b123fb9f8f24a918af0e2838`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/inputs/direct_review_packet.md` (`46219bb06ef8dec39da822f0f7a537621a570da4f65658a9fbc1a1e08a94646e`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/inputs/source_locator.json` (`86e602b27d591666b3938bffab9b2edc7328d40a89cf6835de08ad79b4a9bdb5`)
