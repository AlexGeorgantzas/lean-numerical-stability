# Faithfulness audit: P19-T3

- Classification: `not-faithful-weaker`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `793e14ac90b4c3015ce2f3b3b4e1990b88acff120a3b7418bf373c1e6a9d748e`
- Paper SHA-256: `67af427c72ae891b7863e386db542ef775b1e3eb306f812bb1a78bdbef86aaad`

## Decision

The formulas for the five-entry condition, rhoAR, relative forward error, the right three-source envelope, the flexible two-source envelope, and the omitted reapplication term are recognizable. The complete proposition nevertheless assumes fixed-dimension execution and analysis packages containing the central estimates that the paper derives. Its witnesses merely expose stored fields, and it asserts no package existence for ordinary paper-admissible GMRES executions. Therefore Lean does not imply the paper. Conversely, every inhabited Lean input already contains enough evidence to derive the target, and the remaining identity is algebraic, so the paper implies this weaker conditional proposition. The correct classification is not-faithful-weaker.

## Implications

- **Lean implies paper:** `no`. Lean asserts consequences only for already-inhabited right and flexible execution bundles whose stored analysis records contain the essential Appendix C/D estimates. It neither constructs such bundles from model (3.14) and condition (3.16) nor derives the well-conditioned-basis iteration supplied by Theorem 3.1. It therefore cannot recover the paper's general attainable-iteration results.
- **Paper implies lean:** `yes`. For every pair of values quantified by the complete Lean proposition, D043 already supplies the witness dimensions and D065/D067 already supply the decompositions, component bounds, and O(scale^2) remainders. The two D019 conclusions follow from norm triangle inequalities, and the final envelope equality follows algebraically from D020 and D023. The proposition requires no existence of these packages, so it is a weaker conditional statement implied independently of the paper's additional content.

## Findings

- **critical / assumed analysis and reduced applicability:** The target is a consequence-extraction theorem for already-certified packages and may be vacuous when no package exists; this makes it weaker, not genuinely stronger.
- **critical / attainable witness collapse:** The substantive attainable-iteration conclusion is absent, so Lean cannot imply the paper.
- **major / invented asymptotic semantics:** The numerical regime and logical relation differ from the source; because these properties are largely assumed in the bundles, they further restrict the theorem's domain.
- **major / extra package restrictions:** The proposition does not cover all executions addressed separately by Theorems 3.3 and 3.4.
- **major / polynomial-factor mismatch:** The formal polynomial class neither preserves the low-degree guarantee nor follows the source's intentionally unspecified representation.
- **minor / residual sign mismatch:** Lean does not literally match the displayed algorithm, although the paper may contain a sign error.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `unclear` | `fail` |
| `S09` | `pass` | `fail` |
| `S10` | `fail` | `fail` |
| `S11` | `unclear` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `unclear` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `164` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `164` dependencies (`0` hash-reused interpretations); failing or unclear: `D002, D008, D011, D015, D019, D025, D028, D030, D031, D036, D040, D043, D046, D049, D050, D052, D065, D067, D076, D086, D089, D106, D133, D153, D164`.

## Remaining uncertainties

- The PDF does not reveal whether Algorithm 1's residual A*x0-b is intentional or a typographical reversal of the conventional b-A*x0.
- The qualitative symbols lesssim and much-less-than and the phrase negligible second-order terms do not determine a unique exact remainder relation, threshold, or limiting regime.
- Because rhoAR and condition (3.16) are written using k before the theorem introduces its existential iteration, the paper does not completely formalize whether smallness is required at the eventual witness or over all candidate iterations.
- Generic kappa notation permits a 2-norm interpretation up to norm-equivalence and polynomial factors, but the source does not determine exact constants for that specialization.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/agent_outputs/adjudicator.json` (`1d071a1128983c6ecb5aa0535b1f7fa751e24ce15e2e6e2b165d6017909c682f`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/agent_outputs/blind_translation.json` (`d60e179319dc002bb75a5b551f196654883df492c0f325619672988828573729`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/agent_outputs/direct_judge.json` (`5818bd53fd25cb6c5ac09403dc782e2a104dc95ad314e80ca458c4e03db18a6b`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`c7f14a73d5040581aeb8e176248811131e6f64eb3283a4fd6d677244c8f8c603`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/agent_outputs/source_contract.json` (`a3b63cf761592a054eadebd83f967c657efa9cab85bf9ee56ffaea96dc828c76`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/decision.json` (`ab7bc9255a0bb9aa149f96c4a67167c02c104f11c7f9f62e8ed20e869fbf2afb`)
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
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/inputs/blind_dependency_inventory.json` (`c3a431f7e790874d5bb563525d220d538e52a8e0b8921ec76661edc3af21ff19`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/inputs/blind_dossier.md` (`d525b31f2874d3b228aec6bcad849e1a9201cababb5e35510a7c88ef7d20db6d`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/inputs/blind_review_packet.md` (`d525b31f2874d3b228aec6bcad849e1a9201cababb5e35510a7c88ef7d20db6d`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/inputs/declaration_dossier.md` (`c56f41c837b7be9911545d5837ba0e028c2d2a7a93952fdb8e40896749b7930a`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/inputs/dependency_inventory.json` (`27a17c2f471e14d52096beeebbca4f70f98aeac7113e35d939a10938662db193`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/inputs/direct_review_packet.md` (`c9000e7763181b2645f0239da5602a3ec3eed165ee297d1f094364cf77efc6cf`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/inputs/source_locator.json` (`86e602b27d591666b3938bffab9b2edc7328d40a89cf6835de08ad79b4a9bdb5`)
