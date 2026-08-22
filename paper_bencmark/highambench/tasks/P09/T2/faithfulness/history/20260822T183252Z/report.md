# Faithfulness audit: P09-T2

- Classification: `not-faithful-weaker`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `6bfa09c58a6330e01b1b9d20bec0aa34397c6124deba04bcc0ab0c740a4017b0`
- Paper SHA-256: `9076fe377cc64878a4a10f8a47ff49245bc5acaf116ffbd8e2ccca57033da758`

## Decision

Standard mathematical `O(epsilon^2)` semantics justifies a fixed epsilon-indexed family, a coefficient and radius chosen before epsilon, and an epsilon-indexed perturbation obtained by choice or Fourier inversion. The local declaration also conclusively supplies the positive Fourier sign. The source-selected result is only the backward identity and two bounds, and the operational, numerical-interface, norm, constant, and error-notion details otherwise match. The decisive proposition-level defect is that Lean assumes `P09TheoremOneRmsAsymptotic` rather than proving its existence from the modeled FFT, while the paper proves Theorem 1(a) and then derives the corollary. Thus paper implies Lean, Lean does not imply paper, the classification is not-faithful-weaker, and accepted is false.

## Implications

- **Lean implies paper:** `no`. Lean proves the backward conclusions only after an entire execution family and a `P09TheoremOneRmsAsymptotic` proof are supplied. No target dependency establishes that certificate for every source-admissible FFT family. This added antecedent reduces applicability; family-dependent remainder witnesses also do not recover the paper's bounded-theta worst-case uniformity.
- **Paper implies lean:** `yes`. Under standard local big-O semantics, the paper's proved Theorem 1(a) supplies a coefficient and radius for corresponding asymptotic executions. Positive-sign Fourier invertibility and RMS scaling produce the epsilon-indexed fictional perturbation, and the finite-dimensional max-versus-RMS inequality yields the second bound. The paper's result therefore instantiates the target's weaker supplied certificate.

## Findings

- **critical / improper conditionalization:** The target establishes only an algebraic conversion of an assumed forward estimate and excludes source-admissible executions for which no separate certificate is supplied.
- **major / remainder uniformity:** Even apart from certificate existence, the target does not preserve the natural path-uniform strength of the source derivation.
- **note / source selection:** The target does not omit a selected conclusion by leaving out that informal heuristic.
- **note / core fidelity:** There is no independent sign, normalization, norm, factor, inequality-direction, error-notion, or global-vacuity defect.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `fail` | `unclear` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `pass` |
| `S06` | `pass` | `unclear` |
| `S07` | `pass` | `pass` |
| `S08` | `fail` | `pass` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `fail` | `fail` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `pass` |
| `S14` | `unclear` | `fail` |
| `S15` | `unclear` | `pass` |
| `S16` | `fail` | `pass` |

## Dependency coverage

- Blind translator covered `203` dependencies (`0` hash-reused meanings); unclear: `D026, D040, D041`.
- Direct judge covered `203` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D004, D005, D006, D007, D013, D020, D026, D040, D041, D046, D051`.

## Remaining uncertainties

- The PDF never states the complete dependency set or quantifier order for the hidden `O(epsilon^2)` coefficient and radius. Its finite bounded-theta proof supports independence from epsilon and uniformity over theta realizations for fixed structural data, but intended uniformity across all inputs, algorithm variants, or implementations is not explicitly specified.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/agent_outputs/adjudicator.json` (`32d231526124ff7216b8ced4a4a26e993c38898a007eeb01bb4d3d8be0ccd984`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/agent_outputs/blind_translation.json` (`a30dce2ebd4d1302e853803a3c7521d60436006ec060dbdb90d91ca2128af8e8`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/agent_outputs/direct_judge.json` (`b1b9103364f63cf3c66eb246aa93ab9c6c9d55260c44e19bb40a832890836102`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`571a985f3040da45d5311799fe56cd67f51edea078dd5de81c92e675a7a969dc`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/agent_outputs/source_contract.json` (`f5ae5a89c6846df0dcafaacd3635022fc7111591b14d5f6cc70fcd42c412e35e`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/decision.json` (`a604cd8884284212475c66f3b1d0ea99fed2091c5e95db97ab12226b16bc3c25`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260814T235038Z/agent_outputs/blind_translation.json` (`9a01b41ec8fa4ec0e535babdd26a23ee9a254c5f2dddfb4022347fd85e10b48f`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260814T235038Z/agent_outputs/direct_judge.json` (`96e78149d5f1527bcd14ba3d9f5b7302e081e4abddcf5c375b589344af1c2fa8`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260814T235038Z/agent_outputs/paper_source_contract.json` (`348db3c4cffe4770d8510e9fec47ccdab62bf40c19935e431854786ba7f44db4`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260814T235038Z/agent_outputs/roundtrip_judge.json` (`9190ac3f562ba1bc4dec035015ef2d9fc9e99c35b8b4c8a660907fb300386c68`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260814T235038Z/agent_outputs/source_contract.json` (`9c13c3b7713e9414917faa07e430b9762c89eac6389542ad64fb6e6cde3b71cf`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260814T235038Z/decision.json` (`dcbf463d44cb8cd08a983a971074340b78b8ec27ac824248040c367018bf8860`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260814T235038Z/inputs/blind_dependency_inventory.json` (`fc3d3b7c6cc18275d3502b928f52a741e0d7b858f2df29fa7b73355926baff9f`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260814T235038Z/inputs/blind_dossier.md` (`7362b410440afdb0f170536e029a4b7f4950420491d462b75eece22df2864539`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260814T235038Z/inputs/blind_review_packet.md` (`7362b410440afdb0f170536e029a4b7f4950420491d462b75eece22df2864539`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260814T235038Z/inputs/declaration_dossier.md` (`4989f464acf809a1a315eef2165312f2f768aa23e432dce8df6721c74c3b1231`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260814T235038Z/inputs/dependency_inventory.json` (`7007e3f10524bf3ca95fd2979e8ac87518a05d64722301654960172e0e7894cb`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260814T235038Z/inputs/dependency_reuse_direct.json` (`057fba236f94854071eebfb32df89c84b8b2e73381c348e7cce2c5072f9b010a`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260814T235038Z/inputs/direct_review_packet.md` (`bc0ee1b457543e8af14569c5fe21f98ced94c30a2af87e2414147e9646211e59`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260814T235038Z/inputs/paper_source_locator.json` (`f236078d56116000664fec27c570812daeb11eb5024aaf78838800ecc07f8a13`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260814T235038Z/inputs/source_locator.json` (`fe2bf8a9e74bbce7778ab97cec39a1da3ac1e48456b0cc88c60f8fb8978f3a3b`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260821T180838Z/agent_outputs/adjudicator.json` (`091bf73a774d2e3d643ca282f2c032bac2c208d627a73141548aae4cbac189dc`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260821T180838Z/agent_outputs/blind_translation.json` (`1c753d37afb428894eaad95599c7cec61826074b14aa7c9274233a5507a47e59`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260821T180838Z/agent_outputs/direct_judge.json` (`882916ced92d3ab4fe6c25cdd342d9261c936a9f74a66d40211420e08edf69e1`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260821T180838Z/agent_outputs/roundtrip_judge.json` (`eefd237d2778ac2f6cc6c53c7fedc460e58475fe9fd49a5c09501d492479a6fc`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260821T180838Z/agent_outputs/source_contract.json` (`e8ffe5fc61a1df580946a6085eae8513cb61e84787422d4500a5edbc719ba582`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260821T180838Z/decision.json` (`dcae794023f75446c4904ea82e99b1e2451f2f39b3bb9eb0f581e53e4df50d41`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260821T180838Z/inputs/blind_dependency_inventory.json` (`9083072565d9b948ab2309aaead1e1f81c3b785b151639c842d01a97d2904e14`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260821T180838Z/inputs/blind_dossier.md` (`0407fa65f3f935d0fa18ef6e7d381ef96bc34118b153c51cc3f7973a3f7c0110`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260821T180838Z/inputs/blind_review_packet.md` (`0407fa65f3f935d0fa18ef6e7d381ef96bc34118b153c51cc3f7973a3f7c0110`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260821T180838Z/inputs/declaration_dossier.md` (`1c28ca488b355c604c72957bd3c044e592f99a3938569f1b0912b32b17352945`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260821T180838Z/inputs/dependency_inventory.json` (`2d70beae42489d91a39dfee6c09ee5bcb678d5b476c088f27bad2e83dbe818a6`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260821T180838Z/inputs/direct_review_packet.md` (`ac6d20d9406c4d00d9d7f5ab1da79719debe8edff54949e38ad834a30e68040f`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260821T180838Z/inputs/source_locator.json` (`4b1b954e2df0431e5626df4ee70a912ba59a36064b3ad45d272bc96b4f10cb3c`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/blind_dependency_inventory.json` (`7fd63cb3d76ca64de3012f97ede701e0e99797b84dc26793b1d9926fab183ffe`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/blind_dossier.md` (`0c975951024c16273cbff4fcfb118387e77662bb9424d2740d5525e3e3f926fc`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/blind_review_packet.md` (`0c975951024c16273cbff4fcfb118387e77662bb9424d2740d5525e3e3f926fc`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/declaration_dossier.md` (`15dba63b57d9b3690d0179581d160a4d2aaae767626e1ec281f04817eeea6267`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/dependency_inventory.json` (`ac4a43ae69afafdc168b21fdeb3963d798e6e38ed2904247434b84636da2729d`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/direct_review_packet.md` (`aaf01687c9432344e24d4ca7ec3f7a1c70aed9cf70e003232fea873cc2ca153b`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/source_locator.json` (`4b1b954e2df0431e5626df4ee70a912ba59a36064b3ad45d272bc96b4f10cb3c`)
