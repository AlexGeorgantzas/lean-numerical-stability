# Faithfulness audit: P09-T2

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `3817f663b3d7b50fe06b6ec0197027f47621bee5a6de7a84aa2ffad9b077cc79`
- Paper SHA-256: `9076fe377cc64878a4a10f8a47ff49245bc5acaf116ffbd8e2ccca57033da758`

## Decision

The declaration correctly represents the positive-sign unnormalized DFT, exact input, forward error, fictional transform preimage, RMS scaling, K formula, and the displayed leading RMS and maximum bounds. It nevertheless concerns a materially different and restrictively conditional proposition. The paper derives its stage estimates for an implementation whose radix-2 and radix-4 blocks avoid trigonometric evaluation and multiplication; Lean executes those operations while retaining the optimized constants and then assumes a universal envelope that can be uninhabited because the omitted errors are first order. The source also does not state the target's cross-epsilon and cross-family remainder scopes. These defects independently block both implication directions. The unresolved Pi-norm body and precise big-O convention therefore do not justify an undetermined result.

## Implications

- **Lean implies paper:** `no`. Lean concludes the certificate only after receiving a universal stage envelope, and that envelope can be uninhabited for the paper's intended radix-2 and radix-4 plans because D057 performs omitted first-order operations. A conditional or vacuous result for a different execution does not recover the paper's guarantee from its arithmetic-model hypotheses.
- **Paper implies lean:** `no`. The paper analyzes specialized radix-2 and radix-4 blocks with no trigonometric evaluation or multiplication, not D057's unconditional rounded roots and general complex products. It also does not state the target's all-epsilon family or universally quantified stage-envelope scope. Thus it does not entail the formal proposition under its distinct execution semantics.

## Findings

- **critical / radix execution and vacuity:** No fixed quadratic coefficient can absorb the missing linear term as epsilon tends to zero. Because D018 quantifies over every matching family, the stage-envelope hypothesis is uninhabited for this intended radix-2 case; analogous omitted first-order trigonometric errors affect radix 4.
- **major / unsupported stage premise:** Substantive analytic content is moved into an additional, stronger hypothesis rather than inherited under the paper's stated assumptions, materially reducing applicability.
- **major / quantifier and remainder scope:** The target asserts a different asymptotic and uniformity structure whose equivalence to the source is not established.
- **minor / maximum-norm import:** The expected maximum-norm interpretation is plausible but cannot be certified from the permitted declaration frontier; this does not affect the classification forced by larger defects.
- **note / resolved definitions:** Neither Fourier sign nor opaque variant tags remain a consequential reason for rejection.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `unclear` |
| `S04` | `fail` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `unclear` | `unclear` |
| `S07` | `pass` | `pass` |
| `S08` | `fail` | `fail` |
| `S09` | `pass` | `unclear` |
| `S10` | `fail` | `pass` |
| `S11` | `pass` | `pass` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `pass` |
| `S14` | `unclear` | `unclear` |
| `S15` | `fail` | `pass` |
| `S16` | `pass` | `fail` |

## Dependency coverage

- Blind translator covered `208` dependencies (`0` hash-reused meanings); unclear: `D024, D040, D041`.
- Direct judge covered `208` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D005, D009, D011, D018, D024, D040, D041, D049, D057, D060, D149`.

## Remaining uncertainties

- The supplied declaration frontier does not unfold Pi.seminormedRing.toNorm, so p09ComplexMax cannot be proven from this packet alone to equal max_k |x(k)|, although that is the canonical interpretation.
- The paper does not specify constants, radii, or uniformity dependencies for O(epsilon^2), so the exact intended formal big-O scope remains underdetermined.
- A complete characterization of which exceptional inputs and parameters admit D018 for radix-2 or radix-4 plans is not supplied; explicit admissible counterexamples are sufficient to establish vacuity for intended nontrivial cases.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/agent_outputs/adjudicator.json` (`5720596917e91eabf65ff6afa0e3ed71724c5a2ca9ec3c76621fd1d2d84e494a`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/agent_outputs/blind_translation.json` (`0202885894838ab362f451064d66327321df6aa23ea69ad54e661fe5183442d2`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/agent_outputs/direct_judge.json` (`5212034f088cbde5190ceeed90b0ad1eef5ff9a6f2ff5438571d0c0a74291b93`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`16e552b55e2dd1a5682dac70791c86b055a01be7ada05b32d7c4ecbf1340014b`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/agent_outputs/source_contract.json` (`9ac6fe5b5525884c25b9e12ecefa44a5b14c0cf1cac5898f43de43c60cf446bd`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/decision.json` (`a924d401332161e695e9bd36cf1822267d365873c433d19476fe73f5cd7493ed`)
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
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260822T183252Z/agent_outputs/adjudicator.json` (`32d231526124ff7216b8ced4a4a26e993c38898a007eeb01bb4d3d8be0ccd984`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260822T183252Z/agent_outputs/blind_translation.json` (`a30dce2ebd4d1302e853803a3c7521d60436006ec060dbdb90d91ca2128af8e8`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260822T183252Z/agent_outputs/direct_judge.json` (`b1b9103364f63cf3c66eb246aa93ab9c6c9d55260c44e19bb40a832890836102`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260822T183252Z/agent_outputs/roundtrip_judge.json` (`571a985f3040da45d5311799fe56cd67f51edea078dd5de81c92e675a7a969dc`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260822T183252Z/agent_outputs/source_contract.json` (`f5ae5a89c6846df0dcafaacd3635022fc7111591b14d5f6cc70fcd42c412e35e`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260822T183252Z/decision.json` (`a604cd8884284212475c66f3b1d0ea99fed2091c5e95db97ab12226b16bc3c25`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260822T183252Z/inputs/blind_dependency_inventory.json` (`7fd63cb3d76ca64de3012f97ede701e0e99797b84dc26793b1d9926fab183ffe`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260822T183252Z/inputs/blind_dossier.md` (`0c975951024c16273cbff4fcfb118387e77662bb9424d2740d5525e3e3f926fc`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260822T183252Z/inputs/blind_review_packet.md` (`0c975951024c16273cbff4fcfb118387e77662bb9424d2740d5525e3e3f926fc`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260822T183252Z/inputs/declaration_dossier.md` (`15dba63b57d9b3690d0179581d160a4d2aaae767626e1ec281f04817eeea6267`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260822T183252Z/inputs/dependency_inventory.json` (`ac4a43ae69afafdc168b21fdeb3963d798e6e38ed2904247434b84636da2729d`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260822T183252Z/inputs/direct_review_packet.md` (`aaf01687c9432344e24d4ca7ec3f7a1c70aed9cf70e003232fea873cc2ca153b`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/history/20260822T183252Z/inputs/source_locator.json` (`4b1b954e2df0431e5626df4ee70a912ba59a36064b3ad45d272bc96b4f10cb3c`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/blind_dependency_inventory.json` (`2ea809f723b9828030b2da782b55dde66ef1994a1549be1b94937d17bd42534f`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/blind_dossier.md` (`073e4dc099c4dbd823dc336482204e6ff57e62e38cc420a31def27d7398d5c64`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/blind_review_packet.md` (`073e4dc099c4dbd823dc336482204e6ff57e62e38cc420a31def27d7398d5c64`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/declaration_dossier.md` (`85ec494a238812c5d5c24e401e65884309bafc8562b1fd9f11cbd044097299a8`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/dependency_inventory.json` (`83baf03811a70b72c2b9273dd65365937157d48d08008961d0bc869ac2f057c5`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/direct_review_packet.md` (`3ecae609c9bb1e76a89cdd53b12e12fbfe13c270d5030f24ba43f08a3cfa52eb`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/source_locator.json` (`49d1205d051040de49c5f69f4f9a1e0b8c8bb23b23fee9b6f36ab7202bb2504f`)
