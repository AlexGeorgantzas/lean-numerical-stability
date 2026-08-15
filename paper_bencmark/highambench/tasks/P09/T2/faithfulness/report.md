# Faithfulness audit: P09-T2

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `ab34e0817be964c449461a4e5bd02e397e304d57fab6d1d149cd67ca767423b5`
- Paper SHA-256: `9076fe377cc64878a4a10f8a47ff49245bc5acaf116ffbd8e2ccca57033da758`

## Decision

The declaration preserves the central finite-dimensional backward-error algebra and mixed-radix constants, and packaging Fourier surjectivity and RMS scaling as plan proofs is acceptable. It nevertheless replaces the paper's derived, asymptotic FFT result with a conditional statement over abstract traces and fixed-epsilon certificates. Because the remainder coefficients are selected after epsilon and can absorb arbitrary errors, this is neither an equivalent theorem nor a genuine nonvacuous strengthening. The paper and Lean propositions fail to imply one another, so not-faithful-different is the required classification. The unresolved additive-character sign is recorded explicitly but is not needed to reach that classification.

## Implications

- **Lean implies paper:** `no`. The Lean proposition is a conditional algebraic conversion from an assumed fixed-epsilon forward certificate. Its coefficient may depend on epsilon and can absorb arbitrary finite error, while its run need not arise from the model's floating operations. It therefore cannot imply the paper's asymptotic guarantee for the analyzed FFT, even if ZMod.stdAddChar has the required positive sign.
- **Paper implies lean:** `no`. The paper establishes an asymptotic result for its actual factorized floating-point FFT. It does not entail a universal exact finite-epsilon proposition over the declaration's abstract certified traces and supplied coefficients, nor does it furnish those proof objects for every value admitted by the Lean binders.

## Findings

- **critical / higher-order semantics and nonvacuity:** The formal premise loses the paper's epsilon-uniform first-order stability content and makes the numerical result hold for an unintended pointwise reason.
- **major / conditionalization and execution linkage:** The target is a generic backward-conversion lemma over certified perturbation traces, not the paper's guarantee for computed FFT outputs.
- **major / Fourier convention evidence gap:** Positive-sign agreement cannot be certified from the supplied declaration evidence, although independent defects already determine rejection.
- **note / faithful algebraic core:** The rejection concerns quantifier scope, asymptotic meaning, and execution applicability rather than the displayed leading formulas.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `pass` | `unclear` |
| `S07` | `pass` | `pass` |
| `S08` | `fail` | `pass` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `pass` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `pass` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `162` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `162` dependencies (`0` hash-reused interpretations); failing or unclear: `D002, D004, D005, D018, D020`.

## Remaining uncertainties

- The sign of ZMod.stdAddChar cannot be established from D120 because the supplied evidence does not unfold ZMod.toCircle or state its value. The transform is confirmed unnormalized, but positive-sign agreement remains unverified.
- The PDF does not specify the hidden O(epsilon^2) constants, their dependence on N, gamma, or x, or a small-epsilon threshold. This leaves the exact preferred asymptotic formalization underdetermined, but it does not validate a coefficient allowed to depend on the already fixed epsilon.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/agent_outputs/adjudicator.json` (`091bf73a774d2e3d643ca282f2c032bac2c208d627a73141548aae4cbac189dc`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/agent_outputs/blind_translation.json` (`1c753d37afb428894eaad95599c7cec61826074b14aa7c9274233a5507a47e59`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/agent_outputs/direct_judge.json` (`882916ced92d3ab4fe6c25cdd342d9261c936a9f74a66d40211420e08edf69e1`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`eefd237d2778ac2f6cc6c53c7fedc460e58475fe9fd49a5c09501d492479a6fc`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/agent_outputs/source_contract.json` (`e8ffe5fc61a1df580946a6085eae8513cb61e84787422d4500a5edbc719ba582`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/decision.json` (`dcae794023f75446c4904ea82e99b1e2451f2f39b3bb9eb0f581e53e4df50d41`)
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
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/blind_dependency_inventory.json` (`9083072565d9b948ab2309aaead1e1f81c3b785b151639c842d01a97d2904e14`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/blind_dossier.md` (`0407fa65f3f935d0fa18ef6e7d381ef96bc34118b153c51cc3f7973a3f7c0110`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/blind_review_packet.md` (`0407fa65f3f935d0fa18ef6e7d381ef96bc34118b153c51cc3f7973a3f7c0110`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/declaration_dossier.md` (`1c28ca488b355c604c72957bd3c044e592f99a3938569f1b0912b32b17352945`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/dependency_inventory.json` (`2d70beae42489d91a39dfee6c09ee5bcb678d5b476c088f27bad2e83dbe818a6`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/direct_review_packet.md` (`ac6d20d9406c4d00d9d7f5ab1da79719debe8edff54949e38ad834a30e68040f`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/source_locator.json` (`4b1b954e2df0431e5626df4ee70a912ba59a36064b3ad45d272bc96b4f10cb3c`)
