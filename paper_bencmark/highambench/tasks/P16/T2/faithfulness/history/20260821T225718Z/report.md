# Faithfulness audit: P16-T2

- Classification: `not-faithful-weaker`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `1c582176b5d6f0ea639794f09f49d14c1343fed97e7e030bd8cc1c506739809a`
- Paper SHA-256: `8010a50989428b09ea9f204875cd6cfde6c08c924beb40887a6921287605737a`

## Decision

Primary evidence resolves the disagreement without interpreting the paper's informal lesssim directly. The exact inequality derived after (4.18), combined with D020's additional iterate-comparison witness and epsilonR tending to zero, yields the Lean O(scale^2) conclusion, so the paper implies Lean. The converse fails because Lean addresses only eventual members of vanishing-error filtered families and cannot recover a general fixed small positive-parameter instance of Lemma 4.2. The declaration is nonvacuous and its algebraic core is correct, but its reduced applicability is not genuine theorem strength. Therefore the appropriate classification is not-faithful-weaker.

## Implications

- **Lean implies paper:** `no`. The Lean theorem only gives an eventual result for filtered families whose epsilonR and epsilonU tend to zero and whose iterate norms satisfy an explicit O(scale^2) comparison. A paper instance with fixed nonzero small epsilon_r or epsilon_u cannot be represented by the corresponding constant Lean functions, and placing such an instance at a non-eventual parameter value yields no conclusion about it. Thus Lean does not recover the paper's fixed-instance claim.
- **Paper implies lean:** `yes`. The exact bound following (4.18) applies pointwise to the data stored by D020. If q=O_l(scale^2) witnesses ||xHat||_2 <= ||xHatNext||_2+|q| eventually, substitution into that exact bound leaves at most epsilonR*||A||_F*|q| beyond the Lean RHS. Since epsilonR tends to zero, it is eventually bounded, so rho=epsilonR*||A||_F*q is O_l(scale^2). This proves D014's output relation under the Lean package's additional assumptions, independently of assigning a formal meaning to the paper's lesssim symbol.

## Findings

- **major / quantifier and parameter regime:** The Lean theorem excludes ordinary fixed positive-error instances covered by the paper and therefore cannot imply the source result.
- **major / higher-order semantics:** The central first-order relation receives a precise but unsupported restrictive interpretation.
- **minor / iterate comparison:** Lean repairs a premise used informally by the proof but narrows the published lemma's stated applicability.
- **note / algebraic core:** The mismatch concerns formal asymptotic scope and applicability, not the one-step residual algebra; the paper's exact derivation consequently proves the restricted Lean theorem.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `unclear` | `fail` |
| `S03` | `unclear` | `fail` |
| `S04` | `unclear` | `fail` |
| `S05` | `pass` | `fail` |
| `S06` | `unclear` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `pass` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `fail` |
| `S11` | `pass` | `fail` |
| `S12` | `unclear` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `unclear` | `fail` |
| `S15` | `unclear` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `77` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `77` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D005, D006, D014, D020, D021, D024, D026, D052, D053, D054, D073, D076`.

## Remaining uncertainties

- The PDF does not define lesssim beyond dropping negligible second-order terms, so p16FirstOrderLeAt cannot be certified as the unique or equivalent formal semantics of that notation.
- The PDF gives no numerical threshold for epsilon_r, epsilon_u << 1, so convergence to zero is an added asymptotic replacement rather than an exactly source-defined condition.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/agent_outputs/adjudicator.json` (`e7ed62ab3d6cbd739727ee5cd9a17405b39d8345a271083cc16ce0693047ac3b`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/agent_outputs/blind_translation.json` (`612ada7e02c1017721b3f271ab06420c1c7d2fe954b21f907819a2c66db71707`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/agent_outputs/direct_judge.json` (`e26184c1056721914d3c7b6955a693cef4aad8da10886602a66649d8df2fb545`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`b72a1a340ebf6c0568175ec2e32a0bdedb5bb76225d3c76c58b90066de3d23ec`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/agent_outputs/source_contract.json` (`4e27507df9d886c93512cab4f3bc5ad1e36c206681d1cdc4ee8f13318d544972`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/decision.json` (`1e161efa050652c78f63b6ca6a048d1d7e96ba75cf201074d916539cb97e0460`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/agent_outputs/adjudicator.json` (`1b8959d2395c14cb7189660f1ae067008578d70549c4d3a411699582e9bdadeb`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/agent_outputs/blind_translation.json` (`5c9a00047f3cb9813163120f1eee6b33b1971674bf133751c7e087fe00834548`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/agent_outputs/direct_judge.json` (`b047420c779d23bb80c30034c2270b51ec4f2f4ad00836f75ed532cfe8bf83bf`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/agent_outputs/paper_source_contract.json` (`cc856c94ce22bcb89d018b431db65cfb6c20d25df7bb6aaeb660c48c42f5c886`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/agent_outputs/roundtrip_judge.json` (`7d93fca173362bd374eb788da4b1ce2a5e7520ac69fe8c0e001949691c975870`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/agent_outputs/source_contract.json` (`e1d181bd77d7b8c9b9b292be1fc2276b17a9554977b9abf781fd20cb5c26c5de`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/decision.json` (`d03f965dfd639d090cf8c87646d766d2ee4ce1099816948e5b5fe39973f82104`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/inputs/blind_dependency_inventory.json` (`16dc7b65cb4bd6f0f76fa5585c49f0979dba60b163f8cf1dc3c9bd3e2f543964`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/inputs/blind_dossier.md` (`949361f0cf8c550acb646de63287bb6f07aea3530ba6be2b9cb5775b3fe6de59`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/inputs/blind_review_packet.md` (`949361f0cf8c550acb646de63287bb6f07aea3530ba6be2b9cb5775b3fe6de59`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/inputs/declaration_dossier.md` (`4d2a699808e29d897b8dde89f2702935a390164f78f4902d13dc2acd3950f058`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/inputs/dependency_inventory.json` (`3c886a74cbb732dc7fdf8c2cc18430a344e642faba3cc73e9653630161c9e3bb`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/inputs/dependency_reuse_direct.json` (`f3914a20e8ced9b6bf1423ed488bddad18f4a4e2e9fa38a43312d7af5a141c8f`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/inputs/direct_review_packet.md` (`d37eb5e7721b942f5a744027cbbd07717b816fc114c92affb696cfecd27e7825`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/inputs/paper_source_locator.json` (`29399d42dec8e4d771178436cda1303a77490d8820b032eb370ddffe5e202bd7`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/inputs/source_locator.json` (`fdd20bedee03410eed50151bee4551892c4f79ae6d8fe62492a246d75b1eb45a`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/inputs/blind_dependency_inventory.json` (`cc4db05db44a27ceb5798713819fa836637982f8bad6578aa398044b59eeaff9`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/inputs/blind_dossier.md` (`070aa76520bd211b5d085872c47d451382cc9b5ee77520763055ffd0ca07b2ce`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/inputs/blind_review_packet.md` (`070aa76520bd211b5d085872c47d451382cc9b5ee77520763055ffd0ca07b2ce`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/inputs/declaration_dossier.md` (`cc819da3b14b4610985069f8d35e6ae11caef9961ed6c17320a17542ed54ae77`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/inputs/dependency_inventory.json` (`a5c943007118ade426fa61a17b29a249a6a421d6fde910ef505fffcc31e6d995`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/inputs/direct_review_packet.md` (`9676235fc0d20bbecb9e1910de47f20ee3a54be69a4bfe86f74e08d747a210db`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/inputs/source_locator.json` (`bb48d9ef1a2d4bb35de11367b04e7983b303f3a6a76f066cc78a7c8b26b10d9d`)
