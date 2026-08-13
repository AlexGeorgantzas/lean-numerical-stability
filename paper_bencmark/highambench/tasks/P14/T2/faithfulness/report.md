# Faithfulness audit: P14-T2

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `false`
- Target SHA-256: `da7d602967646f6cc6512c666c64f2d64c3051c712686478d686fe1c8bd13b85`
- Paper SHA-256: `7247047bc49218e001195edc8a2d66131eea7596d252503f34b0ace6328981cd`

## Decision

The verified paper derives a per-component relative error with first-order coefficient n+3 and then weakens it to Theorem 3.3's relative infinity-norm bound. The Lean proposition faithfully models the unshifted Algorithm 3.1 data path, keeps exact and computed quantities separate, and provides a nonvacuous exact componentwise bound. Under epsilonExp=epsilonDiv=u its bound expands to (n+3)u+O(u^2), so it implies the paper result. The converse fails because the paper supplies neither the explicit higher-order bound nor the arbitrary-error-radius generalization.

## Implications

- **Lean implies paper:** `yes`. Specialize epsilonExp=epsilonDiv=u and apply the target separately with each component's division error. For fixed n as u tends to zero, denominatorRadius=(n+1)u/(1-nu), numeratorRadius=2u+u^2, and the exact bound is (n+3)u+O(u^2). The uniform componentwise result implies Theorem 3.3's relative infinity-norm bound.
- **Paper implies lean:** `no`. Theorem 3.3 is normwise and asymptotic, and even the preceding componentwise derivation leaves the O(u^2) coefficient unspecified. It therefore does not imply this explicit rational componentwise bound for arbitrary independent epsilonExp and epsilonDiv.

## Findings

- **note / exact-strengthening:** The formal conclusion is stronger while recovering exactly the paper's first-order coefficient.
- **note / componentwise-versus-normwise:** The displayed theorem is not copied literally, but it follows as a direct corollary of the stronger pointwise statement.
- **note / asymptotic-domain:** These restrictions are compatible with the fixed-n asymptotic paper result but should not be misread as proving an unrestricted finite-n version of equation (3.6).
- **note / explicit higher-order strengthening:** The statements are not literally equivalent, but specialization and asymptotic expansion show that the translation entails the paper result.
- **note / componentwise strengthening:** The translated conclusion is stronger and yields the theorem's normwise conclusion immediately.
- **note / abstract execution model:** This is a general extensional formulation; the concrete paper execution is a valid specialization, but the paper does not imply the full generalized claim.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `pass` | `pass` |
| `S04` | `pass` | `pass` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `pass` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `pass` | `pass` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `pass` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `66` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `66` dependencies (`58` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P14/T2/faithfulness/agent_outputs/blind_translation.json` (`128f5ae09758a87c29293b3b83e87e4442fa5fed9416272ddb96731394b3e1c5`)
- `paper_bencmark/highambench/tasks/P14/T2/faithfulness/agent_outputs/direct_judge.json` (`83092b096f8cef584e241f8e3c2b2d8c2037b4de8bfe8bac1a80e4845fe7392f`)
- `paper_bencmark/highambench/tasks/P14/T2/faithfulness/agent_outputs/paper_source_contract.json` (`b9f05c969428f95fef40bddc0aa0b2a7c1d291ecdd7ba0ca0f5fb748131f1562`)
- `paper_bencmark/highambench/tasks/P14/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`0f6e6ffeda634dfc8541e391b086c4416f18c527cd13cdf7f157bb61e5dcdfb0`)
- `paper_bencmark/highambench/tasks/P14/T2/faithfulness/agent_outputs/source_contract.json` (`c2febe0a862ab2a59dfa2eda8c2dd1de209f1b950cc8fc7f38d5dcabfad8fc9a`)
- `paper_bencmark/highambench/tasks/P14/T2/faithfulness/decision.json` (`01d4ea56542cf20d6aa842b3f830d8d8482266c807a164aa5f3f3736dde71424`)
- `paper_bencmark/highambench/tasks/P14/T2/faithfulness/inputs/blind_dependency_inventory.json` (`124d399bbd27e91096035b4e63538978f6c0e8c2f5a6305f61c357cfd3e6315c`)
- `paper_bencmark/highambench/tasks/P14/T2/faithfulness/inputs/blind_dossier.md` (`579b71d2b34a9fd7ab78dac47a79e6345de8f1ffbd349d47d8b12351cca4329f`)
- `paper_bencmark/highambench/tasks/P14/T2/faithfulness/inputs/blind_review_packet.md` (`579b71d2b34a9fd7ab78dac47a79e6345de8f1ffbd349d47d8b12351cca4329f`)
- `paper_bencmark/highambench/tasks/P14/T2/faithfulness/inputs/declaration_dossier.md` (`cacf87184ca6403b487521c96c6d978c14fb866c509e27e49fa113308d751859`)
- `paper_bencmark/highambench/tasks/P14/T2/faithfulness/inputs/dependency_inventory.json` (`7907615fc979942df5bc3c062216a9b32cf88a630f858d7b3afd1444457ebcbf`)
- `paper_bencmark/highambench/tasks/P14/T2/faithfulness/inputs/dependency_reuse_direct.json` (`e3517072ca73b81ffee0bb8ac10108e9835dd4c81586cd6b97f5daf857b1dd0b`)
- `paper_bencmark/highambench/tasks/P14/T2/faithfulness/inputs/direct_review_packet.md` (`5c383a9af10d3e70a3c104256977fb55fb21fa6424cf0fe15bab564d202e569a`)
- `paper_bencmark/highambench/tasks/P14/T2/faithfulness/inputs/paper_source_locator.json` (`8627ed196c1c7742168563780358efbf3ebaee357ded297978c4d9199a86318c`)
- `paper_bencmark/highambench/tasks/P14/T2/faithfulness/inputs/source_locator.json` (`057f36db017dd6c087e40113fa056eab4cf3880e5ecd5e82e16f3d21dce215eb`)
