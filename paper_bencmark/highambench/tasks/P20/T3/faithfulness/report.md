# Faithfulness audit: P20-T3

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `bed58eaf44970ecf9a18a1418f57786ae9f1f8abd20e7254aaf9ab0c7ad0749b`
- Paper SHA-256: `ad830de20a73ff77b6e457921892b3250ba9ff70f487501979ee3f1c5f3f31e2`

## Decision

The declaration correctly preserves the real matrix dimensions, positive word count within runs, maximal integer-power-of-two scaling, theta, triangular indices, four displayed coefficients, exact AB target, induced infinity norm, and normwise forward-error notion. Those matches do not overcome the substantive differences in hypotheses, quantifier scope, operators, algorithm, floating-point model, relation strength, higher-order treatment, and nonvacuity. The analysis certificate is a restriction rather than genuine theorem strength, while the abstract model and filter family also generalize in unsupported directions. Consequently neither statement implies the other under their intended semantics, so the correct classification is not-faithful-different.

## Implications

- **Lean implies paper:** `no`. The Lean declaration covers only runs already carrying the four desired source bounds and a second-order certificate, and its computed inner products use exact products with rounded additions. It therefore does not establish Theorem 4.1 for every paper-valid Model 1 execution.
- **Paper implies lean:** `no`. The paper treats fixed computations under Model 1 and does not supply an arbitrary filter-indexed certified execution, a uniform Big-O remainder, or a result for the declaration's exact-product accumulation algorithm and broader abstract rounding maps.

## Findings

- **critical / analysis assumed as hypothesis:** The formal theorem recombines pre-certified estimates rather than deriving the paper's bound from Model 1 and the algorithm, sharply reducing applicability and creating circularity risk.
- **critical / accumulation algorithm mismatch:** The formal computed matrix is generally not the paper's C-hat, so its forward-error assertion concerns a different execution model.
- **major / first-order relation and quantifiers:** The pointwise first-order estimate is replaced by a different and potentially much weaker asymptotic proposition.
- **major / floating-point model scope:** The declaration admits operations outside the paper's rounding model and omits conditions needed to identify its parameters with equation (4.32).
- **minor / conclusion coverage:** The selected surrounding comparison is not formalized as a forward-error result or qualitative reduction statement.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `fail` | `unclear` |
| `S07` | `pass` | `pass` |
| `S08` | `fail` | `fail` |
| `S09` | `pass` | `unclear` |
| `S10` | `pass` | `pass` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `196` dependencies (`0` hash-reused meanings); unclear: `D066`.
- Direct judge covered `196` dependencies (`0` hash-reused interpretations); failing or unclear: `D003, D004, D005, D008, D020, D023, D024, D025, D034, D041, D042, D043, D048, D049, D050, D054, D059, D062, D074, D089, D090, D097, D129, D176`.

## Remaining uncertainties

- The PDF does not formally specify a hidden constant or complete remainder semantics for lesssim; it states only that second-order terms are dropped. This does not support D008/D034's arbitrary-filter interpretation and does not affect the classification.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/agent_outputs/adjudicator.json` (`9ca3de35d120439cc6a634c0ece866ee5086d55554a65bf9bab18be55b6eb83f`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/agent_outputs/blind_translation.json` (`0aac426aa3fa48cc1fd7866564f7d984b768828c188dbc2d8e09ecfa9df2a24c`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/agent_outputs/direct_judge.json` (`2c161af09396c465cd67b08ca42834473d7700d205cad3bf77f5d555bceb2068`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`c8a4924f4a2e9d262d01f92b97e1a9caaea4b003da99481aa9376a28707d7858`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/agent_outputs/source_contract.json` (`dca1b4fb3362d81a2ef506e23459d53d4e8ebd6e7e47261c9dd1074e737b4f36`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/decision.json` (`82efa75efdfa825cb4d034c741c815f597584f90b1e53627c3a403e4459c9554`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T051937Z/agent_outputs/adjudicator.json` (`33b91bea9848f9e284403ba5996ef9d573290bdee539d90aff7aea9658eb8962`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T051937Z/agent_outputs/blind_translation.json` (`fd82eef2c6de222d0c0ac907e2dd4e8c73985046fb74d6327ad740ea03d3da22`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T051937Z/agent_outputs/direct_judge.json` (`1e4c437b52e42019cf8afb9b3b2b65e419aa40b982e11a1fe87a7063baa9bc44`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T051937Z/agent_outputs/paper_source_contract.json` (`a0c8bbaa2e261f7adc023b1698c08de77fd260aafddc9aa341073c2704530e40`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T051937Z/agent_outputs/roundtrip_judge.json` (`ac758b88d7a7beca06ca377ea164852ac001db62773eab33ddeb9d19e160af6b`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T051937Z/agent_outputs/source_contract.json` (`9eae542570f015fc88674a2ddca25ffc17c3f6674875ffa7b1d509a94bfbca4f`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T051937Z/decision.json` (`555aca327b67e395ae2a1d8d83be3ac568f4c5ab88d638f14a40c786958e02c7`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T051937Z/inputs/blind_dependency_inventory.json` (`707ebbfaffdc2dac59f2e36035ed9a35870686745713caf7d6157b185652e362`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T051937Z/inputs/blind_dossier.md` (`ed55d301c9b1849584a259886a4dcfe6ed0bc0dde3fe5d5ac94ecaa8d83259ad`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T051937Z/inputs/blind_review_packet.md` (`ed55d301c9b1849584a259886a4dcfe6ed0bc0dde3fe5d5ac94ecaa8d83259ad`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T051937Z/inputs/declaration_dossier.md` (`de0a20bdcc798c7ed05f41742d8c4f9dcde4fd3addf6ef2d118d6ba4f42f2eaf`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T051937Z/inputs/dependency_inventory.json` (`730438286fea988a1a591a527816d04d9d01909c2e2b36068ce90ed1717e8581`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T051937Z/inputs/dependency_reuse_direct.json` (`1fcf1c1503943d5ff72546eed502004eca7f0d13975c702cb7ee1e6fa864bcb8`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T051937Z/inputs/direct_review_packet.md` (`dc155ab8beb53199995d6e0ceedb7aaebde0eae65573f5adf492f5fcb61368b7`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T051937Z/inputs/paper_source_locator.json` (`413757004ac4d15ac7e55e926e2486e54bdac2db1523d83303ddb4cbffe644f4`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T051937Z/inputs/source_locator.json` (`decd8905bc8147d8e38b138ea8aa111abc6f17edffd6a0a7b11b676f4bc89fd7`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T083510Z/agent_outputs/adjudicator.json` (`faa4456f1641bfb7a71bb57e2f3594c9b0b16a3fa269622529397ff457fcecf8`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T083510Z/agent_outputs/blind_translation.json` (`239535a4e9833a8a053aa61e59dc02866b934ae9bca5affe60d68be15e25e8e8`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T083510Z/agent_outputs/direct_judge.json` (`f3e17a51964e35fd44b1adbd0fbfb1e261c00d5cff90a2dac4eb7421ec91c6d1`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T083510Z/agent_outputs/roundtrip_judge.json` (`23994649d391a09d02e895a829ce8766aac9d392a035b15c522e52fff27de51a`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T083510Z/agent_outputs/source_contract.json` (`1cbb097250530164114ee67a2ff0e3abb115d3ab0d1195443f21fd0e649e1b7f`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T083510Z/decision.json` (`011a8d0f3725eb76c986f57bf6553da0826917d56a9f858d11a92846b5d8d2ce`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T083510Z/inputs/blind_dependency_inventory.json` (`4bd0d2f8629478b2d7a45ff7d8c665a010db7e14b9c1da04e62f7c35aa10257b`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T083510Z/inputs/blind_dossier.md` (`7db75d6cb9a0d833c38a2b8b368298fca871d8f5cb9dd6db596cb09e46f71f5e`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T083510Z/inputs/blind_review_packet.md` (`7db75d6cb9a0d833c38a2b8b368298fca871d8f5cb9dd6db596cb09e46f71f5e`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T083510Z/inputs/declaration_dossier.md` (`4d223c37309c24f3cb166980bf96861b37d668bc446cc87dd476fd96ae3e8da2`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T083510Z/inputs/dependency_inventory.json` (`020d56f2d912de9bb4a1e25f6b66ebfbcca7fd0d6bec13523b456fb21b84474b`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T083510Z/inputs/direct_review_packet.md` (`950c4daa24caf3e938c2e3f137f6fa13a777dcbb9b8b77e2fefddba1ddc77b2c`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260821T083510Z/inputs/source_locator.json` (`f4be54770253e03986d14e84ed9df1bab284a47591954177e31a56354067989a`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/inputs/blind_dependency_inventory.json` (`4bd0d2f8629478b2d7a45ff7d8c665a010db7e14b9c1da04e62f7c35aa10257b`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/inputs/blind_dossier.md` (`7db75d6cb9a0d833c38a2b8b368298fca871d8f5cb9dd6db596cb09e46f71f5e`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/inputs/blind_review_packet.md` (`7db75d6cb9a0d833c38a2b8b368298fca871d8f5cb9dd6db596cb09e46f71f5e`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/inputs/declaration_dossier.md` (`4d223c37309c24f3cb166980bf96861b37d668bc446cc87dd476fd96ae3e8da2`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/inputs/dependency_inventory.json` (`020d56f2d912de9bb4a1e25f6b66ebfbcca7fd0d6bec13523b456fb21b84474b`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/inputs/direct_review_packet.md` (`950c4daa24caf3e938c2e3f137f6fa13a777dcbb9b8b77e2fefddba1ddc77b2c`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/inputs/source_locator.json` (`f4be54770253e03986d14e84ed9df1bab284a47591954177e31a56354067989a`)
