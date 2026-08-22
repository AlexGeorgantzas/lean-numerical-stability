# Faithfulness audit: P20-T3

- Classification: `not-faithful-weaker`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `dcc89a9a1a76d2083786647d8d7cf10e9b1dab20ab322d5411f89cd367b38005`
- Paper SHA-256: `ad830de20a73ff77b6e457921892b3250ba9ff70f487501979ee3f1c5f3f31e2`

## Decision

The declaration accurately models Model 1, the weighted recurrences, retained pairs, infinity norm, maximal scaling used by the derivation, and all four coefficients of (4.32). Its decisive logical defect is that P20StaticSection4Derivation turns the paper's substantive derivation into an optional antecedent, while P20FirstOrderSemantics gives no numerical meaning to higher-order smallness. The second bound is only a regrouping of (4.32), not (4.33). Concrete execution choices are acceptable specializations but merely narrow applicability. Thus the paper entails the restricted conditional declaration, while the declaration does not entail the paper theorem, yielding not-faithful-weaker rather than stronger or equivalent.

## Implications

- **Lean implies paper:** `no`. Lean does not establish that a modeled run has a Section 4 derivation certificate, permits remainder predicates with no smallness meaning, covers only a concrete restricted execution, and does not state the standalone range-unrestricted bound (4.33). It therefore cannot recover the paper theorem.
- **Paper implies lean:** `yes`. For the intended maximal-scaling specialization, the paper derives the facts placed in P20StaticSection4Derivation and hence entails the target's conditional regrouped bounds. The remaining two conjuncts are algebraic identities for positive p. The target demands less because it never asserts certificate existence.

## Findings

- **critical / conclusion-bearing-assumptions:** The declaration proves only a conditional combination lemma and supplies no forward-error theorem from the modeled computation alone.
- **critical / arbitrary-first-order-semantics:** The bound can be numerically vacuous or its antecedent can be uninhabited, so it does not faithfully formalize the paper's leading-order claim.
- **major / range-unrestricted-comparison:** The declaration duplicates (4.32) in regrouped form and omits the distinct comparison result.
- **minor / restricted-execution:** This is an acceptable but narrower specialization and cannot count as stronger theorem content.
- **note / source-scaling-defect:** The discrepancy originates in the source restatement rather than in Lean's reconstruction of the derivation.
- **note / source-coefficient-defect:** The main (4.32) Lean coefficient remains correct, but the qualitative single-word comparison cannot be uniquely formalized.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `fail` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `unclear` |
| `S09` | `pass` | `pass` |
| `S10` | `unclear` | `unclear` |
| `S11` | `pass` | `pass` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `unclear` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `192` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `192` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D002, D006, D007, D015, D022, D023, D030, D034, D050, D052, D053, D057, D061, D065, D075`.

## Remaining uncertainties

- The PDF gives no formal global semantics for lesssim, so no canonical P20FirstOrderSemantics predicate can be recovered from it.
- The source does not resolve whether 4n^2 in equation (3.26) or 4n in the B796 comparison prose was intended.
- The exact summation-order and fusion assumptions of the imported Fasi et al. accumulation estimate are not stated in the permitted PDF.
- Theorem 4.1's literal upper-bound-only scaling hypothesis conflicts with the maximal-scaling condition used in its preceding construction and proof.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/agent_outputs/adjudicator.json` (`c8bbfb397a9af5f2c107e66aabd953fc4064d67e0a3f7b2a77dcea806509b3af`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/agent_outputs/blind_translation.json` (`58dbafcca16c78d60b0d38a109e68914eca01571fd8cd37e30c6c3d4783fa127`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/agent_outputs/direct_judge.json` (`c2e28e08aa7777b88621c2d08585b6cef819d5887ae0492bbec4def90ca1e600`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`456b2c2b5c8001ba32d8c71d7d9800d0ab3b26caeb80ca683439f99a4b1a9056`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/agent_outputs/source_contract.json` (`8c90d5c3f7fc032fb60431b0562033819d11a36c5886074a267b5a858f697286`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/decision.json` (`9fa6f03215297e7354f16ea4b0da3ccd839c1e30c0931a21ae6eacffbc76c878`)
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
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260822T015211Z/agent_outputs/adjudicator.json` (`9ca3de35d120439cc6a634c0ece866ee5086d55554a65bf9bab18be55b6eb83f`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260822T015211Z/agent_outputs/blind_translation.json` (`0aac426aa3fa48cc1fd7866564f7d984b768828c188dbc2d8e09ecfa9df2a24c`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260822T015211Z/agent_outputs/direct_judge.json` (`2c161af09396c465cd67b08ca42834473d7700d205cad3bf77f5d555bceb2068`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260822T015211Z/agent_outputs/roundtrip_judge.json` (`c8a4924f4a2e9d262d01f92b97e1a9caaea4b003da99481aa9376a28707d7858`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260822T015211Z/agent_outputs/source_contract.json` (`dca1b4fb3362d81a2ef506e23459d53d4e8ebd6e7e47261c9dd1074e737b4f36`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260822T015211Z/decision.json` (`82efa75efdfa825cb4d034c741c815f597584f90b1e53627c3a403e4459c9554`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260822T015211Z/inputs/blind_dependency_inventory.json` (`4bd0d2f8629478b2d7a45ff7d8c665a010db7e14b9c1da04e62f7c35aa10257b`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260822T015211Z/inputs/blind_dossier.md` (`7db75d6cb9a0d833c38a2b8b368298fca871d8f5cb9dd6db596cb09e46f71f5e`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260822T015211Z/inputs/blind_review_packet.md` (`7db75d6cb9a0d833c38a2b8b368298fca871d8f5cb9dd6db596cb09e46f71f5e`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260822T015211Z/inputs/declaration_dossier.md` (`4d223c37309c24f3cb166980bf96861b37d668bc446cc87dd476fd96ae3e8da2`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260822T015211Z/inputs/dependency_inventory.json` (`020d56f2d912de9bb4a1e25f6b66ebfbcca7fd0d6bec13523b456fb21b84474b`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260822T015211Z/inputs/direct_review_packet.md` (`950c4daa24caf3e938c2e3f137f6fa13a777dcbb9b8b77e2fefddba1ddc77b2c`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/history/20260822T015211Z/inputs/source_locator.json` (`f4be54770253e03986d14e84ed9df1bab284a47591954177e31a56354067989a`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/inputs/blind_dependency_inventory.json` (`d1557a116adb84333f9c72576dbbb3b8b0c490df8702bbccd1907b2d6364cf99`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/inputs/blind_dossier.md` (`9a3c9998130d30a496b3db418b9c4fce13cf5f56a370d64b581e145ad244cee3`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/inputs/blind_review_packet.md` (`9a3c9998130d30a496b3db418b9c4fce13cf5f56a370d64b581e145ad244cee3`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/inputs/declaration_dossier.md` (`358b57aa991896d6424ce8c9f8200dbc087585a88c8d32c1e2ce3f2f38437ad1`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/inputs/dependency_inventory.json` (`837047a1d5aac20bb6f1537230b6e9a2accd05fc13cdc5beed06f724ac0cc295`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/inputs/direct_review_packet.md` (`830bb2327108842bcb47ff086f72531a271b6fe54528aa022b74ed4bf33b4820`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/inputs/source_locator.json` (`f4be54770253e03986d14e84ed9df1bab284a47591954177e31a56354067989a`)
