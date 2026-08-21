# Faithfulness audit: P16-T3

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `f4fd7fadeb5011d3242f9db9f4fa709426c292bf44a1a4353d37ed7d00118107`
- Paper SHA-256: `8010a50989428b09ea9f204875cd6cfde6c08c924beb40887a6921287605737a`

## Decision

The declaration correctly represents the finite real system, exact backward and forward error quotients, Frobenius condition number, high-precision residual/update models, low residual cast, both floor formulas, and the proof-supported upper direction for the contraction coefficient. The complete dossiers also resolve D024, D033, S06, and S11 without residual dependency opacity. Nevertheless, the theorem is propositionally different from Theorem 6.3: it assumes restart-local convergence records, omits the residual initialization that identifies the basis as the selected MGS-GMRES execution, permits a non-polynomial run-dependent dimension factor, replaces qualitative discarded terms with fixed-precision exact remainders, and concludes stationary envelopes that do not preserve the printed attainable levels under its weaker lambda<1 premise. Consequently neither statement implies the other.

## Implications

- **Lean implies paper:** `no`. The Lean proposition covers only runs already carrying exact local convergence certificates and uniform remainder bounds, and D033 admits basis processes not linked to the cast residual as the starting MGS-Arnoldi vector. Its unrestricted data-dependent dimensionFactor and lambda<1 envelope also do not yield Theorem 6.3 for every source execution with a dimension-polynomial c(n,k_i) and the printed attainable levels.
- **Paper implies lean:** `no`. The paper's qualitative first-order theorem does not provide exact uniformly quadratic remainder sequences at fixed precisions, pre-existing P16Theorem41RestartResult records, one fixed run-level dimensionFactor, or the exact all-index geometric envelopes required by Lean.

## Findings

- **critical / conclusion-bearing applicability restriction:** The target proves its central recurrence only for runs that already assume that recurrence in restart-specific form. This reduced applicability cannot be counted as a genuine stronger theorem.
- **major / incomplete MGS-GMRES linkage:** Admissible Lean restarts may be certified modular basis solves rather than executions of the selected restarted MGS-GMRES algorithm.
- **major / dimension-factor semantics:** The contraction and floors may contain arbitrary problem-dependent factors absent from the source claim.
- **major / unsupported higher-order exactification:** The predicate does not express the cross-precision quadratic asymptotics suggested by the source and is additionally assumed for the stored theorem remainders.
- **major / attainable-level mismatch:** For lambda near one, the formal stationary bounds can be arbitrarily larger than both source attainable levels.
- **minor / extra execution restrictions:** The formal domain is narrower than the selected paper theorem independently of the conclusion-bearing theorem41 field.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `pass` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `pass` | `unclear` |
| `S07` | `pass` | `pass` |
| `S08` | `fail` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `fail` | `fail` |
| `S11` | `pass` | `unclear` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `115` dependencies (`0` hash-reused meanings); unclear: `D024, D033`.
- Direct judge covered `115` dependencies (`0` hash-reused interpretations); failing or unclear: `D002, D003, D008, D015, D016, D018, D019, D020, D021, D023, D024, D025, D027, D033, D034`.

## Remaining uncertainties

- The paper leaves k unbound in c(n,k) in Theorem 6.3 while supplying potentially varying k_i in the proof, so it does not determine a unique exact uniform polynomial envelope.
- The source's lesssim and much-less-than notation does not determine explicit remainder functions, constants, or a numerical contraction threshold.
- The low-cast display on printed page 1979 omits the norm subscript on its right-hand side; interpreting it as the 2-norm, as Lean does, is strongly supported by condition (3.2) but is not typographically explicit.
- The paper calls the precisions high and low but does not print uHigh <= uLow as a separate hypothesis.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/agent_outputs/adjudicator.json` (`59b3d40f8c979408ef74737e590b00458845eedc90294fea79f452f5b3cf116a`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/agent_outputs/blind_translation.json` (`0302a2133f6ba47e05d1cddf06747a3fc64395b8649528a0370b1e737955d055`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/agent_outputs/direct_judge.json` (`3b6fa31131fb774d67a410c3c0afbbc21a2a7a473a33dbecebce4a73a78c6e0b`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`f325390cdacf499eb37db570bfaf641f3192624b2d1129423a5c6a539cf052b5`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/agent_outputs/source_contract.json` (`81f0f614d32ecad5910df2533a4940cfbe00fc95aa305b50eb88a9c212dd017e`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/decision.json` (`acffcbdafeaf971bca127bba11fd1c0847e80606e72ccb7321c1ddecb4be76db`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/agent_outputs/adjudicator.json` (`3025456eff60a9c9af18c6c1f9421d7be4d0ebde73e0cbf181457e53eddb6af6`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/agent_outputs/blind_translation.json` (`e104660039d3b031f903f515e8f7296fde48c853ca781817491cbf15b54902a9`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/agent_outputs/direct_judge.json` (`8eba7e89c400fdc521b17b82cbbb8b4a9f18019b1648440344a5821aadb01d0e`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/agent_outputs/paper_source_contract.json` (`cc856c94ce22bcb89d018b431db65cfb6c20d25df7bb6aaeb660c48c42f5c886`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/agent_outputs/roundtrip_judge.json` (`3d42a123faab7da7fb94e3706528e9e493c1bf3989a722611ec9157adfd3d770`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/agent_outputs/source_contract.json` (`cae96a861777731d67ac9ede8d9bc2817755f7ed2ee01592e13d0cfbd8f9dc70`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/decision.json` (`a9f3751fafb151aea9974a1e88cc94c4e6f0a4a2f7f5d6fb024c0462c5c601e1`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/inputs/blind_dependency_inventory.json` (`0f77a178b783d81dd3d4e10f286135cb7e3daa777bf968f3a643c7b985e240d7`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/inputs/blind_dossier.md` (`594676c557447428fa04d3999eb96b85169e0039cd6882467b539ffe7cb8fe48`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/inputs/blind_review_packet.md` (`594676c557447428fa04d3999eb96b85169e0039cd6882467b539ffe7cb8fe48`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/inputs/declaration_dossier.md` (`60a799365b1773519458d839c1ee04d267ddfb309acbea6ae400e8365e3a14e0`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/inputs/dependency_inventory.json` (`2749561c9343fb18101cd6f4dc1c9029ff9d100be9a6ee78b66f47ebd722ee4d`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/inputs/dependency_reuse_direct.json` (`acb3838c216564c282ba4e3e4487840de14d506f28f7b10501c4ffe625ca5064`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/inputs/direct_review_packet.md` (`4d621852b9a906d1bafa361b163ab305a87c034b648cac359603affbdbac66ad`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/inputs/paper_source_locator.json` (`29399d42dec8e4d771178436cda1303a77490d8820b032eb370ddffe5e202bd7`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/inputs/source_locator.json` (`d1ae628acc118c8d298e3add396694d62b669089f91e02000ae0d849f48bade6`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260821T232904Z/agent_outputs/adjudicator.json` (`5846938a59bd31bd2136cecb5de74d9d860f666e2e0f1a8c72f62270658eb0f4`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260821T232904Z/agent_outputs/blind_translation.json` (`0bd6e5ca9d407db6a7059d88640098aa305a3468c80df1c65ac0f20f805c6f4c`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260821T232904Z/agent_outputs/direct_judge.json` (`00fbbfd091f8311e375fab9bb8d0a3bf31dd0efc1ceb657330cbba658d82272d`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260821T232904Z/agent_outputs/roundtrip_judge.json` (`a11a107ed4394d1a3acdb124867d42cdbe04bfe1d89733a7d846f39bdd9819e6`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260821T232904Z/agent_outputs/source_contract.json` (`0aacd322891b6156deaab73e5155df812157665e0916cbbad007330470c048e9`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260821T232904Z/decision.json` (`ec2a8cf7775648da503ea6e74b2d9e57f06acabd26c5d0e462adfce849a1c2b5`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260821T232904Z/inputs/blind_dependency_inventory.json` (`b6bc214f974565af989b50884268797ea4e3dbde928ee63e3f3860c5f3c0cde9`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260821T232904Z/inputs/blind_dossier.md` (`6fe713ab7c72ecb9e9d96cfd28523943aac19a7dea1e011c6641c908ee9ed56e`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260821T232904Z/inputs/blind_review_packet.md` (`6fe713ab7c72ecb9e9d96cfd28523943aac19a7dea1e011c6641c908ee9ed56e`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260821T232904Z/inputs/declaration_dossier.md` (`3e8dc6ae9aa80638d51d67a6a5840d6e164eeae5a3cd002228c4900381513434`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260821T232904Z/inputs/dependency_inventory.json` (`d2d487d1aa68942f4fb13d4862bab45ad02feda6ecd70f4e1f197563478e40d9`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260821T232904Z/inputs/direct_review_packet.md` (`e3172064dd23626fc0f280a01ae29a21fc2f463c053dfcde702bf9cc29e57043`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260821T232904Z/inputs/source_locator.json` (`dc203ccec366dac29723aa263699667cf7ecd81e9f076407eea37d3d5e6531f8`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/inputs/blind_dependency_inventory.json` (`f2d7d97ed31fc536cd84d1b64e7c1c7fb6a2d1cdcf6b77c0832259c45a930c93`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/inputs/blind_dossier.md` (`10a8d521f62b1160edfdd78281ecefa832872c0a7f393d0ce0455974807d8a6d`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/inputs/blind_review_packet.md` (`10a8d521f62b1160edfdd78281ecefa832872c0a7f393d0ce0455974807d8a6d`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/inputs/declaration_dossier.md` (`4b85d00c9731dda68c557a780f854884b530c043a1f11a33b25fb483f252c80f`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/inputs/dependency_inventory.json` (`b31c84d0900d34eab4272b5c1862c1b4276bbdc7bdcfd8260c90606f8b2bb4db`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/inputs/direct_review_packet.md` (`1d8e110b368d53c16adee87f55951c4f40caad12503d632987f7a76ad729fac1`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/inputs/source_locator.json` (`dc203ccec366dac29723aa263699667cf7ecd81e9f076407eea37d3d5e6531f8`)
