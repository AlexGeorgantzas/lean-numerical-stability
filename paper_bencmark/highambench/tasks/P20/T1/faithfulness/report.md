# Faithfulness audit: P20-T1

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `0a5acf0a1d8a55fcd041ea703d68d64c8c1f68aca5fe2b4b010c2d975523d0fd`
- Paper SHA-256: `ad830de20a73ff77b6e457921892b3250ba9ff70f487501979ee3f1c5f3f31e2`

## Decision

Primary PDF evidence confirms that P20-T1 is the A-row component of the scaling scheme: theta is fixed by (3.2), lambda is an unrestricted power of two satisfying (3.4a), and the exact scaled row lies in (theta/2,theta] before conversion. The declaration's unfolded definitions reproduce those quantities, dependencies, endpoint conventions, norm semantics, and diagonal Lambda A construction exactly, while correctly excluding zero rows. The missing B/M and rounded-computation objects therefore reflect the selected row specialization, not a semantic substitution. The material difference is that the paper's fmax and Fmax are maxima of Model 1 formats, whereas the theorem ranges over all positive real values. That extension is satisfiable and preserves the paper instance, so Lean implies the selected paper claim but not conversely. The result is faithful-stronger and accepted.

## Implications

- **Lean implies paper:** `yes`. Instantiate the declaration with the input and accumulation maxima of Model 1 and any matrix whose applicable rows are nonzero. After unfolding D001-D009, it supplies a positive integer power-of-two row factor satisfying exactly (3.4a), constructs the corresponding diagonal Lambda A, and proves the equivalent exact scaled-row interval. This implies the selected P20-T1 paper contract; it does not purport to imply the full rounded matrix-product analysis.
- **Paper implies lean:** `no`. The paper states the row prescription for fmax and Fmax arising from specified floating-point formats and within its MMA setting. It does not quantify the same result over every pair of arbitrary positive real bounds, as the declaration does. The rowwise Skolemization itself is harmless, but the broader parameter domain prevents the reverse implication.

## Findings

- **minor / format-domain-generalization:** The declaration proves the same range construction on a strictly broader, satisfiable domain; this changes equivalence to genuine faithful strength.
- **note / row-local-specialization:** Omission of q, B, M, y, and mu does not alter the selected P20-T1 row contract.
- **note / pre-conversion-scope:** The theorem supports exact pre-conversion range placement only and must not be used as a rounded-MMA or no-underflow theorem.
- **note / zero-row-domain:** The formal hypothesis resolves an implicit source-domain requirement and preserves nonvacuity.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `pass` | `pass` |
| `S04` | `pass` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `pass` | `fail` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `not-applicable` |
| `S14` | `pass` | `not-applicable` |
| `S15` | `pass` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `85` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `85` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/agent_outputs/adjudicator.json` (`0695ba2e9b79d656c0c57d255d12c42c039c9ed68409f6332e89c3620f15a3e7`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/agent_outputs/blind_translation.json` (`e41fa2f6659fcefbac879c6ea4af88d4a4d588a113ff4fd908b84229a6f2f16f`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/agent_outputs/direct_judge.json` (`7aa3e58ffe10ea5bd49d4c2ba1efadbd1462bb27403fbc9dc5996e8055190e02`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`9a3e830a48d478bd5285a4ae768395bb686dbcb7fb0fc949938fcf4f3f336ab0`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/agent_outputs/source_contract.json` (`eec799394042b0f2efc4d6e7cd963686997fb44dc3f09421f04b417ff7d6f742`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/decision.json` (`2a68b0e39a425bb16349e675ffc0434b0870f638f91200fc9fdce01640655c4f`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/history/20260821T043420Z/agent_outputs/adjudicator.json` (`9e429b6a54431e73f309283d27335e49fc1333a1b2acf53d1d870fc006c3f941`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/history/20260821T043420Z/agent_outputs/blind_translation.json` (`f0a2e3f893b82cdf46375fbe4023707ebd031405f7ffb39b214770880066e36d`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/history/20260821T043420Z/agent_outputs/direct_judge.json` (`cf9058d4e2cc05724c0dbaf9c0f580b36a9b66bb5e1c896dc7632ad59dd76f73`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/history/20260821T043420Z/agent_outputs/paper_source_contract.json` (`a0c8bbaa2e261f7adc023b1698c08de77fd260aafddc9aa341073c2704530e40`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/history/20260821T043420Z/agent_outputs/roundtrip_judge.json` (`51584315b72708ced275c0a4d03ca6e90aca19e448325ba8035a1181008eae26`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/history/20260821T043420Z/agent_outputs/source_contract.json` (`f5253076f8203d022a69a7eabc0503053afcb8cfef361fbd9fce0546a1a95dd8`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/history/20260821T043420Z/decision.json` (`2bf82c5a8e2eb22ca7af49a3ca561236a76da036ae539f10d27a7729c3738378`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/history/20260821T043420Z/inputs/blind_dependency_inventory.json` (`0949e2ebcd9dfd0a9f039b6eb1b6bf88a2c1797efa9407d88570ce03c9b0f02d`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/history/20260821T043420Z/inputs/blind_dossier.md` (`d40ac8ca2ddd3459a169e2ec4ebd02a7ed9f2623c975bf7ec8392f5ad3dc9706`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/history/20260821T043420Z/inputs/blind_review_packet.md` (`d40ac8ca2ddd3459a169e2ec4ebd02a7ed9f2623c975bf7ec8392f5ad3dc9706`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/history/20260821T043420Z/inputs/declaration_dossier.md` (`ee508e11f2305d5095c1869082697f3a31816dfa62d6814f65655b78db585976`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/history/20260821T043420Z/inputs/dependency_inventory.json` (`48eb9bac7af6c92db998f6a416b8b33ca2e7497644b4d3a4e7be4fc56246adcd`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/history/20260821T043420Z/inputs/direct_review_packet.md` (`16d509be04c4afaf6c760bc56a869f25375758bb81d574e163bdc747fe34e2df`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/history/20260821T043420Z/inputs/paper_source_locator.json` (`413757004ac4d15ac7e55e926e2486e54bdac2db1523d83303ddb4cbffe644f4`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/history/20260821T043420Z/inputs/source_locator.json` (`66da6a9c6ea70bdea0a7b29a4dde9639c4bd1d860675857f9063693dfa6d60c8`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/history/20260821T083452Z/agent_outputs/adjudicator.json` (`f1e9a6f9c0007e27576d27c3ec857b715a2fa3ec0cc3244d114498c40d6d8693`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/history/20260821T083452Z/agent_outputs/blind_translation.json` (`fe60576e17f0ece150a2dd3e239ac8c8d9285dcdc0a70bf432693d700809ca70`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/history/20260821T083452Z/agent_outputs/direct_judge.json` (`2a0717814331904d07c93c6c3e6c0d81dba42ea7c34aefb64954d4db23753105`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/history/20260821T083452Z/agent_outputs/roundtrip_judge.json` (`0d9df5c9f12d4459c7b769bc8f070e308a3cb9549d79b3c875d945a792488f8b`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/history/20260821T083452Z/agent_outputs/source_contract.json` (`75f47662da704842da5dc236c0cc8f559f86fbc2d4a53c8b6c2f15c9515e7b8a`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/history/20260821T083452Z/decision.json` (`10f3c5585c710a8f4b1aab359be664f754427b826ae609cf7ccfe072f5df11bb`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/history/20260821T083452Z/inputs/blind_dependency_inventory.json` (`3648b48d6fb4bc7f136c5e845c14c68a3b85998a35f0d2036d762a7466df0076`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/history/20260821T083452Z/inputs/blind_dossier.md` (`0ad61100ec7e78ce517a63107a391434139e065ad4acd587a7a988a38866031f`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/history/20260821T083452Z/inputs/blind_review_packet.md` (`0ad61100ec7e78ce517a63107a391434139e065ad4acd587a7a988a38866031f`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/history/20260821T083452Z/inputs/declaration_dossier.md` (`d9c689be10b00b14f516ff1507392593d98eacef4751fb40fa1413e27f54e096`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/history/20260821T083452Z/inputs/dependency_inventory.json` (`2ee2acb3d307c21be8bd63d258365dfe0e115ba758a5a47f738dc023569472cc`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/history/20260821T083452Z/inputs/direct_review_packet.md` (`61fe813b9dfc6db37c62b8afb05a4aa37450f28ec6d214e3e51adfa7510dc806`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/history/20260821T083452Z/inputs/source_locator.json` (`b655a6f42ec923ce23d5b02a51498be47a828284248d0baa560f08297f179910`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/inputs/blind_dependency_inventory.json` (`3648b48d6fb4bc7f136c5e845c14c68a3b85998a35f0d2036d762a7466df0076`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/inputs/blind_dossier.md` (`0ad61100ec7e78ce517a63107a391434139e065ad4acd587a7a988a38866031f`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/inputs/blind_review_packet.md` (`0ad61100ec7e78ce517a63107a391434139e065ad4acd587a7a988a38866031f`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/inputs/declaration_dossier.md` (`d9c689be10b00b14f516ff1507392593d98eacef4751fb40fa1413e27f54e096`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/inputs/dependency_inventory.json` (`2ee2acb3d307c21be8bd63d258365dfe0e115ba758a5a47f738dc023569472cc`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/inputs/direct_review_packet.md` (`61fe813b9dfc6db37c62b8afb05a4aa37450f28ec6d214e3e51adfa7510dc806`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/inputs/source_locator.json` (`b655a6f42ec923ce23d5b02a51498be47a828284248d0baa560f08297f179910`)
