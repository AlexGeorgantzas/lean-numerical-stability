# Faithfulness audit: P09-T3

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `5f4cdf4d102e37290628347ea4ad52baa30f3afcbf86fbc81313e0499dae3f36`
- Paper SHA-256: `9076fe377cc64878a4a10f8a47ff49245bc5acaf116ffbd8e2ccca57033da758`

## Decision

The Lean declaration accurately reproduces many static ingredients of Theorem 2(a), but it changes the theorem's logical and numerical subject. The paper bounds an actual nested floating-point FFT and uses first-order expansions with an O(epsilon^2) remainder. Lean instead quantifies arbitrary exact-transform-plus-residual runs, repeats a telescoping premise as a conclusion, and assumes the decisive local and intermediate estimates through coefficients chosen after one fixed epsilon. Those coefficients can absorb arbitrary finite discrepancies, and the modeled arithmetic operations never generate the computation. Consequently Lean cannot imply the paper, while the paper does not entail Lean's universal claim over non-execution packages. The statements are therefore not-faithful-different; unresolved Fourier sign and common-gamma details are non-determinative.

## Implications

- **Lean implies paper:** `no`. Lean proves only a finite, certificate-relative propagation inequality for abstract residual decompositions. It provides neither actual nested floating-point FFT execution nor existence of epsilon-independent certificates over a small-epsilon family, so it cannot recover the paper's roundoff theorem or its O(epsilon^2) conclusion.
- **Paper implies lean:** `no`. The paper quantifies actual floating-point FFT computations, whereas Lean universally quantifies packaged runs and certificates whose premises do not imply such execution. The fact that Lean's conclusion follows from its own assumed telescoping and quantitative bounds does not make it a consequence of the paper for arbitrary non-execution packages.

## Findings

- **critical / algorithm-execution-unlinked:** The proposition is not about execution of the numerical algorithm studied in the paper.
- **critical / higher-order-quantifier-collapse:** Coefficients may scale as 1/epsilon or 1/epsilon^2, eliminating the paper's asymptotic leading-order content.
- **major / certificate-assumes-numerical-substance:** The target is an algebraic consequence of supplied bounds rather than a formalization of the roundoff theorem.
- **major / input-representation-condition-vacuous:** The premise neither excludes arbitrary input-representation error nor links represented input to the computed run.
- **major / domain-and-implication-mismatch:** The target is not simply the paper theorem under stronger hypotheses; the applicability classes are incomparable, so neither implication direction holds.
- **major / fourier-phase-unresolved:** The exact transform's sign cannot be certified from authorized evidence, although independent critical defects already determine rejection.
- **minor / redundant-telescoping-conclusion:** The extra conjunct supplies no nonvacuous strength and cannot support a faithful-stronger classification.
- **note / faithful-static-components:** These accurate static components do not repair the execution and quantifier failures.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `unclear` | `unclear` |
| `S07` | `fail` | `fail` |
| `S08` | `fail` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `unclear` | `unclear` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `fail` |
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `218` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `218` dependencies (`0` hash-reused interpretations); failing or unclear: `D004, D005, D006, D007, D010, D011, D015, D022, D023, D024, D025, D026, D027, D032, D043, D044, D048, D064, D069, D131, D148, D194`.

## Remaining uncertainties

- The exponential sign of ZMod.stdAddChar is not determined by the supplied D194 body. This uncertainty propagates separately to D010, D048, D064, D069, and S06.
- The paper displays one gamma across all axes but does not explicitly explain how it is selected when coordinate orders use different trigonometric computations. A common upper-bound reading is compatible with Lean.
- The paper does not quantify the constants, parameter dependence, or small-epsilon neighborhood hidden by its O notation. This omission does not justify witnesses chosen after one fixed epsilon.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/agent_outputs/adjudicator.json` (`8cc5bd9c424f7bce62b1b97d3e404a5ed362d71063ad449088b62fcb1d5c75cf`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/agent_outputs/blind_translation.json` (`ec70416b1f970279730b3b611c82f884512c14833fd254d3545a15d8bc23db03`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/agent_outputs/direct_judge.json` (`7e757fcdf7fb33314421856562247d5c490211081066293aee958e8922cd3a04`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`c58ab517eb5313d2ab65d0411230e566652840219a28b22919a61587da6bd653`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/agent_outputs/source_contract.json` (`05bbe4302da98c31949f76b1e7c51bf44c0fcec6a9f1b593b694be7837443245`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/decision.json` (`15d1c62953fc7d9e31025daca4cdbe59a43155a76b041747740f89747657a584`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/agent_outputs/blind_translation.json` (`a13dee089b0902650277ab595f3dd6019deccc8ca22efc166fd9b39b66d749ce`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/agent_outputs/direct_judge.json` (`a351fdf7f66a9e58b4e57f33f50a761bf0fb8ccc797816aba2a4fdbc11103929`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/agent_outputs/paper_source_contract.json` (`348db3c4cffe4770d8510e9fec47ccdab62bf40c19935e431854786ba7f44db4`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/agent_outputs/roundtrip_judge.json` (`de224336dcae540e54f98bd8b38ea3c19daa2d23dc9384c7534f80afbcdb2bc3`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/agent_outputs/source_contract.json` (`a0842a6fb4aa1e4a05e65a879405b31185241d2fdf518de57717b6c71f4059d9`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/decision.json` (`b10edff420dba69191a1207e72c5e464cccb337889770d6a5cbdb1a3a0e44d0d`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/inputs/blind_dependency_inventory.json` (`607c72b3224eedc6e3d6155183b494a1a4ba8ec5f9e6e3c1bf06b7d692ead238`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/inputs/blind_dossier.md` (`b9d6488561612d8cca4deb16990f43df2e0e89cd953a16403a63fa1bbc736dbc`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/inputs/blind_review_packet.md` (`b9d6488561612d8cca4deb16990f43df2e0e89cd953a16403a63fa1bbc736dbc`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/inputs/declaration_dossier.md` (`d9cbe66545e0f96392762a57802bb786c6d02214b9b31140ea5c7570abb1c90b`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/inputs/dependency_inventory.json` (`854f820cb042f0e08f49796f454492cd74109c201aaa57f896420a4bf49c979f`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/inputs/dependency_reuse_direct.json` (`d0fffa09c078ca35b0b7c80cca730983bd4e235ceeb4f871bf7e930ee8ff0ca6`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/inputs/direct_review_packet.md` (`2862d383d371da3e648a939a508f25d0b4ae69015a9a91d488f5b5a413811d64`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/inputs/paper_source_locator.json` (`f236078d56116000664fec27c570812daeb11eb5024aaf78838800ecc07f8a13`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/inputs/source_locator.json` (`b9c0b17cf2754d89c505af7c2ab51f4d30c7df14ab3f31a6fad0861ce6d98bcb`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/inputs/blind_dependency_inventory.json` (`3d6047c608bbb86a109e10234ba0d1a654fa5a2233f054a62e556db2489f916a`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/inputs/blind_dossier.md` (`15d0cd71a0097d60fa76b2554f222bec69acf82a3999c573a6e57058972c737f`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/inputs/blind_review_packet.md` (`15d0cd71a0097d60fa76b2554f222bec69acf82a3999c573a6e57058972c737f`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/inputs/declaration_dossier.md` (`27c786f4e984daafd9075621be641f4189bbc3f2c4f965571909a8e1aaee0851`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/inputs/dependency_inventory.json` (`c72f2a9cac1ac3941cbfe494ebdc8b49a8641401eda8d8ef27a8b316518c09ff`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/inputs/direct_review_packet.md` (`6d31d39c3e3459977d1c995625d0cf70178ac5810d4e29eb2562265b1a33b323`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/inputs/source_locator.json` (`c6220ad13dc28740adfe1b8026a25df6ba99b548d6f3d38a9c1784932f6e0c5f`)
