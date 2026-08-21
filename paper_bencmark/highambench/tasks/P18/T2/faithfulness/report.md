# Faithfulness audit: P18-T2

- Classification: `faithful-equivalent`
- Accepted as paper-faithful: `true`
- Adjudicated: `false`
- Target SHA-256: `3a157ed5c3b2e49991471ea7564525d59d1bd378dd32747d519d26359e2a3fa1`
- Paper SHA-256: `b18628ffc348d7aeec2da02efb989b6e012f0b0fae09b27fbff735bb8a5877cd`

## Decision

The declaration and all dependencies encode exactly the two-stage p=2 corrected implicit-midpoint arrays from PDF p. 11. Its conjunction contains the complete order-two consistency certificate, all smooth perturbation conditions through m=2, and both nonsmooth componentwise-absolute conditions through m=2 from PDF pp. 7-8. The paper-explicit cancellation identities occur directly; the other conjuncts are exact consequences of substituting the printed arrays, and there are no unrelated claims. Both implication directions therefore hold for the selected algebraic result.

## Implications

- **Lean implies paper:** `yes`. After unfolding D006-D015, the Lean constants are exactly the three coefficient arrays and their combined arrays printed on PDF p. 11. The target directly includes the two p. 11 cancellation identities and all order-two consistency, smooth, and nonsmooth contractions from pp. 7-8. Its additional sum and row-sum conjuncts are exact consequences of the same arrays. It makes no unrelated global-error claim.
- **Paper implies lean:** `yes`. Substituting the paper's arrays gives A-tilde=A+A-epsilon, c-tilde=c+c-epsilon, b-tilde=b+b-epsilon, A e=c, and A-epsilon e=c-epsilon. Direct finite contractions then yield b-tilde e=1, b-tilde c-tilde=1/2, all four smooth zeros, and both componentwise-absolute nonsmooth zeros. Thus every Lean conjunct follows exactly.

## Findings

- **note / source-explicit-versus-derived:** The added conjuncts do not make the formalization logically stronger than the selected paper result because the displayed source arrays already imply each one.
- **note / scope-control:** The Lean theorem remains correctly scoped to the exact coefficient cancellation certificate and does not introduce an unsupported unconditional analytic claim.
- **note / explicit-versus-derived:** The extra conjuncts complete the selected certificate but do not strengthen it beyond what the paper's displayed arrays already imply.
- **note / scope-control:** The translation correctly remains within the locator's exact coefficient-certificate scope.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `pass` | `not-applicable` |
| `S04` | `pass` | `pass` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `pass` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `pass` | `not-applicable` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `pass` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `58` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `58` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/agent_outputs/blind_translation.json` (`f548a6fe2eac77509d7e40a21a6ad25bc0438ae93c2137a4ecd5671fb40f668a`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/agent_outputs/direct_judge.json` (`d139537be2671af1bc65658c6ebe575ba35cbe465c804224a4f22e6455669eca`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`aff9150c106860b4d1e1d07487ce532213ab23e45aaf578d312f9ec915bc2735`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/agent_outputs/source_contract.json` (`8e6c7e848d3d667d4cc9f4bb457f82f1701eebb9cb65c9a83db9d8df29cb48f2`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/decision.json` (`00f8fe2cbabe5830ed976ff44b674d1d6185fb9330598d4893ff860e7ee2ff2a`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/history/20260820T202648Z/agent_outputs/adjudicator.json` (`56159e26ef99045d071e312b79c863811b01dba8a03d9763234d7e4386602677`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/history/20260820T202648Z/agent_outputs/blind_translation.json` (`1eebad43ec9d5ea0ac6b487bd941564cb5a663c3a14f55f789e80bfd5f7412b4`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/history/20260820T202648Z/agent_outputs/direct_judge.json` (`3ad35386f880b095eac20d57d6aa9e2af853bfc7073ee86c6c361c7599a7af46`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/history/20260820T202648Z/agent_outputs/paper_source_contract.json` (`6de2cebc98667558bfb276c01a2286c46a88edff824491fda40799511abf8891`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/history/20260820T202648Z/agent_outputs/roundtrip_judge.json` (`817604d2424fc870ac317e480f7851516865d9d4e80ad91a15a23e00acefd389`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/history/20260820T202648Z/agent_outputs/source_contract.json` (`ddd7d68c331a25f5a20c9bdeb6bc46be6be140314bb6da08a1c7060256893f14`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/history/20260820T202648Z/decision.json` (`893204dcdc7fb89bedecaf7bc47593110d34c96922e02f86e4a1d548cf32de15`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/history/20260820T202648Z/inputs/blind_dependency_inventory.json` (`8d80b204e9589819269851852b1fc39d278fb5a8998c2c77f54fc3213729309d`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/history/20260820T202648Z/inputs/blind_dossier.md` (`e481dec0860548d72ab6710531ebdd290f51a62bde10f877ca2515aabcbacd2a`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/history/20260820T202648Z/inputs/blind_review_packet.md` (`e481dec0860548d72ab6710531ebdd290f51a62bde10f877ca2515aabcbacd2a`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/history/20260820T202648Z/inputs/declaration_dossier.md` (`7318322c14bff24bd9fcf1873634299118f2eabf139d40f765e2f7e4d9efa2d7`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/history/20260820T202648Z/inputs/dependency_inventory.json` (`9ff81ac0f0f1b0604922c2e0a3314eca1aaed1ecd0d8724fb16107397daa8532`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/history/20260820T202648Z/inputs/dependency_reuse_direct.json` (`ad044f09607371de6ed2daf6746d04101a044bd13d1fa62afac1e468796ce6a4`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/history/20260820T202648Z/inputs/direct_review_packet.md` (`a46954508d1f648f046baac0aeda4c3851f83c8497ca6f2e5fcdf36d5bbb9219`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/history/20260820T202648Z/inputs/paper_source_locator.json` (`ba129952837b9f0f76f04aaf15df9d09fbc4e140b4fac00813259e514dd1ea6e`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/history/20260820T202648Z/inputs/source_locator.json` (`d7f48453f74dd4d0901641bf3b21e3b4bf43b5a674d4e24862ae98f476012d47`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/inputs/blind_dependency_inventory.json` (`2f5a29721588852d434e989c0f07adfe0b58f90ac4a3228ba51846849c743fe3`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/inputs/blind_dossier.md` (`fc5d42d5c0d7fa6c6366bff1d680404b91a055e8a4942e437f3359d4f9b63901`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/inputs/blind_review_packet.md` (`fc5d42d5c0d7fa6c6366bff1d680404b91a055e8a4942e437f3359d4f9b63901`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/inputs/declaration_dossier.md` (`efeb04250a55f51faf140b53bf8d43d2be31542ac4406939359e28cce5ab2739`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/inputs/dependency_inventory.json` (`de3d18a2d5fbde0ba1a1d329a0f7e95dbee45f8068817497f22a7ec62d2aba99`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/inputs/direct_review_packet.md` (`3b94ed68ea22cba7562fbfdd13013773ee02bc21200b752a5d105d8309d76b00`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/inputs/source_locator.json` (`6e877828521760fde5eb3dfc6ac4d6b77d6e91aba97584241ce7668c9c17d407`)
