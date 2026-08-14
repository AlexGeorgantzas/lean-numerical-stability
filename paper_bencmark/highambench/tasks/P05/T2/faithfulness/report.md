# Faithfulness audit: P05-T2

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `429892a33ec0d2a62b6d40e3e4ca373ffe338533fe8d951823a298b483395182`
- Paper SHA-256: `dd8b525c0eabc509a68b325ee5008cf6f1d4ef262bef8ba54e1947fe3cdb3db6`

## Decision

The paper explicitly licenses Doolittle as sufficient for the intended Gaussian-elimination analysis, so the algorithm-name disagreement is resolvable. The formal run nevertheless assumes the local residual estimates that the paper derives, preventing Lean from recovering the paper theorem from its stated hypotheses. Conversely, the formal format admits nonpaper, non-symmetric representable systems with arbitrary safe-range semantics, so the paper does not cover every Lean run. Because the target combines reduced applicability with a nonvacuous source-external domain, neither implication holds and the correct classification is not-faithful-different.

## Implications

- **Lean implies paper:** `no`. Lean applies only to certificate-bearing P05DoolittleRun objects. Constructing such an object from the paper's hypotheses already requires the local residual estimates that the paper derives through Lemma 4.1. The proposition therefore does not establish the paper theorem from completion and absence of underflow and overflow.
- **Paper implies lean:** `no`. Lean universally quantifies over abstract formats whose representable sets and safeRange predicates may fall outside the paper's symmetric base-beta floating-point model. The paper makes no claim over those nonpaper runs. Their stored residual certificates make the Lean conclusion assumption-driven but do not supply source-domain coverage.

## Findings

- **critical / assumption-leakage:** The central floating-point analysis is a prerequisite of the formal run rather than a consequence of the paper's execution hypotheses.
- **major / abstract-numerical-domain:** Lean makes a nonvacuous universal claim about certified runs outside the paper's domain, so the paper does not imply Lean.
- **major / execution-model-linkage:** Doolittle itself is an appropriate algorithmic representative, but the formal execution object is substantially stronger than a completing exception-free execution.
- **note / surface-formulas:** The rejection is caused by hidden premise and numerical-domain semantics, not by constants, indexing, matrix operators, or the backward-error conclusion.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `fail` | `pass` |
| `S04` | `fail` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `fail` | `fail` |
| `S07` | `pass` | `pass` |
| `S08` | `fail` | `unclear` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `fail` | `fail` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `128` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `128` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D013, D014, D017, D018, D019, D022, D023, D025, D032, D034`.

## Remaining uncertainties

- The PDF does not enumerate the exact outer boundary of "any variant of Gaussian elimination," especially pivoted formulations with permutation matrices. This does not affect the classification because the PDF explicitly authorizes Doolittle for its intended unpermuted LU analysis, while the decisive mismatches are the residual certificates and abstract numerical model.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/agent_outputs/adjudicator.json` (`4f65f5233d767feed87278a5de82706ea0a7c9235150f0f1f1ea0a3fe7a99d2e`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/agent_outputs/blind_translation.json` (`61ef2692b2f2d08e242053b56cab9409355c1257620a14b7628b52f2de03bfe3`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/agent_outputs/direct_judge.json` (`6bab140ca101e1898b6d55a6826d23789c31ed873c1ffe9a25a21f7c7776f653`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`94d8d0609a4adaddee8d75b004da6abaaa4be95764e221645bed0febc7af5c12`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/agent_outputs/source_contract.json` (`0d2c8bf046d1dc30558903c298899e2e50885e73d5ec83ae585beb8d866cfa12`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/decision.json` (`aabf832c0a45d784a5f98c6ce32010a84221374f56449ed285b3c0e6c5bf1ff4`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/agent_outputs/blind_translation.json` (`36fa2ad1734a9feea8493c522b1daa289e652077460a92100b12fff0c6a26383`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/agent_outputs/direct_judge.json` (`8e2dfc0a93151547e3c42f974b4b6af6553d13ed26d2c4b6390435d95045e939`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/agent_outputs/paper_source_contract.json` (`90bcb3f32112e46567a1fde6c0c742ef1d157d1829c1eb2b2cb5ebb4d58d4c1d`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/agent_outputs/roundtrip_judge.json` (`4e81ded2b048c61b2114e49b98832b3b851402ee75492b3158027f8052dc8531`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/agent_outputs/source_contract.json` (`e2e2fd479d2d1c03cabe0f8baef74c7bd8c9da70a251d4a3093a17877090f718`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/decision.json` (`7997e5e5958e59ea1afd99867c7becc8264f1c83af8cfb21141d0516c2dc6ba5`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/inputs/blind_dependency_inventory.json` (`c56549ba28c0a6dc92dc0edf5d686405ed884820822811e6a5adfd3ec01f7937`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/inputs/blind_dossier.md` (`2000282daaa2678d82e662c5f674a4e653a2b8587cd8bae85039f503d083f00e`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/inputs/blind_review_packet.md` (`2000282daaa2678d82e662c5f674a4e653a2b8587cd8bae85039f503d083f00e`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/inputs/declaration_dossier.md` (`f0232a3af8da7802bb6b66afc07fd0779ee87c762c41571c1d999615ea10af8b`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/inputs/dependency_inventory.json` (`c13980e3175f6606ab215fcb97d5a9d5a0bdce8dc5b5a3f268349f4403ceb810`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/inputs/dependency_reuse_direct.json` (`1b65ef5194934195e90c3d73c982f7127d2a4ac67aa9bbbd5f84c5d5123afb9d`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/inputs/direct_review_packet.md` (`f6d7622f8a53de126a8ab2a435148c8f81cd2a30c3989d70ac37b0069d129121`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/inputs/paper_source_locator.json` (`417f8e6a6ff934c35d3c2379d9faefe1c21d44b1f14a69f7674c0ef303123327`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/history/20260814T193105Z/inputs/source_locator.json` (`9fb63ab1035cdbe5b25034bf13d2341b0813504a3fb962b5ac3a1801f93c4fd3`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/inputs/blind_dependency_inventory.json` (`6ea3b72da834eb0ccd1ddf3206f8ef037c87fbf8d33681afe6a3e574a5f23ce3`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/inputs/blind_dossier.md` (`1f736ce5e0ea214f9f06802949e3b1820d5b713f544cadc83bfd7b12690fc3bf`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/inputs/blind_review_packet.md` (`1f736ce5e0ea214f9f06802949e3b1820d5b713f544cadc83bfd7b12690fc3bf`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/inputs/declaration_dossier.md` (`6b14d0f97ee4c68d675fcb5cf33b9a5866cd7827df015f9c2b13110bcc5c2a10`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/inputs/dependency_inventory.json` (`cd658e6379f43db6070f2be533c925334ed64d1efeae1cec678b9fe84606ccd4`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/inputs/direct_review_packet.md` (`969325ea2447cafdd902d1197a52d7eb950e038a62f07ed37a8a69b998427d5f`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/inputs/source_locator.json` (`40669d19b199673463bcdaf61468d8a1461f341bcdc7c10e62c3da90f0d46c08`)
