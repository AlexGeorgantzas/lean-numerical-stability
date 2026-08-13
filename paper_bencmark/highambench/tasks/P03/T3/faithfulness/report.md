# Faithfulness audit: P03-T3

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `false`
- Target SHA-256: `93c283a03101e253e657795229736e82264cbf585f42aabc9a69d40bbcc58d96`
- Paper SHA-256: `952c6827db21fb2a9362b5aa4d38a1b2c75361f2cc7a3badbb7cd4a232d7b7bc`

## Decision

The authoritative PDF confirms that Theorem 5.1's exact recurrence uses M1Z1|A^-1| in both W_i and y_i. Writing P=Z1|A^-1|, the paper derives c<=Pc+Pq and then c<=M1Pq. Lean instead assumes c<=Pc+q and concludes c<=M1q, while omitting the algorithm, uniform iteration scope, floating-point assumptions, and definitions of all data vectors. The formal proposition is nonvacuous and its primitive real and matrix operations are interpreted correctly, but it is a different generic lemma. Neither full statement semantically implies the other under their stated binders and hypotheses.

## Implications

- **Lean implies paper:** `no`. With n=1, M1=1, P=0, us=u=gammaR=0, oldResidual=correction=newResidual=1, and data=update=0, all Lean hypotheses hold and the Lean conclusion is 1<=1. The paper-shaped recurrence with the required M1P coefficient would instead require 1<=0. This formal model is possible precisely because the target lacks the paper's algorithmic linkage and P factor.
- **Paper implies lean:** `no`. The paper proves a statement only for Algorithm 1.1 quantities and derives correction <= P correction + Pq before obtaining M1Pq. Lean universally covers arbitrary matrices and vectors under the different premise correction <= P correction + q. Although the paper's final right-hand side is smaller than the Lean right-hand side under the intended nonnegative substitution, that isolated inequality comparison does not entail Lean's broader, differently premised proposition.

## Findings

- **critical / missing-resolvent-factor:** The target does not state the paper's recurrence. Under the intended P=Z1|A^-1| substitution it generally gives a looser bound, and outside that substitution it has no fixed strength relation.
- **major / altered-correction-premise:** The paper assumptions do not establish the Lean premise in general, and resolving this altered premise yields M1q instead of the required M1Pq.
- **major / algorithm-linkage-and-hypotheses:** The formal result measures a generic resolvent manipulation, not the claimed finite-precision iterative-refinement theorem.
- **major / iteration-scope:** The uniform theorem over algorithm iterations is reduced to an unlabelled single-step assertion without an explicit specialization contract.
- **major / unconstrained-placeholders:** The intended interpretation cannot be recovered from the proposition, and strength comparisons valid for the paper's nonnegative quantities need not hold on Lean's full domain.
- **critical / exact-recurrence:** The central noncommutative factor is omitted, so the translated bound is not Theorem 5.1's recurrence.
- **critical / algorithm-linkage:** The proposition proves only an abstract elimination lemma, not a result about iterative refinement.
- **major / hypotheses-and-numerical-model:** The source's floating-point assumptions and sufficient convergence condition cannot be recovered.
- **major / correction-inequality:** The hypotheses are not source consequences under the natural variable identification, preventing either semantic implication.
- **major / exact-versus-computed:** The translation loses a central distinction in the finite-precision analysis.
- **note / higher-order-treatment:** No approximate statement is falsely strengthened to an exact one; this does not repair the other semantic mismatches.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `fail` | `fail` |
| `S07` | `fail` | `fail` |
| `S08` | `fail` | `fail` |
| `S09` | `fail` | `fail` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `fail` | `fail` |
| `S14` | `pass` | `pass` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `fail` |

## Dependency coverage

- Blind translator covered `31` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `31` dependencies (`18` hash-reused interpretations); failing or unclear: `D001`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/agent_outputs/blind_translation.json` (`08b50e6c847c83f0fce1bffba6f46baecb673551e64c5a963a8d5bec7998d440`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/agent_outputs/direct_judge.json` (`7d3f07890543e5c9fda7109a1bc4223d41877e03efcdab3916f9e2374007050e`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/agent_outputs/paper_source_contract.json` (`cc0f2d27697c7df47ddee702a54285359037d701ffa45ec71a92ca67f9cf3902`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`48126638f9aa05fab979a13e162306bcdcaf7647da0e552539fbb7dafb0cdced`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/agent_outputs/source_contract.json` (`7933032dc0a3d5f1fc45dfb3e4929f648721d76081fe39d63e17ce18d1c91fd5`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/decision.json` (`d58585bc427ad3a439afe08e53998387d065d2e9a0e5a323341be1a5763adb1e`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/inputs/blind_dependency_inventory.json` (`1175e5bede39281fdd034b44dd127f9344547de3eec9363450133aaf500a9f4f`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/inputs/blind_dossier.md` (`f65c7799cf5deaba0f4b3a4f91c5c26548a6447e18d4e7a8956425ee7b5b5375`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/inputs/blind_review_packet.md` (`f65c7799cf5deaba0f4b3a4f91c5c26548a6447e18d4e7a8956425ee7b5b5375`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/inputs/declaration_dossier.md` (`e0a6e87d157d45146c6d4e4f0081ea2901cf732091e7b1ae07f12efca1ee7b66`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/inputs/dependency_inventory.json` (`9cdc9beb61e6936708b2647c847d09bae843bd339bd9420ce881c38f471ec933`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/inputs/dependency_reuse_direct.json` (`db6af2afac4a6b35b33d3997f89d8282465ba57db5baa1cad99cabf406d5740f`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/inputs/direct_review_packet.md` (`db9f8a5f225bf9a670778a9b2d9d796c127d3521ba99660aaf35baaadfa778e8`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/inputs/paper_source_locator.json` (`d325b31e2cf1ecac253237196c87cfb8e169960305af1f36083a03802a8829df`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/inputs/source_locator.json` (`b31e761652558dc922a68a035298fc1b28b7dde246480a15f6c278f9b531100b`)
