# Faithfulness audit: P01-T2

- Classification: `faithful-equivalent`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `8707d7e8b3965c9c6d5c1354116c7cf04471bc0c5b0635b4287729455f79e49f`
- Paper SHA-256: `d5ad99fac5022da54dbe02721ea57116df3cec15badddd7c96c344328718fea7`

## Decision

Primary inspection confirms that the declaration reproduces the exact power-of-two pairwise bound (3.6), the matching instance of recursive bound (2.6), and the source-supported non-strict comparison of their gamma coefficients. All disputed local definitions have the intended meanings: StandardAddModel is the addition part of (1.2), gamma is the exact finite coefficient, pairwiseSum is the adjacent-pair balanced tree, and recursiveSum is the fixed left fold with an exact singleton. The round-trip judgment mistook direct axiomatization of the relative-error model for a theorem about machine behavior outside that model. Since operations exhibiting model-violating underflow or guard-digit behavior are not StandardAddModel instances, no genuine broader exceptional-value claim exists. Both implication directions are therefore yes, requiring faithful-equivalent with accepted=true.

## Implications

- **Lean implies paper:** `yes`. For an underflow-free floating addition in the paper's standard regime, model (1.2), exact initial addition, and the implicit valid-gamma condition provide a StandardAddModel and the target premise. Unfolding the two Lean algorithms then gives the same power-of-two adjacent-pair computation and left-to-right computation, so the target yields (3.6), the n=2^r instance of (2.6), and only their non-strict coefficient comparison.
- **Paper implies lean:** `yes`. At the paper's stated algebraic abstraction, each StandardAddModel operation supplies exactly the bounded per-addition delta used in the derivations. Equation (3.6) supplies the pairwise conjunct, equation (2.6) instantiated at n=2^r supplies the recursive conjunct, and r<=2^r-1 together with u>=0 and positive denominators gives gamma_r<=gamma_(2^r-1). The source's underflow and guard-digit warnings exclude operations for which the model fails; they do not add another mathematical dependency after the model law is assumed.

## Findings

- **note / gamma-domain:** Lean states the intended validity domain needed by both exact gamma bounds; this is not an applicability defect.
- **note / floating-point abstraction:** The target remains an idealized model theorem and does not gain genuine coverage of model-violating underflow or no-guard arithmetic.
- **note / comparison-scope:** The formal theorem does not overstate coefficient superiority as an ordering of actual errors or all available bounds.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `pass` | `pass` |
| `S04` | `pass` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `pass` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `pass` | `fail` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `pass` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `76` dependencies; unclear: `none`.
- Direct judge covered `76` dependencies; failing or unclear: `none`.

## Remaining uncertainties

- The PDF does not formalize machine-level underflow, overflow, nonfinite values, or rounding modes as predicates, so this adjudication is limited to the algebraic model (1.2).
- The usual condition m*u<1 is not printed beside the finite-product display; its intended necessity is inferred from the denominator and from the bound's mathematical validity.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P01/T2/faithfulness/agent_outputs/adjudicator.json` (`e608cdc5e9cd9f0d5448801e5561005bd3f3f1c8a8ed4e26a5da4817fb9fe342`)
- `paper_bencmark/highambench/tasks/P01/T2/faithfulness/agent_outputs/blind_translation.json` (`7b3a319f63269151facb954bb4c0c5cc37218263f9ebbe57b0e03f8a3c6ec901`)
- `paper_bencmark/highambench/tasks/P01/T2/faithfulness/agent_outputs/direct_judge.json` (`4bb4caba375fa57601812839bff9ef7bb53b5d39d94ec56cf8cf20a75bd2e6aa`)
- `paper_bencmark/highambench/tasks/P01/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`5a9ccf533cf2a4000065164880073494c3381e986898653f1463ccc88539cf3a`)
- `paper_bencmark/highambench/tasks/P01/T2/faithfulness/agent_outputs/source_contract.json` (`0dda408cdc0751a55b836dac2f131266857aded24ee0e7e82b75da12036ea868`)
- `paper_bencmark/highambench/tasks/P01/T2/faithfulness/decision.json` (`17d23d00b0beca0426c0cc44379ba483d4c98f5a0a8d3993a60538b2a6044947`)
- `paper_bencmark/highambench/tasks/P01/T2/faithfulness/inputs/blind_dossier.md` (`14f2c51b532ef14475c45374db729456457f7bfb122cb4c92ac52b237510b1c8`)
- `paper_bencmark/highambench/tasks/P01/T2/faithfulness/inputs/declaration_dossier.md` (`687ba96a68c2afdb3c06ea76a03dce3c3541014c76cf39ab421aab793f0b555f`)
- `paper_bencmark/highambench/tasks/P01/T2/faithfulness/inputs/source_locator.json` (`793f2edaf390211973b93b054130d6c6f7494af24f3ef69b7b81f534d3df0b9a`)
