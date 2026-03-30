-- Benchmark/README.lean
/-!
# LLM Benchmark: Does a Verified FP Stability Library Help LLMs Prove New Results?

30 files total: 10 tasks × 3 experimental conditions.

## Research question

Does access to a reusable, machine-checkable stability library (LeanFpAnalysis)
enable LLMs to prove FP stability results they otherwise cannot?

## Experimental conditions (directories)

| Condition | Directory | What the LLM receives |
|---|---|---|
| **A: Bare** | `ConditionA/` | Natural language theorem + Mathlib imports only. Must invent FP model, gamma calculus, all intermediate lemmas. |
| **B: Axioms only** | `ConditionB/` | `FPModel` structure + `gamma`/`gammaValid` definitions (~30 lines). Must build all intermediate lemmas (dot product bounds, backward error, etc.). |
| **C: Full library** | `ConditionC/` | Full library imports + algorithm definitions + theorem statement. Must only fill in the proof (`sorry`). |

The gap A→C measures the library's total value.
The gap B→C isolates the value of the *intermediate lemma layer*.

## Tasks (10 tasks, 3 difficulty tiers)

### Tier 1: Direct application
- **T01** `SymmetricMatVec` — Symmetric matvec backward error with symmetric ΔA (§3.5)
- **T02** `UnitTriangularForwardSub` — Unit triangular forward sub, zero-diagonal ΔL (§8.1)
- **T03** `NormwiseMatVecBound` — Normwise ‖fl(Ax)−Ax‖∞ ≤ γ(n)‖|A|·|x|‖∞ (§3.5)

### Tier 2: Composition (chain 2–3 results)
- **T04** `PLUSolve` — PLU solve with row permutation (§9.3–9.4)
- **T05** `TwoStepRefinement` — Two-step iterative refinement identity (§11.2)
- **T06** `LDLtSolve` — LDLᵀ solve: forward sub + diag + back sub (§10.4)

### Tier 3: Novel reasoning (new defs + gamma calculus composition)
- **T07** `ScaledMatVec` — y = αAx, gamma_mul composition (§3.5)
- **T08** `GEMV` — Full BLAS Level 2: y = αAx + βy₀ (§3.5)
- **T09** `BlockTriangularSolve` — 2×2 block back-substitution (§12.1)
- **T10** `StationaryInexactSolve` — Stationary iteration + concrete triangular solve error (§16 + §8.5)

## Metrics
- **pass@1, pass@5**: fraction of attempts that compile with 0 `sorry`
- **sorry count**: remaining `sorry`'s in best attempt
- **human edits**: lines changed by human to complete the proof
- **proof validity**: `lake build` succeeds
- **lines of code**: total LoC in LLM's response (measures effort)

## Expected results (hypothesis)

| | Condition A (Bare) | Condition B (Axioms) | Condition C (Library) |
|---|---|---|---|
| **Tier 1** | Fail (must reinvent too much) | Partial (some may succeed) | Pass reliably |
| **Tier 2** | Fail | Fail (must chain non-existent lemmas) | Some pass |
| **Tier 3** | Fail | Fail | Struggle, partial |

## Models to evaluate
- Claude Opus, Claude Sonnet
- GPT-4o, o3
- (Optional) Gemini 2.5 Pro, DeepSeek

## Future expansion (when §18–§23 are formalized)
- QR factorization backward error composition (§18)
- Householder QR vs. modified Gram-Schmidt comparison (§18–§19)
- Least squares via QR backward stability (§19)
- Underdetermined system minimum-norm solution (§20)
- Vandermonde system stability (§21)
- Strassen-style fast matrix multiply error (§22)
-/
