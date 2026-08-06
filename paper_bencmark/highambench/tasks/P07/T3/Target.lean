import HighamBench.P07Definitions

namespace HighamBench

/-- P07-T3: certificate form of Lemma 2.1. If `C*T = Q`, both `Q_A` and
`Q` are isometries, and `T` is onto, then the singular-value interval for
`Q_A*T` is reciprocal to that for `C`; their condition ratios agree. -/
theorem p07_t3_sketch_precondition_condition_certificate
    {m n s : ℕ}
    (QA : Fin m → Fin n → ℝ) (Q C : Fin s → Fin n → ℝ)
    (T : Fin n → Fin n → ℝ) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (hQA : p07Isometry QA) (hQ : p07Isometry Q)
    (hCT : p07RectMatMul C T = Q)
    (hTsurj : Function.Surjective (p07MatVec T)) :
    (p07ConditionCertificate (p07RectMatMul QA T) α β ↔
      p07ConditionCertificate C β⁻¹ α⁻¹) ∧
      β / α = α⁻¹ / β⁻¹ := by
  -- PROOF_START
  sorry

end HighamBench
