import NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.ExactTransforms.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.RowNorm.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.UniformRows.Core
import NumStability.Analysis.FiniteProbability
import NumStability.Analysis.MatrixAlgebra

/-!
# NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.ExactTransforms.UniformRowComposition

W11 canonical reusable randomized linear algebra destination. Whole commands are copied unchanged from `NumStability.Algorithms.RandNLA.UniformRowSamplingComposition`; the historical path re-exports this module.
-/

-- Algorithms/RandNLA/UniformRowSamplingComposition.lean
--
-- Product-law composition for Algorithm 3 signed-Hadamard preprocessing
-- followed by iid uniform row sampling.
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602




namespace NumStability

open scoped BigOperators

/-!
## Joint signed-preprocessing and uniform-row sampling law

The preceding files prove two separate probability statements:

* a Rademacher/sign event that makes leverage probabilities small after a flat
  signed-Hadamard preprocessing step;
* a uniform-row trace-MGF theorem for a fixed preconditioned matrix satisfying
  the resulting deterministic one-step row bounds.

This file puts both stages on one product probability space and composes the
events.  It still does not add the floating-point uniform-sketch transfer.
-/

/-- Product law for Algorithm 3 signed-Hadamard preprocessing followed by `s`
iid uniform row samples. -/
noncomputable def signedHadamardUniformRowTraceProbability {m s : ℕ}
    (hm : 0 < m) :
    FiniteProbability (RademacherTrace m × RowTrace m s) :=
  (rademacherTraceProbability m).prod
    (uniformRowTraceProbability (m := m) (steps := s) hm)

/-- Product law for exact finite signed-mixing preprocessing followed by `s`
iid exact uniform row samples. -/
noncomputable def signedMixingUniformRowTraceProbability {r m s : ℕ}
    (hr : 0 < r) :
    FiniteProbability (RademacherTrace m × RowTrace r s) :=
  (rademacherTraceProbability m).prod
    (uniformRowTraceProbability (m := r) (steps := s) hr)

/-- The exact two-sided uniform-row sample-Gram event after finite
signed-mixing preprocessing. -/
def signedMixingUniformRowSampleGramTwoSidedEvent {r m n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ) (ε : ℝ) :
    Set (RademacherTrace m × RowTrace r s) :=
  {x |
    let V : Fin r → Fin n → ℝ :=
      preconditionRows
        (signedMixingRows G (rademacherSignVector x.1)) U
    finiteLoewnerLe
      (fun j k : Fin n =>
        uniformRowSampleGram V x.2 j k - finiteIdMatrix j k)
      (fun j k : Fin n => ε * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n =>
        -(uniformRowSampleGram V x.2 j k - finiteIdMatrix j k))
      (fun j k : Fin n => ε * finiteIdMatrix j k)}












































































































































/-- Product law for exact CountSketch preprocessing followed by `s` iid
uniform row samples from the `r` CountSketch output rows. -/
noncomputable def countSketchUniformRowTraceProbability {r m s : ℕ}
    (hr : 0 < r) :
    FiniteProbability
      ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
  (countSketchProbability (r := r) (m := m) hr).prod
    (uniformRowTraceProbability (m := r) (steps := s) hr)

/-- The exact two-sided uniform-row sample-Gram event after collision-free
CountSketch preprocessing. -/
def countSketchUniformRowSampleGramTwoSidedEvent {r m n s : ℕ}
    (U : Fin m → Fin n → ℝ) (ε : ℝ) :
    Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
  {x |
    let V : Fin r → Fin n → ℝ :=
      preconditionRows
        (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U
    finiteLoewnerLe
      (fun j k : Fin n =>
        uniformRowSampleGram V x.2 j k - finiteIdMatrix j k)
      (fun j k : Fin n => ε * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n =>
        -(uniformRowSampleGram V x.2 j k - finiteIdMatrix j k))
      (fun j k : Fin n => ε * finiteIdMatrix j k)}








































































































































/-- The exact two-sided uniform-row sample-Gram event after signed-Hadamard
preprocessing. -/
def signedHadamardUniformRowSampleGramTwoSidedEvent {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ) (ε : ℝ) :
    Set (RademacherTrace m × RowTrace m s) :=
  {x |
    let V : Fin m → Fin n → ℝ :=
      preconditionRows
        (matMul m H (diagMatrix (rademacherSignVector x.1))) U
    finiteLoewnerLe
      (fun j k : Fin n =>
        uniformRowSampleGram V x.2 j k - finiteIdMatrix j k)
      (fun j k : Fin n => ε * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n =>
        -(uniformRowSampleGram V x.2 j k - finiteIdMatrix j k))
      (fun j k : Fin n => ε * finiteIdMatrix j k)}




























































































































































































































































































































end NumStability
