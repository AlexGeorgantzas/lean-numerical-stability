import NumStability.Algorithms.QR.Higham19Thm6CoxHigham
import NumStability.Analysis.MatrixAlgebra

namespace NumStability

open scoped BigOperators

/-!
# TraceKernel

Canonical reusable module extracted without change from Higham20Theorem20_7.
-/

namespace Theorem20_7

/-- Append one matrix at the inner end of `applyProd`.

`applyProd P a len` is defined by recursion at the outer end; this companion
identity is what connects it to the right-growing `Qacc` trace. -/
theorem applyProd_snoc {m : ℕ} (P : ℕ → Fin m → Fin m → ℝ)
    (a len : ℕ) (x : Fin m → ℝ) :
    Wave19.applyProd P a (len + 1) x =
      Wave19.applyProd P a len (matMulVec m (P (a + len)) x) := by
  induction len generalizing a x with
  | zero => simp [Wave19.applyProd]
  | succ len ih =>
      calc
        Wave19.applyProd P a ((len + 1) + 1) x =
            matMulVec m (P a) (Wave19.applyProd P (a + 1) (len + 1) x) := rfl
        _ = matMulVec m (P a)
            (Wave19.applyProd P (a + 1) len
              (matMulVec m (P ((a + 1) + len)) x)) := by
              rw [ih]
        _ = matMulVec m (P a)
            (Wave19.applyProd P (a + 1) len
              (matMulVec m (P (a + (len + 1))) x)) := by
              rw [show (a + 1) + len = a + (len + 1) by omega]
        _ = Wave19.applyProd P a (len + 1)
            (matMulVec m (P (a + (len + 1))) x) := rfl

end Theorem20_7

end NumStability
