-- NumStability/Analysis/FloatingPointArithmetic.lean
--
-- Import-only compatibility wrapper retained by reorganization wave R03
-- (phase branch B0005, projection P0005). This historical path is preserved,
-- not deleted and not Git-renamed, so every existing `import` keeps resolving.
-- All of its declarations moved unchanged to the canonical module(s) below.

import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import NumStability.Analysis.Error.Measures.All
import NumStability.Analysis.FloatingPointArithmetic.ErrorModels.All
import NumStability.Analysis.FloatingPointArithmetic.ExactSubtraction
import NumStability.Analysis.FloatingPointArithmetic.Format
import NumStability.Analysis.FloatingPointArithmetic.IeeeExceptions
import NumStability.Analysis.FloatingPointArithmetic.IeeeOperations
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Analysis.FloatingPointArithmetic.IeeeValue
import NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError
import NumStability.Analysis.FloatingPointArithmetic.RoundToEvenLocalError
import NumStability.Analysis.FloatingPointArithmetic.Rounding
import NumStability.Analysis.FloatingPointArithmetic.StandardModel
import NumStability.Source.Higham.Chapter01.Problem01.RelativeError.All
import NumStability.Source.Higham.Chapter01.Section03.ErrorSources.All
import NumStability.Source.Higham.Chapter01.Section07.Cancellation.All
import NumStability.Source.Higham.Chapter02.FloatingPointArithmetic.AdditiveUnderflowModel
import NumStability.Source.Higham.Chapter02.FloatingPointArithmetic.Environment
import NumStability.Source.Higham.Chapter02.Section04.NoGuardModel.All

/-!
# FloatingPointArithmetic (compatibility wrapper)

Declaration-free import-only wrapper. Canonical module(s):

* `NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results`

Retained by wave R03 so historical imports continue to resolve unchanged.
-/
