# W05 integrator requests

W05 did not edit any path listed below.  Each path is integrator-owned or is a
later W06 owner.  The requests are ordered so the accepted worker tree can be
made discoverable without broadening B0005.

## 1. Create the reusable family umbrellas

Create the five exact category umbrellas with these single imports:

```lean
-- NumStability/Algorithms/MatrixEquations/Sylvester/Equation.lean
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.All

-- NumStability/Algorithms/MatrixEquations/Sylvester/BackwardError.lean
import NumStability.Algorithms.MatrixEquations.Sylvester.BackwardError.All

-- NumStability/Algorithms/MatrixEquations/Sylvester/Conditioning.lean
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.All

-- NumStability/Algorithms/MatrixEquations/Sylvester/Perturbation.lean
import NumStability.Algorithms.MatrixEquations.Sylvester.Perturbation.All

-- NumStability/Algorithms/MatrixEquations/Sylvester/GeneralizedEquations.lean
import NumStability.Algorithms.MatrixEquations.Sylvester.GeneralizedEquations.All
```

Create the family and parent umbrellas:

```lean
-- NumStability/Algorithms/MatrixEquations/Sylvester.lean
import NumStability.Algorithms.MatrixEquations.Sylvester.BackwardError
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation
import NumStability.Algorithms.MatrixEquations.Sylvester.GeneralizedEquations
import NumStability.Algorithms.MatrixEquations.Sylvester.Perturbation

-- NumStability/Algorithms/MatrixEquations.lean
import NumStability.Algorithms.MatrixEquations.Sylvester
```

Add `import NumStability.Algorithms.MatrixEquations` to
`NumStability/Algorithms.lean`.

Create the analysis umbrellas:

```lean
-- NumStability/Analysis/LinearOperators/Schur.lean
import NumStability.Analysis.LinearOperators.Schur.All

-- NumStability/Analysis/SingularValues/InverseBounds.lean
import NumStability.Analysis.SingularValues.InverseBounds.All
```

Add the Schur import to `NumStability/Analysis/LinearOperators.lean`, the
inverse-bounds import to `NumStability/Analysis/SingularValues.lean`, and
ensure `NumStability/Analysis.lean` reaches both parents.

## 2. Extend the historical Sylvester discovery aggregate

Retain every existing import in `NumStability/Algorithms/Sylvester.lean` and
append the five reusable `...Sylvester.<Category>.All` imports above.  Also
append the following exact source entry points so this explicitly mixed
legacy aggregate keeps complete discovery coverage:

```lean
import NumStability.Source.Higham.Chapter16.Section01.SylvesterEquation.All
import NumStability.Source.Higham.Chapter16.Section02.RealSchurDecomposition.All
import NumStability.Source.Higham.Chapter16.Section02.SylvesterAndLyapunovBackwardError.All
import NumStability.Source.Higham.Chapter16.Section03.PerturbationAndConditioning.All
import NumStability.Source.Higham.Chapter16.Section04.PracticalErrorBounds.All
import NumStability.Source.Higham.Chapter16.Section05.GeneralizedMatrixEquations.All
```

Do not remove the six W05 historical imports.  In particular, `Higham16`
must remain reachable because its private reverse closure is declaration-
bearing and is consumed by W06.

## 3. Create Chapter 16 and Chapter 18 source umbrellas

Create these exact section umbrellas:

```lean
-- NumStability/Source/Higham/Chapter16/Section01.lean
import NumStability.Source.Higham.Chapter16.Section01.SylvesterEquation.All

-- NumStability/Source/Higham/Chapter16/Section02.lean
import NumStability.Source.Higham.Chapter16.Section02.RealSchurDecomposition.All
import NumStability.Source.Higham.Chapter16.Section02.SylvesterAndLyapunovBackwardError.All

-- NumStability/Source/Higham/Chapter16/Section03.lean
import NumStability.Source.Higham.Chapter16.Section03.PerturbationAndConditioning.All

-- NumStability/Source/Higham/Chapter16/Section04.lean
import NumStability.Source.Higham.Chapter16.Section04.PracticalErrorBounds.All

-- NumStability/Source/Higham/Chapter16/Section05.lean
import NumStability.Source.Higham.Chapter16.Section05.GeneralizedMatrixEquations.All

-- NumStability/Source/Higham/Chapter18/Section01.lean
import NumStability.Source.Higham.Chapter18.Section01.SchurDecomposition.All
```

Create `Chapter16.lean` importing its five sections and `Chapter18.lean`
importing Section 01.  Add both chapters to `NumStability/Source/Higham.lean`,
then verify the existing `NumStability/Source.lean` chain reaches them.

## 4. Retarget the accepted W02 import-only consumer

`NumStability/Analysis/SemiconvergentExistenceFull.lean` has no typed edge to
the old owner; its import is discovery-only.  Apply exactly:

```diff
-import NumStability.Analysis.RealQuasiSchur
+import NumStability.Analysis.LinearOperators.Schur.Real.QuasiTriangular.API
```

This is the requested canonical-import retarget; W05 did not touch the
integrator-owned W02 file.

## 5. Preserve and later retarget W06 consumers

Do not edit W06 as part of W05 acceptance.  The thirteen direct W06-to-W05
imports and their eventual canonical actions are:

- Keep the historical `Higham16` import for
  `Higham16Minimizers`, `Higham16Spectrum`, and `Higham16VecNorm`; each uses
  declarations pinned by the private closure.
- Defer reviewed retargets for `Higham16Eq9Assembly`,
  `Higham16NormEstimator`, and `Higham16VecPermutationNotes`, which currently
  import `Higham16` but do not require its private closure.
- Retarget `Higham16LyapunovSigmaMin`, `Higham16PerturbationSigmaMin`, and
  `Higham16PsiSigmaMin` from `Analysis.InverseOpNorm2` to
  `Algorithms.MatrixEquations.Sylvester.Conditioning.SingularValue` when W06
  owns those files.
- Retarget `Higham16Spectrum`'s reusable real-Schur use to
  `Analysis.LinearOperators.Schur.Real.QuasiTriangular.API` while retaining
  its separate historical `Higham16` need.
- Retarget `Analysis.MatrixPowersSchur` and
  `Analysis.SylvesterSchurExistence` to
  `Analysis.LinearOperators.Schur.Complex.Triangulation`.
- Drop the typed-unused old Schur import from
  `Analysis.MatrixPowersHenrici`, or retarget it if its W06 implementation
  subsequently acquires a real dependency.

P0006 preserves all 8,161 typed W06-to-W05 declaration edges.  These later
import changes are navigation cleanup, not permission to change interfaces.

## 6. Test and manifest integration

Create the integrator-owned `NumStabilityTest/Reorganization/W05.lean`
aggregate importing all 92 modules listed in `TEST_MATRIX.tsv`, and import it
from `NumStabilityTest.lean`.

Add all W05 canonical production modules to the correct entries in
`docs/architecture/tiers.json`; remove superseded layout debts for the ten
historical owners and register any temporary aggregate-only debt in
`docs/architecture/layout-exceptions.json`.  Update
`docs/architecture/COMPATIBILITY.md` with the one-to-many mappings in
`DECLARATION_ROUTES.tsv`.  Finally verify that `NumStability.lean`,
`NumStability/All.lean`, and the root semantic aggregates discover the new
families through the narrow umbrellas above.
