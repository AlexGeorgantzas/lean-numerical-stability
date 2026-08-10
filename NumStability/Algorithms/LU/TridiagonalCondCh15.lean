import NumStability.Algorithms.LU.TridiagonalCond
import NumStability.Source.Higham.Chapter15.Theorem07.TridiagonalLU.Basic
import NumStability.Source.Higham.Chapter15.Theorem08.TridiagonalDiagonalDominance.Basic
import NumStability.Source.Higham.Chapter15.Theorem09.Ikebe.Basic

/-!
# TridiagonalCondCh15 (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.LU.TridiagonalCondCh15`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/
