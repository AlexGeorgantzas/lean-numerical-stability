import NumStability.Algorithms.LinearSystems.LeastSquares
import NumStability.Algorithms.LinearSystems.LU
import NumStability.Algorithms.LinearSystems.QR.GivensMatrixStep
import NumStability.Algorithms.LinearSystems.QR.GivensQR
import NumStability.Algorithms.LinearSystems.QR.GivensSpec
import NumStability.Algorithms.LinearSystems.QR.GramSchmidt
import NumStability.Algorithms.LinearSystems.QR.GramSchmidtPolar
import NumStability.Algorithms.LinearSystems.QR.HouseholderConstruction2
import NumStability.Algorithms.LinearSystems.QR.HouseholderQApply
import NumStability.Algorithms.LinearSystems.QR.QRSolve
import NumStability.Algorithms.LinearSystems.SymmetricIndefinite
import NumStability.Algorithms.LinearSystems.Triangular

/-!
# Linear systems

Declaration-free aggregate for the canonical reusable linear-system
algorithm families.
-/
