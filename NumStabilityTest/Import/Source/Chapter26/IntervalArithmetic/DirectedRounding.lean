import NumStability.Source.Higham.Chapter26.IntervalArithmetic.DirectedRounding

/-!
# Higham Chapter 26 outward-directed rounding smoke test
-/

#check NumStability.RealInterval.EndpointInFiniteRange
#check NumStability.RealInterval.finiteRoundTowardNegative_le_of_endpointRange
#check NumStability.RealInterval.le_finiteRoundTowardPositive_of_endpointRange
#check NumStability.RealInterval.outwardRounded
#check NumStability.RealInterval.outwardRounded_contains
#check NumStability.RealInterval.outwardAdd
#check NumStability.RealInterval.outwardAdd_contains
#check NumStability.RealInterval.outwardSub
#check NumStability.RealInterval.outwardSub_contains
#check NumStability.RealInterval.outwardMul
#check NumStability.RealInterval.outwardMul_contains
#check NumStability.RealInterval.outwardDiv
#check NumStability.RealInterval.outwardDiv_contains
