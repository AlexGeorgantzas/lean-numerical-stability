import NumStability.Source.Higham.Chapter08.Equation15.FanInExecutor.FirstOrderResidual

/-!
# R03 canonical test — `FirstOrderResidual` (declaration-free bridge)

Integrator follow-up: the reviewed R03 route amendment
(`reviews/R03-route-amendment.md`) delivers this module as a documented
declaration-free bridge re-exporting the Equation 18 destination, and the
compatibility contract requires every registered canonical target to carry a
direct test import. The Equation 8.15 theorem it re-exports is checked here
through the bridge, proving the historical surface survives.
-/

#check @NumStability.higham8_15_fanIn7Executor_residual_family_firstOrder
