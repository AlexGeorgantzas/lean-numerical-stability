import NumStability.Algorithms.StationaryIteration

/-!
# Stationary-iteration import smoke test

This test imports only the canonical stationary-iteration module and checks the
recovered Drazin powered-vector decomposition and its conditional limit.
-/

#check NumStability.stationaryDrazin_matPow_vec_split
#check NumStability.stationaryDrazin_matPow_vec_tendsto_fixedProjector_of_range_tendsto_zero
