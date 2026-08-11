import NumStability.Source.Higham.Chapter15.Section02.Boyd.EndpointTermination.InfinityCounterexample.Trace

/-!
# Frozen route and private-normalized closure: `NumStability.Source.Higham.Chapter15.Section02.Boyd.EndpointTermination.InfinityCounterexample.Trace`

Exercises the frozen declaration route together with the reviewed private
normalization. The private members re-mangle against this module and are
not addressable from here; the public members of the private reverse
closure that live here are checked instead, which is what pins the
normalization observably.
-/

#check @NumStability.RectPNormPair.higham15_rectangular_infinity_counterexample_stops_at_four
#check @NumStability.RectPNormPair.higham15_rectangular_infinity_n_plus_one_source_discrepancy
