import NumStability.Algorithms.HighamChapter9
import NumStability.Algorithms.HighamChapter9CompletePivotSharpClosure
import NumStability.Algorithms.HighamChapter9ComplexClosure
import NumStability.Algorithms.HighamChapter9ComputedCorrection
import NumStability.Algorithms.HighamChapter9DoolittleClosure
import NumStability.Algorithms.HighamChapter9Theorem914Actual
import NumStability.Algorithms.HighamChapter9Theorem914DiagDominant
import NumStability.Algorithms.HighamChapter9Theorem914Primitive
import NumStability.Algorithms.HighamChapter9Theorem97Classification
import NumStability.Algorithms.HighamChapter9Theorem99Closure
import NumStability.Algorithms.HighamChapter9Theorem99ComplexClosure

/-!
# Isolated historical Chapter 9 import smoke test

Compiles the 11 historical Chapter 9 candidate paths on their own, with
no other repository test module in scope, so that the historical import surface
prepared by `docs/architecture/lane-proposals/claude-classification/ch09/` is
exercised in isolation.

This module is intentionally not reachable from `NumStabilityTest`; wiring the
worker test surface into the root aggregate is integrator work.
-/
