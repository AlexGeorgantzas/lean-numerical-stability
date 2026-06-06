import LeanFpAnalysis.HDP.Probability.Concentration

/-!
# HDP Chapter 2

Concentration of sums of independent random variables.  The current
Berry-Esseen development proves the book-facing theorem end-to-end with
absolute constant `C = 3`; the Prawitz/Shevtsova exact-constant bridge work is
kept as reusable API for the later `C = 1` sharpening.
-/
