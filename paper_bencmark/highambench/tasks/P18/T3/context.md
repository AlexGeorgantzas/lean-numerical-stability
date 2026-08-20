# P18-T3 paper context

## Fixed source

The source is Zachary J. Grant, *Perturbed Runge--Kutta Methods for Mixed
Precision Applications*, Journal of Scientific Computing 92, article 6,
2022. The local PDF SHA-256 is
`b18628ffc348d7aeec2da02efb989b6e012f0b0fae09b27fbff735bb8a5877cd`.

P18-T3 selects the coefficient-level claim for Method 4s3pC:

- the third-order consistency conditions listed on PDF/article page 7;
- the simplified smooth-perturbation conditions (3.5) on page 8;
- the statement on page 17 that Method 4s3pC was devised for those simplified
  conditions; and
- the four-stage `A`, `A^epsilon`, `b`, and `b^epsilon` coefficients and the
  smooth/nonsmooth distinction printed on page 18.

The paper follows the coefficients with expected global errors
`O(Delta t^3) + O(epsilon Delta t^3)` for a well-behaved perturbation and
`O(Delta t^3) + O(epsilon Delta t^2)` otherwise. It does not provide the norm,
hidden constants, asymptotic neighborhood, trajectory semantics, or stability
theorem needed to turn those displays into a formal global bound. Page 19 and
the conclusion instead say that rigorous stability analysis remains necessary.
This task therefore certifies the coefficients responsible for the two
regimes; it does not claim the unfinished global theorem.

## Printed coefficients

The controlled definitions transcribe the four-stage coefficients exactly as
printed. The source gives decimal values to fifteen places rather than symbolic
exact values. Lean treats those printed decimals as exact rational reals, so
identities designed to be zero can have residuals around `10^-15`.

`p18PrintedCoeffTolerance = 2 / 10^15` is a transparent certificate tolerance
for that printed representation. It is larger than every residual asserted in
the target; it is not an error constant for a Runge--Kutta execution.

The node vectors are linked to the printed matrices by
`c = A*e` and `c^epsilon = A^epsilon*e`. Tilde quantities are the pointwise sums
of their full-precision and perturbation parts.

## Fixed conclusion

The theorem proves, without assumptions:

1. the printed perturbation output weights satisfy `b^epsilon = 0` exactly;
2. the four consistency conditions through order three have residual at most
   `2e-15`;
3. every nontrivial simplified smooth-perturbation condition through order
   three has residual at most `2e-15`; and
4. the stricter nonsmooth condition `|b tilde| |c^epsilon| = 0` fails
   decisively: its left side is greater than `1/100`.

Conditions containing `b^epsilon` vanish exactly by item 1. The remaining six
smooth conditions are all stated explicitly. Item 4 records why the same
coefficients do not satisfy the nonsmooth order-three requirements.

No Euclidean state norm, arbitrary state dimension, exact big-O constant,
stability premise, or comparison between unrelated hidden constants occurs in
the target.
