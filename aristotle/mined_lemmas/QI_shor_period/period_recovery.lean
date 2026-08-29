import Mathlib

/-!
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` lines to precede every other command, including module
doc comments, so this header follows the single `import Mathlib` line.)
-/

namespace QI

/-!
## Overview

Shor's algorithm finds the period `r` of the modular exponentiation function
`x ↦ a ^ x mod N` (for `a` coprime to `N`).  Its structure is:

* the function `x ↦ a ^ x mod N` really is periodic, with least period the
  multiplicative order `r` of `a` modulo `N`;
* the quantum phase-estimation stage produces, with probability bounded below by
  some constant `c > 0`, a measurement outcome `y` whose rescaling `y / M`
  approximates a fraction `s / r` with `gcd (s, r) = 1` to within `1 / (2 M)`
  (such an approximating outcome always exists, by rounding);
* the classical post-processing stage (continued fractions) then recovers `r`
  *exactly*, because a rational number with a sufficiently small denominator is
  uniquely determined by an approximation of this quality: any fraction `p / q`
  in lowest terms with `q * r < M` that is that close to `y / M` must have
  `q = r`;
* repeating the experiment amplifies the success probability to `1`.

The theorem `QI.shor_period` below bundles these statements.  The quantum stage
enters only through the abstract success probability `c`, since the amplitude
analysis is not part of the number-theoretic content formalized here.
-/

/-- Two rational numbers with small denominators cannot both be very close to the
same rational `x`: this is the uniqueness statement underlying the classical
continued-fraction post-processing of Shor's algorithm. -/

theorem period_recovery {x Q : ℚ} {p q s r : ℤ} (hq : 0 < q) (hr : 0 < r)
    (hpq : IsCoprime p q) (hsr : IsCoprime s r)
    (hQ : (q : ℚ) * r < Q ^ 2)
    (hp : |x - (p : ℚ) / q| ≤ 1 / (2 * Q ^ 2))
    (hs : |x - (s : ℚ) / r| ≤ 1 / (2 * Q ^ 2)) :
    q = r :=
  denom_eq_of_div_eq_div hq hr hpq hsr (approx_unique hq hr hQ hp hs)

/-- Existence of a good measurement outcome: for every target fraction `z` and
every scale `M > 0` there is an integer `y` with `|y / M - z| ≤ 1 / (2 M)`. -/
