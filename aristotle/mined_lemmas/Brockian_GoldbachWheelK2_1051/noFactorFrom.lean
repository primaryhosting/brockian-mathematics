import Mathlib

/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Brockian

/-- Trial division helper: `noFactorFrom f d n` is `true` when none of
`d, d+1, …` (up to `f` steps, stopping as soon as the divisor squared exceeds `n`)
divides `n`. -/

def noFactorFrom : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | (f + 1), d, n =>
      if n < d * d then true else if n % d == 0 then false else noFactorFrom f (d + 1) n

/-- Kernel-friendly primality test by trial division. -/
