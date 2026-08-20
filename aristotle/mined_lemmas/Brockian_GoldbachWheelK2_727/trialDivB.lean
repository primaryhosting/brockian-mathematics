/-
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000000

namespace Brockian

/-- `trialDivB n f d` performs trial division of `n` by the successive divisors
`d, d+1, ...` (using at most `f` steps), stopping successfully as soon as the
divisor exceeds `√n`. It returns `true` only when no divisor `≥ d` with
`k * k ≤ n` divides `n`. -/

def trialDivB (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | (f + 1), d => if n % d == 0 then false else if n < (d + 1) * (d + 1) then true
      else trialDivB n f (d + 1)

/-- A kernel-friendly primality test by trial division up to `√n`. -/
