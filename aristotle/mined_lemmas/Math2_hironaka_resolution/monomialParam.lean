/-
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxHeartbeats 1000000

namespace Math2

/-- The affine plane curve `C(m,n) = {(x,y) | y ^ n = x ^ m}`. -/

def monomialParam (k : Type*) [Field k] (m n : ℕ) : k → k × k := fun t => (t ^ n, t ^ m)

/-- A nonzero element whose `m`-th and `n`-th powers are `1`, for coprime `m` and `n`,
is equal to `1`. -/
