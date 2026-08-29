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

def monomialCurve (k : Type*) [Field k] (m n : ℕ) : Set (k × k) :=
  {p : k × k | p.2 ^ n = p.1 ^ m}

/-- The parametrization of `C(m,n)` by the (smooth) affine line, `t ↦ (t ^ n, t ^ m)`. -/
