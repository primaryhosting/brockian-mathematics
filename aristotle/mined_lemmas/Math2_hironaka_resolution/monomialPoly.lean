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

noncomputable def monomialPoly (k : Type*) [Field k] (m n : ℕ) : MvPolynomial (Fin 2) k :=
  MvPolynomial.X 1 ^ n - MvPolynomial.X 0 ^ m

