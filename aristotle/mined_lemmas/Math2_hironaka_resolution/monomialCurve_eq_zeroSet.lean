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

lemma monomialCurve_eq_zeroSet (k : Type*) [Field k] (m n : ℕ) :
    monomialCurve k m n =
      {p : k × k | MvPolynomial.eval ![p.1, p.2] (monomialPoly k m n) = 0} := by
  ext ⟨x, y⟩
  simp [monomialCurve, monomialPoly, sub_eq_zero]

/-- The curve `C(m,n)` is genuinely singular at the origin when `m, n ≥ 2`: the origin lies on
the curve and both partial derivatives of the defining equation vanish there. -/
