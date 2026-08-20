/-!
# Trivial Zero Neg Two
Category: Riemann Program
Target: Riemann.Zeta.trivial_zero_neg_two
Statement: riemannZeta (-2) = 0 : the first trivial zero of the Riemann zeta function. (Mathlib proves riemannZeta vanishes at negative even integers, e.g. riemannZeta_neg_two_mul_nat_add_one; specialise to n = 0.)
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Trivial Zero Neg Two
Category: Riemann Program
Target: Riemann.Zeta.trivial_zero_neg_two
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Riemann.Zeta

/-- The first trivial zero of the Riemann zeta function: `ζ(-2) = 0`. -/
theorem trivial_zero_neg_two : riemannZeta (-2) = 0 := by
  have h := riemannZeta_neg_two_mul_nat_add_one 0
  norm_num at h
  exact h

end Riemann.Zeta

