import Mathlib
/-!
# Catalan Closed
Category: Pure Mathematics
Target: Math.catalan_closed
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The exact (division-free) form of the closed formula: `(n+1) * catalan n = C(2n, n)`. -/
theorem catalan_mul_succ (n : ℕ) : (n + 1) * catalan n = Nat.choose (2 * n) n := by
  rw [succ_mul_catalan_eq_centralBinom, Nat.centralBinom, two_mul]

/-- **Closed formula for the Catalan numbers**: the `n`-th Catalan number equals
`C(2n, n) / (n + 1)` (the division is exact). -/
theorem catalan_closed (n : ℕ) : catalan n = Nat.choose (2 * n) n / (n + 1) := by
  rw [← catalan_mul_succ, Nat.mul_div_cancel_left _ (Nat.succ_pos n)]

/-- The same closed formula stated over the rationals. -/
theorem catalan_closed_rat (n : ℕ) :
    (catalan n : ℚ) = (Nat.choose (2 * n) n : ℚ) / (n + 1) := by
  have h : ((n : ℚ) + 1) * (catalan n : ℚ) = (Nat.choose (2 * n) n : ℚ) := by
    exact_mod_cast congrArg (Nat.cast (R := ℚ)) (catalan_mul_succ n)
  field_simp
  linarith [h]

end Math

-- Axiom audit: only the standard axioms `propext`, `Classical.choice`, `Quot.sound`.
#print axioms Math.catalan_closed
#print axioms Math.catalan_mul_succ
#print axioms Math.catalan_closed_rat

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

