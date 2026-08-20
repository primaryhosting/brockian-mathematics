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

/-!
# Two Squares 109
Category: Pure Mathematics
Target: Math.two_squares_109
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- `109` is prime: it is greater than `1` and its only divisors are `1` and `109`. -/

theorem two_squares_109 :
    (1 < 109 ∧ ∀ m : Nat, m ∣ 109 → m = 1 ∨ m = 109) ∧
      ∃ a b : Nat, (109 : Nat) = a ^ 2 + b ^ 2 :=
  ⟨prime_109, 10, 3, rfl⟩

end Math

-- #print axioms Math.two_squares_109

