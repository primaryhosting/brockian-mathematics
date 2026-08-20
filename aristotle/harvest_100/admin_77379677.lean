/-!
# Two Squares 37
Category: Pure Mathematics
Target: Math.two_squares_37
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- `37` is prime: its only divisors are `1` and `37` (and it is greater than `1`). -/
theorem prime_37 : 1 < 37 ∧ ∀ m : Nat, m ∣ 37 → m = 1 ∨ m = 37 := by
  refine ⟨by decide, fun m hm => ?_⟩
  have h1 : m ≤ 37 := Nat.le_of_dvd (by decide) hm
  have h2 : ∀ k : Nat, k < 38 → k ∣ 37 → k = 1 ∨ k = 37 := by decide
  exact h2 m (by omega) hm

/-- The prime `37` is a sum of two squares: `37 = 1 ^ 2 + 6 ^ 2`. -/
theorem two_squares_37 : ∃ a b : Nat, 37 = a ^ 2 + b ^ 2 := ⟨1, 6, by decide⟩

end Math

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

