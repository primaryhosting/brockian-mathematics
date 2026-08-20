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

theorem prime_109 : 1 < 109 ∧ ∀ m : Nat, m ∣ 109 → m = 1 ∨ m = 109 := by
  refine ⟨by decide, fun m hm => ?_⟩
  have hle : m ≤ 109 := Nat.le_of_dvd (by decide) hm
  have key : ∀ k ∈ List.range 110, k ∣ 109 → k = 1 ∨ k = 109 := by decide
  exact key m (List.mem_range.mpr (Nat.lt_succ_of_le hle)) hm

/-- The prime `109` is a sum of two squares: `109 = 10 ^ 2 + 3 ^ 2`. -/
