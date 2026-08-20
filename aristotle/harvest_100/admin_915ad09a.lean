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
# Two Squares 113
Category: Pure Mathematics
Target: Math.two_squares_113
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- `113` is prime: it is greater than `1` and its only divisors are `1` and itself.

(Stated with the primality condition spelled out, since the required header comment must be
the very first thing in the file, which prevents any `import` and hence the use of
`Nat.Prime` from Mathlib.) -/
theorem prime_113 : 1 < 113 ∧ ∀ m : Nat, m ∣ 113 → m = 1 ∨ m = 113 := by
  refine ⟨by decide, fun m hm => ?_⟩
  have hlt : m < 114 := Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hm)
  revert hm
  revert hlt
  revert m
  decide

/-- The prime `113` is a sum of two squares: `113 = 7 ^ 2 + 8 ^ 2`. -/
theorem two_squares_113 :
    (1 < 113 ∧ ∀ m : Nat, m ∣ 113 → m = 1 ∨ m = 113) ∧ ∃ a b : Nat, 113 = a ^ 2 + b ^ 2 :=
  ⟨prime_113, 7, 8, by decide⟩

end Math

