/-!
# Two Squares 29
Category: Pure Mathematics
Target: Math.two_squares_29
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- `n` is a sum of two squares. -/
def IsSumOfTwoSquares (n : Nat) : Prop := ∃ a b : Nat, n = a ^ 2 + b ^ 2

/-- `n` is prime: it is at least `2` and its only divisor below `n` is `1`. -/
def IsPrimeNat (n : Nat) : Prop := 2 ≤ n ∧ ∀ m : Nat, m < n → m ∣ n → m = 1

/-- Key intermediate lemma: `29 = 2 ^ 2 + 5 ^ 2`. -/
theorem twenty_nine_eq_sq_add_sq : (29 : Nat) = 2 ^ 2 + 5 ^ 2 := by decide

/-- 29 is prime. -/
theorem twenty_nine_prime : IsPrimeNat 29 := ⟨by decide, by decide⟩

/-- The prime 29 is a sum of two squares: `29 = 2 ^ 2 + 5 ^ 2`. -/
theorem two_squares_29 : IsPrimeNat 29 ∧ IsSumOfTwoSquares 29 :=
  ⟨twenty_nine_prime, 2, 5, twenty_nine_eq_sq_add_sq⟩

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

