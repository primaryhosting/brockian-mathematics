/-!
# Two Squares 61
Category: Pure Mathematics
Target: Math.two_squares_61
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 61.** The number `61` is prime -- its only divisors are `1` and `61`,
and it is at least `2` -- and it is a sum of two squares, namely `61 = 5 ^ 2 + 6 ^ 2`.

Primality is spelled out elementarily here (`2 ≤ 61` together with the divisor condition)
so that this file needs no imports; the file `TwoSquares61Mathlib.lean` records the same
result phrased with Mathlib's `Nat.Prime`, together with the equivalence of the two
formulations. -/
theorem two_squares_61 :
    (2 ≤ 61 ∧ ∀ m : Nat, m ∣ 61 → m = 1 ∨ m = 61) ∧ ∃ a b : Nat, 61 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by decide, ?_⟩, 5, 6, by decide⟩
  intro m hm
  have h : m < 62 := Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hm)
  revert hm
  revert h
  revert m
  decide

end Math

import Mathlib
import RequestProject.TwoSquares61

/-!
# Two Squares 61 (Mathlib formulation)

The same result as in `RequestProject/TwoSquares61.lean`, phrased with Mathlib's `Nat.Prime`,
together with the fact that the elementary primality condition used there is equivalent to it.
-/

namespace Math

/-- `61` is prime and is a sum of two squares, stated with Mathlib's `Nat.Prime`. -/
theorem prime_61_sum_two_squares : Nat.Prime 61 ∧ ∃ a b : ℕ, 61 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 5, 6, by norm_num⟩

/-- The elementary primality condition used in `Math.two_squares_61` is exactly `Nat.Prime 61`. -/
theorem prime_61_iff : (2 ≤ 61 ∧ ∀ m : ℕ, m ∣ 61 → m = 1 ∨ m = 61) ↔ Nat.Prime 61 := by
  constructor
  · intro _
    norm_num
  · intro h
    exact ⟨h.two_le, fun m hm => (Nat.Prime.eq_one_or_self_of_dvd h m hm)⟩

/-- The target theorem `Math.two_squares_61` indeed yields the Mathlib statement
`Nat.Prime 61 ∧ ∃ a b, 61 = a ^ 2 + b ^ 2`. -/
theorem prime_61_sum_two_squares_of_target :
    Nat.Prime 61 ∧ ∃ a b : ℕ, 61 = a ^ 2 + b ^ 2 :=
  ⟨prime_61_iff.mp two_squares_61.1, two_squares_61.2⟩

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

