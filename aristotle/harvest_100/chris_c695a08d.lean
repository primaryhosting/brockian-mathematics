/-!
# Two Squares 61
Category: Pure Mathematics
Target: Math.two_squares_61
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 61.** The number `61` is prime (it is at least `2` and its only
divisors are `1` and itself) and it is a sum of two squares, namely `61 = 5 ^ 2 + 6 ^ 2`.

Note: Lean requires `import` commands to be the very first commands in a file, so in order to
keep the required header comment at the top of the file this statement is phrased using the
elementary definition of primality rather than `Nat.Prime`.  The equivalent Mathlib-flavoured
statement `Nat.Prime 61 ∧ ∃ a b : ℕ, 61 = a ^ 2 + b ^ 2` is derived in
`RequestProject/TwoSquares61Mathlib.lean`. -/
theorem two_squares_61 :
    (2 ≤ 61 ∧ ∀ m : Nat, m ∣ 61 → m = 1 ∨ m = 61) ∧ ∃ a b : Nat, 61 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by omega, fun m hm => ?_⟩, 5, 6, rfl⟩
  have h : m < 62 := Nat.lt_succ_of_le (Nat.le_of_dvd (by omega) hm)
  revert hm
  revert h
  revert m
  decide

end Math

import Mathlib
import RequestProject.TwoSquares61

/-!
# Two Squares 61 — Mathlib phrasing

The Mathlib-flavoured restatement of `Math.two_squares_61`.
-/

namespace Math

/-- The prime `61` is a sum of two squares: `61 = 5 ^ 2 + 6 ^ 2`. -/
theorem two_squares_61_prime : Nat.Prime 61 ∧ ∃ a b : ℕ, 61 = a ^ 2 + b ^ 2 := by
  refine ⟨?_, (two_squares_61).2⟩
  rw [Nat.prime_def]
  exact two_squares_61.1

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

