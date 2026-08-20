/-!
# Two Squares 37
Category: Pure Mathematics
Target: Math.two_squares_37
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 37.** The number `37` is prime (it is at least `2` and its only
divisors are `1` and itself) and it is a sum of two squares: `37 = 1 ^ 2 + 6 ^ 2`.

The primality condition is spelled out explicitly (rather than via `Nat.Prime`) so that
this file can start with the required header comment: Lean requires `import` commands to
be the very first commands in a file, before any module documentation. A version stated
with Mathlib's `Nat.Prime` is available as `Math.two_squares_37_prime` in
`RequestProject/TwoSquares37Prime.lean`. -/
theorem two_squares_37 :
    (2 ≤ 37 ∧ ∀ m : Nat, m ∣ 37 → m = 1 ∨ m = 37) ∧ ∃ a b : Nat, 37 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by decide, ?_⟩, 1, 6, by decide⟩
  have key : ∀ m : Nat, m < 38 → m ∣ 37 → m = 1 ∨ m = 37 := by decide
  intro m hm
  exact key m (Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hm)) hm

end Math

import Mathlib

/-!
# Two Squares 37 (Mathlib formulation)

Companion to `RequestProject/TwoSquares37.lean`, stating the result with Mathlib's
`Nat.Prime`.
-/

namespace Math

/-- The prime `37` is a sum of two squares: `37 = 1 ^ 2 + 6 ^ 2`. -/
theorem two_squares_37_prime : Nat.Prime 37 ∧ ∃ a b : ℕ, 37 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 1, 6, by norm_num⟩

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

