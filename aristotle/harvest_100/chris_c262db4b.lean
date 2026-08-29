/-!
# Two Squares 101
Category: Pure Mathematics
Target: Math.two_squares_101
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 101.**  The number `101` is prime (it is at least `2` and its only
divisors are `1` and itself) and it is a sum of two squares, namely `101 = 10 ^ 2 + 1 ^ 2`.

The statement is phrased with an explicit, self-contained definition of primality so that the
file needs no imports (a module docstring must be the very first thing in the file). -/
theorem two_squares_101 :
    (2 ≤ 101 ∧ ∀ m, m ∣ 101 → m = 1 ∨ m = 101) ∧ ∃ a b : Nat, 101 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by decide, ?_⟩, 10, 1, by decide⟩
  have key : ∀ m ≤ 101, m ∣ 101 → m = 1 ∨ m = 101 := by decide
  intro m hm
  exact key m (Nat.le_of_dvd (by decide) hm) hm

end Math

import Mathlib
import RequestProject.TwoSquares101

/-!
# Two Squares 101, Mathlib phrasing

Restatement of `Math.two_squares_101` using Mathlib's `Nat.Prime`.
-/

namespace Math

/-- `101` is a prime which is a sum of two squares, stated with Mathlib's `Nat.Prime`. -/
theorem two_squares_101_prime : Nat.Prime 101 ∧ ∃ a b : ℕ, 101 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, two_squares_101.2⟩

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

