/-!
# Two Squares 29
Category: Pure Mathematics
Target: Math.two_squares_29
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **The prime 29 is a sum of two squares.**

The statement has two parts:
* `29` is prime, spelled out elementarily as `2 ≤ 29` together with the fact that every
  natural divisor of `29` is either `1` or `29`;
* `29 = a ^ 2 + b ^ 2` for some naturals `a`, `b` (indeed `29 = 2 ^ 2 + 5 ^ 2`).

The file is deliberately import-free (so that the required header comment can be the very
first thing in the file), hence primality is phrased directly instead of via `Nat.Prime`. -/
theorem two_squares_29 :
    (2 ≤ 29 ∧ ∀ m : Nat, m ∣ 29 → m = 1 ∨ m = 29) ∧ ∃ a b : Nat, 29 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by decide, ?_⟩, 2, 5, rfl⟩
  have key : ∀ m < 30, m ∣ 29 → m = 1 ∨ m = 29 := by decide
  intro m hm
  exact key m (Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hm)) hm

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

