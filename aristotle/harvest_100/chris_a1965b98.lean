/-!
# Two Squares 37
Category: Pure Mathematics
Target: Math.two_squares_37
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **The prime 37 is a sum of two squares.**

Primality of `37` is spelled out directly (`2 ≤ 37` together with the fact that every divisor
of `37` is `1` or `37`), which is exactly the definition of `Nat.Prime 37`; the file is kept
self-contained so that the required header comment can be the very first thing in it.
The representation as a sum of two squares is `37 = 1 ^ 2 + 6 ^ 2`. -/
theorem two_squares_37 :
    (2 ≤ 37 ∧ ∀ m : Nat, m ∣ 37 → m = 1 ∨ m = 37) ∧ ∃ a b : Nat, 37 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by decide, ?_⟩, 1, 6, by decide⟩
  have key : ∀ m : Nat, m < 38 → m ∣ 37 → m = 1 ∨ m = 37 := by decide
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

