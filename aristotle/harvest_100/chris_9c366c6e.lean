/-!
# Two Squares 17
Category: Pure Mathematics
Target: Math.two_squares_17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **The prime 17 is a sum of two squares.**

The statement has two parts:
* `17` is prime, spelled out as `2 ≤ 17` together with the fact that every divisor of `17`
  is either `1` or `17` (this is exactly Mathlib's `Nat.prime_def` characterisation);
* `17 = 1 ^ 2 + 4 ^ 2` exhibits `17` as a sum of two squares.

Since this file must begin with the header comment above, it cannot contain an `import`
command; the proof therefore uses only Lean's core library.  The bridge to Mathlib's
`Nat.Prime` is given in `RequestProject.TwoSquares17Mathlib`.
-/
theorem two_squares_17 :
    (2 ≤ 17 ∧ ∀ m : Nat, m ∣ 17 → m = 1 ∨ m = 17) ∧ ∃ a b : Nat, 17 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by decide, ?_⟩, 1, 4, by decide⟩
  have key : ∀ m : Nat, m < 18 → m ∣ 17 → m = 1 ∨ m = 17 := by decide
  intro m hm
  exact key m (Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hm)) hm

end Math

import Mathlib
import RequestProject.TwoSquares17

/-!
# Two Squares 17 — Mathlib phrasing

Restatement of `Math.two_squares_17` using Mathlib's `Nat.Prime`.
-/

namespace Math

/-- The prime `17` is a sum of two squares, phrased with Mathlib's `Nat.Prime`. -/
theorem two_squares_17_prime : Nat.Prime 17 ∧ ∃ a b : ℕ, 17 = a ^ 2 + b ^ 2 :=
  ⟨Nat.prime_def.mpr ⟨two_squares_17.1.1, two_squares_17.1.2⟩, two_squares_17.2⟩

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

