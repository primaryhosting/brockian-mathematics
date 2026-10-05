/-!
# Two Squares 61
Category: Pure Mathematics
Target: Math.two_squares_61
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **The prime `61` is a sum of two squares.**

The first component states that `61` is prime, spelled out elementarily as
`1 < 61` together with "every proper divisor of `61` equals `1`"; the second
component exhibits `61 = 5 ^ 2 + 6 ^ 2`.

The required header comment must be the first thing in this file, which Lean does
not allow to be followed by `import` commands, so this file is stated and proved
using only Lean core.  The same result phrased with Mathlib's `Nat.Prime` and
derived from Mathlib's two-square theorem `Nat.Prime.sq_add_sq` is in
`RequestProject/TwoSquares61Mathlib.lean`. -/
theorem two_squares_61 :
    (1 < 61 ∧ ∀ m < 61, m ∣ 61 → m = 1) ∧ ∃ a b : Nat, 61 = a ^ 2 + b ^ 2 :=
  ⟨⟨by decide, by decide⟩, ⟨5, 6, rfl⟩⟩

end Math

import Mathlib

/-!
# Two Squares 61 (Mathlib phrasing)

Companion to `RequestProject/Math.lean`: the statement "the prime `61` is a sum of
two squares", phrased with Mathlib's `Nat.Prime`, both with explicit witnesses and
via Mathlib's two-square theorem `Nat.Prime.sq_add_sq`.
-/

namespace Math

/-- `61` is prime and `61 = 5 ^ 2 + 6 ^ 2`. -/
theorem prime_61_sum_two_squares : Nat.Prime 61 ∧ ∃ a b : ℕ, 61 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 5, 6, by norm_num⟩

/-- The same existence statement obtained from Mathlib's two-square theorem
`Nat.Prime.sq_add_sq`, applied to the prime `61` (which is `1 mod 4`). -/
theorem prime_61_sum_two_squares' : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 61 :=
  haveI : Fact (Nat.Prime 61) := ⟨by norm_num⟩
  Nat.Prime.sq_add_sq (p := 61) (by norm_num)

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

