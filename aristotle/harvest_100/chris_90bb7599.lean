import Mathlib

/-!
# Two Squares 113 — via Mathlib's Fermat two-square theorem

Companion to `RequestProject/TwoSquares113.lean`: the same statement obtained from the
existing Mathlib lemma `Nat.Prime.sq_add_sq`.
-/

namespace Math

/-- `113` is prime. -/
theorem prime_113 : Nat.Prime 113 := by norm_num

/-- Existence of a two-square representation of `113` from `Nat.Prime.sq_add_sq`. -/
theorem two_squares_113_of_mathlib : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 113 :=
  haveI : Fact (Nat.Prime 113) := ⟨prime_113⟩
  Nat.Prime.sq_add_sq (by norm_num)

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

/-!
# Two Squares 113
Category: Pure Mathematics
Target: Math.two_squares_113
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The prime `113` is a sum of two squares: `113 = 7 ^ 2 + 8 ^ 2`.

(Mathlib's Fermat two-square theorem `Nat.Prime.sq_add_sq` gives this abstractly for any
prime `p` with `p % 4 ≠ 3`; see `RequestProject/TwoSquares113Mathlib.lean`. Here the
explicit witnesses make the statement provable by computation alone.) -/
theorem two_squares_113 : ∃ a b : Nat, a ^ 2 + b ^ 2 = 113 := ⟨7, 8, rfl⟩

end Math

