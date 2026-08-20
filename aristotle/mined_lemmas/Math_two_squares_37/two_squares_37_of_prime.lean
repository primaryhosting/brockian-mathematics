/-!
# Two Squares 37
Category: Pure Mathematics
Target: Math.two_squares_37
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The prime `37` is a sum of two squares: `37 = 6 ^ 2 + 1 ^ 2`.

(In Mathlib this also follows from `Nat.Prime.sq_add_sq`, which says a prime `p`
with `p % 4 ≠ 3` is a sum of two squares; see `RequestProject/TwoSquares37Mathlib.lean`.) -/

theorem two_squares_37_of_prime : ∃ a b : ℕ, (37 : ℕ) = a ^ 2 + b ^ 2 := by
  haveI : Fact (Nat.Prime 37) := ⟨prime_37⟩
  obtain ⟨a, b, h⟩ := Nat.Prime.sq_add_sq (p := 37) (by norm_num)
  exact ⟨a, b, h.symm⟩

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

