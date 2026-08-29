/-
# Two Squares 37
Category: Pure Mathematics
Target: Math.two_squares_37
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Two Squares 37
Category: Pure Mathematics
Target: Math.two_squares_37
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The prime `37` is a sum of two squares (indeed `37 = 1 ^ 2 + 6 ^ 2`).

The proof invokes Fermat's two-squares theorem, available in Mathlib as
`Nat.Prime.sq_add_sq`: for a prime `p` with `p % 4 ≠ 3` there are `a b` with
`a ^ 2 + b ^ 2 = p`. -/
theorem two_squares_37 : ∃ a b : ℕ, (37 : ℕ) = a ^ 2 + b ^ 2 := by
  haveI : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := 37) (by norm_num)
  exact ⟨a, b, hab.symm⟩

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

