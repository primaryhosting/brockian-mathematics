/-!
# Two Squares 97
Category: Pure Mathematics
Target: Math.two_squares_97
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- `97` is prime, stated elementarily: it is at least `2` and every divisor of it
is either `1` or `97`. -/
theorem prime_97 : 2 ≤ 97 ∧ ∀ m : Nat, m ∣ 97 → m = 1 ∨ m = 97 := by
  refine ⟨by decide, fun m hm => ?_⟩
  have hlt : m < 98 := Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hm)
  exact (by decide : ∀ m < 98, m ∣ 97 → m = 1 ∨ m = 97) m hlt hm

/-- The prime `97` is a sum of two squares: `97 = 9 ^ 2 + 4 ^ 2`.

Mathlib's general result `Nat.Prime.sq_add_sq` (Fermat's two-squares theorem: a prime
`p` with `p % 4 ≠ 3` is a sum of two squares) also applies here, but the explicit
witness gives a self-contained, import-free proof. -/
theorem two_squares_97 : ∃ a b : Nat, 97 = a ^ 2 + b ^ 2 := ⟨9, 4, rfl⟩

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

