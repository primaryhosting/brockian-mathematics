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

/-
# Two Squares 73
Category: Pure Mathematics
Target: Math.two_squares_73
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The requested header is kept verbatim above as a plain block comment: Lean 4 requires
-- `import` to be the first command, so a module doc comment `/-! ... -/` cannot precede it.)

import Mathlib

namespace Math

/-- The prime `73` is a sum of two squares: `73 = 8 ^ 2 + 3 ^ 2`.

Mathlib's `Nat.Prime.sq_add_sq` (Fermat's two-squares theorem for primes `p % 4 ≠ 3`)
gives an abstract existence proof; here we also exhibit the explicit witnesses. -/
theorem two_squares_73 : Nat.Prime 73 ∧ ∃ a b : ℕ, 73 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 8, 3, by norm_num⟩

/-- The same statement obtained from Mathlib's Fermat two-squares theorem
`Nat.Prime.sq_add_sq`. -/
theorem two_squares_73_via_mathlib : ∃ a b : ℕ, 73 = a ^ 2 + b ^ 2 := by
  have : Fact (Nat.Prime 73) := ⟨by norm_num⟩
  obtain ⟨a, b, h⟩ := Nat.Prime.sq_add_sq (p := 73) (by decide)
  exact ⟨a, b, h.symm⟩

end Math

