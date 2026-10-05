-- Note: Lean 4 requires `import` lines to precede every other token in a file,
-- so the requested module docstring header appears immediately below the import.
import Mathlib

/-!
# Two Squares 73
Category: Pure Mathematics
Target: Math.two_squares_73
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 73.** The prime `73` is a sum of two squares, namely
`73 = 3 ^ 2 + 8 ^ 2`. Existence also follows from Fermat's two-squares theorem
(`Nat.Prime.sq_add_sq` in Mathlib), since `73 % 4 = 1`. -/
theorem two_squares_73 : Nat.Prime 73 ∧ ∃ a b : ℕ, 73 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 3, 8, by norm_num⟩

/-- The existence part, derived instead from Mathlib's form of Fermat's
two-squares theorem, `Nat.Prime.sq_add_sq`. -/
theorem two_squares_73_of_mathlib : ∃ a b : ℕ, 73 = a ^ 2 + b ^ 2 := by
  haveI : Fact (Nat.Prime 73) := ⟨by norm_num⟩
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := 73) (by norm_num)
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

