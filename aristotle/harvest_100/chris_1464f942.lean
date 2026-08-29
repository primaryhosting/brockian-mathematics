/-
# Pell 6
Category: Pure Mathematics
Target: Math.pell_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pell 6
Category: Pure Mathematics
Target: Math.pell_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Pell's equation `x² - 6·y² = 1` has a nontrivial integer solution,
witnessed by `(x, y) = (5, 2)`, since `25 - 6 * 4 = 1`. -/
theorem pell_6 : ∃ x y : ℤ, x ^ 2 - 6 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨5, 2, by norm_num, by norm_num⟩

/-- `6` is not a perfect square (as an integer). -/
theorem six_not_isSquare : ¬ IsSquare (6 : ℤ) := by
  decide +kernel

/-- The same statement obtained from Mathlib's general existence theorem for Pell
equations, `Pell.exists_of_not_isSquare`: for `0 < d` with `d` not a square, the
equation `x² - d·y² = 1` has a solution with `y ≠ 0`. -/
theorem pell_6_of_mathlib : ∃ x y : ℤ, x ^ 2 - 6 * y ^ 2 = 1 ∧ y ≠ 0 :=
  Pell.exists_of_not_isSquare (by norm_num) six_not_isSquare

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

