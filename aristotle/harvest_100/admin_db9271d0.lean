/-
# Pell 8
Category: Pure Mathematics
Target: Math.pell_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pell 8
Category: Pure Mathematics
Target: Math.pell_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Pell equation `x² - 8·y² = 1` has a nontrivial integer solution, i.e. one with
`y ≠ 0` (so `x ≠ ±1`).  Witness: `(x, y) = (3, 1)`, since `9 - 8 = 1`. -/
theorem pell_8 : ∃ x y : ℤ, x ^ 2 - 8 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨3, 1, by norm_num, one_ne_zero⟩

/-- `8` is not a perfect square in `ℤ`. -/
theorem not_isSquare_eight : ¬ IsSquare (8 : ℤ) := by
  rintro ⟨r, hr⟩
  have h1 : r ≤ 3 := by nlinarith
  have h2 : -3 ≤ r := by nlinarith
  interval_cases r <;> omega

/-- An alternative, non-constructive proof of `Math.pell_8`, obtained from Mathlib's general
existence theorem for Pell equations, `Pell.exists_of_not_isSquare`. -/
theorem pell_8' : ∃ x y : ℤ, x ^ 2 - 8 * y ^ 2 = 1 ∧ y ≠ 0 :=
  Pell.exists_of_not_isSquare (by norm_num) not_isSquare_eight

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

