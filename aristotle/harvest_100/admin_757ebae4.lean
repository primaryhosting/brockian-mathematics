import Mathlib
/-!
# Pell 7
Category: Pure Mathematics
Target: Math.pell_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Pell equation `x² - 7·y² = 1` has a nontrivial integer solution
(nontrivial in the sense that `y ≠ 0`, ruling out the trivial solutions `(±1, 0)`);
explicitly `(x, y) = (8, 3)` works, since `64 - 63 = 1`. -/
theorem pell_7 : ∃ x y : ℤ, x ^ 2 - 7 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨8, 3, by norm_num, by norm_num⟩

/-- The same statement, obtained instead from Mathlib's general existence theorem
`Pell.exists_of_not_isSquare` for the Pell equation `x² - d·y² = 1` with `d > 0`
not a perfect square. -/
theorem pell_7_of_mathlib : ∃ x y : ℤ, x ^ 2 - 7 * y ^ 2 = 1 ∧ y ≠ 0 :=
  Pell.exists_of_not_isSquare (by norm_num) (by decide +kernel)

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

