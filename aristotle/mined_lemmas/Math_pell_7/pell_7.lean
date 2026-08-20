/-
# Pell 7
Category: Pure Mathematics
Target: Math.pell_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math

/-- The Pell equation `x² - 7·y² = 1` has a nontrivial integer solution,
i.e. one with `y ≠ 0` (equivalently, `x ≠ ±1`).  Witness: `(x, y) = (8, 3)`,
since `8² - 7·3² = 64 - 63 = 1`. -/

theorem pell_7 : ∃ x y : ℤ, x ^ 2 - 7 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨8, 3, by norm_num, by norm_num⟩

/-- The same statement, obtained instead from Mathlib's general solvability theorem
for Pell's equation, `Pell.exists_of_not_isSquare`, applied to `d = 7`
(which is positive and not a perfect square). -/
