/-
# Pell 2
Category: Pure Mathematics
Target: Math.pell_2
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

/-- **Pell's equation for `d = 2`.** The equation `x² - 2·y² = 1` has a nontrivial
integer solution, i.e. one with `y ≠ 0` (equivalently `x ≠ ±1`).

Mathlib also provides the general existence result
`Pell.exists_of_not_isSquare : 1 < d → ¬IsSquare d → ∃ x y, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0`,
which applies here with `d = 2`; we record both a concrete witness `(x, y) = (3, 2)`
and the derivation from that Mathlib lemma. -/
theorem pell_2 : ∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨3, 2, by norm_num, by norm_num⟩

/-- The same statement, obtained from Mathlib's general theorem
`Pell.exists_of_not_isSquare` (since `2` is not a perfect square). -/
theorem pell_2_of_mathlib : ∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = 1 ∧ y ≠ 0 :=
  Pell.exists_of_not_isSquare (by norm_num) (by decide +kernel)

end Math

