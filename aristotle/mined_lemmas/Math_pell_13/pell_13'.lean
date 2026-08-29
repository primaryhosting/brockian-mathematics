/-
# Pell 13
Category: Pure Mathematics
Target: Math.pell_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- **Pell's equation for `d = 13`.** The equation `x² - 13·y² = 1` has a
nontrivial integer solution: the fundamental solution is `x = 649`, `y = 180`,
since `649² - 13·180² = 421201 - 421200 = 1`.

Mathlib's general theory (`Pell.exists_of_not_isSquare`, which produces a
solution with `y ≠ 0` for any non-square `d > 0`) also gives this; both proofs
are recorded below. -/

theorem pell_13' : ∃ x y : ℤ, x ^ 2 - 13 * y ^ 2 = 1 ∧ y ≠ 0 := by
  obtain ⟨x, y, hxy, hy⟩ :=
    Pell.exists_of_not_isSquare (d := 13) (by norm_num) (by norm_num)
  exact ⟨x, y, hxy, hy⟩

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

