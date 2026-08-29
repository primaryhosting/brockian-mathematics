/-!
# Pell 10
Category: Pure Mathematics
Target: Math.pell_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 10`.**

`x² - 10 y² = 1` has a nontrivial integer solution (i.e. one with `y ≠ 0`),
namely `(x, y) = (19, 6)`, since `19² - 10 · 6² = 361 - 360 = 1`.

(The general existence statement for non-square `d` is available in Mathlib as
`Pell.exists_of_not_isSquare`; here the explicit fundamental solution is given
directly, which also keeps this file free of imports so that the required
header comment can stand at the very top of the file.) -/
theorem pell_10 : ∃ x y : Int, x ^ 2 - 10 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨19, 6, by decide, by decide⟩

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

import Mathlib

/-!
# Pell 10 — via Mathlib's general existence theorem

A companion to `Math.pell_10`: the same statement derived from Mathlib's
`Pell.exists_of_not_isSquare`, which gives a nontrivial solution of
`x² - d y² = 1` for every positive non-square `d`.
-/

namespace Math

/-- `x² - 10 y² = 1` has a nontrivial integer solution, obtained from Mathlib's
general Pell existence theorem `Pell.exists_of_not_isSquare` (10 is positive and
not a perfect square). -/
theorem pell_10_of_mathlib : ∃ x y : ℤ, x ^ 2 - 10 * y ^ 2 = 1 ∧ y ≠ 0 :=
  Pell.exists_of_not_isSquare (by norm_num) (by decide +kernel)

end Math

