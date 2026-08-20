import Mathlib

/-!
# Pell 7, via Mathlib's general Pell theory

The same statement as `Math.pell_7` (in `RequestProject/Pell7.lean`), but derived
from Mathlib's existence theorem for Pell's equation,
`Pell.exists_of_not_isSquare : 0 < d → ¬IsSquare d → ∃ x y, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0`.
-/

namespace Math

/-- **Pell's equation for `d = 7`**, obtained from Mathlib's `Pell.exists_of_not_isSquare`. -/
theorem pell_7_of_mathlib : ∃ x y : ℤ, x ^ 2 - 7 * y ^ 2 = 1 ∧ y ≠ 0 :=
  Pell.exists_of_not_isSquare (d := 7) (by norm_num) (by decide +kernel)

end Math

/-!
# Pell 7
Category: Pure Mathematics
Target: Math.pell_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: Lean requires `import` commands to come before any other command,
including module docstrings, so the mandated header above forces this file to be
import-free. The proof is therefore fully self-contained in Lean core; a Mathlib
version of the same statement (obtained from `Pell.exists_of_not_isSquare`) is
given in `RequestProject/Pell7Mathlib.lean`.
-/

namespace Math

/-- **Pell's equation for `d = 7`.** The equation `x² - 7·y² = 1` has a nontrivial
integer solution: `(x, y) = (8, 3)`, since `64 - 63 = 1`. -/
theorem pell_7 : ∃ x y : Int, x ^ 2 - 7 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨8, 3, by decide, by decide⟩

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

