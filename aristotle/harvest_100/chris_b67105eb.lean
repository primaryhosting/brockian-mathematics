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

/-!
# Pell 5 — Mathlib variant

A second, non-constructive proof of the same statement as `Math.pell_5`,
obtained from Mathlib's general existence theorem for Pell equations,
`Pell.exists_of_not_isSquare` : for `0 < d` with `d` not a square,
`∃ x y, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0`.
-/

namespace Math

/-- `x² - 5·y² = 1` has a solution with `y ≠ 0`, via Mathlib's
`Pell.exists_of_not_isSquare` (5 is positive and not a perfect square). -/
theorem pell_5_mathlib : ∃ x y : ℤ, x ^ 2 - 5 * y ^ 2 = 1 ∧ y ≠ 0 :=
  Pell.exists_of_not_isSquare (d := 5) (by norm_num) (by decide +kernel)

end Math

/-!
# Pell 5
Category: Pure Mathematics
Target: Math.pell_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` commands to be the very first
commands in a file, so no `import Mathlib` can appear above the header comment
requested for this file. This module is therefore self-contained (core Lean
only) and its proof is fully kernel-checked. A Mathlib-based variant of the
same statement, using `Pell.exists_of_not_isSquare`, is in
`RequestProject/Pell5Mathlib.lean`.
-/

namespace Math

/-- **Pell's equation for `d = 5`.** The equation `x² - 5·y² = 1` has a
nontrivial integer solution, i.e. one with `y ≠ 0`; explicitly `(x, y) = (9, 4)`,
since `81 - 5 · 16 = 1`. -/
theorem pell_5 : ∃ x y : Int, x ^ 2 - 5 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨9, 4, by decide, by decide⟩

end Math

