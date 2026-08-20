import Mathlib

/-!
# Pell 10 — Mathlib-based proof

A second, non-constructive proof of the statement `Math.pell_10` (see `RequestProject/Main.lean`),
obtained from Mathlib's general existence theorem for Pell equations,
`Pell.exists_of_not_isSquare : 0 < d → ¬IsSquare d → ∃ x y, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0`.
-/

namespace Math

/-- `10` is not a perfect square (as an integer). -/

theorem pell_10_via_mathlib : ∃ x y : ℤ, x ^ 2 - 10 * y ^ 2 = 1 ∧ y ≠ 0 :=
  Pell.exists_of_not_isSquare (by norm_num) not_isSquare_ten

end Math

/-!
# Pell 10
Category: Pure Mathematics
Target: Math.pell_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to be the very first commands in a file,
-- before any other command (including module doc comments such as the header above).
-- Since the header must literally begin this file, this module is kept import-free and the
-- proof below uses only Lean core.  A Mathlib-based proof of the same statement, obtained
-- from `Pell.exists_of_not_isSquare`, is given in `RequestProject/Pell10Mathlib.lean`.

-- The following `open scoped` commands from the project boilerplate require Mathlib and are
-- therefore disabled in this import-free module:
-- open scoped BigOperators
-- open scoped Real
-- open scoped Nat
-- open scoped Classical
-- open scoped Pointwise

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

/-- **Pell's equation for `d = 10`.**  The equation `x² − 10·y² = 1` has a nontrivial integer
solution, i.e. one with `y ≠ 0`.  Witness: `(x, y) = (19, 6)`, since `19² − 10·6² = 361 − 360 = 1`.
-/
