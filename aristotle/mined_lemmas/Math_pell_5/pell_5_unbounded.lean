/-!
# Pell 5
Category: Pure Mathematics
Target: Math.pell_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the required header comment above is a module docstring, which Lean requires to be the
-- very first thing in the file; `import` commands may not follow it.  The proof below therefore
-- uses no imports at all (plain Lean 4 core suffices).  The original `import Mathlib` line and the
-- Mathlib-only `open scoped ...` lines are kept here, commented out, for reference:
--   import Mathlib
--   open scoped BigOperators
--   open scoped Real
--   open scoped Nat
--   open scoped Classical
--   open scoped Pointwise

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

/-- **Pell's equation for `d = 5`.**  The equation `x² - 5·y² = 1` has a nontrivial integer
solution, i.e. one with `y ≠ 0` (equivalently `x ≠ ±1`).  Witness: `(x, y) = (9, 4)`, since
`81 - 5 · 16 = 1`. -/

theorem pell_5_unbounded (n : Nat) :
    ∃ x y : Int, x ^ 2 - 5 * y ^ 2 = 1 ∧ 0 < x ∧ (n : Int) < y := by
  induction n with
  | zero => exact ⟨9, 4, by decide, by decide, by decide⟩
  | succ k ih =>
    obtain ⟨x, y, hxy, hx, hy⟩ := ih
    refine ⟨9 * x + 20 * y, 4 * x + 9 * y, pell_5_step hxy, by omega, by omega⟩

end Math

