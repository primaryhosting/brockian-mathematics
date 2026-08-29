/-!
# Pell 3
Category: Pure Mathematics
Target: Math.pell_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: this file deliberately has no `import` line, since Lean requires imports to precede
-- every other command (including module doc comments) and the header above must come first.
-- The proofs below only use `Int` arithmetic available in core Lean.

namespace Math

/-- **Pell's equation for `d = 3`.** The equation `x² - 3·y² = 1` has a nontrivial
integer solution, i.e. one with `y ≠ 0` (so `x ≠ ±1`). Witness: `(x, y) = (2, 1)`.

In Mathlib this also follows from the general theory of Pell's equation
(`Pell.exists_of_not_isSquare` / `Pell.Solution₁`), since `3` is not a square. -/

theorem pell_3_unbounded (n : Nat) :
    ∃ x y : Int, x ^ 2 - 3 * y ^ 2 = 1 ∧ 1 ≤ x ∧ (n : Int) ≤ y := by
  induction n with
  | zero => exact ⟨2, 1, by decide, by decide, by decide⟩
  | succ k ih =>
      obtain ⟨x, y, hxy, hx, hy⟩ := ih
      exact ⟨2 * x + 3 * y, x + 2 * y, pell_3_step hxy, by omega, by omega⟩

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

