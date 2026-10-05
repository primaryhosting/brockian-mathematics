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
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately self-contained (no `import` at all), so that the header comment
above can literally be the first thing in the file: Lean requires `import` commands to precede
any other syntax, including module documentation.  Consequently the factorial function is
defined here from scratch rather than taken from Mathlib.
-/

namespace Brockian.BrocardGap

/-- The factorial function, `factorial n = n !`. -/

theorem eq_four_or_five_or_seven_of_le_seven {n : Nat} (hn : n ≤ 7) (h : IsBrocardIndex n) :
    n = 4 ∨ n = 5 ∨ n = 7 := by
  match n, hn, h with
  | 0, _, h => exact absurd h not_isBrocardIndex_zero
  | 1, _, h => exact absurd h not_isBrocardIndex_one
  | 2, _, h => exact absurd h not_isBrocardIndex_two
  | 3, _, h => exact absurd h not_isBrocardIndex_three
  | 4, _, _ => exact Or.inl rfl
  | 5, _, _ => exact Or.inr (Or.inl rfl)
  | 6, _, h => exact absurd h not_isBrocardIndex_six
  | 7, _, _ => exact Or.inr (Or.inr rfl)
  | (k + 8), hn, _ => exact absurd hn (by omega)

/-- The (currently open) arithmetic input to the gap conjecture: Brocard's equation
`n ! + 1 = m ^ 2` has no solution with `n ≥ 8`. -/
