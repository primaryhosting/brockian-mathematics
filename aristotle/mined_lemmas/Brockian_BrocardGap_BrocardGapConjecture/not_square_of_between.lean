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

theorem not_square_of_between {k a : Nat} (h1 : a ^ 2 < k) (h2 : k < (a + 1) ^ 2) :
    ¬ ∃ m : Nat, k = m ^ 2 := by
  intro ⟨m, hm⟩
  subst hm
  have ha : a + 1 ≤ m := by
    match Nat.lt_or_ge a m with
    | Or.inl h => exact h
    | Or.inr h => exact absurd h1 (Nat.not_lt.mpr (Nat.pow_le_pow_left h 2))
  exact absurd h2 (Nat.not_lt.mpr (Nat.pow_le_pow_left ha 2))

/-- Convenience wrapper: `n ! + 1 = k` and `k` strictly between consecutive squares
implies `n` is not a Brocard index. -/
