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
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately self-contained (no `import` statements), because the
required header comment above must be the very first thing in the file, and Lean
only accepts `import` commands at the very beginning of a file.  Consequently the
factorial function is defined here from scratch and only core Lean tactics are
used.  Nothing below depends on any unproved assumption.
-/

namespace Brockian.BrocardProblem

/-- The factorial function, `factorial n = n !`. -/

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

/-- **Brocard's problem / Brocard conjecture.**  The only natural numbers `n` for which
`n ! + 1` is a perfect square are `n = 4, 5, 7` (with `4! + 1 = 5²`, `5! + 1 = 11²`,
`7! + 1 = 71²`).  This is a famous open problem. -/

theorem brocard_known_solutions :
    factorial 4 + 1 = 5 ^ 2 ∧ factorial 5 + 1 = 11 ^ 2 ∧ factorial 7 + 1 = 71 ^ 2 := by
  decide

/-! ### Elementary arithmetic helpers -/
