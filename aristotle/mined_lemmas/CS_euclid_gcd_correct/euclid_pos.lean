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

namespace CS

/-- Euclid's algorithm, by repeated remainder.  The recursion is on the second
argument, which strictly decreases (`a % (b+1) < b+1`); Lean accepts the
definition precisely because this measure is well founded, so the algorithm
terminates on every input. -/

theorem euclid_pos (a b : Nat) (hb : b ≠ 0) : euclid a b = euclid b (a % b) := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  exact euclid_succ a c

/-- **Termination**: `euclid` is a total function on `ℕ × ℕ`, and each recursive
call strictly decreases the second argument, hence the algorithm halts. -/
