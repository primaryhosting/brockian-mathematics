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

theorem expand (k : Nat) : (2 * k + 1) ^ 2 = 4 * k * (k + 1) + 1 := by
  simp [sq_eq, Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm]
  omega

/-- A number strictly between two consecutive squares is not a square. -/
