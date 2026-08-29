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
# Collatz Conjecture
Category: Brockian Conjecture
Target: Brockian.CollatzPartial.CollatzConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file deliberately has no `import` line: the required header above is a module
docstring, and Lean requires all imports to precede any command, including module
docstrings.  Everything below therefore uses only core Lean 4 (no Mathlib), which
is sufficient for the development.
-/

set_option autoImplicit false

namespace Brockian.CollatzPartial

/-- One step of the Collatz map: `n ↦ n / 2` for even `n`, `n ↦ 3 * n + 1` for odd `n`. -/

theorem descent_even {n : Nat} (hn : 1 < n) (h : n % 2 = 0) :
    ∃ k, 0 < k ∧ iter k n < n := by
  refine ⟨1, by omega, ?_⟩
  rw [iter_one, collatz_even h]
  omega

/-- Unconditional descent for `n ≡ 1 (mod 4)`: three steps strictly decrease such an `n > 1`. -/
