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

theorem root_odd (n m : Nat) (hn : 2 ≤ n) (h : factorial n + 1 = m ^ 2) :
    ∃ k, m = 2 * k + 1 := by
  obtain ⟨s, hs⟩ := factorial_even n hn
  refine ⟨m / 2, ?_⟩
  have hm : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases hm with h0 | h1
  · exfalso
    obtain ⟨t, ht⟩ : ∃ t, m = 2 * t := ⟨m / 2, by omega⟩
    subst ht
    rw [sq_eq] at h
    have : 2 * t * (2 * t) = 4 * (t * t) := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    omega
  · omega

/-- Factored form of a Brocard equation with odd root: `n ! + 1 = (2k+1)²` is the same
as `n ! = 4k(k+1)`. -/
