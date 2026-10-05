/-
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Phys

/-- Shannon entropy (in nats) of a finitely supported probability vector `p`.
Terms with `p x = 0` contribute `0`, since `Real.log 0 = 0`. -/

theorem shannonEntropy_eq_zero_of_isDeterministic {α : Type*} [Fintype α] [DecidableEq α]
    {q : α → ℝ} (hq : IsDeterministic q) : shannonEntropy q = 0 := by
  obtain ⟨x₀, hx₀⟩ := hq
  unfold shannonEntropy
  refine Finset.sum_eq_zero ?_
  intro x _
  rcases eq_or_ne x x₀ with h | h
  · rw [hx₀ x, if_pos h]; simp
  · rw [hx₀ x, if_neg h]; simp

/-- The uniform distribution on a two-state system (a bit) has Shannon entropy `log 2`. -/
