import Mathlib

/-!
# Deutsch Correct
Category: Quantum Computing
Target: QC.deutsch_correct
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

set_option grind.warning false

namespace QC

/-- A state of a two–qubit register: a complex amplitude for each computational
basis state `|x y⟩`, `x y : Bool`. -/
abbrev State := Bool × Bool → ℂ

/-- The sign `(-1)^b`. -/

theorem deutsch_balanced_iff (f : Bool → Bool) :
    probZero f = 0 ↔ f false ≠ f true := by
  rw [deutsch_correct]
  cases hf0 : f false <;> cases hf1 : f true <;> simp

/-- Sanity check: the final state is a unit vector, i.e. the two measurement
outcomes for the first qubit have probabilities summing to `1`. -/
