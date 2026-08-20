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

private lemma oracle_state (f : Bool → Bool) (p : Bool × Bool) :
    oracle f (hadamard₂ (hadamard₁ initial)) p = sgn (f p.1) * sgn p.2 / 2 := by
  obtain ⟨x, y⟩ := p
  simp only [oracle, h2_h1_initial]
  cases y <;> cases hfx : f x <;> simp

/-- The amplitudes of the final state on the basis states with first qubit `0`. -/
