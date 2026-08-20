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

@[simp] private lemma h1_initial_true (x : Bool) :
    hadamard₁ initial (x, true) = 1 / (Real.sqrt 2 : ℝ) := by
  cases x <;> simp [hadamard₁, initial]

/-- After `H ⊗ H` the register is in the state `(|0⟩+|1⟩)(|0⟩-|1⟩)/2`. -/
