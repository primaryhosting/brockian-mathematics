import Mathlib

/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
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

namespace QI

variable {n : ℕ}

/-- The computational basis of `n` qubits, indexed by bit strings `Fin n → Bool`. -/
abbrev Bits (n : ℕ) := Fin n → Bool

/-- The all-zeros bit string. -/

theorem hadamard_zeroState (y : Bits n) :
    hadamard (zeroState : Bits n → ℂ) y = ((Real.sqrt 2 ^ n : ℝ) : ℂ)⁻¹ := by
  unfold hadamard zeroState
  rw [Finset.sum_eq_single (zeros n)]
  · rw [phaseSign_left_zeros]
    simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The amplitude of any basis state `y` in the final state. -/
