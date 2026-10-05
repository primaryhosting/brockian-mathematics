import Mathlib
/-!
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

/-! ## Basis states and tensor products of one-qubit operators -/

/-- A computational basis state of `n` qubits. -/
abbrev BasisState (n : ℕ) := Fin n → Bool

/-- An operator on `n` qubits, as a `2^n × 2^n` complex matrix. -/
abbrev Op (n : ℕ) := Matrix (BasisState n) (BasisState n) ℂ

/-- The tensor product `f 0 ⊗ f 1 ⊗ ⋯ ⊗ f (n-1)` of one-qubit operators. -/

lemma iPow_real_eq (c : ZMod 4) (h : (starRingEnd ℂ) (iPow c) = iPow c) :
    iPow c = ((phaseQ c : ℚ) : ℂ) := by
  have hc : ∀ d : ZMod 4, d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by decide
  rcases hc c with rfl | rfl | rfl | rfl
  · simp [phaseQ]
  · exfalso
    rw [iPow_one] at h
    simp at h
    exact Complex.I_ne_zero (by linear_combination -h / 2)
  · rw [iPow_two]
    norm_num [phaseQ, show (2 : ZMod 4) ≠ 0 by decide]
  · exfalso
    rw [iPow_three] at h
    simp at h
    exact Complex.I_ne_zero (by linear_combination h / 2)

/-- The value `⟨b| U† Zₖ U |b⟩` as computed by the classical tableau algorithm. -/
