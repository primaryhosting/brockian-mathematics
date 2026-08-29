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

lemma iPow_one : iPow 1 = Complex.I := by simp [iPow, show (1 : ZMod 4).val = 1 from rfl]

/-! ## Pauli operators on `n` qubits -/

/-- A Pauli operator on `n` qubits: the phase `i^ph` times `⨂ⱼ X^{xⱼ} Z^{zⱼ}`. -/
structure Pauli (n : ℕ) where
  /-- The power of `i` in front of the operator. -/
  ph : ZMod 4
  /-- The `X`-part. -/
  x : BasisState n
  /-- The `Z`-part. -/
  z : BasisState n

/-- The matrix of a Pauli operator. -/
