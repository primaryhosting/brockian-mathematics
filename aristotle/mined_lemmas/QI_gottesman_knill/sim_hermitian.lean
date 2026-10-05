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

lemma sim_hermitian {n : ℕ} (C : List (Gate n)) (k : Fin n) :
    (pauliMat (simulate C (pauliZ k)))ᴴ = pauliMat (simulate C (pauliZ k)) := by
  rw [← conj_pauliZ C k]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    pauliZ_mat_hermitian, Matrix.mul_assoc]

/-- The diagonal entry of the evolved Pauli is the rational number computed classically. -/
