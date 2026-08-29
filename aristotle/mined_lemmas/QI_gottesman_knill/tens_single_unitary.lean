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

lemma tens_single_unitary {n : ℕ} (k : Fin n) (G : Matrix Bool Bool ℂ) (hG : Gᴴ * G = 1) :
    (tens (Function.update (fun _ => 1) k G))ᴴ * tens (Function.update (fun _ => 1) k G)
      = (1 : Op n) := by
  rw [tens_conjTranspose, tens_mul]
  have h : (fun j => ((Function.update (fun _ => (1 : Matrix Bool Bool ℂ)) k G) j)ᴴ *
      (Function.update (fun _ => (1 : Matrix Bool Bool ℂ)) k G) j)
      = fun _ : Fin n => (1 : Matrix Bool Bool ℂ) := by
    funext j
    by_cases hj : j = k
    · subst hj; simpa using hG
    · simp [Function.update_of_ne hj]
  rw [h, tens_one]

