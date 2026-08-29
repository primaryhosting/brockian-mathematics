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

lemma gate_intertwine {n : ℕ} (g : Gate n) (p : Pauli n) :
    gateMat g * pauliMat (step g p) = pauliMat p * gateMat g := by
  match g with
  | Gate.H k =>
      exact single_qubit_intertwine k mH p _ _ _ (mH_conj (p.x k) (p.z k))
  | Gate.S k =>
      have h := single_qubit_intertwine k mS p (if p.x k then 3 else 0) (p.x k)
        (xor (p.z k) (p.x k)) (by
          have := mS_conj (p.x k) (p.z k)
          simpa [Bool.xor_comm] using this)
      simpa [gateMat, step, Function.update_eq_self_iff] using h
  | Gate.CZ k l hkl => exact cz_intertwine k l hkl p

/-- A one-qubit unitary tensored with identities is unitary. -/
