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

lemma single_qubit_intertwine {n : ℕ} (k : Fin n) (G : Matrix Bool Bool ℂ) (p : Pauli n)
    (d : ZMod 4) (x' z' : Bool)
    (hG : iPow d • (G * p1 x' z') = p1 (p.x k) (p.z k) * G) :
    tens (Function.update (fun _ => 1) k G) *
        pauliMat ⟨p.ph + d, Function.update p.x k x', Function.update p.z k z'⟩
      = pauliMat p * tens (Function.update (fun _ => 1) k G) := by
  set F : Fin n → Matrix Bool Bool ℂ := fun j => p1 (p.x j) (p.z j) with hF
  have hleft : (fun j => (Function.update (fun _ => (1 : Matrix Bool Bool ℂ)) k G) j *
      p1 ((Function.update p.x k x') j) ((Function.update p.z k z') j))
      = Function.update F k (G * p1 x' z') := by
    funext j
    by_cases hj : j = k
    · subst hj; simp [Function.update_self, hF]
    · simp [Function.update_of_ne hj, hF]
  have hright : (fun j => p1 (p.x j) (p.z j) *
      (Function.update (fun _ => (1 : Matrix Bool Bool ℂ)) k G) j)
      = Function.update F k (p1 (p.x k) (p.z k) * G) := by
    funext j
    by_cases hj : j = k
    · subst hj; simp [Function.update_self, hF]
    · simp [Function.update_of_ne hj, hF]
  simp only [pauliMat, Matrix.mul_smul, Matrix.smul_mul, tens_mul, hleft, hright, iPow_add]
  rw [← hG, tens_update_smul, smul_smul]

