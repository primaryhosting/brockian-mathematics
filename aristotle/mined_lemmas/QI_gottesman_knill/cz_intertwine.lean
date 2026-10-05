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

lemma cz_intertwine {n : ℕ} (k l : Fin n) (hkl : k ≠ l) (p : Pauli n) :
    gateMat (Gate.CZ k l hkl) * pauliMat (step (Gate.CZ k l hkl) p)
      = pauliMat p * gateMat (Gate.CZ k l hkl) := by
  ext a b
  have hx : (step (Gate.CZ k l hkl) p).x = p.x := rfl
  have hsgn : sgnQ (step (Gate.CZ k l hkl) p).z b
      = (if p.x k && b l then -1 else 1) * ((if p.x l && b k then -1 else 1) * sgnQ p.z b) := by
    show sgnQ (Function.update (Function.update p.z k (xor (p.z k) (p.x l))) l
      (xor (p.z l) (p.x k))) b = _
    rw [sgnQ_update, sgnQ_update, Function.update_of_ne (Ne.symm hkl)]
    congr 2
    · cases hzl : p.z l <;> cases hxk : p.x k <;> simp
    · cases hzk : p.z k <;> cases hxl : p.x l <;> simp
  have hph : iPow (step (Gate.CZ k l hkl) p).ph
      = iPow p.ph * (if p.x k && p.x l then -1 else 1) := by
    show iPow (p.ph + (if p.x k && p.x l then 2 else 0)) = _
    rw [iPow_add]
    by_cases h : p.x k && p.x l <;> simp [h, iPow_two]
  simp only [gateMat, Matrix.diagonal_mul, Matrix.mul_diagonal, pauliMat_apply, hx]
  by_cases h : ∀ j, a j = xor (b j) (p.x j)
  · rw [if_pos h, if_pos h, hsgn, hph]
    rw [h k, h l]
    push_cast
    cases hxk : p.x k <;> cases hxl : p.x l <;> cases hbk : b k <;> cases hbl : b l <;> simp
  · rw [if_neg h, if_neg h, mul_zero, zero_mul]

