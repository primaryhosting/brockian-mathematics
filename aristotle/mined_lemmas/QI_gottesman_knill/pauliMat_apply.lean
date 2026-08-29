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

lemma pauliMat_apply {n : ℕ} (p : Pauli n) (a b : BasisState n) :
    pauliMat p a b =
      if (∀ j, a j = xor (b j) (p.x j)) then iPow p.ph * ((sgnQ p.z b : ℚ) : ℂ) else 0 := by
  have hprod : ∀ j : Fin n, p1 (p.x j) (p.z j) (a j) (b j)
      = (if a j = xor (b j) (p.x j) then 1 else 0) * (if p.z j && b j then (-1 : ℂ) else 1) :=
    fun j => p1_apply _ _ _ _
  simp only [pauliMat, Matrix.smul_apply, smul_eq_mul, tens_apply, hprod]
  rw [Finset.prod_mul_distrib]
  by_cases h : ∀ j, a j = xor (b j) (p.x j)
  · rw [if_pos h]
    have h1 : (∏ j, if a j = xor (b j) (p.x j) then (1 : ℂ) else 0) = 1 :=
      Finset.prod_eq_one (fun j _ => by rw [if_pos (h j)])
    rw [h1, one_mul]
    congr 1
    simp only [sgnQ, Rat.cast_prod]
    exact Finset.prod_congr rfl (fun j _ => by by_cases hz : p.z j && b j <;> simp [hz])
  · rw [if_neg h]
    push_neg at h
    obtain ⟨j, hj⟩ := h
    have : (∏ j, if a j = xor (b j) (p.x j) then (1 : ℂ) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by rw [if_neg hj])
    rw [this, zero_mul, mul_zero]

/-! ## Clifford gates -/

/-- The generating Clifford gates: Hadamard, phase, and controlled-`Z`. -/
inductive Gate (n : ℕ)
  | H (k : Fin n) : Gate n
  | S (k : Fin n) : Gate n
  | CZ (k l : Fin n) (h : k ≠ l) : Gate n

/-- The unitary matrix of a gate. -/
