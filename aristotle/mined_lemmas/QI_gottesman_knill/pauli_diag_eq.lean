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

lemma pauli_diag_eq {n : ℕ} (C : List (Gate n)) (b : BasisState n) (k : Fin n) :
    pauliMat (simulate C (pauliZ k)) b b = ((classicalExp C b k : ℚ) : ℂ) := by
  set q := simulate C (pauliZ k) with hq
  rw [pauliMat_apply, classicalExp, ← hq]
  by_cases h : ∀ j, q.x j = false
  · have hcond : ∀ j, b j = xor (b j) (q.x j) := by intro j; rw [h j]; simp
    rw [if_pos hcond, if_pos h]
    have hherm : (starRingEnd ℂ) (pauliMat q b b) = pauliMat q b b := by
      have := sim_hermitian C k
      have h2 : (pauliMat q)ᴴ b b = pauliMat q b b := by rw [this]
      simpa [Matrix.conjTranspose_apply] using h2
    rw [pauliMat_apply, if_pos hcond] at hherm
    have hs : ((sgnQ q.z b : ℚ) : ℂ) ≠ 0 := sgnQ_ne_zero _ _
    have hconj : (starRingEnd ℂ) (iPow q.ph) = iPow q.ph := by
      rw [map_mul, (by simp : (starRingEnd ℂ) ((sgnQ q.z b : ℚ) : ℂ) = ((sgnQ q.z b : ℚ) : ℂ))]
        at hherm
      exact mul_right_cancel₀ hs hherm
    rw [iPow_real_eq q.ph hconj]
    push_cast
    ring
  · have hcond : ¬ (∀ j, b j = xor (b j) (q.x j)) := by
      intro hall
      apply h
      intro j
      have := hall j
      cases hqj : q.x j
      · rfl
      · rw [hqj] at this; simp at this
    rw [if_neg hcond, if_neg h]
    simp

