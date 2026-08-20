/-
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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
open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-! ## Bit strings and phases -/

/-- The computational basis of `n` qubits is indexed by bit strings `Fin n → ZMod 2`. -/
abbrev Bits (n : ℕ) := Fin n → ZMod 2

/-- The `𝔽₂`-valued inner product of two bit strings. -/

lemma H_mul_H {n : ℕ} (i : Fin n) : gateMat (Gate.H i) * gateMat (Gate.H i) = 1 := by
  have hXX : (Xp i).mul (Xp i) = (⟨0, 0, 0⟩ : Pauli n) := by
    rw [mul_Xp]; simp [Xp, unitVec_add_self, dbl]
  have hZZ : (Zp i).mul (Zp i) = (⟨0, 0, 0⟩ : Pauli n) := by
    rw [mul_Zp]; simp [Zp, unitVec_add_self]
  have hXZ : (Xp i).mul (Zp i) = (⟨0, unitVec i, unitVec i⟩ : Pauli n) := by
    simp [mul_Zp, Xp]
  have hZX : (Zp i).mul (Xp i) = (⟨0 + 2, unitVec i, unitVec i⟩ : Pauli n) := by
    simp [mul_Xp, Zp, unitVec_self, dbl]
  simp only [gateMat, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    Pauli.toMat_mul, hXX, hZZ, hXZ, hZX, Pauli.toMat_one]
  rw [Pauli.toMat_phase 0 2, iPowC_two, smul_add, smul_smul, smul_smul, sqrt_two_inv_sq]
  module

/-- Heisenberg update for the Hadamard gate, in commuted form. -/
