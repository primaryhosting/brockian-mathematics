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

lemma S_comm {n : ℕ} (i : Fin n) (P : Pauli n) :
    P.toMat * gateMat (Gate.S i) = gateMat (Gate.S i) * (stepPauli (Gate.S i) P).toMat := by
  simp only [gateMat, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Matrix.one_mul, Pauli.toMat_mul, Zp_mul, mul_Zp, stepPauli]
  rcases zmod2_cases (P.xs i) with ha | ha
  · have e2 : Function.update P.zs i (P.zs i + P.xs i) = P.zs :=
      update_same' _ _ _ (by rw [ha, add_zero])
    rw [e2, ha]
    simp only [if_true, add_zero, dbl_zero, add_comm (unitVec i)]
  · have e2 : Function.update P.zs i (P.zs i + P.xs i) = P.zs + unitVec i :=
      update_flip _ _ _ (by rw [ha])
    rw [e2, ha]
    simp only [if_neg (by decide : ¬ (1 : ZMod 2) = 0), dbl_one,
      add_comm (unitVec i), unitVec_add_self, add_zero, add_assoc,
      show (3 : ZMod 4) + 2 = 1 from by decide]
    rw [Pauli.toMat_phase P.ph 3, Pauli.toMat_phase P.ph 1, iPowC_three, iPowC_one,
      smul_smul, smul_smul]
    have c1 : (1 + Complex.I) / 2 * -Complex.I = (1 - Complex.I) / 2 := by
      linear_combination (-1/2 : ℂ) * Complex.I_sq
    have c2 : (1 - Complex.I) / 2 * Complex.I = (1 + Complex.I) / 2 := by
      linear_combination (-1/2 : ℂ) * Complex.I_sq
    rw [c1, c2]
    module

/-! ### CNOT -/

