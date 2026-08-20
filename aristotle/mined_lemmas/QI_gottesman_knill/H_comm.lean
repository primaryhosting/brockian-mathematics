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

lemma H_comm {n : ℕ} (i : Fin n) (P : Pauli n) :
    P.toMat * gateMat (Gate.H i) = gateMat (Gate.H i) * (stepPauli (Gate.H i) P).toMat := by
  simp only [gateMat, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    Pauli.toMat_mul, Xp_mul, mul_Xp, Zp_mul, mul_Zp]
  congr 1
  rcases zmod2_cases (P.xs i) with ha | ha <;> rcases zmod2_cases (P.zs i) with hb | hb <;>
    simp only [stepPauli]
  · have e1 : Function.update P.xs i (P.zs i) = P.xs := update_same' _ _ _ (by rw [ha, hb])
    have e2 : Function.update P.zs i (P.xs i) = P.zs := update_same' _ _ _ (by rw [ha, hb])
    rw [e1, e2, ha, hb]
    simp only [dbl_zero, add_zero, mul_zero, add_comm (unitVec i)]
  · have e1 : Function.update P.xs i (P.zs i) = P.xs + unitVec i :=
      update_flip _ _ _ (by rw [ha, hb]; decide)
    have e2 : Function.update P.zs i (P.xs i) = P.zs + unitVec i :=
      update_flip _ _ _ (by rw [ha, hb]; decide)
    rw [e1, e2, ha, hb]
    simp only [dbl_zero, dbl_one, zero_mul, add_zero, Pi.add_apply, unitVec_self, ha,
      bits_add_self_cancel, add_comm (unitVec i), zero_add]
    abel
  · have e1 : Function.update P.xs i (P.zs i) = P.xs + unitVec i :=
      update_flip _ _ _ (by rw [ha, hb]; decide)
    have e2 : Function.update P.zs i (P.xs i) = P.zs + unitVec i :=
      update_flip _ _ _ (by rw [ha, hb]; decide)
    rw [e1, e2, ha, hb]
    simp only [dbl_zero, mul_zero, add_zero, Pi.add_apply, unitVec_self, ha,
      bits_add_self_cancel, show (1 + 1 : ZMod 2) = 0 from by decide, add_comm (unitVec i)]
    abel
  · have e1 : Function.update P.xs i (P.zs i) = P.xs := update_same' _ _ _ (by rw [ha, hb])
    have e2 : Function.update P.zs i (P.xs i) = P.zs := update_same' _ _ _ (by rw [ha, hb])
    rw [e1, e2, ha, hb]
    simp only [dbl_one, one_mul, add_assoc, show (2 : ZMod 4) + 2 = 0 from by decide, add_zero,
      add_comm (unitVec i)]

/-- The phase gate is unitary. -/
