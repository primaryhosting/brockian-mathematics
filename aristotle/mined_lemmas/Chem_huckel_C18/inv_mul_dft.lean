import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Matrix

/-- The standard additive character `x ↦ exp (2 π i x / 18)` on `ZMod 18`. -/

lemma inv_mul_dft : dftInv * dftMat = 1 := by
  ext j k
  rw [Matrix.mul_apply]
  simp only [dftMat, dftInv, Matrix.of_apply]
  have key : ∀ i : ZMod 18, (18 : ℂ)⁻¹ * psi (-(j * i)) * psi (i * k)
      = (18 : ℂ)⁻¹ * psi ((k - j) * i) := by
    intro i
    rw [show (k - j) * i = -(j * i) + i * k by ring, AddChar.map_add_eq_mul, mul_assoc]
  rw [Finset.sum_congr rfl (fun i _ => key i), ← Finset.mul_sum, psi_sum]
  by_cases hjk : j = k
  · simp [hjk, Matrix.one_apply]
  · rw [if_neg (sub_ne_zero_of_ne (fun h => hjk h.symm)), Matrix.one_apply_ne hjk, mul_zero]

