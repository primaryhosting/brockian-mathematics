import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

open Complex Polynomial Matrix

/-- A primitive 15-th root of unity. -/

lemma dft_mul_inv : dftMat * dftInv = 1 := by
  ext j k
  rw [Matrix.mul_apply]
  have hterm : ∀ l : Fin 15, dftMat j l * dftInv l k = (15 : ℂ)⁻¹ * zeta (l * (j - k)) := by
    intro l
    simp only [dftMat, dftInv, Matrix.of_apply]
    rw [show l * (j - k) = j * l + -(l * k) by
      rw [mul_sub, sub_eq_add_neg, mul_comm l j], zeta_add]
    ring
  rw [Finset.sum_congr rfl fun l _ => hterm l, ← Finset.mul_sum, sum_zeta]
  by_cases h : j = k
  · subst h
    simp
  · have hjk : j - k ≠ 0 := sub_ne_zero_of_ne h
    simp [hjk, h]

