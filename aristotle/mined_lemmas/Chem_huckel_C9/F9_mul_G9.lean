import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
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

set_option grind.warning false

namespace Chem

open Complex Matrix Polynomial

/-- A primitive ninth root of unity. -/

theorem F9_mul_G9 : F9 * G9 = 1 := by
  ext j j'
  rw [Matrix.mul_apply]
  have key : ∀ k : Fin 9, F9 j k * G9 k j' = (9:ℂ)⁻¹ * (om ^ j.val * (om ^ j'.val)⁻¹) ^ k.val := by
    intro k
    simp only [F9, G9, Matrix.of_apply]
    rw [pow_mul, mul_comm k.val j'.val, pow_mul, mul_pow, ← inv_pow]
    ring
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.mul_sum, geom_sum_om]
  by_cases h : j = j' <;> simp [h, Matrix.one_apply]

