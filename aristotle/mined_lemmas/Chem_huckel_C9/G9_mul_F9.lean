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

theorem G9_mul_F9 : G9 * F9 = 1 := by
  ext k k'
  rw [Matrix.mul_apply]
  have key : ∀ j : Fin 9, G9 k j * F9 j k' = (9:ℂ)⁻¹ * (om ^ k'.val * (om ^ k.val)⁻¹) ^ j.val := by
    intro j
    simp only [F9, G9, Matrix.of_apply]
    rw [mul_comm k.val j.val, pow_mul, pow_mul, mul_pow, ← inv_pow]
    ring
  rw [Finset.sum_congr rfl (fun j _ => key j), ← Finset.mul_sum, geom_sum_om]
  by_cases h : k = k' <;> simp [h, Matrix.one_apply, eq_comm]

/-- The unit given by the Fourier matrix. -/
