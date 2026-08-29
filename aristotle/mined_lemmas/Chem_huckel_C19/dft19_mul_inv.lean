import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
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

open Matrix SimpleGraph

/-- A primitive 19-th root of unity. -/

theorem dft19_mul_inv : dft19 * dft19inv = 1 := by
  ext i l
  rw [Matrix.mul_apply]
  have hz : ∀ k : Fin 19,
      dft19 i k * dft19inv k l = (19 : ℂ)⁻¹ * (om ^ i.val * (om ^ l.val)⁻¹) ^ k.val := by
    intro k
    have hA : (om ^ i.val * (om ^ l.val)⁻¹) ^ k.val
        = om ^ (i.val * k.val) * (om ^ (k.val * l.val))⁻¹ := by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, Nat.mul_comm l.val k.val]
    simp only [dft19, dft19inv, Matrix.of_apply, hA]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hz k), ← Finset.mul_sum]
  set z : ℂ := om ^ i.val * (om ^ l.val)⁻¹ with hzdef
  have hsum : ∑ k : Fin 19, z ^ k.val = ∑ k ∈ Finset.range 19, z ^ k :=
    Fin.sum_univ_eq_sum_range (fun k => z ^ k) 19
  rw [hsum]
  by_cases hil : i = l
  · subst hil
    have hz1 : z = 1 := by
      rw [hzdef]
      field_simp
      exact div_self (pow_ne_zero _ om_ne_zero)
    rw [hz1]
    simp
  · have hne : z ≠ 1 := by
      rw [hzdef]
      intro h
      have hl : om ^ l.val ≠ 0 := pow_ne_zero _ om_ne_zero
      have heq : om ^ i.val = om ^ l.val := by
        field_simp at h
        exact h
      exact hil (Fin.ext (om_primitive.pow_inj i.isLt l.isLt heq))
    have hz19 : z ^ 19 = 1 := by
      have h2 : ((om ^ l.val)⁻¹) ^ 19 = 1 := by
        rw [inv_pow, om_pow_mul_19, inv_one]
      rw [hzdef, mul_pow, om_pow_mul_19, h2, one_mul]
    rw [geom_sum_eq hne, hz19]
    simp [hil]

