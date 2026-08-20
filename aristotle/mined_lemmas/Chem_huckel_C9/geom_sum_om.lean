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

theorem geom_sum_om (a b : Fin 9) :
    ∑ k : Fin 9, (om ^ a.val * (om ^ b.val)⁻¹) ^ k.val = if a = b then (9 : ℂ) else 0 := by
  have hpow9 : ∀ c : ℕ, (om ^ c) ^ 9 = 1 := by
    intro c; rw [← pow_mul, mul_comm, pow_mul, om_pow_nine, one_pow]
  by_cases h : a = b
  · subst h
    rw [mul_inv_cancel₀ (pow_ne_zero _ om_ne_zero)]
    simp
  · have hne : om ^ a.val * (om ^ b.val)⁻¹ ≠ 1 := by
      intro hc
      rw [mul_inv_eq_one₀ (pow_ne_zero _ om_ne_zero)] at hc
      exact h (Fin.ext (om_primitive.pow_inj a.isLt b.isLt hc))
    have hz9 : (om ^ a.val * (om ^ b.val)⁻¹) ^ 9 = 1 := by
      rw [mul_pow, hpow9, inv_pow, hpow9, inv_one, mul_one]
    rw [if_neg h, Fin.sum_univ_eq_sum_range (fun k => (om ^ a.val * (om ^ b.val)⁻¹) ^ k) 9,
      geom_sum_eq hne, hz9]
    simp

