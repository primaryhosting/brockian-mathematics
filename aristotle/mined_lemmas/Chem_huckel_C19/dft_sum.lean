/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Matrix Complex SimpleGraph Finset

namespace Chem

/-- The primitive 19-th root of unity `exp (2πi/19)`. -/

lemma dft_sum (a b : Fin 19) :
    ∑ j : Fin 19, zeta ^ (a.val * j.val) * (zeta ^ (j.val * b.val))⁻¹ =
      if a = b then (19 : ℂ) else 0 := by
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = zeta ^ a.val * (zeta ^ b.val)⁻¹ := ⟨_, rfl⟩
  have hterm : ∀ j : Fin 19, zeta ^ (a.val * j.val) * (zeta ^ (j.val * b.val))⁻¹ = w ^ j.val := by
    intro j
    have h1 : w ^ j.val = (zeta ^ a.val) ^ j.val * ((zeta ^ b.val) ^ j.val)⁻¹ := by
      rw [hw, mul_pow, inv_pow]
    rw [h1, ← pow_mul, ← pow_mul, mul_comm b.val j.val]
  have hw19 : w ^ 19 = 1 := by
    have h1 : w ^ 19 = (zeta ^ a.val) ^ 19 * ((zeta ^ b.val) ^ 19)⁻¹ := by
      rw [hw, mul_pow, inv_pow]
    rw [h1, ← pow_mul, ← pow_mul, mul_comm a.val 19, mul_comm b.val 19, pow_mul, pow_mul,
      zeta_pow_19, one_pow, one_pow, inv_one, mul_one]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Fin.sum_univ_eq_sum_range (fun i => w ^ i) 19]
  by_cases hab : a = b
  · subst hab
    have hw1 : w = 1 := by rw [hw, mul_inv_cancel₀ (zeta_pow_ne_zero a.val)]
    simp [hw1]
  · have hwne : w ≠ 1 := by
      intro h
      apply hab
      rw [hw, mul_inv_eq_one₀ (zeta_pow_ne_zero b.val)] at h
      exact Fin.ext (zeta_primitive.pow_inj a.isLt b.isLt h)
    rw [geom_sum_eq hwne, hw19]
    simp [hab]

