import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real
open Complex Matrix

namespace Chem

/-- A primitive 19-th root of unity. -/

lemma F_mul_G : F19 * G19 = 1 := by
  ext i k
  rw [Matrix.mul_apply]
  set z : ℂ := omega19 ^ i.val * (omega19 ^ k.val)⁻¹ with hzdef
  have hterm : ∀ j : Fin 19, F19 i j * G19 j k = (19 : ℂ)⁻¹ * z ^ (j : ℕ) := by
    intro j
    simp only [F19, G19, Matrix.of_apply, hzdef]
    rw [mul_pow, ← inv_pow, ← pow_mul, ← pow_mul, mul_comm k.val j.val]
    ring
  have hz19 : z ^ 19 = 1 := by
    have hwi : (omega19⁻¹) ^ 19 = 1 := by rw [inv_pow, omega19_pow, inv_one]
    rw [hzdef, ← inv_pow, mul_pow, pow_pow_19 _ omega19_pow, pow_pow_19 _ hwi, one_mul]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum, sum_pow_val z hz19]
  by_cases hik : i = k
  · subst hik
    have hz1 : z = 1 := by
      rw [hzdef, mul_inv_cancel₀ (pow_ne_zero _ omega19_ne_zero)]
    rw [if_pos hz1, Matrix.one_apply_eq]
    field_simp
  · have hz1 : z ≠ 1 := by
      intro h
      rw [hzdef, mul_inv_eq_one₀ (pow_ne_zero _ omega19_ne_zero)] at h
      exact hik (Fin.ext (isPrimitiveRoot_omega19.pow_inj i.isLt k.isLt h))
    rw [if_neg hz1, mul_zero, Matrix.one_apply_ne hik]

