import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset SimpleGraph

/-- A primitive 15-th root of unity. -/

lemma Pm_mul_Qm : Pm * Qm = 1 := by
  ext i l
  rw [Matrix.mul_apply]
  have hterm : ∀ j : Fin 15, Pm i j * Qm j l = (15 : ℂ)⁻¹ * (g i * (g l)⁻¹) ^ (j.val) := by
    intro j
    simp only [Pm, Qm, Matrix.of_apply]
    rw [mul_pow, inv_pow]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun j => (g i * (g l)⁻¹) ^ j) 15, Matrix.one_apply]
  by_cases h : i = l
  · subst h
    rw [mul_inv_cancel₀ (g_ne_zero i)]
    simp
  · have hx : g i * (g l)⁻¹ ≠ 1 := by
      intro hx
      exact h (g_injective (mul_inv_eq_one₀ (g_ne_zero l) |>.mp hx))
    have hx15 : (g i * (g l)⁻¹) ^ 15 = 1 := by
      rw [mul_pow, inv_pow, g_pow_fifteen, g_pow_fifteen, inv_one, mul_one]
    rw [geom_sum_eq hx, hx15]
    simp [h]

