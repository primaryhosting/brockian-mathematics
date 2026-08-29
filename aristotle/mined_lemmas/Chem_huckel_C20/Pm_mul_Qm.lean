import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Matrix Polynomial Finset

/-- A primitive 20-th root of unity. -/

lemma Pm_mul_Qm : Pm * Qm = 1 := by
  ext i l
  rw [Matrix.mul_apply]
  have hterm : ∀ k : Fin 20, Pm i k * Qm k l = (20 : ℂ)⁻¹ * ee ((i - l) * k) := by
    intro k
    simp only [Pm, Qm, Matrix.of_apply]
    rw [sub_mul, ee_sub]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum, sum_ee]
  by_cases h : i = l
  · subst h
    rw [if_pos (sub_self i), Matrix.one_apply_eq]
    norm_num
  · rw [if_neg (fun hc => h (sub_eq_zero.mp hc)), Matrix.one_apply_ne h, mul_zero]

