import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix

/-- A primitive 17-th root of unity. -/

lemma U17_mul_V17 : U17 * V17 = 1 := by
  ext j l
  have hentry : ∀ k : ZMod 17, U17 j k * V17 k l = (17 : ℂ)⁻¹ * ee (k * (j - l)) := by
    intro k
    have : ee (j * k) * ee (-(l * k)) = ee (k * (j - l)) := by
      rw [← ee_add]; ring_nf
    simp only [U17, V17]
    rw [← this]; ring
  rw [Matrix.mul_apply, Finset.sum_congr rfl (fun k _ => hentry k), ← Finset.mul_sum,
    sum_ee_mul]
  by_cases h : j = l
  · subst h; simp [Matrix.one_apply_eq]
  · have hne : j - l ≠ 0 := sub_ne_zero_of_ne h
    simp [hne, h]

