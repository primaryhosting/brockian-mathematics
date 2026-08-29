/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators Real

namespace Chem

open Complex Finset

/-- A primitive 16-th root of unity. -/

lemma zeta_sum (b : ZMod 16) : ∑ a : ZMod 16, zeta (a * b) = if b = 0 then 16 else 0 := by
  have key : ∑ a : ZMod 16, zeta (a * b) = ∑ m ∈ Finset.range 16, zeta b ^ m := by
    have h1 : ∀ a : ZMod 16, zeta (a * b) = zeta b ^ a.val := by
      intro a
      have hc : ((a.val : ℕ) : ZMod 16) = a := ZMod.natCast_zmod_val a
      conv_lhs => rw [← hc]
      rw [zeta_natCast_mul]
    simp only [h1]
    exact Fin.sum_univ_eq_sum_range (fun m => zeta b ^ m) 16
  rw [key]
  by_cases hb : b = 0
  · subst hb; simp [zeta_zero]
  · have hz : zeta b ≠ 1 := fun h => hb ((zeta_eq_one_iff b).1 h)
    rw [geom_sum_eq hz]
    have : zeta b ^ 16 = 1 := by
      have : ((16 : ℕ) : ZMod 16) = 0 := by decide
      have h2 := zeta_natCast_mul 16 b
      rw [this, zero_mul, zeta_zero] at h2
      exact h2.symm
    simp [this, hb]

/-- The adjacency matrix of the cycle graph `C₁₆`, indexed by `ZMod 16`. -/
