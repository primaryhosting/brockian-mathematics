/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Polynomial Finset

noncomputable section

/-- A primitive 18-th root of unity. -/

theorem sum_wch (c : ZMod 18) : ∑ k : ZMod 18, wch (k * c) = if c = 0 then 18 else 0 := by
  have hrange : ∑ k : ZMod 18, wch (k * c) = ∑ n ∈ Finset.range 18, wch ((n : ZMod 18) * c) := by
    refine Finset.sum_nbij' (fun (k : ZMod 18) => k.val) (fun (n : ℕ) => (n : ZMod 18))
      ?_ ?_ ?_ ?_ ?_
    · intro a _; simp [ZMod.val_lt]
    · intro a _; simp
    · intro a _; simp
    · intro a ha; simp only [Finset.mem_range] at ha; exact ZMod.val_natCast_of_lt ha
    · intro a _; rw [ZMod.natCast_zmod_val]
  rw [hrange]
  simp only [wch_natCast_mul]
  by_cases hc : c = 0
  · subst hc; simp [wch]
  · rw [if_neg hc]
    have h1 : wch c ≠ 1 := wch_ne_one hc
    have h18 : wch c ^ 18 = 1 := by
      rw [wch, ← pow_mul, mul_comm, pow_mul, zeta_pow_18, one_pow]
    rw [geom_sum_eq h1, h18]
    simp

