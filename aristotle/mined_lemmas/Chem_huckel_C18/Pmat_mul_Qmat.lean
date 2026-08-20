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

theorem Pmat_mul_Qmat : Pmat * Qmat = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have : ∀ k : ZMod 18, Pmat j k * Qmat k l = (18 : ℂ)⁻¹ * wch (k * (j - l)) := by
    intro k
    simp only [Pmat, Qmat]
    rw [← mul_assoc, mul_comm (wch (j * k)) ((18:ℂ)⁻¹), mul_assoc, ← wch_add]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun k _ => this k), ← Finset.mul_sum, sum_wch]
  by_cases h : j = l
  · subst h; simp
  · rw [if_neg (by simpa [sub_eq_zero] using h)]
    simp [h]

