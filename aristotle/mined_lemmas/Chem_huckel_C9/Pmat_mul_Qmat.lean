import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

noncomputable section

/-- A primitive 9-th root of unity. -/

lemma Pmat_mul_Qmat : Pmat * Qmat = (9 : ℂ) • (1 : Matrix (ZMod 9) (ZMod 9) ℂ) := by
  ext i l
  rw [Matrix.mul_apply]
  have hterm : ∀ j : ZMod 9, Pmat i j * Qmat j l = ee ((i - l) * j) := by
    intro j
    simp only [Pmat, Qmat, Matrix.of_apply, ← ee_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), sum_ee]
  by_cases h : i = l
  · simp [h]
  · have hsub : i - l ≠ 0 := sub_ne_zero_of_ne h
    simp [hsub, h]

