import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Real Matrix Finset

namespace Chem

/-- A primitive 10-th root of unity. -/

theorem C10F_mul_C10G : C10F * C10G = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have h : ∀ k : ZMod 10, C10F i k * C10G k j = chi (k * (i - j)) / 10 := by
    intro k
    rw [C10F, C10G]
    simp only [Matrix.of_apply]
    rw [mul_div_assoc', ← chi_add]
    congr 2
    ring
  simp only [h, ← Finset.sum_div, sum_chi]
  by_cases hij : i = j
  · subst hij
    simp
  · have : i - j ≠ 0 := sub_ne_zero_of_ne hij
    simp [this, hij]

