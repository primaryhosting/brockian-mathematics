/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Complex Finset

namespace Chem

/-- The circulant form of the adjacency matrix of the cycle graph `C₁₁`,
with vertices indexed by `ZMod 11`. -/

theorem fourierQ_mul_fourierP : fourierQ * fourierP = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have key : ∀ k : ZMod 11, fourierQ i k * fourierP k j = (11 : ℂ)⁻¹ * ee ((j - i) * k) := by
    intro k
    simp only [fourierP, fourierQ]
    rw [show (j - i) * k = (-(i * k)) + k * j by ring, AddChar.map_add_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.mul_sum, sum_char]
  by_cases h : i = j
  · subst h; norm_num
  · have h2 : j - i ≠ 0 := sub_ne_zero_of_ne (Ne.symm h)
    simp [h2, h]

/-- The Fourier matrix, as a unit of the matrix ring. -/
