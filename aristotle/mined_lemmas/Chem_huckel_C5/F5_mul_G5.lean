/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix

namespace Chem

/-- A primitive fifth root of unity. -/

lemma F5_mul_G5 : F5 * G5 = 1 := by
  ext i k
  simp only [Matrix.mul_apply, F5, G5, Matrix.one_apply]
  have : ∀ j : ZMod 5, e5 (i * j) * ((5 : ℂ)⁻¹ * e5 (-(j * k)))
      = (5 : ℂ)⁻¹ * e5 (j * (i - k)) := by
    intro j
    rw [show j * (i - k) = i * j + -(j * k) by ring, e5_add]
    ring
  rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.mul_sum, sum_e5]
  by_cases h : i = k
  · subst h; norm_num
  · have : i - k ≠ 0 := sub_ne_zero.mpr h
    simp [this, h]

