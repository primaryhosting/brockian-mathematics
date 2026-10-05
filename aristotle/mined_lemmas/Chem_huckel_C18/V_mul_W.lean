/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Complex

namespace Chem

/-- A primitive 18-th root of unity. -/

theorem V_mul_W : V * W = 1 := by
  ext j l
  rw [Matrix.mul_apply, Matrix.one_apply]
  have key : ∀ k : Fin 18, V j k * W k l = (18 : ℂ)⁻¹ * ch (k * (j - l)) := by
    intro k
    have h1 : V j k * W k l = ch (j * k) * ((18 : ℂ)⁻¹ * ch (-(k * l))) := rfl
    rw [h1, show k * (j - l) = j * k + -(k * l) by
      rw [mul_sub, mul_comm k j, sub_eq_add_neg], ch_add]
    ring
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.mul_sum, ch_sum]
  by_cases h : j = l
  · simp [h]
  · rw [if_neg (by simpa [sub_eq_zero] using h), if_neg h]
    ring

