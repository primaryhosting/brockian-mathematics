import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

open Matrix Polynomial

namespace Chem

/-! ## A primitive tenth root of unity and the associated additive character -/

/-- A primitive `10`-th root of unity. -/

lemma dftMat_mul_dftMatInv : dftMat * dftMatInv = 1 := by
  ext j k
  rw [Matrix.mul_apply]
  simp only [dftMat, dftMatInv, Matrix.of_apply]
  have hterm : ∀ l : ZMod 10,
      chi (j * l) * ((10 : ℂ)⁻¹ * chi (-(l * k))) = (10 : ℂ)⁻¹ * chi (l * (j - k)) := by
    intro l
    rw [show l * (j - k) = j * l + -(l * k) by ring, AddChar.map_add_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun l _ => hterm l), ← Finset.mul_sum,
    AddChar.sum_mulShift _ chi_isPrimitive]
  by_cases h : j = k
  · subst h
    simp
  · rw [Matrix.one_apply_ne h]
    simp [sub_eq_zero, h]

