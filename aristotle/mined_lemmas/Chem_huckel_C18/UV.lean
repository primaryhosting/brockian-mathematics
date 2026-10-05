import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Real Matrix Finset

/-- A primitive 18-th root of unity. -/

lemma UV : U * V = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have h : ∀ k : ZMod 18, U j k * V k l = (18 : ℂ)⁻¹ * ee (k * (j - l)) := by
    intro k
    simp only [U, V, Matrix.of_apply]
    rw [show k * (j - l) = j * k + -(k * l) by ring, ee_add]
    ring
  rw [Finset.sum_congr rfl (fun k _ => h k), ← Finset.mul_sum, ee_sum]
  by_cases hjl : j = l
  · simp [hjl, Matrix.one_apply]
  · have : j - l ≠ 0 := sub_ne_zero_of_ne hjl
    simp [this, Matrix.one_apply, hjl]

