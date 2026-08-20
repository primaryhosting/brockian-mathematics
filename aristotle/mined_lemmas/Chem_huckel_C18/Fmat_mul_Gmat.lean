import Mathlib
/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix

/-- The adjacency matrix of the cycle graph `C₁₈`, with vertices indexed by `ZMod 18`:
two vertices are adjacent iff they differ by `1` modulo `18`. -/

lemma Fmat_mul_Gmat : Fmat * Gmat = 1 := by
  ext i l
  simp only [Matrix.mul_apply, Fmat, Gmat, Matrix.of_apply]
  have hterm : ∀ k : ZMod 18,
      w (i * k) * ((18 : ℂ)⁻¹ * w (-(k * l))) = (18 : ℂ)⁻¹ * w (k * (i - l)) := by
    intro k
    rw [show k * (i - l) = i * k + -(k * l) by ring, w_add]
    ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.mul_sum, w_sum]
  rw [Matrix.one_apply]
  by_cases h : i = l
  · simp [h]
  · have : i - l ≠ 0 := sub_ne_zero_of_ne h
    simp [this, h]

