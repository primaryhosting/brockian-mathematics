import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Finset Matrix

namespace Chem

/-- The adjacency matrix of the cycle graph `C₁₁`, with vertices indexed by `ZMod 11`:
vertex `i` is adjacent to `i + 1` and `i - 1`. -/

lemma F_mul_G : F * G = (11 : ℂ) • (1 : Matrix (ZMod 11) (ZMod 11) ℂ) := by
  ext i j
  rw [Matrix.mul_apply]
  have : ∀ k : ZMod 11, F i k * G k j = ch ((i - j) * k) := by
    intro k
    rw [F, G, ← ch_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun k _ => this k), sum_ch_mul]
  by_cases h : i = j
  · simp [h]
  · have : i - j ≠ 0 := sub_ne_zero_of_ne h
    simp [this, h]

