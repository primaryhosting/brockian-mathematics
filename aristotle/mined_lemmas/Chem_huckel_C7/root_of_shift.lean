import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- Adjacency matrix of the cycle graph `C₇`, with vertices indexed by `ZMod 7`:
vertex `i` is adjacent to `i + 1` and to `i - 1`. -/

lemma root_of_shift {y : ℂ} {u : ZMod 7 → ℂ} (hu : u ≠ 0) (h : ∀ i, u (i + 1) = y * u i) :
    y ^ 7 = 1 := by
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hu (funext hc)
  have h7 := shift_iter h 7 i
  have hz : ((7 : ℕ) : ZMod 7) = 0 := by decide
  rw [hz, add_zero] at h7
  field_simp at h7
  exact h7.symm

/-- `ζ⁷ᵏ + ζ⁷⁻ᵏ = 2 cos (2πk/7)`. -/
