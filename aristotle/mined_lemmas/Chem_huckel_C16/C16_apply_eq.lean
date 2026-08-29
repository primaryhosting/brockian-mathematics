import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Finset

/-- A primitive 16-th root of unity. -/

lemma C16_apply_eq (i j : ZMod 16) :
    C16 i j = (if j = i - 1 then (1 : ℂ) else 0) + (if j = i + 1 then (1 : ℂ) else 0) := by
  have hne : (i - 1 : ZMod 16) ≠ i + 1 := by
    intro h
    have h2 : (i - 1) - i = (i + 1) - i := by rw [h]
    have h3 : (-1 : ZMod 16) = 1 := by
      have h5 : (i - 1) - i = (-1 : ZMod 16) := by ring
      have h4 : (i + 1) - i = (1 : ZMod 16) := by ring
      rw [h5, h4] at h2; exact h2
    exact absurd h3 (by decide)
  unfold C16
  by_cases h1 : j = i - 1
  · subst h1
    have e1 : i - (i - 1) = (1 : ZMod 16) := by ring
    rw [e1]
    simp [hne]
  · by_cases h2 : j = i + 1
    · subst h2
      have e2 : i - (i + 1) = (-1 : ZMod 16) := by ring
      rw [e2]
      simp [h1]
    · have hA : i - j ≠ 1 := by
        intro h; exact h1 (by rw [← h]; ring)
      have hB : i - j ≠ -1 := by
        intro h; exact h2 (by
          have h6 : j = i - (i - j) := by ring
          rw [h6, h]; ring)
      simp [hA, hB, h1, h2]

