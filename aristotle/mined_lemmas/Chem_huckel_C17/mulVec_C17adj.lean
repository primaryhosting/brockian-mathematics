/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Complex

/-! ### A primitive 17-th root of unity and the associated additive character -/

/-- A primitive 17-th root of unity. -/

lemma mulVec_C17adj (v : ZMod 17 → ℂ) (i : ZMod 17) :
    (C17adj *ᵥ v) i = v (i - 1) + v (i + 1) := by
  have hne : (i - 1 : ZMod 17) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 17) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  have hlt : ∀ j : ZMod 17, (i - j = 1) ↔ (j = i - 1) := by
    intro j
    constructor
    · intro h; rw [← h]; ring
    · intro h; subst h; ring
  have hgt : ∀ j : ZMod 17, (j - i = 1) ↔ (j = i + 1) := by
    intro j
    constructor
    · intro h; rw [← h]; ring
    · intro h; subst h; ring
  have key : ∀ j : ZMod 17, C17adj i j * v j
      = (if j = i - 1 then v j else 0) + (if j = i + 1 then v j else 0) := by
    intro j
    simp only [C17adj, Matrix.of_apply, hlt, hgt]
    by_cases h1 : j = i - 1
    · subst h1; simp [hne]
    · by_cases h2 : j = i + 1
      · subst h2; simp [h1]
      · simp [h1, h2]
  simp only [Matrix.mulVec, dotProduct, key]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

/-! ### The Hückel eigenvalues -/

/-- The `k`-th Hückel eigenvalue of `C₁₇`: `2 cos (2πk/17)`. -/
