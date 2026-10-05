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

open Matrix Polynomial

namespace Chem

/-- A primitive 11-th root of unity. -/

theorem C11adj_apply (i j : Fin 11) :
    C11adj i j = (if i = j - 1 then 1 else 0) + (if i = j + 1 then 1 else 0) := by
  have hd1 : ∀ i j : Fin 11, (j = i + 1) ↔ (i = j - 1) := by decide
  have hd2 : ∀ j : Fin 11, (j - 1 : Fin 11) ≠ j + 1 := by decide
  rcases eq_or_ne i (j - 1) with h1 | h1
  · have h2 : i ≠ j + 1 := by rw [h1]; exact hd2 j
    have h3 : j = i + 1 := (hd1 i j).mpr h1
    simp [C11adj, h1, h2, h3]
  · rcases eq_or_ne i (j + 1) with h2 | h2
    · have h3 : ¬ (j = i + 1) := fun h => h1 ((hd1 i j).mp h)
      simp [C11adj, h1, h2, h3]
    · have h3 : ¬ (j = i + 1) := fun h => h1 ((hd1 i j).mp h)
      simp [C11adj, h1, h2, h3]

