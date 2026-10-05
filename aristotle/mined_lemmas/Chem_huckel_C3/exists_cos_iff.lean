/-
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

/-- The adjacency matrix of the cycle graph `C₃` (every pair of distinct vertices
is adjacent). In Hückel theory this is the (shifted, scaled) Hamiltonian of the
cyclic three-carbon π-system. -/

lemma exists_cos_iff (μ : ℝ) :
    (∃ k : Fin 3, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 3)) ↔ (μ = 2 ∨ μ = -1) := by
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k
    · left; norm_num
    · right; simpa using cos_one
    · right; simpa using cos_two
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by simpa using cos_one.symm⟩

