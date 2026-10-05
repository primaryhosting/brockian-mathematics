/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Matrix

namespace Chem

/-- The adjacency matrix (Hückel matrix with `α = 0`, `β = 1`) of the cycle graph `C₄`. -/

lemma range_cosEig : Set.range cosEig = {2, 0, -2} := by
  ext r
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k
    · exact Or.inl cosEig_zero
    · exact Or.inr (Or.inl cosEig_one)
    · exact Or.inr (Or.inr cosEig_two)
    · exact Or.inr (Or.inl cosEig_three)
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, cosEig_zero⟩
    · exact ⟨1, cosEig_one⟩
    · exact ⟨2, cosEig_two⟩

/-! ### The characteristic determinant -/

set_option maxRecDepth 4000 in
