/-
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above repeats verbatim as a module docstring below; Lean 4 does not allow a
-- module docstring to precede the `import` commands.)

import Mathlib

/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

universe u

/-! ## Infinite two-player games on sequences -/

/-- A strategy is a map from the finite history of moves played so far to the next move. -/

lemma isOpen_of_isOpenSeq {S : Set (ℕ → A)} (hS : IsOpenSeq S) : IsOpen S := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨n, hn⟩ := hS x hx
  exact ⟨{y | hist y n = hist x n}, fun y hy => hn y hy, isOpen_cylinder x n, rfl⟩

/-- For a discrete alphabet, `IsOpenSeq` is exactly openness in the product topology. -/
