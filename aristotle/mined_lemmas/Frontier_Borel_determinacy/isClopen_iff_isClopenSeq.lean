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

lemma isClopen_iff_isClopenSeq {S : Set (ℕ → A)} : IsClopen S ↔ IsClopenSeq S := by
  constructor
  · intro h
    exact ⟨isOpenSeq_of_isOpen h.2, isOpenSeq_of_isOpen h.1.isOpen_compl⟩
  · intro h
    refine ⟨?_, isOpen_of_isOpenSeq h.1⟩
    rw [← isOpen_compl_iff]
    exact isOpen_of_isOpenSeq h.2

end Topology

/-! ## The Gale–Stewart theorem: open games are determined -/

section GaleStewart

variable [Inhabited A]

