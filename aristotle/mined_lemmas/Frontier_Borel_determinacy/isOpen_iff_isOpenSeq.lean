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

lemma isOpen_iff_isOpenSeq {S : Set (ℕ → A)} : IsOpen S ↔ IsOpenSeq S :=
  ⟨isOpenSeq_of_isOpen, isOpen_of_isOpenSeq⟩

/-- For a discrete alphabet, `IsClopenSeq` is exactly clopenness in the product topology. -/
