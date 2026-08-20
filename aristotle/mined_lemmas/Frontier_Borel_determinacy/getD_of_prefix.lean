import Mathlib
/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

universe u

namespace Frontier

variable {X : Type u}

/-- A strategy assigns a move to every finite position of the game. -/
abbrev Strategy (X : Type u) := List X → X

/-- The move played at position `q`: player I (resp. II) moves at positions of
even (resp. odd) length. -/

theorem getD_of_prefix {l₁ l₂ : List X} (h : l₁ <+: l₂) {k : ℕ} (hk : k < l₁.length)
    (d : X) : l₁.getD k d = l₂.getD k d := by
  rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ (hk.trans_le h.length_le),
    h.getElem hk]

omit [Nonempty X] in
