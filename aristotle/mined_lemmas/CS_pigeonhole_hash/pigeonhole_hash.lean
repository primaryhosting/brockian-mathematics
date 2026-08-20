/-
# Pigeonhole Hash
Category: Computer Science
Target: CS.pigeonhole_hash
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean requires `import` to come first in a file, and a module docstring
`/-! ... -/` may not precede it. The header above is therefore rendered as a
plain block comment; the same text is repeated as a module docstring below.)
-/

import Mathlib

/-!
# Pigeonhole Hash
Category: Computer Science
Target: CS.pigeonhole_hash
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- **Pigeonhole hash**: any hash function from a set of `n + 1` keys to a set of
`n` buckets has a collision, i.e. two distinct keys mapping to the same bucket. -/

theorem pigeonhole_hash (n : ℕ) (h : Fin (n + 1) → Fin n) :
    ∃ a b : Fin (n + 1), a ≠ b ∧ h a = h b := by
  have hcard : Fintype.card (Fin n) < Fintype.card (Fin (n + 1)) := by simp
  obtain ⟨a, b, hab, hfab⟩ := Fintype.exists_ne_map_eq_of_card_lt h hcard
  exact ⟨a, b, hab, hfab⟩

/-- General form: any map from a finite type `α` to a finite type `β` with
`Fintype.card β < Fintype.card α` has a collision. -/
