/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a module docstring: Lean 4 requires `import` lines to come
first, so the very first comment of the file cannot be a module docstring.)

This file develops space bounded machines, proves Savitch's theorem
`NSPACE f ⊆ DSPACE (f ^ 2)` and deduces `PSPACE = NPSPACE`.
-/

set_option autoImplicit false

namespace CS

/-! ## Languages -/

/-- A language is a predicate on binary strings. -/
abbrev Language := List Bool → Prop

/-- The bit of `x` at position `i` (`false` beyond the end of `x`). -/

theorem Steps_add {a b u v : ℕ} :
    Steps E (a + b) u v ↔ ∃ w, Steps E a u w ∧ Steps E b w v := by
  induction b generalizing v with
  | zero => simp [Steps]
  | succ b ih =>
    constructor
    · rintro (h | ⟨z, hz, hzv⟩)
      · obtain ⟨w, hw1, hw2⟩ := ih.1 h
        exact ⟨w, hw1, Or.inl hw2⟩
      · obtain ⟨w, hw1, hw2⟩ := ih.1 hz
        exact ⟨w, hw1, Or.inr ⟨z, hw2, hzv⟩⟩
    · rintro ⟨w, hw1, (h2 | ⟨z, hz1, hz2⟩)⟩
      · exact Or.inl (ih.2 ⟨w, hw1, h2⟩)
      · exact Or.inr ⟨z, ih.2 ⟨w, hw1, hz1⟩, hz2⟩

