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

theorem Steps_mono_rel {E' : ℕ → ℕ → Prop} (hEE : ∀ a b, E a b → E' a b) {m u v : ℕ}
    (h : Steps E m u v) : Steps E' m u v := by
  induction m generalizing v with
  | zero => exact h
  | succ m ih =>
    rcases h with h | ⟨w, hw, hwv⟩
    · exact Or.inl (ih h)
    · exact Or.inr ⟨w, ih hw, hEE _ _ hwv⟩

