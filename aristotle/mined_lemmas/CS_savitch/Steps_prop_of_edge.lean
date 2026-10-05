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

theorem Steps_prop_of_edge {P : ℕ → Prop} (hE : ∀ a b, E a b → P b) {m u v : ℕ}
    (hu : P u) (h : Steps E m u v) : P v := by
  induction m generalizing v with
  | zero => exact h ▸ hu
  | succ m ih =>
    rcases h with h | ⟨w, _, hw⟩
    · exact ih h
    · exact hE _ _ hw

