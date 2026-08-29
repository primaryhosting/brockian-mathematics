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

theorem reflTransGen_iff_steps {u v : ℕ} :
    Relation.ReflTransGen E u v ↔ ∃ m, Steps E m u v := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail hab hbc ih =>
      obtain ⟨m, hm⟩ := ih
      exact ⟨m + 1, Or.inr ⟨_, hm, hbc⟩⟩
  · rintro ⟨m, hm⟩
    induction m generalizing v with
    | zero => exact hm ▸ Relation.ReflTransGen.refl
    | succ m ih =>
      rcases hm with h | ⟨w, hw, hwv⟩
      · exact ih h
      · exact (ih hw).tail hwv

/-- Saturation: in a graph whose edges land in `{0,…,N}`, any reachability is witnessed by a
walk of length at most `N + 1`. -/
