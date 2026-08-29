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

theorem savitch_init_valid (M : NMachine) (s : ℕ → ℕ) (n : ℕ) :
    SValid (M.size n) (s n + 1)
      ((none, [⟨M.init n, M.size n, s n + 1, 0, false⟩]) : SState) := by
  refine ⟨by simp, ?_⟩
  intro F hF
  simp only [List.mem_singleton] at hF
  subst hF
  exact ⟨le_rfl, (M.init_lt n).le, le_rfl, Nat.zero_le _⟩

/-- The deterministic machine simulating `M` by the recursive midpoint search. -/
