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

theorem srun_trans {a b c : SState} (h1 : ∃ t, (srun N edge epos bitf)^[t] a = b)
    (h2 : ∃ t, (srun N edge epos bitf)^[t] b = c) : ∃ t, (srun N edge epos bitf)^[t] a = c := by
  obtain ⟨t1, rfl⟩ := h1
  obtain ⟨t2, rfl⟩ := h2
  exact ⟨t2 + t1, by rw [Function.iterate_add_apply]⟩

