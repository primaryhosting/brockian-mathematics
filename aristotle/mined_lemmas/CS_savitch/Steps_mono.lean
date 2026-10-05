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

theorem Steps_mono {m m' u v : ℕ} (h : m ≤ m') (hs : Steps E m u v) : Steps E m' u v := by
  induction m' with
  | zero => exact (Nat.le_zero.mp h) ▸ hs
  | succ m' ih =>
    rcases Nat.lt_or_ge m (m' + 1) with h' | h'
    · exact Or.inl (ih (by omega))
    · have hm : m = m' + 1 := by omega
      exact hm ▸ hs

