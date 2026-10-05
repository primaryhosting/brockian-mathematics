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

noncomputable def dToN (D : DMachine) (sz : ℕ → ℕ) (e : (n : ℕ) → D.Conf n ↪ Fin (sz n)) :
    NMachine where
  size := sz
  init := fun n => ((e n (D.init n)) : ℕ)
  ipos := fun n i => if h : ∃ w : D.Conf n, ((e n w) : ℕ) = i then D.ipos n h.choose else 0
  step := fun n b i j => ∃ w : D.Conf n, ((e n w) : ℕ) = i ∧ ((e n (D.step n b w)) : ℕ) = j
  acc := fun n i => ∃ w : D.Conf n, ((e n w) : ℕ) = i ∧ D.acc n w
  init_lt := fun n => (e n (D.init n)).isLt
  step_lt := by
    rintro n b i j ⟨w, rfl, rfl⟩
    exact ⟨(e n w).isLt, (e n (D.step n b w)).isLt⟩

