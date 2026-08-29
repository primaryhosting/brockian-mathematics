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

theorem isChain_cons_replace {F G : Frame} {rest : List Frame} (hk : G.k = F.k)
    (h : List.IsChain (fun a b : Frame => b.k = a.k + 1) (F :: rest)) :
    List.IsChain (fun a b : Frame => b.k = a.k + 1) (G :: rest) := by
  rw [List.isChain_cons] at h ⊢
  exact ⟨fun y hy => by rw [hk]; exact h.1 y hy, h.2⟩

/-- Pushing a frame one level below the current top preserves the chain condition. -/
