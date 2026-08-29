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

theorem isChain_push {A G : Frame} {rest : List Frame} (hA : G.k = A.k + 1)
    (h : List.IsChain (fun a b : Frame => b.k = a.k + 1) (G :: rest)) :
    List.IsChain (fun a b : Frame => b.k = a.k + 1) (A :: G :: rest) := by
  rw [List.isChain_cons]
  refine ⟨?_, h⟩
  intro y hy
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
  exact hy ▸ hA

