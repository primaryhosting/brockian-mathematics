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

theorem chain_length_aux {K : ℕ} : ∀ (l : List Frame) (F : Frame),
    List.IsChain (fun a b : Frame => b.k = a.k + 1) (F :: l) → (∀ G ∈ F :: l, G.k ≤ K) →
      (F :: l).length + F.k ≤ K + 1 := by
  intro l
  induction l with
  | nil =>
    intro F _ hall
    have := hall F (by simp)
    simp
    omega
  | cons G l ih =>
    intro F hchain hall
    rw [List.isChain_cons] at hchain
    have hGk : G.k = F.k + 1 := hchain.1 G (by simp)
    have := ih G hchain.2 (fun H hH => hall H (List.mem_cons_of_mem _ hH))
    simp only [List.length_cons] at this ⊢
    omega

