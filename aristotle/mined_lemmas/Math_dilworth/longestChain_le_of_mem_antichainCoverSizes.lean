/-
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the required header is
-- reproduced verbatim as a module docstring immediately after the import below.)

import Mathlib

/-!
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

namespace Math

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- The length of a longest chain in a finite poset. -/

theorem longestChain_le_of_mem_antichainCoverSizes {n : ℕ}
    (hn : n ∈ antichainCoverSizes α) : longestChain α ≤ n := by
  obtain ⟨C, hcard, hanti, hcover⟩ := hn
  refine Finset.sup_le ?_
  intro s hs
  simp only [Set.mem_toFinset, Set.mem_setOf_eq] at hs
  choose g hgC hgmem using hcover
  have hinj : Set.InjOn g ↑s := by
    intro x hx y hy hxy
    by_contra hne
    rcases hs hx hy hne with h | h
    · exact hanti _ (hgC x) (hgmem x) (by rw [hxy]; exact hgmem y) hne h
    · exact hanti _ (hgC y) (hgmem y) (by rw [← hxy]; exact hgmem x) (Ne.symm hne) h
  calc s.card = (s.image g).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ C.card := Finset.card_le_card (by
        intro t ht
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ht
        exact hgC x)
    _ ≤ n := hcard

/-- **Mirsky's theorem** (the dual of Dilworth's theorem): in a finite poset, the minimum
number of antichains needed to cover the poset equals the size of a longest chain. -/
