/-
Basic theory of "almost equality" (equality off a finite set) of functions
`Ordinal → ℕ` below a given ordinal, used in the construction of an Aronszajn tree.
-/
import Mathlib

open Cardinal Ordinal Set

namespace Aronszajn

/-- `AlmostEq a f g` means that `f` and `g` agree at all but finitely many `ξ < a`. -/

theorem almostEq_of_eqOn (hfg : ∀ ξ < a, f ξ = g ξ) : AlmostEq a f g := by
  have : {ξ : Ordinal.{0} | ξ < a ∧ f ξ ≠ g ξ} = ∅ := by
    ext ξ; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2⟩; exact h2 (hfg ξ h1)
  rw [AlmostEq, this]; exact Set.finite_empty

