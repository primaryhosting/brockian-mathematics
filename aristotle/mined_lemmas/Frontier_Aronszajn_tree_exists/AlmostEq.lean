/-
Basic theory of "almost equality" (equality off a finite set) of functions
`Ordinal → ℕ` below a given ordinal, used in the construction of an Aronszajn tree.
-/
import Mathlib

open Cardinal Ordinal Set

namespace Aronszajn

/-- `AlmostEq a f g` means that `f` and `g` agree at all but finitely many `ξ < a`. -/

theorem AlmostEq.coinfinite (hfg : AlmostEq a f g) (hg : (g '' Set.Iio a)ᶜ.Infinite) :
    (f '' Set.Iio a)ᶜ.Infinite := by
  obtain ⟨F, hF, hsub⟩ := hfg.image_subset_union
  refine Set.Infinite.mono ?_ (hg.diff hF)
  intro n hn
  simp only [Set.mem_diff, Set.mem_compl_iff] at hn
  simp only [Set.mem_compl_iff]
  intro hmem
  rcases hsub hmem with h1 | h1
  · exact hn.1 h1
  · exact hn.2 h1

