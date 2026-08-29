/-
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Ordinal Cardinal Set

namespace Aronszajn

/-! ## Cofinal `ω`-sequences in countable limit ordinals -/

/-- `c` is a nondecreasing `ω`-indexed sequence, starting at `0`, cofinal in `l`. -/

theorem level_countable (α : Ordinal) : {s : Node | s.len = α}.Countable := by
  rcases lt_or_ge α ω₁ with hα | hα
  · refine Set.MapsTo.countable_of_injOn (f := dev)
      (t := {A : Set (Ordinal × ℕ) | A.Finite ∧ A ⊆ Set.Iio α ×ˢ (Set.univ : Set ℕ)}) ?_ ?_ ?_
    · intro s hs
      refine ⟨s.fn_coh.image _, ?_⟩
      rintro p ⟨ξ, ⟨h1, -⟩, rfl⟩
      exact ⟨by simpa [Set.mem_setOf_eq] using (hs ▸ h1 : ξ < α), trivial⟩
    · intro s hs t ht hdev
      exact eq_of_dev_eq (by rw [hs, ht]) hdev
    · exact Set.countable_setOf_finite_subset
        ((countable_Iio_of_lt_omega1 hα).prod Set.countable_univ)
  · have : {s : Node | s.len = α} = ∅ := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact absurd (h ▸ s.len_lt) (not_lt.mpr hα)
    rw [this]
    exact Set.countable_empty

/-! ## Chains are countable -/

open Classical in
/-- The union of a chain of nodes, as a function. -/
