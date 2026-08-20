import Mathlib

/-!
# Abstract machinery for paradoxical decompositions

This file develops the general theory needed for the Banach–Tarski paradox, on top of
Mathlib's `Equidecomp` (equidecompositions for a group action).
-/

open Set Function Pointwise

namespace BT

variable {X G H : Type*} [Nonempty X] [Group G] [MulAction G X]

/-- Build an equidecomposition out of a function which is a bijection from `A` to `B` and
moves every point of `A` by an element of a fixed finite set of group elements. -/

lemma sphere_paradoxical : Paradoxical O3 S2 := by
  obtain ⟨t, ht⟩ := exists_rotY_disjoint poles poles_countable poles_off_axis
  have hsub : ∀ n : ℕ, ((RY t ^ n) • poles : Set E) ⊆ S2 := by
    rintro n y ⟨x, hx, rfl⟩
    show ‖(RY t ^ n) • x‖ = 1
    rw [O3.norm_smul]; exact hx.1
  obtain ⟨e, hes, het⟩ := exists_equidecomp_sdiff (A := S2) (D := poles) (RY t) hsub ht
  exact Paradoxical.of_equidecomp e.symm het hes sphere_sdiff_poles_paradoxical

/-- Radial extension: the punctured closed unit ball is paradoxical. -/
