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

lemma poles_countable : poles.Countable := by
  have hsub : poles ⊆ ⋃ w : FreeGroup (Fin 2), {x : E | ‖x‖ = 1 ∧ Phi w • x = x ∧ w ≠ 1} := by
    rintro x ⟨hx1, w, hw, hfix⟩
    exact Set.mem_iUnion.2 ⟨w, hx1, hfix, hw⟩
  refine Set.Countable.mono hsub (Set.countable_iUnion fun w => ?_)
  by_cases hw : w = 1
  · have h : {x : E | ‖x‖ = 1 ∧ Phi w • x = x ∧ w ≠ 1} = ∅ := by
      ext x; simp [hw]
    rw [h]; exact Set.countable_empty
  · refine Set.Countable.mono ?_ (countable_fixed (Phi w) (Phi_det w) (Phi_ne_one hw))
    exact fun x hx => ⟨hx.1, hx.2.1⟩

/-- No pole lies on the `y`-axis: the two points `±e₂` are not fixed by any nontrivial
element of the free group. -/
