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

lemma norm_e2 : ‖e2‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_three]

/-- No nontrivial word of the free group fixes `(0,1,0)`. -/
