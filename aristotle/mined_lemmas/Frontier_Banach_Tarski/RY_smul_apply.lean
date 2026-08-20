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

lemma RY_smul_apply (t : ℝ) (x : E) :
    ((RY t • x) 0 = Real.cos t * x 0 + Real.sin t * x 2) ∧
    ((RY t • x) 2 = -(Real.sin t) * x 0 + Real.cos t * x 2) := by
  constructor <;>
    simp [O3.smul_apply, rotY, Fin.sum_univ_three]

/-- A rotation about the `y`-axis fixing a point off the `y`-axis is trivial. -/
