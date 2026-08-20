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

lemma cross_mulVec (M : Matrix (Fin 3) (Fin 3) ℝ) (u v : Fin 3 → ℝ) :
    Mᵀ *ᵥ (crossProduct (M *ᵥ u) (M *ᵥ v)) = M.det • crossProduct u v := by
  funext i
  fin_cases i <;>
    simp [cross_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.det_fin_three] <;>
    ring

/-- Two vectors with vanishing cross product are parallel. -/
