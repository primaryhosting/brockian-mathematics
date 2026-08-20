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

lemma rotY_mem (t : ℝ) : rotY t ∈ O3 := by
  rw [Matrix.mem_orthogonalGroup_iff]
  have h := Real.sin_sq_add_cos_sq t
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotY, Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [h]

/-- Rotation about the `y`-axis, as an element of the orthogonal group. -/
