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

theorem Phi_det (w : FreeGroup (Fin 2)) :
    ((Phi w : O3) : Matrix (Fin 3) (Fin 3) ℝ).det = 1 := by
  have hmat : ((Phi w : O3) : Matrix (Fin 3) (Fin 3) ℝ) = matWord w.toWord := by
    conv_lhs => rw [← FreeGroup.mk_toWord (x := w)]
    exact coe_Phi_mk _
  rw [hmat]
  induction w.toWord with
  | nil => simp
  | cons x t ih =>
      rw [matWord_cons, Matrix.det_mul, ih, mul_one]
      rcases x with ⟨i, b⟩
      cases b <;> simp [matOf, det_genMat, Matrix.det_transpose]

end BT

import RequestProject.Space

/-!
# Rotations about the `y`-axis, and absorbing a countable set

Given a countable set `D` of points of `ℝ³` none of which lies on the `y`-axis, there is a
rotation `R` about the `y`-axis such that the sets `Rⁿ D` (`n ≥ 1`) are all disjoint from `D`.
-/

open Matrix Set Function Pointwise

namespace BT

/-- Rotation by the angle `t` about the `y`-axis. -/
