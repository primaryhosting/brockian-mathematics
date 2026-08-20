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

lemma coe_Phi_mk (L : List (Fin 2 × Bool)) :
    ((Phi (FreeGroup.mk L) : O3) : Matrix (Fin 3) (Fin 3) ℝ) = matWord L := by
  induction L with
  | nil =>
      show ((Phi 1 : O3) : Matrix (Fin 3) (Fin 3) ℝ) = matWord []
      rw [map_one, matWord_nil]
      rfl
  | cons x t ih =>
      have hsplit : FreeGroup.mk (x :: t) = FreeGroup.mk [x] * FreeGroup.mk t := by
        rw [FreeGroup.mul_mk]; rfl
      rw [hsplit, map_mul, Submonoid.coe_mul, ih, matWord_cons]
      congr 1
      rcases x with ⟨i, b⟩
      cases b <;> simp [Phi, FreeGroup.lift_mk, gen, matOf, star_genMat]

/-- The second standard basis vector of `ℝ³`. -/
