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

theorem matWord_mulVec (L : List (Fin 2 × Bool)) :
    matWord L *ᵥ ![0, Real.sqrt 2, 0] =
      ((3 : ℝ) ^ L.length)⁻¹ •
        ![((ival L).1 : ℝ), ((ival L).2.1 : ℝ) * Real.sqrt 2, ((ival L).2.2 : ℝ)] := by
  induction L with
  | nil =>
      ext k
      fin_cases k <;> simp
  | cons x t ih =>
      rw [matWord_cons, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, matOf_mulVec, smul_smul,
        ival_cons, List.length_cons]
      congr 1
      rw [pow_succ]
      field_simp

