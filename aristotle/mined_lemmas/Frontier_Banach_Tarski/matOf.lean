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

noncomputable def matOf (x : Fin 2 × Bool) : Matrix (Fin 3) (Fin 3) ℝ :=
  if x.2 then genMat x.1 else (genMat x.1)ᵀ

/-- The matrix of a word. -/
