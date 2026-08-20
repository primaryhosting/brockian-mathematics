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

@[simp] lemma coe_gen (i : Fin 2) : ((gen i : O3) : Matrix (Fin 3) (Fin 3) ℝ) = genMat i := rfl

/-- The homomorphism from the free group of rank two into the rotation group. -/
