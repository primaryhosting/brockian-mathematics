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

@[simp] lemma ival_cons (x : Fin 2 × Bool) (t : List (Fin 2 × Bool)) :
    ival (x :: t) = istep x (ival t) := rfl

/-- The key `3`-adic invariant: for a nonempty reduced word, the middle coordinate is not
divisible by `3`. -/
