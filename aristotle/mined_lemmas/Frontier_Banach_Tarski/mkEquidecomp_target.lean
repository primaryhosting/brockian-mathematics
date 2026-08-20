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

@[simp] lemma mkEquidecomp_target (f : X → X) (A B : Set X) (S : Finset G)
    (hd : Equidecomp.IsDecompOn f A S) (hb : BijOn f A B) :
    (mkEquidecomp f A B S hd hb).target = B := rfl

/-- `A` is `G`-paradoxical: it contains two disjoint subsets, each of which is
equidecomposable (using the group `G`) with all of `A`. -/
