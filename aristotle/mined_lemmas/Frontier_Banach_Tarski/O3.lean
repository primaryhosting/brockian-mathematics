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

lemma O3.toIsom_smul (M : O3) (x : E) : (O3.toIsom M) • x = M • x := rfl

end BT

import RequestProject.Space

/-!
# Fixed points of a rotation

A nontrivial rotation of `ℝ³` (an orthogonal matrix of determinant one) fixes only the two
points where its axis meets the unit sphere. In particular its fixed points on the sphere
form a countable (indeed, finite) set.
-/

open Matrix Set Function

namespace BT

