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

lemma punctured_ball_paradoxical : Paradoxical O3 (closedBall (0 : E) 1 \ {0}) := by
  rw [← cone_S2]
  exact paradoxical_cone sphere_paradoxical subset_rfl

/-- Finally the centre is absorbed by a screw motion (a rotation about an axis missing the
centre), so the full closed unit ball is paradoxical for the isometry group. -/
