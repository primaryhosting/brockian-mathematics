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

theorem Frontier.Banach_Tarski :
    ∃ f g : Equidecomp BT.E BT.Isom,
      f.source ⊆ Metric.closedBall 0 1 ∧ g.source ⊆ Metric.closedBall 0 1 ∧
        Disjoint f.source g.source ∧
        f.target = Metric.closedBall 0 1 ∧ g.target = Metric.closedBall 0 1 :=
  BT.ball_paradoxical

import RequestProject.Space

/-!
# A free group of rotations of `ℝ³`

The two rotations by `arccos (1/3)` about the `z`-axis and the `x`-axis generate a free group
of rank two. The proof is the classical `3`-adic argument: a nonempty reduced word applied to
the vector `(0, √2, 0)` has the form `(p, q√2, r)/3ᵏ` with `q` not divisible by `3`.
-/

open Matrix Set Function

namespace BT

/-- Rotation by `arccos (1/3)` about the `z`-axis. -/
