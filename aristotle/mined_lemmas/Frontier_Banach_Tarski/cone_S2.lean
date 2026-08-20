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

lemma cone_S2 : cone S2 = Metric.closedBall (0 : E) 1 \ {0} := by
  ext x
  constructor
  · rintro ⟨hx0, hx1, -⟩
    exact ⟨by simpa using hx1, hx0⟩
  · rintro ⟨hx1, hx0⟩
    simp only [mem_singleton_iff] at hx0
    exact ⟨hx0, by simpa using hx1, by rw [mem_S2, norm_normalize hx0]⟩

