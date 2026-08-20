import Mathlib

/-!
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Frontier

open Set TopologicalSpace

universe u

/-- The **countable chain condition** (ccc): every family of pairwise disjoint nonempty open
sets is countable. -/

theorem countable_Iio_of_lt_ord_aleph_one {a : Ordinal.{u}} (ha : a < (Cardinal.aleph 1).ord) :
    (Set.Iio a).Countable := by
  rw [Cardinal.countable_iff_lt_aleph_one, Ordinal.mk_Iio_ordinal]
  have h := Cardinal.lt_ord.mp ha
  calc Cardinal.lift.{u + 1, u} a.card
      < Cardinal.lift.{u + 1, u} (Cardinal.aleph 1) := Cardinal.lift_lt.mpr h
    _ = Cardinal.aleph 1 := by simp

/-- In a non-separable space the recursion never gets stuck: each `leftSepSeq Y a` with `a < ω₁`
lies outside the closure of its predecessors. -/
