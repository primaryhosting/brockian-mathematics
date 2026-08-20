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

theorem leftSepSeq_notMem_closure (Y : Type u) [TopologicalSpace Y] [Nonempty Y]
    (hns : ¬ SeparableSpace Y) {a : Ordinal.{u}} (ha : a < (Cardinal.aleph 1).ord) :
    leftSepSeq Y a ∉ closure (leftSepSeq Y '' Set.Iio a) := by
  haveI : Countable (Set.Iio a) := (countable_Iio_of_lt_ord_aleph_one ha).to_subtype
  have hex : ∃ x : Y, x ∉ closure (Set.range (fun b : Set.Iio a => leftSepSeq Y b.1)) := by
    by_contra hall
    push_neg at hall
    refine hns ⟨⟨Set.range (fun b : Set.Iio a => leftSepSeq Y b.1), Set.countable_range _, ?_⟩⟩
    exact dense_iff_closure_eq.mpr (Set.eq_univ_of_forall hall)
  have himg : leftSepSeq Y '' Set.Iio a = Set.range (fun b : Set.Iio a => leftSepSeq Y b.1) := by
    rw [Set.image_eq_range]
  rw [himg, leftSepSeq_def Y a, dif_pos hex]
  exact hex.choose_spec

/-- **Left-separated `ω₁`-sequence.**  Every non-separable topological space admits an injective
`ω₁`-sequence of points, each lying outside the closure of its predecessors.  Applied to a Suslin
line this is the skeleton of the classical construction of a Suslin tree. -/
