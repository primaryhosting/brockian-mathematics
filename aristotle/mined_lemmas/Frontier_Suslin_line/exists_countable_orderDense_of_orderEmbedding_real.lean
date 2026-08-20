import Mathlib

/-!
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
## Suslin's problem

Cantor characterised the real line as (up to order isomorphism) the unique
nonempty separable dense linear order without endpoints that is complete.
*Suslin's problem* asks whether "separable" may be weakened to the
**countable chain condition** (ccc): every family of pairwise disjoint nonempty
open sets is countable.  Separability implies ccc (`Frontier.isCcc_of_separable`
below), so the question is whether the two conditions coincide for dense linear
orders.

A **Suslin line** is a counterexample: a nontrivial dense linear order without
endpoints, carrying the order topology, which is ccc but *not* separable.
**Suslin's Hypothesis** (`Frontier.SuslinHypothesis`) is the statement that no
Suslin line exists.

Suslin's Hypothesis is independent of ZFC: Jensen's diamond principle `◊`
(which holds in Gödel's constructible universe `L`) implies that a Suslin line
exists, while `MA_{ℵ₁} + ¬CH` implies that none does.  Consequently the
phrasing "a Suslin line exists iff ◊-type hypotheses fail" is *not* a theorem —
both `◊` and its failure are consistent with the existence of a Suslin line
being false, and the existence of a Suslin line is simply not decided by ZFC
(so, in particular, it is not provably equivalent to any ZFC-refutable or
ZFC-provable statement).  What can be established inside Lean/ZFC is the precise
formulation of the problem together with the ZFC-provable reductions; those are
what is proved here, in `Frontier.Suslin_line`:

* separability implies ccc, so a Suslin line, if any, is a genuine gap between
  the two conditions;
* the real line is not a Suslin line;
* a Suslin line is uncountable, is not second countable, and is not order
  isomorphic to `ℝ`;
* Suslin's Hypothesis is equivalent to the assertion that every ccc dense
  linear order without endpoints (with the order topology) is separable.
-/

namespace Frontier

open TopologicalSpace

/-- The **countable chain condition**: every family of pairwise disjoint
nonempty open sets is countable. -/

theorem exists_countable_orderDense_of_orderEmbedding_real (α : Type*) [LinearOrder α]
    [Nonempty α] [DenselyOrdered α] (f : α ↪o ℝ) :
    ∃ D : Set α, D.Countable ∧ ∀ x y : α, x < y → ∃ d ∈ D, x < d ∧ d < y := by
  set A : ℚ × ℚ → Set α := fun pq => {x : α | (pq.1 : ℝ) < f x ∧ f x < (pq.2 : ℝ)}
  have hchoice : ∀ pq : ℚ × ℚ, ∃ x : α, (A pq).Nonempty → x ∈ A pq := by
    intro pq
    by_cases h : (A pq).Nonempty
    · exact ⟨h.choose, fun _ => h.choose_spec⟩
    · exact ⟨Classical.arbitrary α, fun hc => absurd hc h⟩
  choose g hg using hchoice
  refine ⟨Set.range g, Set.countable_range g, ?_⟩
  intro x y hxy
  obtain ⟨z, hxz, hzy⟩ := exists_between hxy
  obtain ⟨w, hxw, hwz⟩ := exists_between hxz
  obtain ⟨v, hzv, hvy⟩ := exists_between hzy
  obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (f.lt_iff_lt.mpr hwz)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (f.lt_iff_lt.mpr hzv)
  have hne : (A (p, q)).Nonempty := ⟨z, hp2, hq1⟩
  have hmem := hg (p, q) hne
  obtain ⟨h1, h2⟩ := hmem
  refine ⟨g (p, q), Set.mem_range_self _, ?_, ?_⟩
  · exact hxw.trans (f.lt_iff_lt.mp (hp1.trans h1))
  · exact (f.lt_iff_lt.mp (h2.trans hq2)).trans hvy

/-- A nontrivial densely ordered space with the order topology that order-embeds into `ℝ`
is separable. -/
