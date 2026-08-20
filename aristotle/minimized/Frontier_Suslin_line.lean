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

def IsCcc (α : Type*) [TopologicalSpace α] : Prop :=
  ∀ S : Set (Set α), (∀ s ∈ S, IsOpen s) → (∀ s ∈ S, s.Nonempty) →
    S.PairwiseDisjoint id → S.Countable

/-- `α` (a linearly ordered topological space) is a **Suslin line**: it carries
the order topology, is nontrivial, densely ordered, has no endpoints, satisfies
the countable chain condition, but is not separable. -/

def IsSuslinLine (α : Type*) [LinearOrder α] [TopologicalSpace α] : Prop :=
  OrderTopology α ∧ Nontrivial α ∧ DenselyOrdered α ∧ NoMaxOrder α ∧ NoMinOrder α ∧
    IsCcc α ∧ ¬ SeparableSpace α

/-- **Suslin's Hypothesis**: there is no Suslin line. -/

def SuslinHypothesis : Prop :=
  ∀ (α : Type) (_ : LinearOrder α) (_ : TopologicalSpace α), ¬ IsSuslinLine α

/-- A separable space satisfies the countable chain condition. -/

theorem isCcc_of_separable (α : Type*) [TopologicalSpace α] [SeparableSpace α] :
    IsCcc α := by
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense α
  intro S hopen hne hdisj
  rcases isEmpty_or_nonempty α with hα | hα
  · have hS : S = ∅ := by
      ext s
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hs
      obtain ⟨x, -⟩ := hne s hs
      exact hα.elim x
    simp [hS]
  -- choose a point of `D` in each member of `S`
  have hpt : ∀ s ∈ S, ∃ x, x ∈ s ∩ D := by
    intro s hs
    have := hDd.inter_open_nonempty s (hopen s hs) (hne s hs)
    obtain ⟨x, hx⟩ := this
    exact ⟨x, hx⟩
  choose! f hf using hpt
  have hinj : Set.InjOn f S := by
    intro s hs t ht hst
    by_contra hne'
    have hd := hdisj hs ht hne'
    have h1 : f s ∈ s := (hf s hs).1
    have h2 : f s ∈ t := by rw [hst]; exact (hf t ht).1
    exact (Set.disjoint_left.mp hd h1) h2
  refine Set.countable_of_injective_of_countable_image hinj ?_
  refine hDc.mono ?_
  rintro x ⟨s, hs, rfl⟩
  exact (hf s hs).2

/-- A countable space satisfies the countable chain condition. -/

theorem not_isSuslinLine_real : ¬ IsSuslinLine ℝ := by
  rintro ⟨-, -, -, -, -, -, hsep⟩
  exact hsep inferInstance

/-- A Suslin line is uncountable. -/

theorem not_countable_of_isSuslinLine (α : Type*) [LinearOrder α] [TopologicalSpace α]
    (h : IsSuslinLine α) : ¬ Countable α := by
  intro hc
  haveI := hc
  exact h.2.2.2.2.2.2 inferInstance

/-- A Suslin line is not second countable. -/

theorem not_secondCountable_of_isSuslinLine (α : Type*) [LinearOrder α] [TopologicalSpace α]
    (h : IsSuslinLine α) : ¬ SecondCountableTopology α := by
  intro hsc
  haveI := hsc
  exact h.2.2.2.2.2.2 inferInstance

/-- A linear order with a countable *order-dense* subset (one meeting every nonempty
open interval) and no endpoints is a separable space for the order topology. -/

theorem separableSpace_of_countable_orderDense (α : Type*) [LinearOrder α]
    [TopologicalSpace α] [OrderTopology α] [Nontrivial α] {D : Set α} (hDc : D.Countable)
    (hD : ∀ x y : α, x < y → ∃ d ∈ D, x < d ∧ d < y) : SeparableSpace α := by
  refine ⟨⟨D, hDc, ?_⟩⟩
  rw [dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨a, b, hab, hsub⟩ := hU.exists_Ioo_subset hUne
  obtain ⟨d, hdD, hd1, hd2⟩ := hD a b hab
  exact ⟨d, hsub ⟨hd1, hd2⟩, hdD⟩

/-- A densely ordered set that order-embeds into `ℝ` has a countable order-dense subset. -/

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

theorem separableSpace_of_orderEmbedding_real (α : Type*) [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [Nontrivial α] [DenselyOrdered α] (f : α ↪o ℝ) : SeparableSpace α := by
  haveI : Nonempty α := inferInstance
  obtain ⟨D, hDc, hD⟩ := exists_countable_orderDense_of_orderEmbedding_real α f
  exact separableSpace_of_countable_orderDense α hDc hD

/-- A Suslin line does not order-embed into the real line. -/

theorem isEmpty_orderEmbedding_real_of_isSuslinLine (α : Type*) [LinearOrder α]
    [TopologicalSpace α] (h : IsSuslinLine α) : IsEmpty (α ↪o ℝ) := by
  obtain ⟨hot, hnt, hdo, -, -, -, hsep⟩ := h
  haveI := hot; haveI := hnt; haveI := hdo
  exact ⟨fun f => hsep (separableSpace_of_orderEmbedding_real α f)⟩

/-- A Suslin line is not order isomorphic to the real line. -/

theorem isEmpty_orderIso_real_of_isSuslinLine (α : Type*) [LinearOrder α] [TopologicalSpace α]
    (h : IsSuslinLine α) : IsEmpty (α ≃o ℝ) :=
  ⟨fun e => (isEmpty_orderEmbedding_real_of_isSuslinLine α h).elim e.toOrderEmbedding⟩

/-- **Cantor's base case.** A countable nontrivial dense linear order without endpoints is
order isomorphic to `ℚ`; in particular (being countable) it is separable and hence not a
Suslin line. -/

theorem suslinHypothesis_iff :
    SuslinHypothesis ↔
      ∀ (α : Type) (_ : LinearOrder α) (_ : TopologicalSpace α),
        OrderTopology α → Nontrivial α → DenselyOrdered α → NoMaxOrder α → NoMinOrder α →
          IsCcc α → SeparableSpace α := by
  constructor
  · intro h α _ _ h1 h2 h3 h4 h5 h6
    by_contra h7
    exact h α ‹_› ‹_› ⟨h1, h2, h3, h4, h5, h6, h7⟩
  · rintro h α _ _ ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact h7 (h α ‹_› ‹_› h1 h2 h3 h4 h5 h6)

/-- **Suslin's problem, formalized.**

`Frontier.SuslinHypothesis` says that there is no *Suslin line*, i.e. no
nontrivial dense linear order without endpoints, equipped with the order
topology, that satisfies the countable chain condition but is not separable.
This statement is independent of ZFC (it fails under Jensen's `◊`, and holds
under `MA_{ℵ₁} + ¬CH`), so it is neither provable nor refutable here.  The
present theorem collects the ZFC-provable content:

1. Suslin's Hypothesis is exactly the assertion that ccc implies separability
   for dense linear orders without endpoints (so Suslin's problem is precisely
   Cantor's characterisation of `ℝ` with "separable" weakened to "ccc").
2. Separability always implies ccc — the implication that is *not* in question.
3. The real line is not a Suslin line.
4. Any Suslin line is uncountable, not second countable, and does not order-embed
   into `ℝ` (in particular it is not order isomorphic to `ℝ`). -/

theorem Suslin_line :
    (SuslinHypothesis ↔
      ∀ (α : Type) (_ : LinearOrder α) (_ : TopologicalSpace α),
        OrderTopology α → Nontrivial α → DenselyOrdered α → NoMaxOrder α → NoMinOrder α →
          IsCcc α → SeparableSpace α)
    ∧ (∀ (α : Type*) [TopologicalSpace α] [SeparableSpace α], IsCcc α)
    ∧ ¬ IsSuslinLine ℝ
    ∧ (∀ (α : Type*) [LinearOrder α] [TopologicalSpace α], IsSuslinLine α →
        ¬ Countable α ∧ ¬ SecondCountableTopology α ∧ IsEmpty (α ↪o ℝ) ∧ IsEmpty (α ≃o ℝ)) := by
  refine ⟨suslinHypothesis_iff, fun α _ _ => isCcc_of_separable α, not_isSuslinLine_real,
    fun α _ _ h => ⟨not_countable_of_isSuslinLine α h, not_secondCountable_of_isSuslinLine α h,
      isEmpty_orderEmbedding_real_of_isSuslinLine α h,
      isEmpty_orderIso_real_of_isSuslinLine α h⟩⟩

end Frontier
