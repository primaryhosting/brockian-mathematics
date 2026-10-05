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

set_option grind.warning false

/-!
## Suslin's problem

Cantor characterised the real line as (up to order isomorphism) the unique nonempty complete
dense linear order without endpoints which is *separable*.  Suslin asked whether "separable"
can be weakened to the *countable chain condition* (ccc): every family of pairwise disjoint
nonempty open sets is countable.  A counterexample — a ccc, non-separable dense linear order
without endpoints, equipped with its order topology — is called a **Suslin line**, and
**Suslin's Hypothesis** (`SuslinHypothesis`) is the assertion that no Suslin line exists.

Suslin's Hypothesis is independent of ZFC (Jech, Tennenbaum, Solovay–Tennenbaum): Jensen's
diamond principle `◊` implies that a Suslin line exists, while `MA + ¬CH` implies that none
does.  Neither implication can be settled inside ZFC alone, so neither `SuslinHypothesis`
nor its negation is provable here.  What this file does is:

* give a precise formalisation of the notions involved (`IsCellularFamily`, `IsCCC`,
  `IsSuslinLine`, `SuslinHypothesis`);
* prove that Suslin's Hypothesis is *equivalent* to the classical topological statement
  "every ccc dense linear order without endpoints is separable";
* prove a **Lean-checked reduction** of Suslin's problem to a purely order-theoretic
  (topology-free) statement: every dense linear order without endpoints all of whose
  families of pairwise disjoint nonempty open intervals are countable has a countable
  order-dense subset;
* prove the *base case*: separable spaces are ccc, so a Suslin line is exactly a
  counterexample to the converse; in particular `ℝ` is not a Suslin line, and no Suslin
  line is countable, second countable, or topologically embeddable in `ℝ`.
-/

namespace Frontier

open Set TopologicalSpace Topology

universe u

/-- A *cellular family* in a topological space: a family of pairwise disjoint nonempty
open sets. -/
def IsCellularFamily {X : Type u} [TopologicalSpace X] (𝒰 : Set (Set X)) : Prop :=
  (∀ U ∈ 𝒰, IsOpen U) ∧ (∀ U ∈ 𝒰, U.Nonempty) ∧ 𝒰.PairwiseDisjoint id

/-- The *countable chain condition*: every cellular family is countable. -/
def IsCCC (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ 𝒰 : Set (Set X), IsCellularFamily 𝒰 → 𝒰.Countable

/-- A **Suslin line**: a nonempty dense linear order without endpoints, carrying its order
topology, which satisfies the countable chain condition but is not separable. -/
structure IsSuslinLine (X : Type u) [LinearOrder X] [TopologicalSpace X] : Prop where
  orderTopology : OrderTopology X
  nonempty : Nonempty X
  denselyOrdered : DenselyOrdered X
  noMinOrder : NoMinOrder X
  noMaxOrder : NoMaxOrder X
  ccc : IsCCC X
  not_separableSpace : ¬ SeparableSpace X

/-- **Suslin's Hypothesis**: there is no Suslin line. -/
def SuslinHypothesis : Prop :=
  ∀ (X : Type u) [LinearOrder X] [TopologicalSpace X], ¬ IsSuslinLine X

/-- The purely order-theoretic form of the countable chain condition: every family of
pairwise disjoint nonempty open intervals is countable. -/
def IntervalCCC (X : Type u) [LinearOrder X] : Prop :=
  ∀ s : Set (X × X), (∀ p ∈ s, p.1 < p.2) →
    (s.PairwiseDisjoint fun p => Ioo p.1 p.2) → s.Countable

/-- The purely order-theoretic form of separability: there is a countable subset meeting
every nonempty open interval. -/
def HasCountableOrderDenseSubset (X : Type u) [LinearOrder X] : Prop :=
  ∃ D : Set X, D.Countable ∧ ∀ a b : X, a < b → (D ∩ Ioo a b).Nonempty

section Basic

variable {X : Type u}

/-- Every separable space satisfies the countable chain condition.  (The point of Suslin's
problem is whether the converse can fail for order topologies.) -/
theorem isCCC_of_separableSpace [TopologicalSpace X] [SeparableSpace X] : IsCCC X := by
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense X
  rintro 𝒰 ⟨hopen, hne, hdisj⟩
  rcases isEmpty_or_nonempty X with hX | hX
  · have hsub : 𝒰 ⊆ ∅ := fun U hU =>
      absurd (hne U hU) (by simp [Set.eq_empty_of_isEmpty U])
    exact Set.Countable.mono hsub Set.countable_empty
  · have hch : ∀ U ∈ 𝒰, ∃ x, x ∈ D ∩ U := fun U hU => by
      obtain ⟨x, hx1, hx2⟩ := hDd.inter_open_nonempty U (hopen U hU) (hne U hU)
      exact ⟨x, hx2, hx1⟩
    choose! f hf using hch
    refine Set.countable_of_injective_of_countable_image (f := f) ?_ (hDc.mono ?_)
    · intro U hU V hV h
      by_contra hne'
      exact Set.disjoint_left.mp (hdisj hU hV hne') (hf U hU).2 (h ▸ (hf V hV).2)
    · rintro _ ⟨U, hU, rfl⟩
      exact (hf U hU).1

theorem not_isSuslinLine_of_separableSpace [LinearOrder X] [TopologicalSpace X]
    [SeparableSpace X] : ¬ IsSuslinLine X := fun h => h.not_separableSpace ‹_›

/-- Base case: the real line is not a Suslin line. -/
theorem not_isSuslinLine_real : ¬ IsSuslinLine ℝ :=
  not_isSuslinLine_of_separableSpace

theorem IsSuslinLine.not_countable [LinearOrder X] [TopologicalSpace X]
    (h : IsSuslinLine X) : ¬ Countable X := fun _ =>
  h.not_separableSpace inferInstance

theorem IsSuslinLine.not_secondCountableTopology [LinearOrder X] [TopologicalSpace X]
    (h : IsSuslinLine X) : ¬ SecondCountableTopology X := fun _ =>
  h.not_separableSpace SecondCountableTopology.to_separableSpace

/-- No Suslin line embeds topologically into the real line. -/
theorem IsSuslinLine.not_isInducing_real [LinearOrder X] [TopologicalSpace X]
    (h : IsSuslinLine X) (f : X → ℝ) : ¬ IsInducing f := fun hf =>
  h.not_secondCountableTopology hf.secondCountableTopology

theorem IsSuslinLine.nontrivial [LinearOrder X] [TopologicalSpace X]
    (h : IsSuslinLine X) : Nontrivial X := by
  haveI := h.noMinOrder
  obtain ⟨x⟩ := h.nonempty
  obtain ⟨y, hy⟩ := exists_lt x
  exact ⟨x, y, ne_of_gt hy⟩

end Basic

section Reduction

variable {X : Type u} [LinearOrder X] [TopologicalSpace X] [OrderTopology X]

/-- For a nontrivial dense linear order, topological separability is the same as having a
countable order-dense subset. -/
theorem separableSpace_iff_hasCountableOrderDenseSubset [DenselyOrdered X] [Nontrivial X] :
    SeparableSpace X ↔ HasCountableOrderDenseSubset X := by
  constructor
  · intro _
    obtain ⟨D, hDc, hDd⟩ := exists_countable_dense X
    refine ⟨D, hDc, fun a b hab => ?_⟩
    obtain ⟨x, hx1, hx2⟩ := hDd.inter_open_nonempty (Ioo a b) isOpen_Ioo (nonempty_Ioo.2 hab)
    exact ⟨x, hx2, hx1⟩
  · rintro ⟨D, hDc, hD⟩
    refine ⟨⟨D, hDc, ?_⟩⟩
    rw [dense_iff_inter_open]
    intro U hU hUne
    obtain ⟨a, b, hab, hsub⟩ := hU.exists_Ioo_subset hUne
    obtain ⟨x, hx1, hx2⟩ := hD a b hab
    exact ⟨x, hsub hx2, hx1⟩

/-- For a nontrivial dense linear order, the countable chain condition can be tested on
open intervals only. -/
theorem isCCC_iff_intervalCCC [DenselyOrdered X] [Nontrivial X] :
    IsCCC X ↔ IntervalCCC X := by
  constructor
  · intro hccc s hlt hdisj
    have hcard : ((fun p : X × X => Ioo p.1 p.2) '' s).Countable := by
      refine hccc _ ⟨?_, ?_, ?_⟩
      · rintro _ ⟨p, hp, rfl⟩
        exact isOpen_Ioo
      · rintro _ ⟨p, hp, rfl⟩
        exact nonempty_Ioo.2 (hlt p hp)
      · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hne
        exact hdisj hp hq (by rintro rfl; exact hne rfl)
    refine Set.countable_of_injective_of_countable_image
      (f := fun p : X × X => Ioo p.1 p.2) ?_ hcard
    intro p hp q hq h
    by_contra hpq
    obtain ⟨x, hx⟩ := nonempty_Ioo.2 (hlt p hp)
    exact Set.disjoint_left.mp (hdisj hp hq hpq) hx (h ▸ hx)
  · rintro hI 𝒰 ⟨hopen, hne, hdisj⟩
    have hch : ∀ U ∈ 𝒰, ∃ p : X × X, p.1 < p.2 ∧ Ioo p.1 p.2 ⊆ U := by
      intro U hU
      obtain ⟨a, b, hab, hsub⟩ := (hopen U hU).exists_Ioo_subset (hne U hU)
      exact ⟨(a, b), hab, hsub⟩
    choose! f hf1 hf2 using hch
    have hs : (f '' 𝒰).Countable := by
      refine hI _ ?_ ?_
      · rintro _ ⟨U, hU, rfl⟩
        exact hf1 U hU
      · rintro _ ⟨U, hU, rfl⟩ _ ⟨V, hV, rfl⟩ hne'
        exact Set.disjoint_of_subset (hf2 U hU) (hf2 V hV)
          (hdisj hU hV (by rintro rfl; exact hne' rfl))
    refine Set.countable_of_injective_of_countable_image (f := f) ?_ hs
    intro U hU V hV h
    by_contra hUV
    obtain ⟨x, hx⟩ := nonempty_Ioo.2 (hf1 U hU)
    have hx' : x ∈ Ioo (f V).1 (f V).2 := by rw [← h]; exact hx
    exact Set.disjoint_left.mp (hdisj hU hV hUV) (hf2 U hU hx) (hf2 V hV hx')

end Reduction

/-- Suslin's Hypothesis, stated topologically: every ccc dense linear order without
endpoints, with its order topology, is separable. -/
theorem suslinHypothesis_iff_topological :
    SuslinHypothesis.{u} ↔
      ∀ (X : Type u) [LinearOrder X] [TopologicalSpace X] [OrderTopology X],
        Nonempty X → DenselyOrdered X → NoMinOrder X → NoMaxOrder X → IsCCC X →
        SeparableSpace X := by
  constructor
  · intro SH X _ _ _ hne hd hmin hmax hccc
    by_contra hsep
    exact SH X ⟨‹OrderTopology X›, hne, hd, hmin, hmax, hccc, hsep⟩
  · intro H X _ _ h
    haveI := h.orderTopology
    exact h.not_separableSpace
      (H X h.nonempty h.denselyOrdered h.noMinOrder h.noMaxOrder h.ccc)

/-- **Reduction of Suslin's problem to a topology-free statement.**  Suslin's Hypothesis
holds iff every dense linear order without endpoints in which all families of pairwise
disjoint nonempty open intervals are countable possesses a countable order-dense subset. -/
theorem suslinHypothesis_iff_order :
    SuslinHypothesis.{u} ↔
      ∀ (X : Type u) [LinearOrder X],
        Nonempty X → DenselyOrdered X → NoMinOrder X → NoMaxOrder X → IntervalCCC X →
        HasCountableOrderDenseSubset X := by
  rw [suslinHypothesis_iff_topological]
  constructor
  · intro H X _ hne hd hmin hmax hI
    letI : TopologicalSpace X := Preorder.topology X
    haveI : OrderTopology X := ⟨rfl⟩
    haveI := hd
    haveI : Nontrivial X := by
      haveI := hmin
      obtain ⟨x⟩ := hne
      obtain ⟨y, hy⟩ := exists_lt x
      exact ⟨x, y, ne_of_gt hy⟩
    haveI := H X hne hd hmin hmax (isCCC_iff_intervalCCC.2 hI)
    exact separableSpace_iff_hasCountableOrderDenseSubset.1 inferInstance
  · intro H X _ _ _ hne hd hmin hmax hccc
    haveI := hd
    haveI : Nontrivial X := by
      haveI := hmin
      obtain ⟨x⟩ := hne
      obtain ⟨y, hy⟩ := exists_lt x
      exact ⟨x, y, ne_of_gt hy⟩
    exact separableSpace_iff_hasCountableOrderDenseSubset.2
      (H X hne hd hmin hmax (isCCC_iff_intervalCCC.1 hccc))

/-- **Suslin's problem.**

1. Suslin's Hypothesis is equivalent to the classical topological statement: every ccc dense
   linear order without endpoints is separable.
2. It is equivalent to a purely order-theoretic statement, with no topology involved.
3. Separability always implies the countable chain condition, so a Suslin line is precisely a
   counterexample to the converse implication for order topologies.
4. Base case: `ℝ` is not a Suslin line; and no Suslin line is countable, second countable, or
   topologically embeddable in `ℝ`.
-/
theorem Suslin_line :
    (SuslinHypothesis.{u} ↔
      ∀ (X : Type u) [LinearOrder X] [TopologicalSpace X] [OrderTopology X],
        Nonempty X → DenselyOrdered X → NoMinOrder X → NoMaxOrder X → IsCCC X →
        SeparableSpace X)
    ∧ (SuslinHypothesis.{u} ↔
      ∀ (X : Type u) [LinearOrder X],
        Nonempty X → DenselyOrdered X → NoMinOrder X → NoMaxOrder X → IntervalCCC X →
        HasCountableOrderDenseSubset X)
    ∧ (∀ (X : Type u) [TopologicalSpace X], SeparableSpace X → IsCCC X)
    ∧ ¬ IsSuslinLine ℝ
    ∧ (∀ (X : Type u) [LinearOrder X] [TopologicalSpace X], IsSuslinLine X →
        ¬ Countable X ∧ ¬ SecondCountableTopology X ∧ ∀ f : X → ℝ, ¬ IsInducing f) := by
  refine ⟨suslinHypothesis_iff_topological, suslinHypothesis_iff_order,
    fun X _ _ => isCCC_of_separableSpace, not_isSuslinLine_real, fun X _ _ h =>
      ⟨h.not_countable, h.not_secondCountableTopology, h.not_isInducing_real⟩⟩

end Frontier

