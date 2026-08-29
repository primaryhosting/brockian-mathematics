/-
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` before any module docstring, so the header block is repeated
-- below as the module docstring.)

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

open TopologicalSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## The countable chain condition

A *cellular family* in a topological space is a family of pairwise disjoint nonempty open
sets.  A space satisfies the *countable chain condition* (ccc) if every cellular family in it
is countable.
-/

/-- A family of pairwise disjoint nonempty open sets. -/
def IsCellularFamily {X : Type*} [TopologicalSpace X] (C : Set (Set X)) : Prop :=
  (∀ U ∈ C, IsOpen U) ∧ (∀ U ∈ C, U.Nonempty) ∧ C.PairwiseDisjoint id

/-- The countable chain condition: every family of pairwise disjoint nonempty open sets is
countable. -/
def IsCCC (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ C : Set (Set X), IsCellularFamily C → C.Countable

/-- Every separable space satisfies the countable chain condition: a countable dense set must
meet each member of a cellular family, in distinct points. -/
theorem isCCC_of_separableSpace (X : Type*) [TopologicalSpace X] [SeparableSpace X] :
    IsCCC X := by
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense X
  have : Countable D := hDc.to_subtype
  rintro C ⟨hopen, hne, hdisj⟩
  have hchoice : ∀ U : C, ∃ d : X, d ∈ (U : Set X) ∩ D := fun U =>
    hDd.inter_open_nonempty (U : Set X) (hopen U U.2) (hne U U.2)
  choose f hf using hchoice
  have hinj : Function.Injective fun U : C => (⟨f U, (hf U).2⟩ : D) := by
    intro U V h
    have hfUV : f U = f V := congrArg Subtype.val h
    by_contra hUV
    have hUV' : (U : Set X) ≠ (V : Set X) := fun h' => hUV (Subtype.ext h')
    have hd : Disjoint (U : Set X) (V : Set X) := hdisj U.2 V.2 hUV'
    have hmem : f U ∈ (U : Set X) ∩ (V : Set X) := ⟨(hf U).1, hfUV ▸ (hf V).1⟩
    exact (Set.disjoint_iff_inter_eq_empty.mp hd ▸ hmem : f U ∈ (∅ : Set X))
  have : Countable C := hinj.countable
  exact Set.countable_coe_iff.mp this

/-- In a discrete space the countable chain condition is exactly countability; in particular
the condition is not vacuous. -/
theorem isCCC_iff_countable_of_discrete (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    IsCCC X ↔ Countable X := by
  constructor
  · intro h
    have hcell : IsCellularFamily (Set.range (fun x : X => ({x} : Set X))) := by
      refine ⟨?_, ?_, ?_⟩
      · rintro U ⟨x, rfl⟩; exact isOpen_discrete _
      · rintro U ⟨x, rfl⟩; exact ⟨x, rfl⟩
      · rintro U ⟨x, rfl⟩ V ⟨y, rfl⟩ hUV
        have hxy : x ≠ y := fun hxy => hUV (by rw [hxy])
        simp only [Function.onFun, id_eq, Set.disjoint_singleton]
        exact hxy
    have hc := h _ hcell
    have : Countable (Set.range (fun x : X => ({x} : Set X))) := hc.to_subtype
    have hinj : Function.Injective
        (fun x : X => (⟨({x} : Set X), ⟨x, rfl⟩⟩ : Set.range (fun x : X => ({x} : Set X)))) := by
      intro x y h
      have : ({x} : Set X) = ({y} : Set X) := congrArg Subtype.val h
      simpa using this
    exact hinj.countable
  · intro _
    exact isCCC_of_separableSpace X

/-- Every second countable space satisfies the countable chain condition. -/
theorem isCCC_of_secondCountableTopology (X : Type*) [TopologicalSpace X]
    [SecondCountableTopology X] : IsCCC X :=
  isCCC_of_separableSpace X

/-- **Reduction of ccc to open intervals.** In a densely ordered linear order with at least two
points, carrying the order topology, the countable chain condition is equivalent to the
countability of every pairwise disjoint family of nonempty open intervals. -/
theorem isCCC_iff_countable_disjoint_Ioo (X : Type*) [LinearOrder X] [TopologicalSpace X]
    [OrderTopology X] [DenselyOrdered X] [Nontrivial X] :
    IsCCC X ↔ ∀ I : Set (Set X), (∀ U ∈ I, ∃ a b : X, a < b ∧ U = Set.Ioo a b) →
      I.PairwiseDisjoint id → I.Countable := by
  constructor
  · intro h I hI hdisj
    refine h I ⟨?_, ?_, hdisj⟩
    · intro U hU
      obtain ⟨a, b, -, rfl⟩ := hI U hU
      exact isOpen_Ioo
    · intro U hU
      obtain ⟨a, b, hab, rfl⟩ := hI U hU
      obtain ⟨c, hc⟩ := exists_between hab
      exact ⟨c, hc⟩
  · rintro h C ⟨hopen, hne, hdisj⟩
    have hchoice : ∀ U : C, ∃ p : X × X, p.1 < p.2 ∧ Set.Ioo p.1 p.2 ⊆ (U : Set X) := by
      intro U
      obtain ⟨a, b, hab, hsub⟩ := (hopen U U.2).exists_Ioo_subset (hne U U.2)
      exact ⟨(a, b), hab, hsub⟩
    choose p hp using hchoice
    set g : C → Set X := fun U => Set.Ioo (p U).1 (p U).2 with hg
    have hgne : ∀ U : C, (g U).Nonempty := by
      intro U
      obtain ⟨c, hc⟩ := exists_between (hp U).1
      exact ⟨c, hc⟩
    have hginj : Function.Injective g := by
      intro U V hUV
      by_contra hne'
      have hUV' : (U : Set X) ≠ (V : Set X) := fun h' => hne' (Subtype.ext h')
      have hd : Disjoint (U : Set X) (V : Set X) := hdisj U.2 V.2 hUV'
      obtain ⟨c, hc⟩ := hgne U
      have hcU : c ∈ (U : Set X) := (hp U).2 hc
      have hcgV : c ∈ g V := hUV ▸ hc
      have hcV : c ∈ (V : Set X) := (hp V).2 hcgV
      exact (Set.disjoint_iff_inter_eq_empty.mp hd ▸ (⟨hcU, hcV⟩ : c ∈ (U : Set X) ∩ V) :
        c ∈ (∅ : Set X))
    have hIcount : (Set.range g).Countable := by
      refine h _ ?_ ?_
      · rintro U ⟨V, rfl⟩
        exact ⟨(p V).1, (p V).2, (hp V).1, rfl⟩
      · rintro U ⟨V, rfl⟩ U' ⟨V', rfl⟩ hUU'
        have hVV' : V ≠ V' := fun h' => hUU' (by rw [h'])
        have hV : (V : Set X) ≠ (V' : Set X) := fun h' => hVV' (Subtype.ext h')
        have hd : Disjoint (V : Set X) (V' : Set X) := hdisj V.2 V'.2 hV
        exact hd.mono (hp V).2 (hp V').2
    have : Countable (Set.range g) := hIcount.to_subtype
    have hinj : Function.Injective fun U : C => (⟨g U, ⟨U, rfl⟩⟩ : Set.range g) := by
      intro U V hUV
      exact hginj (congrArg Subtype.val hUV)
    exact Set.countable_coe_iff.mp hinj.countable

/-!
## Suslin lines and Suslin's Hypothesis
-/

/-- A *Suslin line* is a densely ordered linear order without endpoints whose order topology
satisfies the countable chain condition but is not separable. -/
def IsSuslinLine (X : Type*) [LinearOrder X] [TopologicalSpace X] [OrderTopology X] : Prop :=
  DenselyOrdered X ∧ NoMinOrder X ∧ NoMaxOrder X ∧ IsCCC X ∧ ¬ SeparableSpace X

/-- A bundled Suslin line, used to phrase the existence statement. -/
structure SuslinLine where
  /-- The underlying type. -/
  carrier : Type
  [linOrd : LinearOrder carrier]
  [topo : TopologicalSpace carrier]
  [ordTop : OrderTopology carrier]
  /-- The defining properties of a Suslin line. -/
  isSuslinLine : IsSuslinLine carrier

attribute [instance] SuslinLine.linOrd SuslinLine.topo SuslinLine.ordTop

/-- *Suslin's Hypothesis*: every densely ordered linear order without endpoints whose order
topology satisfies the countable chain condition is separable.  (Equivalently: there is no
Suslin line.) -/
def SuslinsHypothesis : Prop :=
  ∀ (X : Type) [LinearOrder X] [TopologicalSpace X] [OrderTopology X],
    DenselyOrdered X → NoMinOrder X → NoMaxOrder X → IsCCC X → SeparableSpace X

/-- Suslin's problem, precisely stated: a Suslin line exists if and only if Suslin's
Hypothesis fails. -/
theorem suslinLine_nonempty_iff_not_suslinsHypothesis :
    Nonempty SuslinLine ↔ ¬ SuslinsHypothesis := by
  constructor
  · rintro ⟨L⟩ h
    obtain ⟨hd, hmin, hmax, hccc, hsep⟩ := L.isSuslinLine
    exact hsep (h L.carrier hd hmin hmax hccc)
  · intro h
    by_contra hne
    refine h ?_
    intro X _ _ _ hd hmin hmax hccc
    by_contra hsep
    exact hne ⟨⟨X, ⟨hd, hmin, hmax, hccc, hsep⟩⟩⟩

/-- The real line is not a Suslin line: it is a densely ordered, unbounded, ccc linear order,
but it *is* separable. -/
theorem not_isSuslinLine_real : ¬ IsSuslinLine ℝ := by
  rintro ⟨-, -, -, -, h⟩
  exact h inferInstance

/-- The real line satisfies the countable chain condition. -/
theorem isCCC_real : IsCCC ℝ := isCCC_of_separableSpace ℝ

/-- A Suslin line is uncountable. -/
theorem SuslinLine.uncountable (L : SuslinLine) : ¬ Countable L.carrier := by
  intro h
  exact L.isSuslinLine.2.2.2.2 (@Countable.to_separableSpace _ _ h)

/-- A Suslin line is not second countable. -/
theorem SuslinLine.not_secondCountable (L : SuslinLine) :
    ¬ SecondCountableTopology L.carrier := by
  intro h
  exact L.isSuslinLine.2.2.2.2 (@SecondCountableTopology.to_separableSpace _ _ h)

/-- A Suslin line is nonempty (the empty space is separable). -/
theorem SuslinLine.nonempty (L : SuslinLine) : Nonempty L.carrier := by
  by_contra h
  rw [not_nonempty_iff] at h
  exact L.isSuslinLine.2.2.2.2 ⟨⟨∅, Set.countable_empty, fun x => (IsEmpty.false x).elim⟩⟩

/-- A Suslin line has at least two points. -/
theorem SuslinLine.nontrivial (L : SuslinLine) : Nontrivial L.carrier := by
  haveI := L.nonempty
  haveI := L.isSuslinLine.2.2.1
  obtain ⟨a⟩ := L.nonempty
  obtain ⟨b, hb⟩ := exists_gt a
  exact ⟨⟨a, b, ne_of_lt hb⟩⟩

/-- A Suslin line has no countable dense subset. -/
theorem SuslinLine.no_countable_dense (L : SuslinLine) :
    ¬ ∃ D : Set L.carrier, D.Countable ∧ Dense D := by
  intro h
  exact L.isSuslinLine.2.2.2.2 ⟨h⟩

/-- In a Suslin line every pairwise disjoint family of nonempty open intervals is countable:
the ccc hypothesis in interval form. -/
theorem SuslinLine.countable_disjoint_Ioo (L : SuslinLine) (I : Set (Set L.carrier))
    (hI : ∀ U ∈ I, ∃ a b : L.carrier, a < b ∧ U = Set.Ioo a b)
    (hdisj : I.PairwiseDisjoint id) : I.Countable := by
  haveI := L.isSuslinLine.1
  haveI := L.nontrivial
  exact (isCCC_iff_countable_disjoint_Ioo L.carrier).1 L.isSuslinLine.2.2.2.1 I hI hdisj

/-- A Suslin line is not order isomorphic to the real line: an order isomorphism of linear
orders carrying the order topology is a homeomorphism, and `ℝ` is separable. -/
theorem SuslinLine.isEmpty_orderIso_real (L : SuslinLine) : IsEmpty (L.carrier ≃o ℝ) := by
  constructor
  intro e
  refine L.isSuslinLine.2.2.2.2 ?_
  have hcont : Continuous (e.symm : ℝ → L.carrier) := (e.symm).continuous
  have hdr : DenseRange (e.symm : ℝ → L.carrier) :=
    Function.Surjective.denseRange (e.symm).surjective
  exact hdr.separableSpace hcont

/-!
## The target statement

We record: (i) the general fact that separability implies the countable chain condition, so
that a Suslin line is exactly a space witnessing the failure of the converse in the class of
dense unbounded linear orders; (ii) the base case that `ℝ` is not a Suslin line; (iii) the
precise formulation of Suslin's problem as the equivalence between the existence of a Suslin
line and the failure of Suslin's Hypothesis; and (iv) structural consequences: any Suslin line
is uncountable, is not second countable, and is not order isomorphic to `ℝ`.
-/

/-- **Suslin's problem.**

* every separable space is ccc (so a Suslin line is precisely a dense unbounded linear order
  witnessing that the converse fails);
* `ℝ` is ccc, separable, and hence not a Suslin line (base case);
* a Suslin line exists if and only if Suslin's Hypothesis fails;
* every Suslin line is uncountable, is not second countable, and is not order isomorphic
  to `ℝ`;
* in every Suslin line each pairwise disjoint family of nonempty open intervals is countable,
  while no countable subset is dense (the ccc-versus-separability tension in explicit form).

The existence of a Suslin line is independent of ZFC, so no ZFC proof can decide the middle
equivalence; what is proved here is the precise reduction together with the ZFC-provable facts
surrounding it. -/
theorem Suslin_line :
    (∀ (X : Type) [TopologicalSpace X], SeparableSpace X → IsCCC X) ∧
    (IsCCC ℝ ∧ SeparableSpace ℝ ∧ ¬ IsSuslinLine ℝ) ∧
    (Nonempty SuslinLine ↔ ¬ SuslinsHypothesis) ∧
    (∀ L : SuslinLine, ¬ Countable L.carrier ∧
      ¬ SecondCountableTopology L.carrier ∧
      IsEmpty (L.carrier ≃o ℝ)) ∧
    (∀ L : SuslinLine,
      (∀ I : Set (Set L.carrier),
        (∀ U ∈ I, ∃ a b : L.carrier, a < b ∧ U = Set.Ioo a b) →
        I.PairwiseDisjoint id → I.Countable) ∧
      ¬ ∃ D : Set L.carrier, D.Countable ∧ Dense D) := by
  refine ⟨fun X _ h => @isCCC_of_separableSpace X _ h, ⟨isCCC_real, inferInstance,
    not_isSuslinLine_real⟩, suslinLine_nonempty_iff_not_suslinsHypothesis,
    fun L => ⟨L.uncountable, L.not_secondCountable, L.isEmpty_orderIso_real⟩,
    fun L => ⟨fun I hI hdisj => L.countable_disjoint_Ioo I hI hdisj, L.no_countable_dense⟩⟩

end Frontier

