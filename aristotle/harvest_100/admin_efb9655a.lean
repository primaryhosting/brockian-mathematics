import Mathlib
import RequestProject.CantorDedekind

/-!
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open TopologicalSpace Set

namespace Frontier

/-- The **countable chain condition** (ccc) for a topological space `X`: every family of
pairwise disjoint nonempty open subsets of `X` is countable. -/
def CountableChainCondition (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ S : Set (Set X), (∀ s ∈ S, IsOpen s) → (∀ s ∈ S, s.Nonempty) →
    S.PairwiseDisjoint id → S.Countable

/-- A **Suslin line**: a densely ordered linear order without endpoints, equipped with its
order topology, which satisfies the countable chain condition but is *not* separable.

(Suslin's problem asks whether such a line exists; equivalently, whether every ccc dense
complete linear order without endpoints is order-isomorphic to `ℝ`.  The existence of a Suslin
line is independent of ZFC: Jensen's diamond principle `◊` implies one exists, while
`MA + ¬CH` implies none does.) -/
structure IsSuslinLine (X : Type u) [LinearOrder X] [TopologicalSpace X] : Prop where
  orderTopology : OrderTopology X
  denselyOrdered : DenselyOrdered X
  noMin : NoMinOrder X
  noMax : NoMaxOrder X
  ccc : CountableChainCondition X
  not_separable : ¬ SeparableSpace X

/-- **Suslin's Hypothesis** (SH): no Suslin line exists. -/
def SuslinHypothesis : Prop :=
  ∀ (X : Type) (_ : LinearOrder X) (_ : TopologicalSpace X), ¬ IsSuslinLine X

/-- In a separable space every pairwise disjoint family of nonempty open sets is countable:
separability implies the countable chain condition. -/
theorem countableChainCondition_of_separableSpace (X : Type u) [TopologicalSpace X]
    [SeparableSpace X] : CountableChainCondition X := by
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense X
  intro S hopen hne hdisj
  -- choose a point of `D` in each member of `S`
  have hchoice : ∀ s : S, ∃ d, d ∈ D ∩ (s : Set X) := by
    rintro ⟨s, hs⟩
    have := hDd.inter_open_nonempty s (hopen s hs) (hne s hs)
    simpa [Set.inter_comm] using this
  choose f hf using hchoice
  have hinj : Function.Injective f := by
    rintro ⟨s, hs⟩ ⟨t, ht⟩ hst
    by_contra hne'
    have hst' : s ≠ t := by
      intro h; exact hne' (by cases h; rfl)
    have := hdisj hs ht hst'
    have h1 : f ⟨s, hs⟩ ∈ s := (hf ⟨s, hs⟩).2
    have h2 : f ⟨s, hs⟩ ∈ t := by rw [hst]; exact (hf ⟨t, ht⟩).2
    exact (Set.disjoint_left.mp this h1) h2
  have hDcount : Countable (↥D) := hDc.to_subtype
  have hginj : Function.Injective (fun s : S => (⟨f s, (hf s).1⟩ : ↥D)) := by
    intro s t hst
    exact hinj (congrArg Subtype.val hst)
  have hcount : Countable S := hginj.countable
  exact Set.countable_coe_iff.mp hcount

/-- A Suslin line is not separable, hence not countable. -/
theorem not_countable_of_isSuslinLine {X : Type u} [LinearOrder X] [TopologicalSpace X]
    (h : IsSuslinLine X) : ¬ Countable X := by
  intro hc
  exact h.not_separable inferInstance

/-- `ℝ` is not a Suslin line: it is separable. -/
theorem not_isSuslinLine_real : ¬ IsSuslinLine ℝ := fun h => h.not_separable inferInstance

/-- A Suslin line is not homeomorphic to `ℝ` (indeed not to any separable space), since
separability is a topological invariant. -/
theorem isEmpty_homeomorph_real_of_isSuslinLine {X : Type u} [LinearOrder X]
    [TopologicalSpace X] (h : IsSuslinLine X) : IsEmpty (X ≃ₜ ℝ) := by
  refine ⟨fun e => h.not_separable ?_⟩
  exact (e.symm.surjective.denseRange).separableSpace e.symm.continuous

/-- **Suslin's problem, stated precisely as a reduction.**  Suslin's Hypothesis holds exactly
when every densely ordered, endpointless linear order with the order topology satisfying the
countable chain condition is separable. -/
theorem suslinHypothesis_iff :
    SuslinHypothesis ↔
      ∀ (X : Type) (_ : LinearOrder X) (_ : TopologicalSpace X), OrderTopology X →
        DenselyOrdered X → NoMinOrder X → NoMaxOrder X →
        CountableChainCondition X → SeparableSpace X := by
  constructor
  · intro h X _ _ hot hd hmin hmax hccc
    by_contra hsep
    exact h X ‹_› ‹_› ⟨hot, hd, hmin, hmax, hccc, hsep⟩
  · intro h X _ _ hS
    exact hS.not_separable
      (h X ‹_› ‹_› hS.orderTopology hS.denselyOrdered hS.noMin hS.noMax hS.ccc)


/-- **Suslin's original problem** (SP), verbatim: every nonempty, conditionally complete,
densely ordered linear order without endpoints whose order topology satisfies the countable
chain condition is order-isomorphic to `ℝ`. -/
def SuslinProblemOriginal : Prop :=
  ∀ (X : Type) (_ : ConditionallyCompleteLinearOrder X) (_ : TopologicalSpace X),
    OrderTopology X → DenselyOrdered X → NoMinOrder X → NoMaxOrder X → Nonempty X →
    CountableChainCondition X → Nonempty (X ≃o ℝ)

/-- Suslin's original problem has a positive answer exactly when there is no *complete*
Suslin line.  The nontrivial direction uses the Cantor–Dedekind theorem
`Frontier.orderIso_real_of_separableSpace`. -/
theorem suslinProblemOriginal_iff :
    SuslinProblemOriginal ↔
      ∀ (X : Type) (_ : ConditionallyCompleteLinearOrder X) (_ : TopologicalSpace X),
        Nonempty X → ¬ IsSuslinLine X := by
  constructor
  · intro h X _ _ hX hS
    haveI := hS.orderTopology
    obtain ⟨e⟩ := h X ‹_› ‹_› hS.orderTopology hS.denselyOrdered hS.noMin hS.noMax hX hS.ccc
    exact (isEmpty_homeomorph_real_of_isSuslinLine hS).false e.toHomeomorph
  · intro h X _ _ hot hd hmin hmax hX hccc
    haveI := hot; haveI := hd; haveI := hmin; haveI := hmax; haveI := hX
    have hsep : SeparableSpace X := by
      by_contra hns
      exact h X ‹_› ‹_› hX ⟨hot, hd, hmin, hmax, hccc, hns⟩
    haveI := hsep
    exact orderIso_real_of_separableSpace X

/-- Suslin's Hypothesis implies a positive answer to Suslin's original problem. -/
theorem suslinProblemOriginal_of_suslinHypothesis (h : SuslinHypothesis) :
    SuslinProblemOriginal :=
  suslinProblemOriginal_iff.mpr fun X _ _ _ => h X inferInstance inferInstance

/-- **Suslin line.**

The package: (1) separability implies ccc for any topological space, so the ccc half of the
definition of a Suslin line is the weakening of separability that Suslin's problem is about;
(2) `ℝ` is not a Suslin line; (3) any Suslin line is uncountable; (4) no Suslin line is
homeomorphic to `ℝ`; (5) Suslin's Hypothesis is equivalent to the assertion that every ccc
dense endpointless linearly ordered topological space is separable; (6) Suslin's original
problem (is every ccc complete dense endpointless linear order order-isomorphic to `ℝ`?) has
a positive answer exactly when there is no complete Suslin line; and (7) Suslin's Hypothesis
implies a positive answer to Suslin's original problem. -/
theorem Suslin_line :
    (∀ (X : Type) (_ : TopologicalSpace X), SeparableSpace X → CountableChainCondition X) ∧
    ¬ IsSuslinLine ℝ ∧
    (∀ (X : Type) (_ : LinearOrder X) (_ : TopologicalSpace X), IsSuslinLine X → ¬ Countable X) ∧
    (∀ (X : Type) (_ : LinearOrder X) (_ : TopologicalSpace X), IsSuslinLine X →
      IsEmpty (X ≃ₜ ℝ)) ∧
    (SuslinHypothesis ↔
      ∀ (X : Type) (_ : LinearOrder X) (_ : TopologicalSpace X), OrderTopology X →
        DenselyOrdered X → NoMinOrder X → NoMaxOrder X →
        CountableChainCondition X → SeparableSpace X) ∧
    (SuslinProblemOriginal ↔
      ∀ (X : Type) (_ : ConditionallyCompleteLinearOrder X) (_ : TopologicalSpace X),
        Nonempty X → ¬ IsSuslinLine X) ∧
    (SuslinHypothesis → SuslinProblemOriginal) :=
  ⟨fun X _ _ => countableChainCondition_of_separableSpace X,
   not_isSuslinLine_real,
   fun _ _ _ h => not_countable_of_isSuslinLine h,
   fun _ _ _ h => isEmpty_homeomorph_real_of_isSuslinLine h,
   suslinHypothesis_iff,
   suslinProblemOriginal_iff,
   suslinProblemOriginal_of_suslinHypothesis⟩

end Frontier

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# The Cantor–Dedekind theorem

Every nonempty, conditionally complete, densely ordered linear order without endpoints which
has a countable order-dense subset (e.g. a separable one, for the order topology) is
order-isomorphic to `ℝ`.

This is the classical ingredient behind Suslin's problem: Suslin asked whether the hypothesis
"has a countable dense subset" can be weakened to the countable chain condition.
-/

open Set

namespace Frontier

variable {X : Type} [ConditionallyCompleteLinearOrder X] [NoMinOrder X] [NoMaxOrder X]
  [Nonempty X]

/-- **Cantor–Dedekind.**  A nonempty conditionally complete dense linear order without
endpoints having a countable order-dense subset is order-isomorphic to `ℝ`. -/
theorem orderIso_real_of_countable_orderDense (D : Set X) (hDc : D.Countable)
    (hD : ∀ a b : X, a < b → ∃ d ∈ D, a < d ∧ d < b) : Nonempty (X ≃o ℝ) := by
  -- `D`, as a linear order, is a countable dense order without endpoints, hence `≃o ℚ`.
  haveI : Countable (↥D) := hDc.to_subtype
  haveI : Nonempty (↥D) := by
    obtain ⟨a⟩ := ‹Nonempty X›
    obtain ⟨b, hb⟩ := exists_gt a
    obtain ⟨d, hdD, _, _⟩ := hD a b hb
    exact ⟨⟨d, hdD⟩⟩
  haveI : DenselyOrdered (↥D) := by
    refine ⟨fun a b hab => ?_⟩
    obtain ⟨d, hdD, h1, h2⟩ := hD a b hab
    exact ⟨⟨d, hdD⟩, h1, h2⟩
  haveI : NoMinOrder (↥D) := by
    refine ⟨fun a => ?_⟩
    obtain ⟨y, hy⟩ := exists_lt (a : X)
    obtain ⟨d, hdD, _, h2⟩ := hD y a hy
    exact ⟨⟨d, hdD⟩, h2⟩
  haveI : NoMaxOrder (↥D) := by
    refine ⟨fun a => ?_⟩
    obtain ⟨y, hy⟩ := exists_gt (a : X)
    obtain ⟨d, hdD, h1, _⟩ := hD a y hy
    exact ⟨⟨d, hdD⟩, h1⟩
  obtain ⟨g⟩ := Order.iso_of_countable_dense (↥D) ℚ
  -- the embedding of `X` into `ℝ`
  set q : ↥D → ℝ := fun d => ((g d : ℚ) : ℝ) with hq
  set S : X → Set ℝ := fun x => q '' {d : ↥D | (d : X) < x} with hS
  have hqmono : StrictMono q := by
    intro a b hab
    have h : g a < g b := g.lt_iff_lt.mpr hab
    simp only [hq]
    exact_mod_cast h
  have hne : ∀ x : X, (S x).Nonempty := by
    intro x
    obtain ⟨y, hy⟩ := exists_lt x
    obtain ⟨d, hdD, _, h2⟩ := hD y x hy
    exact ⟨q ⟨d, hdD⟩, ⟨d, hdD⟩, h2, rfl⟩
  have hbdd : ∀ x : X, BddAbove (S x) := by
    intro x
    obtain ⟨z, hz⟩ := exists_gt x
    obtain ⟨d, hdD, h1, _⟩ := hD x z hz
    refine ⟨q ⟨d, hdD⟩, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    have : e < (⟨d, hdD⟩ : ↥D) := Subtype.coe_lt_coe.mp (lt_trans he h1)
    exact (hqmono this).le
  set F : X → ℝ := fun x => sSup (S x) with hF
  have hle : ∀ (x : X) (d : ↥D), (d : X) < x → q d ≤ F x := by
    intro x d hd
    exact le_csSup (hbdd x) ⟨d, hd, rfl⟩
  have hFmono : StrictMono F := by
    intro a b hab
    obtain ⟨d₁, hd₁D, ha1, h1b⟩ := hD a b hab
    obtain ⟨d₂, hd₂D, h12, h2b⟩ := hD d₁ b h1b
    have hFa : F a ≤ q ⟨d₁, hd₁D⟩ := by
      refine csSup_le (hne a) ?_
      rintro _ ⟨e, he, rfl⟩
      exact (hqmono (Subtype.coe_lt_coe.mp (lt_trans he ha1) :
        e < (⟨d₁, hd₁D⟩ : ↥D))).le
    have h2 : q ⟨d₂, hd₂D⟩ ≤ F b := hle b ⟨d₂, hd₂D⟩ h2b
    have : q ⟨d₁, hd₁D⟩ < q ⟨d₂, hd₂D⟩ := hqmono h12
    linarith
  have hFsurj : Function.Surjective F := by
    intro r
    set T : Set X := (fun d : ↥D => (d : X)) '' {d : ↥D | q d < r} with hT
    have hTne : T.Nonempty := by
      obtain ⟨s, hs⟩ := exists_rat_lt r
      exact ⟨(g.symm s : X), ⟨g.symm s, by simp [hq, hs], rfl⟩⟩
    have hTbdd : BddAbove T := by
      obtain ⟨s, hs⟩ := exists_rat_gt r
      refine ⟨(g.symm s : X), ?_⟩
      rintro _ ⟨e, he, rfl⟩
      have hlt : q e < ((s : ℚ) : ℝ) := lt_trans he hs
      simp only [hq] at hlt
      have hgs : g e < s := by exact_mod_cast hlt
      have : e < g.symm s := by
        have h := (g.lt_iff_lt (x := e) (y := g.symm s))
        simpa using h.mp (by simpa using hgs)
      exact Subtype.coe_le_coe.mpr this.le
    refine ⟨sSup T, le_antisymm ?_ ?_⟩
    · -- `F (sSup T) ≤ r`
      refine csSup_le (hne _) ?_
      rintro _ ⟨e, he, rfl⟩
      obtain ⟨y, hyT, hy⟩ := exists_lt_of_lt_csSup hTne he
      obtain ⟨d, hd, rfl⟩ := hyT
      have : e < d := hy
      exact le_of_lt (lt_trans (hqmono this) hd)
    · -- `r ≤ F (sSup T)`
      by_contra hcon
      push_neg at hcon
      obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn hcon
      obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn hs2
      have hst : (g.symm s : X) < (g.symm t : X) := by
        have : g.symm s < g.symm t := by
          have hst' : s < t := by exact_mod_cast ht1
          simpa using (g.symm.lt_iff_lt (x := s) (y := t)).mpr hst'
        exact this
      have hts : (g.symm t : X) ≤ sSup T := by
        refine le_csSup hTbdd ⟨g.symm t, ?_, rfl⟩
        simp only [mem_setOf_eq, hq]
        simpa using ht2
      have hlt : (g.symm s : X) < sSup T := lt_of_lt_of_le hst hts
      have := hle (sSup T) (g.symm s) hlt
      have hqs : q (g.symm s) = ((s : ℚ) : ℝ) := by simp [hq]
      rw [hqs] at this
      linarith
  exact ⟨StrictMono.orderIsoOfSurjective F hFmono hFsurj⟩

/-- A nonempty conditionally complete dense linear order without endpoints whose order topology
is separable is order-isomorphic to `ℝ`. -/
theorem orderIso_real_of_separableSpace (X : Type) [ConditionallyCompleteLinearOrder X]
    [TopologicalSpace X] [OrderTopology X] [DenselyOrdered X] [NoMinOrder X] [NoMaxOrder X]
    [Nonempty X] [TopologicalSpace.SeparableSpace X] : Nonempty (X ≃o ℝ) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense X
  refine orderIso_real_of_countable_orderDense D hDc ?_
  intro a b hab
  obtain ⟨c, hc⟩ := hDd.inter_open_nonempty (Ioo a b) isOpen_Ioo (nonempty_Ioo.mpr hab)
  exact ⟨c, hc.2, hc.1.1, hc.1.2⟩

/-- Sanity check that the hypotheses above are satisfiable: `ℝ` itself is a nonempty,
conditionally complete, densely ordered separable linear order without endpoints. -/
example : Nonempty (ℝ ≃o ℝ) := orderIso_real_of_separableSpace ℝ

end Frontier

