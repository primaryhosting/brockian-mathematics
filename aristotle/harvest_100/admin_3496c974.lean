/-
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 forbids a module docstring before `import`; the same header is repeated as the module
-- docstring immediately below the import.)
import Mathlib

/-!
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open TopologicalSpace Set

namespace Frontier

/-!
## Suslin's problem, stated precisely

A *linear continuum* is a nonempty densely ordered linear order without endpoints in which every
nonempty bounded-above set has a least upper bound (i.e. `ℝ`-like order completeness).

The *countable chain condition* (ccc) says: every family of pairwise disjoint nonempty open sets is
countable.

A **Suslin line** is a linear continuum, equipped with its order topology, which satisfies the ccc
but is *not* separable.  Cantor's theorem characterises `ℝ` as the unique separable linear
continuum; **Suslin's problem** asks whether "separable" may be weakened to "ccc" in that
characterisation, i.e. whether a Suslin line exists.  The statement "no Suslin line exists" is
*Suslin's Hypothesis* (`Frontier.SuslinHypothesis` below).

Suslin's Hypothesis is independent of ZFC (Jech, Tennenbaum, Solovay–Tennenbaum): Jensen's diamond
principle `◊` implies that a Suslin line exists, while `MA + ¬CH` implies that none does.  Neither
implication — nor any "iff" between the existence of a Suslin line and `◊`-type hypotheses — is a
theorem of ZFC, and independence results cannot be established inside Lean's ambient set theory.
What *is* provable in ZFC, and is proved below, is the base case together with the reductions that
delimit the problem:

* separability implies the ccc, so a Suslin line is precisely a ccc linear continuum that fails the
  (a priori stronger) separability half of Cantor's characterisation;
* consequently no separable space — in particular neither `ℝ` nor `ℚ` — is a Suslin line;
* a Suslin line is uncountable and not second countable;
* being a Suslin line is invariant under order isomorphism, so no Suslin line is order isomorphic
  to `ℝ`;
* Suslin's Hypothesis is equivalent to: every ccc linear continuum is separable.
-/

/-- The **countable chain condition**: every family of pairwise disjoint nonempty open sets is
countable. -/
def IsCCC (α : Type*) [TopologicalSpace α] : Prop :=
  ∀ S : Set (Set α), (∀ s ∈ S, IsOpen s) → (∀ s ∈ S, s.Nonempty) →
    S.PairwiseDisjoint id → S.Countable

/-- Order completeness in the sense of Dedekind: every nonempty set that is bounded above has a
least upper bound. -/
def HasLUBProperty (α : Type*) [LinearOrder α] : Prop :=
  ∀ s : Set α, s.Nonempty → BddAbove s → ∃ x, IsLUB s x

/-- A **linear continuum**: a nonempty, densely ordered linear order without endpoints in which
every nonempty bounded-above set has a least upper bound. -/
structure IsLinearContinuum (α : Type*) [LinearOrder α] : Prop where
  nonempty : Nonempty α
  densely : DenselyOrdered α
  noMin : NoMinOrder α
  noMax : NoMaxOrder α
  lub : HasLUBProperty α

/-- A **Suslin line**: a linear continuum, with its order topology, which satisfies the countable
chain condition but is not separable. -/
structure IsSuslinLine (α : Type*) [LinearOrder α] [TopologicalSpace α] [OrderTopology α] :
    Prop where
  continuum : IsLinearContinuum α
  ccc : IsCCC α
  not_separable : ¬ SeparableSpace α

/-- **Suslin's Hypothesis**: no Suslin line exists. -/
def SuslinHypothesis : Prop :=
  ∀ (α : Type) [LinearOrder α] [TopologicalSpace α] [OrderTopology α], ¬ IsSuslinLine α

/-! ## Separability implies the countable chain condition -/

/-- Every separable topological space satisfies the countable chain condition: a pairwise disjoint
family of nonempty open sets injects into any countable dense subset. -/
theorem isCCC_of_separableSpace (α : Type*) [TopologicalSpace α] [SeparableSpace α] : IsCCC α := by
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense α
  intro S hopen hne hdisj
  -- choose a point of the countable dense set `D` inside each member of `S`
  have hpick : ∀ s : S, ((s : Set α) ∩ D).Nonempty := fun s =>
    hDd.inter_open_nonempty _ (hopen _ s.2) (hne _ s.2)
  choose f hf using hpick
  have hinj : Function.Injective fun s : S => (⟨f s, (hf s).2⟩ : D) := by
    rintro ⟨s, hs⟩ ⟨t, ht⟩ h
    simp only [Subtype.mk.injEq] at h
    by_contra hst
    have hst' : s ≠ t := by simpa [Subtype.ext_iff] using hst
    have hdis := hdisj hs ht hst'
    have hmem : f ⟨s, hs⟩ ∈ s ∩ t := ⟨(hf ⟨s, hs⟩).1, h ▸ (hf ⟨t, ht⟩).1⟩
    exact (Set.disjoint_left.mp hdis hmem.1) hmem.2
  have hD : Countable D := hDc.to_subtype
  have : Countable S := Function.Injective.countable hinj
  exact Set.countable_coe_iff.mp this

/-! ## Consequences: which spaces are not Suslin lines -/

theorem not_isSuslinLine_of_separableSpace (α : Type*) [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [SeparableSpace α] : ¬ IsSuslinLine α :=
  fun h => h.not_separable ‹SeparableSpace α›

/-- The real line is a linear continuum (this shows the definitions above are not vacuous). -/
theorem isLinearContinuum_real : IsLinearContinuum ℝ :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    fun _ hs hb => Real.exists_isLUB hs hb⟩

/-- The real line satisfies the countable chain condition. -/
theorem isCCC_real : IsCCC ℝ := isCCC_of_separableSpace ℝ

/-- The real line is not a Suslin line: it is a ccc linear continuum, but it *is* separable. -/
theorem not_isSuslinLine_real : ¬ IsSuslinLine ℝ :=
  not_isSuslinLine_of_separableSpace ℝ

/-- The rationals do not form a Suslin line (they are countable, hence separable). -/
theorem not_isSuslinLine_rat : ¬ IsSuslinLine ℚ :=
  not_isSuslinLine_of_separableSpace ℚ

/-- A Suslin line is uncountable: a countable space is separable. -/
theorem IsSuslinLine.not_countable {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] (h : IsSuslinLine α) : ¬ Countable α := by
  intro hc
  exact h.not_separable (by haveI := hc; infer_instance)

/-- A Suslin line is not second countable: second countable spaces are separable. -/
theorem IsSuslinLine.not_secondCountableTopology {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] (h : IsSuslinLine α) : ¬ SecondCountableTopology α := by
  intro hs
  exact h.not_separable SecondCountableTopology.to_separableSpace

/-! ## Invariance under order isomorphism -/

theorem isCCC_of_homeomorph {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : α ≃ₜ β) (h : IsCCC α) : IsCCC β := by
  intro S hopen hne hdisj
  have hcount : ((fun s => e ⁻¹' s) '' S).Countable := by
    refine h _ ?_ ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      exact (hopen s hs).preimage e.continuous
    · rintro _ ⟨s, hs, rfl⟩
      obtain ⟨x, hx⟩ := hne s hs
      exact ⟨e.symm x, by simpa using hx⟩
    · rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩ hst
      have hst' : s ≠ t := by rintro rfl; exact hst rfl
      have hdis := hdisj hs ht hst'
      simp only [id_eq, Set.disjoint_left] at hdis ⊢
      intro x hx hx'
      exact hdis hx hx'
  have hS : S = (fun s => e '' s) '' ((fun s => e ⁻¹' s) '' S) := by
    ext s
    constructor
    · intro hs
      exact ⟨e ⁻¹' s, ⟨s, hs, rfl⟩, by simp [Set.image_preimage_eq _ e.surjective]⟩
    · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      simpa [Set.image_preimage_eq _ e.surjective] using ht
  rw [hS]
  exact hcount.image _

theorem separableSpace_of_homeomorph {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : α ≃ₜ β) [SeparableSpace α] : SeparableSpace β :=
  e.surjective.denseRange.separableSpace e.continuous

theorem isLinearContinuum_of_orderIso {α β : Type*} [LinearOrder α] [LinearOrder β]
    (e : α ≃o β) (h : IsLinearContinuum α) : IsLinearContinuum β := by
  obtain ⟨hne, hd, hmin, hmax, hlub⟩ := h
  refine ⟨hne.map e, ⟨?_⟩, ⟨?_⟩, ⟨?_⟩, ?_⟩
  · intro a b hab
    obtain ⟨c, hc1, hc2⟩ := hd.dense (e.symm a) (e.symm b) (e.symm.lt_iff_lt.2 hab)
    exact ⟨e c, by simpa using e.lt_iff_lt.2 hc1, by simpa using e.lt_iff_lt.2 hc2⟩
  · intro a
    obtain ⟨b, hb⟩ := hmin.exists_lt (e.symm a)
    exact ⟨e b, by simpa using e.lt_iff_lt.2 hb⟩
  · intro a
    obtain ⟨b, hb⟩ := hmax.exists_gt (e.symm a)
    exact ⟨e b, by simpa using e.lt_iff_lt.2 hb⟩
  · intro s hs hbdd
    obtain ⟨y, hy⟩ := hs
    obtain ⟨x, hx⟩ := hlub (e ⁻¹' s) ⟨e.symm y, by simpa using hy⟩
      ((OrderIso.bddAbove_preimage e).2 hbdd)
    refine ⟨e x, ?_⟩
    have := (OrderIso.isLUB_image' e).2 hx
    rwa [Set.image_preimage_eq _ e.surjective] at this

/-- Being a Suslin line is invariant under order isomorphism (an order isomorphism between spaces
carrying the order topology is a homeomorphism). -/
theorem IsSuslinLine.of_orderIso {α β : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [LinearOrder β] [TopologicalSpace β] [OrderTopology β] (e : α ≃o β)
    (h : IsSuslinLine α) : IsSuslinLine β := by
  refine ⟨isLinearContinuum_of_orderIso e h.continuum, isCCC_of_homeomorph e.toHomeomorph h.ccc,
    fun hsep => ?_⟩
  exact h.not_separable (separableSpace_of_homeomorph e.toHomeomorph.symm)

/-- No Suslin line is order isomorphic to the real line. -/
theorem not_orderIso_real_of_isSuslinLine {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] (h : IsSuslinLine α) : IsEmpty (α ≃o ℝ) :=
  ⟨fun e => not_isSuslinLine_real (h.of_orderIso e)⟩

/-! ## Reformulation of Suslin's Hypothesis -/

/-- Suslin's Hypothesis is equivalent to the statement that every ccc linear continuum is
separable, i.e. that the "separable" hypothesis in Cantor's characterisation of `ℝ` may be
weakened to the countable chain condition. -/
theorem suslinHypothesis_iff :
    SuslinHypothesis ↔
      ∀ (α : Type) [LinearOrder α] [TopologicalSpace α] [OrderTopology α],
        IsLinearContinuum α → IsCCC α → SeparableSpace α := by
  constructor
  · intro h α _ _ _ hcont hccc
    by_contra hsep
    exact h α ⟨hcont, hccc, hsep⟩
  · intro h α _ _ _ hsus
    exact hsus.not_separable (h α hsus.continuum hsus.ccc)

/-! ## The target statement -/

/-- **Suslin's problem.**  The formal statement of the problem together with the ZFC-provable base
case and reductions:

1. separability implies the countable chain condition, so a Suslin line is exactly a ccc linear
   continuum failing the separability clause of Cantor's characterisation of `ℝ`;
2. no separable space is a Suslin line; in particular neither `ℝ` nor `ℚ` is one;
3. a Suslin line is uncountable, not second countable, and not order isomorphic to `ℝ`;
4. Suslin's Hypothesis is exactly the assertion that every ccc linear continuum is separable.

(The independence of Suslin's Hypothesis from ZFC — `◊` yields a Suslin line, `MA + ¬CH` refutes
one — is not a ZFC theorem and hence is not asserted here.) -/
theorem Suslin_line :
    IsLinearContinuum ℝ ∧ IsCCC ℝ ∧
    (∀ (α : Type) [TopologicalSpace α], SeparableSpace α → IsCCC α) ∧
    (∀ (α : Type) [LinearOrder α] [TopologicalSpace α] [OrderTopology α],
      SeparableSpace α → ¬ IsSuslinLine α) ∧
    ¬ IsSuslinLine ℝ ∧ ¬ IsSuslinLine ℚ ∧
    (∀ (α : Type) [LinearOrder α] [TopologicalSpace α] [OrderTopology α],
      IsSuslinLine α → ¬ Countable α ∧ ¬ SecondCountableTopology α ∧ IsEmpty (α ≃o ℝ)) ∧
    (SuslinHypothesis ↔
      ∀ (α : Type) [LinearOrder α] [TopologicalSpace α] [OrderTopology α],
        IsLinearContinuum α → IsCCC α → SeparableSpace α) :=
  ⟨isLinearContinuum_real, isCCC_real,
   fun α _ _ => isCCC_of_separableSpace α,
   fun α _ _ _ _ => not_isSuslinLine_of_separableSpace α,
   not_isSuslinLine_real, not_isSuslinLine_rat,
   fun _ _ _ _ h => ⟨h.not_countable, h.not_secondCountableTopology,
     not_orderIso_real_of_isSuslinLine h⟩,
   suslinHypothesis_iff⟩

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

