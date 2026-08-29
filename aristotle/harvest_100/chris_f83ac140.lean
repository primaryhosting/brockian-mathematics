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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## The countable chain condition -/

/-- A topological space satisfies the **countable chain condition** (ccc) if every family of
pairwise disjoint nonempty open sets is countable. -/
def CCC (α : Type) [TopologicalSpace α] : Prop :=
  ∀ S : Set (Set α), (∀ s ∈ S, IsOpen s) → (∀ s ∈ S, s.Nonempty) →
    S.PairwiseDisjoint id → S.Countable

/-- Every separable space satisfies the countable chain condition. -/
theorem ccc_of_separableSpace (α : Type) [TopologicalSpace α] [TopologicalSpace.SeparableSpace α] :
    CCC α := fun _ hopen hne hdisj =>
  Set.PairwiseDisjoint.countable_of_isOpen (s := id) hdisj hopen hne

/-- The countable chain condition is a topological invariant. -/
theorem CCC.of_homeomorph {α β : Type} [TopologicalSpace α] [TopologicalSpace β] (e : α ≃ₜ β)
    (h : CCC α) : CCC β := by
  intro S hopen hne hdisj
  have key : ((fun s => e ⁻¹' s) '' S).Countable := by
    refine h _ ?_ ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      exact (hopen s hs).preimage e.continuous
    · rintro _ ⟨s, hs, rfl⟩
      obtain ⟨x, hx⟩ := hne s hs
      exact ⟨e.symm x, by simpa using hx⟩
    · rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩ hst
      have hst' : s ≠ t := fun h' => hst (by rw [h'])
      have := hdisj hs ht hst'
      simpa [Set.disjoint_left, Function.onFun] using
        fun x hx hx' => (Set.disjoint_left.1 this) hx hx'
  have : S = (fun t => e.symm ⁻¹' t) '' ((fun s => e ⁻¹' s) '' S) := by
    ext s
    constructor
    · intro hs
      exact ⟨e ⁻¹' s, ⟨s, hs, rfl⟩, by ext x; simp⟩
    · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      have ht' : e.symm ⁻¹' (e ⁻¹' t) = t := by ext x; simp
      simpa only [ht'] using ht
  rw [this]
  exact key.image _

/-! ## Suslin lines -/

/-- A **Suslin line** is a nonempty dense linear order without endpoints, equipped with its
order topology, which satisfies the countable chain condition but is not separable.

(Equivalently, one often additionally requires order-completeness; this is inessential, since
the Dedekind completion of such an order is again ccc and non-separable.) -/
structure IsSuslinLine (α : Type) [LinearOrder α] [TopologicalSpace α] [OrderTopology α] :
    Prop where
  /-- The order is nontrivial (in particular the space is nonempty). -/
  nontrivial : Nontrivial α
  /-- The order is dense: between any two points there is a third. -/
  densely_ordered : DenselyOrdered α
  /-- The order has no least element. -/
  no_min : NoMinOrder α
  /-- The order has no greatest element. -/
  no_max : NoMaxOrder α
  /-- Every family of pairwise disjoint nonempty open sets is countable. -/
  ccc : CCC α
  /-- The space has no countable dense subset. -/
  not_separable : ¬ TopologicalSpace.SeparableSpace α

/-- **Suslin's problem.** Is there a Suslin line? The statement `SuslinLineExists` asserts that
there is one. -/
def SuslinLineExists : Prop :=
  ∃ (α : Type) (_ : LinearOrder α) (_ : TopologicalSpace α),
    ∃ _ : OrderTopology α, IsSuslinLine α

/-- **Suslin's hypothesis (SH)**: there is no Suslin line, i.e. every ccc dense linear order
without endpoints is separable. -/
def SuslinHypothesis : Prop := ¬ SuslinLineExists

/-- Suslin's hypothesis, unfolded: every nontrivial dense linear order without endpoints which
is ccc in its order topology is separable. -/
theorem suslinHypothesis_iff :
    SuslinHypothesis ↔
      ∀ (α : Type) (_ : LinearOrder α) (_ : TopologicalSpace α) (_ : OrderTopology α),
        Nontrivial α → DenselyOrdered α → NoMinOrder α → NoMaxOrder α → CCC α →
          TopologicalSpace.SeparableSpace α := by
  constructor
  · intro h α inst1 inst2 inst3 hnt hdo hmin hmax hccc
    by_contra hsep
    exact h ⟨α, inst1, inst2, inst3, ⟨hnt, hdo, hmin, hmax, hccc, hsep⟩⟩
  · rintro h ⟨α, inst1, inst2, inst3, hS⟩
    exact hS.not_separable
      (h α inst1 inst2 inst3 hS.nontrivial hS.densely_ordered hS.no_min hS.no_max hS.ccc)

/-! ## The real line is not a Suslin line -/

/-- The real line satisfies the countable chain condition. -/
theorem ccc_real : CCC ℝ := ccc_of_separableSpace ℝ

/-- The real line is *not* a Suslin line: it is a ccc dense linear order without endpoints, but
it *is* separable. This is the base case of Suslin's problem — the question is precisely whether
`ℝ` is characterised up to order isomorphism by the remaining properties. -/
theorem not_isSuslinLine_real : ¬ IsSuslinLine ℝ := fun h => h.not_separable inferInstance

/-- No Suslin line is order-isomorphic to the real line. -/
theorem not_orderIso_real_of_isSuslinLine (α : Type) [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] (h : IsSuslinLine α) : IsEmpty (α ≃o ℝ) := by
  constructor
  intro e
  have hh : α ≃ₜ ℝ := e.toHomeomorph
  exact h.not_separable
    (hh.symm.surjective.denseRange.separableSpace hh.symm.continuous)

/-- A Suslin line is not second countable (so it is a ccc space that is not second countable). -/
theorem not_secondCountable_of_isSuslinLine (α : Type) [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] (h : IsSuslinLine α) : ¬ SecondCountableTopology α :=
  fun h2 => h.not_separable (@TopologicalSpace.SecondCountableTopology.to_separableSpace α _ h2)

/-- A Suslin line is uncountable: a countable space is separable. -/
theorem uncountable_of_isSuslinLine (α : Type) [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] (h : IsSuslinLine α) : Uncountable α := by
  rw [← not_countable_iff]
  intro hc
  exact h.not_separable (@TopologicalSpace.Countable.to_separableSpace α _ hc)

/-- **Suslin's problem, formalized.**

1. Separability always implies the countable chain condition (for any topological space); a
   Suslin line is exactly a witness to the failure of the converse among dense linear orders
   without endpoints.
2. Suslin's hypothesis says precisely that every nontrivial, ccc, dense linear order without
   endpoints is separable.
3. The real line is a ccc, separable, dense linear order without endpoints — hence not a Suslin
   line; and no Suslin line is order-isomorphic to `ℝ`, nor second countable, and every Suslin
   line is uncountable.
-/
theorem Suslin_line :
    (∀ (α : Type) (_ : TopologicalSpace α), TopologicalSpace.SeparableSpace α → CCC α) ∧
    (SuslinHypothesis ↔
      ∀ (α : Type) (_ : LinearOrder α) (_ : TopologicalSpace α) (_ : OrderTopology α),
        Nontrivial α → DenselyOrdered α → NoMinOrder α → NoMaxOrder α → CCC α →
          TopologicalSpace.SeparableSpace α) ∧
    (CCC ℝ ∧ DenselyOrdered ℝ ∧ NoMinOrder ℝ ∧ NoMaxOrder ℝ ∧
      TopologicalSpace.SeparableSpace ℝ ∧ ¬ IsSuslinLine ℝ) ∧
    (∀ (α : Type) (_ : LinearOrder α) (_ : TopologicalSpace α) (_ : OrderTopology α),
      IsSuslinLine α → IsEmpty (α ≃o ℝ) ∧ ¬ SecondCountableTopology α ∧ Uncountable α) := by
  refine ⟨fun α _ _ => ccc_of_separableSpace α, suslinHypothesis_iff,
    ⟨ccc_real, inferInstance, inferInstance, inferInstance, inferInstance,
      not_isSuslinLine_real⟩, ?_⟩
  intro α _ _ _ h
  exact ⟨not_orderIso_real_of_isSuslinLine α h, not_secondCountable_of_isSuslinLine α h,
    uncountable_of_isSuslinLine α h⟩

end Frontier

