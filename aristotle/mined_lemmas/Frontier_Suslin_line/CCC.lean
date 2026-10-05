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
