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
