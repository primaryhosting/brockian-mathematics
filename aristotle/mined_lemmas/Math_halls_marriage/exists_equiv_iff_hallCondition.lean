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

set_option grind.warning false

namespace Math

open Finset Function

variable {V W : Type*}

/-- The bipartite graph on `V ⊕ W` determined by a relation `r : V → W → Prop`:
the only edges join a vertex `v` of the left part to a vertex `w` of the right part,
and such an edge is present exactly when `r v w` holds. -/

lemma exists_equiv_iff_hallCondition [Fintype V] [Fintype W] (r : V → W → Prop) :
    (∃ e : V ≃ W, ∀ v, r v (e v)) ↔ HallCondition r := by
  classical
  constructor
  · rintro ⟨e, he⟩
    constructor
    · intro A
      refine le_trans (le_of_eq (Finset.card_image_of_injective A e.injective).symm) ?_
      refine Finset.card_le_card ?_
      intro b hb
      simp only [Finset.mem_image] at hb
      obtain ⟨a, ha, rfl⟩ := hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨a, ha, he a⟩
    · intro B
      refine le_trans (le_of_eq (Finset.card_image_of_injective B e.symm.injective).symm) ?_
      refine Finset.card_le_card ?_
      intro a ha
      simp only [Finset.mem_image] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨b, hb, ?_⟩
      have := he (e.symm b)
      simpa using this
  · rintro ⟨h1, h2⟩
    obtain ⟨f, hf, hfr⟩ :=
      (Fintype.all_card_le_filter_rel_iff_exists_injective r).1 (by
        intro A; simpa using h1 A)
    obtain ⟨g, hg, hgr⟩ :=
      (Fintype.all_card_le_filter_rel_iff_exists_injective (fun (b : W) (a : V) => r a b)).1 (by
        intro B; simpa using h2 B)
    have hcard : Fintype.card V = Fintype.card W :=
      le_antisymm (Fintype.card_le_of_injective f hf) (Fintype.card_le_of_injective g hg)
    have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hcard⟩
    exact ⟨Equiv.ofBijective f hbij, fun v => hfr v⟩

/-- **Hall's marriage theorem.** The bipartite graph associated to a relation `r : V → W → Prop`
between two finite vertex sets has a perfect matching if and only if Hall's condition holds:
every set of vertices on either side has at least as many neighbours as elements. -/
