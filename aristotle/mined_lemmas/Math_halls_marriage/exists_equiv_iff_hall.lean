import Mathlib

/-!
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Function

namespace Math

variable {L R : Type*}

/-- The bipartite graph on `L ⊕ R` whose edges are exactly the pairs `(a, b)` with `r a b`,
where `a : L` is a left vertex and `b : R` is a right vertex. -/

theorem exists_equiv_iff_hall [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (r : L → R → Prop) [DecidableRel r] :
    (∃ e : L ≃ R, ∀ a, r a (e a)) ↔
      ((∀ A : Finset L, #A ≤ #{b : R | ∃ a ∈ A, r a b}) ∧
        (∀ B : Finset R, #B ≤ #{a : L | ∃ b ∈ B, r a b})) := by
  constructor
  · rintro ⟨e, he⟩
    constructor
    · intro A
      rw [← Finset.card_image_of_injective A e.injective]
      refine Finset.card_le_card ?_
      intro b hb
      simp only [Finset.mem_image] at hb
      obtain ⟨a, ha, rfl⟩ := hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨a, ha, he a⟩
    · intro B
      rw [← Finset.card_image_of_injective B e.symm.injective]
      refine Finset.card_le_card ?_
      intro a ha
      simp only [Finset.mem_image] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨b, hb, ?_⟩
      simpa using he (e.symm b)
  · rintro ⟨hL, hR⟩
    obtain ⟨f, hf, hfr⟩ :=
      (Fintype.all_card_le_filter_rel_iff_exists_injective r).mp hL
    obtain ⟨g, hg, hgr⟩ :=
      (Fintype.all_card_le_filter_rel_iff_exists_injective (fun b a => r a b)).mp hR
    have hcard : Fintype.card L = Fintype.card R :=
      le_antisymm (Fintype.card_le_of_injective f hf) (Fintype.card_le_of_injective g hg)
    have hbij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hcard⟩
    exact ⟨Equiv.ofBijective f hbij, fun a => hfr a⟩

/-- **Hall's Marriage Theorem** for bipartite graphs: the bipartite graph on `L ⊕ R` determined
by the relation `r` has a perfect matching if and only if Hall's condition holds on both sides,
i.e. every set of left vertices has at least as many neighbours, and likewise for the right. -/
