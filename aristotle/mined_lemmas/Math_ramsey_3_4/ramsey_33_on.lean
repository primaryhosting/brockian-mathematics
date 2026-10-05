/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset SimpleGraph

namespace Math

/-- The `(3,4)`-Ramsey property for `n`: every simple graph on `n` vertices contains
either a triangle (a `3`-clique) or an independent set of size `4`. -/

lemma ramsey_33_on (G : SimpleGraph V) (s : Finset V) (hs : 6 ≤ s.card) :
    (∃ t ⊆ s, G.IsNClique 3 t) ∨ (∃ t ⊆ s, G.IsNIndepSet 3 t) := by
  classical
  obtain ⟨v, hv⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
  have hs' : 5 ≤ (s.erase v).card := by
    rw [Finset.card_erase_of_mem hv]; omega
  have hAB : ((s.erase v).filter (fun w => G.Adj v w)).card +
      ((s.erase v).filter (fun w => ¬ G.Adj v w)).card = (s.erase v).card :=
    Finset.card_filter_add_card_filter_not _
  rcases (show 3 ≤ ((s.erase v).filter (fun w => G.Adj v w)).card ∨
      3 ≤ ((s.erase v).filter (fun w => ¬ G.Adj v w)).card by omega) with h | h
  · obtain ⟨t, hts, ht3⟩ := Finset.exists_subset_card_eq h
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp ht3
    have hx := Finset.mem_filter.mp (hts (by simp : x ∈ ({x, y, z} : Finset V)))
    have hy := Finset.mem_filter.mp (hts (by simp : y ∈ ({x, y, z} : Finset V)))
    have hz := Finset.mem_filter.mp (hts (by simp : z ∈ ({x, y, z} : Finset V)))
    have hxs : x ∈ s := Finset.mem_of_mem_erase hx.1
    have hys : y ∈ s := Finset.mem_of_mem_erase hy.1
    have hzs : z ∈ s := Finset.mem_of_mem_erase hz.1
    by_cases hxy' : G.Adj x y
    · exact Or.inl ⟨{v, x, y}, by simp [Finset.insert_subset_iff, hv, hxs, hys],
        SimpleGraph.is3Clique_triple_iff.mpr ⟨hx.2, hy.2, hxy'⟩⟩
    · by_cases hxz' : G.Adj x z
      · exact Or.inl ⟨{v, x, z}, by simp [Finset.insert_subset_iff, hv, hxs, hzs],
          SimpleGraph.is3Clique_triple_iff.mpr ⟨hx.2, hz.2, hxz'⟩⟩
      · by_cases hyz' : G.Adj y z
        · exact Or.inl ⟨{v, y, z}, by simp [Finset.insert_subset_iff, hv, hys, hzs],
            SimpleGraph.is3Clique_triple_iff.mpr ⟨hy.2, hz.2, hyz'⟩⟩
        · exact Or.inr ⟨{x, y, z}, by simp [Finset.insert_subset_iff, hxs, hys, hzs],
            isNIndepSet_three hxy hxz hyz hxy' hxz' hyz'⟩
  · obtain ⟨t, hts, ht3⟩ := Finset.exists_subset_card_eq h
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp ht3
    have hx := Finset.mem_filter.mp (hts (by simp : x ∈ ({x, y, z} : Finset V)))
    have hy := Finset.mem_filter.mp (hts (by simp : y ∈ ({x, y, z} : Finset V)))
    have hz := Finset.mem_filter.mp (hts (by simp : z ∈ ({x, y, z} : Finset V)))
    have hxs : x ∈ s := Finset.mem_of_mem_erase hx.1
    have hys : y ∈ s := Finset.mem_of_mem_erase hy.1
    have hzs : z ∈ s := Finset.mem_of_mem_erase hz.1
    have hvx : v ≠ x := fun e => (Finset.ne_of_mem_erase hx.1) e.symm
    have hvy : v ≠ y := fun e => (Finset.ne_of_mem_erase hy.1) e.symm
    have hvz : v ≠ z := fun e => (Finset.ne_of_mem_erase hz.1) e.symm
    by_cases hxy' : G.Adj x y
    · by_cases hxz' : G.Adj x z
      · by_cases hyz' : G.Adj y z
        · exact Or.inl ⟨{x, y, z}, by simp [Finset.insert_subset_iff, hxs, hys, hzs],
            SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy', hxz', hyz'⟩⟩
        · exact Or.inr ⟨{v, y, z}, by simp [Finset.insert_subset_iff, hv, hys, hzs],
            isNIndepSet_three hvy hvz hyz hy.2 hz.2 hyz'⟩
      · exact Or.inr ⟨{v, x, z}, by simp [Finset.insert_subset_iff, hv, hxs, hzs],
          isNIndepSet_three hvx hvz hxz hx.2 hz.2 hxz'⟩
    · exact Or.inr ⟨{v, x, y}, by simp [Finset.insert_subset_iff, hv, hxs, hys],
        isNIndepSet_three hvx hvy hxy hx.2 hy.2 hxy'⟩

end Helpers

/-- **Key intermediate lemma**: `R(3,4) ≤ 9`. Every graph on 9 vertices contains a triangle
or an independent set of size 4. -/
