/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

open Finset

/-- `RamseyProp n` says that every simple graph on `n` vertices contains either a triangle
(a 3-clique) or an independent set of size 4 (a 4-clique in the complement). -/

theorem three_le_degree (v : Fin 9) : 3 ≤ G.degree v := by
  by_contra hlt
  push_neg at hlt
  -- `S` is the set of vertices distinct from `v` and not adjacent to `v`.
  set S : Finset (Fin 9) := Finset.univ \ insert v (G.neighborFinset v) with hS
  have hmemS : ∀ x, x ∈ S ↔ (x ≠ v ∧ ¬ G.Adj v x) := by
    intro x
    simp [hS, SimpleGraph.mem_neighborFinset]
  have hcard_ins : (insert v (G.neighborFinset v)).card ≤ 3 := by
    have := Finset.card_insert_le v (G.neighborFinset v)
    have hd : (G.neighborFinset v).card = G.degree v := rfl
    omega
  have hScard : 6 ≤ S.card := by
    have h1 : S.card + (insert v (G.neighborFinset v)).card = (Finset.univ : Finset (Fin 9)).card :=
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have hSe : 5 ≤ (S.erase u).card := by
    rw [Finset.card_erase_of_mem hu]; omega
  classical
  set A := (S.erase u).filter (fun x => G.Adj u x) with hA
  set B := (S.erase u).filter (fun x => ¬ G.Adj u x) with hB
  have hsum : A.card + B.card = (S.erase u).card :=
    Finset.card_filter_add_card_filter_not _
  have hu' := (hmemS u).mp hu
  rcases (by omega : 3 ≤ A.card ∨ 3 ≤ B.card) with hcase | hcase
  · obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (n := 3) hcase
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp htc
    have hmem : ∀ w ∈ ({x, y, z} : Finset (Fin 9)), w ∈ S ∧ G.Adj u w := by
      intro w hw
      have := hts hw
      rw [hA, Finset.mem_filter] at this
      exact ⟨Finset.mem_of_mem_erase this.1, this.2⟩
    obtain ⟨hxS, hux⟩ := hmem x (by simp)
    obtain ⟨hyS, huy⟩ := hmem y (by simp)
    obtain ⟨hzS, huz⟩ := hmem z (by simp)
    have hx' := (hmemS x).mp hxS
    have hy' := (hmemS y).mp hyS
    have hz' := (hmemS z).mp hzS
    exact no_indep_four h4 (Ne.symm hx'.1) (Ne.symm hy'.1) (Ne.symm hz'.1) hxy hxz hyz
      hx'.2 hy'.2 hz'.2
      (fun h => no_triangle h3 hux huy h) (fun h => no_triangle h3 hux huz h)
      (fun h => no_triangle h3 huy huz h)
  · obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (n := 3) hcase
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp htc
    have hmem : ∀ w ∈ ({x, y, z} : Finset (Fin 9)), (w ∈ S ∧ w ≠ u) ∧ ¬ G.Adj u w := by
      intro w hw
      have := hts hw
      rw [hB, Finset.mem_filter] at this
      exact ⟨⟨Finset.mem_of_mem_erase this.1, Finset.ne_of_mem_erase this.1⟩, this.2⟩
    obtain ⟨⟨hxS, hxu⟩, hux⟩ := hmem x (by simp)
    obtain ⟨⟨hyS, hyu⟩, huy⟩ := hmem y (by simp)
    obtain ⟨⟨hzS, hzu⟩, huz⟩ := hmem z (by simp)
    have hx' := (hmemS x).mp hxS
    have hy' := (hmemS y).mp hyS
    have hz' := (hmemS z).mp hzS
    by_cases hxy' : G.Adj x y
    · by_cases hxz' : G.Adj x z
      · by_cases hyz' : G.Adj y z
        · exact no_triangle h3 hxy' hxz' hyz'
        · exact no_indep_four h4 (Ne.symm hu'.1) (Ne.symm hy'.1) (Ne.symm hz'.1)
            (Ne.symm hyu) (Ne.symm hzu) hyz hu'.2 hy'.2 hz'.2 huy huz hyz'
      · exact no_indep_four h4 (Ne.symm hu'.1) (Ne.symm hx'.1) (Ne.symm hz'.1)
          (Ne.symm hxu) (Ne.symm hzu) hxz hu'.2 hx'.2 hz'.2 hux huz hxz'
    · exact no_indep_four h4 (Ne.symm hu'.1) (Ne.symm hx'.1) (Ne.symm hy'.1)
        (Ne.symm hxu) (Ne.symm hyu) hxy hu'.2 hx'.2 hy'.2 hux huy hxy'

include h3 h4 in
/-- No graph on 9 vertices is both triangle-free and free of independent 4-sets:
such a graph would be 3-regular on an odd number of vertices. -/
