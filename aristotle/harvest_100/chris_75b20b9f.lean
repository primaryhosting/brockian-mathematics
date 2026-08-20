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
def RamseyProp (n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree 3 ∨ ¬ Gᶜ.CliqueFree 4

/-! ### Upper bound : every graph on 9 vertices has a triangle or an independent 4-set -/

section Upper

variable {G : SimpleGraph (Fin 9)} [DecidableRel G.Adj]
  (h3 : G.CliqueFree 3) (h4 : Gᶜ.CliqueFree 4)

omit [DecidableRel G.Adj] in
include h3 in
/-- Triangle-freeness in element form. -/
theorem no_triangle {a b c : Fin 9} (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    False :=
  h3 {a, b, c} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)

omit [DecidableRel G.Adj] in
include h4 in
/-- No independent set of size four, in element form. -/
theorem no_indep_four {a b c d : Fin 9} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (nab : ¬ G.Adj a b) (nac : ¬ G.Adj a c) (nad : ¬ G.Adj a d)
    (nbc : ¬ G.Adj b c) (nbd : ¬ G.Adj b d) (ncd : ¬ G.Adj c d) : False := by
  refine h4 {a, b, c, d} ⟨?_, ?_⟩
  · intro x hx y hy hxy
    simp only [coe_insert, Set.mem_insert_iff, coe_singleton, Set.mem_singleton_iff] at hx hy
    refine ⟨hxy, ?_⟩
    have hs : ∀ {u w : Fin 9}, ¬ G.Adj u w → ¬ G.Adj w u := fun h hw => h hw.symm
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hxy
        | assumption
        | exact hs (by assumption)
  · rw [card_insert_of_notMem (by simp [hab, hac, had]),
      card_insert_of_notMem (by simp [hbc, hbd]),
      card_insert_of_notMem (by simp [hcd]), card_singleton]

include h3 h4 in
/-- In a triangle-free graph on 9 vertices with no independent 4-set, every degree is at most 3. -/
theorem degree_le_three (v : Fin 9) : G.degree v ≤ 3 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (n := 4) (s := G.neighborFinset v) hlt
  refine h4 t ⟨?_, htc⟩
  intro x hx y hy hxy
  refine ⟨hxy, fun hadj => ?_⟩
  have hvx : G.Adj v x := by
    simpa using hts (by simpa using hx)
  have hvy : G.Adj v y := by
    simpa using hts (by simpa using hy)
  exact no_triangle h3 hvx hvy hadj

include h3 h4 in
/-- In a triangle-free graph on 9 vertices with no independent 4-set, every degree is at least 3. -/
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
theorem no_good_graph_nine : False := by
  have hdeg : ∀ v : Fin 9, G.degree v = 3 := fun v =>
    le_antisymm (degree_le_three h3 h4 v) (three_le_degree h3 h4 v)
  have hsum := G.sum_degrees_eq_twice_card_edges
  rw [Finset.sum_congr rfl (fun v _ => hdeg v)] at hsum
  simp at hsum
  omega

end Upper

theorem ramseyProp_nine : RamseyProp 9 := by
  intro G
  classical
  by_contra hcon
  push_neg at hcon
  exact no_good_graph_nine hcon.1 hcon.2

/-! ### Lower bound : the circulant graph `C₈(1,4)` on 8 vertices -/

/-- The relation generating the circulant graph `C₈(1,4)` (the Wagner graph). -/
def r8 (a b : Fin 8) : Prop := (a.val + 1) % 8 = b.val ∨ (a.val + 4) % 8 = b.val

instance : DecidableRel r8 := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The Wagner graph: the circulant graph on 8 vertices with connection set `{±1, 4}`.
It is triangle-free and has independence number 3. -/
def G8 : SimpleGraph (Fin 8) := SimpleGraph.fromRel r8

instance : DecidableRel G8.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

set_option maxRecDepth 100000 in
theorem G8_cliqueFree_three : G8.CliqueFree 3 := by
  unfold SimpleGraph.CliqueFree; decide

set_option maxRecDepth 100000 in
theorem G8_compl_cliqueFree_four : G8ᶜ.CliqueFree 4 := by
  unfold SimpleGraph.CliqueFree; decide

/-- For `n ≤ 8`, the graph induced by the Wagner graph on the first `n` vertices witnesses
`¬ RamseyProp n`. -/
theorem not_ramseyProp_of_le_eight {n : ℕ} (hn : n ≤ 8) : ¬ RamseyProp n := by
  intro h
  set f : Fin n ↪ Fin 8 := Fin.castLEEmb hn with hf
  set H : SimpleGraph (Fin n) := SimpleGraph.comap f G8 with hH
  have hinj : Function.Injective f := f.injective
  have e1 : H ↪g G8 := SimpleGraph.Embedding.comap f G8
  have e2 : Hᶜ ↪g G8ᶜ := by
    refine ⟨f, ?_⟩
    intro a b
    simp only [SimpleGraph.compl_adj, hH, SimpleGraph.comap_adj]
    constructor
    · rintro ⟨hne, hadj⟩
      exact ⟨fun hab => hne (by rw [hab]), hadj⟩
    · rintro ⟨hne, hadj⟩
      exact ⟨fun hab => hne (hinj hab), hadj⟩
  rcases h H with hc | hc
  · exact hc (G8_cliqueFree_three.comap e1)
  · exact hc (G8_compl_cliqueFree_four.comap e2)

/-- **R(3,4) = 9**: nine is the least number of vertices forcing a triangle or an
independent set of size four. -/
theorem ramsey_3_4 : IsLeast {n : ℕ | RamseyProp n} 9 := by
  refine ⟨ramseyProp_nine, ?_⟩
  intro n hn
  by_contra hlt
  exact not_ramseyProp_of_le_eight (by omega) hn

end Math
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

