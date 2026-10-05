/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math

/-- `RamseyProp r s N` says: every simple graph on `N` vertices contains either a clique of
size `r` or an independent set of size `s` (i.e. an `s`-clique in the complement).
Equivalently: every 2-colouring of the edges of `K_N` has a red `K_r` or a blue `K_s`. -/
def RamseyProp (r s N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    (∃ A : Finset (Fin N), G.IsNClique r A) ∨ (∃ B : Finset (Fin N), Gᶜ.IsNClique s B)

/-! ### The extremal graph on 8 vertices (the Wagner / Möbius–Kantor graph `C₈(1,4)`) -/

/-- Adjacency of the circulant graph `C₈(1,4)`. -/
def wadj (a b : Fin 8) : Prop :=
  ((a.val + 8 - b.val) % 8 = 1) ∨ ((a.val + 8 - b.val) % 8 = 7) ∨ ((a.val + 8 - b.val) % 8 = 4)

instance : DecidableRel wadj := fun a b => by unfold wadj; infer_instance

/-- The Wagner graph on 8 vertices: it is triangle-free and has independence number 3. -/
def W : SimpleGraph (Fin 8) where
  Adj := wadj
  symm := by intro a b; revert a b; decide
  loopless := ⟨by intro a; revert a; decide⟩

instance : DecidableRel W.Adj := fun a b => inferInstanceAs (Decidable (wadj a b))

set_option maxRecDepth 100000 in
theorem W_no_tri : ∀ A : Finset (Fin 8), ¬ W.IsNClique 3 A := by decide

set_option maxRecDepth 100000 in
theorem W_no_ind : ∀ A : Finset (Fin 8), ¬ Wᶜ.IsNClique 4 A := by decide

/-! ### Transporting cliques along an injection -/

theorem isNClique_image {m n k : ℕ} (f : Fin m → Fin n) (hf : Function.Injective f)
    (H : SimpleGraph (Fin n)) (A : Finset (Fin m)) (hA : (H.comap f).IsNClique k A) :
    H.IsNClique k (A.image f) := by
  obtain ⟨hclique, hcard⟩ := hA
  constructor
  · rintro x hx y hy hxy
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact hclique ha hb (fun h => hxy (by rw [h]))
  · rw [Finset.card_image_of_injective _ hf, hcard]

theorem comap_compl {m n : ℕ} (f : Fin m → Fin n) (hf : Function.Injective f)
    (H : SimpleGraph (Fin n)) : (H.comap f)ᶜ = (Hᶜ).comap f := by
  ext a b
  simp [SimpleGraph.compl_adj, SimpleGraph.comap_adj, hf.eq_iff]

theorem not_ramsey_of_le_eight {N : ℕ} (hN : N ≤ 8) : ¬ RamseyProp 3 4 N := by
  intro h
  have hf : Function.Injective (Fin.castLE hN) := Fin.castLE_injective hN
  rcases h (W.comap (Fin.castLE hN)) with ⟨A, hA⟩ | ⟨B, hB⟩
  · exact W_no_tri _ (isNClique_image _ hf W A hA)
  · rw [comap_compl _ hf] at hB
    exact W_no_ind _ (isNClique_image _ hf Wᶜ B hB)

/-! ### The upper bound: every graph on 9 vertices has a triangle or an independent 4-set -/

section Upper

variable {G : SimpleGraph (Fin 9)}

theorem no_triangle (h3 : ∀ A : Finset (Fin 9), ¬ G.IsNClique 3 A)
    {a b c : Fin 9} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h1 : G.Adj a b) (h2 : G.Adj a c) (h3' : G.Adj b c) : False := by
  refine h3 {a, b, c} ⟨?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl <;>
      simp_all [G.symm h1, G.symm h2, G.symm h3']
  · rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]

theorem no_indep (h4 : ∀ B : Finset (Fin 9), ¬ Gᶜ.IsNClique 4 B)
    {a b c d : Fin 9} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (n1 : ¬ G.Adj a b) (n2 : ¬ G.Adj a c) (n3 : ¬ G.Adj a d)
    (n4 : ¬ G.Adj b c) (n5 : ¬ G.Adj b d) (n6 : ¬ G.Adj c d) : False := by
  refine h4 {a, b, c, d} ⟨?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at hx hy
    have s1 : ¬ G.Adj b a := fun h => n1 h.symm
    have s2 : ¬ G.Adj c a := fun h => n2 h.symm
    have s3 : ¬ G.Adj d a := fun h => n3 h.symm
    have s4 : ¬ G.Adj c b := fun h => n4 h.symm
    have s5 : ¬ G.Adj d b := fun h => n5 h.symm
    have s6 : ¬ G.Adj d c := fun h => n6 h.symm
    rcases hx with rfl|rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl|rfl <;>
      simp_all [SimpleGraph.compl_adj]
  · rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]),
      Finset.card_insert_of_notMem (by simp [hcd]), Finset.card_singleton]

/-- If `T` is a set of three vertices, all non-adjacent to `v` and pairwise non-adjacent,
then `insert v T` is an independent set of size four. -/
theorem indep_of_card_three (h4 : ∀ B : Finset (Fin 9), ¬ Gᶜ.IsNClique 4 B)
    (v : Fin 9) (T : Finset (Fin 9)) (hcard : T.card = 3) (hvT : v ∉ T)
    (hv : ∀ w ∈ T, ¬ G.Adj v w) (hTT : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ G.Adj x y) : False := by
  refine h4 (insert v T) ⟨?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
    rw [SimpleGraph.compl_adj]
    refine ⟨hxy, ?_⟩
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact absurd rfl hxy
    · exact hv _ hy
    · exact fun h => hv _ hx h.symm
    · exact hTT _ hx _ hy hxy
  · rw [Finset.card_insert_of_notMem hvT, hcard]

theorem degree_le_three [DecidableRel G.Adj] (h3 : ∀ A : Finset (Fin 9), ¬ G.IsNClique 3 A)
    (h4 : ∀ B : Finset (Fin 9), ¬ Gᶜ.IsNClique 4 B) (v : Fin 9) :
    G.degree v ≤ 3 := by
  by_contra hlt
  obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq
    (show 4 ≤ (G.neighborFinset v).card by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; omega)
  refine h4 T ⟨?_, hcard⟩
  intro x hx y hy hxy
  rw [SimpleGraph.compl_adj]
  refine ⟨hxy, fun hadj => ?_⟩
  have hvx : G.Adj v x := by simpa using hT hx
  have hvy : G.Adj v y := by simpa using hT hy
  exact no_triangle h3 (G.ne_of_adj hvx) (G.ne_of_adj hvy) hxy hvx hvy hadj

theorem three_le_degree [DecidableRel G.Adj] (h3 : ∀ A : Finset (Fin 9), ¬ G.IsNClique 3 A)
    (h4 : ∀ B : Finset (Fin 9), ¬ Gᶜ.IsNClique 4 B) (v : Fin 9) :
    3 ≤ G.degree v := by
  by_contra hlt
  push_neg at hlt
  set S : Finset (Fin 9) := Finset.univ \ (insert v (G.neighborFinset v)) with hSdef
  have hmem : ∀ w ∈ S, w ≠ v ∧ ¬ G.Adj v w := by
    intro w hw
    rw [hSdef, Finset.mem_sdiff] at hw
    simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or] at hw
    exact ⟨hw.2.1, hw.2.2⟩
  have hvS : v ∉ S := by
    rw [hSdef]; simp
  have hScard : 6 ≤ S.card := by
    have hv : v ∉ G.neighborFinset v := by simp
    have hc : (insert v (G.neighborFinset v)).card = 1 + G.degree v := by
      rw [Finset.card_insert_of_notMem hv, SimpleGraph.card_neighborFinset_eq_degree]
      omega
    have hsum := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (insert v (G.neighborFinset v)))
    rw [← hSdef] at hsum
    simp only [Finset.card_univ, Fintype.card_fin] at hsum
    omega
  obtain ⟨u, hu⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  have huv : u ≠ v := (hmem u hu).1
  have hvu : ¬ G.Adj v u := (hmem u hu).2
  set A : Finset (Fin 9) := (S.erase u).filter (fun w => G.Adj u w) with hAdef
  set B : Finset (Fin 9) := (S.erase u).filter (fun w => ¬ G.Adj u w) with hBdef
  have hsplit : A.card + B.card = (S.erase u).card :=
    Finset.card_filter_add_card_filter_not _
  have herase : (S.erase u).card = S.card - 1 := Finset.card_erase_of_mem hu
  have hAB : 3 ≤ A.card ∨ 3 ≤ B.card := by omega
  rcases hAB with hA | hB
  · obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hA
    have hTA : ∀ w ∈ T, w ∈ S ∧ G.Adj u w := by
      intro w hw
      have := hT hw
      rw [hAdef, Finset.mem_filter] at this
      exact ⟨Finset.mem_of_mem_erase this.1, this.2⟩
    refine indep_of_card_three h4 v T hTcard (fun hv => hvS ((hTA v hv).1)) ?_ ?_
    · intro w hw
      exact (hmem w (hTA w hw).1).2
    · intro x hx y hy hxy hadj
      exact no_triangle h3 (G.ne_of_adj (hTA x hx).2) (G.ne_of_adj (hTA y hy).2) hxy
        (hTA x hx).2 (hTA y hy).2 hadj
  · obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hB
    have hTB : ∀ w ∈ T, w ∈ S ∧ w ≠ u ∧ ¬ G.Adj u w := by
      intro w hw
      have := hT hw
      rw [hBdef, Finset.mem_filter] at this
      exact ⟨Finset.mem_of_mem_erase this.1, Finset.ne_of_mem_erase this.1, this.2⟩
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hTcard
    have ha := hTB a (by simp)
    have hb := hTB b (by simp)
    have hc := hTB c (by simp)
    have hva : ¬ G.Adj v a := (hmem a ha.1).2
    have hvb : ¬ G.Adj v b := (hmem b hb.1).2
    have hvc : ¬ G.Adj v c := (hmem c hc.1).2
    have hav : a ≠ v := (hmem a ha.1).1
    have hbv : b ≠ v := (hmem b hb.1).1
    have hcv : c ≠ v := (hmem c hc.1).1
    by_cases hab' : G.Adj a b
    · by_cases hac' : G.Adj a c
      · by_cases hbc' : G.Adj b c
        · exact no_triangle h3 hab hac hbc hab' hac' hbc'
        · exact no_indep h4 (Ne.symm huv) (Ne.symm hbv) (Ne.symm hcv)
            (Ne.symm hb.2.1) (Ne.symm hc.2.1) hbc hvu hvb hvc hb.2.2 hc.2.2 hbc'
      · exact no_indep h4 (Ne.symm huv) (Ne.symm hav) (Ne.symm hcv)
          (Ne.symm ha.2.1) (Ne.symm hc.2.1) hac hvu hva hvc ha.2.2 hc.2.2 hac'
    · exact no_indep h4 (Ne.symm huv) (Ne.symm hav) (Ne.symm hbv)
        (Ne.symm ha.2.1) (Ne.symm hb.2.1) hab hvu hva hvb ha.2.2 hb.2.2 hab'

theorem ramsey_upper : RamseyProp 3 4 9 := by
  intro G
  by_contra hcon
  push_neg at hcon
  obtain ⟨h3, h4⟩ := hcon
  haveI : DecidableRel G.Adj := Classical.decRel _
  have hdeg : ∀ v : Fin 9, G.degree v = 3 := fun v =>
    le_antisymm (degree_le_three h3 h4 v) (three_le_degree h3 h4 v)
  have hsum := SimpleGraph.sum_degrees_eq_twice_card_edges G
  rw [Finset.sum_congr rfl (fun v _ => hdeg v)] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega

end Upper

/-- **R(3,4) = 9.**  Nine is the least `N` such that every simple graph on `N` vertices
contains a triangle or an independent set of size four. -/
theorem ramsey_3_4 : IsLeast {N : ℕ | RamseyProp 3 4 N} 9 := by
  constructor
  · exact ramsey_upper
  · intro N hN
    by_contra h
    exact not_ramsey_of_le_eight (by omega) hN

end Math

