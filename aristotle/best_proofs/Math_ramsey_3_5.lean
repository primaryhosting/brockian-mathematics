import Mathlib
import RequestProject.Ramsey

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

import Mathlib

/-!
# The Ramsey number `R(3,5) = 14`

This file proves that `14` is the least `n` such that every simple graph on `n` vertices
contains a triangle (a `3`-clique) or an independent set of size `5` (a `5`-clique of the
complement).
-/

namespace Math

open Finset SimpleGraph

section Bounds

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- `NoCliqueIn G n s` says that `G` has no `n`-clique contained in the vertex set `s`. -/
def NoCliqueIn (G : SimpleGraph V) (n : ℕ) (s : Finset V) : Prop :=
  ∀ t ⊆ s, ¬ G.IsNClique n t

omit [DecidableEq V] [Fintype V] in
theorem NoCliqueIn.mono {G : SimpleGraph V} {n : ℕ} {s t : Finset V}
    (h : NoCliqueIn G n s) (hts : t ⊆ s) : NoCliqueIn G n t :=
  fun u hu => h u (hu.trans hts)

omit [DecidableEq V] [Fintype V] in
theorem card_lt_of_isClique {G : SimpleGraph V} {n : ℕ} {s t : Finset V}
    (hcl : G.IsClique (t : Set V)) (h : NoCliqueIn G n s) (hts : t ⊆ s) : t.card < n := by
  by_contra hle
  push_neg at hle
  obtain ⟨u, hut, hu⟩ := Finset.exists_subset_card_eq hle
  exact h u (hut.trans hts) ⟨hcl.subset (by exact_mod_cast hut), hu⟩

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In a triangle-free graph the neighbourhood of a vertex is independent. -/
theorem nbrs_indep {s : Finset V} {v : V} (hv : v ∈ s) (h3 : NoCliqueIn G 3 s) :
    Gᶜ.IsClique ((s ∩ G.neighborFinset v : Finset V) : Set V) := by
  intro a ha b hb hab
  simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe, mem_neighborFinset] at ha hb
  refine ⟨hab, ?_⟩
  intro hadj
  refine h3 {v, a, b} ?_ (is3Clique_triple_iff.2 ⟨ha.2, hb.2, hadj⟩)
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact hv
  · exact ha.1
  · exact hb.1

theorem nbr_card_lt {k : ℕ} {s : Finset V} {v : V} (hv : v ∈ s) (h3 : NoCliqueIn G 3 s)
    (hk : NoCliqueIn Gᶜ k s) : (s ∩ G.neighborFinset v).card < k :=
  card_lt_of_isClique (nbrs_indep hv h3) hk Finset.inter_subset_left

/-- The non-neighbours of `v` inside `s` contain no `k`-independent set, if `s` contains no
`(k+1)`-independent set. -/
theorem nonNbrs_noClique {k : ℕ} {s : Finset V} {v : V} (hv : v ∈ s)
    (hk : NoCliqueIn Gᶜ (k + 1) s) :
    NoCliqueIn Gᶜ k (s \ insert v (G.neighborFinset v)) := by
  intro t ht hcl
  have hvt : v ∉ t := by
    intro hvt
    have := ht hvt
    simp at this
  refine hk (insert v t) (Finset.insert_subset hv (ht.trans Finset.sdiff_subset)) ⟨?_, ?_⟩
  · rw [Finset.coe_insert]
    refine hcl.1.insert ?_
    intro b hb hvb
    have hb' := ht (by exact_mod_cast hb)
    simp only [Finset.mem_sdiff, Finset.mem_insert, mem_neighborFinset, not_or] at hb'
    exact ⟨hvb, hb'.2.2⟩
  · rw [Finset.card_insert_of_notMem hvt, hcl.2]

theorem card_split (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) (v : V) :
    s.card ≤ 1 + (s ∩ G.neighborFinset v).card + (s \ insert v (G.neighborFinset v)).card := by
  have hsub : s ⊆ insert v ((s ∩ G.neighborFinset v) ∪ (s \ insert v (G.neighborFinset v))) := by
    intro x hx
    by_cases hxv : x = v
    · simp [hxv]
    · by_cases hadj : G.Adj v x
      · simp [Finset.mem_insert, Finset.mem_union, Finset.mem_inter, hx, hadj]
      · simp [Finset.mem_insert, Finset.mem_union, Finset.mem_sdiff, hx, hxv, hadj]
  calc s.card ≤ _ := Finset.card_le_card hsub
    _ ≤ 1 + ((s ∩ G.neighborFinset v) ∪ (s \ insert v (G.neighborFinset v))).card := by
        simp [Nat.add_comm]
    _ ≤ 1 + ((s ∩ G.neighborFinset v).card + (s \ insert v (G.neighborFinset v)).card) := by
        exact Nat.add_le_add_left (Finset.card_union_le _ _) 1
    _ = 1 + (s ∩ G.neighborFinset v).card + (s \ insert v (G.neighborFinset v)).card := by ring

omit [Fintype V] in
/-- `R(2,3)`-type bound: a triangle-free graph whose vertex set `s` induces a complete graph
has at most `2` vertices. -/
theorem bound_two {s : Finset V} (h3 : NoCliqueIn G 3 s) (h2 : NoCliqueIn Gᶜ 2 s) :
    s.card ≤ 2 := by
  have hcl : G.IsClique (s : Set V) := by
    intro a ha b hb hab
    by_contra hadj
    refine h2 {a, b} ?_ ⟨?_, Finset.card_pair hab⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    · rw [Finset.coe_pair]
      exact SimpleGraph.isClique_pair.2 (fun _ => ⟨hab, hadj⟩)
  have := card_lt_of_isClique hcl h3 (le_refl s)
  omega

/-- `R(3,3) ≤ 6`. -/
theorem bound_three {s : Finset V} (h3 : NoCliqueIn G 3 s) (hk : NoCliqueIn Gᶜ 3 s) :
    s.card ≤ 5 := by
  rcases Finset.eq_empty_or_nonempty s with rfl | ⟨v, hv⟩
  · simp
  · have hd : (s ∩ G.neighborFinset v).card < 3 := nbr_card_lt hv h3 hk
    have hM : (s \ insert v (G.neighborFinset v)).card ≤ 2 :=
      bound_two (h3.mono Finset.sdiff_subset) (nonNbrs_noClique (k := 2) hv hk)
    have := card_split G s v
    omega

/-- Every vertex of `s` having `3` neighbours inside `s` forces `s` to have even cardinality. -/
theorem even_card_of_three_regular {s : Finset V}
    (h : ∀ v ∈ s, (s ∩ G.neighborFinset v).card = 3) : Even s.card := by
  classical
  set G' : SimpleGraph V :=
    { Adj := fun a b => G.Adj a b ∧ a ∈ s ∧ b ∈ s
      symm := fun a b hab => ⟨hab.1.symm, hab.2.2, hab.2.1⟩
      loopless := ⟨fun a ha => G.irrefl ha.1⟩ } with hG'
  haveI : DecidableRel G'.Adj := fun a b => by
    rw [hG']
    exact inferInstanceAs (Decidable (G.Adj a b ∧ a ∈ s ∧ b ∈ s))
  have hdeg : ∀ v : V, G'.neighborFinset v = if v ∈ s then s ∩ G.neighborFinset v else ∅ := by
    intro v
    ext u
    by_cases hv : v ∈ s <;>
      simp [hv, mem_neighborFinset, hG', Finset.mem_inter, and_comm]
  have key : Finset.univ.filter (fun v => Odd (G'.degree v)) = s := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hodd
      by_contra hv
      rw [SimpleGraph.degree, hdeg v, if_neg hv] at hodd
      simp at hodd
    · intro hv
      rw [SimpleGraph.degree, hdeg v, if_pos hv, h v hv]
      decide
  have h2 := G'.even_card_odd_degree_vertices
  rwa [key] at h2

/-- `R(3,4) ≤ 9`. -/
theorem bound_four {s : Finset V} (h3 : NoCliqueIn G 3 s)
    (hk : NoCliqueIn Gᶜ 4 s) : s.card ≤ 8 := by
  by_contra hlt
  push_neg at hlt
  have hall : ∀ v ∈ s, (s ∩ G.neighborFinset v).card = 3 := by
    intro v hv
    have hd : (s ∩ G.neighborFinset v).card < 4 := nbr_card_lt hv h3 hk
    have hM : (s \ insert v (G.neighborFinset v)).card ≤ 5 :=
      bound_three (h3.mono Finset.sdiff_subset) (nonNbrs_noClique (k := 3) hv hk)
    have := card_split G s v
    omega
  obtain ⟨v, hv⟩ : s.Nonempty := Finset.card_pos.1 (by omega)
  have hd : (s ∩ G.neighborFinset v).card = 3 := hall v hv
  have hM : (s \ insert v (G.neighborFinset v)).card ≤ 5 :=
    bound_three (h3.mono Finset.sdiff_subset) (nonNbrs_noClique (k := 3) hv hk)
  have hsplit := card_split G s v
  have heven : Even s.card := even_card_of_three_regular hall
  have : s.card = 9 := by omega
  rw [this] at heven
  simp [Nat.even_iff] at heven

/-- `R(3,5) ≤ 14`. -/
theorem bound_five {s : Finset V} (h3 : NoCliqueIn G 3 s)
    (hk : NoCliqueIn Gᶜ 5 s) : s.card ≤ 13 := by
  rcases Finset.eq_empty_or_nonempty s with rfl | ⟨v, hv⟩
  · simp
  · have hd : (s ∩ G.neighborFinset v).card < 5 := nbr_card_lt hv h3 hk
    have hM : (s \ insert v (G.neighborFinset v)).card ≤ 8 :=
      bound_four (h3.mono Finset.sdiff_subset) (nonNbrs_noClique (k := 4) hv hk)
    have := card_split G s v
    omega

end Bounds

section Construction

/-- Adjacency of the circulant graph `C₁₃(1,5)` on `ZMod 13`, encoded on `Fin 13`:
`i` and `j` are adjacent iff their difference is `±1` or `±5` modulo `13`. -/
def adj13 (i j : Fin 13) : Bool :=
  ((i.val + 13 - j.val) % 13 == 1) || ((i.val + 13 - j.val) % 13 == 12) ||
  ((i.val + 13 - j.val) % 13 == 5) || ((i.val + 13 - j.val) % 13 == 8)

/-- The circulant graph `C₁₃(1,5)`: it is triangle-free and has independence number `4`,
which witnesses `R(3,5) > 13`. -/
def graph13 : SimpleGraph (Fin 13) where
  Adj i j := adj13 i j = true
  symm := by intro i j; revert i j; decide
  loopless := by constructor; intro i; revert i; decide

instance : DecidableRel graph13.Adj := fun i j => inferInstanceAs (Decidable (adj13 i j = true))

set_option maxRecDepth 40000 in
private theorem no_triangle_aux : ∀ a b : Fin 13, (a ≠ b ∧ adj13 a b = true) →
    ∀ c : Fin 13, (c ≠ a ∧ c ≠ b ∧ adj13 a c = true ∧ adj13 b c = true) → False := by decide

set_option maxRecDepth 40000 in
set_option maxHeartbeats 1000000 in
private theorem no_indep5_aux : ∀ a b : Fin 13, (a ≠ b ∧ adj13 a b = false) →
    ∀ c : Fin 13, (c ≠ a ∧ c ≠ b ∧ adj13 a c = false ∧ adj13 b c = false) →
    ∀ d : Fin 13, (d ≠ a ∧ d ≠ b ∧ d ≠ c ∧ adj13 a d = false ∧ adj13 b d = false ∧
      adj13 c d = false) →
    ∀ e : Fin 13, (e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d ∧ adj13 a e = false ∧ adj13 b e = false ∧
      adj13 c e = false ∧ adj13 d e = false) → False := by decide

/-- Any finset of cardinality `5` contains five pairwise distinct elements. -/
theorem exists_five_distinct {α : Type*} [DecidableEq α] {t : Finset α} (h : t.card = 5) :
    ∃ a b c d e : α, a ∈ t ∧ b ∈ t ∧ c ∈ t ∧ d ∈ t ∧ e ∈ t ∧
      b ≠ a ∧ c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧ d ≠ c ∧ e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d := by
  obtain ⟨a, t1, ha, rfl, h1⟩ := Finset.card_eq_succ.1 h
  obtain ⟨b, t2, hb, rfl, h2⟩ := Finset.card_eq_succ.1 h1
  obtain ⟨c, t3, hc, rfl, h3⟩ := Finset.card_eq_succ.1 h2
  obtain ⟨d, t4, hd, rfl, h4⟩ := Finset.card_eq_succ.1 h3
  obtain ⟨e, rfl⟩ := Finset.card_eq_one.1 h4
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha hb hc hd ⊢
  exact ⟨a, b, c, d, e, by tauto, by tauto, by tauto, by tauto, by tauto,
    fun h => ha.1 h.symm, fun h => ha.2.1 h.symm, fun h => hb.1 h.symm,
    fun h => ha.2.2.1 h.symm, fun h => hb.2.1 h.symm, fun h => hc.1 h.symm,
    fun h => ha.2.2.2 h.symm, fun h => hb.2.2 h.symm, fun h => hc.2 h.symm, fun h => hd h.symm⟩

/-- `graph13` is triangle-free. -/
theorem graph13_cliqueFree_three : graph13.CliqueFree 3 := by
  intro t ht
  obtain ⟨a, b, c, -, -, -, rfl⟩ := Finset.card_eq_three.1 ht.2
  obtain ⟨hab, hac, hbc⟩ := is3Clique_triple_iff.1 ht
  exact no_triangle_aux a b ⟨hab.ne, hab⟩ c ⟨hac.ne', hbc.ne', hac, hbc⟩

/-- `graph13` has no independent set of size `5`. -/
theorem graph13_compl_cliqueFree_five : graph13ᶜ.CliqueFree 5 := by
  intro t ht
  obtain ⟨a, b, c, d, e, ha, hb, hc, hd, he, hba, hca, hcb, hda, hdb, hdc,
    hea, heb, hec, hed⟩ := exists_five_distinct ht.2
  have key : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → adj13 x y = false := by
    intro x hx y hy hxy
    have := ht.1 hx hy hxy
    simpa [graph13, Bool.not_eq_true] using this.2
  exact no_indep5_aux a b ⟨fun h => hba h.symm, key a ha b hb (fun h => hba h.symm)⟩
    c ⟨hca, hcb, key a ha c hc (fun h => hca h.symm), key b hb c hc (fun h => hcb h.symm)⟩
    d ⟨hda, hdb, hdc, key a ha d hd (fun h => hda h.symm), key b hb d hd (fun h => hdb h.symm),
      key c hc d hd (fun h => hdc h.symm)⟩
    e ⟨hea, heb, hec, hed, key a ha e he (fun h => hea h.symm), key b hb e he (fun h => heb h.symm),
      key c hc e he (fun h => hec h.symm), key d hd e he (fun h => hed h.symm)⟩

end Construction

/-- Every graph on at least `14` vertices contains a triangle or an independent set of size `5`. -/
theorem exists_triangle_or_indep_five {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : 14 ≤ Fintype.card V) (G : SimpleGraph V) :
    (∃ s : Finset V, G.IsNClique 3 s) ∨ (∃ t : Finset V, Gᶜ.IsNClique 5 t) := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hb := bound_five (G := G) (s := Finset.univ)
    (fun t _ ht => h1 t ht) (fun t _ ht => h2 t ht)
  rw [Finset.card_univ] at hb
  omega

/-- The graph on `Fin n`, `n ≤ 13`, obtained by restricting `graph13`. -/
private def smallGraph {n : ℕ} (hn : n ≤ 13) : SimpleGraph (Fin n) :=
  SimpleGraph.comap (Fin.castLEEmb hn) graph13

private theorem smallGraph_no_triangle {n : ℕ} (hn : n ≤ 13) :
    (smallGraph hn).CliqueFree 3 :=
  SimpleGraph.CliqueFree.comap (SimpleGraph.Embedding.comap (Fin.castLEEmb hn) graph13)
    graph13_cliqueFree_three

private theorem smallGraph_no_indep {n : ℕ} (hn : n ≤ 13) :
    (smallGraph hn)ᶜ.CliqueFree 5 := by
  have hcompl : (smallGraph hn)ᶜ = SimpleGraph.comap (Fin.castLEEmb hn) graph13ᶜ := by
    ext a b
    simp [smallGraph]
  rw [hcompl]
  exact SimpleGraph.CliqueFree.comap (SimpleGraph.Embedding.comap (Fin.castLEEmb hn) graph13ᶜ)
    graph13_compl_cliqueFree_five

/-- **The Ramsey number `R(3,5)` equals `14`**: `14` is the least `n` such that every simple
graph on `n` vertices contains a triangle or an independent set of size `5`. -/
theorem ramsey_3_5 :
    IsLeast {n : ℕ | ∀ G : SimpleGraph (Fin n),
      (∃ s : Finset (Fin n), G.IsNClique 3 s) ∨ (∃ t : Finset (Fin n), Gᶜ.IsNClique 5 t)} 14 := by
  constructor
  · intro G
    exact exists_triangle_or_indep_five (by simp) G
  · intro n hn
    by_contra hlt
    push_neg at hlt
    have hn13 : n ≤ 13 := by omega
    rcases hn (smallGraph hn13) with ⟨s, hs⟩ | ⟨t, ht⟩
    · exact smallGraph_no_triangle hn13 s hs
    · exact smallGraph_no_indep hn13 t ht

end Math

