/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open Finset SimpleGraph

/-! ### Generic clique helpers -/

section Helpers
variable {V : Type*} {G : SimpleGraph V}

/-- A set with no internal `G`-edges is a clique of the complement. -/
lemma isNClique_compl_of [DecidableEq V] {t : Finset V} {n : ℕ} (htn : t.card = n)
    (h : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → ¬ G.Adj a b) : Gᶜ.IsNClique n t := by
  refine ⟨?_, htn⟩
  intro a ha b hb hab
  exact ⟨hab, h a (by simpa using ha) b (by simpa using hb) hab⟩

lemma cliqueFree_three_of [DecidableEq V]
    (h : ∀ a b c : V, G.Adj a b → G.Adj a c → G.Adj b c → False) : G.CliqueFree 3 := by
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := is3Clique_iff.mp ht
  exact h a b c hab hac hbc

lemma cliqueFree_four_of [DecidableEq V]
    (h : ∀ a b c d : V, G.Adj a b → G.Adj a c → G.Adj a d → G.Adj b c → G.Adj b d →
      G.Adj c d → False) : G.CliqueFree 4 := by
  intro t ht
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_four.mp ht.card_eq
  have hcl := ht.isClique
  exact h a b c d (hcl (by simp) (by simp) hab) (hcl (by simp) (by simp) hac)
    (hcl (by simp) (by simp) had) (hcl (by simp) (by simp) hbc) (hcl (by simp) (by simp) hbd)
    (hcl (by simp) (by simp) hcd)

/-- If `G` has no triangle, any set of common neighbours of a vertex is a clique of `Gᶜ`. -/
lemma compl_isNClique_of_neighbors [DecidableEq V] {v : V} {t : Finset V} {n : ℕ}
    (htn : t.card = n) (hadj : ∀ w ∈ t, G.Adj v w) (h3 : G.CliqueFree 3) :
    Gᶜ.IsNClique n t := by
  refine isNClique_compl_of htn ?_
  intro a ha b hb hab hadjab
  exact h3 {v, a, b} (is3Clique_triple_iff.mpr ⟨hadj a ha, hadj b hb, hadjab⟩)

lemma induce_compl (G : SimpleGraph V) (s : Set V) : (Gᶜ).induce s = (G.induce s)ᶜ := by
  ext a b
  simp [SimpleGraph.compl_adj, Subtype.ext_iff]

/-- A clique of an induced subgraph gives a clique of the ambient graph inside the set. -/
lemma exists_isNClique_of_induce {s : Set V} {n : ℕ} {t : Finset s}
    (ht : (G.induce s).IsNClique n t) :
    ∃ u : Finset V, (∀ x ∈ u, x ∈ s) ∧ G.IsNClique n u := by
  refine ⟨t.map (Function.Embedding.subtype _), ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  · exact (ht.map (f := Function.Embedding.subtype _)).mono (SimpleGraph.map_comap_le _ _)

end Helpers

/-! ### The upper bound `R(4,4) ≤ 18` -/

section UpperBound
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Neighbours of `v`. -/
private def nbrs (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  {w ∈ Finset.univ.erase v | G.Adj v w}

/-- Non-neighbours of `v` (other than `v`). -/
private def nonnbrs (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  {w ∈ Finset.univ.erase v | ¬ G.Adj v w}

private lemma card_nbrs_add_card_nonnbrs (v : V) :
    (nbrs G v).card + (nonnbrs G v).card + 1 = Fintype.card V := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ.erase v)
    (p := fun w => G.Adj v w)
  have h2 : (Finset.univ.erase v).card = Fintype.card V - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
  have h3 : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  simp only [nbrs, nonnbrs]
  omega

private lemma adj_of_mem_nbrs {v w : V} (h : w ∈ nbrs G v) : G.Adj v w := by
  simp only [nbrs, Finset.mem_filter] at h
  exact h.2

private lemma compl_adj_of_mem_nonnbrs {v w : V} (h : w ∈ nonnbrs G v) : Gᶜ.Adj v w := by
  simp only [nonnbrs, Finset.mem_filter, Finset.mem_erase] at h
  exact ⟨fun hvw => h.1.1 hvw.symm, h.2⟩

private lemma nonnbrs_eq_nbrs_compl (v : V) : nonnbrs G v = nbrs Gᶜ v := by
  ext w
  simp [nonnbrs, nbrs, SimpleGraph.compl_adj, and_comm, eq_comm, Ne]

private lemma nbrs_eq_neighborFinset (v : V) : nbrs G v = G.neighborFinset v := by
  ext w
  simp only [nbrs, Finset.mem_filter, Finset.mem_erase, SimpleGraph.mem_neighborFinset]
  exact ⟨fun h => h.2, fun h => ⟨⟨(G.ne_of_adj h).symm, Finset.mem_univ _⟩, h⟩⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Transfer a clique of the complement of an induced subgraph up to the ambient graph. -/
private lemma lift_compl_clique {s : Set V} {n : ℕ} {t : Finset s}
    (ht : ((G.induce s)ᶜ).IsNClique n t) :
    ∃ u : Finset V, (∀ x ∈ u, x ∈ s) ∧ Gᶜ.IsNClique n u := by
  rw [← induce_compl] at ht
  exact exists_isNClique_of_induce ht

/-- `R(3,3) ≤ 6`. -/
lemma ramsey_3_3 (hc : 6 ≤ Fintype.card V) (h3 : G.CliqueFree 3) :
    ∃ t : Finset V, Gᶜ.IsNClique 3 t := by
  obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hsum := card_nbrs_add_card_nonnbrs (G := G) v
  by_cases hN : 3 ≤ (nbrs G v).card
  · obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hN
    exact ⟨t, compl_isNClique_of_neighbors htc (fun w hw => adj_of_mem_nbrs (hts hw)) h3⟩
  · have hM : 3 ≤ (nonnbrs G v).card := by omega
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hM
    by_cases hE : ∃ a ∈ t, ∃ b ∈ t, a ≠ b ∧ ¬ G.Adj a b
    · obtain ⟨a, ha, b, hb, hab, hnadj⟩ := hE
      exact ⟨{v, a, b}, is3Clique_triple_iff.mpr ⟨compl_adj_of_mem_nonnbrs (hts ha),
        compl_adj_of_mem_nonnbrs (hts hb), hab, hnadj⟩⟩
    · push_neg at hE
      exact absurd ⟨fun a ha b hb hab => hE a (by simpa using ha) b (by simpa using hb) hab, htc⟩
        (h3 t)

/-- `R(3,4) ≤ 9`, on a vertex set of exactly 9 vertices. -/
lemma ramsey_3_4_eq (hc : Fintype.card V = 9) (h3 : G.CliqueFree 3) :
    ∃ t : Finset V, Gᶜ.IsNClique 4 t := by
  classical
  by_contra hcon
  push_neg at hcon
  have h4 : Gᶜ.CliqueFree 4 := hcon
  have hdeg : ∀ v : V, (nbrs G v).card = 3 := by
    intro v
    have hsum := card_nbrs_add_card_nonnbrs (G := G) v
    have hup : (nbrs G v).card ≤ 3 := by
      by_contra hgt
      push_neg at hgt
      obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (n := 4) (s := nbrs G v) (by omega)
      exact h4 t (compl_isNClique_of_neighbors htc (fun w hw => adj_of_mem_nbrs (hts hw)) h3)
    have hlow : 3 ≤ (nbrs G v).card := by
      by_contra hlt
      push_neg at hlt
      have hM : 6 ≤ (nonnbrs G v).card := by omega
      set M : Set V := ((nonnbrs G v : Finset V) : Set V) with hMdef
      have hcardM : 6 ≤ Fintype.card M := by simpa [hMdef] using hM
      obtain ⟨t, ht⟩ := ramsey_3_3 (G := G.induce M) hcardM
        (h3.comap (SimpleGraph.Embedding.induce M))
      obtain ⟨u, hu, hucl⟩ := lift_compl_clique ht
      refine h4 (insert v u) (hucl.insert ?_)
      intro b hb
      exact compl_adj_of_mem_nonnbrs (by simpa [hMdef] using hu b hb)
    omega
  have hdegree : ∀ v : V, G.degree v = 3 := by
    intro v
    rw [← hdeg v, nbrs_eq_neighborFinset]
    rfl
  have hsum := G.sum_degrees_eq_twice_card_edges
  rw [Finset.sum_congr rfl (fun v _ => hdegree v)] at hsum
  simp only [Finset.sum_const, Finset.card_univ, hc, smul_eq_mul] at hsum
  omega

/-- `R(3,4) ≤ 9`. -/
lemma ramsey_3_4 (hc : 9 ≤ Fintype.card V) (h3 : G.CliqueFree 3) :
    ∃ t : Finset V, Gᶜ.IsNClique 4 t := by
  classical
  obtain ⟨s, -, hs9⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset V)) (n := 9)
    (by simpa using hc)
  set M : Set V := (s : Set V) with hMdef
  have hcardM : Fintype.card M = 9 := by simpa [hMdef] using hs9
  obtain ⟨t, ht⟩ := ramsey_3_4_eq (G := G.induce M) hcardM
    (h3.comap (SimpleGraph.Embedding.induce M))
  obtain ⟨u, -, hucl⟩ := lift_compl_clique ht
  exact ⟨u, hucl⟩

/-- `R(4,3) ≤ 9`. -/
lemma ramsey_4_3 (hc : 9 ≤ Fintype.card V) (h4 : G.CliqueFree 4) :
    ∃ t : Finset V, Gᶜ.IsNClique 3 t := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨t, ht⟩ := ramsey_3_4 (G := Gᶜ) hc hcon
  rw [compl_compl] at ht
  exact h4 t ht

/-- `R(4,4) ≤ 18`. -/
lemma ramsey_4_4_le (hc : 18 ≤ Fintype.card V) (h4 : G.CliqueFree 4) :
    ∃ t : Finset V, Gᶜ.IsNClique 4 t := by
  classical
  obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hsum := card_nbrs_add_card_nonnbrs (G := G) v
  by_cases hN : 9 ≤ (nbrs G v).card
  · set N : Set V := ((nbrs G v : Finset V) : Set V) with hNdef
    have hcardN : 9 ≤ Fintype.card N := by simpa [hNdef] using hN
    by_cases hCF : (G.induce N).CliqueFree 3
    · obtain ⟨t, ht⟩ := ramsey_3_4 (G := G.induce N) hcardN hCF
      obtain ⟨u, -, hucl⟩ := lift_compl_clique ht
      exact ⟨u, hucl⟩
    · rw [SimpleGraph.CliqueFree] at hCF
      push_neg at hCF
      obtain ⟨t, ht⟩ := hCF
      obtain ⟨u, hu, hucl⟩ := exists_isNClique_of_induce ht
      exact absurd (hucl.insert (fun b hb => adj_of_mem_nbrs (by simpa [hNdef] using hu b hb)))
        (h4 _)
  · have hM : 9 ≤ (nonnbrs G v).card := by omega
    set M : Set V := ((nonnbrs G v : Finset V) : Set V) with hMdef
    have hcardM : 9 ≤ Fintype.card M := by simpa [hMdef] using hM
    obtain ⟨t, ht⟩ := ramsey_4_3 (G := G.induce M) hcardM
      (h4.comap (SimpleGraph.Embedding.induce M))
    obtain ⟨u, hu, hucl⟩ := lift_compl_clique ht
    exact ⟨insert v u, hucl.insert
      (fun b hb => compl_adj_of_mem_nonnbrs (by simpa [hMdef] using hu b hb))⟩

end UpperBound

/-! ### The lower bound: the Paley graph on 17 vertices -/

/-- Membership test for the nonzero quadratic residues mod 17. -/
def isQR17 (k : ℕ) : Bool :=
  k = 1 || k = 2 || k = 4 || k = 8 || k = 9 || k = 13 || k = 15 || k = 16

/-- Adjacency of the Paley graph on 17 vertices. -/
def paleyAdj (a b : Fin 17) : Bool := isQR17 ((a.val + 17 - b.val) % 17)

/-- The Paley graph on 17 vertices. -/
def paley17 : SimpleGraph (Fin 17) where
  Adj a b := paleyAdj a b
  symm := by intro a b h; revert a b; decide
  loopless := by constructor; intro a h; revert a; decide

instance : DecidableRel paley17.Adj := fun a b => by
  unfold paley17; exact inferInstanceAs (Decidable (paleyAdj a b = true))

/-- Non-adjacency in the Paley graph. -/
def paleyNonAdj (a b : Fin 17) : Bool := (a != b) && !paleyAdj a b

lemma paley_no_four : ∀ a b c d : Fin 17,
    ¬(paleyAdj a b ∧ paleyAdj a c ∧ paleyAdj a d ∧ paleyAdj b c ∧ paleyAdj b d ∧ paleyAdj c d) := by
  decide +kernel

lemma paley_no_four_non : ∀ a b c d : Fin 17,
    ¬(paleyNonAdj a b ∧ paleyNonAdj a c ∧ paleyNonAdj a d ∧ paleyNonAdj b c ∧ paleyNonAdj b d ∧
      paleyNonAdj c d) := by
  decide +kernel

lemma paley17_cliqueFree : paley17.CliqueFree 4 :=
  cliqueFree_four_of fun a b c d h1 h2 h3 h4 h5 h6 =>
    paley_no_four a b c d ⟨h1, h2, h3, h4, h5, h6⟩

lemma paleyNonAdj_of_compl_adj {a b : Fin 17} (h : paley17ᶜ.Adj a b) : paleyNonAdj a b := by
  obtain ⟨hne, hadj⟩ := h
  simp only [paleyNonAdj, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true']
  refine ⟨hne, ?_⟩
  simpa [paley17] using hadj

lemma paley17_compl_cliqueFree : paley17ᶜ.CliqueFree 4 :=
  cliqueFree_four_of fun a b c d h1 h2 h3 h4 h5 h6 =>
    paley_no_four_non a b c d ⟨paleyNonAdj_of_compl_adj h1, paleyNonAdj_of_compl_adj h2,
      paleyNonAdj_of_compl_adj h3, paleyNonAdj_of_compl_adj h4, paleyNonAdj_of_compl_adj h5,
      paleyNonAdj_of_compl_adj h6⟩

/-- The witness graph on `Fin n` for `n ≤ 17`. -/
def paleyOn (n : ℕ) (hn : n ≤ 17) : SimpleGraph (Fin n) :=
  paley17.comap (Fin.castLEEmb hn)

lemma comap_compl {V W : Type*} (f : V ↪ W) (G : SimpleGraph W) :
    (G.comap f)ᶜ = (Gᶜ).comap f := by
  ext a b
  simp [SimpleGraph.comap, SimpleGraph.compl_adj, f.injective.eq_iff]

lemma paleyOn_cliqueFree (n : ℕ) (hn : n ≤ 17) : (paleyOn n hn).CliqueFree 4 :=
  paley17_cliqueFree.comap (SimpleGraph.Embedding.comap (Fin.castLEEmb hn) paley17)

lemma paleyOn_compl_cliqueFree (n : ℕ) (hn : n ≤ 17) : (paleyOn n hn)ᶜ.CliqueFree 4 := by
  rw [paleyOn, comap_compl]
  exact paley17_compl_cliqueFree.comap (SimpleGraph.Embedding.comap (Fin.castLEEmb hn) paley17ᶜ)

/-! ### The Ramsey number `R(4,4) = 18` -/

/-- **R(4,4) = 18**: `18` is the least `n` such that every graph on `n` vertices contains
either a clique of size 4 or an independent set of size 4. -/
theorem ramsey_4_4 :
    IsLeast {n : ℕ | ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree 4 ∨ ¬ Gᶜ.CliqueFree 4} 18 := by
  constructor
  · intro G
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    classical
    obtain ⟨t, ht⟩ := ramsey_4_4_le (G := G) (by simp) h1
    exact h2 t ht
  · intro n hn
    by_contra hlt
    push_neg at hlt
    have hn17 : n ≤ 17 := by omega
    rcases hn (paleyOn n hn17) with h | h
    · exact h (paleyOn_cliqueFree n hn17)
    · exact h (paleyOn_compl_cliqueFree n hn17)

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

