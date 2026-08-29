import Mathlib
/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

open Finset

/-! ## Upper bound: every 2-colouring of `K₁₈` has a monochromatic `K₄`

We phrase a 2-colouring of the edges of a complete graph as a simple graph `G`
(the "red" edges); the "blue" edges are the edges of the complement `Gᶜ`.
-/

section Core

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The neighbours of `v` inside the finite set `s`. -/
def nb (s : Finset V) (v : V) : Finset V := s.filter (fun u => G.Adj v u)

variable {G}

omit [Fintype V] [DecidableEq V] in
lemma mem_nb {s : Finset V} {v u : V} : u ∈ nb G s v ↔ u ∈ s ∧ G.Adj v u := by
  simp [nb]

omit [Fintype V] [DecidableEq V] in
lemma nb_subset (s : Finset V) (v : V) : nb G s v ⊆ s := Finset.filter_subset _ _

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma adj_of_not_compl_adj {x y : V} (hxy : x ≠ y) (h : ¬ Gᶜ.Adj x y) : G.Adj x y := by
  simp only [SimpleGraph.compl_adj, hxy, not_and, not_not, ne_eq, not_false_eq_true,
    forall_const] at h
  exact h

omit [Fintype V] in
lemma card_nb_add_card_nb_compl {s : Finset V} {v : V} (hv : v ∈ s) :
    (nb G s v).card + (nb Gᶜ s v).card + 1 = s.card := by
  have h1 : nb G s v = (s.erase v).filter (fun u => G.Adj v u) := by
    ext u
    simp only [mem_nb, Finset.mem_filter, Finset.mem_erase]
    exact ⟨fun h => ⟨⟨(G.ne_of_adj h.2).symm, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
  have h2 : nb Gᶜ s v = (s.erase v).filter (fun u => ¬ G.Adj v u) := by
    ext u
    simp only [mem_nb, Finset.mem_filter, Finset.mem_erase, SimpleGraph.compl_adj]
    constructor
    · rintro ⟨hus, hne, hadj⟩
      exact ⟨⟨hne.symm, hus⟩, hadj⟩
    · rintro ⟨⟨hne, hus⟩, hadj⟩
      exact ⟨hus, hne.symm, hadj⟩
  have h3 := Finset.card_filter_add_card_filter_not (s := s.erase v) (fun u => G.Adj v u)
  rw [h1, h2]
  rw [h3, Finset.card_erase_of_mem hv]
  have : 1 ≤ s.card := Finset.card_pos.mpr ⟨v, hv⟩
  omega

omit [Fintype V] in
/-- If `v` has at least three neighbours inside `s`, then `s` contains a monochromatic triangle. -/
lemma triangle_of_nb {s : Finset V} {v : V} (hv : v ∈ s) (h3 : 3 ≤ (nb G s v).card) :
    (∃ t ⊆ s, G.IsNClique 3 t) ∨ (∃ t ⊆ s, Gᶜ.IsNClique 3 t) := by
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq h3
  by_cases hcl : Gᶜ.IsClique (t : Set V)
  · exact Or.inr ⟨t, hts.trans (nb_subset s v), hcl, htc⟩
  · rw [SimpleGraph.isClique_iff, Set.Pairwise] at hcl
    push_neg at hcl
    obtain ⟨x, hx, y, hy, hxy, hadj⟩ := hcl
    simp only [Finset.mem_coe] at hx hy
    have hax : G.Adj v x := (mem_nb.mp (hts hx)).2
    have hay : G.Adj v y := (mem_nb.mp (hts hy)).2
    refine Or.inl ⟨{v, x, y}, ?_, ?_⟩
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact hv
      · exact (nb_subset s v) (hts hx)
      · exact (nb_subset s v) (hts hy)
    · exact SimpleGraph.is3Clique_triple_iff.mpr ⟨hax, hay, adj_of_not_compl_adj hxy hadj⟩

omit [Fintype V] in
/-- `R(3,3) ≤ 6`. -/
lemma exists_mono_three {s : Finset V} (hs : 6 ≤ s.card) :
    (∃ t ⊆ s, G.IsNClique 3 t) ∨ (∃ t ⊆ s, Gᶜ.IsNClique 3 t) := by
  obtain ⟨v, hv⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
  have hpart := card_nb_add_card_nb_compl (G := G) hv
  by_cases hR : 3 ≤ (nb G s v).card
  · exact triangle_of_nb hv hR
  · have hB : 3 ≤ (nb Gᶜ s v).card := by omega
    have := triangle_of_nb (G := Gᶜ) hv hB
    rw [compl_compl] at this
    exact this.symm

/-- `R(3,4) ≤ 9`: nine vertices contain a red triangle or a blue `K₄`. -/
lemma exists_r34 {s : Finset V} (hs : 9 ≤ s.card) :
    (∃ t ⊆ s, G.IsNClique 3 t) ∨ (∃ t ⊆ s, Gᶜ.IsNClique 4 t) := by
  obtain ⟨s', hs's, hs'⟩ := Finset.exists_subset_card_eq hs
  suffices h : (∃ t ⊆ s', G.IsNClique 3 t) ∨ (∃ t ⊆ s', Gᶜ.IsNClique 4 t) by
    rcases h with ⟨t, ht, h⟩ | ⟨t, ht, h⟩
    exacts [Or.inl ⟨t, ht.trans hs's, h⟩, Or.inr ⟨t, ht.trans hs's, h⟩]
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  -- every vertex has red degree at most three
  have redle : ∀ v ∈ s', (nb G s' v).card ≤ 3 := by
    intro v hv
    by_contra hlt
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (show 4 ≤ (nb G s' v).card by omega)
    refine h2 t (hts.trans (nb_subset s' v)) ⟨?_, htc⟩
    intro x hx y hy hxy
    simp only [Finset.mem_coe] at hx hy
    by_contra hadj
    have hxy' : G.Adj x y := adj_of_not_compl_adj hxy hadj
    refine h1 {v, x, y} ?_ (SimpleGraph.is3Clique_triple_iff.mpr
      ⟨(mem_nb.mp (hts hx)).2, (mem_nb.mp (hts hy)).2, hxy'⟩)
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact hv
    · exact (nb_subset s' v) (hts hx)
    · exact (nb_subset s' v) (hts hy)
  -- every vertex has blue degree at most five
  have bluele : ∀ v ∈ s', (nb Gᶜ s' v).card ≤ 5 := by
    intro v hv
    by_contra hlt
    have h6 : 6 ≤ (nb Gᶜ s' v).card := by omega
    rcases exists_mono_three (G := G) h6 with ⟨t, ht, h3⟩ | ⟨t, ht, h3⟩
    · exact h1 t (ht.trans (nb_subset s' v)) h3
    · refine h2 (insert v t) ?_ ?_
      · refine Finset.insert_subset hv (ht.trans (nb_subset s' v))
      · exact h3.insert (fun b hb => (mem_nb.mp (ht hb)).2)
  -- hence every vertex has red degree exactly three
  have hdeg3 : ∀ v ∈ s', (nb G s' v).card = 3 := by
    intro v hv
    have hpart := card_nb_add_card_nb_compl (G := G) hv
    have := redle v hv
    have := bluele v hv
    omega
  -- handshake: the red graph restricted to `s'` is 3-regular on nine vertices
  let H : SimpleGraph V :=
    { Adj := fun a b => a ∈ s' ∧ b ∈ s' ∧ G.Adj a b
      symm := by
        rintro a b ⟨ha, hb, hab⟩
        exact ⟨hb, ha, hab.symm⟩
      loopless := ⟨by
        rintro a ⟨-, -, hab⟩
        exact G.irrefl hab⟩ }
  haveI : DecidableRel H.Adj := fun a b => inferInstanceAs (Decidable (a ∈ s' ∧ b ∈ s' ∧ G.Adj a b))
  have hHdeg : ∀ v : V, H.degree v = if v ∈ s' then 3 else 0 := by
    intro v
    by_cases hv : v ∈ s'
    · rw [if_pos hv, ← hdeg3 v hv, ← SimpleGraph.card_neighborFinset_eq_degree]
      congr 1
      ext u
      simp only [SimpleGraph.mem_neighborFinset, mem_nb]
      exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hv, h.1, h.2⟩⟩
    · rw [if_neg hv, ← SimpleGraph.card_neighborFinset_eq_degree]
      simp only [Finset.card_eq_zero]
      ext u
      simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
      rintro ⟨h, -, -⟩
      exact hv h
  have hsum := H.sum_degrees_eq_twice_card_edges
  rw [Finset.sum_congr rfl (fun v _ => hHdeg v)] at hsum
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, hs', smul_eq_mul] at hsum
  omega

/-- Inductive step for the upper bound `R(4,4) ≤ 18`. -/
lemma four_clique_of_nb {s : Finset V} {v : V} (hv : v ∈ s) (h9 : 9 ≤ (nb G s v).card) :
    (∃ t ⊆ s, G.IsNClique 4 t) ∨ (∃ t ⊆ s, Gᶜ.IsNClique 4 t) := by
  rcases exists_r34 (G := G) h9 with ⟨t, ht, h3⟩ | ⟨t, ht, h4⟩
  · refine Or.inl ⟨insert v t, Finset.insert_subset hv (ht.trans (nb_subset s v)), ?_⟩
    exact h3.insert (fun b hb => (mem_nb.mp (ht hb)).2)
  · exact Or.inr ⟨t, ht.trans (nb_subset s v), h4⟩

/-- `R(4,4) ≤ 18`. -/
lemma exists_r44 {s : Finset V} (hs : 18 ≤ s.card) :
    (∃ t ⊆ s, G.IsNClique 4 t) ∨ (∃ t ⊆ s, Gᶜ.IsNClique 4 t) := by
  obtain ⟨v, hv⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
  have hpart := card_nb_add_card_nb_compl (G := G) hv
  by_cases hR : 9 ≤ (nb G s v).card
  · exact four_clique_of_nb hv hR
  · have hB : 9 ≤ (nb Gᶜ s v).card := by omega
    have := four_clique_of_nb (G := Gᶜ) hv hB
    rw [compl_compl] at this
    exact this.symm

end Core

/-! ## Lower bound: the Paley graph on 17 vertices

The Paley graph on `ZMod 17`: `i ~ j` iff `i - j` is a nonzero quadratic residue mod `17`,
i.e. lies in `{1,2,4,8,9,13,15,16}`.  Neither it nor its complement contains a `K₄`.
-/

/-- Membership test for the nonzero quadratic residues modulo `17`. -/
def paleyQ (x : ℕ) : Bool :=
  x == 1 || x == 2 || x == 4 || x == 8 || x == 9 || x == 13 || x == 15 || x == 16

/-- Adjacency in the Paley graph of order `17`, on natural number representatives. -/
def padj (a b : ℕ) : Bool := paleyQ ((a + 17 - b) % 17) || paleyQ ((b + 17 - a) % 17)

lemma padj_comm (a b : ℕ) : padj a b = padj b a := by
  unfold padj
  exact Bool.or_comm _ _

/-- The exhaustive check that no four distinct vertices of the Paley graph of order `17`
span a monochromatic `K₄`. -/
def paleyCheck : Bool :=
  (List.range 17).all fun a =>
    (List.range 17).all fun b => (a == b) ||
      ((List.range 17).all fun c => (a == c) || (b == c) ||
        ((List.range 17).all fun d => (a == d) || (b == d) || (c == d) ||
          !((padj a c == padj a b) && (padj a d == padj a b) && (padj b c == padj a b) &&
            (padj b d == padj a b) && (padj c d == padj a b))))

theorem paleyCheck_true : paleyCheck = true := by decide

theorem paley_no_mono_four (a b c d : ℕ) (ha : a < 17) (hb : b < 17) (hc : c < 17) (hd : d < 17)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (x : Bool) (h1 : padj a b = x) (h2 : padj a c = x) (h3 : padj a d = x)
    (h4 : padj b c = x) (h5 : padj b d = x) (h6 : padj c d = x) : False := by
  have H := paleyCheck_true
  simp only [paleyCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    Bool.not_eq_true'] at H
  rcases H a ha b hb with h | H
  · exact hab h
  rcases H c hc with (h | h) | H
  · exact hac h
  · exact hbc h
  rcases H d hd with ((h | h) | h) | H
  · exact had h
  · exact hbd h
  · exact hcd h
  · simp [h1, h2, h3, h4, h5, h6] at H

/-- The Paley graph of order `17`, restricted to the first `n` vertices. -/
def paleyGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ padj i.val j.val = true
  symm := by
    rintro i j ⟨h1, h2⟩
    exact ⟨h1.symm, by rw [padj_comm]; exact h2⟩
  loopless := ⟨by
    rintro i ⟨h1, -⟩
    exact h1 rfl⟩

lemma paley_no_clique_four {n : ℕ} (hn : n ≤ 17) (s : Finset (Fin n))
    (hs : (paleyGraph n).IsNClique 4 s ∨ (paleyGraph n)ᶜ.IsNClique 4 s) : False := by
  have hcard : s.card = 4 := by rcases hs with h | h; exacts [h.2, h.2]
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_four.mp hcard
  have hma : a ∈ ({a, b, c, d} : Finset (Fin n)) := by simp
  have hmb : b ∈ ({a, b, c, d} : Finset (Fin n)) := by simp
  have hmc : c ∈ ({a, b, c, d} : Finset (Fin n)) := by simp
  have hmd : d ∈ ({a, b, c, d} : Finset (Fin n)) := by simp
  have hlt : ∀ i : Fin n, (i : ℕ) < 17 := fun i => lt_of_lt_of_le i.isLt hn
  have hne : ∀ {i j : Fin n}, i ≠ j → (i : ℕ) ≠ (j : ℕ) := by
    intro i j h hv
    exact h (Fin.ext hv)
  rcases hs with ⟨hcl, -⟩ | ⟨hcl, -⟩
  · refine paley_no_mono_four a b c d (hlt a) (hlt b) (hlt c) (hlt d) (hne hab) (hne hac)
      (hne had) (hne hbc) (hne hbd) (hne hcd) true
      (hcl hma hmb hab).2 (hcl hma hmc hac).2 (hcl hma hmd had).2
      (hcl hmb hmc hbc).2 (hcl hmb hmd hbd).2 (hcl hmc hmd hcd).2
  · have key : ∀ {i j : Fin n}, i ≠ j → (paleyGraph n)ᶜ.Adj i j → padj i.val j.val = false := by
      intro i j hij h
      simp only [SimpleGraph.compl_adj, paleyGraph, hij, ne_eq, not_false_eq_true,
        Bool.not_eq_true, true_and] at h
      exact h
    exact paley_no_mono_four a b c d (hlt a) (hlt b) (hlt c) (hlt d) (hne hab) (hne hac)
      (hne had) (hne hbc) (hne hbd) (hne hcd) false
      (key hab (hcl hma hmb hab)) (key hac (hcl hma hmc hac)) (key had (hcl hma hmd had))
      (key hbc (hcl hmb hmc hbc)) (key hbd (hcl hmb hmd hbd)) (key hcd (hcl hmc hmd hcd))

/-! ## The Ramsey number `R(4,4) = 18` -/

/-- **The two-colour Ramsey number `R(4,4)` equals `18`.**
Reading a 2-colouring of the edges of the complete graph on `n` vertices as a simple graph `G`
(the edges of the first colour) together with its complement `Gᶜ` (the second colour),
`18` is the least `n` such that every 2-colouring of `Kₙ` contains a monochromatic `K₄`. -/
theorem ramsey_4_4 :
    IsLeast {n : ℕ | ∀ G : SimpleGraph (Fin n),
      ∃ s : Finset (Fin n), G.IsNClique 4 s ∨ Gᶜ.IsNClique 4 s} 18 := by
  constructor
  · intro G
    classical
    have hcard : (Finset.univ : Finset (Fin 18)).card = 18 := by simp
    rcases exists_r44 (G := G) (s := Finset.univ) (by omega) with ⟨t, -, h⟩ | ⟨t, -, h⟩
    exacts [⟨t, Or.inl h⟩, ⟨t, Or.inr h⟩]
  · intro n hn
    by_contra hlt
    push_neg at hlt
    obtain ⟨s, hs⟩ := hn (paleyGraph n)
    exact paley_no_clique_four (by omega) s hs

end Math

