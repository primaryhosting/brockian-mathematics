/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Math

open Finset SimpleGraph

/-- Extract four elements in increasing order from a four-element finset. -/

def RamF (G : SimpleGraph V) (T : Finset V) (p q : ℕ) : Prop :=
  (∃ s ⊆ T, G.IsNClique p s) ∨ (∃ s ⊆ T, Gᶜ.IsNClique q s)

omit [LinearOrder V] in

theorem RamF.mono {G : SimpleGraph V} {T T' : Finset V} {p q : ℕ} (h : T ⊆ T')
    (hR : RamF G T p q) : RamF G T' p q := by
  rcases hR with ⟨s, hs, hc⟩ | ⟨s, hs, hc⟩
  · exact Or.inl ⟨s, hs.trans h, hc⟩
  · exact Or.inr ⟨s, hs.trans h, hc⟩

omit [LinearOrder V] in

theorem RamF.of_compl {G : SimpleGraph V} {T : Finset V} {p q : ℕ}
    (h : RamF Gᶜ T p q) : RamF G T q p := by
  rcases h with ⟨s, hs, hc⟩ | ⟨s, hs, hc⟩
  · exact Or.inr ⟨s, hs, hc⟩
  · rw [compl_compl] at hc; exact Or.inl ⟨s, hs, hc⟩

omit [LinearOrder V] in

theorem exists_nclique_of_clique {G : SimpleGraph V} {S : Finset V} (hS : G.IsClique S) {n : ℕ}
    (hn : n ≤ S.card) : ∃ s ⊆ S, G.IsNClique n s := by
  obtain ⟨t, ht, hcard⟩ := Finset.exists_subset_card_eq hn
  exact ⟨t, ht, ⟨hS.subset (by exact_mod_cast ht), hcard⟩⟩

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The neighbours of `v` inside `T`. -/

def nbhd (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (v : V) : Finset V :=
  (T.erase v).filter (fun w => G.Adj v w)

/-- The non-neighbours of `v` inside `T` (excluding `v`). -/

def nonNbhd (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (v : V) : Finset V :=
  (T.erase v).filter (fun w => ¬ G.Adj v w)

theorem nbhd_subset {T : Finset V} {v : V} : nbhd G T v ⊆ T :=
  (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)

theorem nonNbhd_subset {T : Finset V} {v : V} : nonNbhd G T v ⊆ T :=
  (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)

theorem adj_of_mem_nbhd {T : Finset V} {v w : V} (h : w ∈ nbhd G T v) : G.Adj v w :=
  (Finset.mem_filter.1 h).2

theorem card_nbhd_add_card_nonNbhd {T : Finset V} {v : V} (hv : v ∈ T) :
    (nbhd G T v).card + (nonNbhd G T v).card = T.card - 1 := by
  rw [nbhd, nonNbhd, Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hv]

theorem nonNbhd_eq_compl_nbhd {T : Finset V} {v : V} :
    nonNbhd G T v = nbhd Gᶜ T v := by
  ext w
  simp only [nonNbhd, nbhd, Finset.mem_filter, Finset.mem_erase, SimpleGraph.compl_adj]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h1.1 h.symm, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2.2⟩

/-- Extending a clique contained in the neighbourhood of `v` by the vertex `v` itself. -/

theorem nclique_insert_nbhd {T : Finset V} {v : V} (hv : v ∈ T) {s : Finset V} {k : ℕ}
    (hs : s ⊆ nbhd G T v) (hcl : G.IsNClique k s) : ∃ t ⊆ T, G.IsNClique (k + 1) t :=
  ⟨insert v s, Finset.insert_subset hv (hs.trans nbhd_subset),
    hcl.insert (fun _ hb => adj_of_mem_nbhd (hs hb))⟩

theorem nbhd_eq_filter (T : Finset V) (v : V) : nbhd G T v = T.filter (fun w => G.Adj v w) := by
  ext w
  simp only [nbhd, Finset.mem_filter, Finset.mem_erase]
  constructor
  · tauto
  · rintro ⟨hw, hadj⟩
    exact ⟨⟨fun h => G.irrefl (h ▸ hadj), hw⟩, hadj⟩

theorem sum_nbhd_eq (T : Finset V) :
    ∑ v ∈ T, (nbhd G T v).card = ((T ×ˢ T).filter (fun p => G.Adj p.1 p.2)).card := by
  rw [Finset.card_filter, Finset.sum_product]
  simp only [nbhd_eq_filter, Finset.card_filter]

/-- Handshake parity: the number of ordered adjacent pairs inside `T` is even. -/

theorem even_sum_nbhd_card (T : Finset V) :
    Even (∑ v ∈ T, (nbhd G T v).card) := by
  rw [sum_nbhd_eq]
  set P := (T ×ˢ T).filter (fun p => G.Adj p.1 p.2) with hP
  have hbij : (P.filter fun p => p.1 < p.2).card = (P.filter fun p => ¬ p.1 < p.2).card := by
    apply Finset.card_bij (fun p _ => (p.2, p.1))
    · intro p hp
      simp only [hP, Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨⟨hp.1.1.2, hp.1.1.1⟩, hp.1.2.symm⟩, asymm hp.2⟩
    · intro p hp q hq h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.2 h.1
    · intro q hq
      refine ⟨(q.2, q.1), ?_, rfl⟩
      simp only [hP, Finset.mem_filter, Finset.mem_product] at hq ⊢
      refine ⟨⟨⟨hq.1.1.2, hq.1.1.1⟩, hq.1.2.symm⟩, ?_⟩
      exact lt_of_le_of_ne (not_lt.1 hq.2) hq.1.2.ne'
  have h2 := Finset.card_filter_add_card_filter_not (s := P) (fun p => p.1 < p.2)
  exact ⟨(P.filter fun p => p.1 < p.2).card, by omega⟩

/-- If some vertex `v ∈ T` has at least `q` neighbours in `T`, then inside `T` there is
either a triangle of `G` or a `q`-clique of the complement. -/

theorem ram_of_nbhd (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (v : V) (hv : v ∈ T)
    {q : ℕ} (hq : q ≤ (nbhd G T v).card) : RamF G T 3 q := by
  by_cases hex : ∃ a ∈ nbhd G T v, ∃ b ∈ nbhd G T v, a ≠ b ∧ G.Adj a b
  · obtain ⟨a, ha, b, hb, hab, hadj⟩ := hex
    refine Or.inl ⟨{v, a, b}, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hv
      · exact nbhd_subset ha
      · exact nbhd_subset hb
    · rw [SimpleGraph.is3Clique_triple_iff]
      exact ⟨adj_of_mem_nbhd ha, adj_of_mem_nbhd hb, hadj⟩
  · push_neg at hex
    have hcl : Gᶜ.IsClique (nbhd G T v : Finset V) := by
      intro a ha b hb hab
      exact ⟨hab, hex a (Finset.mem_coe.1 ha) b (Finset.mem_coe.1 hb) hab⟩
    obtain ⟨s, hs, hns⟩ := exists_nclique_of_clique hcl hq
    exact Or.inr ⟨s, hs.trans nbhd_subset, hns⟩

/-- Ramsey `R(3,3) ≤ 6`. -/

theorem ram33 (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (hT : 6 ≤ T.card) :
    RamF G T 3 3 := by
  obtain ⟨v, hv⟩ : ∃ v, v ∈ T := Finset.card_pos.1 (by omega)
  have hsum := card_nbhd_add_card_nonNbhd (G := G) hv
  by_cases h : 3 ≤ (nbhd G T v).card
  · exact ram_of_nbhd G T v hv h
  · refine RamF.of_compl (ram_of_nbhd Gᶜ T v hv ?_)
    rw [← nonNbhd_eq_compl_nbhd]
    omega

/-- Ramsey `R(3,4) ≤ 9`. -/

theorem ram34 (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (hT : 9 ≤ T.card) :
    RamF G T 3 4 := by
  obtain ⟨T', hT', hcard⟩ := Finset.exists_subset_card_eq hT
  refine RamF.mono hT' ?_
  clear hT' hT
  by_contra hcon
  -- in a counterexample every vertex would have exactly three neighbours
  have key : ∀ v ∈ T', (nbhd G T' v).card = 3 := by
    intro v hv
    have hsum := card_nbhd_add_card_nonNbhd (G := G) hv
    rw [hcard] at hsum
    have hup : ¬ (4 ≤ (nbhd G T' v).card) := fun h4 => hcon (ram_of_nbhd G T' v hv h4)
    have hlow : ¬ ((nbhd G T' v).card ≤ 2) := by
      intro h2
      have h6 : 6 ≤ (nonNbhd G T' v).card := by omega
      rcases ram33 G (nonNbhd G T' v) h6 with ⟨s, hs, hcl⟩ | ⟨s, hs, hcl⟩
      · exact hcon (Or.inl ⟨s, hs.trans nonNbhd_subset, hcl⟩)
      · refine hcon (Or.inr ?_)
        rw [nonNbhd_eq_compl_nbhd] at hs
        exact nclique_insert_nbhd hv hs hcl
    omega
  -- but then the sum of the degrees is 27, contradicting handshake parity
  have hsum : ∑ v ∈ T', (nbhd G T' v).card = 27 := by
    rw [Finset.sum_congr rfl key, Finset.sum_const, hcard, smul_eq_mul]
  have heven := even_sum_nbhd_card (G := G) T'
  rw [hsum] at heven
  exact (Nat.not_even_iff_odd.2 (by decide)) heven

/-- Ramsey `R(4,4) ≤ 18`. -/
