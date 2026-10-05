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
