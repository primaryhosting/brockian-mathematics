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
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

open Finset SimpleGraph

/-- The Ramsey property `R(3,4) ≤ n`: every simple graph on `n` vertices contains either a
triangle or an independent set of size `4`. -/

theorem ramseyProp34_nine : RamseyProp34 9 := by
  intro G
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨hT, hI⟩ := hcon
  have hCF : G.CliqueFree 3 := hT
  -- no triangles
  have htri : ∀ a b c : Fin 9, G.Adj a b → G.Adj a c → G.Adj b c → False := by
    intro a b c h1 h2 h3
    exact hT {a, b, c} (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1, h2, h3⟩)
  -- no independent sets of size four
  have hind : ∀ a b c d : Fin 9, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ¬ G.Adj a b → ¬ G.Adj a c → ¬ G.Adj a d → ¬ G.Adj b c → ¬ G.Adj b d → ¬ G.Adj c d →
      False := by
    intro a b c d hab hac had hbc hbd hcd nab nac nad nbc nbd ncd
    have h1 : Gᶜ.IsNClique 1 {d} := SimpleGraph.isNClique_singleton.mpr rfl
    have h2 : Gᶜ.IsNClique 2 (insert c {d}) := by
      refine h1.insert ?_
      intro x hx
      rw [Finset.mem_singleton] at hx
      subst hx
      exact ⟨hcd, ncd⟩
    have h3 : Gᶜ.IsNClique 3 (insert b (insert c {d})) := by
      refine h2.insert ?_
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ⟨hbc, nbc⟩
      · exact ⟨hbd, nbd⟩
    have h4 : Gᶜ.IsNClique 4 (insert a (insert b (insert c {d}))) := by
      refine h3.insert ?_
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨hab, nab⟩
      · exact ⟨hac, nac⟩
      · exact ⟨had, nad⟩
    exact hI _ ((G.isNClique_compl).mp h4)
  -- every degree is at most three
  have hdeg_le : ∀ v : Fin 9, G.degree v ≤ 3 := by
    intro v
    by_contra hgt
    push_neg at hgt
    have h4 : 4 ≤ (G.neighborFinset v).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      omega
    obtain ⟨S, hS, hS4⟩ := Finset.exists_subset_card_eq h4
    refine hI S ⟨?_, hS4⟩
    have hind0 := SimpleGraph.isIndepSet_neighborSet_of_triangleFree G hCF v
    refine hind0.mono ?_
    intro x hx
    have hx' : x ∈ G.neighborFinset v := hS hx
    simpa using hx'
  -- every degree is at least three
  have hdeg_ge : ∀ v : Fin 9, 3 ≤ G.degree v := by
    intro v
    by_contra hlt
    push_neg at hlt
    set M := (Finset.univ : Finset (Fin 9)) \ insert v (G.neighborFinset v) with hMdef
    have hins : (insert v (G.neighborFinset v)).card ≤ 3 := by
      have h1 := Finset.card_insert_le v (G.neighborFinset v)
      rw [SimpleGraph.card_neighborFinset_eq_degree] at h1
      omega
    have hMcard : 6 ≤ M.card := by
      have hsub : insert v (G.neighborFinset v) ⊆ Finset.univ := Finset.subset_univ _
      rw [hMdef, Finset.card_sdiff_of_subset hsub]
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hcase⟩ :=
      exists_three_clique_or_three_indep G M hMcard
    have hmem : ∀ x ∈ M, x ≠ v ∧ ¬ G.Adj v x := by
      intro x hx
      rw [hMdef, Finset.mem_sdiff] at hx
      have hx2 := hx.2
      simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or] at hx2
      exact hx2
    obtain ⟨hav, hva⟩ := hmem a ha
    obtain ⟨hbv, hvb⟩ := hmem b hb
    obtain ⟨hcv, hvc⟩ := hmem c hc
    rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact htri a b c h1 h2 h3
    · exact hind v a b c (Ne.symm hav) (Ne.symm hbv) (Ne.symm hcv) hab hac hbc
        hva hvb hvc h1 h2 h3
  -- so the graph is 3-regular on nine vertices, contradicting the handshake lemma
  have hdeg : ∀ v : Fin 9, G.degree v = 3 := fun v => le_antisymm (hdeg_le v) (hdeg_ge v)
  have hsum := SimpleGraph.sum_degrees_eq_twice_card_edges G
  rw [Finset.sum_congr rfl (fun v _ => hdeg v)] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega

/-! ### Lower bound: the Wagner graph witnesses `R(3,4) > 8` -/

/-- The Wagner graph (Möbius–Kantor graph `V₈`): the cycle `C₈` together with its four main
diagonals. It is triangle-free and has independence number `3`. -/
