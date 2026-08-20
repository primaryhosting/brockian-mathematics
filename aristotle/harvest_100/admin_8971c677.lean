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
def RamseyProp34 (n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n),
    (∃ s : Finset (Fin n), G.IsNClique 3 s) ∨ (∃ t : Finset (Fin n), G.IsNIndepSet 4 t)

/-! ### The Ramsey bound `R(3,3) ≤ 6` in the form we need -/

/-- Among any six vertices of a graph there are three that are pairwise adjacent or three that
are pairwise non-adjacent (i.e. `R(3,3) ≤ 6`). -/
theorem exists_three_clique_or_three_indep {α : Type*} [DecidableEq α] (G : SimpleGraph α)
    (W : Finset α) (hW : 6 ≤ W.card) :
    ∃ a ∈ W, ∃ b ∈ W, ∃ c ∈ W, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      ((G.Adj a b ∧ G.Adj a c ∧ G.Adj b c) ∨ (¬ G.Adj a b ∧ ¬ G.Adj a c ∧ ¬ G.Adj b c)) := by
  classical
  obtain ⟨v, hv⟩ : W.Nonempty := Finset.card_pos.mp (by omega)
  set W' := W.erase v with hW'def
  have hcard : 5 ≤ W'.card := by
    have h := Finset.card_erase_of_mem hv
    rw [hW'def, h]
    omega
  set A := W'.filter (fun u => G.Adj v u) with hAdef
  set B := W'.filter (fun u => ¬ G.Adj v u) with hBdef
  have hAB : A.card + B.card = W'.card :=
    Finset.card_filter_add_card_filter_not _
  have hsplit : 3 ≤ A.card ∨ 3 ≤ B.card := by omega
  rcases hsplit with hA3 | hB3
  · obtain ⟨S, hSA, hS3⟩ := Finset.exists_subset_card_eq hA3
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hS3
    have ha := hSA (by simp : a ∈ ({a, b, c} : Finset α))
    have hb := hSA (by simp : b ∈ ({a, b, c} : Finset α))
    have hc := hSA (by simp : c ∈ ({a, b, c} : Finset α))
    rw [hAdef, Finset.mem_filter, hW'def, Finset.mem_erase] at ha hb hc
    obtain ⟨⟨hav, haW⟩, hva⟩ := ha
    obtain ⟨⟨hbv, hbW⟩, hvb⟩ := hb
    obtain ⟨⟨hcv, hcW⟩, hvc⟩ := hc
    by_cases h1 : G.Adj a b
    · exact ⟨v, hv, a, haW, b, hbW, (Ne.symm hav), (Ne.symm hbv), hab, Or.inl ⟨hva, hvb, h1⟩⟩
    by_cases h2 : G.Adj a c
    · exact ⟨v, hv, a, haW, c, hcW, (Ne.symm hav), (Ne.symm hcv), hac, Or.inl ⟨hva, hvc, h2⟩⟩
    by_cases h3 : G.Adj b c
    · exact ⟨v, hv, b, hbW, c, hcW, (Ne.symm hbv), (Ne.symm hcv), hbc, Or.inl ⟨hvb, hvc, h3⟩⟩
    exact ⟨a, haW, b, hbW, c, hcW, hab, hac, hbc, Or.inr ⟨h1, h2, h3⟩⟩
  · obtain ⟨S, hSB, hS3⟩ := Finset.exists_subset_card_eq hB3
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hS3
    have ha := hSB (by simp : a ∈ ({a, b, c} : Finset α))
    have hb := hSB (by simp : b ∈ ({a, b, c} : Finset α))
    have hc := hSB (by simp : c ∈ ({a, b, c} : Finset α))
    rw [hBdef, Finset.mem_filter, hW'def, Finset.mem_erase] at ha hb hc
    obtain ⟨⟨hav, haW⟩, hva⟩ := ha
    obtain ⟨⟨hbv, hbW⟩, hvb⟩ := hb
    obtain ⟨⟨hcv, hcW⟩, hvc⟩ := hc
    by_cases h1 : G.Adj a b
    · by_cases h2 : G.Adj a c
      · by_cases h3 : G.Adj b c
        · exact ⟨a, haW, b, hbW, c, hcW, hab, hac, hbc, Or.inl ⟨h1, h2, h3⟩⟩
        · exact ⟨v, hv, b, hbW, c, hcW, (Ne.symm hbv), (Ne.symm hcv), hbc,
            Or.inr ⟨hvb, hvc, h3⟩⟩
      · exact ⟨v, hv, a, haW, c, hcW, (Ne.symm hav), (Ne.symm hcv), hac,
          Or.inr ⟨hva, hvc, h2⟩⟩
    · exact ⟨v, hv, a, haW, b, hbW, (Ne.symm hav), (Ne.symm hbv), hab,
        Or.inr ⟨hva, hvb, h1⟩⟩

/-! ### Upper bound: `R(3,4) ≤ 9` -/

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
def wagner : SimpleGraph (Fin 8) where
  Adj i j := ((i : ℕ) + 1) % 8 = (j : ℕ) ∨ ((j : ℕ) + 1) % 8 = (i : ℕ) ∨ ((i : ℕ) + 4) % 8 = (j : ℕ)
  symm := by
    intro i j h
    revert h
    revert i j
    decide
  loopless := by
    constructor
    intro i
    revert i
    decide

instance : DecidableRel wagner.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The Wagner graph contains no triangle. -/
theorem wagner_cliqueFree3 : wagner.CliqueFree 3 := by
  intro t
  revert t
  decide

/-- The Wagner graph contains no independent set of size four. -/
theorem wagner_compl_cliqueFree4 : wagnerᶜ.CliqueFree 4 := by
  intro t
  revert t
  decide

theorem compl_comap {V W : Type*} (f : V ↪ W) (G : SimpleGraph W) :
    (G.comap f)ᶜ = Gᶜ.comap f := by
  ext x y
  simp [f.injective.ne_iff]

theorem not_ramseyProp34_of_le_eight {n : ℕ} (hn : n ≤ 8) : ¬ RamseyProp34 n := by
  classical
  intro h
  set f : Fin n ↪ Fin 8 :=
    ⟨fun i => ⟨(i : ℕ), lt_of_lt_of_le i.isLt hn⟩, by
      intro a b hab
      simpa [Fin.ext_iff] using hab⟩ with hf
  have h1 : (wagner.comap f).CliqueFree 3 :=
    wagner_cliqueFree3.comap (SimpleGraph.Embedding.comap f wagner)
  have h2 : (wagner.comap f)ᶜ.CliqueFree 4 := by
    rw [compl_comap]
    exact wagner_compl_cliqueFree4.comap (SimpleGraph.Embedding.comap f wagnerᶜ)
  rcases h (wagner.comap f) with ⟨s, hs⟩ | ⟨t, ht⟩
  · exact h1 s hs
  · exact h2 t (by rwa [SimpleGraph.isNClique_compl])

/-! ### The Ramsey number `R(3,4) = 9` -/

/-- `R(3,4) = 9`: nine is the least `n` such that every graph on `n` vertices contains a
triangle or an independent set of size four. -/
theorem ramsey_3_4 : IsLeast {n : ℕ | RamseyProp34 n} 9 := by
  refine ⟨ramseyProp34_nine, ?_⟩
  intro m hm
  by_contra hlt
  exact not_ramseyProp34_of_le_eight (by omega : m ≤ 8) hm

end Math

#print axioms Math.ramsey_3_4

