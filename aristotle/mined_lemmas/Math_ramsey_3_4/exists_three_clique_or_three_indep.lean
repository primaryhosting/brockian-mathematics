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

