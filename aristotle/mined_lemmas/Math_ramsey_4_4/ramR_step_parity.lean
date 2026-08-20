import Mathlib

/-!
# Upper bound for the Ramsey number R(4,4)

This file develops, from scratch, the classical inductive bounds on two-colour Ramsey
numbers, culminating in `Math.ramsey_upper_4_4`: every graph on a vertex set of size at
least `18` contains a `4`-clique or an independent set of size `4`.
-/

namespace Math

open Finset

variable {V : Type*} [DecidableEq V]

open scoped Classical in
/-- The neighbours of `v` inside `s` (excluding `v` itself). -/

lemma ramR_step_parity {k l a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hae : Even a) (hbe : Even b)
    (h1 : RamR G k (l + 1) a) (h2 : RamR G (k + 1) l b) :
    RamR G (k + 1) (l + 1) (a + b - 1) := by
  intro s hs
  by_cases hex : ∃ v ∈ s, a ≤ (redN G s v).card ∨ b ≤ (blueN G s v).card
  · obtain ⟨v, hv, hcase⟩ := hex
    rcases hcase with hR | hB
    · rcases h1 _ hR with ⟨t, hts, ht⟩ | ⟨t, hts, ht⟩
      · obtain ⟨h1', h2'⟩ := insert_isNClique_of_redN hv hts ht
        exact Or.inl ⟨insert v t, h1', h2'⟩
      · exact Or.inr ⟨t, hts.trans redN_subset, ht⟩
    · rcases h2 _ hB with ⟨t, hts, ht⟩ | ⟨t, hts, ht⟩
      · exact Or.inl ⟨t, hts.trans blueN_subset, ht⟩
      · obtain ⟨h1', h2'⟩ := insert_isNClique_of_blueN hv hts ht
        exact Or.inr ⟨insert v t, h1', h2'⟩
  · exfalso
    push_neg at hex
    have hne : s.Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨v0, hv0⟩ := hne
    have hcard : s.card = a + b - 1 := by
      have h := card_redN_add_card_blueN (G := G) hv0
      have := hex v0 hv0
      omega
    have hall : ∀ v ∈ s, (redN G s v).card = a - 1 := by
      intro v hv
      have h := card_redN_add_card_blueN (G := G) hv
      have := hex v hv
      omega
    have hsum : ∑ v ∈ s, (redN G s v).card = s.card * (a - 1) := by
      rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_eq_mul]
    have heven := even_sum_card_redN G s
    rw [hsum, hcard] at heven
    have hodd1 : Odd (a + b - 1) := by
      rw [Nat.odd_iff]
      rw [Nat.even_iff] at hae hbe
      omega
    have hodd2 : Odd (a - 1) := by
      rw [Nat.odd_iff]
      rw [Nat.even_iff] at hae
      omega
    rw [Nat.even_iff] at heven
    rw [Nat.odd_iff] at hodd1 hodd2
    have hm := Nat.mul_mod (a + b - 1) (a - 1) 2
    rw [hodd1, hodd2] at hm
    omega

