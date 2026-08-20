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

lemma ramR_step {k l a b : ℕ} (ha : 0 < a) (h1 : RamR G k (l + 1) a) (h2 : RamR G (k + 1) l b) :
    RamR G (k + 1) (l + 1) (a + b) := by
  intro s hs
  have hsne : s.Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨v, hv⟩ := hsne
  have hcard := card_redN_add_card_blueN (G := G) hv
  by_cases hR : a ≤ (redN G s v).card
  · rcases h1 _ hR with ⟨t, hts, ht⟩ | ⟨t, hts, ht⟩
    · obtain ⟨h1', h2'⟩ := insert_isNClique_of_redN hv hts ht
      exact Or.inl ⟨insert v t, h1', h2'⟩
    · exact Or.inr ⟨t, hts.trans redN_subset, ht⟩
  · have hB : b ≤ (blueN G s v).card := by omega
    rcases h2 _ hB with ⟨t, hts, ht⟩ | ⟨t, hts, ht⟩
    · exact Or.inl ⟨t, hts.trans blueN_subset, ht⟩
    · obtain ⟨h1', h2'⟩ := insert_isNClique_of_blueN hv hts ht
      exact Or.inr ⟨insert v t, h1', h2'⟩

