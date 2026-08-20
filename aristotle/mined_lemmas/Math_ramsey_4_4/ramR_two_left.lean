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

lemma ramR_two_left (l : ℕ) : RamR G 2 l l := by
  intro s hs
  by_cases h : ∃ a ∈ s, ∃ b ∈ s, G.Adj a b
  · obtain ⟨a, ha, b, hb, hab⟩ := h
    refine Or.inl ⟨{a, b}, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.1 hx with h | h
      · exact h ▸ ha
      · exact (Finset.mem_singleton.1 h) ▸ hb
    · refine ⟨?_, Finset.card_pair hab.ne⟩
      simp only [Finset.coe_insert, Finset.coe_singleton,
        Set.pairwise_insert_of_symmetric G.symm, Set.pairwise_singleton, Set.mem_singleton_iff]
      exact ⟨trivial, fun b hb _ => hb ▸ hab⟩
  · push_neg at h
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hs
    refine Or.inr ⟨t, hts, ⟨?_, htc⟩⟩
    intro a ha b hb hab
    exact (SimpleGraph.compl_adj _ _ _).2 ⟨hab, h a (hts ha) b (hts hb)⟩

/-- `R(k, 2) ≤ k`. -/
