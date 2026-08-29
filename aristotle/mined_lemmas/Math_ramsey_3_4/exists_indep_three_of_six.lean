import Mathlib

/-!
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

open SimpleGraph Finset

/-- `RamseyProp n k l` says that every simple graph on `n` vertices contains either a clique
of size `k` or an independent set (a clique of its complement) of size `l`. -/

theorem exists_indep_three_of_six (h3 : G.CliqueFree 3) (T : Finset V) (hT : 6 ≤ T.card) :
    ∃ s ⊆ T, Gᶜ.IsNClique 3 s := by
  classical
  obtain ⟨u, hu⟩ : ∃ u, u ∈ T := Finset.card_pos.1 (by omega) |>.imp fun _ h => h
  set T' : Finset V := T.erase u with hT'
  have hcardT' : 5 ≤ T'.card := by
    rw [hT', Finset.card_erase_of_mem hu]
    omega
  set N : Finset V := T'.filter (fun x => G.Adj u x) with hN
  set M : Finset V := T'.filter (fun x => ¬ G.Adj u x) with hM
  have hsplit : N.card + M.card = T'.card :=
    Finset.card_filter_add_card_filter_not (s := T') (p := fun x => G.Adj u x)
  have hu' : ∀ x ∈ T', x ≠ u := fun x hx => Finset.ne_of_mem_erase hx
  have hsubT : ∀ x ∈ T', x ∈ T := fun x hx => Finset.mem_of_mem_erase hx
  by_cases hcase : 3 ≤ N.card
  · -- three common neighbours of `u`: they are pairwise non-adjacent
    obtain ⟨s, hsN, hs3⟩ := Finset.exists_subset_card_eq hcase
    have hsT' : ∀ x ∈ s, x ∈ T' := fun x hx => Finset.mem_of_mem_filter x (hsN hx)
    refine ⟨s, fun x hx => hsubT x (hsT' x hx), ?_⟩
    refine ⟨?_, hs3⟩
    intro a ha b hb hab
    have hadj_ua : G.Adj u a := (Finset.mem_filter.1 (hsN ha)).2
    have hadj_ub : G.Adj u b := (Finset.mem_filter.1 (hsN hb)).2
    refine ⟨hab, fun hG => ?_⟩
    exact h3 {u, a, b} (SimpleGraph.is3Clique_triple_iff.2 ⟨hadj_ua, hadj_ub, hG⟩)
  · -- otherwise `u` has three non-neighbours in `T`
    have hcase' : 3 ≤ M.card := by omega
    obtain ⟨s, hsM, hs3⟩ := Finset.exists_subset_card_eq hcase'
    have hsT' : ∀ x ∈ s, x ∈ T' := fun x hx => Finset.mem_of_mem_filter x (hsM hx)
    have hnadj : ∀ x ∈ s, ¬ G.Adj u x := fun x hx => (Finset.mem_filter.1 (hsM hx)).2
    by_cases hall : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → G.Adj a b
    · -- `s` would be a triangle
      exfalso
      exact h3 s ⟨fun a ha b hb hab => hall a ha b hb hab, hs3⟩
    · push_neg at hall
      obtain ⟨a, ha, b, hb, hab, hnab⟩ := hall
      refine ⟨{u, a, b}, ?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hu
        · exact hsubT _ (hsT' _ ha)
        · exact hsubT _ (hsT' _ hb)
      · refine SimpleGraph.is3Clique_triple_iff.2 ⟨⟨?_, hnadj a ha⟩, ⟨?_, hnadj b hb⟩, hab, hnab⟩
        · exact fun h => (hu' a (hsT' a ha)) h.symm
        · exact fun h => (hu' b (hsT' b hb)) h.symm

end Upper

section Nine

variable {G : SimpleGraph (Fin 9)} [DecidableRel G.Adj]

/-- In a triangle-free graph whose complement has no `4`-clique, every vertex has degree
at most `3`. -/
