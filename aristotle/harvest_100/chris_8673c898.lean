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
def RamseyProp (n k l : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), (∃ s, G.IsNClique k s) ∨ (∃ s, Gᶜ.IsNClique l s)

/-! ### The lower bound: a graph on 8 vertices with no triangle and no independent 4-set -/

/-- The circulant relation with connection set `{1, 4}` on `Fin 8`. -/
def wagnerRel : Fin 8 → Fin 8 → Prop :=
  fun i j => (i.val + 1) % 8 = j.val ∨ (i.val + 4) % 8 = j.val

instance : DecidableRel wagnerRel := fun i j =>
  inferInstanceAs (Decidable ((i.val + 1) % 8 = j.val ∨ (i.val + 4) % 8 = j.val))

/-- The Wagner graph (Möbius–Kantor graph `V₈`), i.e. the circulant graph `C₈(1,4)`.
It is triangle-free and has independence number `3`, hence it witnesses `R(3,4) > 8`. -/
def wagner : SimpleGraph (Fin 8) := SimpleGraph.fromRel wagnerRel

instance : DecidableRel wagner.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel wagnerRel).Adj)

theorem wagner_cliqueFree_three : wagner.CliqueFree 3 := by
  intro t; revert t; decide

theorem wagner_compl_cliqueFree_four : wagnerᶜ.CliqueFree 4 := by
  intro t; revert t; decide

/-! ### The upper bound -/

section Upper

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- Ramsey `R(3,3) ≤ 6`, in the form needed below: in a triangle-free graph, any set of at
least `6` vertices contains an independent set of size `3`. -/
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
theorem degree_le_three (h3 : G.CliqueFree 3) (h4 : Gᶜ.CliqueFree 4) (v : Fin 9) :
    (G.neighborFinset v).card ≤ 3 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨s, hs, hs4⟩ := Finset.exists_subset_card_eq (show 4 ≤ (G.neighborFinset v).card by omega)
  refine h4 s ⟨?_, hs4⟩
  intro a ha b hb hab
  have hva : G.Adj v a := by
    have := hs ha; rwa [SimpleGraph.mem_neighborFinset] at this
  have hvb : G.Adj v b := by
    have := hs hb; rwa [SimpleGraph.mem_neighborFinset] at this
  refine ⟨hab, fun hG => ?_⟩
  exact h3 {v, a, b} (SimpleGraph.is3Clique_triple_iff.2 ⟨hva, hvb, hG⟩)

/-- In a triangle-free graph on `9` vertices whose complement has no `4`-clique, every vertex
has degree at least `3`. -/
theorem three_le_degree (h3 : G.CliqueFree 3) (h4 : Gᶜ.CliqueFree 4) (v : Fin 9) :
    3 ≤ (G.neighborFinset v).card := by
  by_contra hcon
  push_neg at hcon
  set T : Finset (Fin 9) := (Finset.univ : Finset (Fin 9)) \ insert v (G.neighborFinset v) with hT
  have hvnb : v ∉ G.neighborFinset v := by simp
  have hcardins : (insert v (G.neighborFinset v)).card = (G.neighborFinset v).card + 1 := by
    rw [Finset.card_insert_of_notMem hvnb]
  have hcardT : 6 ≤ T.card := by
    have h1 : T.card = 9 - (insert v (G.neighborFinset v)).card := by
      rw [hT, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      simp
    omega
  obtain ⟨s, hsT, hs⟩ := exists_indep_three_of_six h3 T hcardT
  have hvs : ∀ b ∈ s, Gᶜ.Adj v b := by
    intro b hb
    have hbT := hsT hb
    rw [hT, Finset.mem_sdiff] at hbT
    have hb' : b ∉ insert v (G.neighborFinset v) := hbT.2
    simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or] at hb'
    exact ⟨fun h => hb'.1 h.symm, hb'.2⟩
  exact h4 (insert v s) (hs.insert hvs)

/-- The upper bound `R(3,4) ≤ 9`. -/
theorem ramsey_upper (G : SimpleGraph (Fin 9)) :
    (∃ s, G.IsNClique 3 s) ∨ (∃ s, Gᶜ.IsNClique 4 s) := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨hc3, hc4⟩ := hcon
  have h3 : G.CliqueFree 3 := fun t ht => hc3 t ht
  have h4 : Gᶜ.CliqueFree 4 := fun t ht => hc4 t ht
  have hdeg : ∀ v : Fin 9, G.degree v = 3 := by
    intro v
    have h1 := degree_le_three h3 h4 v
    have h2 := three_le_degree h3 h4 v
    rw [SimpleGraph.degree] at *
    omega
  have hsum : ∑ v : Fin 9, G.degree v = 2 * G.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges G
  rw [Finset.sum_congr rfl (fun v _ => hdeg v)] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega

end Nine

/-! ### Transferring the `8`-vertex example to fewer vertices -/

theorem not_ramseyProp_of_le_eight {n : ℕ} (hn : n ≤ 8) : ¬ RamseyProp n 3 4 := by
  classical
  intro h
  set f : Fin n ↪ Fin 8 := Fin.castLEEmb hn with hf
  set G : SimpleGraph (Fin n) := wagner.comap f with hG
  have hinj : Function.Injective f := f.injective
  have hcompl : Gᶜ = wagnerᶜ.comap f := by
    ext a b
    simp only [hG, SimpleGraph.compl_adj, SimpleGraph.comap_adj]
    constructor
    · rintro ⟨hab, hnadj⟩
      exact ⟨fun hc => hab (hinj hc), hnadj⟩
    · rintro ⟨hab, hnadj⟩
      exact ⟨fun hc => hab (congrArg f hc), hnadj⟩
  have h3 : G.CliqueFree 3 :=
    wagner_cliqueFree_three.comap (SimpleGraph.Embedding.comap f wagner)
  have h4 : Gᶜ.CliqueFree 4 := by
    rw [hcompl]
    exact wagner_compl_cliqueFree_four.comap (SimpleGraph.Embedding.comap f wagnerᶜ)
  rcases h G with ⟨s, hs⟩ | ⟨s, hs⟩
  · exact h3 s hs
  · exact h4 s hs

/-- **The Ramsey number `R(3,4)` equals `9`**: nine is the least number of vertices `n` such
that every graph on `n` vertices contains a triangle or an independent set of size `4`. -/
theorem ramsey_3_4 : IsLeast {n : ℕ | RamseyProp n 3 4} 9 := by
  constructor
  · exact ramsey_upper
  · intro n hn
    by_contra hlt
    exact not_ramseyProp_of_le_eight (by omega) hn

end Math


