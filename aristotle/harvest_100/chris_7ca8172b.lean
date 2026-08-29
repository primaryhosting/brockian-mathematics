/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Math

open SimpleGraph

/-- `RamseyProp n` says that every simple graph on `n` vertices contains either a triangle
(a clique of size `3`) or an independent set of size `4`. -/
def RamseyProp (n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n),
    (∃ s : Finset (Fin n), G.IsNClique 3 s) ∨ (∃ t : Finset (Fin n), G.IsNIndepSet 4 t)

/-! ### Transporting cliques and independent sets along an embedding -/

lemma isNClique_map_of_comap {V W : Type*} [DecidableEq V] [DecidableEq W] {G : SimpleGraph W}
    (f : V ↪ W) {k : ℕ} {s : Finset V} (h : (G.comap f).IsNClique k s) :
    G.IsNClique k (s.map f) := by
  constructor
  · intro a ha b hb hab
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    exact h.isClique hx hy (fun hxy => hab (by rw [hxy]))
  · rw [Finset.card_map]; exact h.card_eq

lemma isNIndepSet_map_of_comap {V W : Type*} [DecidableEq V] [DecidableEq W] {G : SimpleGraph W}
    (f : V ↪ W) {k : ℕ} {s : Finset V} (h : (G.comap f).IsNIndepSet k s) :
    G.IsNIndepSet k (s.map f) := by
  constructor
  · intro a ha b hb hab
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    exact h.isIndepSet hx hy (fun hxy => hab (by rw [hxy]))
  · rw [Finset.card_map]; exact h.card_eq

lemma RamseyProp.mono {m n : ℕ} (hmn : m ≤ n) (hm : RamseyProp m) : RamseyProp n := by
  intro G
  classical
  let f : Fin m ↪ Fin n := Fin.castLEEmb hmn
  rcases hm (G.comap f) with ⟨s, hs⟩ | ⟨t, ht⟩
  · exact Or.inl ⟨s.map f, isNClique_map_of_comap f hs⟩
  · exact Or.inr ⟨t.map f, isNIndepSet_map_of_comap f ht⟩

/-! ### The key intermediate lemma: `R(3,3) ≤ 6` -/

/-- In a triangle-free graph, any set of at least `6` vertices contains an independent set of
size `3`.  This is the bound `R(3,3) ≤ 6`. -/
lemma exists_isNIndepSet_three {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (h3 : ∀ s : Finset V, ¬ G.IsNClique 3 s) (s : Finset V) (hs : 6 ≤ s.card) :
    ∃ t ⊆ s, G.IsNIndepSet 3 t := by
  classical
  obtain ⟨v, hv⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
  have hs' : 5 ≤ (s.erase v).card := by
    rw [Finset.card_erase_of_mem hv]; omega
  have hAB : ((s.erase v).filter (fun w => G.Adj v w)).card
      + ((s.erase v).filter (fun w => ¬ G.Adj v w)).card = (s.erase v).card :=
    Finset.card_filter_add_card_filter_not _
  have hcase : 3 ≤ ((s.erase v).filter (fun w => G.Adj v w)).card ∨
      3 ≤ ((s.erase v).filter (fun w => ¬ G.Adj v w)).card := by omega
  rcases hcase with hA | hB
  · obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hA
    refine ⟨t, ?_, ?_, htc⟩
    · intro x hx
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_filter x (hts hx))
    · intro a ha b hb hab hadj
      have ha' := hts ha
      have hb' := hts hb
      rw [Finset.mem_filter] at ha' hb'
      exact h3 {v, a, b} (is3Clique_triple_iff.mpr ⟨ha'.2, hb'.2, hadj⟩)
  · obtain ⟨u, hus, huc⟩ := Finset.exists_subset_card_eq hB
    by_cases hcl : G.IsClique (u : Set V)
    · exact absurd ⟨hcl, huc⟩ (h3 u)
    · rw [SimpleGraph.isClique_iff, Set.Pairwise] at hcl
      push_neg at hcl
      obtain ⟨a, ha, b, hb, hne, hnadj⟩ := hcl
      have ha' := hus ha
      have hb' := hus hb
      rw [Finset.mem_filter] at ha' hb'
      have hva : v ≠ a := fun h => (Finset.ne_of_mem_erase ha'.1) h.symm
      have hvb : v ≠ b := fun h => (Finset.ne_of_mem_erase hb'.1) h.symm
      refine ⟨{v, a, b}, ?_, ?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hv
        · exact Finset.mem_of_mem_erase ha'.1
        · exact Finset.mem_of_mem_erase hb'.1
      · intro x hx y hy hxy
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
          Set.mem_singleton_iff] at hx hy
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
          first
            | exact absurd rfl hxy
            | exact ha'.2
            | exact hb'.2
            | exact hnadj
            | (intro hadj; exact ha'.2 hadj.symm)
            | (intro hadj; exact hb'.2 hadj.symm)
            | (intro hadj; exact hnadj hadj.symm)
      · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simpa using hne
        · simp only [Finset.mem_insert, Finset.mem_singleton]
          exact fun h => h.elim hva hvb

/-! ### The upper bound: every graph on 9 vertices has a triangle or a 4-independent set -/

theorem ramseyProp_nine : RamseyProp 9 := by
  intro G
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨h3, h4⟩ := hcon
  haveI : DecidableRel G.Adj := Classical.decRel _
  -- neighbourhoods are independent
  have hNindep : ∀ v : Fin 9, ∀ a ∈ G.neighborFinset v, ∀ b ∈ G.neighborFinset v,
      a ≠ b → ¬ G.Adj a b := by
    intro v a ha b hb hab hadj
    rw [mem_neighborFinset] at ha hb
    exact h3 {v, a, b} (is3Clique_triple_iff.mpr ⟨ha, hb, hadj⟩)
  -- hence every degree is at most 3
  have hdeg_le : ∀ v : Fin 9, G.degree v ≤ 3 := by
    intro v
    by_contra hlt
    push_neg at hlt
    have h4le : 4 ≤ (G.neighborFinset v).card := by
      rw [card_neighborFinset_eq_degree]; omega
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq h4le
    refine h4 t ⟨?_, htc⟩
    intro a ha b hb hab
    exact hNindep v a (hts ha) b (hts hb) hab
  -- and every degree is at least 3
  have hdeg_ge : ∀ v : Fin 9, 3 ≤ G.degree v := by
    intro v
    by_contra hlt
    push_neg at hlt
    set s : Finset (Fin 9) := Finset.univ \ insert v (G.neighborFinset v) with hsdef
    have hcard : 6 ≤ s.card := by
      have h1 : (insert v (G.neighborFinset v)).card ≤ 3 := by
        refine le_trans (Finset.card_insert_le _ _) ?_
        rw [card_neighborFinset_eq_degree]
        omega
      have h2 := Finset.card_univ_diff (α := Fin 9) (insert v (G.neighborFinset v))
      rw [hsdef]
      simp only [Fintype.card_fin] at h2
      omega
    obtain ⟨t, hts, htindep, htc⟩ := exists_isNIndepSet_three G h3 s hcard
    have hvt : v ∉ t := by
      intro hvt
      have := hts hvt
      rw [hsdef, Finset.mem_sdiff] at this
      exact this.2 (Finset.mem_insert_self _ _)
    have hvnadj : ∀ a ∈ t, ¬ G.Adj v a := by
      intro a ha hadj
      have := hts ha
      rw [hsdef, Finset.mem_sdiff] at this
      exact this.2 (Finset.mem_insert_of_mem ((mem_neighborFinset G v a).mpr hadj))
    refine h4 (insert v t) ⟨?_, ?_⟩
    · intro a ha b hb hab
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · exact absurd rfl hab
        · exact hvnadj b hb
      · rcases hb with rfl | hb
        · exact fun hadj => hvnadj a ha hadj.symm
        · exact htindep ha hb hab
    · rw [Finset.card_insert_of_notMem hvt, htc]
  -- so the graph is 3-regular on 9 vertices, contradicting the handshake lemma
  have hsum : ∑ v : Fin 9, G.degree v = 2 * G.edgeFinset.card :=
    G.sum_degrees_eq_twice_card_edges
  have h27 : ∑ v : Fin 9, G.degree v = 27 := by
    have : ∀ v : Fin 9, G.degree v = 3 := fun v => le_antisymm (hdeg_le v) (hdeg_ge v)
    simp [this]
  omega

/-! ### The lower bound: the Wagner graph on 8 vertices -/

/-- Adjacency relation of the circulant graph `C₈(1,4)` (the Wagner graph). -/
def wagnerAdj (a b : Fin 8) : Prop :=
  (a.val + 8 - b.val) % 8 = 1 ∨ (a.val + 8 - b.val) % 8 = 4 ∨ (a.val + 8 - b.val) % 8 = 7

instance : DecidableRel wagnerAdj := fun a b => by unfold wagnerAdj; infer_instance

/-- The Wagner graph: the cycle on 8 vertices together with its four main diagonals.
It is triangle-free and has independence number 3. -/
def wagner : SimpleGraph (Fin 8) where
  Adj := wagnerAdj
  symm := by intro a b h; revert a b h; decide
  loopless := ⟨by decide⟩

instance : DecidableRel wagner.Adj := fun a b => decidable_of_iff (wagnerAdj a b) Iff.rfl

theorem wagner_no_triangle : ∀ s : Finset (Fin 8), ¬ wagner.IsNClique 3 s := by decide

theorem wagner_no_indep_four : ∀ s : Finset (Fin 8), ¬ wagner.IsNIndepSet 4 s := by decide

theorem not_ramseyProp_eight : ¬ RamseyProp 8 := by
  intro h
  rcases h wagner with ⟨s, hs⟩ | ⟨t, ht⟩
  · exact wagner_no_triangle s hs
  · exact wagner_no_indep_four t ht

/-- **R(3,4) = 9**: nine is the least `n` such that every graph on `n` vertices contains a
triangle or an independent set of size four. -/
theorem ramsey_3_4 : IsLeast {n : ℕ | RamseyProp n} 9 := by
  constructor
  · exact ramseyProp_nine
  · intro n hn
    by_contra hlt
    push_neg at hlt
    exact not_ramseyProp_eight (RamseyProp.mono (by omega) hn)

end Math

