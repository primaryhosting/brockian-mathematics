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
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

open Finset SimpleGraph

/-! ## A decidable reformulation of `CliqueFree` -/

/-- `G.CliqueFree n` says: no finset of `n` pairwise-adjacent vertices. -/
theorem cliqueFree_iff_pairwise {V : Type*} [DecidableEq V] (G : SimpleGraph V) (n : ℕ) :
    G.CliqueFree n ↔ ∀ s : Finset V, ¬ ((∀ a ∈ s, ∀ b ∈ s, a ≠ b → G.Adj a b) ∧ s.card = n) := by
  constructor
  · intro h s hs
    exact h s ⟨fun a ha b hb hab => hs.1 a ha b hb hab, hs.2⟩
  · intro h s hs
    exact h s ⟨fun a ha b hb hab => hs.1 ha hb hab, hs.2⟩

/-- From cliquefreeness: a set of pairwise adjacent vertices cannot have `n` elements. -/
theorem card_ne_of_cliqueFree {V : Type*} [DecidableEq V] {G : SimpleGraph V} {n : ℕ}
    (h : G.CliqueFree n) (s : Finset V) (hs : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → G.Adj a b) :
    s.card ≠ n := fun hc => (cliqueFree_iff_pairwise G n).mp h s ⟨hs, hc⟩

/-! ## The Ramsey property -/

/-- `RamseyProp n s t` holds when every graph on `n` vertices contains either a clique of
size `s` or an independent set of size `t`. -/
def RamseyProp (n s t : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree s ∨ ¬ Gᶜ.CliqueFree t

/-! ## The lower bound: a (3,4)-Ramsey graph on 8 vertices -/

/-- The Wagner graph (`C₈` plus its four main diagonals): triangle-free with independence
number 3. -/
def W8 : SimpleGraph (Fin 8) :=
  SimpleGraph.fromRel (fun i j => (i.val + 1) % 8 = j.val ∨ (i.val + 4) % 8 = j.val)

instance : DecidableRel W8.Adj := fun a b => by unfold W8; infer_instance

theorem W8_cliqueFree_three : W8.CliqueFree 3 := by
  rw [cliqueFree_iff_pairwise]; decide

theorem W8_compl_cliqueFree_four : W8ᶜ.CliqueFree 4 := by
  rw [cliqueFree_iff_pairwise]; decide

/-! ## Auxiliary combinatorial lemmas (upper bound) -/

section Aux

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In a triangle-free graph with no independent set of size 4, every vertex has degree
at most 3. -/
theorem degree_le_three (h3 : G.CliqueFree 3) (h4 : Gᶜ.CliqueFree 4) (v : V) :
    G.degree v ≤ 3 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq (s := G.neighborFinset v) (n := 4) (by
      rw [← SimpleGraph.card_neighborFinset_eq_degree] at hlt; omega)
  refine card_ne_of_cliqueFree h4 T ?_ hTcard
  intro a ha b hb hab
  have hva : G.Adj v a := by
    have := hTsub ha; rwa [SimpleGraph.mem_neighborFinset] at this
  have hvb : G.Adj v b := by
    have := hTsub hb; rwa [SimpleGraph.mem_neighborFinset] at this
  rw [SimpleGraph.compl_adj]
  refine ⟨hab, fun hadj => ?_⟩
  exact card_ne_of_cliqueFree h3 {v, a, b} (by
    intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hxy
        | exact hva | exact hvb | exact hadj
        | exact hva.symm | exact hvb.symm | exact hadj.symm) (by
    rw [Finset.card_insert_of_notMem (by simp [hva.ne, hvb.ne]),
      Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton])

omit [Fintype V] in
/-- Ramsey `R(3,3) ≤ 6`, localized: in a triangle-free graph, any 6 vertices contain three
pairwise non-adjacent ones. -/
theorem exists_independent_three (h3 : G.CliqueFree 3) (S : Finset V) (hS : 6 ≤ S.card) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      ¬ G.Adj a b ∧ ¬ G.Adj a c ∧ ¬ G.Adj b c := by
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hSne
  set T := S.erase x with hT
  have hTcard : 5 ≤ T.card := by
    have h : T.card = S.card - 1 := by rw [hT]; exact Finset.card_erase_of_mem hx
    omega
  set A := T.filter (fun y => G.Adj x y) with hA
  set B := T.filter (fun y => ¬ G.Adj x y) with hB
  have hsplit : A.card + B.card = T.card := Finset.card_filter_add_card_filter_not _
  -- three vertices adjacent to `x` are pairwise non-adjacent
  by_cases hcase : 3 ≤ A.card
  · obtain ⟨A', hA'sub, hA'card⟩ := Finset.exists_subset_card_eq hcase
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hA'card
    have hmemA : ∀ y ∈ ({a, b, c} : Finset V), y ∈ S ∧ G.Adj x y := by
      intro y hy
      have hyA := hA'sub hy
      rw [hA, Finset.mem_filter] at hyA
      exact ⟨Finset.mem_of_mem_erase hyA.1, hyA.2⟩
    have key : ∀ p ∈ ({a, b, c} : Finset V), ∀ q ∈ ({a, b, c} : Finset V), p ≠ q →
        ¬ G.Adj p q := by
      intro p hp q hq hpq hadj
      obtain ⟨hpS, hxp⟩ := hmemA p hp
      obtain ⟨hqS, hxq⟩ := hmemA q hq
      exact card_ne_of_cliqueFree h3 {x, p, q} (by
        intro u hu w hw huw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu hw
        rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
          first
            | exact absurd rfl huw
            | exact hxp | exact hxq | exact hadj
            | exact hxp.symm | exact hxq.symm | exact hadj.symm) (by
        rw [Finset.card_insert_of_notMem (by simp [hxp.ne, hxq.ne]),
          Finset.card_insert_of_notMem (by simp [hpq]), Finset.card_singleton])
    have ha : a ∈ ({a, b, c} : Finset V) := by simp
    have hb : b ∈ ({a, b, c} : Finset V) := by simp
    have hc : c ∈ ({a, b, c} : Finset V) := by simp
    exact ⟨a, (hmemA a ha).1, b, (hmemA b hb).1, c, (hmemA c hc).1, hab, hac, hbc,
      key a ha b hb hab, key a ha c hc hac, key b hb c hc hbc⟩
  · -- three vertices non-adjacent to `x`
    have hcase' : 3 ≤ B.card := by omega
    obtain ⟨B', hB'sub, hB'card⟩ := Finset.exists_subset_card_eq hcase'
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hB'card
    have hmemB : ∀ y ∈ ({a, b, c} : Finset V), y ∈ S ∧ ¬ G.Adj x y ∧ x ≠ y := by
      intro y hy
      have hyB := hB'sub hy
      rw [hB, Finset.mem_filter] at hyB
      exact ⟨Finset.mem_of_mem_erase hyB.1, hyB.2, fun h => (Finset.ne_of_mem_erase hyB.1) h.symm⟩
    have ha := hmemB a (by simp)
    have hb := hmemB b (by simp)
    have hc := hmemB c (by simp)
    by_cases hab' : G.Adj a b
    · by_cases hac' : G.Adj a c
      · by_cases hbc' : G.Adj b c
        · exact absurd (card_ne_of_cliqueFree h3 {a, b, c} (by
            intro u hu w hw huw
            simp only [Finset.mem_insert, Finset.mem_singleton] at hu hw
            rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
              first
                | exact absurd rfl huw
                | exact hab' | exact hac' | exact hbc'
                | exact hab'.symm | exact hac'.symm | exact hbc'.symm) (by
            rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
              Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]))
            (by simp)
        · exact ⟨x, hx, b, hb.1, c, hc.1, hb.2.2, hc.2.2, hbc, hb.2.1, hc.2.1, hbc'⟩
      · exact ⟨x, hx, a, ha.1, c, hc.1, ha.2.2, hc.2.2, hac, ha.2.1, hc.2.1, hac'⟩
    · exact ⟨x, hx, a, ha.1, b, hb.1, ha.2.2, hb.2.2, hab, ha.2.1, hb.2.1, hab'⟩

/-- In a triangle-free graph on 9 vertices with no independent set of size 4, every vertex
has degree at least 3. -/
theorem three_le_degree (hcard : Fintype.card V = 9) (h3 : G.CliqueFree 3)
    (h4 : Gᶜ.CliqueFree 4) (v : V) : 3 ≤ G.degree v := by
  by_contra hlt
  push_neg at hlt
  set S := (Finset.univ : Finset V) \ insert v (G.neighborFinset v) with hS
  have hins : (insert v (G.neighborFinset v)).card ≤ 3 := by
    have hv : v ∉ G.neighborFinset v := by simp
    rw [Finset.card_insert_of_notMem hv, SimpleGraph.card_neighborFinset_eq_degree]
    omega
  have hScard : 6 ≤ S.card := by
    have := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (insert v (G.neighborFinset v)))
    rw [Finset.card_univ, hcard, ← hS] at this
    omega
  obtain ⟨a, haS, b, hbS, c, hcS, hab, hac, hbc, hnab, hnac, hnbc⟩ :=
    exists_independent_three G h3 S hScard
  have hprop : ∀ y ∈ S, y ≠ v ∧ ¬ G.Adj v y := by
    intro y hy
    rw [hS, Finset.mem_sdiff] at hy
    have := hy.2
    simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset] at this
    push_neg at this
    exact this
  obtain ⟨hav, hva⟩ := hprop a haS
  obtain ⟨hbv, hvb⟩ := hprop b hbS
  obtain ⟨hcv, hvc⟩ := hprop c hcS
  refine card_ne_of_cliqueFree h4 {v, a, b, c} ?_ ?_
  · intro p hp q hq hpq
    rw [SimpleGraph.compl_adj]
    refine ⟨hpq, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hpq
        | exact hva | exact hvb | exact hvc
        | exact hnab | exact hnac | exact hnbc
        | exact fun h => hva h.symm | exact fun h => hvb h.symm | exact fun h => hvc h.symm
        | exact fun h => hnab h.symm | exact fun h => hnac h.symm | exact fun h => hnbc h.symm
  · rw [Finset.card_insert_of_notMem (by
        simp [Ne.symm hav, Ne.symm hbv, Ne.symm hcv]),
      Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]

end Aux

/-! ## The upper bound -/

theorem ramseyProp_nine : RamseyProp 9 3 4 := by
  intro G
  by_contra hcon
  push_neg at hcon
  obtain ⟨h3, h4⟩ := hcon
  classical
  have hcard : Fintype.card (Fin 9) = 9 := by simp
  have hdeg : ∀ v : Fin 9, G.degree v = 3 := fun v =>
    le_antisymm (degree_le_three G h3 h4 v) (three_le_degree G hcard h3 h4 v)
  have hsum : ∑ v : Fin 9, G.degree v = 2 * G.edgeFinset.card :=
    G.sum_degrees_eq_twice_card_edges
  rw [Finset.sum_congr rfl (fun v _ => hdeg v)] at hsum
  simp only [Finset.sum_const, Finset.card_univ, hcard, smul_eq_mul] at hsum
  omega

/-! ## The main theorem -/

/-- **The Ramsey number `R(3,4)` equals 9**: 9 is the least `n` such that every graph on `n`
vertices contains a triangle or an independent set of size 4, and there is a graph on 8
vertices with neither. -/
theorem ramsey_3_4 : IsLeast {n : ℕ | RamseyProp n 3 4} 9 := by
  constructor
  · exact ramseyProp_nine
  · intro n hn
    by_contra hlt
    push_neg at hlt
    have hle : n ≤ 8 := by omega
    classical
    set f : Fin n ↪ Fin 8 := Fin.castLEEmb hle with hf
    set H : SimpleGraph (Fin n) := W8.comap f with hH
    have hemb : H ↪g W8 := SimpleGraph.Embedding.comap f W8
    have hH3 : H.CliqueFree 3 := SimpleGraph.CliqueFree.comap hemb W8_cliqueFree_three
    have hH4 : Hᶜ.CliqueFree 4 := by
      have : Hᶜ = W8ᶜ.comap f := by
        ext a b
        simp only [SimpleGraph.compl_adj, hH, SimpleGraph.comap_adj]
        constructor
        · rintro ⟨hne, hnadj⟩
          exact ⟨fun h => hne (f.injective h), hnadj⟩
        · rintro ⟨hne, hnadj⟩
          exact ⟨fun h => hne (by rw [h]), hnadj⟩
      rw [this]
      exact SimpleGraph.CliqueFree.comap (SimpleGraph.Embedding.comap f W8ᶜ)
        W8_compl_cliqueFree_four
    rcases hn H with h | h
    · exact h hH3
    · exact h hH4

end Math

