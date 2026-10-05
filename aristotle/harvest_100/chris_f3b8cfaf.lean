import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset SimpleGraph

namespace Ramsey35

variable {V : Type*} [DecidableEq V]

/-! ### Basic clique helpers -/

omit [DecidableEq V] in
/-- A finset all of whose distinct pairs are non-adjacent is a clique in the complement. -/
lemma compl_isNClique_of_pairwise_not_adj (G : SimpleGraph V) (t : Finset V)
    (h : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → ¬ G.Adj a b) : Gᶜ.IsNClique t.card t := by
  refine ⟨?_, rfl⟩
  intro a ha b hb hab
  simp only [Finset.mem_coe] at ha hb
  exact (SimpleGraph.compl_adj G a b).2 ⟨hab, h a ha b hb hab⟩

omit [DecidableEq V] in
/-- A finset all of whose distinct pairs are adjacent is a clique. -/
lemma isNClique_of_pairwise_adj (G : SimpleGraph V) (t : Finset V)
    (h : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → G.Adj a b) : G.IsNClique t.card t := by
  refine ⟨?_, rfl⟩
  intro a ha b hb hab
  simp only [Finset.mem_coe] at ha hb
  exact h a ha b hb hab

/-- Extending an independent set by a vertex non-adjacent to all of it. -/
lemma compl_isNClique_insert (G : SimpleGraph V) {v : V} {t : Finset V} {k : ℕ}
    (hvt : v ∉ t) (hnadj : ∀ w ∈ t, ¬ G.Adj v w) (ht : Gᶜ.IsNClique k t) :
    Gᶜ.IsNClique (k + 1) (insert v t) := by
  refine ⟨?_, ?_⟩
  · rw [Finset.coe_insert]
    refine SimpleGraph.IsClique.insert ht.1 ?_
    intro b hb hbv
    exact (SimpleGraph.compl_adj G v b).2 ⟨hbv, hnadj b hb⟩
  · rw [Finset.card_insert_of_notMem hvt, ht.2]

/-! ### The handshake parity lemma, relativised to a finset -/

lemma even_sum_card_filter_adj (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Even (∑ v ∈ S, #{w ∈ S | G.Adj v w}) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert x S hx ih =>
      have hxx : ¬ G.Adj x x := G.irrefl
      have h1 : {w ∈ insert x S | G.Adj x w} = {w ∈ S | G.Adj x w} := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hw, ha⟩
          · exact absurd ha hxx
          · exact ⟨hw, ha⟩
        · rintro ⟨hw, ha⟩; exact ⟨Or.inr hw, ha⟩
      have h2 : ∀ v ∈ S, #{w ∈ insert x S | G.Adj v w}
          = #{w ∈ S | G.Adj v w} + (if G.Adj v x then 1 else 0) := by
        intro v hv
        by_cases hvx : G.Adj v x
        · have : {w ∈ insert x S | G.Adj v w} = insert x {w ∈ S | G.Adj v w} := by
            ext w
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨rfl | hw, ha⟩
              · exact Or.inl rfl
              · exact Or.inr ⟨hw, ha⟩
            · rintro (rfl | ⟨hw, ha⟩)
              · exact ⟨Or.inl rfl, hvx⟩
              · exact ⟨Or.inr hw, ha⟩
          rw [this, Finset.card_insert_of_notMem (by simp [hx]), if_pos hvx]
        · have : {w ∈ insert x S | G.Adj v w} = {w ∈ S | G.Adj v w} := by
            ext w
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨rfl | hw, ha⟩
              · exact absurd ha hvx
              · exact ⟨hw, ha⟩
            · rintro ⟨hw, ha⟩; exact ⟨Or.inr hw, ha⟩
          rw [this, if_neg hvx, Nat.add_zero]
      have h3 : ∑ v ∈ S, (if G.Adj v x then 1 else 0) = #{w ∈ S | G.Adj x w} := by
        rw [Finset.card_filter]
        exact Finset.sum_congr rfl (fun v _ => if_congr (G.adj_comm v x) rfl rfl)
      rw [Finset.sum_insert hx, h1, Finset.sum_congr rfl h2, Finset.sum_add_distrib, h3]
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + #{w ∈ S | G.Adj x w}, by omega⟩

/-! ### The Ramsey upper bounds -/

lemma ramsey_3_3 (G : SimpleGraph V) (S : Finset V) (hS : 6 ≤ #S) :
    (∃ s ⊆ S, G.IsNClique 3 s) ∨ (∃ t ⊆ S, Gᶜ.IsNClique 3 t) := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨h3, h4⟩ := hcon
  obtain ⟨v, hv⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  set A := {w ∈ S.erase v | G.Adj v w} with hAdef
  set B := {w ∈ S.erase v | ¬ G.Adj v w} with hBdef
  have hcard : #A + #B = #S - 1 := by
    rw [hAdef, hBdef, Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hv]
  have hAS : A ⊆ S := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  have hBS : B ⊆ S := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  -- neighbours are pairwise non-adjacent
  have hApair : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ G.Adj a b := by
    intro a ha b hb hab hadj
    rw [hAdef, Finset.mem_filter] at ha hb
    refine h3 {v, a, b} ?_ ?_
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hv
      · exact Finset.mem_of_mem_erase ha.1
      · exact Finset.mem_of_mem_erase hb.1
    · exact SimpleGraph.is3Clique_triple_iff.2 ⟨ha.2, hb.2, hadj⟩
  -- non-neighbours are pairwise adjacent
  have hBpair : ∀ a ∈ B, ∀ b ∈ B, a ≠ b → G.Adj a b := by
    intro a hb' b hb hab
    by_contra hadj
    rw [hBdef, Finset.mem_filter] at hb' hb
    refine h4 {v, a, b} ?_ ?_
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hv
      · exact Finset.mem_of_mem_erase hb'.1
      · exact Finset.mem_of_mem_erase hb.1
    · refine SimpleGraph.is3Clique_triple_iff.2 ⟨?_, ?_, ?_⟩
      · exact (SimpleGraph.compl_adj G _ _).2
          ⟨fun h => (Finset.ne_of_mem_erase hb'.1) h.symm, hb'.2⟩
      · exact (SimpleGraph.compl_adj G _ _).2
          ⟨fun h => (Finset.ne_of_mem_erase hb.1) h.symm, hb.2⟩
      · exact (SimpleGraph.compl_adj G _ _).2 ⟨hab, hadj⟩
  rcases (by omega : 3 ≤ #A ∨ 3 ≤ #B) with hA3 | hB3
  · obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hA3
    refine h4 t (hts.trans hAS) ?_
    have := compl_isNClique_of_pairwise_not_adj G t
      (fun a ha b hb hab => hApair a (hts ha) b (hts hb) hab)
    rwa [htc] at this
  · obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hB3
    refine h3 t (hts.trans hBS) ?_
    have := isNClique_of_pairwise_adj G t
      (fun a ha b hb hab => hBpair a (hts ha) b (hts hb) hab)
    rwa [htc] at this

lemma ramsey_3_4 (G : SimpleGraph V) (S : Finset V) (hS : 9 ≤ #S) :
    (∃ s ⊆ S, G.IsNClique 3 s) ∨ (∃ t ⊆ S, Gᶜ.IsNClique 4 t) := by
  classical
  obtain ⟨S', hS'sub, hS'card⟩ := Finset.exists_subset_card_eq hS
  suffices h : (∃ s ⊆ S', G.IsNClique 3 s) ∨ (∃ t ⊆ S', Gᶜ.IsNClique 4 t) by
    rcases h with ⟨s, hs, h⟩ | ⟨t, ht, h⟩
    · exact Or.inl ⟨s, hs.trans hS'sub, h⟩
    · exact Or.inr ⟨t, ht.trans hS'sub, h⟩
  clear hS hS'sub
  by_contra hcon
  push_neg at hcon
  obtain ⟨h3, h4⟩ := hcon
  -- every vertex has exactly three neighbours inside `S'`
  have key : ∀ v ∈ S', #{w ∈ S' | G.Adj v w} = 3 := by
    intro v hv
    set A := {w ∈ S'.erase v | G.Adj v w} with hAdef
    set B := {w ∈ S'.erase v | ¬ G.Adj v w} with hBdef
    have hcard : #A + #B = 8 := by
      rw [hAdef, hBdef, Finset.card_filter_add_card_filter_not,
        Finset.card_erase_of_mem hv, hS'card]
    have hAS : A ⊆ S' := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
    have hBS : B ⊆ S' := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
    have hApair : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ G.Adj a b := by
      intro a ha b hb hab hadj
      rw [hAdef, Finset.mem_filter] at ha hb
      refine h3 {v, a, b} ?_ ?_
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hv
        · exact Finset.mem_of_mem_erase ha.1
        · exact Finset.mem_of_mem_erase hb.1
      · exact SimpleGraph.is3Clique_triple_iff.2 ⟨ha.2, hb.2, hadj⟩
    -- at most three neighbours
    have hAle : #A ≤ 3 := by
      by_contra hA
      push_neg at hA
      obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hA
      refine h4 t (hts.trans hAS) ?_
      have := compl_isNClique_of_pairwise_not_adj G t
        (fun a ha b hb hab => hApair a (hts ha) b (hts hb) hab)
      rwa [htc] at this
    -- at most five non-neighbours
    have hBle : #B ≤ 5 := by
      by_contra hB
      push_neg at hB
      rcases ramsey_3_3 G B (by omega) with ⟨s, hs, hsc⟩ | ⟨t, ht, htc⟩
      · exact h3 s (hs.trans hBS) hsc
      · refine h4 (insert v t) ?_ ?_
        · intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact hv
          · exact hBS (ht hx)
        · refine compl_isNClique_insert G ?_ ?_ htc
          · intro hvt
            exact (Finset.ne_of_mem_erase (Finset.mem_filter.1 (ht hvt)).1) rfl
          · intro w hw
            exact (Finset.mem_filter.1 (ht hw)).2
    have hAeq : #A = 3 := by omega
    have : {w ∈ S' | G.Adj v w} = A := by
      rw [hAdef]
      ext w
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hw, ha⟩
        exact ⟨⟨fun h => G.irrefl (h ▸ ha), hw⟩, ha⟩
      · rintro ⟨⟨_, hw⟩, ha⟩
        exact ⟨hw, ha⟩
    rw [this, hAeq]
  have hsum : ∑ v ∈ S', #{w ∈ S' | G.Adj v w} = 27 := by
    rw [Finset.sum_congr rfl key, Finset.sum_const, hS'card]
    simp
  have := even_sum_card_filter_adj G S'
  rw [hsum] at this
  exact (by decide : ¬ Even 27) this

lemma ramsey_3_5_finset (G : SimpleGraph V) (S : Finset V) (hS : 14 ≤ #S) :
    (∃ s ⊆ S, G.IsNClique 3 s) ∨ (∃ t ⊆ S, Gᶜ.IsNClique 5 t) := by
  classical
  obtain ⟨S', hS'sub, hS'card⟩ := Finset.exists_subset_card_eq hS
  suffices h : (∃ s ⊆ S', G.IsNClique 3 s) ∨ (∃ t ⊆ S', Gᶜ.IsNClique 5 t) by
    rcases h with ⟨s, hs, h⟩ | ⟨t, ht, h⟩
    · exact Or.inl ⟨s, hs.trans hS'sub, h⟩
    · exact Or.inr ⟨t, ht.trans hS'sub, h⟩
  clear hS hS'sub
  by_contra hcon
  push_neg at hcon
  obtain ⟨h3, h5⟩ := hcon
  obtain ⟨v, hv⟩ : S'.Nonempty := Finset.card_pos.mp (by omega)
  set A := {w ∈ S'.erase v | G.Adj v w} with hAdef
  set B := {w ∈ S'.erase v | ¬ G.Adj v w} with hBdef
  have hcard : #A + #B = 13 := by
    rw [hAdef, hBdef, Finset.card_filter_add_card_filter_not,
      Finset.card_erase_of_mem hv, hS'card]
  have hAS : A ⊆ S' := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  have hBS : B ⊆ S' := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  have hApair : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ G.Adj a b := by
    intro a ha b hb hab hadj
    rw [hAdef, Finset.mem_filter] at ha hb
    refine h3 {v, a, b} ?_ ?_
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hv
      · exact Finset.mem_of_mem_erase ha.1
      · exact Finset.mem_of_mem_erase hb.1
    · exact SimpleGraph.is3Clique_triple_iff.2 ⟨ha.2, hb.2, hadj⟩
  have hAle : #A ≤ 4 := by
    by_contra hA
    push_neg at hA
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hA
    refine h5 t (hts.trans hAS) ?_
    have := compl_isNClique_of_pairwise_not_adj G t
      (fun a ha b hb hab => hApair a (hts ha) b (hts hb) hab)
    rwa [htc] at this
  have hBle : #B ≤ 8 := by
    by_contra hB
    push_neg at hB
    rcases ramsey_3_4 G B (by omega) with ⟨s, hs, hsc⟩ | ⟨t, ht, htc⟩
    · exact h3 s (hs.trans hBS) hsc
    · refine h5 (insert v t) ?_ ?_
      · intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact hv
        · exact hBS (ht hx)
      · refine compl_isNClique_insert G ?_ ?_ htc
        · intro hvt
          exact (Finset.ne_of_mem_erase (Finset.mem_filter.1 (ht hvt)).1) rfl
        · intro w hw
          exact (Finset.mem_filter.1 (ht hw)).2
  omega

/-! ### The lower bound: an explicit graph on 13 vertices -/

/-- Adjacency of the circulant graph `C₁₃(1,5)`. -/
def adjB (i j : Fin 13) : Bool :=
  let d := (i.val + 13 - j.val) % 13
  d = 1 || d = 5 || d = 8 || d = 12

lemma adjB_symm : ∀ i j : Fin 13, adjB i j = adjB j i := by decide

lemma adjB_irrefl : ∀ i : Fin 13, adjB i i = false := by decide

/-- The circulant graph `C₁₃(1,5)`: it is triangle-free and has independence number 4. -/
def G13 : SimpleGraph (Fin 13) where
  Adj i j := adjB i j = true
  symm := by
    intro i j h
    rw [adjB_symm]; exact h
  loopless := ⟨by
    intro i h
    rw [adjB_irrefl] at h
    exact Bool.false_ne_true h⟩

instance : DecidableRel G13.Adj := fun i j => inferInstanceAs (Decidable (adjB i j = true))

set_option maxHeartbeats 1000000 in
lemma G13_no_triangle : ∀ a b c : Fin 13, ¬ (adjB a b ∧ adjB b c ∧ adjB a c) := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma G13_no_indep5 : ∀ a b c d e : Fin 13, a < b → b < c → c < d → d < e →
    (adjB a b || adjB a c || adjB a d || adjB a e || adjB b c || adjB b d || adjB b e ||
      adjB c d || adjB c e || adjB d e) = true := by decide

/-- Five distinct elements, in increasing order, of a finset of cardinality 5. -/
lemma exists_sorted_five {α : Type*} [LinearOrder α] {t : Finset α} (h : #t = 5) :
    ∃ a b c d e : α, a < b ∧ b < c ∧ c < d ∧ d < e ∧
      a ∈ t ∧ b ∈ t ∧ c ∈ t ∧ d ∈ t ∧ e ∈ t := by
  set f := t.orderIsoOfFin h
  exact ⟨f 0, f 1, f 2, f 3, f 4,
    Subtype.coe_lt_coe.2 (f.lt_iff_lt.2 (by decide)),
    Subtype.coe_lt_coe.2 (f.lt_iff_lt.2 (by decide)),
    Subtype.coe_lt_coe.2 (f.lt_iff_lt.2 (by decide)),
    Subtype.coe_lt_coe.2 (f.lt_iff_lt.2 (by decide)),
    (f 0).2, (f 1).2, (f 2).2, (f 3).2, (f 4).2⟩

theorem G13_triangle_free : ¬ ∃ s : Finset (Fin 13), G13.IsNClique 3 s := by
  rintro ⟨s, hs⟩
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 hs.2
  rw [SimpleGraph.is3Clique_triple_iff] at hs
  exact G13_no_triangle a b c ⟨hs.1, hs.2.2, hs.2.1⟩

theorem G13_no_indep_five : ¬ ∃ t : Finset (Fin 13), G13ᶜ.IsNClique 5 t := by
  rintro ⟨t, ht⟩
  obtain ⟨a, b, c, d, e, hab, hbc, hcd, hde, ha, hb, hc, hd, he⟩ := exists_sorted_five ht.2
  have hne : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → ¬ G13.Adj x y := by
    intro x hx y hy hxy
    exact ((SimpleGraph.compl_adj G13 x y).1 (ht.1 hx hy hxy)).2
  have h := G13_no_indep5 a b c d e hab hbc hcd hde
  simp only [Bool.or_eq_true] at h
  have hfalse : ∀ x ∈ t, ∀ y ∈ t, x < y → adjB x y = false := by
    intro x hx y hy hxy
    have := hne x hx y hy (ne_of_lt hxy)
    simpa [G13] using this
  rw [hfalse a ha b hb hab, hfalse a ha c hc (hab.trans hbc),
    hfalse a ha d hd (hab.trans (hbc.trans hcd)),
    hfalse a ha e he (hab.trans (hbc.trans (hcd.trans hde))),
    hfalse b hb c hc hbc, hfalse b hb d hd (hbc.trans hcd),
    hfalse b hb e he (hbc.trans (hcd.trans hde)),
    hfalse c hc d hd hcd, hfalse c hc e he (hcd.trans hde),
    hfalse d hd e he hde] at h
  simp at h

/-! ### Monotonicity of the Ramsey property -/

/-- The set of `N` for which every graph on `Fin N` contains a triangle or an
independent set of size 5. -/
def RamseySet : Set ℕ :=
  {N : ℕ | ∀ G : SimpleGraph (Fin N),
    (∃ s : Finset (Fin N), G.IsNClique 3 s) ∨ (∃ t : Finset (Fin N), Gᶜ.IsNClique 5 t)}

lemma RamseySet_upward {N M : ℕ} (hNM : N ≤ M) (hN : N ∈ RamseySet) : M ∈ RamseySet := by
  intro G
  set f : Fin N ↪ Fin M := (Fin.castLEEmb hNM) with hf
  set H : SimpleGraph (Fin N) := SimpleGraph.comap f G with hH
  have hadj : ∀ a b : Fin N, H.Adj a b ↔ G.Adj (f a) (f b) := fun a b => Iff.rfl
  rcases hN H with ⟨s, hs⟩ | ⟨t, ht⟩
  · refine Or.inl ⟨s.map f, ?_, ?_⟩
    · intro x hx y hy hxy
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      have hab : a ≠ b := fun h => hxy (by rw [h])
      exact (hadj a b).1 (hs.1 ha hb hab)
    · rw [Finset.card_map, hs.2]
  · refine Or.inr ⟨t.map f, ?_, ?_⟩
    · intro x hx y hy hxy
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      have hab : a ≠ b := fun h => hxy (by rw [h])
      have := ht.1 ha hb hab
      rw [SimpleGraph.compl_adj] at this ⊢
      exact ⟨hxy, fun hcon => this.2 ((hadj a b).2 hcon)⟩
    · rw [Finset.card_map, ht.2]

end Ramsey35

namespace Math

/-- **R(3,5) = 14**: fourteen is the least `N` such that every graph on `N` vertices
contains a triangle or an independent set of size 5. -/
theorem ramsey_3_5 :
    IsLeast {N : ℕ | ∀ G : SimpleGraph (Fin N),
      (∃ s : Finset (Fin N), G.IsNClique 3 s) ∨
        (∃ t : Finset (Fin N), Gᶜ.IsNClique 5 t)} 14 := by
  constructor
  · intro G
    rcases Ramsey35.ramsey_3_5_finset G Finset.univ (by simp) with ⟨s, _, hs⟩ | ⟨t, _, ht⟩
    · exact Or.inl ⟨s, hs⟩
    · exact Or.inr ⟨t, ht⟩
  · intro N hN
    by_contra hlt
    push_neg at hlt
    have h13 : (13 : ℕ) ∈ Ramsey35.RamseySet :=
      Ramsey35.RamseySet_upward (by omega) hN
    rcases h13 Ramsey35.G13 with h | h
    · exact Ramsey35.G13_triangle_free h
    · exact Ramsey35.G13_no_indep_five h

end Math

