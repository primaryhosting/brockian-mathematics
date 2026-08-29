/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000

namespace Math

open Finset

/-- `RamseyProp n s t` says: every simple graph on `n` vertices contains either a clique of
size `s` or an independent set (a clique in the complement) of size `t`. -/
def RamseyProp (n s t : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n),
    (∃ S : Finset (Fin n), G.IsNClique s S) ∨ (∃ T : Finset (Fin n), Gᶜ.IsNClique t T)

/-- The two-colour Ramsey number `R(s,t)`: the least `n` such that `RamseyProp n s t` holds. -/
noncomputable def ramseyNumber (s t : ℕ) : ℕ := sInf {n | RamseyProp n s t}

/-! ## Basic reformulations -/

section Basic

variable {V : Type*}

/-- A clique in the complement is exactly a pairwise non-adjacent set. -/
lemma isNClique_compl_iff (G : SimpleGraph V) (n : ℕ) (S : Finset V) :
    Gᶜ.IsNClique n S ↔ ((S : Set V).Pairwise fun a b => ¬ G.Adj a b) ∧ S.card = n := by
  rw [SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun a ha b hb hab => ((SimpleGraph.compl_adj _ _ _).1 (h1 ha hb hab)).2, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun a ha b hb hab => (SimpleGraph.compl_adj _ _ _).2 ⟨hab, h1 ha hb hab⟩, h2⟩

lemma isNClique_iff' (G : SimpleGraph V) (n : ℕ) (S : Finset V) :
    G.IsNClique n S ↔ ((S : Set V).Pairwise G.Adj) ∧ S.card = n := by
  rw [SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff]

/-- A triple `{a, b, c}` is pairwise `r`-related as soon as the three relevant pairs are. -/
lemma pairwise_triple (r : V → V → Prop) (hs : ∀ x y, r x y → r y x)
    (a b c : V) (hab : r a b) (hac : r a c) (hbc : r b c) :
    ({a, b, c} : Set V).Pairwise r := by
  intro x hx y hy hxy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl <;>
    first
      | exact absurd rfl hxy
      | assumption
      | exact hs _ _ (by assumption)

lemma card_triple [DecidableEq V] (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset V).card = 3 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
    Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]

end Basic

/-! ## Monotonicity in the number of vertices -/

section Mono

lemma comap_compl {V W : Type*} (f : V ↪ W) (G : SimpleGraph W) :
    SimpleGraph.comap f Gᶜ = (SimpleGraph.comap f G)ᶜ := by
  ext a b
  simp only [SimpleGraph.comap_adj, SimpleGraph.compl_adj]
  exact and_congr_left' (by simp [f.injective.ne_iff])

lemma clique_map {V W : Type*} (f : V ↪ W) (G : SimpleGraph W) (n : ℕ) (S : Finset V)
    (h : (SimpleGraph.comap f G).IsNClique n S) : G.IsNClique n (S.map f) := by
  rw [isNClique_iff'] at h ⊢
  refine ⟨?_, by simpa using h.2⟩
  intro x hx y hy hxy
  simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  have hab : a ≠ b := fun h => hxy (by rw [h])
  exact SimpleGraph.comap_adj.1 (h.1 ha hb hab)

lemma ramseyProp_mono {m n s t : ℕ} (hmn : m ≤ n) (H : RamseyProp m s t) : RamseyProp n s t := by
  intro G
  let f : Fin m ↪ Fin n := Fin.castLEEmb hmn
  rcases H (SimpleGraph.comap f G) with ⟨S, hS⟩ | ⟨T, hT⟩
  · exact Or.inl ⟨S.map f, clique_map f G s S hS⟩
  · refine Or.inr ⟨T.map f, clique_map f Gᶜ t T ?_⟩
    rw [comap_compl]
    exact hT

end Mono

/-! ## R(3,3) ≤ 6 -/

section R33

variable {V : Type*} [DecidableEq V]

/-- Ramsey's theorem for `(3,3)`: any six vertices contain a triangle or an independent
triple. -/
lemma ramsey_3_3 (G : SimpleGraph V) (A : Finset V) (hA : 6 ≤ A.card) :
    (∃ S ⊆ A, ((S : Set V).Pairwise G.Adj) ∧ S.card = 3) ∨
    (∃ S ⊆ A, ((S : Set V).Pairwise fun a b => ¬ G.Adj a b) ∧ S.card = 3) := by
  classical
  obtain ⟨A', hA'sub, hA'card⟩ := Finset.exists_subset_card_eq hA
  have hne : A'.Nonempty := by rw [← Finset.card_pos, hA'card]; norm_num
  obtain ⟨v, hv⟩ := hne
  set B := A'.erase v with hB
  have hBA : B ⊆ A := fun x hx => hA'sub (Finset.mem_of_mem_erase hx)
  have hBcard : B.card = 5 := by rw [hB, Finset.card_erase_of_mem hv, hA'card]
  have hsplit : (B.filter (fun u => G.Adj v u)).card
      + (B.filter (fun u => ¬ G.Adj v u)).card = 5 := by
    rw [Finset.card_filter_add_card_filter_not, hBcard]
  have hcase : 3 ≤ (B.filter (fun u => G.Adj v u)).card
      ∨ 3 ≤ (B.filter (fun u => ¬ G.Adj v u)).card := by omega
  rcases hcase with hc | hc
  · obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hc
    by_cases hp : ((S : Set V).Pairwise fun a b => ¬ G.Adj a b)
    · exact Or.inr ⟨S, fun x hx => hBA (Finset.mem_of_mem_filter x (hSsub hx)), hp, hScard⟩
    · left
      simp only [Set.Pairwise, not_forall, not_not] at hp
      obtain ⟨a, ha, b, hb, hab, hadj⟩ := hp
      have haF := hSsub ha
      have hbF := hSsub hb
      rw [Finset.mem_filter] at haF hbF
      have hva : v ≠ a := by rintro rfl; exact Finset.notMem_erase v A' haF.1
      have hvb : v ≠ b := by rintro rfl; exact Finset.notMem_erase v A' hbF.1
      refine ⟨{v, a, b}, ?_, ?_, card_triple v a b hva hvb hab⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl|rfl|rfl
        · exact hA'sub hv
        · exact hBA haF.1
        · exact hBA hbF.1
      · rw [Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton]
        exact pairwise_triple _ (fun _ _ h => G.symm h) v a b haF.2 hbF.2 hadj
  · obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hc
    by_cases hp : ((S : Set V).Pairwise G.Adj)
    · exact Or.inl ⟨S, fun x hx => hBA (Finset.mem_of_mem_filter x (hSsub hx)), hp, hScard⟩
    · right
      simp only [Set.Pairwise, not_forall] at hp
      obtain ⟨a, ha, b, hb, hab, hadj⟩ := hp
      have haF := hSsub ha
      have hbF := hSsub hb
      rw [Finset.mem_filter] at haF hbF
      have hva : v ≠ a := by rintro rfl; exact Finset.notMem_erase v A' haF.1
      have hvb : v ≠ b := by rintro rfl; exact Finset.notMem_erase v A' hbF.1
      refine ⟨{v, a, b}, ?_, ?_, card_triple v a b hva hvb hab⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl|rfl|rfl
        · exact hA'sub hv
        · exact hBA haF.1
        · exact hBA hbF.1
      · rw [Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton]
        exact pairwise_triple _ (fun _ _ h hh => h (G.symm hh)) v a b haF.2 hbF.2 hadj

end R33

/-! ## R(3,4) ≤ 9 -/

section R34

/-- Every graph on nine vertices contains a triangle or an independent set of size four. -/
lemma ramseyProp_nine : RamseyProp 9 3 4 := by
  classical
  intro G
  by_contra hcon
  push_neg at hcon
  obtain ⟨h3, h4⟩ := hcon
  have hTri : ∀ S : Finset (Fin 9), ((S : Set (Fin 9)).Pairwise G.Adj) → S.card ≠ 3 :=
    fun S hpw hc => h3 S ((isNClique_iff' G 3 S).2 ⟨hpw, hc⟩)
  have hInd : ∀ S : Finset (Fin 9),
      ((S : Set (Fin 9)).Pairwise fun a b => ¬ G.Adj a b) → S.card ≠ 4 :=
    fun S hpw hc => h4 S ((isNClique_compl_iff G 4 S).2 ⟨hpw, hc⟩)
  have hsymNot : Symmetric (fun a b : Fin 9 => ¬ G.Adj a b) := fun _ _ h hh => h (G.symm hh)
  -- Every degree is at most three: four neighbours of a vertex would be independent.
  have hdeg_le : ∀ v : Fin 9, G.degree v ≤ 3 := by
    intro v
    by_contra hlt
    push_neg at hlt
    have h4le : 4 ≤ (G.neighborFinset v).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; omega
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq h4le
    refine hInd S ?_ hScard
    intro a ha b hb hab hadj
    have hav : G.Adj v a := (G.mem_neighborFinset v a).1 (hSsub ha)
    have hbv : G.Adj v b := (G.mem_neighborFinset v b).1 (hSsub hb)
    refine hTri {v, a, b} ?_ (card_triple v a b hav.ne hbv.ne hab)
    rw [Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton]
    exact pairwise_triple _ (fun _ _ h => G.symm h) v a b hav hbv hadj
  -- Every degree is at least three: otherwise six non-neighbours give an independent triple.
  have hdeg_ge : ∀ v : Fin 9, 3 ≤ G.degree v := by
    intro v
    by_contra hlt
    push_neg at hlt
    set A : Finset (Fin 9) := Finset.univ \ insert v (G.neighborFinset v) with hA
    have hins : (insert v (G.neighborFinset v)).card = G.degree v + 1 := by
      rw [Finset.card_insert_of_notMem (G.notMem_neighborFinset_self v),
        SimpleGraph.card_neighborFinset_eq_degree]
    have hAcard : 6 ≤ A.card := by
      have hcard : A.card = 9 - (G.degree v + 1) := by
        rw [hA, Finset.sdiff_eq_inter_compl, Finset.univ_inter, Finset.card_compl, hins]
        simp
      omega
    have hvA : v ∉ A := by rw [hA]; simp
    have hAnotadj : ∀ x ∈ A, ¬ G.Adj v x := by
      intro x hx hadj
      rw [hA, Finset.mem_sdiff] at hx
      exact hx.2 (Finset.mem_insert_of_mem ((G.mem_neighborFinset v x).2 hadj))
    rcases ramsey_3_3 G A hAcard with ⟨S, hSsub, hpw, hcard⟩ | ⟨S, hSsub, hpw, hcard⟩
    · exact hTri S hpw hcard
    · refine hInd (insert v S) ?_ ?_
      · rw [Finset.coe_insert, Set.pairwise_insert_of_symmetric hsymNot]
        exact ⟨hpw, fun b hb _ => hAnotadj b (hSsub hb)⟩
      · rw [Finset.card_insert_of_notMem (fun h => hvA (hSsub h)), hcard]
  -- Hence every degree is exactly three, contradicting the handshake lemma on nine vertices.
  have hall : ∀ v : Fin 9, G.degree v = 3 := fun v => le_antisymm (hdeg_le v) (hdeg_ge v)
  have hsum : ∑ v : Fin 9, G.degree v = 2 * G.edgeFinset.card :=
    G.sum_degrees_eq_twice_card_edges
  rw [Finset.sum_congr rfl (fun v _ => hall v)] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega

end R34

/-! ## R(3,4) > 8 : the Wagner graph -/

section Wagner

/-- Adjacency relation of the Wagner graph (Möbius ladder `V₈`) on `Fin 8`:
`i ~ j` iff `j - i ∈ {1, 7, 4}` modulo `8`. -/
def wagnerAdj (i j : Fin 8) : Prop := j - i = 1 ∨ j - i = 7 ∨ j - i = 4

instance : DecidableRel wagnerAdj := fun i j => by unfold wagnerAdj; infer_instance

/-- The Wagner graph on `8` vertices: triangle-free with independence number `3`. -/
def wagner : SimpleGraph (Fin 8) where
  Adj := wagnerAdj
  symm := by intro a b; revert a b; decide
  loopless := ⟨by decide⟩

instance : DecidableRel wagner.Adj := fun i j => by
  change Decidable (wagnerAdj i j); infer_instance

set_option maxHeartbeats 1000000 in
lemma wagner_no_triangle : ¬ ∃ S : Finset (Fin 8), wagner.IsNClique 3 S := by decide

set_option maxHeartbeats 1000000 in
lemma wagner_no_indep4 : ¬ ∃ S : Finset (Fin 8), wagnerᶜ.IsNClique 4 S := by decide

lemma not_ramseyProp_eight : ¬ RamseyProp 8 3 4 := by
  intro H
  rcases H wagner with h | h
  · exact wagner_no_triangle h
  · exact wagner_no_indep4 h

end Wagner

/-! ## The main theorem -/

/-- The two-colour Ramsey number `R(3,4)` equals `9`. -/
theorem ramsey_3_4 : ramseyNumber 3 4 = 9 := by
  have h9 : (9 : ℕ) ∈ {n | RamseyProp n 3 4} := ramseyProp_nine
  apply le_antisymm (Nat.sInf_le h9)
  by_contra hlt
  push_neg at hlt
  have hmem : sInf {n | RamseyProp n 3 4} ∈ {n | RamseyProp n 3 4} := Nat.sInf_mem ⟨9, h9⟩
  exact not_ramseyProp_eight (ramseyProp_mono (by omega) hmem)

end Math

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

