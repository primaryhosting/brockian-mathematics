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

We define the two-colour Ramsey number `Math.ramseyNumber` and prove `R(3,4) = 9`.
-/

open Finset SimpleGraph

namespace Math

/-- `Arrows n r s` says that every simple graph on `n` vertices contains either a clique of
size `r` or an independent set of size `s`, i.e. `n → (r, s)` in Ramsey arrow notation. -/
def Arrows (n r s : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n),
    (∃ A : Finset (Fin n), G.IsNClique r A) ∨ (∃ B : Finset (Fin n), G.IsNIndepSet s B)

/-- The two-colour Ramsey number `R(r, s)`: the least `n` such that every graph on `n`
vertices contains an `r`-clique or an `s`-element independent set. -/
noncomputable def ramseyNumber (r s : ℕ) : ℕ := sInf {n | Arrows n r s}

/-! ### Transfer along embeddings and monotonicity -/

theorem isNClique_map_comap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph β) (f : α ↪ β) {r : ℕ} {A : Finset α}
    (h : (G.comap f).IsNClique r A) : G.IsNClique r (A.map f) := by
  refine ⟨?_, by simpa using h.card_eq⟩
  intro x hx y hy hxy
  simp only [coe_map, Set.mem_image, mem_coe] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact h.isClique (mem_coe.mpr ha) (mem_coe.mpr hb) (fun hab => hxy (by rw [hab]))

theorem isNIndepSet_map_comap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph β) (f : α ↪ β) {s : ℕ} {B : Finset α}
    (h : (G.comap f).IsNIndepSet s B) : G.IsNIndepSet s (B.map f) := by
  refine ⟨?_, by simpa using h.card_eq⟩
  intro x hx y hy hxy
  simp only [coe_map, Set.mem_image, mem_coe] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact h.isIndepSet (mem_coe.mpr ha) (mem_coe.mpr hb) (fun hab => hxy (by rw [hab]))

theorem arrows_mono {m n r s : ℕ} (hmn : m ≤ n) (h : Arrows m r s) : Arrows n r s := by
  intro G
  rcases h (G.comap (Fin.castLEEmb hmn)) with ⟨A, hA⟩ | ⟨B, hB⟩
  · exact Or.inl ⟨A.map (Fin.castLEEmb hmn), isNClique_map_comap G _ hA⟩
  · exact Or.inr ⟨B.map (Fin.castLEEmb hmn), isNIndepSet_map_comap G _ hB⟩

/-! ### Small constructions of independent sets -/

theorem isNIndepSet_triple {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (nab : ¬ G.Adj a b) (nac : ¬ G.Adj a c) (nbc : ¬ G.Adj b c) :
    G.IsNIndepSet 3 ({a, b, c} : Finset V) := by
  refine ⟨?_, by simp [hab, hac, hbc]⟩
  intro x hx y hy hxy
  simp only [coe_insert, Set.mem_insert_iff, coe_singleton, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    first
      | exact absurd rfl hxy
      | exact nab
      | exact nac
      | exact nbc
      | exact fun h => nab h.symm
      | exact fun h => nac h.symm
      | exact fun h => nbc h.symm

theorem isNIndepSet_insert {V : Type*} [DecidableEq V] {G : SimpleGraph V} {n : ℕ} {v : V}
    {T : Finset V} (hv : v ∉ T) (hadj : ∀ t ∈ T, ¬ G.Adj v t) (hT : G.IsNIndepSet n T) :
    G.IsNIndepSet (n + 1) (insert v T) := by
  refine ⟨?_, by rw [card_insert_of_notMem hv, hT.card_eq]⟩
  rw [coe_insert]
  refine (Set.pairwise_insert_of_symmetric ?_).2 ⟨hT.isIndepSet, ?_⟩
  · intro x y hxy hyx
    exact hxy hyx.symm
  · intro b hb _
    exact hadj b hb

/-! ### Every triangle-free graph on six vertices has an independent set of size three -/

theorem exists_isNIndepSet_three {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (h3 : ∀ A : Finset V, ¬ G.IsNClique 3 A) (S : Finset V) (hS : 6 ≤ S.card) :
    ∃ T ⊆ S, G.IsNIndepSet 3 T := by
  classical
  obtain ⟨u, hu⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  have hcard : 5 ≤ (S.erase u).card := by
    rw [Finset.card_erase_of_mem hu]; omega
  set N := (S.erase u).filter (fun x => G.Adj u x) with hNdef
  set M := (S.erase u).filter (fun x => ¬ G.Adj u x) with hMdef
  have hsplit : N.card + M.card = (S.erase u).card :=
    Finset.card_filter_add_card_filter_not _
  by_cases hN3 : 3 ≤ N.card
  · obtain ⟨T, hTN, hTcard⟩ := Finset.exists_subset_card_eq hN3
    have hTS : T ⊆ S := fun x hx =>
      Finset.mem_of_mem_erase (Finset.mem_of_mem_filter x (hTN hx))
    refine ⟨T, hTS, ?_, hTcard⟩
    intro x hx y hy hxy hadj
    have hux : G.Adj u x := (Finset.mem_filter.mp (hTN hx)).2
    have huy : G.Adj u y := (Finset.mem_filter.mp (hTN hy)).2
    exact h3 {u, x, y} (is3Clique_triple_iff.mpr ⟨hux, huy, hadj⟩)
  · have hM3 : 3 ≤ M.card := by omega
    obtain ⟨T, hTM, hTcard⟩ := Finset.exists_subset_card_eq hM3
    have hTS : T ⊆ S := fun x hx =>
      Finset.mem_of_mem_erase (Finset.mem_of_mem_filter x (hTM hx))
    by_cases hclq : G.IsClique (T : Set V)
    · exact absurd ⟨hclq, hTcard⟩ (h3 T)
    · rw [SimpleGraph.isClique_iff, Set.Pairwise] at hclq
      push_neg at hclq
      obtain ⟨x, hx, y, hy, hxy, hnadj⟩ := hclq
      have hxT : x ∈ T := hx
      have hyT : y ∈ T := hy
      have hux : ¬ G.Adj u x := (Finset.mem_filter.mp (hTM hxT)).2
      have huy : ¬ G.Adj u y := (Finset.mem_filter.mp (hTM hyT)).2
      have hxu : x ≠ u := Finset.ne_of_mem_erase (Finset.mem_of_mem_filter x (hTM hxT))
      have hyu : y ≠ u := Finset.ne_of_mem_erase (Finset.mem_of_mem_filter y (hTM hyT))
      refine ⟨{u, x, y}, ?_, isNIndepSet_triple (Ne.symm hxu) (Ne.symm hyu) hxy hux huy hnadj⟩
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact hu
      · exact hTS hxT
      · exact hTS hyT

/-! ### The upper bound: `9 → (3, 4)` -/

theorem arrows_nine : Arrows 9 3 4 := by
  classical
  intro G
  by_contra hcon
  push_neg at hcon
  obtain ⟨hcl, hind⟩ := hcon
  have hcf : G.CliqueFree 3 := hcl
  -- No vertex has degree at least four.
  have hdeg_le : ∀ v, G.degree v ≤ 3 := by
    intro v
    by_contra hlt
    push_neg at hlt
    have h4 : 4 ≤ (G.neighborFinset v).card := by
      rw [card_neighborFinset_eq_degree]; omega
    obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq h4
    refine hind T ⟨?_, hTcard⟩
    refine Set.Pairwise.mono ?_ (G.isIndepSet_neighborSet_of_triangleFree hcf v)
    intro x hx
    exact (mem_neighborFinset _ _ _).mp (hT hx)
  -- No vertex has degree at most two.
  have hdeg_ge : ∀ v, 3 ≤ G.degree v := by
    intro v
    by_contra hlt
    push_neg at hlt
    set S : Finset (Fin 9) := Finset.univ \ insert v (G.neighborFinset v) with hSdef
    have hins : (insert v (G.neighborFinset v)).card ≤ 3 := by
      have h1 := Finset.card_insert_le v (G.neighborFinset v)
      rw [card_neighborFinset_eq_degree] at h1
      omega
    have hScard : 6 ≤ S.card := by
      have h3 : S.card = 9 - (insert v (G.neighborFinset v)).card := by
        rw [hSdef, Finset.card_univ_diff]
        simp
      omega
    obtain ⟨T, hTS, hT3⟩ := exists_isNIndepSet_three G hcl S hScard
    have hvT : v ∉ T := by
      intro hv
      have := hTS hv
      rw [hSdef, Finset.mem_sdiff] at this
      exact this.2 (Finset.mem_insert_self _ _)
    have hadj : ∀ t ∈ T, ¬ G.Adj v t := by
      intro t ht hadj
      have := hTS ht
      rw [hSdef, Finset.mem_sdiff] at this
      exact this.2 (Finset.mem_insert_of_mem ((mem_neighborFinset _ _ _).mpr hadj))
    exact hind _ (isNIndepSet_insert hvT hadj hT3)
  -- Hence `G` is 3-regular on 9 vertices, contradicting the handshake lemma.
  have hreg : ∀ v, G.degree v = 3 := fun v => le_antisymm (hdeg_le v) (hdeg_ge v)
  have hsum := G.sum_degrees_eq_twice_card_edges
  rw [Finset.sum_congr rfl (fun v _ => hreg v)] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega

/-! ### The lower bound: the Wagner graph on eight vertices -/

/-- The circulant graph `C₈(1,4)` (the Wagner graph): it is triangle-free and has
independence number three. -/
def wagner : SimpleGraph (Fin 8) where
  Adj i j := (i - j : Fin 8) = 1 ∨ (i - j : Fin 8) = 4 ∨ (i - j : Fin 8) = 7
  symm := fun {i j} => by revert i j; decide
  loopless := ⟨by decide⟩

instance : DecidableRel wagner.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

set_option maxRecDepth 10000 in
theorem wagner_no_triangle : ¬ ∃ A : Finset (Fin 8), wagner.IsNClique 3 A := by
  simp only [isNClique_iff, not_exists, not_and]
  decide

set_option maxRecDepth 40000 in
theorem wagner_no_indep_four : ¬ ∃ B : Finset (Fin 8), wagner.IsNIndepSet 4 B := by
  simp only [isNIndepSet_iff, not_exists, not_and]
  decide

theorem not_arrows_eight : ¬ Arrows 8 3 4 := by
  intro h
  rcases h wagner with hA | hB
  · exact wagner_no_triangle hA
  · exact wagner_no_indep_four hB

/-! ### The Ramsey number -/

/-- **R(3,4) = 9.** -/
theorem ramsey_3_4 : ramseyNumber 3 4 = 9 := by
  show sInf {n | Arrows n 3 4} = 9
  have h9 : (9 : ℕ) ∈ {n | Arrows n 3 4} := arrows_nine
  refine le_antisymm (Nat.sInf_le h9) ?_
  by_contra hlt
  push_neg at hlt
  have hmem := Nat.sInf_mem (⟨9, h9⟩ : {n | Arrows n 3 4}.Nonempty)
  exact not_arrows_eight (arrows_mono (by omega : sInf {n | Arrows n 3 4} ≤ 8) hmem)

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

