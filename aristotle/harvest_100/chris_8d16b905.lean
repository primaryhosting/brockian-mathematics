import Mathlib
import RequestProject.Paley

/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open Finset

/-! ## Monochromatic cliques for a two-colouring -/

variable {α : Type*} [DecidableEq α] {c : α → α → Bool} {x : Bool}

/-- `S` is a monochromatic clique of colour `x` for the two-colouring `c`. -/
def MonoClique (c : α → α → Bool) (x : Bool) (S : Finset α) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c i j = x

omit [DecidableEq α] in
lemma monoClique_not {S : Finset α} :
    MonoClique (fun i j => !(c i j)) x S ↔ MonoClique c (!x) S := by
  constructor
  · intro h i hi j hj hij
    have h' : (!(c i j)) = x := h i hi j hj hij
    rw [← h', Bool.not_not]
  · intro h i hi j hj hij
    have h' : c i j = !x := h i hi j hj hij
    show (!(c i j)) = x
    rw [h', Bool.not_not]

lemma monoClique_triple {v i j : α} (hsym : ∀ a b, c a b = c b a)
    (hvi : c v i = x) (hvj : c v j = x) (hij : c i j = x) :
    MonoClique c x ({v, i, j} : Finset α) := by
  have hiv : c i v = x := by rw [hsym]; exact hvi
  have hjv : c j v = x := by rw [hsym]; exact hvj
  have hji : c j i = x := by rw [hsym]; exact hij
  intro a ha b hb hab
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first
      | exact absurd rfl hab
      | assumption

lemma monoClique_insert {S : Finset α} {v : α} (hsym : ∀ a b, c a b = c b a)
    (hS : MonoClique c x S) (hv : ∀ u ∈ S, c v u = x) :
    MonoClique c x (insert v S) := by
  intro a ha b hb hab
  simp only [Finset.mem_insert] at ha hb
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact hv b hb
  · rcases hb with rfl | hb
    · rw [hsym]; exact hv a ha
    · exact hS a ha b hb hab

/-! ## Neighbourhoods -/

/-- The vertices of `V` joined to `v` by colour `true`. -/
def redN (c : α → α → Bool) (V : Finset α) (v : α) : Finset α :=
  (V.erase v).filter (fun u => c v u = true)

/-- The vertices of `V` joined to `v` by colour `false`. -/
def blueN (c : α → α → Bool) (V : Finset α) (v : α) : Finset α :=
  (V.erase v).filter (fun u => c v u = false)

lemma redN_subset {V : Finset α} {v : α} : redN c V v ⊆ V.erase v :=
  Finset.filter_subset _ _

lemma blueN_subset {V : Finset α} {v : α} : blueN c V v ⊆ V.erase v :=
  Finset.filter_subset _ _

lemma mem_redN {V : Finset α} {v u : α} : u ∈ redN c V v ↔ (u ∈ V ∧ u ≠ v) ∧ c v u = true := by
  simp [redN, Finset.mem_filter, Finset.mem_erase, and_comm]

lemma mem_blueN {V : Finset α} {v u : α} : u ∈ blueN c V v ↔ (u ∈ V ∧ u ≠ v) ∧ c v u = false := by
  simp [blueN, Finset.mem_filter, Finset.mem_erase, and_comm]

lemma card_redN_add_card_blueN {V : Finset α} {v : α} (hv : v ∈ V) :
    (redN c V v).card + (blueN c V v).card = V.card - 1 := by
  have hb : blueN c V v = (V.erase v).filter (fun u => ¬ (c v u = true)) := by
    unfold blueN
    refine Finset.filter_congr ?_
    intro u _
    simp
  rw [redN, hb, Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hv]

/-! ## The key colour-extension step -/

lemma key_red {V : Finset α} {v : α} (hv : v ∈ V) (hsym : ∀ a b, c a b = c b a)
    {T : Finset α} (hT : T ⊆ redN c V v) :
    (∃ S ⊆ V, S.card = 3 ∧ MonoClique c true S) ∨ MonoClique c false T := by
  by_cases hc : ∃ i ∈ T, ∃ j ∈ T, i ≠ j ∧ c i j = true
  · obtain ⟨i, hi, j, hj, hij, hcij⟩ := hc
    have hi' := mem_redN.1 (hT hi)
    have hj' := mem_redN.1 (hT hj)
    refine Or.inl ⟨{v, i, j}, ?_, ?_, monoClique_triple hsym hi'.2 hj'.2 hcij⟩
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact hv
      · exact hi'.1.1
      · exact hj'.1.1
    · exact Finset.card_eq_three.2 ⟨v, i, j, (hi'.1.2).symm, (hj'.1.2).symm, hij, rfl⟩
  · push_neg at hc
    exact Or.inr fun i hi j hj hij => by simpa using hc i hi j hj hij

lemma key_blue {V : Finset α} {v : α} (hv : v ∈ V) (hsym : ∀ a b, c a b = c b a)
    {T : Finset α} (hT : T ⊆ blueN c V v) :
    (∃ S ⊆ V, S.card = 3 ∧ MonoClique c false S) ∨ MonoClique c true T := by
  by_cases hc : ∃ i ∈ T, ∃ j ∈ T, i ≠ j ∧ c i j = false
  · obtain ⟨i, hi, j, hj, hij, hcij⟩ := hc
    have hi' := mem_blueN.1 (hT hi)
    have hj' := mem_blueN.1 (hT hj)
    refine Or.inl ⟨{v, i, j}, ?_, ?_, monoClique_triple hsym hi'.2 hj'.2 hcij⟩
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact hv
      · exact hi'.1.1
      · exact hj'.1.1
    · exact Finset.card_eq_three.2 ⟨v, i, j, (hi'.1.2).symm, (hj'.1.2).symm, hij, rfl⟩
  · push_neg at hc
    exact Or.inr fun i hi j hj hij => by simpa using hc i hi j hj hij

/-! ## Handshake -/

lemma even_sum_redDeg (hsym : ∀ a b, c a b = c b a) (W : Finset α) :
    Even (∑ v ∈ W, (redN c W v).card) := by
  classical
  set f : α × α → ZMod 2 := fun p => if p.2 ≠ p.1 ∧ c p.1 p.2 = true then 1 else 0 with hf
  have hswap : ∀ p : α × α, f (p.2, p.1) = f p := by
    intro p
    have hcond : (p.1 ≠ p.2 ∧ c p.2 p.1 = true) ↔ (p.2 ≠ p.1 ∧ c p.1 p.2 = true) := by
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1.symm, by rw [hsym]; exact h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1.symm, by rw [hsym]; exact h2⟩
    simp only [hf]
    exact if_congr hcond rfl rfl
  have hzero : ∑ p ∈ W ×ˢ W, f p = 0 := by
    refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p _
      rw [hswap p]
      exact CharTwo.add_self_eq_zero (f p)
    · intro p _ hfp hpe
      apply hfp
      have h12 : p.1 = p.2 := congrArg Prod.fst hpe.symm ▸ rfl
      simp only [hf]
      rw [if_neg]
      rintro ⟨h1, -⟩
      exact h1 h12.symm
    · intro p hp
      simp only [Finset.mem_product] at hp ⊢
      exact ⟨hp.2, hp.1⟩
    · intro p _
      rfl
  have hcast : ((∑ v ∈ W, (redN c W v).card : ℕ) : ZMod 2) = 0 := by
    rw [← hzero, Finset.sum_product]
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro v _
    have hset : redN c W v = W.filter (fun u => u ≠ v ∧ c v u = true) := by
      ext u
      simp only [mem_redN, Finset.mem_filter]
      tauto
    rw [hset, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro u _
    simp only [hf]
    split <;> simp
  exact ZMod.natCast_eq_zero_iff_even.mp hcast

/-! ## R(3,3) ≤ 6 -/

lemma ramsey_3_3 (hsym : ∀ a b, c a b = c b a) {V : Finset α} (hV : 6 ≤ V.card) :
    ∃ S ⊆ V, S.card = 3 ∧ (MonoClique c true S ∨ MonoClique c false S) := by
  obtain ⟨W, hWV, hW⟩ := Finset.exists_subset_card_eq hV
  have hne : W.Nonempty := by
    rw [← Finset.card_pos, hW]; norm_num
  obtain ⟨v, hvW⟩ := hne
  have hsplit := card_redN_add_card_blueN (c := c) hvW
  rw [hW] at hsplit
  by_cases h : 3 ≤ (redN c W v).card
  · obtain ⟨T, hTsub, hT3⟩ := Finset.exists_subset_card_eq h
    have hTW : T ⊆ W := hTsub.trans (redN_subset.trans (Finset.erase_subset _ _))
    rcases key_red hvW hsym hTsub with ⟨S, hSW, hS3, hS⟩ | hTm
    · exact ⟨S, hSW.trans hWV, hS3, Or.inl hS⟩
    · exact ⟨T, hTW.trans hWV, hT3, Or.inr hTm⟩
  · have hb : 3 ≤ (blueN c W v).card := by omega
    obtain ⟨T, hTsub, hT3⟩ := Finset.exists_subset_card_eq hb
    have hTW : T ⊆ W := hTsub.trans (blueN_subset.trans (Finset.erase_subset _ _))
    rcases key_blue hvW hsym hTsub with ⟨S, hSW, hS3, hS⟩ | hTm
    · exact ⟨S, hSW.trans hWV, hS3, Or.inr hS⟩
    · exact ⟨T, hTW.trans hWV, hT3, Or.inl hTm⟩

/-! ## R(3,4) ≤ 9 -/

lemma ramsey_3_4 (hsym : ∀ a b, c a b = c b a) {V : Finset α} (hV : 9 ≤ V.card) :
    (∃ S ⊆ V, S.card = 3 ∧ MonoClique c true S) ∨
      (∃ S ⊆ V, S.card = 4 ∧ MonoClique c false S) := by
  obtain ⟨W, hWV, hW⟩ := Finset.exists_subset_card_eq hV
  by_contra hcon
  push_neg at hcon
  obtain ⟨h3, h4⟩ := hcon
  have key3 : ∀ S ⊆ W, S.card = 3 → ¬ MonoClique c true S := fun S hS => h3 S (hS.trans hWV)
  have key4 : ∀ S ⊆ W, S.card = 4 → ¬ MonoClique c false S := fun S hS => h4 S (hS.trans hWV)
  have hdeg : ∀ v ∈ W, (redN c W v).card = 3 := by
    intro v hv
    have hsplit := card_redN_add_card_blueN (c := c) hv
    rw [hW] at hsplit
    have hle : (redN c W v).card ≤ 3 := by
      by_contra hgt
      obtain ⟨T, hTsub, hT4⟩ := Finset.exists_subset_card_eq
        (show 4 ≤ (redN c W v).card by omega)
      rcases key_red hv hsym hTsub with ⟨S, hSW, hS3, hS⟩ | hTm
      · exact key3 S hSW hS3 hS
      · exact key4 T (hTsub.trans (redN_subset.trans (Finset.erase_subset _ _))) hT4 hTm
    have hge : 3 ≤ (redN c W v).card := by
      by_contra hlt
      obtain ⟨B, hBsub, hB6⟩ := Finset.exists_subset_card_eq
        (show 6 ≤ (blueN c W v).card by omega)
      have hBW : B ⊆ W := hBsub.trans (blueN_subset.trans (Finset.erase_subset _ _))
      obtain ⟨S, hSB, hS3, hS⟩ := ramsey_3_3 (c := c) hsym hB6.ge
      rcases hS with hS | hS
      · exact key3 S (hSB.trans hBW) hS3 hS
      · have hvS : v ∉ S := fun hvS =>
          (Finset.mem_erase.1 (blueN_subset (hBsub (hSB hvS)))).1 rfl
        refine key4 (insert v S) (Finset.insert_subset hv (hSB.trans hBW)) ?_
          (monoClique_insert hsym hS (fun u hu => (mem_blueN.1 (hBsub (hSB hu))).2))
        rw [Finset.card_insert_of_notMem hvS, hS3]
    omega
  have hsum : ∑ v ∈ W, (redN c W v).card = 27 := by
    rw [Finset.sum_congr rfl hdeg, Finset.sum_const, hW]
    norm_num
  have heven := even_sum_redDeg (c := c) hsym W
  rw [hsum] at heven
  exact (by decide : ¬ Even 27) heven

lemma ramsey_4_3 (hsym : ∀ a b, c a b = c b a) {V : Finset α} (hV : 9 ≤ V.card) :
    (∃ S ⊆ V, S.card = 4 ∧ MonoClique c true S) ∨
      (∃ S ⊆ V, S.card = 3 ∧ MonoClique c false S) := by
  have hsym' : ∀ a b, (fun i j => !(c i j)) a b = (fun i j => !(c i j)) b a := by
    intro a b; simp only []; rw [hsym a b]
  rcases ramsey_3_4 (c := fun i j => !(c i j)) hsym' hV with ⟨S, hS, h3, hm⟩ | ⟨S, hS, h4, hm⟩
  · exact Or.inr ⟨S, hS, h3, by simpa using (monoClique_not (c := c) (x := true)).1 hm⟩
  · exact Or.inl ⟨S, hS, h4, by simpa using (monoClique_not (c := c) (x := false)).1 hm⟩

/-! ## R(4,4) ≤ 18 -/

lemma ramsey_4_4_upper (hsym : ∀ a b, c a b = c b a) {V : Finset α} (hV : 18 ≤ V.card) :
    ∃ S ⊆ V, S.card = 4 ∧ (MonoClique c true S ∨ MonoClique c false S) := by
  obtain ⟨W, hWV, hW⟩ := Finset.exists_subset_card_eq hV
  have hne : W.Nonempty := by
    rw [← Finset.card_pos, hW]; norm_num
  obtain ⟨v, hvW⟩ := hne
  have hsplit := card_redN_add_card_blueN (c := c) hvW
  rw [hW] at hsplit
  by_cases h : 9 ≤ (redN c W v).card
  · obtain ⟨T, hTsub, hT9⟩ := Finset.exists_subset_card_eq h
    have hTW : T ⊆ W := hTsub.trans (redN_subset.trans (Finset.erase_subset _ _))
    rcases ramsey_3_4 (c := c) hsym hT9.ge with ⟨S, hST, hS3, hS⟩ | ⟨S, hST, hS4, hS⟩
    · have hvS : v ∉ S := fun hvS => (Finset.mem_erase.1 (redN_subset (hTsub (hST hvS)))).1 rfl
      refine ⟨insert v S, Finset.insert_subset (hWV hvW) ((hST.trans hTW).trans hWV), ?_,
        Or.inl (monoClique_insert hsym hS (fun u hu => (mem_redN.1 (hTsub (hST hu))).2))⟩
      rw [Finset.card_insert_of_notMem hvS, hS3]
    · exact ⟨S, (hST.trans hTW).trans hWV, hS4, Or.inr hS⟩
  · obtain ⟨T, hTsub, hT9⟩ := Finset.exists_subset_card_eq
      (show 9 ≤ (blueN c W v).card by omega)
    have hTW : T ⊆ W := hTsub.trans (blueN_subset.trans (Finset.erase_subset _ _))
    rcases ramsey_4_3 (c := c) hsym hT9.ge with ⟨S, hST, hS4, hS⟩ | ⟨S, hST, hS3, hS⟩
    · exact ⟨S, (hST.trans hTW).trans hWV, hS4, Or.inl hS⟩
    · have hvS : v ∉ S := fun hvS => (Finset.mem_erase.1 (blueN_subset (hTsub (hST hvS)))).1 rfl
      refine ⟨insert v S, Finset.insert_subset (hWV hvW) ((hST.trans hTW).trans hWV), ?_,
        Or.inr (monoClique_insert hsym hS (fun u hu => (mem_blueN.1 (hTsub (hST hu))).2))⟩
      rw [Finset.card_insert_of_notMem hvS, hS3]

/-! ## The Ramsey property and the main theorem -/

/-- Every symmetric two-colouring of the edges of the complete graph on `n` vertices
contains a monochromatic clique on `4` vertices. -/
def RamseyProp (n : ℕ) : Prop :=
  ∀ c : Fin n → Fin n → Bool, (∀ i j, c i j = c j i) →
    ∃ S : Finset (Fin n), S.card = 4 ∧ (MonoClique c true S ∨ MonoClique c false S)

lemma ramseyProp_18 : RamseyProp 18 := by
  intro c hsym
  obtain ⟨S, -, hS4, hS⟩ := ramsey_4_4_upper (c := c) hsym
    (V := (Finset.univ : Finset (Fin 18))) (by simp)
  exact ⟨S, hS4, hS⟩

lemma not_ramseyProp_of_le_17 {n : ℕ} (hn : n ≤ 17) : ¬ RamseyProp n := by
  intro hR
  set emb : Fin n → Fin 17 := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hn⟩ with hemb
  have hembinj : Function.Injective emb := by
    intro i j hij
    apply Fin.ext
    simpa [hemb, Fin.ext_iff] using hij
  obtain ⟨S, hS4, hS⟩ := hR (fun i j => paley (emb i) (emb j)) (fun i j => paley_symm _ _)
  obtain ⟨a, b, d, e, hab, had, hae, hbd, hbe, hde, rfl⟩ := Finset.card_eq_four.1 hS4
  have ha : a ∈ ({a, b, d, e} : Finset (Fin n)) := by simp
  have hb : b ∈ ({a, b, d, e} : Finset (Fin n)) := by simp
  have hd : d ∈ ({a, b, d, e} : Finset (Fin n)) := by simp
  have he : e ∈ ({a, b, d, e} : Finset (Fin n)) := by simp
  refine paley_no_mono (emb a) (emb b) (emb d) (emb e)
    (fun h => hab (hembinj h)) (fun h => had (hembinj h)) (fun h => hae (hembinj h))
    (fun h => hbd (hembinj h)) (fun h => hbe (hembinj h)) (fun h => hde (hembinj h)) ?_
  rcases hS with hm | hm
  · have e1 : paley (emb a) (emb b) = true := hm _ ha _ hb hab
    have e2 : paley (emb a) (emb d) = true := hm _ ha _ hd had
    have e3 : paley (emb a) (emb e) = true := hm _ ha _ he hae
    have e4 : paley (emb b) (emb d) = true := hm _ hb _ hd hbd
    have e5 : paley (emb b) (emb e) = true := hm _ hb _ he hbe
    have e6 : paley (emb d) (emb e) = true := hm _ hd _ he hde
    exact ⟨e1.trans e2.symm, e2.trans e3.symm, e3.trans e4.symm, e4.trans e5.symm,
      e5.trans e6.symm⟩
  · have e1 : paley (emb a) (emb b) = false := hm _ ha _ hb hab
    have e2 : paley (emb a) (emb d) = false := hm _ ha _ hd had
    have e3 : paley (emb a) (emb e) = false := hm _ ha _ he hae
    have e4 : paley (emb b) (emb d) = false := hm _ hb _ hd hbd
    have e5 : paley (emb b) (emb e) = false := hm _ hb _ he hbe
    have e6 : paley (emb d) (emb e) = false := hm _ hd _ he hde
    exact ⟨e1.trans e2.symm, e2.trans e3.symm, e3.trans e4.symm, e4.trans e5.symm,
      e5.trans e6.symm⟩

/-- **The Ramsey number `R(4,4)` equals `18`.** -/
theorem ramsey_4_4 : IsLeast {n | RamseyProp n} 18 := by
  refine ⟨ramseyProp_18, ?_⟩
  intro n hn
  by_contra h
  exact not_ramseyProp_of_le_17 (by omega) hn

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

import Mathlib

/-!
# The Paley two-colouring on 17 vertices

This file contains the explicit two-colouring of the complete graph on `17` vertices
witnessing `R(4,4) > 17`: two vertices `i j : Fin 17` get colour `true` exactly when their
difference `j - i` (mod 17) is a nonzero quadratic residue mod 17.
-/

namespace Math

/-! ## The Paley colouring of `Fin 17` -/

/-- Membership test for the nonzero quadratic residues mod `17`. -/
def isQR (n : ℕ) : Bool :=
  n == 1 || n == 2 || n == 4 || n == 8 || n == 9 || n == 13 || n == 15 || n == 16

/-- The Paley two-colouring of the complete graph on 17 vertices. -/
def paley (i j : Fin 17) : Bool := isQR ((j.val + 17 - i.val) % 17)

lemma paley_symm : ∀ i j : Fin 17, paley i j = paley j i := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma paley_no_mono (a b d e : Fin 17) (hab : a ≠ b) (had : a ≠ d) (hae : a ≠ e)
    (hbd : b ≠ d) (hbe : b ≠ e) (hde : d ≠ e) :
    ¬ (paley a b = paley a d ∧ paley a d = paley a e ∧ paley a e = paley b d ∧
        paley b d = paley b e ∧ paley b e = paley d e) := by
  revert a b d e
  decide


end Math

