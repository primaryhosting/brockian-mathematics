/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` to be the first command; the header above is repeated below
-- as a module docstring.)

import Mathlib

/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math

open Finset

/-! ## Generalities on monochromatic cliques -/

section General

variable {V : Type*} [LinearOrder V] {G : SimpleGraph V}

/-- The set of vertices of `W` adjacent to `v` in `G`. -/
noncomputable def nbr (G : SimpleGraph V) (v : V) (W : Finset V) : Finset V := W.filter (fun w => G.Adj v w)

omit [LinearOrder V] in
lemma mem_nbr {v w : V} {W : Finset V} : w ∈ nbr G v W ↔ w ∈ W ∧ G.Adj v w := by
  simp [nbr]

omit [LinearOrder V] in
lemma nbr_subset (G : SimpleGraph V) (v : V) (W : Finset V) : nbr G v W ⊆ W :=
  Finset.filter_subset _ _

lemma card_nbr_add_card_nbr_compl {v : V} {W : Finset V} (hv : v ∈ W) :
    (nbr G v W).card + (nbr Gᶜ v W).card = W.card - 1 := by
  have h1 : nbr G v W = (W.erase v).filter (fun w => G.Adj v w) := by
    ext w
    simp only [mem_nbr, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hw, hadj⟩; exact ⟨⟨(G.ne_of_adj hadj).symm, hw⟩, hadj⟩
    · rintro ⟨⟨_, hw⟩, hadj⟩; exact ⟨hw, hadj⟩
  have h2 : nbr Gᶜ v W = (W.erase v).filter (fun w => ¬ G.Adj v w) := by
    ext w
    simp only [mem_nbr, Finset.mem_filter, Finset.mem_erase, SimpleGraph.compl_adj]
    constructor
    · rintro ⟨hw, hne, hadj⟩; exact ⟨⟨fun h => hne h.symm, hw⟩, hadj⟩
    · rintro ⟨⟨hne, hw⟩, hadj⟩; exact ⟨hw, fun h => hne h.symm, hadj⟩
  rw [h1, h2, Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hv]

/-- `Mono G r s W` : the subset `W` contains an `r`-clique of `G` or an `s`-clique of `Gᶜ`. -/
def Mono (G : SimpleGraph V) (r s : ℕ) (W : Finset V) : Prop :=
  (∃ t ⊆ W, G.IsNClique r t) ∨ (∃ t ⊆ W, Gᶜ.IsNClique s t)

omit [LinearOrder V] in
lemma Mono.subset {r s : ℕ} {W W' : Finset V} (h : Mono G r s W) (hsub : W ⊆ W') :
    Mono G r s W' := by
  rcases h with ⟨t, ht, hc⟩ | ⟨t, ht, hc⟩
  · exact Or.inl ⟨t, ht.trans hsub, hc⟩
  · exact Or.inr ⟨t, ht.trans hsub, hc⟩

/-- A clique inside the neighbourhood of `v` extends by `v`. -/
lemma extend {k : ℕ} {v : V} {W t : Finset V} (hv : v ∈ W) (ht : t ⊆ nbr G v W)
    (hc : G.IsNClique k t) : ∃ u ⊆ W, G.IsNClique (k + 1) u := by
  refine ⟨insert v t, ?_, hc.insert ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hv
    · exact nbr_subset G v W (ht hx)
  · intro b hb
    exact (mem_nbr.mp (ht hb)).2

/-- If `A` has at least `s` elements then either it contains an edge of `G`,
or an `s`-clique of `Gᶜ`. -/
lemma mono_two {s : ℕ} {A : Finset V} (h : s ≤ A.card) : Mono G 2 s A := by
  by_cases hred : ∃ x ∈ A, ∃ y ∈ A, G.Adj x y
  · obtain ⟨x, hx, y, hy, hxy⟩ := hred
    refine Or.inl ⟨{x, y}, ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hx
      · rw [Finset.mem_singleton] at hz; subst hz; exact hy
    · refine ⟨?_, ?_⟩
      · intro a ha b hb hab
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all [G.symm hxy]
      · exact Finset.card_pair (G.ne_of_adj hxy)
  · push_neg at hred
    obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq h
    refine Or.inr ⟨t, ht, ⟨?_, htc⟩⟩
    intro a ha b hb hab
    refine ⟨hab, hred a (ht ha) b (ht hb)⟩

/-- R(3,3) ≤ 6. -/
lemma mono_three_three {W : Finset V} (h : 6 ≤ W.card) : Mono G 3 3 W := by
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < W.card by omega)
  have hsplit := card_nbr_add_card_nbr_compl (G := G) hv
  by_cases ha : 3 ≤ (nbr G v W).card
  · rcases mono_two (G := G) (s := 3) ha with ⟨t, ht, hc⟩ | ⟨t, ht, hc⟩
    · exact Or.inl (extend hv ht hc)
    · exact Or.inr ⟨t, ht.trans (nbr_subset _ _ _), hc⟩
  · have hb : 3 ≤ (nbr Gᶜ v W).card := by omega
    rcases mono_two (G := Gᶜ) (s := 3) hb with ⟨t, ht, hc⟩ | ⟨t, ht, hc⟩
    · exact Or.inr (extend (G := Gᶜ) hv ht hc)
    · rw [compl_compl] at hc
      exact Or.inl ⟨t, ht.trans (nbr_subset _ _ _), hc⟩

/-- Handshake lemma, relative to a finite set of vertices. -/
lemma even_sum_nbr_card (G : SimpleGraph V) (W : Finset V) :
    Even (∑ v ∈ W, (nbr G v W).card) := by
  refine ⟨∑ v ∈ W, ∑ w ∈ W, (if G.Adj v w ∧ v < w then 1 else 0), ?_⟩
  have h1 : ∑ v ∈ W, (nbr G v W).card
      = (∑ v ∈ W, ∑ w ∈ W, (if G.Adj v w ∧ v < w then 1 else 0))
        + ∑ v ∈ W, ∑ w ∈ W, (if G.Adj v w ∧ w < v then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [nbr, Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    by_cases hadj : G.Adj v w
    · rcases lt_or_gt_of_ne (G.ne_of_adj hadj) with hlt | hlt
      · simp [hadj, hlt, asymm hlt]
      · simp [hadj, hlt, asymm hlt]
    · simp [hadj]
  have h2 : (∑ v ∈ W, ∑ w ∈ W, (if G.Adj v w ∧ w < v then 1 else 0))
      = ∑ v ∈ W, ∑ w ∈ W, (if G.Adj v w ∧ v < w then 1 else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [G.adj_comm y x]
  rw [h1, h2]

/-- R(3,4) ≤ 9. -/
lemma mono_three_four {W : Finset V} (h : 9 ≤ W.card) : Mono G 3 4 W := by
  obtain ⟨W', hsub, hcard⟩ := Finset.exists_subset_card_eq h
  suffices hM : Mono G 3 4 W' from hM.subset hsub
  by_contra hcon
  rw [Mono, not_or] at hcon
  obtain ⟨hno3, hno4⟩ := hcon
  push_neg at hno3 hno4
  have hdeg : ∀ v ∈ W', (nbr G v W').card = 3 := by
    intro v hv
    have hsplit := card_nbr_add_card_nbr_compl (G := G) hv
    have ha : (nbr G v W').card ≤ 3 := by
      by_contra hgt
      push_neg at hgt
      rcases mono_two (G := G) (s := 4) hgt with ⟨t, ht, hc⟩ | ⟨t, ht, hc⟩
      · obtain ⟨u, hu, hcu⟩ := extend hv ht hc
        exact hno3 u hu hcu
      · exact hno4 t (ht.trans (nbr_subset _ _ _)) hc
    have hb : (nbr Gᶜ v W').card ≤ 5 := by
      by_contra hgt
      push_neg at hgt
      rcases mono_three_three (G := Gᶜ) hgt with ⟨t, ht, hc⟩ | ⟨t, ht, hc⟩
      · obtain ⟨u, hu, hcu⟩ := extend (G := Gᶜ) hv ht hc
        exact hno4 u hu hcu
      · rw [compl_compl] at hc
        exact hno3 t (ht.trans (nbr_subset _ _ _)) hc
    omega
  have hsum : ∑ v ∈ W', (nbr G v W').card = 27 := by
    rw [Finset.sum_congr rfl hdeg, Finset.sum_const, hcard, smul_eq_mul]
  have heven := even_sum_nbr_card G W'
  rw [hsum, Nat.even_iff] at heven
  omega

/-- R(4,4) ≤ 18. -/
lemma mono_four_four {W : Finset V} (h : 18 ≤ W.card) : Mono G 4 4 W := by
  obtain ⟨W', hsub, hcard⟩ := Finset.exists_subset_card_eq h
  suffices hM : Mono G 4 4 W' from hM.subset hsub
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < W'.card by omega)
  have hsplit := card_nbr_add_card_nbr_compl (G := G) hv
  by_cases ha : 9 ≤ (nbr G v W').card
  · rcases mono_three_four (G := G) ha with ⟨t, ht, hc⟩ | ⟨t, ht, hc⟩
    · exact Or.inl (extend hv ht hc)
    · exact Or.inr ⟨t, ht.trans (nbr_subset _ _ _), hc⟩
  · have hb : 9 ≤ (nbr Gᶜ v W').card := by omega
    rcases mono_three_four (G := Gᶜ) hb with ⟨t, ht, hc⟩ | ⟨t, ht, hc⟩
    · exact Or.inr (extend (G := Gᶜ) hv ht hc)
    · rw [compl_compl] at hc
      exact Or.inl ⟨t, ht.trans (nbr_subset _ _ _), hc⟩

end General

/-! ## The Ramsey property -/

/-- `RamseyProp n` says that every 2-colouring of the edges of the complete graph on `n`
vertices (encoded as a simple graph `G`, the edges of `G` being the "red" ones) contains a
monochromatic clique on 4 vertices. -/
def RamseyProp (n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree 4 ∨ ¬ Gᶜ.CliqueFree 4

/-! ### Upper bound: every 2-colouring of `K₁₈` has a monochromatic `K₄`. -/

theorem ramseyProp_18 : RamseyProp 18 := by
  intro G
  have h : Mono G 4 4 (Finset.univ : Finset (Fin 18)) := by
    apply mono_four_four
    simp
  rcases h with ⟨t, _, hc⟩ | ⟨t, _, hc⟩
  · exact Or.inl (fun hfree => hfree t hc)
  · exact Or.inr (fun hfree => hfree t hc)

/-! ### Lower bound: the Paley graph on 17 vertices. -/

/-- The nonzero quadratic residues modulo `17`. -/
def QR : Finset (Fin 17) := {1, 2, 4, 8, 9, 13, 15, 16}

/-- The Paley graph on `17` vertices. -/
def paley : SimpleGraph (Fin 17) where
  Adj x y := (x - y) ∈ QR
  symm := by intro x y h; revert h; revert x y; decide
  loopless := ⟨by decide⟩

instance : DecidableRel paley.Adj := fun x y => by
  simp only [paley]; infer_instance

instance : DecidableRel paleyᶜ.Adj := fun x y => by
  simp only [SimpleGraph.compl_adj]; infer_instance

theorem cliqueFree_four_of {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (h : ∀ a b c d : V, G.Adj a b → G.Adj a c → G.Adj a d → G.Adj b c → G.Adj b d → G.Adj c d →
      False) : G.CliqueFree 4 := by
  intro t ht
  obtain ⟨hclique, hcard⟩ := ht
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < t.card by omega)
  have h3 : (t.erase a).card = 3 := by rw [Finset.card_erase_of_mem ha, hcard]
  obtain ⟨b, c, d, hbc, hbd, hcd, he⟩ := Finset.card_eq_three.mp h3
  have hb : b ∈ t.erase a := by rw [he]; simp
  have hc : c ∈ t.erase a := by rw [he]; simp
  have hd : d ∈ t.erase a := by rw [he]; simp
  exact h a b c d (hclique ha (Finset.mem_of_mem_erase hb)
      (fun h => (Finset.ne_of_mem_erase hb) h.symm))
    (hclique ha (Finset.mem_of_mem_erase hc) (fun h => (Finset.ne_of_mem_erase hc) h.symm))
    (hclique ha (Finset.mem_of_mem_erase hd) (fun h => (Finset.ne_of_mem_erase hd) h.symm))
    (hclique (Finset.mem_of_mem_erase hb) (Finset.mem_of_mem_erase hc) hbc)
    (hclique (Finset.mem_of_mem_erase hb) (Finset.mem_of_mem_erase hd) hbd)
    (hclique (Finset.mem_of_mem_erase hc) (Finset.mem_of_mem_erase hd) hcd)

theorem paley_cliqueFree : paley.CliqueFree 4 := by
  refine cliqueFree_four_of _ ?_
  decide

theorem paley_compl_cliqueFree : paleyᶜ.CliqueFree 4 := by
  refine cliqueFree_four_of _ ?_
  decide

theorem not_ramseyProp_17 : ¬ RamseyProp 17 := by
  intro h
  rcases h paley with h | h
  · exact h paley_cliqueFree
  · exact h paley_compl_cliqueFree

/-- Cliques transfer along injective pullbacks. -/
lemma isNClique_map_comap {m n k : ℕ} (f : Fin n → Fin m) (hf : Function.Injective f)
    {G : SimpleGraph (Fin m)} {t : Finset (Fin n)} (ht : (G.comap f).IsNClique k t) :
    G.IsNClique k (t.image f) := by
  obtain ⟨hclique, hcard⟩ := ht
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact hclique ha hb (fun h => hxy (by rw [h]))
  · rw [Finset.card_image_of_injective _ hf, hcard]

lemma compl_comap {m n : ℕ} (f : Fin n → Fin m) (hf : Function.Injective f)
    (G : SimpleGraph (Fin m)) : (G.comap f)ᶜ = Gᶜ.comap f := by
  ext a b
  simp only [SimpleGraph.compl_adj, SimpleGraph.comap_adj]
  exact ⟨fun ⟨h1, h2⟩ => ⟨fun h => h1 (hf h), h2⟩, fun ⟨h1, h2⟩ => ⟨fun h => h1 (by rw [h]), h2⟩⟩

/-- The Ramsey property is monotone in the number of vertices. -/
lemma ramseyProp_mono {n m : ℕ} (hnm : n ≤ m) (h : RamseyProp n) : RamseyProp m := by
  intro G
  have hf : Function.Injective (Fin.castLE hnm) := Fin.castLE_injective hnm
  rcases h (G.comap (Fin.castLE hnm)) with hcase | hcase
  · rw [SimpleGraph.CliqueFree] at hcase
    push_neg at hcase
    obtain ⟨t, ht⟩ := hcase
    exact Or.inl (fun hfree => hfree _ (isNClique_map_comap _ hf ht))
  · rw [compl_comap _ hf, SimpleGraph.CliqueFree] at hcase
    push_neg at hcase
    obtain ⟨t, ht⟩ := hcase
    exact Or.inr (fun hfree => hfree _ (isNClique_map_comap _ hf ht))

/-! ## The Ramsey number `R(4,4) = 18` -/

theorem ramsey_4_4_isLeast : IsLeast {n : ℕ | RamseyProp n} 18 := by
  refine ⟨ramseyProp_18, ?_⟩
  intro n hn
  by_contra hlt
  push_neg at hlt
  exact not_ramseyProp_17 (ramseyProp_mono (by omega) hn)

/-- **R(4,4) = 18**: the least `n` such that every red/blue colouring of the edges of the
complete graph on `n` vertices contains a monochromatic clique on 4 vertices is `18`. -/
theorem ramsey_4_4 : sInf {n : ℕ | RamseyProp n} = 18 :=
  ramsey_4_4_isLeast.csInf_eq

end Math

