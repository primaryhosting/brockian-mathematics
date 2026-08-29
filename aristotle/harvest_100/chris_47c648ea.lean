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

namespace Math

/-! ## The Ramsey property -/

/-- `RamseyProp n s t` says: every simple graph on `n` vertices contains either a clique of
size `s`, or an independent set of size `t` (a clique of size `t` in the complement).
Equivalently, every 2-colouring of the edges of `K n` has a red `K s` or a blue `K t`. -/
def RamseyProp (n s t : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n),
    (∃ S : Finset (Fin n), G.IsNClique s S) ∨ (∃ S : Finset (Fin n), Gᶜ.IsNClique t S)

/-! ## Generic tools -/

section Tools

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Neighbours of `v` inside `A`. -/
def nbrs (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (v : V) : Finset V :=
  (A.erase v).filter (fun u => G.Adj v u)

/-- Non-neighbours of `v` inside `A` (excluding `v` itself). -/
def nonnbrs (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (v : V) : Finset V :=
  (A.erase v).filter (fun u => ¬ G.Adj v u)

lemma nbrs_subset {A : Finset V} {v : V} : nbrs G A v ⊆ A := by
  intro x hx
  exact mem_of_mem_erase (mem_of_mem_filter x hx)

lemma nonnbrs_subset {A : Finset V} {v : V} : nonnbrs G A v ⊆ A := by
  intro x hx
  exact mem_of_mem_erase (mem_of_mem_filter x hx)

lemma card_split {A : Finset V} {v : V} (hv : v ∈ A) :
    A.card = 1 + (nbrs G A v).card + (nonnbrs G A v).card := by
  have h := Finset.card_filter_add_card_filter_not (s := A.erase v) (fun u => G.Adj v u)
  have h2 := Finset.card_erase_add_one hv
  simp only [nbrs, nonnbrs]
  omega

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Monotonicity of `CliqueFreeOn` in the vertex set. -/
lemma cliqueFreeOn_subset {K : SimpleGraph V} {A B : Finset V} {n : ℕ} (hBA : B ⊆ A)
    (h : K.CliqueFreeOn (↑A) n) : K.CliqueFreeOn (↑B) n := by
  intro t ht
  exact h (ht.trans (by exact_mod_cast hBA))

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- A clique which contains no `n`-clique has fewer than `n` elements. -/
lemma clique_card_lt {K : SimpleGraph V} {B : Finset V} {n : ℕ} (hC : K.IsClique (↑B))
    (h : K.CliqueFreeOn (↑B) n) : B.card < n := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨S, hSB, hS⟩ := Finset.exists_subset_card_eq hlt
  exact h (by exact_mod_cast hSB) ⟨hC.subset (by exact_mod_cast hSB), hS⟩

/-- If there is no independent pair inside `B`, then `B` is a clique. -/
lemma isClique_of_cliqueFreeOn_two {B : Finset V} (h : Gᶜ.CliqueFreeOn (↑B) 2) :
    G.IsClique (↑B) := by
  intro x hx y hy hxy
  by_contra hadj
  refine h (t := {x, y}) ?_ ?_
  · intro z hz
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> assumption
  · rw [SimpleGraph.isNClique_iff]
    constructor
    · intro a ha b hb hab
      simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      have : ∀ p q : V, p = x ∨ p = y → q = x ∨ q = y → p ≠ q → Gᶜ.Adj p q := by
        rintro p q (rfl | rfl) (rfl | rfl) hpq
        · exact absurd rfl hpq
        · exact ⟨hpq, hadj⟩
        · exact ⟨hpq, fun h' => hadj h'.symm⟩
        · exact absurd rfl hpq
      exact this a b ha hb hab
    · rw [Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]

/-- In a triangle-free graph, the neighbourhood of a vertex is independent. -/
lemma nbrs_isClique_compl {A : Finset V} {v : V} (hv : v ∈ A) (h3 : G.CliqueFreeOn (↑A) 3) :
    Gᶜ.IsClique (↑(nbrs G A v)) := by
  intro x hx y hy hxy
  simp only [mem_coe, nbrs, mem_filter, mem_erase] at hx hy
  refine ⟨hxy, ?_⟩
  intro hadj
  refine h3 (t := {v, x, y}) ?_ ?_
  · intro z hz
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hv
    · exact hx.1.2
    · exact hy.1.2
  · rw [SimpleGraph.is3Clique_triple_iff]
    exact ⟨hx.2, hy.2, hadj⟩

/-- The neighbourhood of a vertex in a triangle-free graph is small. -/
lemma nbrs_card_lt {A : Finset V} {v : V} {t : ℕ} (hv : v ∈ A) (h3 : G.CliqueFreeOn (↑A) 3)
    (ht : Gᶜ.CliqueFreeOn (↑A) t) : (nbrs G A v).card < t :=
  clique_card_lt (nbrs_isClique_compl hv h3) (cliqueFreeOn_subset nbrs_subset ht)

/-- Independent sets among the non-neighbours of `v` are one shorter. -/
lemma nonnbrs_cliqueFreeOn {A : Finset V} {v : V} {t : ℕ} (hv : v ∈ A)
    (ht : Gᶜ.CliqueFreeOn (↑A) (t + 1)) : Gᶜ.CliqueFreeOn (↑(nonnbrs G A v)) t := by
  intro S hS hSclique
  have hvS : v ∉ S := by
    intro hv'
    have := hS hv'
    simp only [mem_coe, nonnbrs, mem_filter, mem_erase] at this
    exact this.1.1 rfl
  have hadj : ∀ b ∈ S, Gᶜ.Adj v b := by
    intro b hb
    have := hS hb
    simp only [mem_coe, nonnbrs, mem_filter, mem_erase] at this
    exact ⟨fun h => this.1.1 h.symm, this.2⟩
  refine ht (t := insert v S) ?_ (hSclique.insert hadj)
  intro z hz
  simp only [coe_insert, Set.mem_insert_iff] at hz
  rcases hz with rfl | hz
  · exact hv
  · exact nonnbrs_subset (hS hz)

end Tools

/-! ## A parity lemma -/

section Parity

variable {V : Type*} [DecidableEq V]

lemma even_sum_symm (f : V → V → ℕ) (hs : ∀ x y, f x y = f y x) (hd : ∀ x, f x x = 0)
    (A : Finset V) : Even (∑ v ∈ A, ∑ u ∈ A, f v u) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha ih =>
      rw [Finset.sum_insert ha]
      have h1 : ∑ u ∈ insert a A, f a u = ∑ u ∈ A, f a u := by
        rw [Finset.sum_insert ha, hd a, zero_add]
      have h2 : ∀ v ∈ A, ∑ u ∈ insert a A, f v u = f v a + ∑ u ∈ A, f v u := by
        intro v _
        rw [Finset.sum_insert ha]
      rw [h1, Finset.sum_congr rfl h2, Finset.sum_add_distrib]
      have h3 : ∑ v ∈ A, f v a = ∑ u ∈ A, f a u := by
        exact Finset.sum_congr rfl (fun v _ => hs v a)
      rw [h3]
      have : ∑ u ∈ A, f a u + (∑ u ∈ A, f a u + ∑ v ∈ A, ∑ u ∈ A, f v u)
          = 2 * (∑ u ∈ A, f a u) + ∑ v ∈ A, ∑ u ∈ A, f v u := by ring
      rw [this]
      exact (even_two_mul _).add ih

variable {G : SimpleGraph V} [DecidableRel G.Adj]

lemma nbrs_eq_filter (A : Finset V) (v : V) : nbrs G A v = A.filter (fun u => G.Adj v u) := by
  ext u
  simp only [nbrs, mem_filter, mem_erase]
  constructor
  · rintro ⟨⟨-, hu⟩, h⟩; exact ⟨hu, h⟩
  · rintro ⟨hu, h⟩
    refine ⟨⟨?_, hu⟩, h⟩
    rintro rfl
    exact G.irrefl h

lemma even_sum_nbrs (A : Finset V) : Even (∑ v ∈ A, (nbrs G A v).card) := by
  have key : ∀ v ∈ A, (nbrs G A v).card = ∑ u ∈ A, (if G.Adj v u then 1 else 0) := by
    intro v _
    rw [nbrs_eq_filter, Finset.card_filter]
  rw [Finset.sum_congr rfl key]
  refine even_sum_symm (fun x y => if G.Adj x y then 1 else 0) (fun x y => ?_)
    (fun x => ?_) A
  · simp [SimpleGraph.adj_comm]
  · simp

end Parity

/-! ## The upper bound `R(3,5) ≤ 14` -/

section Upper

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma ramsey_33 {A : Finset V} (h3 : G.CliqueFreeOn (↑A) 3) (h3' : Gᶜ.CliqueFreeOn (↑A) 3) :
    A.card ≤ 5 := by
  by_contra hc
  push_neg at hc
  obtain ⟨v, hv⟩ : ∃ v, v ∈ A := Finset.card_pos.mp (by omega)
  have h1 : (nbrs G A v).card < 3 := nbrs_card_lt hv h3 h3'
  have h2 : Gᶜ.CliqueFreeOn (↑(nonnbrs G A v)) 2 := nonnbrs_cliqueFreeOn hv h3'
  have h4 : (nonnbrs G A v).card < 3 :=
    clique_card_lt (isClique_of_cliqueFreeOn_two h2) (cliqueFreeOn_subset nonnbrs_subset h3)
  have h5 := card_split (G := G) hv
  omega

lemma ramsey_34 {A : Finset V} (h3 : G.CliqueFreeOn (↑A) 3) (h4 : Gᶜ.CliqueFreeOn (↑A) 4) :
    A.card ≤ 8 := by
  by_contra hc
  push_neg at hc
  obtain ⟨B, hBA, hB9⟩ := Finset.exists_subset_card_eq (show 9 ≤ A.card by omega)
  have h3B : G.CliqueFreeOn (↑B) 3 := cliqueFreeOn_subset hBA h3
  have h4B : Gᶜ.CliqueFreeOn (↑B) 4 := cliqueFreeOn_subset hBA h4
  have hdeg : ∀ v ∈ B, (nbrs G B v).card = 3 := by
    intro v hv
    have h1 : (nbrs G B v).card < 4 := nbrs_card_lt hv h3B h4B
    have h2 : Gᶜ.CliqueFreeOn (↑(nonnbrs G B v)) 3 := nonnbrs_cliqueFreeOn hv h4B
    have h5 : (nonnbrs G B v).card ≤ 5 :=
      ramsey_33 (cliqueFreeOn_subset nonnbrs_subset h3B) h2
    have h6 := card_split (G := G) hv
    omega
  have hsum : ∑ v ∈ B, (nbrs G B v).card = 27 := by
    rw [Finset.sum_congr rfl hdeg, Finset.sum_const, hB9]
    rfl
  have heven := even_sum_nbrs (G := G) B
  rw [hsum] at heven
  exact (by decide : ¬ Even 27) heven

lemma ramsey_35 {A : Finset V} (h3 : G.CliqueFreeOn (↑A) 3) (h5 : Gᶜ.CliqueFreeOn (↑A) 5) :
    A.card ≤ 13 := by
  by_contra hc
  push_neg at hc
  obtain ⟨v, hv⟩ : ∃ v, v ∈ A := Finset.card_pos.mp (by omega)
  have h1 : (nbrs G A v).card < 5 := nbrs_card_lt hv h3 h5
  have h2 : Gᶜ.CliqueFreeOn (↑(nonnbrs G A v)) 4 := nonnbrs_cliqueFreeOn hv h5
  have h4 : (nonnbrs G A v).card ≤ 8 :=
    ramsey_34 (cliqueFreeOn_subset nonnbrs_subset h3) h2
  have h6 := card_split (G := G) hv
  omega

end Upper

theorem ramseyProp_14 : RamseyProp 14 3 5 := by
  classical
  intro G
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have h3 : G.CliqueFreeOn (↑(Finset.univ : Finset (Fin 14))) 3 := fun t _ ht => h1 t ht
  have h5 : Gᶜ.CliqueFreeOn (↑(Finset.univ : Finset (Fin 14))) 5 := fun t _ ht => h2 t ht
  have h := ramsey_35 h3 h5
  simp at h

/-! ## The lower bound: a `(3,5)`-graph on 13 vertices -/

/-- Adjacency of the circulant graph `C₁₃(1,5)`. -/
def hb (i j : Fin 13) : Bool :=
  let d := (i.val + 13 - j.val) % 13
  d == 1 || d == 5 || d == 8 || d == 12

/-- The circulant graph on `ZMod 13` with connection set `{±1, ±5}`: it is triangle-free and
its independence number is 4, so it witnesses `R(3,5) > 13`. -/
def H : SimpleGraph (Fin 13) where
  Adj i j := hb i j = true
  symm := by intro i j; revert i j; decide
  loopless := ⟨by decide⟩

instance : DecidableRel H.Adj := fun i j => inferInstanceAs (Decidable (hb i j = true))

set_option maxRecDepth 40000 in
theorem no_tri : ∀ a b c : Fin 13, hb a b = true → hb b c = true → hb a c = true → False := by
  decide

set_option maxRecDepth 40000 in
theorem no_indep5 : ∀ a b : Fin 13, a < b → hb a b = false →
    ∀ c : Fin 13, b < c → hb a c = false → hb b c = false →
    ∀ d : Fin 13, c < d → hb a d = false → hb b d = false → hb c d = false →
    ∀ e : Fin 13, d < e → hb a e = false → hb b e = false → hb c e = false → hb d e = false →
    False := by
  decide

theorem H_triangle_free : ∀ S : Finset (Fin 13), ¬ H.IsNClique 3 S := by
  intro S hS
  rw [SimpleGraph.is3Clique_iff] at hS
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := hS
  exact no_tri a b c hab hbc hac

theorem H_no_indep_five : ∀ S : Finset (Fin 13), ¬ Hᶜ.IsNClique 5 S := by
  rintro S ⟨hclique, hcard⟩
  have hnadj : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → hb x y = false := by
    intro x hx y hy hxy
    have := hclique (by exact_mod_cast hx) (by exact_mod_cast hy) hxy
    rw [SimpleGraph.compl_adj] at this
    simpa [H] using this.2
  have hlen : (S.sort (· ≤ ·)).length = 5 := by rw [Finset.length_sort, hcard]
  have hpair : (S.sort (· ≤ ·)).Pairwise (· < ·) :=
    List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort S)
  have hmem : ∀ x, x ∈ S.sort (· ≤ ·) → x ∈ S := fun x hx => (Finset.mem_sort _).mp hx
  match hl : S.sort (· ≤ ·), hlen, hpair, hmem with
  | [a, b, c, d, e], _, hp, hm =>
      simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true] at hp
      have ha : a ∈ S := hm a (by simp)
      have hbS : b ∈ S := hm b (by simp)
      have hcS : c ∈ S := hm c (by simp)
      have hdS : d ∈ S := hm d (by simp)
      have heS : e ∈ S := hm e (by simp)
      obtain ⟨⟨hab, hac, had, hae⟩, ⟨hbc, hbd, hbe⟩, ⟨hcd, hce⟩, hde, -⟩ := hp
      exact no_indep5 a b hab (hnadj a ha b hbS (ne_of_lt hab))
        c hbc (hnadj a ha c hcS (ne_of_lt hac)) (hnadj b hbS c hcS (ne_of_lt hbc))
        d hcd (hnadj a ha d hdS (ne_of_lt had)) (hnadj b hbS d hdS (ne_of_lt hbd))
        (hnadj c hcS d hdS (ne_of_lt hcd))
        e hde (hnadj a ha e heS (ne_of_lt hae)) (hnadj b hbS e heS (ne_of_lt hbe))
        (hnadj c hcS e heS (ne_of_lt hce)) (hnadj d hdS e heS (ne_of_lt hde))

/-- Cliques transfer along an injective map by taking images. -/
lemma isNClique_image {W : Type*} {n : ℕ} (f : W → Fin 13) (hf : Function.Injective f)
    (K : SimpleGraph (Fin 13)) {S : Finset W} (h : (K.comap f).IsNClique n S) :
    K.IsNClique n (S.image f) := by
  obtain ⟨hcl, hc⟩ := h
  constructor
  · rintro x hx y hy hxy
    simp only [coe_image, Set.mem_image, mem_coe] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact hcl ha hb (fun h => hxy (by rw [h]))
  · rw [Finset.card_image_of_injective _ hf, hc]

theorem not_ramseyProp_of_le_13 {n : ℕ} (hn : n ≤ 13) : ¬ RamseyProp n 3 5 := by
  intro hR
  set f : Fin n → Fin 13 := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hn⟩ with hf
  have hfinj : Function.Injective f := by
    intro x y hxy
    simp only [hf, Fin.mk.injEq] at hxy
    exact Fin.ext hxy
  rcases hR (H.comap f) with ⟨S, hS⟩ | ⟨S, hS⟩
  · exact H_triangle_free _ (isNClique_image f hfinj H hS)
  · refine H_no_indep_five (S.image f) (isNClique_image f hfinj Hᶜ ?_)
    refine hS.mono ?_
    intro x y hxy
    exact ⟨fun h => hxy.1 (hfinj h), hxy.2⟩

/-- **R(3,5) = 14**. -/
theorem ramsey_3_5 : IsLeast {n | RamseyProp n 3 5} 14 := by
  constructor
  · exact ramseyProp_14
  · intro n hn
    by_contra h
    exact not_ramseyProp_of_le_13 (by omega) hn

end Math

