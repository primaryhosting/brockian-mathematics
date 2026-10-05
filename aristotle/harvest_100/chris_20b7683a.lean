/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 4 4

We show that the two-colour Ramsey number `R(4,4)` equals `18`:

* every symmetric two-colouring of the edges of the complete graph on `18` vertices
  contains a monochromatic set of `4` vertices;
* there is a symmetric two-colouring of the edges of the complete graph on `17` vertices
  (the Paley graph of order `17`) with no monochromatic set of `4` vertices.
-/

namespace Math

open Finset

/-- `MonoSet f b S` says that every pair of distinct vertices of `S` receives colour `b`. -/
def MonoSet {V : Type*} (f : V → V → Bool) (b : Bool) (S : Finset V) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → f i j = b

/-- `RamseyProp N` says that every symmetric two-colouring of the edges of the complete
graph on `N` vertices contains a monochromatic clique on `4` vertices. -/
def RamseyProp (N : ℕ) : Prop :=
  ∀ f : Fin N → Fin N → Bool, (∀ i j, f i j = f j i) →
    ∃ S : Finset (Fin N), S.card = 4 ∧ (MonoSet f true S ∨ MonoSet f false S)

section General

variable {V : Type*} [DecidableEq V] {f : V → V → Bool}

/-- The set of neighbours of `v` inside `W` joined to `v` by an edge of colour `b`. -/
def nbr (f : V → V → Bool) (b : Bool) (W : Finset V) (v : V) : Finset V :=
  {u ∈ W.erase v | f v u = b}

lemma mem_nbr {b : Bool} {W : Finset V} {v u : V} :
    u ∈ nbr f b W v ↔ (u ∈ W ∧ u ≠ v ∧ f v u = b) := by
  simp [nbr, Finset.mem_erase, and_assoc, and_comm]

lemma nbr_subset {b : Bool} {W : Finset V} {v : V} : nbr f b W v ⊆ W := fun _ hu =>
  (mem_nbr.mp hu).1

/-- Every vertex of `W` has `W.card - 1` neighbours in `W`, split by colour. -/
lemma card_nbr_add {W : Finset V} {v : V} (hv : v ∈ W) :
    (nbr f true W v).card + (nbr f false W v).card + 1 = W.card := by
  have h2 : nbr f false W v = {u ∈ W.erase v | ¬ (f v u = true)} := by
    apply Finset.filter_congr
    intro u _
    simp
  have h1 := Finset.card_filter_add_card_filter_not (s := W.erase v) (p := fun u => f v u = true)
  rw [nbr, h2, h1, Finset.card_erase_of_mem hv]
  have : 1 ≤ W.card := Finset.card_pos.mpr ⟨v, hv⟩
  omega

/-- Adding `v` to a `b`-monochromatic subset of its `b`-neighbourhood keeps it
`b`-monochromatic. -/
lemma mono_insert (hsym : ∀ x y, f x y = f y x) {b : Bool} {W S : Finset V} {v : V}
    (hv : v ∈ W) (hS : S ⊆ nbr f b W v) (hm : MonoSet f b S) :
    insert v S ⊆ W ∧ (insert v S).card = S.card + 1 ∧ MonoSet f b (insert v S) := by
  have hvS : v ∉ S := fun h => (mem_nbr.mp (hS h)).2.1 rfl
  refine ⟨?_, Finset.card_insert_of_notMem hvS, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hv
    · exact nbr_subset (hS hx)
  · intro i hi j hj hij
    rcases Finset.mem_insert.mp hi with hi | hi <;> rcases Finset.mem_insert.mp hj with hj | hj
    · exact absurd (hi.trans hj.symm) hij
    · rw [hi]; exact (mem_nbr.mp (hS hj)).2.2
    · rw [hj, hsym]; exact (mem_nbr.mp (hS hi)).2.2
    · exact hm i hi j hj hij

/-- Either `A` contains an edge of colour `b`, or any `n` of its vertices form a
`!b`-monochromatic set. -/
lemma pair_or_mono {b : Bool} {A : Finset V} {n : ℕ} (h : n ≤ A.card) :
    (∃ i ∈ A, ∃ j ∈ A, i ≠ j ∧ f i j = b) ∨ (∃ S ⊆ A, S.card = n ∧ MonoSet f (!b) S) := by
  by_cases hp : ∃ i ∈ A, ∃ j ∈ A, i ≠ j ∧ f i j = b
  · exact Or.inl hp
  · right
    push_neg at hp
    obtain ⟨S, hSA, hS⟩ := Finset.le_card_iff_exists_subset_card.mp h
    refine ⟨S, hSA, hS, fun i hi j hj hij => ?_⟩
    have := hp i (hSA hi) j (hSA hj) hij
    cases hb : f i j <;> cases b <;> simp_all

lemma mono_pair (hsym : ∀ x y, f x y = f y x) {b : Bool} {i j : V} (h : f i j = b) :
    MonoSet f b ({i, j} : Finset V) := by
  intro x hx y hy hxy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · exact h
  · rw [hsym]; exact h
  · exact absurd rfl hxy

omit [DecidableEq V] in
lemma mono_or {b : Bool} {S : Finset V} (h : MonoSet f b S) :
    MonoSet f true S ∨ MonoSet f false S := by
  cases b
  · exact Or.inr h
  · exact Or.inl h

omit [DecidableEq V] in
lemma mono_flip {b : Bool} {S : Finset V} :
    MonoSet (fun i j => !f i j) b S ↔ MonoSet f (!b) S := by
  have key : ∀ x y : Bool, ((!x) = y) ↔ (x = !y) := by decide
  constructor <;> intro h i hi j hj hij
  · exact (key _ _).mp (h i hi j hj hij)
  · exact (key _ _).mpr (h i hi j hj hij)

/-- Handshake lemma: the sum over `W` of the number of `true`-neighbours in `W` is even. -/
lemma even_sum_deg [LinearOrder V] (hsym : ∀ x y, f x y = f y x) (W : Finset V) :
    Even (∑ v ∈ W, (nbr f true W v).card) := by
  classical
  set P : Finset (V × V) := {p ∈ W ×ˢ W | p.1 ≠ p.2 ∧ f p.1 p.2 = true} with hP
  have hnb : ∀ v, nbr f true W v = {u ∈ W | v ≠ u ∧ f v u = true} := by
    intro v
    ext u
    simp only [nbr, Finset.mem_filter, Finset.mem_erase]
    tauto
  have key : ∑ v ∈ W, (nbr f true W v).card = P.card := by
    rw [hP, Finset.card_filter, Finset.sum_product]
    exact Finset.sum_congr rfl fun v _ => by rw [hnb v, Finset.card_filter]
  have hsplit := Finset.card_filter_add_card_filter_not (s := P) (p := fun p : V × V => p.1 < p.2)
  have hmemP : ∀ p : V × V, p ∈ P ↔ (p.1 ∈ W ∧ p.2 ∈ W ∧ p.1 ≠ p.2 ∧ f p.1 p.2 = true) := by
    intro p
    simp only [hP, Finset.mem_filter, Finset.mem_product]
    tauto
  have hbij : ({p ∈ P | p.1 < p.2}).card = ({p ∈ P | ¬ p.1 < p.2}).card := by
    refine Finset.card_bij' (fun p _ => (p.2, p.1)) (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, hmemP] at hp ⊢
      obtain ⟨⟨h1, h2, hne, hf⟩, hlt⟩ := hp
      exact ⟨⟨h2, h1, hne.symm, by rw [hsym]; exact hf⟩, by simpa using le_of_lt hlt⟩
    · intro p hp
      simp only [Finset.mem_filter, hmemP] at hp ⊢
      obtain ⟨⟨h1, h2, hne, hf⟩, hlt⟩ := hp
      exact ⟨⟨h2, h1, hne.symm, by rw [hsym]; exact hf⟩,
        lt_of_le_of_ne (not_lt.mp hlt) hne.symm⟩
    · intro p _; rfl
    · intro p _; rfl
  have hP2 : P.card = 2 * ({p ∈ P | p.1 < p.2}).card := by omega
  rw [key, hP2]
  exact even_two_mul _

/-- If some vertex `v` of `W` has at least three `b`-coloured neighbours in `W`, then `W`
contains a monochromatic triangle. -/
lemma triple_of_three (hsym : ∀ x y, f x y = f y x) {W : Finset V} {v : V} {b : Bool}
    (hv : v ∈ W) (h : 3 ≤ (nbr f b W v).card) :
    ∃ S ⊆ W, S.card = 3 ∧ (MonoSet f true S ∨ MonoSet f false S) := by
  rcases pair_or_mono (b := b) (n := 3) h with ⟨i, hi, j, hj, hij, hfij⟩ | ⟨S, hSA, hc, hm⟩
  · obtain ⟨h1, h2, h3⟩ := mono_insert hsym hv
      (Finset.insert_subset hi (Finset.singleton_subset_iff.mpr hj)) (mono_pair hsym hfij)
    exact ⟨insert v {i, j}, h1, by rw [h2, Finset.card_pair hij], mono_or h3⟩
  · exact ⟨S, hSA.trans nbr_subset, hc, mono_or hm⟩

/-- `R(3,3) ≤ 6`. -/
lemma ramsey_33 (hsym : ∀ x y, f x y = f y x) (W : Finset V) (hW : 6 ≤ W.card) :
    ∃ S ⊆ W, S.card = 3 ∧ (MonoSet f true S ∨ MonoSet f false S) := by
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < W.card by omega)
  have h := card_nbr_add (f := f) hv
  rcases (show 3 ≤ (nbr f true W v).card ∨ 3 ≤ (nbr f false W v).card by omega) with h3 | h3
  · exact triple_of_three hsym hv h3
  · exact triple_of_three hsym hv h3

/-- `R(3,4) ≤ 9`. -/
lemma ramsey_34 [LinearOrder V] (hsym : ∀ x y, f x y = f y x) (W : Finset V) (hW : 9 ≤ W.card) :
    ∃ S ⊆ W, (S.card = 3 ∧ MonoSet f true S) ∨ (S.card = 4 ∧ MonoSet f false S) := by
  obtain ⟨W', hW'W, hW'⟩ := Finset.le_card_iff_exists_subset_card.mp hW
  suffices h : ∃ S ⊆ W', (S.card = 3 ∧ MonoSet f true S) ∨ (S.card = 4 ∧ MonoSet f false S) by
    obtain ⟨S, hS, h⟩ := h
    exact ⟨S, hS.trans hW'W, h⟩
  by_contra hcon
  have hno : ∀ S, S ⊆ W' →
      ¬((S.card = 3 ∧ MonoSet f true S) ∨ (S.card = 4 ∧ MonoSet f false S)) :=
    fun S hS h => hcon ⟨S, hS, h⟩
  -- no vertex has four `true`-neighbours
  have hv3 : ∀ v ∈ W', (nbr f true W' v).card ≤ 3 := by
    intro v hv
    by_contra hgt
    push_neg at hgt
    rcases pair_or_mono (b := true) (n := 4) (show 4 ≤ (nbr f true W' v).card by omega) with
      ⟨i, hi, j, hj, hij, hfij⟩ | ⟨S, hSA, hc, hm⟩
    · obtain ⟨h1, h2, h3⟩ := mono_insert hsym hv
        (Finset.insert_subset hi (Finset.singleton_subset_iff.mpr hj)) (mono_pair hsym hfij)
      exact hno _ h1 (Or.inl ⟨by rw [h2, Finset.card_pair hij], h3⟩)
    · exact hno S (hSA.trans nbr_subset) (Or.inr ⟨hc, hm⟩)
  -- no vertex has six `false`-neighbours
  have hv5 : ∀ v ∈ W', (nbr f false W' v).card ≤ 5 := by
    intro v hv
    by_contra hgt
    push_neg at hgt
    obtain ⟨S, hSA, hc, hm⟩ := ramsey_33 hsym (nbr f false W' v) (by omega)
    rcases hm with hm | hm
    · exact hno S (hSA.trans nbr_subset) (Or.inl ⟨hc, hm⟩)
    · obtain ⟨h1, h2, h3⟩ := mono_insert hsym hv hSA hm
      exact hno _ h1 (Or.inr ⟨by rw [h2, hc], h3⟩)
  -- hence the `true` graph is 3-regular on nine vertices, contradicting the handshake lemma
  have hdeg : ∀ v ∈ W', (nbr f true W' v).card = 3 := by
    intro v hv
    have h := card_nbr_add (f := f) hv
    have h3 := hv3 v hv
    have h5 := hv5 v hv
    omega
  have hsum : ∑ v ∈ W', (nbr f true W' v).card = 27 := by
    rw [Finset.sum_congr rfl hdeg]
    simp [hW']
  have heven := even_sum_deg hsym W'
  rw [hsum] at heven
  exact (by decide : ¬ Even 27) heven

/-- `R(4,3) ≤ 9`. -/
lemma ramsey_43 [LinearOrder V] (hsym : ∀ x y, f x y = f y x) (W : Finset V) (hW : 9 ≤ W.card) :
    ∃ S ⊆ W, (S.card = 4 ∧ MonoSet f true S) ∨ (S.card = 3 ∧ MonoSet f false S) := by
  have hsym' : ∀ x y, (!f x y) = (!f y x) := fun x y => by rw [hsym]
  obtain ⟨S, hSW, h⟩ := ramsey_34 (f := fun i j => !f i j) hsym' W hW
  refine ⟨S, hSW, ?_⟩
  rcases h with ⟨hc, hm⟩ | ⟨hc, hm⟩
  · exact Or.inr ⟨hc, mono_flip.mp hm⟩
  · exact Or.inl ⟨hc, mono_flip.mp hm⟩

/-- `R(4,4) ≤ 18`. -/
lemma ramsey_44_le [LinearOrder V] (hsym : ∀ x y, f x y = f y x) (W : Finset V)
    (hW : 18 ≤ W.card) : ∃ S ⊆ W, S.card = 4 ∧ (MonoSet f true S ∨ MonoSet f false S) := by
  obtain ⟨W', hW'W, hW'⟩ := Finset.le_card_iff_exists_subset_card.mp hW
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < W'.card by omega)
  have hc := card_nbr_add (f := f) hv
  rcases (show 9 ≤ (nbr f true W' v).card ∨ 9 ≤ (nbr f false W' v).card by omega) with h9 | h9
  · obtain ⟨S, hSA, h⟩ := ramsey_34 hsym (nbr f true W' v) h9
    rcases h with ⟨hcard, hm⟩ | ⟨hcard, hm⟩
    · obtain ⟨h1, h2, h3⟩ := mono_insert hsym hv hSA hm
      exact ⟨insert v S, h1.trans hW'W, by rw [h2, hcard], Or.inl h3⟩
    · exact ⟨S, (hSA.trans nbr_subset).trans hW'W, hcard, Or.inr hm⟩
  · obtain ⟨S, hSA, h⟩ := ramsey_43 hsym (nbr f false W' v) h9
    rcases h with ⟨hcard, hm⟩ | ⟨hcard, hm⟩
    · exact ⟨S, (hSA.trans nbr_subset).trans hW'W, hcard, Or.inl hm⟩
    · obtain ⟨h1, h2, h3⟩ := mono_insert hsym hv hSA hm
      exact ⟨insert v S, h1.trans hW'W, by rw [h2, hcard], Or.inr h3⟩

end General

/-! ### The lower bound: the Paley graph of order 17 -/

/-- `qr n` decides whether `n % 17` is a nonzero quadratic residue modulo `17`.
The residues are `1, 2, 4, 8, 9, 13, 15, 16`, encoded as the bit mask `107286`. -/
def qr (n : ℕ) : Bool := (107286 >>> (n % 17)) % 2 == 1

/-- The Paley colouring on `Fin 17`: the edge `{i, j}` is `true` exactly when `j - i` is a
nonzero quadratic residue modulo `17`. -/
def paleyColor (i j : Fin 17) : Bool := qr (j.val + 17 - i.val)

lemma paley_symm : ∀ i j : Fin 17, paleyColor i j = paleyColor j i := by decide

set_option maxRecDepth 100000 in
/-- No four vertices of the Paley graph of order `17` are monochromatic. -/
theorem paley_no_mono4 : ∀ a b c d : Fin 17, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ∀ col : Bool, ¬(paleyColor a b = col ∧ paleyColor a c = col ∧ paleyColor a d = col ∧
      paleyColor b c = col ∧ paleyColor b d = col ∧ paleyColor c d = col) := by
  decide +kernel

lemma exists_four_of_card_eq_four {V : Type*} [DecidableEq V] {S : Finset V} (h : S.card = 4) :
    ∃ a b c d, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ S = {a, b, c, d} := by
  obtain ⟨a, t, hat, rfl, ht⟩ := Finset.card_eq_succ.mp h
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp ht
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hat
  exact ⟨a, x, y, z, hat.1, hat.2.1, hat.2.2, hxy, hxz, hyz, rfl⟩

/-- The Paley colouring of `K₁₇` has no monochromatic set of four vertices. -/
lemma paley_no_mono_finset {S : Finset (Fin 17)} (h : S.card = 4) (col : Bool) :
    ¬ MonoSet paleyColor col S := by
  intro hm
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := exists_four_of_card_eq_four h
  have ha : a ∈ ({a, b, c, d} : Finset (Fin 17)) := by simp
  have hb : b ∈ ({a, b, c, d} : Finset (Fin 17)) := by simp
  have hc : c ∈ ({a, b, c, d} : Finset (Fin 17)) := by simp
  have hd : d ∈ ({a, b, c, d} : Finset (Fin 17)) := by simp
  exact paley_no_mono4 a b c d hab hac had hbc hbd hcd col
    ⟨hm a ha b hb hab, hm a ha c hc hac, hm a ha d hd had,
      hm b hb c hc hbc, hm b hb d hd hbd, hm c hc d hd hcd⟩

lemma not_ramseyProp_of_le_17 {N : ℕ} (hN : N ≤ 17) : ¬ RamseyProp N := by
  intro h
  set g : Fin N → Fin 17 := Fin.castLE hN with hg
  have hginj : Function.Injective g := Fin.castLE_injective hN
  obtain ⟨S, hcard, hmono⟩ := h (fun i j => paleyColor (g i) (g j))
    (fun i j => paley_symm (g i) (g j))
  have hcard' : (S.image g).card = 4 := by
    rw [Finset.card_image_of_injective _ hginj, hcard]
  have himg : ∀ col : Bool, MonoSet (fun i j => paleyColor (g i) (g j)) col S →
      MonoSet paleyColor col (S.image g) := by
    intro col hm x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    exact hm i hi j hj (fun hij => hxy (by rw [hij]))
  rcases hmono with hm | hm
  · exact paley_no_mono_finset hcard' true (himg true hm)
  · exact paley_no_mono_finset hcard' false (himg false hm)

/-- **The Ramsey number `R(4,4)` is `18`**: `18` is the least `N` such that every symmetric
two-colouring of the edges of the complete graph on `N` vertices contains a monochromatic
clique on `4` vertices. -/
theorem ramsey_4_4 : IsLeast {N : ℕ | RamseyProp N} 18 := by
  constructor
  · intro f hsym
    obtain ⟨S, _, hcard, hmono⟩ := ramsey_44_le hsym Finset.univ (by simp)
    exact ⟨S, hcard, hmono⟩
  · intro N hN
    by_contra h
    exact not_ramseyProp_of_le_17 (show N ≤ 17 by omega) hN

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

