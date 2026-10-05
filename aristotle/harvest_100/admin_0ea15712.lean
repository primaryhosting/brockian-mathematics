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
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The two-colour Ramsey number `R(4,4)` equals `18`.

Mathlib (at the pinned revision) contains no theory of Ramsey numbers, so the whole
argument is developed here:

* the classical upper bound `R(p+1,q+1) ≤ R(p,q+1) + R(p+1,q)` (`Math.arrow_step`),
* `R(3,3) ≤ 6` and, via the parity/degree argument, `R(3,4) ≤ 9`
  (`Math.arrow_three_three`, `Math.arrow_three_four`), giving `R(4,4) ≤ 18`,
* the Paley graph on 17 vertices, which has neither a 4-clique nor a 4-element
  independent set, giving `R(4,4) > 17`.
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

open Finset

/-! ## A relation-theoretic formulation of Ramsey's theorem for two colours -/

variable {V : Type*}

/-- A finite set `t` is homogeneous for the relation `r` if all distinct pairs of elements
of `t` are related by `r`. -/
def Homog (r : V → V → Prop) (t : Finset V) : Prop :=
  ∀ x ∈ t, ∀ y ∈ t, x ≠ y → r x y

/-- The arrow relation `S → (p, q)`: for the 2-colouring of the pairs of `S` given by `r`,
there is a `p`-set homogeneous for `r` or a `q`-set homogeneous for the complement of `r`. -/
def Arrow (r : V → V → Prop) (S : Finset V) (p q : ℕ) : Prop :=
  (∃ t ⊆ S, t.card = p ∧ Homog r t) ∨ (∃ t ⊆ S, t.card = q ∧ Homog (fun a b => ¬ r a b) t)

lemma arrow_swap {r : V → V → Prop} {S : Finset V} {p q : ℕ}
    (h : Arrow (fun a b => ¬ r a b) S q p) : Arrow r S p q := by
  rcases h with ⟨t, hts, hc, hh⟩ | ⟨t, hts, hc, hh⟩
  · exact Or.inr ⟨t, hts, hc, hh⟩
  · exact Or.inl ⟨t, hts, hc, fun x hx y hy hxy => not_not.mp (hh x hx y hy hxy)⟩

lemma homog_triple [DecidableEq V] {r : V → V → Prop} (hsymm : ∀ x y, r x y → r y x) {a b c : V}
    (hab : r a b) (hac : r a c) (hbc : r b c) : Homog r ({a, b, c} : Finset V) := by
  intro x hx y hy hxy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    first
      | exact absurd rfl hxy
      | assumption
      | exact hsymm _ _ (by assumption)

lemma homog_insert [DecidableEq V] {r : V → V → Prop} (hsymm : ∀ x y, r x y → r y x) {v : V}
    {t : Finset V} (hh : Homog r t) (hv : ∀ u ∈ t, r v u) : Homog r (insert v t) := by
  intro x hx y hy hxy
  simp only [Finset.mem_insert] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact absurd (hx.trans hy.symm) hxy
  · rw [hx]; exact hv y hy
  · rw [hy]; exact hsymm _ _ (hv x hx)
  · exact hh x hx y hy hxy

/-- `R(2,q) ≤ q`. -/
lemma arrow_two_left (r : V → V → Prop) (hsymm : ∀ x y, r x y → r y x) (S : Finset V) {q : ℕ}
    (hcard : q ≤ S.card) : Arrow r S 2 q := by
  classical
  by_cases h : ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ r x y
  · obtain ⟨x, hx, y, hy, hxy, hr⟩ := h
    refine Or.inl ⟨{x, y}, ?_, ?_, ?_⟩
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    · rw [Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]
    · intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact hr
      · exact hsymm _ _ hr
      · exact absurd rfl hab
  · push_neg at h
    obtain ⟨t, hts, hct⟩ := Finset.exists_subset_card_eq hcard
    exact Or.inr ⟨t, hts, hct, fun x hx y hy hxy => h x (hts hx) y (hts hy) hxy⟩

/-- `R(p,2) ≤ p`. -/
lemma arrow_two_right (r : V → V → Prop) (hsymm : ∀ x y, r x y → r y x) (S : Finset V) {p : ℕ}
    (hcard : p ≤ S.card) : Arrow r S p 2 :=
  arrow_swap (arrow_two_left (fun a b => ¬ r a b) (fun _ _ h hc => h (hsymm _ _ hc)) S hcard)

/-- The classical induction step `R(p+1, q+1) ≤ R(p, q+1) + R(p+1, q)`. -/
lemma arrow_step {r : V → V → Prop} (hsymm : ∀ x y, r x y → r y x) {S : Finset V}
    {p q n₁ n₂ : ℕ}
    (hA : ∀ T : Finset V, n₁ ≤ T.card → Arrow r T p (q + 1))
    (hB : ∀ T : Finset V, n₂ ≤ T.card → Arrow r T (p + 1) q)
    (hne : S.Nonempty) (hS : n₁ + n₂ ≤ S.card) : Arrow r S (p + 1) (q + 1) := by
  classical
  obtain ⟨v, hv⟩ := hne
  set T := S.erase v with hT
  set A := T.filter (fun u => r v u) with hAdef
  set B := T.filter (fun u => ¬ r v u) with hBdef
  have hsum : A.card + B.card = T.card := Finset.card_filter_add_card_filter_not _
  have hTc : T.card + 1 = S.card := by
    rw [hT, Finset.card_erase_of_mem hv]
    have : 1 ≤ S.card := Finset.card_pos.mpr ⟨v, hv⟩
    omega
  have hAT : A ⊆ T := Finset.filter_subset _ _
  have hBT : B ⊆ T := Finset.filter_subset _ _
  have hTS : T ⊆ S := Finset.erase_subset _ _
  have hcase : n₁ ≤ A.card ∨ n₂ ≤ B.card := by omega
  rcases hcase with hc | hc
  · rcases hA A hc with ⟨t, hts, hcard, hh⟩ | ⟨t, hts, hcard, hh⟩
    · have hvt : v ∉ t := fun hvt => (Finset.notMem_erase v S) (hAT (hts hvt))
      refine Or.inl ⟨insert v t, ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with h | h
        · exact h ▸ hv
        · exact hTS (hAT (hts h))
      · rw [Finset.card_insert_of_notMem hvt, hcard]
      · exact homog_insert hsymm hh (fun u hu => (Finset.mem_filter.mp (hts hu)).2)
    · exact Or.inr ⟨t, fun x hx => hTS (hAT (hts hx)), hcard, hh⟩
  · rcases hB B hc with ⟨t, hts, hcard, hh⟩ | ⟨t, hts, hcard, hh⟩
    · exact Or.inl ⟨t, fun x hx => hTS (hBT (hts hx)), hcard, hh⟩
    · have hvt : v ∉ t := fun hvt => (Finset.notMem_erase v S) (hBT (hts hvt))
      refine Or.inr ⟨insert v t, ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with h | h
        · exact h ▸ hv
        · exact hTS (hBT (hts h))
      · rw [Finset.card_insert_of_notMem hvt, hcard]
      · exact homog_insert (fun _ _ h hcon => h (hsymm _ _ hcon)) hh
          (fun u hu => (Finset.mem_filter.mp (hts hu)).2)

/-- `R(3,3) ≤ 6`. -/
lemma arrow_three_three (r : V → V → Prop) (hsymm : ∀ x y, r x y → r y x) (S : Finset V)
    (hS : 6 ≤ S.card) : Arrow r S 3 3 := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega : 0 < S.card)
  have h := arrow_step (r := r) (p := 2) (q := 2) (n₁ := 3) (n₂ := 3) hsymm
    (fun T hT => arrow_two_left r hsymm T hT)
    (fun T hT => arrow_two_right r hsymm T hT) hne (by omega)
  simpa using h

/-- Parity: the sum of a symmetric weight function with vanishing diagonal over a square
is even. -/
lemma even_sum_pairs (f : V → V → ℕ) (hf : ∀ a b, f a b = f b a) (hd : ∀ a, f a a = 0)
    (S : Finset V) : Even (∑ v ∈ S, ∑ u ∈ S, f v u) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have h1 : ∀ v : V, ∑ u ∈ insert a s, f v u = f v a + ∑ u ∈ s, f v u := by
        intro v; rw [Finset.sum_insert ha]
      rw [Finset.sum_insert ha, h1]
      simp only [h1]
      rw [Finset.sum_add_distrib, hd a]
      have h2 : ∑ v ∈ s, f v a = ∑ u ∈ s, f a u := Finset.sum_congr rfl fun v _ => hf v a
      rw [h2]
      obtain ⟨k, hk⟩ := ih
      exact ⟨∑ u ∈ s, f a u + k, by omega⟩

/-- `R(3,4) ≤ 9`, for a set of exactly nine vertices.

If there is no homogeneous triple and no anti-homogeneous quadruple, then every vertex has
exactly three neighbours, so the sum of the degrees is `27`, contradicting the handshake
parity. -/
lemma arrow_three_four_aux (r : V → V → Prop) (hsymm : ∀ x y, r x y → r y x) (S : Finset V)
    (hS : S.card = 9) : Arrow r S 3 4 := by
  classical
  by_contra hcon
  have hred : ∀ t ⊆ S, t.card = 3 → ¬ Homog r t :=
    fun t hts hc hh => hcon (Or.inl ⟨t, hts, hc, hh⟩)
  have hblue : ∀ t ⊆ S, t.card = 4 → ¬ Homog (fun a b => ¬ r a b) t :=
    fun t hts hc hh => hcon (Or.inr ⟨t, hts, hc, hh⟩)
  have hsymm' : ∀ x y : V, (¬ r x y) → ¬ r y x := fun _ _ h hc => h (hsymm _ _ hc)
  set A : V → Finset V := fun v => (S.erase v).filter (fun u => r v u) with hA
  set B : V → Finset V := fun v => (S.erase v).filter (fun u => ¬ r v u) with hB
  have hAsub : ∀ v, A v ⊆ S := fun v => (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  have hBsub : ∀ v, B v ⊆ S := fun v => (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  -- the neighbourhood of a vertex is anti-homogeneous
  have hindep : ∀ v ∈ S, ∀ x ∈ A v, ∀ y ∈ A v, x ≠ y → ¬ r x y := by
    intro v hv x hx y hy hxy hr
    have hvx : v ≠ x := fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp hx).1).1 h.symm
    have hvy : v ≠ y := fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp hy).1).1 h.symm
    refine hred {v, x, y} ?_ ?_ (homog_triple hsymm (Finset.mem_filter.mp hx).2
      (Finset.mem_filter.mp hy).2 hr)
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact hv
      · exact hAsub v hx
      · exact hAsub v hy
    · exact Finset.card_eq_three.mpr ⟨v, x, y, hvx, hvy, hxy, rfl⟩
  -- every degree is at most three
  have hdeg_le : ∀ v ∈ S, (A v).card ≤ 3 := by
    intro v hv
    by_contra hgt
    push_neg at hgt
    obtain ⟨t, hts, hct⟩ := Finset.exists_subset_card_eq (show 4 ≤ (A v).card by omega)
    exact hblue t (hts.trans (hAsub v)) hct
      (fun x hx y hy hxy => hindep v hv x (hts hx) y (hts hy) hxy)
  -- every degree is at least three
  have hdeg_ge : ∀ v ∈ S, 3 ≤ (A v).card := by
    intro v hv
    by_contra hlt
    push_neg at hlt
    have hsum : (A v).card + (B v).card = (S.erase v).card :=
      Finset.card_filter_add_card_filter_not _
    have herase : (S.erase v).card = 8 := by rw [Finset.card_erase_of_mem hv, hS]
    have hBcard : 6 ≤ (B v).card := by omega
    rcases arrow_three_three r hsymm (B v) hBcard with ⟨t, hts, hct, hh⟩ | ⟨t, hts, hct, hh⟩
    · exact hred t (hts.trans (hBsub v)) hct hh
    · have hvt : v ∉ t := fun hvt =>
        (Finset.mem_erase.mp (Finset.mem_filter.mp (hts hvt)).1).1 rfl
      refine hblue (insert v t) ?_ ?_ (homog_insert hsymm' hh
        (fun u hu => (Finset.mem_filter.mp (hts hu)).2))
      · intro x hx
        rcases Finset.mem_insert.mp hx with h | h
        · exact h ▸ hv
        · exact hBsub v (hts h)
      · rw [Finset.card_insert_of_notMem hvt, hct]
  have hdeg : ∀ v ∈ S, (A v).card = 3 := fun v hv => le_antisymm (hdeg_le v hv) (hdeg_ge v hv)
  -- the degree sum is both `27` and even
  set f : V → V → ℕ := fun a b => if a ≠ b ∧ r a b then 1 else 0 with hf
  have hfsymm : ∀ a b, f a b = f b a := by
    intro a b
    by_cases h : a ≠ b ∧ r a b
    · have h' : b ≠ a ∧ r b a := ⟨Ne.symm h.1, hsymm _ _ h.2⟩
      simp only [hf, if_pos h, if_pos h']
    · have h' : ¬ (b ≠ a ∧ r b a) := fun hc => h ⟨Ne.symm hc.1, hsymm _ _ hc.2⟩
      simp only [hf, if_neg h, if_neg h']
  have hfd : ∀ a, f a a = 0 := by
    intro a
    simp only [hf, ne_eq, not_true_eq_false, false_and, if_false]
  have hcardf : ∀ v ∈ S, (A v).card = ∑ u ∈ S, f v u := by
    intro v _
    have hAv : A v = S.filter (fun u => v ≠ u ∧ r v u) := by
      ext u
      simp only [hA, Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨hne, hu⟩, hr⟩; exact ⟨hu, ⟨Ne.symm hne, hr⟩⟩
      · rintro ⟨hu, hne, hr⟩; exact ⟨⟨Ne.symm hne, hu⟩, hr⟩
    rw [hAv, Finset.card_filter]
  have h27 : ∑ v ∈ S, ∑ u ∈ S, f v u = 27 := by
    rw [← Finset.sum_congr rfl hcardf, Finset.sum_congr rfl hdeg]
    simp [hS]
  have hev := even_sum_pairs f hfsymm hfd S
  rw [h27] at hev
  obtain ⟨k, hk⟩ := hev
  omega

/-- `R(3,4) ≤ 9`. -/
lemma arrow_three_four (r : V → V → Prop) (hsymm : ∀ x y, r x y → r y x) (S : Finset V)
    (hS : 9 ≤ S.card) : Arrow r S 3 4 := by
  obtain ⟨T, hTS, hT9⟩ := Finset.exists_subset_card_eq hS
  rcases arrow_three_four_aux r hsymm T hT9 with ⟨t, hts, h⟩ | ⟨t, hts, h⟩
  · exact Or.inl ⟨t, hts.trans hTS, h⟩
  · exact Or.inr ⟨t, hts.trans hTS, h⟩

/-- `R(4,3) ≤ 9`. -/
lemma arrow_four_three (r : V → V → Prop) (hsymm : ∀ x y, r x y → r y x) (S : Finset V)
    (hS : 9 ≤ S.card) : Arrow r S 4 3 :=
  arrow_swap (arrow_three_four (fun a b => ¬ r a b) (fun _ _ h hc => h (hsymm _ _ hc)) S hS)

/-- `R(4,4) ≤ 18`. -/
lemma arrow_four_four (r : V → V → Prop) (hsymm : ∀ x y, r x y → r y x) (S : Finset V)
    (hS : 18 ≤ S.card) : Arrow r S 4 4 := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega : 0 < S.card)
  have h := arrow_step (r := r) (p := 3) (q := 3) (n₁ := 9) (n₂ := 9) hsymm
    (fun T hT => arrow_three_four r hsymm T hT)
    (fun T hT => arrow_four_three r hsymm T hT) hne (by omega)
  simpa using h

/-! ## The Paley graph on 17 vertices -/

/-- Adjacency in the Paley graph of order 17: `i ~ j` iff `i - j` is a nonzero quadratic
residue mod 17. -/
def qrAdj (i j : Fin 17) : Bool :=
  ((i.val + 17 - j.val) % 17) ∈ ([1, 2, 4, 8, 9, 13, 15, 16] : List ℕ)

lemma qrAdj_symm : ∀ i j : Fin 17, qrAdj i j = qrAdj j i := by decide

lemma qrAdj_irrefl : ∀ i : Fin 17, qrAdj i i = false := by decide

/-- The Paley graph on 17 vertices. -/
def paley : SimpleGraph (Fin 17) where
  Adj i j := qrAdj i j = true
  symm := by
    intro x y h
    rw [qrAdj_symm]
    exact h
  loopless := ⟨by
    intro x h
    rw [qrAdj_irrefl] at h
    exact Bool.noConfusion h⟩

lemma paley_no_red_four : ∀ a b c d : Fin 17, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ¬ (qrAdj a b ∧ qrAdj a c ∧ qrAdj a d ∧ qrAdj b c ∧ qrAdj b d ∧ qrAdj c d) := by decide

lemma paley_no_blue_four : ∀ a b c d : Fin 17, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ¬ (qrAdj a b = false ∧ qrAdj a c = false ∧ qrAdj a d = false ∧ qrAdj b c = false ∧
       qrAdj b d = false ∧ qrAdj c d = false) := by decide

lemma card_eq_four {α : Type*} [DecidableEq α] {t : Finset α} (h : t.card = 4) :
    ∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ t = {a, b, c, d} := by
  obtain ⟨a, s, has, rfl, hs⟩ := Finset.card_eq_succ.mp h
  obtain ⟨b, c, d, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_three.mp hs
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at has
  exact ⟨a, b, c, d, has.1, has.2.1, has.2.2, hbc, hbd, hcd, rfl⟩

/-- The Paley graph on 17 vertices contains no monochromatic 4-set. -/
lemma paley_no_mono (t : Finset (Fin 17)) (ht : t.card = 4) :
    ¬ Homog (fun a b => qrAdj a b = true) t ∧ ¬ Homog (fun a b => ¬ (qrAdj a b = true)) t := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := card_eq_four ht
  have ma : a ∈ ({a, b, c, d} : Finset (Fin 17)) := by simp
  have mb : b ∈ ({a, b, c, d} : Finset (Fin 17)) := by simp
  have mc : c ∈ ({a, b, c, d} : Finset (Fin 17)) := by simp
  have md : d ∈ ({a, b, c, d} : Finset (Fin 17)) := by simp
  constructor
  · intro hh
    exact paley_no_red_four a b c d hab hac had hbc hbd hcd
      ⟨hh a ma b mb hab, hh a ma c mc hac, hh a ma d md had, hh b mb c mc hbc,
       hh b mb d md hbd, hh c mc d md hcd⟩
  · intro hh
    refine paley_no_blue_four a b c d hab hac had hbc hbd hcd
      ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Bool.not_eq_true] at hh
    · exact hh a ma b mb hab
    · exact hh a ma c mc hac
    · exact hh a ma d md had
    · exact hh b mb c mc hbc
    · exact hh b mb d md hbd
    · exact hh c mc d md hcd

/-! ## The main theorem -/

/-- The Ramsey number `R(4,4)` equals `18`: `18` is the least `N` such that every
graph on `N` vertices contains a clique of size 4 or an independent set of size 4
(i.e. a 4-clique of the complement). -/
theorem ramsey_4_4 :
    IsLeast {N : ℕ | ∀ G : SimpleGraph (Fin N), ∃ t : Finset (Fin N),
      G.IsNClique 4 t ∨ Gᶜ.IsNClique 4 t} 18 := by
  constructor
  · intro G
    have hcard : (Finset.univ : Finset (Fin 18)).card = 18 := by simp
    rcases arrow_four_four G.Adj (fun x y h => G.symm h) Finset.univ (by omega) with
      ⟨t, _, hct, hh⟩ | ⟨t, _, hct, hh⟩
    · exact ⟨t, Or.inl ⟨fun x hx y hy hxy => hh x hx y hy hxy, hct⟩⟩
    · exact ⟨t, Or.inr ⟨fun x hx y hy hxy => ⟨hxy, hh x hx y hy hxy⟩, hct⟩⟩
  · intro N hN
    by_contra hlt
    push_neg at hlt
    set f : Fin N → Fin 17 := fun i => ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩ with hf
    have hinj : Function.Injective f := by
      intro x y hxy
      apply Fin.ext
      simpa [hf, Fin.ext_iff] using hxy
    obtain ⟨t, ht⟩ := hN (SimpleGraph.comap f paley)
    classical
    have hcard : (t.image f).card = 4 := by
      rcases ht with ⟨_, hc⟩ | ⟨_, hc⟩ <;> rw [Finset.card_image_of_injective _ hinj, hc]
    obtain ⟨h1, h2⟩ := paley_no_mono (t.image f) hcard
    rcases ht with ⟨hcl, _⟩ | ⟨hcl, _⟩
    · refine h1 ?_
      intro x hx y hy hxy
      simp only [Finset.mem_image] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact hcl ha hb (fun h => hxy (by rw [h]))
    · refine h2 ?_
      intro x hx y hy hxy
      simp only [Finset.mem_image] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      have hadj := hcl ha hb (fun h => hxy (by rw [h]))
      simp only [SimpleGraph.compl_adj, SimpleGraph.comap_adj] at hadj
      exact hadj.2

end Math

