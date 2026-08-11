import RequestProject.Ramsey
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
# The Ramsey number `R(4,4) = 18`

We define two-colourings of the edges of a complete graph as simple graphs (`red` = adjacent,
`blue` = non-adjacent), and prove that every graph on 18 vertices contains a red or a blue
clique on 4 vertices, while the Paley graph on 17 vertices contains neither.
-/

open Finset
open scoped Classical

namespace Math

variable {V : Type*} {G : SimpleGraph V} {S S' : Finset V} {s t : ℕ} {v : V}

/-- `A` is a set of vertices, all pairs of which are adjacent (a "red" clique). -/
def RedClique (G : SimpleGraph V) (A : Finset V) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ≠ y → G.Adj x y

/-- `A` is a set of vertices, no pair of which is adjacent (a "blue" clique). -/
def BlueClique (G : SimpleGraph V) (A : Finset V) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ¬ G.Adj x y

/-- Inside the vertex set `S` there is a red clique of size `s` or a blue clique of size `t`. -/
def Ram (G : SimpleGraph V) (S : Finset V) (s t : ℕ) : Prop :=
  (∃ A ⊆ S, A.card = s ∧ RedClique G A) ∨ (∃ B ⊆ S, B.card = t ∧ BlueClique G B)

lemma RedClique.subset {A B : Finset V} (h : RedClique G A) (hBA : B ⊆ A) : RedClique G B :=
  fun _ hx _ hy hxy => h _ (hBA hx) _ (hBA hy) hxy

lemma BlueClique.subset {A B : Finset V} (h : BlueClique G A) (hBA : B ⊆ A) : BlueClique G B :=
  fun _ hx _ hy hxy => h _ (hBA hx) _ (hBA hy) hxy

lemma Ram.mono (h : Ram G S s t) (hS : S ⊆ S') : Ram G S' s t := by
  rcases h with ⟨A, hA, hc, hr⟩ | ⟨B, hB, hc, hb⟩
  · exact Or.inl ⟨A, hA.trans hS, hc, hr⟩
  · exact Or.inr ⟨B, hB.trans hS, hc, hb⟩

lemma redClique_insert {A : Finset V} (hv : v ∉ A) (hadj : ∀ y ∈ A, G.Adj v y)
    (h : RedClique G A) : RedClique G (insert v A) := by
  intro x hx y hy hxy
  simp only [Finset.mem_insert] at hx hy
  rcases hx with rfl | hx
  · rcases hy with rfl | hy
    · exact absurd rfl hxy
    · exact hadj _ hy
  · rcases hy with rfl | hy
    · exact (hadj _ hx).symm
    · exact h _ hx _ hy hxy

lemma blueClique_insert {A : Finset V} (hv : v ∉ A) (hadj : ∀ y ∈ A, ¬ G.Adj v y)
    (h : BlueClique G A) : BlueClique G (insert v A) := by
  intro x hx y hy hxy
  simp only [Finset.mem_insert] at hx hy
  rcases hx with rfl | hx
  · rcases hy with rfl | hy
    · exact absurd rfl hxy
    · exact hadj _ hy
  · rcases hy with rfl | hy
    · intro hc; exact hadj _ hx hc.symm
    · exact h _ hx _ hy hxy

/-- The red (adjacent) neighbours of `v` inside `S`. -/
noncomputable def redN (G : SimpleGraph V) (S : Finset V) (v : V) : Finset V := S.filter (fun y => G.Adj v y)

/-- The blue (non-adjacent, distinct) neighbours of `v` inside `S`. -/
noncomputable def blueN (G : SimpleGraph V) (S : Finset V) (v : V) : Finset V :=
  S.filter (fun y => y ≠ v ∧ ¬ G.Adj v y)

lemma redN_subset : redN G S v ⊆ S := Finset.filter_subset _ _

lemma blueN_subset : blueN G S v ⊆ S := Finset.filter_subset _ _

lemma mem_redN {y : V} : y ∈ redN G S v ↔ y ∈ S ∧ G.Adj v y := Finset.mem_filter

lemma mem_blueN {y : V} : y ∈ blueN G S v ↔ y ∈ S ∧ (y ≠ v ∧ ¬ G.Adj v y) := Finset.mem_filter

lemma card_redN_add_card_blueN (hv : v ∈ S) :
    (redN G S v).card + (blueN G S v).card + 1 = S.card := by
  have hsplit : (S.filter (fun y => G.Adj v y)).card
      + (S.filter (fun y => ¬ G.Adj v y)).card = S.card :=
    Finset.card_filter_add_card_filter_not _
  have hins : S.filter (fun y => ¬ G.Adj v y) = insert v (blueN G S v) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_insert, mem_blueN]
    constructor
    · rintro ⟨hyS, hadj⟩
      by_cases h : y = v
      · exact Or.inl h
      · exact Or.inr ⟨hyS, h, hadj⟩
    · rintro (rfl | ⟨hyS, _, hadj⟩)
      · exact ⟨hv, by simp⟩
      · exact ⟨hyS, hadj⟩
  have hvnot : v ∉ blueN G S v := by simp [mem_blueN]
  rw [hins, Finset.card_insert_of_notMem hvnot] at hsplit
  simpa [redN] using hsplit

lemma ram_succ_left (hv : v ∈ S) (h : Ram G (redN G S v) s t) : Ram G S (s + 1) t := by
  rcases h with ⟨A, hA, hc, hr⟩ | ⟨B, hB, hc, hb⟩
  · have hvA : v ∉ A := by
      intro hmem
      have := (mem_redN (G := G) (S := S) (v := v)).1 (hA hmem)
      exact G.ne_of_adj this.2 rfl
    refine Or.inl ⟨insert v A, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hv
      · exact redN_subset (hA hx)
    · rw [Finset.card_insert_of_notMem hvA, hc]
    · exact redClique_insert hvA (fun y hy => ((mem_redN (G := G)).1 (hA hy)).2) hr
  · exact Or.inr ⟨B, hB.trans redN_subset, hc, hb⟩

lemma ram_succ_right (hv : v ∈ S) (h : Ram G (blueN G S v) s t) : Ram G S s (t + 1) := by
  rcases h with ⟨A, hA, hc, hr⟩ | ⟨B, hB, hc, hb⟩
  · exact Or.inl ⟨A, hA.trans blueN_subset, hc, hr⟩
  · have hvB : v ∉ B := by
      intro hmem
      exact ((mem_blueN (G := G) (S := S) (v := v)).1 (hB hmem)).2.1 rfl
    refine Or.inr ⟨insert v B, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hv
      · exact blueN_subset (hB hx)
    · rw [Finset.card_insert_of_notMem hvB, hc]
    · exact blueClique_insert hvB (fun y hy => ((mem_blueN (G := G)).1 (hB hy)).2.2) hb

lemma ram_two_left (h : t ≤ S.card) : Ram G S 2 t := by
  by_cases hedge : ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ G.Adj x y
  · obtain ⟨x, hx, y, hy, hxy, hadj⟩ := hedge
    refine Or.inl ⟨{x, y}, ?_, ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hx
      · rw [Finset.mem_singleton] at hz; subst hz; exact hy
    · rw [Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]
    · intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact hadj
      · exact hadj.symm
      · exact absurd rfl hab
  · push_neg at hedge
    obtain ⟨B, hBS, hB⟩ := Finset.exists_subset_card_eq h
    exact Or.inr ⟨B, hBS, hB, fun x hx y hy hxy => hedge x (hBS hx) y (hBS hy) hxy⟩

lemma ram_two_right (h : s ≤ S.card) : Ram G S s 2 := by
  by_cases hedge : ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ ¬ G.Adj x y
  · obtain ⟨x, hx, y, hy, hxy, hadj⟩ := hedge
    refine Or.inr ⟨{x, y}, ?_, ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hx
      · rw [Finset.mem_singleton] at hz; subst hz; exact hy
    · rw [Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]
    · intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact hadj
      · exact fun hc => hadj hc.symm
      · exact absurd rfl hab
  · push_neg at hedge
    obtain ⟨A, hAS, hA⟩ := Finset.exists_subset_card_eq h
    exact Or.inl ⟨A, hAS, hA, fun x hx y hy hxy => hedge x (hAS hx) y (hAS hy) hxy⟩

/-- Handshake lemma: the sum of the degrees inside `S` is even. -/
lemma even_sum_card_redN (G : SimpleGraph V) (S : Finset V) :
    Even (∑ v ∈ S, (redN G S v).card) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
      have key : ∀ v ∈ T, (redN G (insert a T) v).card
          = (redN G T v).card + (if G.Adj v a then 1 else 0) := by
        intro v _
        by_cases hva : G.Adj v a
        · have : redN G (insert a T) v = insert a (redN G T v) := by
            ext y; simp only [mem_redN, Finset.mem_insert]
            constructor
            · rintro ⟨hy | hy, h2⟩
              · exact Or.inl hy
              · exact Or.inr ⟨hy, h2⟩
            · rintro (rfl | ⟨hy, h2⟩)
              · exact ⟨Or.inl rfl, hva⟩
              · exact ⟨Or.inr hy, h2⟩
          rw [this, Finset.card_insert_of_notMem (fun hc => ha ((mem_redN (G := G)).1 hc).1),
            if_pos hva]
        · have : redN G (insert a T) v = redN G T v := by
            ext y; simp only [mem_redN, Finset.mem_insert]
            constructor
            · rintro ⟨hy | hy, h2⟩
              · subst hy; exact absurd h2 hva
              · exact ⟨hy, h2⟩
            · rintro ⟨hy, h2⟩; exact ⟨Or.inr hy, h2⟩
          rw [this, if_neg hva, Nat.add_zero]
      have hA : redN G (insert a T) a = redN G T a := by
        ext y; simp only [mem_redN, Finset.mem_insert]
        constructor
        · rintro ⟨hy | hy, h2⟩
          · subst hy; exact absurd rfl (G.ne_of_adj h2)
          · exact ⟨hy, h2⟩
        · rintro ⟨hy, h2⟩; exact ⟨Or.inr hy, h2⟩
      have hsum : ∑ v ∈ T, (if G.Adj v a then 1 else 0) = (redN G T a).card := by
        have heq : T.filter (fun v => G.Adj v a) = T.filter (fun y => G.Adj a y) :=
          Finset.filter_congr (fun x _ => by rw [SimpleGraph.adj_comm])
        rw [← Finset.card_filter, heq]
        rfl
      rw [Finset.sum_insert ha, hA, Finset.sum_congr rfl key, Finset.sum_add_distrib, hsum]
      have : (redN G T a).card + (∑ v ∈ T, (redN G T v).card + (redN G T a).card)
          = (∑ v ∈ T, (redN G T v).card) + 2 * (redN G T a).card := by ring
      rw [this]
      exact ih.add (even_two_mul _)

lemma ram_3_3 (h : 6 ≤ S.card) : Ram G S 3 3 := by
  obtain ⟨v, hv⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
  have hcards := card_redN_add_card_blueN (G := G) hv
  by_cases hred : 3 ≤ (redN G S v).card
  · exact ram_succ_left hv (ram_two_left hred)
  · have hblue : 3 ≤ (blueN G S v).card := by omega
    exact ram_succ_right hv (ram_two_right hblue)

lemma ram_3_4_of_card_eq (hS : S.card = 9) : Ram G S 3 4 := by
  by_contra hcon
  have hdeg : ∀ v ∈ S, (redN G S v).card = 3 := by
    intro v hv
    have hcards := card_redN_add_card_blueN (G := G) hv
    have h1 : ¬ (4 ≤ (redN G S v).card) := by
      intro h4
      exact hcon (ram_succ_left hv (ram_two_left h4))
    have h2 : ¬ (6 ≤ (blueN G S v).card) := by
      intro h6
      exact hcon (ram_succ_right hv (ram_3_3 h6))
    omega
  have hsum : ∑ v ∈ S, (redN G S v).card = 27 := by
    rw [Finset.sum_congr rfl hdeg, Finset.sum_const, hS, smul_eq_mul]
  have := even_sum_card_redN G S
  rw [hsum] at this
  exact (by decide : ¬ Even 27) this

lemma ram_3_4 (h : 9 ≤ S.card) : Ram G S 3 4 := by
  obtain ⟨S₀, hS₀, hcard⟩ := Finset.exists_subset_card_eq h
  exact (ram_3_4_of_card_eq hcard).mono hS₀

lemma redClique_compl {A : Finset V} : RedClique Gᶜ A ↔ BlueClique G A := by
  constructor
  · intro h x hx y hy hxy hadj
    exact ((SimpleGraph.compl_adj _ _ _).1 (h x hx y hy hxy)).2 hadj
  · intro h x hx y hy hxy
    exact (SimpleGraph.compl_adj _ _ _).2 ⟨hxy, h x hx y hy hxy⟩

lemma blueClique_compl {B : Finset V} : BlueClique Gᶜ B ↔ RedClique G B := by
  constructor
  · intro h x hx y hy hxy
    have := h x hx y hy hxy
    rw [SimpleGraph.compl_adj] at this
    tauto
  · intro h x hx y hy hxy hc
    exact ((SimpleGraph.compl_adj _ _ _).1 hc).2 (h x hx y hy hxy)

lemma ram_compl : Ram Gᶜ S s t ↔ Ram G S t s := by
  unfold Ram
  constructor
  · rintro (⟨A, hA, hc, hr⟩ | ⟨B, hB, hc, hb⟩)
    · exact Or.inr ⟨A, hA, hc, redClique_compl.1 hr⟩
    · exact Or.inl ⟨B, hB, hc, blueClique_compl.1 hb⟩
  · rintro (⟨A, hA, hc, hr⟩ | ⟨B, hB, hc, hb⟩)
    · exact Or.inr ⟨A, hA, hc, blueClique_compl.2 hr⟩
    · exact Or.inl ⟨B, hB, hc, redClique_compl.2 hb⟩

lemma ram_4_3 (h : 9 ≤ S.card) : Ram G S 4 3 := ram_compl.1 (ram_3_4 (G := Gᶜ) h)

lemma ram_4_4_of_card_eq (hS : S.card = 18) : Ram G S 4 4 := by
  obtain ⟨v, hv⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
  have hcards := card_redN_add_card_blueN (G := G) hv
  by_cases hred : 9 ≤ (redN G S v).card
  · exact ram_succ_left hv (ram_3_4 hred)
  · have hblue : 9 ≤ (blueN G S v).card := by omega
    exact ram_succ_right hv (ram_4_3 hblue)

lemma ram_4_4 (h : 18 ≤ S.card) : Ram G S 4 4 := by
  obtain ⟨S₀, hS₀, hcard⟩ := Finset.exists_subset_card_eq h
  exact (ram_4_4_of_card_eq hcard).mono hS₀

/-! ### The Ramsey number -/

/-- Every graph on `n` vertices has a red `s`-clique or a blue `t`-clique. -/
def IsRamsey (n s t : ℕ) : Prop := ∀ G : SimpleGraph (Fin n), Ram G Finset.univ s t

/-- The two-colour Ramsey number `R(s,t)`. -/
noncomputable def ramseyNumber (s t : ℕ) : ℕ := sInf {n | IsRamsey n s t}

lemma isRamsey_mono {m n s t : ℕ} (h : IsRamsey m s t) (hmn : m ≤ n) : IsRamsey n s t := by
  intro G
  set f : Fin m → Fin n := Fin.castLE hmn with hf
  have hinj : Function.Injective f := Fin.castLE_injective hmn
  rcases h (SimpleGraph.comap f G) with ⟨A, -, hc, hr⟩ | ⟨B, -, hc, hb⟩
  · refine Or.inl ⟨A.image f, Finset.subset_univ _, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hinj, hc]
    · intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
      exact hr a ha b hb (fun hc => hxy (by rw [hc]))
  · refine Or.inr ⟨B.image f, Finset.subset_univ _, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hinj, hc]
    · intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨b, hb', rfl⟩ := Finset.mem_image.1 hy
      exact hb a ha b hb' (fun hc => hxy (by rw [hc]))

theorem isRamsey_18 : IsRamsey 18 4 4 := by
  intro G
  refine ram_4_4 ?_
  simp

/-! ### The Paley graph on 17 vertices -/

/-- The nonzero quadratic residues mod 17. -/
def qr17 (n : ℕ) : Bool :=
  n = 1 || n = 2 || n = 4 || n = 8 || n = 9 || n = 13 || n = 15 || n = 16

/-- Adjacency in the Paley graph of order 17. -/
def paleyAdj (x y : Fin 17) : Bool := qr17 ((x.val + 17 - y.val) % 17)

lemma paleyAdj_symm : ∀ x y : Fin 17, paleyAdj x y = paleyAdj y x := by decide +kernel

lemma paleyAdj_irrefl : ∀ x : Fin 17, paleyAdj x x = false := by decide +kernel

/-- The Paley graph on 17 vertices. -/
def paley : SimpleGraph (Fin 17) where
  Adj x y := paleyAdj x y = true
  symm := by
    intro x y h
    rw [paleyAdj_symm]
    exact h
  loopless := ⟨by
    intro x h
    rw [paleyAdj_irrefl x] at h
    exact Bool.false_ne_true h⟩

lemma paley_adj_iff {x y : Fin 17} : paley.Adj x y ↔ paleyAdj x y = true := Iff.rfl

lemma paley_key : ∀ a b c d : Fin 17, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    (paleyAdj a b && paleyAdj a c && paleyAdj a d && paleyAdj b c && paleyAdj b d
      && paleyAdj c d) = false ∧
    ((!paleyAdj a b) && (!paleyAdj a c) && (!paleyAdj a d) && (!paleyAdj b c)
      && (!paleyAdj b d) && (!paleyAdj c d)) = false := by
  decide +kernel

lemma paley_no_red4 {A : Finset (Fin 17)} (hA : A.card = 4) : ¬ RedClique paley A := by
  intro hr
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_four.1 hA
  have h := (paley_key a b c d hab hac had hbc hbd hcd).1
  have ma : a ∈ ({a, b, c, d} : Finset (Fin 17)) := by simp
  have mb : b ∈ ({a, b, c, d} : Finset (Fin 17)) := by simp
  have mc : c ∈ ({a, b, c, d} : Finset (Fin 17)) := by simp
  have md : d ∈ ({a, b, c, d} : Finset (Fin 17)) := by simp
  have h1 := hr a ma b mb hab
  have h2 := hr a ma c mc hac
  have h3 := hr a ma d md had
  have h4 := hr b mb c mc hbc
  have h5 := hr b mb d md hbd
  have h6 := hr c mc d md hcd
  rw [paley_adj_iff] at h1 h2 h3 h4 h5 h6
  rw [h1, h2, h3, h4, h5, h6] at h
  simp at h

lemma paley_no_blue4 {A : Finset (Fin 17)} (hA : A.card = 4) : ¬ BlueClique paley A := by
  intro hr
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_four.1 hA
  have h := (paley_key a b c d hab hac had hbc hbd hcd).2
  have ma : a ∈ ({a, b, c, d} : Finset (Fin 17)) := by simp
  have mb : b ∈ ({a, b, c, d} : Finset (Fin 17)) := by simp
  have mc : c ∈ ({a, b, c, d} : Finset (Fin 17)) := by simp
  have md : d ∈ ({a, b, c, d} : Finset (Fin 17)) := by simp
  have h1 := hr a ma b mb hab
  have h2 := hr a ma c mc hac
  have h3 := hr a ma d md had
  have h4 := hr b mb c mc hbc
  have h5 := hr b mb d md hbd
  have h6 := hr c mc d md hcd
  rw [paley_adj_iff, Bool.not_eq_true] at h1 h2 h3 h4 h5 h6
  rw [h1, h2, h3, h4, h5, h6] at h
  simp at h

theorem not_isRamsey_17 : ¬ IsRamsey 17 4 4 := by
  intro h
  rcases h paley with ⟨A, -, hc, hr⟩ | ⟨B, -, hc, hb⟩
  · exact paley_no_red4 hc hr
  · exact paley_no_blue4 hc hb

/-- **The two-colour Ramsey number `R(4,4)` equals 18.** -/
theorem ramsey_4_4 : ramseyNumber 4 4 = 18 := by
  have hmem : (18 : ℕ) ∈ {n | IsRamsey n 4 4} := isRamsey_18
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra hlt
  push_neg at hlt
  have hmem' : ramseyNumber 4 4 ∈ {n | IsRamsey n 4 4} := Nat.sInf_mem ⟨18, hmem⟩
  exact not_isRamsey_17 (isRamsey_mono hmem' (by omega))

end Math

