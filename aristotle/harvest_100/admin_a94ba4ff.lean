import Mathlib
/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

open scoped Classical

namespace Ramsey44

variable {V : Type*}

/-- `Arr G s p q` says that inside the vertex set `s` there is either a `p`-clique of `G`
or a `q`-clique of the complement of `G` (i.e. an independent set of size `q`). -/
def Arr (G : SimpleGraph V) (s : Finset V) (p q : ℕ) : Prop :=
  (∃ t ⊆ s, G.IsNClique p t) ∨ (∃ t ⊆ s, Gᶜ.IsNClique q t)

lemma arr_compl (G : SimpleGraph V) (s : Finset V) (p q : ℕ) :
    Arr Gᶜ s q p ↔ Arr G s p q := by
  simp only [Arr, compl_compl]
  exact or_comm

lemma Arr.mono {G : SimpleGraph V} {s s' : Finset V} {p q : ℕ} (hss : s ⊆ s')
    (h : Arr G s p q) : Arr G s' p q := by
  rcases h with ⟨t, hts, ht⟩ | ⟨t, hts, ht⟩
  · exact Or.inl ⟨t, hts.trans hss, ht⟩
  · exact Or.inr ⟨t, hts.trans hss, ht⟩

/-- `R(2,q) ≤ q`. -/
lemma arr_two_left {G : SimpleGraph V} {s : Finset V} {q : ℕ} (hq : q ≤ s.card) :
    Arr G s 2 q := by
  by_cases hex : ∃ a ∈ s, ∃ b ∈ s, G.Adj a b
  · obtain ⟨a, ha, b, hb, hab⟩ := hex
    refine Or.inl ⟨{a, b}, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · simp [SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff, Set.pairwise_insert,
        hab, hab.symm, hab.ne]
  · push_neg at hex
    obtain ⟨t, hts, ht⟩ := Finset.exists_subset_card_eq hq
    refine Or.inr ⟨t, hts, ?_⟩
    rw [SimpleGraph.isNClique_iff]
    refine ⟨?_, ht⟩
    intro x hx y hy hxy
    exact ⟨hxy, hex x (hts hx) y (hts hy)⟩

lemma arr_two_right {G : SimpleGraph V} {s : Finset V} {p : ℕ} (hp : p ≤ s.card) :
    Arr G s p 2 := by
  rw [← arr_compl]
  exact arr_two_left hp

lemma arr_step_left {G : SimpleGraph V} {s A : Finset V} {v : V} (hv : v ∈ s) {p q : ℕ}
    (hA : ∀ u, u ∈ A ↔ u ∈ s ∧ G.Adj v u) (h : Arr G A p q) : Arr G s (p + 1) q := by
  have hAs : A ⊆ s := fun u hu => ((hA u).1 hu).1
  rcases h with ⟨t, hts, ht⟩ | ⟨t, hts, ht⟩
  · have hvt : v ∉ t := fun hvt => G.irrefl ((hA v).1 (hts hvt)).2
    refine Or.inl ⟨insert v t, ?_, ht.insert (fun b hb => ((hA b).1 (hts hb)).2)⟩
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hv
    · exact hAs (hts hx)
  · exact Or.inr ⟨t, hts.trans hAs, ht⟩

lemma arr_step_right {G : SimpleGraph V} {s B : Finset V} {v : V} (hv : v ∈ s) {p q : ℕ}
    (hB : ∀ u, u ∈ B ↔ u ∈ s ∧ Gᶜ.Adj v u) (h : Arr G B p (q)) : Arr G s p (q + 1) := by
  rw [← arr_compl]
  refine arr_step_left hv (A := B) ?_ ?_
  · intro u
    simpa using hB u
  · rw [arr_compl]
    exact h

lemma card_split {G : SimpleGraph V} {s A B : Finset V} {v : V} (hv : v ∈ s)
    (hA : ∀ u, u ∈ A ↔ u ∈ s ∧ G.Adj v u) (hB : ∀ u, u ∈ B ↔ u ∈ s ∧ Gᶜ.Adj v u) :
    A.card + B.card + 1 = s.card := by
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro u huA huB
    exact ((hB u).1 huB).2.2 ((hA u).1 huA).2
  have hunion : A ∪ B = s.erase v := by
    ext u
    simp only [Finset.mem_union, hA, hB, Finset.mem_erase, SimpleGraph.compl_adj]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
      · exact ⟨h2.ne', h1⟩
      · exact ⟨fun h => h2 h.symm, h1⟩
    · rintro ⟨h1, h2⟩
      by_cases hadj : G.Adj v u
      · exact Or.inl ⟨h2, hadj⟩
      · exact Or.inr ⟨h2, fun h => h1 h.symm, hadj⟩
  have hc := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.card_erase_of_mem hv] at hc
  have h1 : 1 ≤ s.card := Finset.card_pos.2 ⟨v, hv⟩
  omega

lemma even_sum_adj (G : SimpleGraph V) (s : Finset V) :
    Even (∑ v ∈ s, (s.filter (fun u => G.Adj v u)).card) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    have h1 : ((insert a t).filter (fun u => G.Adj a u)) = t.filter (fun u => G.Adj a u) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hu, h2⟩
        · exact absurd h2 (G.irrefl)
        · exact ⟨hu, h2⟩
      · rintro ⟨hu, h2⟩; exact ⟨Or.inr hu, h2⟩
    have h2 : ∀ v ∈ t, ((insert a t).filter (fun u => G.Adj v u)).card
        = (t.filter (fun u => G.Adj v u)).card + (if G.Adj v a then 1 else 0) := by
      intro v hv
      by_cases hva : G.Adj v a
      · have hins : ((insert a t).filter (fun u => G.Adj v u))
            = insert a (t.filter (fun u => G.Adj v u)) := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hu, h3⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨hu, h3⟩
          · rintro (rfl | ⟨hu, h3⟩)
            · exact ⟨Or.inl rfl, hva⟩
            · exact ⟨Or.inr hu, h3⟩
        rw [hins, Finset.card_insert_of_notMem (by simp [ha]), if_pos hva]
      · have hins : ((insert a t).filter (fun u => G.Adj v u))
            = t.filter (fun u => G.Adj v u) := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hu, h3⟩
            · exact absurd h3 hva
            · exact ⟨hu, h3⟩
          · rintro ⟨hu, h3⟩; exact ⟨Or.inr hu, h3⟩
        rw [hins, if_neg hva, Nat.add_zero]
    rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, h1]
    have h3 : (∑ v ∈ t, if G.Adj v a then 1 else 0) = (t.filter (fun u => G.Adj a u)).card := by
      rw [Finset.card_filter]
      exact Finset.sum_congr rfl fun x _ => by simp [SimpleGraph.adj_comm]
    rw [h3]
    rcases ih with ⟨k, hk⟩
    exact ⟨k + (t.filter (fun u => G.Adj a u)).card, by omega⟩

/-- `R(3,3) ≤ 6`. -/
lemma arr_33 {G : SimpleGraph V} {s : Finset V} (hs : 6 ≤ s.card) : Arr G s 3 3 := by
  obtain ⟨v, hv⟩ : s.Nonempty := Finset.card_pos.1 (by omega)
  set A := s.filter (fun u => G.Adj v u) with hAdef
  set B := s.filter (fun u => Gᶜ.Adj v u) with hBdef
  have hA : ∀ u, u ∈ A ↔ u ∈ s ∧ G.Adj v u := by intro u; rw [hAdef, Finset.mem_filter]
  have hB : ∀ u, u ∈ B ↔ u ∈ s ∧ Gᶜ.Adj v u := by intro u; rw [hBdef, Finset.mem_filter]
  have hcard := card_split hv hA hB
  rcases le_or_gt 3 A.card with h | h
  · exact arr_step_left hv hA (arr_two_left (q := 3) h)
  · exact arr_step_right hv hB (arr_two_right (p := 3) (by omega))

/-- `R(3,4) ≤ 9`, the key parity argument. -/
lemma arr_34_eq {G : SimpleGraph V} {s : Finset V} (hs : s.card = 9) : Arr G s 3 4 := by
  by_contra hcon
  have key : ∀ v ∈ s, (s.filter (fun u => G.Adj v u)).card = 3 := by
    intro v hv
    set A := s.filter (fun u => G.Adj v u) with hAdef
    set B := s.filter (fun u => Gᶜ.Adj v u) with hBdef
    have hA : ∀ u, u ∈ A ↔ u ∈ s ∧ G.Adj v u := by intro u; rw [hAdef, Finset.mem_filter]
    have hB : ∀ u, u ∈ B ↔ u ∈ s ∧ Gᶜ.Adj v u := by intro u; rw [hBdef, Finset.mem_filter]
    have hcard := card_split hv hA hB
    have hA3 : A.card ≤ 3 := by
      by_contra hlt
      push_neg at hlt
      exact hcon (arr_step_left hv hA (arr_two_left (q := 4) (by omega)))
    have hB5 : B.card ≤ 5 := by
      by_contra hlt
      push_neg at hlt
      exact hcon (arr_step_right hv hB (arr_33 (by omega)))
    omega
  have hsum : ∑ v ∈ s, (s.filter (fun u => G.Adj v u)).card = 27 := by
    rw [Finset.sum_congr rfl key, Finset.sum_const, hs]
    rfl
  have heven := even_sum_adj G s
  rw [hsum] at heven
  exact (by decide : ¬ Even 27) heven

lemma arr_34 {G : SimpleGraph V} {s : Finset V} (hs : 9 ≤ s.card) : Arr G s 3 4 := by
  obtain ⟨t, hts, ht⟩ := Finset.exists_subset_card_eq hs
  exact (arr_34_eq ht).mono hts

lemma arr_43 {G : SimpleGraph V} {s : Finset V} (hs : 9 ≤ s.card) : Arr G s 4 3 := by
  rw [← arr_compl]
  exact arr_34 hs

/-- `R(4,4) ≤ 18`. -/
lemma arr_44 {G : SimpleGraph V} {s : Finset V} (hs : 18 ≤ s.card) : Arr G s 4 4 := by
  obtain ⟨v, hv⟩ : s.Nonempty := Finset.card_pos.1 (by omega)
  set A := s.filter (fun u => G.Adj v u) with hAdef
  set B := s.filter (fun u => Gᶜ.Adj v u) with hBdef
  have hA : ∀ u, u ∈ A ↔ u ∈ s ∧ G.Adj v u := by intro u; rw [hAdef, Finset.mem_filter]
  have hB : ∀ u, u ∈ B ↔ u ∈ s ∧ Gᶜ.Adj v u := by intro u; rw [hBdef, Finset.mem_filter]
  have hcard := card_split hv hA hB
  rcases le_or_gt 9 A.card with h | h
  · exact arr_step_left hv hA (arr_34 h)
  · exact arr_step_right hv hB (arr_43 (by omega))

/-! ### The Paley graph on 17 vertices -/

/-- The nonzero quadratic residues mod 17. -/
def isQR (n : ℕ) : Bool :=
  n == 1 || n == 2 || n == 4 || n == 8 || n == 9 || n == 13 || n == 15 || n == 16

def paleyAdj (a b : ℕ) : Bool := isQR ((a + 17 - b) % 17)

lemma paleyAdj_symm : ∀ a < 17, ∀ b < 17, paleyAdj a b = paleyAdj b a := by decide

lemma paleyAdj_irrefl (a : ℕ) : paleyAdj a a = false := by
  simp [paleyAdj, isQR]

/-- The Paley graph on `Fin 17`. -/
def paley : SimpleGraph (Fin 17) where
  Adj a b := paleyAdj a.val b.val = true
  symm := by
    intro a b h
    rw [paleyAdj_symm b.val b.isLt a.val a.isLt]
    exact h
  loopless := ⟨fun a => by simp [paleyAdj_irrefl]⟩

def paleyCheck : Bool :=
  (List.range 17).all fun a => (List.range a).all fun b => (List.range b).all fun c =>
    (List.range c).all fun d =>
      !(paleyAdj a b && paleyAdj a c && paleyAdj a d && paleyAdj b c && paleyAdj b d &&
          paleyAdj c d) &&
      !(!paleyAdj a b && !paleyAdj a c && !paleyAdj a d && !paleyAdj b c && !paleyAdj b d &&
          !paleyAdj c d)

set_option maxRecDepth 100000 in
lemma paleyCheck_eq : paleyCheck = true := by decide

lemma paley_all {a b c d : ℕ} (ha : a < 17) (hb : b < a) (hc : c < b) (hd : d < c) :
    (!(paleyAdj a b && paleyAdj a c && paleyAdj a d && paleyAdj b c && paleyAdj b d &&
          paleyAdj c d) &&
      !(!paleyAdj a b && !paleyAdj a c && !paleyAdj a d && !paleyAdj b c && !paleyAdj b d &&
          !paleyAdj c d)) = true := by
  have h := paleyCheck_eq
  rw [paleyCheck, List.all_eq_true] at h
  have h1 := h a (List.mem_range.2 ha)
  rw [List.all_eq_true] at h1
  have h2 := h1 b (List.mem_range.2 hb)
  rw [List.all_eq_true] at h2
  have h3 := h2 c (List.mem_range.2 hc)
  rw [List.all_eq_true] at h3
  exact h3 d (List.mem_range.2 hd)

lemma paley_no_clique {a b c d : ℕ} (ha : a < 17) (hb : b < a) (hc : c < b) (hd : d < c)
    (h1 : paleyAdj a b = true) (h2 : paleyAdj a c = true) (h3 : paleyAdj a d = true)
    (h4 : paleyAdj b c = true) (h5 : paleyAdj b d = true) (h6 : paleyAdj c d = true) : False := by
  have h := paley_all ha hb hc hd
  simp [h1, h2, h3, h4, h5, h6] at h

lemma paley_no_indep {a b c d : ℕ} (ha : a < 17) (hb : b < a) (hc : c < b) (hd : d < c)
    (h1 : paleyAdj a b = false) (h2 : paleyAdj a c = false) (h3 : paleyAdj a d = false)
    (h4 : paleyAdj b c = false) (h5 : paleyAdj b d = false) (h6 : paleyAdj c d = false) :
    False := by
  have h := paley_all ha hb hc hd
  simp [h1, h2, h3, h4, h5, h6] at h

lemma exists_four_sorted {s : Finset (Fin 17)} (hs : s.card = 4) :
    ∃ a b c d : Fin 17, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ d ∈ s ∧
      d.val < c.val ∧ c.val < b.val ∧ b.val < a.val := by
  set e := s.orderIsoOfFin hs with he
  have key : ∀ i j : Fin 4, i < j → ((e i : Fin 17)).val < ((e j : Fin 17)).val := by
    intro i j hij
    exact e.lt_iff_lt.2 hij
  exact ⟨e 3, e 2, e 1, e 0, (e 3).2, (e 2).2, (e 1).2, (e 0).2,
    key 0 1 (by decide), key 1 2 (by decide), key 2 3 (by decide)⟩

lemma paley_cliqueFree : ∀ s : Finset (Fin 17), ¬ paley.IsNClique 4 s := by
  intro s hs
  obtain ⟨hcl, hcard⟩ := (SimpleGraph.isNClique_iff _).1 hs
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hdc, hcb, hba⟩ := exists_four_sorted hcard
  have adj : ∀ x y : Fin 17, x ∈ s → y ∈ s → x.val ≠ y.val → paleyAdj x.val y.val = true :=
    fun x y hx hy hxy =>
      hcl (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hy) (fun h => hxy (by rw [h]))
  exact paley_no_clique a.isLt hba hcb hdc (adj a b ha hb (by omega)) (adj a c ha hc (by omega))
    (adj a d ha hd (by omega)) (adj b c hb hc (by omega)) (adj b d hb hd (by omega))
    (adj c d hc hd (by omega))

lemma paley_compl_cliqueFree : ∀ s : Finset (Fin 17), ¬ paleyᶜ.IsNClique 4 s := by
  intro s hs
  obtain ⟨hcl, hcard⟩ := (SimpleGraph.isNClique_iff _).1 hs
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hdc, hcb, hba⟩ := exists_four_sorted hcard
  have adj : ∀ x y : Fin 17, x ∈ s → y ∈ s → x.val ≠ y.val → paleyAdj x.val y.val = false := by
    intro x y hx hy hxy
    have h := hcl (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hy) (fun h => hxy (by rw [h]))
    rw [SimpleGraph.compl_adj] at h
    simpa [paley] using h.2
  exact paley_no_indep a.isLt hba hcb hdc (adj a b ha hb (by omega)) (adj a c ha hc (by omega))
    (adj a d ha hd (by omega)) (adj b c hb hc (by omega)) (adj b d hb hd (by omega))
    (adj c d hc hd (by omega))

/-! ### Monotonicity in the number of vertices -/

def RamseyProp (N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    (∃ s : Finset (Fin N), G.IsNClique 4 s) ∨ (∃ s : Finset (Fin N), Gᶜ.IsNClique 4 s)

lemma clique_image {N M : ℕ} {f : Fin N → Fin M} (hf : Function.Injective f)
    {G : SimpleGraph (Fin M)} {s : Finset (Fin N)} {n : ℕ}
    (hs : (SimpleGraph.comap f G).IsNClique n s) : G.IsNClique n (s.image f) := by
  obtain ⟨hcl, hcard⟩ := (SimpleGraph.isNClique_iff _).1 hs
  rw [SimpleGraph.isNClique_iff]
  constructor
  · intro x hx y hy hxy
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    exact hcl (Finset.mem_coe.2 hx') (Finset.mem_coe.2 hy') (fun h => hxy (by rw [h]))
  · rw [Finset.card_image_of_injective _ hf, hcard]

lemma ramseyProp_mono {N M : ℕ} (hNM : N ≤ M) (h : RamseyProp N) : RamseyProp M := by
  intro G
  have hf : Function.Injective (Fin.castLE hNM) := Fin.castLE_injective hNM
  rcases h (SimpleGraph.comap (Fin.castLE hNM) G) with ⟨s, hs⟩ | ⟨s, hs⟩
  · exact Or.inl ⟨_, clique_image hf hs⟩
  · refine Or.inr ⟨_, clique_image (G := Gᶜ) hf (hs.mono ?_)⟩
    intro x y hxy
    rw [SimpleGraph.compl_adj] at hxy
    rw [SimpleGraph.comap_adj, SimpleGraph.compl_adj]
    exact ⟨fun h => hxy.1 (hf h), hxy.2⟩

end Ramsey44

open Ramsey44 in
/-- The two-colour Ramsey number `R(4,4)` equals `18`: `18` is the least `N` such that every
graph on `N` vertices contains a clique of size `4` or an independent set of size `4`. -/
theorem Math.ramsey_4_4 :
    IsLeast {N : ℕ | ∀ G : SimpleGraph (Fin N),
      (∃ s : Finset (Fin N), G.IsNClique 4 s) ∨ (∃ s : Finset (Fin N), Gᶜ.IsNClique 4 s)} 18 := by
  constructor
  · intro G
    rcases arr_44 (s := (Finset.univ : Finset (Fin 18))) (G := G) (by simp) with
      ⟨t, _, ht⟩ | ⟨t, _, ht⟩
    · exact Or.inl ⟨t, ht⟩
    · exact Or.inr ⟨t, ht⟩
  · intro N hN
    by_contra hlt
    have hN17 : N ≤ 17 := by omega
    have := ramseyProp_mono hN17 hN
    rcases this paley with ⟨s, hs⟩ | ⟨s, hs⟩
    · exact paley_cliqueFree s hs
    · exact paley_compl_cliqueFree s hs

