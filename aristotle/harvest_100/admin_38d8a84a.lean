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
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000

namespace Math

/-! ## Basic notions: cliques and independent sets relative to a finite vertex set -/

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- `IsCl G t` says that the finite set `t` is a clique of `G`. -/
def IsCl (G : SimpleGraph V) (t : Finset V) : Prop :=
  ∀ a ∈ t, ∀ b ∈ t, a ≠ b → G.Adj a b

/-- `IsInd G t` says that the finite set `t` is an independent set of `G`. -/
def IsInd (G : SimpleGraph V) (t : Finset V) : Prop :=
  ∀ a ∈ t, ∀ b ∈ t, a ≠ b → ¬ G.Adj a b

/-- `Arrow G s k` : inside the vertex set `s` there is a triangle of `G` or an
independent set of `G` of size `k`. -/
def Arrow (G : SimpleGraph V) (s : Finset V) (k : ℕ) : Prop :=
  (∃ t ⊆ s, t.card = 3 ∧ IsCl G t) ∨ (∃ t ⊆ s, t.card = k ∧ IsInd G t)

omit [DecidableEq V] in
lemma IsInd.subset {t t' : Finset V} (h : IsInd G t) (hsub : t' ⊆ t) : IsInd G t' :=
  fun a ha b hb hab => h a (hsub ha) b (hsub hb) hab

omit [DecidableEq V] in
lemma Arrow.mono {s s' : Finset V} {k : ℕ} (h : Arrow G s k) (hs : s ⊆ s') : Arrow G s' k := by
  rcases h with ⟨t, ht, h⟩ | ⟨t, ht, h⟩
  · exact Or.inl ⟨t, ht.trans hs, h⟩
  · exact Or.inr ⟨t, ht.trans hs, h⟩

section Deg

variable [DecidableRel G.Adj]

/-- The neighbours of `v` inside `s`. -/
def Nb (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) (v : V) : Finset V :=
  s.filter (fun u => G.Adj v u)

/-- The non-neighbours of `v` inside `s`, excluding `v` itself. -/
def Mb (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) (v : V) : Finset V :=
  (s.erase v).filter (fun u => ¬ G.Adj v u)

omit [DecidableEq V] in
lemma Nb_subset {s : Finset V} {v : V} : Nb G s v ⊆ s := Finset.filter_subset _ _

lemma Mb_subset {s : Finset V} {v : V} : Mb G s v ⊆ s :=
  (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)

lemma card_Nb_add_card_Mb {s : Finset V} {v : V} (hv : v ∈ s) :
    (Nb G s v).card + (Mb G s v).card = s.card - 1 := by
  have h1 : Nb G s v = (s.erase v).filter (fun u => G.Adj v u) := by
    unfold Nb
    ext u
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hu, hadj⟩
      exact ⟨⟨fun h => G.irrefl (h ▸ hadj), hu⟩, hadj⟩
    · rintro ⟨⟨_, hu⟩, hadj⟩
      exact ⟨hu, hadj⟩
  rw [h1]
  unfold Mb
  rw [Finset.card_filter_add_card_filter_not (p := fun u => G.Adj v u),
    Finset.card_erase_of_mem hv]

/-- If `v` has at least `k` neighbours in `s` and there is no triangle in `s`, then
there is an independent set of size `k` inside `s`. -/
lemma indep_of_card_Nb {s : Finset V} {v : V} (hv : v ∈ s) {k : ℕ}
    (hk : k ≤ (Nb G s v).card)
    (hno : ¬ ∃ t ⊆ s, t.card = 3 ∧ IsCl G t) :
    ∃ t ⊆ s, t.card = k ∧ IsInd G t := by
  have hNind : IsInd G (Nb G s v) := by
    intro a ha b hb hab hadj
    simp only [Nb, Finset.mem_filter] at ha hb
    refine hno ⟨{v, a, b}, ?_, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hv
      · exact ha.1
      · exact hb.1
    · have hva : v ≠ a := fun h => G.irrefl (h ▸ ha.2)
      have hvb : v ≠ b := fun h => G.irrefl (h ▸ hb.2)
      rw [Finset.card_insert_of_notMem (by simp [hva, hvb]),
        Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
    · intro x hx y hy hxy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        first
          | exact absurd rfl hxy
          | exact ha.2
          | exact hb.2
          | exact ha.2.symm
          | exact hb.2.symm
          | exact hadj
          | exact hadj.symm
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hk
  exact ⟨t, hts.trans Nb_subset, htc, hNind.subset hts⟩

/-- Adding `v` to an independent set of non-neighbours of `v` keeps it independent. -/
lemma indep_insert {s : Finset V} {v : V} (hv : v ∈ s) {T : Finset V}
    (hT : T ⊆ Mb G s v) (hTind : IsInd G T) :
    ∃ t ⊆ s, t.card = T.card + 1 ∧ IsInd G t := by
  have hvT : v ∉ T := by
    intro h
    have := hT h
    simp [Mb, Finset.mem_filter, Finset.mem_erase] at this
  refine ⟨insert v T, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hv
    · exact Mb_subset (hT hx)
  · rw [Finset.card_insert_of_notMem hvT]
  · intro a ha b hb hab
    have key : ∀ c ∈ T, ¬ G.Adj v c := by
      intro c hc
      have := hT hc
      simp only [Mb, Finset.mem_filter, Finset.mem_erase] at this
      exact this.2
    rw [Finset.mem_insert] at ha hb
    rcases ha with ha | ha
    · rcases hb with hb | hb
      · exact absurd (ha.trans hb.symm) hab
      · subst ha; exact key b hb
    · rcases hb with hb | hb
      · subst hb; exact fun h => key a ha h.symm
      · exact hTind a ha b hb hab

/-! ## The handshake parity lemma -/

lemma even_sum_deg (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) :
    Even (∑ v ∈ s, (Nb G s v).card) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfa : Nb G (insert a s) a = Nb G s a := by
      unfold Nb
      rw [Finset.filter_insert, if_neg G.irrefl]
    have hd : ∀ v ∈ s, (Nb G (insert a s) v).card
        = (Nb G s v).card + (if G.Adj v a then 1 else 0) := by
      intro v _
      unfold Nb
      rw [Finset.filter_insert]
      by_cases h : G.Adj v a
      · rw [if_pos h, if_pos h,
          Finset.card_insert_of_notMem (fun hmem => ha (Finset.mem_filter.mp hmem).1)]
      · rw [if_neg h, if_neg h, Nat.add_zero]
    have hswap : ∑ v ∈ s, (if G.Adj v a then 1 else 0) = (Nb G s a).card := by
      rw [Nb, Finset.card_filter]
      exact Finset.sum_congr rfl
        (fun v _ => if_congr ⟨fun h => h.symm, fun h => h.symm⟩ rfl rfl)
    rw [Finset.sum_insert ha, hfa, Finset.sum_congr rfl hd, Finset.sum_add_distrib, hswap]
    obtain ⟨m, hm⟩ := ih
    exact ⟨m + (Nb G s a).card, by omega⟩

end Deg

/-! ## The Ramsey upper bounds -/

/-- `R(3,2) ≤ 3`: three vertices contain a triangle or two non-adjacent vertices. -/
lemma r32 [DecidableRel G.Adj] {s : Finset V} (hs : 3 ≤ s.card) : Arrow G s 2 := by
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hs
  by_cases h : IsCl G t
  · exact Or.inl ⟨t, hts, htc, h⟩
  · unfold IsCl at h
    push_neg at h
    obtain ⟨a, ha, b, hb, hab, hadj⟩ := h
    refine Or.inr ⟨{a, b}, ?_, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hts ha
      · exact hts hb
    · rw [Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
    · intro x hx y hy hxy
      rw [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · exact hadj
      · exact fun h => hadj h.symm
      · exact absurd rfl hxy

/-- `R(3,3) ≤ 6`. -/
lemma r33 [DecidableRel G.Adj] {s : Finset V} (hs : 6 ≤ s.card) : Arrow G s 3 := by
  by_cases hno : ∃ t ⊆ s, t.card = 3 ∧ IsCl G t
  · exact Or.inl hno
  obtain ⟨v, hv⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
  by_cases hN : 3 ≤ (Nb G s v).card
  · exact Or.inr (indep_of_card_Nb hv hN hno)
  push_neg at hN
  have hsplit := card_Nb_add_card_Mb (G := G) hv
  have hM : 3 ≤ (Mb G s v).card := by omega
  rcases r32 (G := G) hM with ⟨t, ht, htc, hti⟩ | ⟨t, ht, htc, hti⟩
  · exact absurd ⟨t, ht.trans Mb_subset, htc, hti⟩ hno
  · obtain ⟨u, hu, huc, hui⟩ := indep_insert hv ht hti
    exact Or.inr ⟨u, hu, by omega, hui⟩

/-- `R(3,4) ≤ 9`.  The bound `9` (rather than the easy `10`) comes from the parity
of the degree sum: a triangle-free graph on `9` vertices with no independent set of
size `4` would have to be `3`-regular, which is impossible. -/
lemma r34 [DecidableRel G.Adj] {s : Finset V} (hs : 9 ≤ s.card) : Arrow G s 4 := by
  by_contra hcon
  rw [Arrow, not_or] at hcon
  obtain ⟨hno, hnoind⟩ := hcon
  obtain ⟨s', hs's, hs'card⟩ := Finset.exists_subset_card_eq hs
  have hno' : ¬ ∃ t ⊆ s', t.card = 3 ∧ IsCl G t := by
    rintro ⟨t, ht, h⟩
    exact hno ⟨t, ht.trans hs's, h⟩
  have hnoind' : ∀ t ⊆ s', t.card = 4 → ¬ IsInd G t := by
    intro t ht hc hi
    exact hnoind ⟨t, ht.trans hs's, hc, hi⟩
  have hdeg : ∀ v ∈ s', (Nb G s' v).card = 3 := by
    intro v hv
    have hsplit := card_Nb_add_card_Mb (G := G) hv
    have hle : (Nb G s' v).card ≤ 3 := by
      by_contra hgt
      push_neg at hgt
      obtain ⟨t, ht, htc, hti⟩ := indep_of_card_Nb hv (k := 4) (by omega) hno'
      exact hnoind' t ht htc hti
    have hge : 3 ≤ (Nb G s' v).card := by
      by_contra hlt
      push_neg at hlt
      have hM : 6 ≤ (Mb G s' v).card := by omega
      rcases r33 (G := G) hM with ⟨t, ht, htc, hti⟩ | ⟨t, ht, htc, hti⟩
      · exact hno' ⟨t, ht.trans Mb_subset, htc, hti⟩
      · obtain ⟨u, hu, huc, hui⟩ := indep_insert hv ht hti
        exact hnoind' u hu (by omega) hui
    omega
  have hsum : ∑ v ∈ s', (Nb G s' v).card = 27 := by
    rw [Finset.sum_congr rfl hdeg, Finset.sum_const, hs'card, smul_eq_mul]
  have hev := even_sum_deg G s'
  rw [hsum] at hev
  exact (by decide : ¬ Even 27) hev

/-- `R(3,5) ≤ 14`. -/
lemma r35 [DecidableRel G.Adj] {s : Finset V} (hs : 14 ≤ s.card) : Arrow G s 5 := by
  by_cases hno : ∃ t ⊆ s, t.card = 3 ∧ IsCl G t
  · exact Or.inl hno
  obtain ⟨v, hv⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
  by_cases hN : 5 ≤ (Nb G s v).card
  · exact Or.inr (indep_of_card_Nb hv hN hno)
  push_neg at hN
  have hsplit := card_Nb_add_card_Mb (G := G) hv
  have hM : 9 ≤ (Mb G s v).card := by omega
  rcases r34 (G := G) hM with ⟨t, ht, htc, hti⟩ | ⟨t, ht, htc, hti⟩
  · exact absurd ⟨t, ht.trans Mb_subset, htc, hti⟩ hno
  · obtain ⟨u, hu, huc, hui⟩ := indep_insert hv ht hti
    exact Or.inr ⟨u, hu, by omega, hui⟩

/-! ## The lower bound: an explicit graph on 13 vertices -/

/-- Adjacency of the circulant graph `C₁₃(1,5)`. -/
def cAdj (i j : Fin 13) : Bool :=
  ((i.val + 1) % 13 == j.val) || ((j.val + 1) % 13 == i.val) ||
  ((i.val + 5) % 13 == j.val) || ((j.val + 5) % 13 == i.val)

/-- The circulant graph `C₁₃(1,5)`: triangle-free with independence number `4`. -/
def C13 : SimpleGraph (Fin 13) where
  Adj i j := cAdj i j = true
  symm := by
    have h : ∀ i j : Fin 13, cAdj i j = true → cAdj j i = true := by decide
    intro i j hij
    exact h i j hij
  loopless := by
    have h : ∀ i : Fin 13, cAdj i i = false := by decide
    refine ⟨?_⟩
    intro i hi
    rw [h i] at hi
    exact Bool.false_ne_true hi

lemma C13_adj_iff (i j : Fin 13) : C13.Adj i j ↔ cAdj i j = true := Iff.rfl

/-- `C₁₃(1,5)` contains no triangle. -/
theorem C13_triangle_free : ∀ t : Finset (Fin 13), t.card = 3 → ¬ IsCl C13 t := by
  have key : ∀ a b c : Fin 13, a < b → b < c →
      ¬ (cAdj a b = true ∧ cAdj b c = true ∧ cAdj a c = true) := by decide
  intro t hc hcl
  have hm := t.orderEmbOfFin_mem hc
  have hmono := (t.orderEmbOfFin hc).strictMono
  set f := t.orderEmbOfFin hc with hf
  exact key (f 0) (f 1) (f 2) (hmono (by decide)) (hmono (by decide))
    ⟨hcl _ (hm 0) _ (hm 1) (ne_of_lt (hmono (by decide))),
     hcl _ (hm 1) _ (hm 2) (ne_of_lt (hmono (by decide))),
     hcl _ (hm 0) _ (hm 2) (ne_of_lt (hmono (by decide)))⟩

/-- `C₁₃(1,5)` contains no independent set of size `5`. -/
theorem C13_no_indep5 : ∀ t : Finset (Fin 13), t.card = 5 → ¬ IsInd C13 t := by
  have key : ∀ a b : Fin 13, a < b → cAdj a b = false →
      ∀ c : Fin 13, b < c → cAdj a c = false → cAdj b c = false →
      ∀ d : Fin 13, c < d → cAdj a d = false → cAdj b d = false → cAdj c d = false →
      ∀ e : Fin 13, d < e → cAdj a e = false → cAdj b e = false → cAdj c e = false →
        cAdj d e = false → False := by decide
  intro t hc hind
  have hm := t.orderEmbOfFin_mem hc
  have hmono := (t.orderEmbOfFin hc).strictMono
  set f := t.orderEmbOfFin hc with hf
  have hadj : ∀ i j : Fin 5, i < j → cAdj (f i) (f j) = false := by
    intro i j hij
    have h := hind _ (hm i) _ (hm j) (ne_of_lt (hmono hij))
    simpa [C13_adj_iff] using h
  exact key (f 0) (f 1) (hmono (by decide)) (hadj 0 1 (by decide))
    (f 2) (hmono (by decide)) (hadj 0 2 (by decide)) (hadj 1 2 (by decide))
    (f 3) (hmono (by decide)) (hadj 0 3 (by decide)) (hadj 1 3 (by decide))
      (hadj 2 3 (by decide))
    (f 4) (hmono (by decide)) (hadj 0 4 (by decide)) (hadj 1 4 (by decide))
      (hadj 2 4 (by decide)) (hadj 3 4 (by decide))

/-! ## The main theorem -/

/-- **The Ramsey number `R(3,5)` equals `14`**: `14` is the least `n` such that every
graph on `n` vertices contains a triangle or an independent set of size `5`. -/
theorem ramsey_3_5 :
    IsLeast {n : ℕ | ∀ G : SimpleGraph (Fin n),
      (∃ t : Finset (Fin n), t.card = 3 ∧ IsCl G t) ∨
      (∃ t : Finset (Fin n), t.card = 5 ∧ IsInd G t)} 14 := by
  constructor
  · intro G
    classical
    have hcard : (Finset.univ : Finset (Fin 14)).card = 14 := by simp
    rcases r35 (G := G) (s := Finset.univ) (by omega) with
      ⟨t, _, htc, hti⟩ | ⟨t, _, htc, hti⟩
    · exact Or.inl ⟨t, htc, hti⟩
    · exact Or.inr ⟨t, htc, hti⟩
  · intro n hn
    by_contra hlt
    push_neg at hlt
    have hn13 : n ≤ 13 := by omega
    have hinj : Function.Injective (Fin.castLE hn13) := (Fin.castLEEmb hn13).injective
    rcases hn (SimpleGraph.comap (Fin.castLE hn13) C13) with ⟨t, htc, hti⟩ | ⟨t, htc, hti⟩
    · refine C13_triangle_free (t.map ⟨Fin.castLE hn13, hinj⟩) (by simpa using htc) ?_
      intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
      simp only [Function.Embedding.coeFn_mk] at hxy ⊢
      exact hti a ha b hb (fun h => hxy (by rw [h]))
    · refine C13_no_indep5 (t.map ⟨Fin.castLE hn13, hinj⟩) (by simpa using htc) ?_
      intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
      simp only [Function.Embedding.coeFn_mk] at hxy ⊢
      exact hti a ha b hb (fun h => hxy (by rw [h]))

/-! ## Restatement in Mathlib's vocabulary -/

omit [DecidableEq V] in
lemma isCl_iff {t : Finset V} : IsCl G t ↔ G.IsClique (t : Set V) := by
  constructor
  · intro h a ha b hb hab
    exact h a ha b hb hab
  · intro h a ha b hb hab
    exact h ha hb hab

omit [DecidableEq V] in
lemma isInd_iff {t : Finset V} : IsInd G t ↔ G.IsIndepSet (t : Set V) := by
  constructor
  · intro h a ha b hb hab
    exact h a ha b hb hab
  · intro h a ha b hb hab
    exact h ha hb hab

/-- **`R(3,5) = 14`**, phrased with Mathlib's `IsNClique` and `IsNIndepSet`. -/
theorem ramsey_3_5' :
    IsLeast {n : ℕ | ∀ G : SimpleGraph (Fin n),
      (∃ t : Finset (Fin n), G.IsNClique 3 t) ∨
      (∃ t : Finset (Fin n), G.IsNIndepSet 5 t)} 14 := by
  obtain ⟨hmem, hlb⟩ := ramsey_3_5
  constructor
  · intro G
    rcases hmem G with ⟨t, htc, hti⟩ | ⟨t, htc, hti⟩
    · exact Or.inl ⟨t, isCl_iff.mp hti, htc⟩
    · exact Or.inr ⟨t, isInd_iff.mp hti, htc⟩
  · intro n hn
    refine hlb (fun G => ?_)
    rcases hn G with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact Or.inl ⟨t, ht.2, isCl_iff.mpr ht.1⟩
    · exact Or.inr ⟨t, ht.2, isInd_iff.mpr ht.1⟩

end Math

