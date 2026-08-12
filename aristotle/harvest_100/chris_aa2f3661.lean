import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

/-! ## Cliques and independent sets inside a finite set of vertices -/

section General

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {s t : Finset V} {n : ℕ} {v : V}

/-- `CliqueOn G s n` : the vertex set `s` contains a clique of `G` with `n` vertices. -/
def CliqueOn (G : SimpleGraph V) (s : Finset V) (n : ℕ) : Prop :=
  ∃ A ⊆ s, A.card = n ∧ G.IsClique (A : Set V)

/-- `IndepOn G s n` : the vertex set `s` contains an independent set of `G` with `n` vertices. -/
def IndepOn (G : SimpleGraph V) (s : Finset V) (n : ℕ) : Prop :=
  ∃ B ⊆ s, B.card = n ∧ G.IsIndepSet (B : Set V)

omit [DecidableEq V] in
lemma CliqueOn.mono (hst : s ⊆ t) (h : CliqueOn G s n) : CliqueOn G t n := by
  obtain ⟨A, hA, hcard, hcl⟩ := h
  exact ⟨A, hA.trans hst, hcard, hcl⟩

omit [DecidableEq V] in
lemma IndepOn.mono (hst : s ⊆ t) (h : IndepOn G s n) : IndepOn G t n := by
  obtain ⟨B, hB, hcard, hind⟩ := h
  exact ⟨B, hB.trans hst, hcard, hind⟩

omit [DecidableEq V] in
lemma cliqueOn_of_clique {A : Finset V} (hA : A ⊆ s) (hcl : G.IsClique (A : Set V))
    (hn : n ≤ A.card) : CliqueOn G s n := by
  obtain ⟨B, hB, hcard⟩ := Finset.exists_subset_card_eq hn
  exact ⟨B, hB.trans hA, hcard, Set.Pairwise.mono (by exact_mod_cast hB) hcl⟩

omit [DecidableEq V] in
lemma indepOn_of_indep {A : Finset V} (hA : A ⊆ s) (hind : G.IsIndepSet (A : Set V))
    (hn : n ≤ A.card) : IndepOn G s n := by
  obtain ⟨B, hB, hcard⟩ := Finset.exists_subset_card_eq hn
  exact ⟨B, hB.trans hA, hcard, hind.mono (by exact_mod_cast hB)⟩

/-- The neighbours of `v` inside `s`. -/
def nbrs (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) (v : V) : Finset V :=
  s.filter (fun w => G.Adj v w)

/-- The vertices of `s`, other than `v`, that are not adjacent to `v`. -/
def nonnbrs (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) (v : V) : Finset V :=
  (s.erase v).filter (fun w => ¬ G.Adj v w)

variable [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma nbrs_subset : nbrs G s v ⊆ s := Finset.filter_subset _ _

lemma nonnbrs_subset : nonnbrs G s v ⊆ s :=
  (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)

omit [DecidableEq V] in
lemma mem_nbrs {v w : V} : w ∈ nbrs G s v ↔ w ∈ s ∧ G.Adj v w := by
  simp [nbrs]

lemma mem_nonnbrs {v w : V} : w ∈ nonnbrs G s v ↔ (w ∈ s ∧ w ≠ v) ∧ ¬ G.Adj v w := by
  simp [nonnbrs, and_comm]

lemma card_nbrs_add_card_nonnbrs {v : V} (hv : v ∈ s) :
    (nbrs G s v).card + (nonnbrs G s v).card = s.card - 1 := by
  have h1 : (s.erase v).filter (fun w => G.Adj v w) = nbrs G s v := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_erase, mem_nbrs]
    constructor
    · rintro ⟨⟨-, hw⟩, ha⟩; exact ⟨hw, ha⟩
    · rintro ⟨hw, ha⟩
      exact ⟨⟨fun h => G.irrefl (h ▸ ha), hw⟩, ha⟩
  have h2 := Finset.card_filter_add_card_filter_not
    (s := s.erase v) (p := fun w => G.Adj v w)
  rw [h1] at h2
  rw [show (nonnbrs G s v) = (s.erase v).filter (fun w => ¬ G.Adj v w) from rfl, h2,
    Finset.card_erase_of_mem hv]

/-- If `s` contains no triangle then the neighbourhood of `v` in `s` is independent. -/
lemma isIndepSet_nbrs {v : V} (hv : v ∈ s) (h3 : ¬ CliqueOn G s 3) :
    G.IsIndepSet ((nbrs G s v : Finset V) : Set V) := by
  intro x hx y hy hxy hadj
  simp only [Finset.coe_filter, Set.mem_setOf_eq, nbrs] at hx hy
  refine h3 (cliqueOn_of_clique (A := {v, x, y}) ?_ ?_ ?_)
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact hv
    · exact hx.1
    · exact hy.1
  · have hvx : v ≠ x := fun h => G.irrefl (h ▸ hx.2)
    have hvy : v ≠ y := fun h => G.irrefl (h ▸ hy.2)
    intro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hab
        | exact hx.2
        | exact hy.2
        | exact hadj
        | exact hx.2.symm
        | exact hy.2.symm
        | exact hadj.symm
  · have hvx : v ≠ x := fun h => G.irrefl (h ▸ hx.2)
    have hvy : v ≠ y := fun h => G.irrefl (h ▸ hy.2)
    rw [Finset.card_insert_of_notMem (by simp [hvx, hvy]),
      Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]

/-- Adding `v` to an independent set of non-neighbours of `v` keeps it independent. -/
lemma indepOn_insert {v : V} (hv : v ∈ s) {B : Finset V} (hB : B ⊆ nonnbrs G s v)
    (hind : G.IsIndepSet (B : Set V)) : IndepOn G s (B.card + 1) := by
  have hvB : v ∉ B := by
    intro h
    have := mem_nonnbrs.mp (hB h)
    exact this.1.2 rfl
  refine ⟨insert v B, ?_, ?_, ?_⟩
  · intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hv
    · exact nonnbrs_subset (hB hw)
  · rw [Finset.card_insert_of_notMem hvB]
  · intro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact (mem_nonnbrs.mp (hB (by exact_mod_cast hb))).2
    · rcases hb with rfl | hb
      · exact fun h => (mem_nonnbrs.mp (hB (by exact_mod_cast ha))).2 h.symm
      · exact hind ha hb hab

end General

/-! ## Handshake parity -/

section Parity

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The sum of the degrees inside a finite vertex set is even. -/
lemma even_sum_card_nbrs (s : Finset V) :
    Even (∑ v ∈ s, (nbrs G s v).card) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      have key : ∀ v ∈ t, (nbrs G (insert a t) v).card
          = (nbrs G t v).card + (if G.Adj v a then 1 else 0) := by
        intro v _
        by_cases h : G.Adj v a
        · have : nbrs G (insert a t) v = insert a (nbrs G t v) := by
            ext w; simp only [mem_nbrs, Finset.mem_insert]
            constructor
            · rintro ⟨rfl | hw, hadj⟩
              · exact Or.inl rfl
              · exact Or.inr ⟨hw, hadj⟩
            · rintro (rfl | ⟨hw, hadj⟩)
              · exact ⟨Or.inl rfl, h⟩
              · exact ⟨Or.inr hw, hadj⟩
          rw [this, Finset.card_insert_of_notMem (fun hmem => ha (mem_nbrs.mp hmem).1), if_pos h]
        · have : nbrs G (insert a t) v = nbrs G t v := by
            ext w; simp only [mem_nbrs, Finset.mem_insert]
            constructor
            · rintro ⟨rfl | hw, hadj⟩
              · exact absurd hadj h
              · exact ⟨hw, hadj⟩
            · rintro ⟨hw, hadj⟩; exact ⟨Or.inr hw, hadj⟩
          rw [this, if_neg h, Nat.add_zero]
      have hA : (nbrs G (insert a t) a).card = (nbrs G t a).card := by
        congr 1
        ext w; simp only [mem_nbrs, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hw, hadj⟩
          · exact absurd hadj G.irrefl
          · exact ⟨hw, hadj⟩
        · rintro ⟨hw, hadj⟩; exact ⟨Or.inr hw, hadj⟩
      rw [Finset.sum_insert ha, Finset.sum_congr rfl key, Finset.sum_add_distrib, hA]
      have hfin : ∑ v ∈ t, (if G.Adj v a then 1 else 0) = (nbrs G t a).card := by
        rw [nbrs, Finset.card_filter]
        refine Finset.sum_congr rfl fun w _ => ?_
        simp only [G.adj_comm w a]
      rw [hfin]
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + (nbrs G t a).card, by omega⟩

end Parity

/-! ## The upper bounds -/

section Bounds

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {s : Finset V}

lemma ramsey_3_3_le (hs : 6 ≤ s.card) : CliqueOn G s 3 ∨ IndepOn G s 3 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h3, h3'⟩ := hcon
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := hne
  have hNi : G.IsIndepSet ((nbrs G s v : Finset V) : Set V) := isIndepSet_nbrs hv h3
  have hNcard : (nbrs G s v).card ≤ 2 := by
    by_contra hc
    exact h3' (indepOn_of_indep nbrs_subset hNi (by omega))
  have hsum := card_nbrs_add_card_nonnbrs (G := G) (s := s) hv
  have hMcard : 3 ≤ (nonnbrs G s v).card := by omega
  -- the non-neighbourhood must be a clique
  have hMcl : G.IsClique ((nonnbrs G s v : Finset V) : Set V) := by
    intro x hx y hy hxy
    by_contra hadj
    have hsub : ({x, y} : Finset V) ⊆ nonnbrs G s v := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact_mod_cast hx
      · exact_mod_cast hy
    have hind : G.IsIndepSet ((({x, y} : Finset V) : Finset V) : Set V) := by
      intro a ha b hb hab
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
        Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact hadj
      · exact fun h => hadj h.symm
      · exact absurd rfl hab
    have hres := indepOn_insert hv hsub hind
    rw [Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton] at hres
    exact h3' hres
  exact h3 (cliqueOn_of_clique nonnbrs_subset hMcl hMcard)

lemma ramsey_3_4_le_of_card_eq (hs : s.card = 9) : CliqueOn G s 3 ∨ IndepOn G s 4 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h3, h4⟩ := hcon
  -- every vertex of `s` has exactly 3 neighbours in `s`
  have hdeg : ∀ v ∈ s, (nbrs G s v).card = 3 := by
    intro v hv
    have hNi : G.IsIndepSet ((nbrs G s v : Finset V) : Set V) := isIndepSet_nbrs hv h3
    have hle : (nbrs G s v).card ≤ 3 := by
      by_contra hc
      exact h4 (indepOn_of_indep nbrs_subset hNi (by omega))
    have hsum := card_nbrs_add_card_nonnbrs (G := G) (s := s) hv
    have hge : 3 ≤ (nbrs G s v).card := by
      by_contra hc
      have hM : 6 ≤ (nonnbrs G s v).card := by omega
      rcases ramsey_3_3_le (G := G) (s := nonnbrs G s v) hM with hcl | hind
      · exact h3 (hcl.mono nonnbrs_subset)
      · obtain ⟨B, hB, hBcard, hBind⟩ := hind
        have := indepOn_insert hv hB hBind
        rw [hBcard] at this
        exact h4 this
    omega
  have heven := even_sum_card_nbrs G s
  rw [Finset.sum_congr rfl hdeg, Finset.sum_const, hs] at heven
  simp only [smul_eq_mul] at heven
  obtain ⟨k, hk⟩ := heven
  omega

lemma ramsey_3_4_le (hs : 9 ≤ s.card) : CliqueOn G s 3 ∨ IndepOn G s 4 := by
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq hs
  rcases ramsey_3_4_le_of_card_eq (G := G) (s := t) htcard with h | h
  · exact Or.inl (h.mono hts)
  · exact Or.inr (h.mono hts)

lemma ramsey_3_5_le (hs : 14 ≤ s.card) : CliqueOn G s 3 ∨ IndepOn G s 5 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h3, h5⟩ := hcon
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := hne
  have hNi : G.IsIndepSet ((nbrs G s v : Finset V) : Set V) := isIndepSet_nbrs hv h3
  have hNcard : (nbrs G s v).card ≤ 4 := by
    by_contra hc
    exact h5 (indepOn_of_indep nbrs_subset hNi (by omega))
  have hsum := card_nbrs_add_card_nonnbrs (G := G) (s := s) hv
  have hM : 9 ≤ (nonnbrs G s v).card := by omega
  rcases ramsey_3_4_le (G := G) (s := nonnbrs G s v) hM with hcl | hind
  · exact h3 (hcl.mono nonnbrs_subset)
  · obtain ⟨B, hB, hBcard, hBind⟩ := hind
    have := indepOn_insert hv hB hBind
    rw [hBcard] at this
    exact h5 this

end Bounds

/-! ## The Ramsey property and the Ramsey number -/

/-- `RamseyArrow n p q` says that every graph on `n` vertices contains either a clique with
`p` vertices or an independent set with `q` vertices. -/
def RamseyArrow (n p q : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n),
    (∃ A : Finset (Fin n), G.IsNClique p A) ∨ (∃ B : Finset (Fin n), G.IsNIndepSet q B)

/-- The two-colour Ramsey number `R(p, q)`. -/
noncomputable def ramseyNumber (p q : ℕ) : ℕ := sInf {n | RamseyArrow n p q}

lemma RamseyArrow.mono {n m p q : ℕ} (hnm : n ≤ m) (h : RamseyArrow n p q) :
    RamseyArrow m p q := by
  intro G
  let f : Fin n ↪ Fin m := ⟨Fin.castLE hnm, Fin.castLE_injective hnm⟩
  rcases h (G.comap f) with ⟨A, hA⟩ | ⟨B, hB⟩
  · refine Or.inl ⟨A.map f, ⟨?_, ?_⟩⟩
    · intro x hx y hy hxy
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact hA.1 ha hb (fun h => hxy (by rw [h]))
    · rw [Finset.card_map, hA.2]
  · refine Or.inr ⟨B.map f, ⟨?_, ?_⟩⟩
    · intro x hx y hy hxy
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact hB.1 ha hb (fun h => hxy (by rw [h]))
    · rw [Finset.card_map, hB.2]

/-! ## The 13-vertex extremal graph -/

/-- Adjacency of the circulant graph `C₁₃(1,5)`. -/
def adj13 (i j : Fin 13) : Bool := ((i.val + 13 - j.val) % 13) ∈ ([1, 5, 8, 12] : List ℕ)

lemma adj13_symm (i j : Fin 13) : adj13 i j = adj13 j i := by
  revert i j; decide

lemma adj13_irrefl (i : Fin 13) : adj13 i i = false := by
  revert i; decide

/-- The circulant graph `C₁₃(1,5)`: a triangle-free graph on 13 vertices with independence
number 4. -/
def G13 : SimpleGraph (Fin 13) where
  Adj i j := adj13 i j
  symm := by
    intro i j h
    rw [adj13_symm j i]; exact h
  loopless := ⟨by
    intro i h
    rw [adj13_irrefl i] at h
    exact Bool.false_ne_true h⟩

lemma adj13_no_triangle : ∀ a b c : Fin 13, adj13 a b → adj13 b c → ¬ adj13 a c := by decide

lemma adj13_no_indep5 : ∀ a b c d e : Fin 13, a < b → b < c → c < d → d < e →
    (adj13 a b ∨ adj13 a c ∨ adj13 a d ∨ adj13 a e ∨ adj13 b c ∨ adj13 b d ∨ adj13 b e ∨
      adj13 c d ∨ adj13 c e ∨ adj13 d e) := by decide

lemma G13_triangle_free : ∀ A : Finset (Fin 13), ¬ G13.IsNClique 3 A := by
  intro A hA
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := SimpleGraph.is3Clique_iff.mp hA
  exact adj13_no_triangle a b c hab hbc hac

/-- Any five vertices of `Fin 13`, listed in increasing order, contain an edge of `G13`. -/
lemma exists_sorted_five {B : Finset (Fin 13)} (hcard : B.card = 5) :
    ∃ a b c d e : Fin 13, a < b ∧ b < c ∧ c < d ∧ d < e ∧
      a ∈ B ∧ b ∈ B ∧ c ∈ B ∧ d ∈ B ∧ e ∈ B := by
  have hlen : (B.sort (· ≤ ·)).length = 5 := by rw [Finset.length_sort, hcard]
  have hsorted : (B.sort (· ≤ ·)).Pairwise (· < ·) := B.sortedLT_sort.pairwise
  have hmem : ∀ x, x ∈ B.sort (· ≤ ·) → x ∈ B := fun x hx => (Finset.mem_sort _).mp hx
  rcases hs : B.sort (· ≤ ·) with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, t⟩⟩⟩⟩⟩ <;>
    rw [hs] at hlen hsorted hmem <;> simp at hlen
  · subst hlen
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false] at hsorted
    refine ⟨a, b, c, d, e, ?_, ?_, ?_, ?_, hmem _ (by simp), hmem _ (by simp), hmem _ (by simp),
      hmem _ (by simp), hmem _ (by simp)⟩ <;> aesop

lemma G13_indep_free : ∀ B : Finset (Fin 13), ¬ G13.IsNIndepSet 5 B := by
  intro B hB
  obtain ⟨hind, hcard⟩ := hB
  obtain ⟨a, b, c, d, e, hab, hbc, hcd, hde, ha, hb, hc, hd, he⟩ := exists_sorted_five hcard
  have key : ∀ x y : Fin 13, x ∈ B → y ∈ B → x < y → ¬ adj13 x y := by
    intro x y hx hy hxy hadj
    exact hind (by exact_mod_cast hx) (by exact_mod_cast hy) (ne_of_lt hxy) hadj
  rcases adj13_no_indep5 a b c d e hab hbc hcd hde with
    h | h | h | h | h | h | h | h | h | h
  · exact key a b ha hb hab h
  · exact key a c ha hc (hab.trans hbc) h
  · exact key a d ha hd (hab.trans (hbc.trans hcd)) h
  · exact key a e ha he (hab.trans (hbc.trans (hcd.trans hde))) h
  · exact key b c hb hc hbc h
  · exact key b d hb hd (hbc.trans hcd) h
  · exact key b e hb he (hbc.trans (hcd.trans hde)) h
  · exact key c d hc hd hcd h
  · exact key c e hc he (hcd.trans hde) h
  · exact key d e hd he hde h

lemma not_ramseyArrow_13 : ¬ RamseyArrow 13 3 5 := by
  intro h
  rcases h G13 with ⟨A, hA⟩ | ⟨B, hB⟩
  · exact G13_triangle_free A hA
  · exact G13_indep_free B hB

lemma ramseyArrow_14 : RamseyArrow 14 3 5 := by
  classical
  intro G
  rcases ramsey_3_5_le (G := G) (s := (Finset.univ : Finset (Fin 14))) (by simp) with h | h
  · obtain ⟨A, -, hcard, hcl⟩ := h
    exact Or.inl ⟨A, hcl, hcard⟩
  · obtain ⟨B, -, hcard, hind⟩ := h
    exact Or.inr ⟨B, hind, hcard⟩

/-- **The Ramsey number `R(3,5)` equals 14.** -/
theorem ramsey_3_5 : ramseyNumber 3 5 = 14 := by
  apply le_antisymm
  · exact Nat.sInf_le ramseyArrow_14
  · refine le_csInf ⟨14, ramseyArrow_14⟩ ?_
    intro n hn
    by_contra hlt
    push_neg at hlt
    exact not_ramseyArrow_13 (RamseyArrow.mono (by omega) hn)

end Math

