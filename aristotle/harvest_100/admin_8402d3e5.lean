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

(Lean requires `import` to come first in a file, so the header above the import is a plain
block comment and this is the module docstring with the same content.)

Mathlib does not contain Ramsey numbers, so the whole development is built here:
the recursion `R(3,t+1) ≤ t + R(3,t)`, the parity refinement giving `R(3,4) ≤ 9`,
hence `R(3,5) ≤ 14`, and the circulant graph `C₁₃(1,5)` witnessing `R(3,5) > 13`.
-/

set_option maxHeartbeats 2000000

namespace Math

open Finset

/-! ## The Ramsey property -/

/-- `RamseyProp n s t` says that every simple graph on `n` vertices contains either a clique
of size `s` or an independent set of size `t` (equivalently, a clique of size `t` in the
complement).  `R(s,t)` is the least `n` with this property. -/
def RamseyProp (n s t : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree s ∨ ¬ Gᶜ.CliqueFree t

section Relative

variable {V : Type}

/-- `G` has a triangle all of whose vertices lie in `A`. -/
def HasTriangleIn (G : SimpleGraph V) (A : Finset V) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c

/-- `G` has an independent set of size `k` contained in `A`. -/
def HasIndepIn (G : SimpleGraph V) (A : Finset V) (k : ℕ) : Prop :=
  ∃ S ⊆ A, S.card = k ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ G.Adj x y

/-- Relative form of the Ramsey bound `R(3,t) ≤ n`: in any graph, every vertex set of size
at least `n` contains a triangle or an independent set of size `t`. -/
def RamseyRel (n t : ℕ) : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) (A : Finset V), n ≤ A.card →
    HasTriangleIn G A ∨ HasIndepIn G A t

theorem HasTriangleIn.mono {G : SimpleGraph V} {A B : Finset V} (hAB : A ⊆ B)
    (h : HasTriangleIn G A) : HasTriangleIn G B := by
  obtain ⟨a, ha, b, hb, c, hc, h⟩ := h
  exact ⟨a, hAB ha, b, hAB hb, c, hAB hc, h⟩

theorem HasIndepIn.mono {G : SimpleGraph V} {A B : Finset V} {k : ℕ} (hAB : A ⊆ B)
    (h : HasIndepIn G A k) : HasIndepIn G B k := by
  obtain ⟨S, hS, h⟩ := h
  exact ⟨S, hS.trans hAB, h⟩

theorem ramseyRel_of_card_eq (n t : ℕ)
    (h : ∀ (V : Type) (G : SimpleGraph V) (A : Finset V), A.card = n →
      HasTriangleIn G A ∨ HasIndepIn G A t) : RamseyRel n t := by
  intro V G A hA
  obtain ⟨A', hA', hcard⟩ := Finset.exists_subset_card_eq hA
  rcases h V G A' hcard with h | h
  · exact Or.inl (h.mono hA')
  · exact Or.inr (h.mono hA')

/-- `R(3,2) ≤ 3`. -/
theorem ramseyRel_two : RamseyRel 3 2 := by
  intro V G A hA
  classical
  by_cases hpair : ∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ ¬ G.Adj x y
  · obtain ⟨x, hx, y, hy, hxy, hadj⟩ := hpair
    refine Or.inr ⟨{x, y}, ?_, ?_, ?_⟩
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    · rw [Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]
    · intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all
      exact fun h => hadj h.symm
  · push_neg at hpair
    obtain ⟨A', hA', hcard⟩ := Finset.exists_subset_card_eq hA
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 hcard
    have ha : a ∈ A := hA' (by simp)
    have hb : b ∈ A := hA' (by simp)
    have hc : c ∈ A := hA' (by simp)
    exact Or.inl ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hpair a ha b hb hab,
      hpair a ha c hc hac, hpair b hb c hc hbc⟩

section Neighborhood

variable [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The neighbours of `v` inside `A`. -/
def nbrIn (A : Finset V) (v : V) : Finset V := A.filter (fun x => G.Adj v x)

/-- The non-neighbours of `v` inside `A`, excluding `v` itself. -/
def nonNbrIn (A : Finset V) (v : V) : Finset V := A \ insert v (nbrIn G A v)

theorem card_split {A : Finset V} {v : V} (hv : v ∈ A) :
    A.card = 1 + (nbrIn G A v).card + (nonNbrIn G A v).card := by
  have hsub : nbrIn G A v ⊆ A := Finset.filter_subset _ _
  have hvnot : v ∉ nbrIn G A v := by simp [nbrIn]
  have hins : insert v (nbrIn G A v) ⊆ A := Finset.insert_subset hv hsub
  have h1 : (insert v (nbrIn G A v)).card = (nbrIn G A v).card + 1 :=
    Finset.card_insert_of_notMem hvnot
  have h2 := Finset.card_sdiff_add_card_eq_card hins
  unfold nonNbrIn
  omega

omit [DecidableEq V] in
/-- In a triangle-free graph the neighbourhood of a vertex is independent, so it has at most
`t` elements if there is no independent set of size `t + 1`. -/
theorem card_nbrIn_le {A : Finset V} {v : V} {t : ℕ} (hv : v ∈ A)
    (htri : ¬ HasTriangleIn G A) (hind : ¬ HasIndepIn G A (t + 1)) :
    (nbrIn G A v).card ≤ t := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq (n := t + 1) hlt
  refine hind ⟨S, hS.trans (Finset.filter_subset _ _), hcard, ?_⟩
  intro x hx y hy hxy hadj
  have hx' := hS hx
  have hy' := hS hy
  simp only [nbrIn, Finset.mem_filter] at hx' hy'
  exact htri ⟨v, hv, x, hx'.1, y, hy'.1, (G.ne_of_adj hx'.2), (G.ne_of_adj hy'.2), hxy,
    hx'.2, hy'.2, hadj⟩

/-- The set of non-neighbours of `v` contains no triangle and no independent set of size `t`
(the latter would extend by `v`), so it is smaller than `R(3,t)`. -/
theorem card_nonNbrIn_lt {A : Finset V} {v : V} {t k : ℕ} (hk : RamseyRel k t) (hv : v ∈ A)
    (htri : ¬ HasTriangleIn G A) (hind : ¬ HasIndepIn G A (t + 1)) :
    (nonNbrIn G A v).card < k := by
  by_contra hle
  push_neg at hle
  have hMA : nonNbrIn G A v ⊆ A := Finset.sdiff_subset
  rcases hk V G (nonNbrIn G A v) hle with h | h
  · exact htri (h.mono hMA)
  · obtain ⟨S, hS, hcard, hindep⟩ := h
    have hvS : v ∉ S := by
      intro hvS
      have := hS hvS
      simp [nonNbrIn] at this
    have hnadj : ∀ x ∈ S, ¬ G.Adj v x := by
      intro x hx
      have := hS hx
      simp only [nonNbrIn, nbrIn, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_filter] at this
      tauto
    refine hind ⟨insert v S, Finset.insert_subset hv (hS.trans hMA), ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hvS, hcard]
    · intro x hx y hy hxy
      simp only [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx
      · rcases hy with rfl | hy
        · exact absurd rfl hxy
        · exact hnadj y hy
      · rcases hy with rfl | hy
        · exact fun h => hnadj x hx h.symm
        · exact hindep x hx y hy hxy

end Neighborhood

/-- The basic Ramsey recursion `R(3,t+1) ≤ t + R(3,t)`. -/
theorem ramseyRel_step {k t : ℕ} (hk : RamseyRel k t) : RamseyRel (t + k + 1) (t + 1) := by
  intro V G A hA
  by_contra hcon
  push_neg at hcon
  obtain ⟨htri, hind⟩ := hcon
  classical
  have hne : A.Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨v, hv⟩ := hne
  have h1 := card_split G hv
  have h2 := card_nbrIn_le (t := t) G (A := A) (v := v) hv htri hind
  have h3 := card_nonNbrIn_lt G hk hv htri hind
  omega

/-- `R(3,3) ≤ 6`. -/
theorem ramseyRel_three : RamseyRel 6 3 := by
  have := ramseyRel_step (k := 3) (t := 2) ramseyRel_two
  norm_num at this
  exact this

/-! ### A parity lemma -/

/-- The double sum of a symmetric function vanishing on the diagonal is even. -/
theorem even_sum_symm {W : Type} (f : W → W → ℕ) (hs : ∀ x y, f x y = f y x)
    (hd : ∀ x, f x x = 0) (A : Finset W) : Even (∑ v ∈ A, ∑ w ∈ A, f v w) := by
  induction A using Finset.cons_induction with
  | empty => simp
  | cons a B ha ih =>
      simp only [Finset.sum_cons]
      have key : f a a + ∑ w ∈ B, f a w + ∑ x ∈ B, (f x a + ∑ w ∈ B, f x w)
           = 2 * (∑ w ∈ B, f a w) + ∑ x ∈ B, ∑ w ∈ B, f x w := by
        rw [Finset.sum_add_distrib, hd]
        have hswap : ∑ x ∈ B, f x a = ∑ x ∈ B, f a x := Finset.sum_congr rfl (fun x _ => hs x a)
        rw [hswap]; ring
      rw [key]
      exact (even_two_mul _).add ih

/-- `R(3,4) ≤ 9`.  The naive recursion only gives `10`; a parity argument (there is no
`3`-regular graph on `9` vertices) improves the bound to `9`. -/
theorem ramseyRel_four : RamseyRel 9 4 := by
  refine ramseyRel_of_card_eq 9 4 ?_
  intro V G A hA
  by_contra hcon
  push_neg at hcon
  obtain ⟨htri, hind⟩ := hcon
  classical
  have hind' : ¬ HasIndepIn G A (3 + 1) := by simpa using hind
  have hdeg : ∀ v ∈ A, (nbrIn G A v).card = 3 := by
    intro v hv
    have h1 := card_split G hv
    have h2 := card_nbrIn_le (t := 3) G (A := A) (v := v) hv htri hind'
    have h3 := card_nonNbrIn_lt (t := 3) (k := 6) G ramseyRel_three hv htri hind'
    omega
  have hsum : ∑ v ∈ A, (nbrIn G A v).card = 27 := by
    rw [Finset.sum_congr rfl hdeg, Finset.sum_const, hA]
    rfl
  have heven : Even (∑ v ∈ A, (nbrIn G A v).card) := by
    have hcf : ∀ v, (nbrIn G A v).card = ∑ w ∈ A, if G.Adj v w then 1 else 0 := by
      intro v; exact Finset.card_filter _ _
    simp_rw [hcf]
    refine even_sum_symm (fun v w => if G.Adj v w then 1 else 0) ?_ ?_ A
    · intro x y
      by_cases h : G.Adj x y
      · simp [h, h.symm]
      · simp only [h, if_false]
        rw [if_neg (fun h' : G.Adj y x => h h'.symm)]
    · intro x; simp
  rw [hsum] at heven
  norm_num at heven

/-- `R(3,5) ≤ 14`. -/
theorem ramseyRel_five : RamseyRel 14 5 := by
  have := ramseyRel_step (k := 9) (t := 4) ramseyRel_four
  norm_num at this
  exact this

end Relative

/-! ## The upper bound: every graph on 14 vertices has a triangle or an independent 5-set -/

theorem ramseyProp_fourteen : RamseyProp 14 3 5 := by
  intro G
  classical
  have hcard : (14 : ℕ) ≤ (Finset.univ : Finset (Fin 14)).card := by simp
  rcases ramseyRel_five (Fin 14) G Finset.univ hcard with h | h
  · left
    obtain ⟨a, -, b, -, c, -, hab, hac, hbc, h1, h2, h3⟩ := h
    exact SimpleGraph.IsNClique.not_cliqueFree
      ((SimpleGraph.is3Clique_triple_iff).2 ⟨h1, h2, h3⟩)
  · right
    obtain ⟨S, -, hcard5, hindep⟩ := h
    refine SimpleGraph.IsNClique.not_cliqueFree (s := S) ?_
    refine (SimpleGraph.isNClique_iff _).2 ⟨?_, hcard5⟩
    intro x hx y hy hxy
    exact (SimpleGraph.compl_adj _ _ _).2 ⟨hxy, hindep x hx y hy hxy⟩

/-! ## The lower bound: a triangle-free graph on 13 vertices with independence number 4 -/

/-- Adjacency of the circulant graph `C₁₃(1,5)`. -/
def adj13 (a b : Fin 13) : Bool :=
  let d := (a.val + 13 - b.val) % 13
  d = 1 || d = 5 || d = 8 || d = 12

/-- The circulant graph on `ℤ/13` with connection set `{±1, ±5}`.  It is triangle-free and
its independence number is `4`, witnessing `R(3,5) > 13`. -/
def G13 : SimpleGraph (Fin 13) where
  Adj a b := adj13 a b
  symm := by intro a b; revert a b; decide
  loopless := ⟨by decide⟩

instance : DecidableRel G13.Adj := fun a b => by
  show Decidable (adj13 a b = true); infer_instance

/-- Extract three elements of a `3`-element finset in increasing order. -/
theorem exists_sorted_three {α : Type} [LinearOrder α] (S : Finset α) (h : S.card = 3) :
    ∃ a b c, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ a < b ∧ b < c := by
  have f := S.orderIsoOfFin h
  refine ⟨f 0, f 1, f 2, (f 0).2, (f 1).2, (f 2).2, ?_, ?_⟩ <;>
    · exact Subtype.coe_lt_coe.2 (f.strictMono (by decide))

/-- Extract five elements of a `5`-element finset in increasing order. -/
theorem exists_sorted_five {α : Type} [LinearOrder α] (S : Finset α) (h : S.card = 5) :
    ∃ a b c d e, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ d ∈ S ∧ e ∈ S ∧ a < b ∧ b < c ∧ c < d ∧ d < e := by
  have f := S.orderIsoOfFin h
  refine ⟨f 0, f 1, f 2, f 3, f 4, (f 0).2, (f 1).2, (f 2).2, (f 3).2, (f 4).2, ?_, ?_, ?_, ?_⟩ <;>
    · exact Subtype.coe_lt_coe.2 (f.strictMono (by decide))

set_option maxRecDepth 100000 in
theorem G13_no_triangle : ∀ a b c : Fin 13, a < b → b < c →
    ¬ (G13.Adj a b ∧ G13.Adj a c ∧ G13.Adj b c) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem G13_no_indep_five : ∀ a b c d e : Fin 13, a < b → b < c → c < d → d < e →
    ¬ (¬ G13.Adj a b ∧ ¬ G13.Adj a c ∧ ¬ G13.Adj a d ∧ ¬ G13.Adj a e ∧ ¬ G13.Adj b c ∧
       ¬ G13.Adj b d ∧ ¬ G13.Adj b e ∧ ¬ G13.Adj c d ∧ ¬ G13.Adj c e ∧ ¬ G13.Adj d e) := by
  decide +kernel

theorem G13_cliqueFree_three : G13.CliqueFree 3 := by
  intro S hS
  obtain ⟨a, b, c, ha, hb, hc, hab, hbc⟩ := exists_sorted_three S hS.2
  have hclique := hS.1
  exact G13_no_triangle a b c hab hbc
    ⟨hclique ha hb (ne_of_lt hab), hclique ha hc (ne_of_lt (hab.trans hbc)),
     hclique hb hc (ne_of_lt hbc)⟩

theorem G13_compl_cliqueFree_five : G13ᶜ.CliqueFree 5 := by
  intro S hS
  obtain ⟨a, b, c, d, e, ha, hb, hc, hd, he, hab, hbc, hcd, hde⟩ := exists_sorted_five S hS.2
  have hclique := hS.1
  have key : ∀ {x y : Fin 13}, x ∈ (S : Set (Fin 13)) → y ∈ (S : Set (Fin 13)) → x < y →
      ¬ G13.Adj x y := fun hx hy hxy =>
    ((SimpleGraph.compl_adj _ _ _).1 (hclique hx hy (ne_of_lt hxy))).2
  exact G13_no_indep_five a b c d e hab hbc hcd hde
    ⟨key ha hb hab, key ha hc (hab.trans hbc), key ha hd (hab.trans (hbc.trans hcd)),
     key ha he (hab.trans (hbc.trans (hcd.trans hde))), key hb hc hbc,
     key hb hd (hbc.trans hcd), key hb he (hbc.trans (hcd.trans hde)), key hc hd hcd,
     key hc he (hcd.trans hde), key hd he hde⟩

theorem not_ramseyProp_of_le_thirteen {n : ℕ} (hn : n ≤ 13) : ¬ RamseyProp n 3 5 := by
  intro h
  set f : Fin n ↪ Fin 13 := ⟨Fin.castLE hn, Fin.castLE_injective hn⟩ with hf
  have hcompl : (SimpleGraph.comap (⇑f) G13)ᶜ = SimpleGraph.comap (⇑f) G13ᶜ := by
    ext a b
    simp [hf, SimpleGraph.comap, Fin.castLE_inj]
  rcases h (SimpleGraph.comap (⇑f) G13) with h3 | h5
  · exact h3 (G13_cliqueFree_three.comap (SimpleGraph.Embedding.comap f G13))
  · rw [hcompl] at h5
    exact h5 (G13_compl_cliqueFree_five.comap (SimpleGraph.Embedding.comap f G13ᶜ))

/-! ## The Ramsey number -/

/-- `R(3,5) = 14`: `14` is the least `n` such that every graph on `n` vertices contains a
triangle or an independent set of size `5`. -/
theorem ramsey_3_5 : IsLeast {n | RamseyProp n 3 5} 14 := by
  constructor
  · exact ramseyProp_fourteen
  · intro n hn
    by_contra hlt
    exact not_ramseyProp_of_le_thirteen (by omega) hn

end Math

