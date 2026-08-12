import Mathlib

/-!
# Covering the pairs of a finite set by intersecting families

This file contains the combinatorial core of the case `k = 2` of the Lovász–Kneser theorem.

A proper colouring of the Kneser graph `KG_{n,2}` is exactly a partition of the `2`-element
subsets of an `n`-element set into *intersecting families*.  Such a family is either contained
in a "star" (all its members share a common element) or is a "triangle" (and then has exactly
three members).  This dichotomy drives an induction showing that at least `n - 2` families are
needed.
-/

namespace Frontier

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- A two-element finset containing `x` is `{x, y}` for some `y ≠ x`. -/
lemma exists_eq_pair_of_mem {s : Finset ι} (hs : s.card = 2) {x : ι} (hx : x ∈ s) :
    ∃ y, y ≠ x ∧ s = {x, y} := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ⟨b, fun h => hab h.symm, rfl⟩
  · exact ⟨a, hab, Finset.pair_comm _ _⟩

/-- An intersecting family of `2`-element sets in which no element of a member is common to
all members has at most three members (it is a triangle). -/
lemma card_le_three_of_intersecting (F : Finset (Finset ι))
    (hcard : ∀ e ∈ F, e.card = 2)
    (hint : ∀ e ∈ F, ∀ f ∈ F, ¬ Disjoint e f)
    (hnc : ∀ e ∈ F, ∀ v ∈ e, ∃ f ∈ F, v ∉ f) :
    F.card ≤ 3 := by
  rcases F.eq_empty_or_nonempty with rfl | ⟨e1, he1⟩
  · simp
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (hcard e1 he1)
  -- `e2` avoids `a`, hence contains `b`
  obtain ⟨e2, he2, ha2⟩ := hnc _ he1 a (by simp)
  have hb2 : b ∈ e2 := by
    have h := hint _ he1 _ he2
    rw [Finset.not_disjoint_iff] at h
    obtain ⟨z, hz1, hz2⟩ := h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz1
    rcases hz1 with rfl | rfl
    · exact absurd hz2 ha2
    · exact hz2
  obtain ⟨d, hdb, he2eq⟩ := exists_eq_pair_of_mem (hcard e2 he2) hb2
  have hda : d ≠ a := by
    rintro rfl
    exact ha2 (by rw [he2eq]; simp)
  -- `e3` avoids `b`, hence contains `a` and `d`
  obtain ⟨e3, he3, hb3⟩ := hnc _ he1 b (by simp)
  have ha3 : a ∈ e3 := by
    have h := hint _ he1 _ he3
    rw [Finset.not_disjoint_iff] at h
    obtain ⟨z, hz1, hz2⟩ := h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz1
    rcases hz1 with rfl | rfl
    · exact hz2
    · exact absurd hz2 hb3
  obtain ⟨w, hwa, he3eq⟩ := exists_eq_pair_of_mem (hcard e3 he3) ha3
  have hbw : b ≠ w := by
    intro h
    exact hb3 (by rw [he3eq, ← h]; simp)
  have hwd : w = d := by
    have h := hint _ he2 _ he3
    rw [Finset.not_disjoint_iff] at h
    obtain ⟨z, hz1, hz2⟩ := h
    rw [he2eq] at hz1
    rw [he3eq] at hz2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz1 hz2
    rcases hz1 with h1 | h1 <;> rcases hz2 with h2 | h2
    · exact absurd (h1.symm.trans h2) (Ne.symm hab)
    · exact absurd (h1.symm.trans h2) hbw
    · exact absurd (h1.symm.trans h2) hda
    · exact (h1.symm.trans h2).symm
  subst hwd
  -- every member of `F` is contained in `{a, b, w}`
  have key : ∀ e ∈ F, e ⊆ ({a, b, w} : Finset ι) := by
    intro e he z hz
    by_contra hznot
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hznot
    obtain ⟨u, hu, heeq⟩ := exists_eq_pair_of_mem (hcard e he) hz
    have hmem : ∀ f ∈ F, ∀ x y : ι, f = {x, y} → z ≠ x → z ≠ y → (u = x ∨ u = y) := by
      intro f hf x y hfeq hzx hzy
      have h := hint _ he _ hf
      rw [Finset.not_disjoint_iff] at h
      obtain ⟨t, ht1, ht2⟩ := h
      rw [heeq] at ht1
      rw [hfeq] at ht2
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht1 ht2
      rcases ht1 with h1 | h1
      · rw [h1] at ht2
        rcases ht2 with h2 | h2
        · exact absurd h2 hzx
        · exact absurd h2 hzy
      · rw [h1] at ht2
        exact ht2
    have m1 := hmem _ he1 a b rfl hznot.1 hznot.2.1
    have m2 := hmem _ he2 b w he2eq hznot.2.1 hznot.2.2
    have m3 := hmem _ he3 a w he3eq hznot.1 hznot.2.2
    rcases m1 with h1 | h1
    · rcases m2 with h | h
      · exact hab (h1.symm.trans h)
      · exact hwa (h.symm.trans h1)
    · rcases m3 with h | h
      · exact hab (h.symm.trans h1)
      · exact hbw (h1.symm.trans h)
  have hsub : F ⊆ ({a, b, w} : Finset ι).powersetCard 2 := by
    intro e he
    rw [Finset.mem_powersetCard]
    exact ⟨key e he, hcard e he⟩
  have hc3 : ({a, b, w} : Finset ι).card = 3 := by
    have h1 : a ∉ ({b, w} : Finset ι) := by simp [hab, Ne.symm hwa]
    have h2 : b ∉ ({w} : Finset ι) := by simp [hbw]
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_singleton]
  calc F.card ≤ (({a, b, w} : Finset ι).powersetCard 2).card := Finset.card_le_card hsub
    _ = 3 := by rw [Finset.card_powersetCard, hc3]; decide

lemma two_mul_choose_two (m : ℕ) : 2 * m.choose 2 = m * (m - 1) := by
  induction m with
  | zero => simp
  | succ p ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.mul_add, ih]
    cases p with
    | zero => simp
    | succ q => simp only [Nat.succ_sub_one]; ring

/-- **Key counting lemma.**  If the `2`-element subsets of a finite set `V` are coloured so
that disjoint pairs receive different colours, then at least `#V - 2` colours occur. -/
theorem card_image_ge_of_pair_coloring {γ : Type*} [DecidableEq γ] :
    ∀ (N : ℕ) (V : Finset ι), V.card = N → ∀ col : Finset ι → γ,
      (∀ a ∈ V.powersetCard 2, ∀ b ∈ V.powersetCard 2, Disjoint a b → col a ≠ col b) →
      V.card - 2 ≤ ((V.powersetCard 2).image col).card := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro V hVN col hcol
    by_cases hsmall : V.card ≤ 2
    · omega
    push_neg at hsmall
    set C : Finset γ := (V.powersetCard 2).image col with hC
    by_cases hA : ∃ v ∈ V, ∃ g ∈ C, ∀ e ∈ V.powersetCard 2, col e = g → v ∈ e
    · -- Case A: some colour class is a star centred at `v`; delete `v` and induct.
      obtain ⟨v, hv, g, hg, hstar⟩ := hA
      set V' : Finset ι := V.erase v with hV'
      have hV'card : V'.card = V.card - 1 := Finset.card_erase_of_mem hv
      have hlt : V'.card < N := by omega
      have hsub : V'.powersetCard 2 ⊆ V.powersetCard 2 := by
        apply Finset.powersetCard_mono
        exact Finset.erase_subset _ _
      have hIH := ih V'.card hlt V' rfl col
        (fun a ha b hb hab => hcol a (hsub ha) b (hsub hb) hab)
      have hsub2 : (V'.powersetCard 2).image col ⊆ C.erase g := by
        intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨e, he, rfl⟩ := hx
        rw [Finset.mem_erase]
        refine ⟨?_, Finset.mem_image_of_mem _ (hsub he)⟩
        intro hcg
        have hve := hstar e (hsub he) hcg
        rw [Finset.mem_powersetCard] at he
        have := he.1 hve
        exact (Finset.notMem_erase v V) this
      have hcard2 := Finset.card_le_card hsub2
      rw [Finset.card_erase_of_mem hg] at hcard2
      have hgpos : 1 ≤ C.card := Finset.card_pos.mpr ⟨g, hg⟩
      omega
    · -- Case B: every colour class is a triangle, so has at most three members.
      push_neg at hA
      have hfiber : ∀ g ∈ C, ((V.powersetCard 2).filter (fun e => col e = g)).card ≤ 3 := by
        intro g hg
        refine card_le_three_of_intersecting _ ?_ ?_ ?_
        · intro e he
          rw [Finset.mem_filter, Finset.mem_powersetCard] at he
          exact he.1.2
        · intro e he f hf
          rw [Finset.mem_filter] at he hf
          intro hdisj
          exact hcol e he.1 f hf.1 hdisj (he.2.trans hf.2.symm)
        · intro e he v hve
          rw [Finset.mem_filter, Finset.mem_powersetCard] at he
          have hvV : v ∈ V := he.1.1 hve
          obtain ⟨f, hf, hfg, hvf⟩ := hA v hvV g hg
          exact ⟨f, by rw [Finset.mem_filter]; exact ⟨hf, hfg⟩, hvf⟩
      have hsum : (V.powersetCard 2).card = ∑ g ∈ C, ((V.powersetCard 2).filter
          (fun e => col e = g)).card :=
        Finset.card_eq_sum_card_fiberwise (fun e he => Finset.mem_image_of_mem _ he)
      have hle : (V.powersetCard 2).card ≤ 3 * C.card := by
        rw [hsum]
        calc ∑ g ∈ C, ((V.powersetCard 2).filter (fun e => col e = g)).card
            ≤ ∑ _g ∈ C, 3 := Finset.sum_le_sum hfiber
          _ = 3 * C.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      rw [Finset.card_powersetCard] at hle
      have h2 : 2 * (V.card.choose 2) = V.card * (V.card - 1) := two_mul_choose_two V.card
      -- arithmetic: `n (n-1) ≤ 6 c` and `n ≥ 3` force `c ≥ n - 2`
      by_contra hcon
      push_neg at hcon
      have hn : V.card * (V.card - 1) ≤ 6 * C.card := by omega
      have h3 : C.card + 3 ≤ V.card := by omega
      have h4 : 3 ≤ V.card := by omega
      obtain ⟨m, hm⟩ : ∃ m, V.card = m + 1 := ⟨V.card - 1, by omega⟩
      rw [hm] at hn h3 h4
      simp only [Nat.add_sub_cancel] at hn
      have h5 : m ≤ 5 := by nlinarith
      interval_cases m <;> omega

end Frontier

import Mathlib
import RequestProject.IntersectingCover

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

namespace Frontier

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of an `n`-element set,
and two distinct such subsets are adjacent when they are disjoint. -/
def KneserGraph (n k : ℕ) : SimpleGraph (KneserVertex n k) where
  Adj a b := a ≠ b ∧ Disjoint (a : Finset (Fin n)) (b : Finset (Fin n))
  symm := by
    rintro a b ⟨h1, h2⟩
    exact ⟨h1.symm, h2.symm⟩
  loopless := ⟨by rintro a ⟨h1, -⟩; exact h1 rfl⟩

@[simp] lemma kneserGraph_adj {n k : ℕ} (a b : KneserVertex n k) :
    (KneserGraph n k).Adj a b ↔ a ≠ b ∧ Disjoint (a : Finset (Fin n)) (b : Finset (Fin n)) :=
  Iff.rfl

/-! ### The upper bound `χ(KG_{n,k}) ≤ n - 2k + 2` -/

/-- Two `k`-subsets of `Fin n` contained in the final `2k - 1` elements must intersect. -/
lemma not_disjoint_of_tail {n k : ℕ} (c : Fin n) (hc : (c : ℕ) = n - 2 * k + 1)
    (a b : Finset (Fin n)) (ha : a.card = k) (hb : b.card = k)
    (ha' : a ⊆ Finset.Ici c) (hb' : b ⊆ Finset.Ici c) :
    ¬ Disjoint a b := by
  intro hd
  have h1 : (a ∪ b).card = 2 * k := by
    rw [Finset.card_union_of_disjoint hd, ha, hb]; ring
  have h3 := Finset.card_le_card (Finset.union_subset ha' hb')
  rw [Fin.card_Ici, hc, h1] at h3
  have : (c : ℕ) < n := c.isLt
  omega

/-- The Kneser graph `KG_{n,k}` is colorable with `n - 2k + 2` colors, for `1 ≤ k` and
`2k ≤ n`.  (This is the easy half of Lovász's theorem.) -/
theorem kneser_colorable (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    (KneserGraph n k).Colorable (n - 2 * k + 2) := by
  classical
  have hne : ∀ a : KneserVertex n k, (a : Finset (Fin n)).Nonempty := by
    intro a
    rw [← Finset.card_pos, a.2]
    omega
  set N : ℕ := n - 2 * k + 1 with hN
  have hNlt : N < n := by omega
  set c : Fin n := ⟨N, hNlt⟩ with hcdef
  have hc : (c : ℕ) = n - 2 * k + 1 := rfl
  -- colour a set by the minimum of (the value of) its least element and `N`
  refine ⟨SimpleGraph.Coloring.mk
    (fun a => (⟨min ((a : Finset (Fin n)).min' (hne a) : ℕ) N, by omega⟩ :
      Fin (n - 2 * k + 2))) ?_⟩
  rintro a b ⟨hab, hd⟩ hcol
  simp only [Fin.mk.injEq] at hcol
  set x : ℕ := ((a : Finset (Fin n)).min' (hne a) : ℕ) with hx
  set y : ℕ := ((b : Finset (Fin n)).min' (hne b) : ℕ) with hy
  by_cases hlt : min x N < N
  · -- both sets have the same least element, hence share it
    have hxy : x = y := by omega
    have hmem : (a : Finset (Fin n)).min' (hne a) ∈ (b : Finset (Fin n)) := by
      have heq : (a : Finset (Fin n)).min' (hne a) = (b : Finset (Fin n)).min' (hne b) :=
        Fin.ext (by rw [← hx, ← hy, hxy])
      rw [heq]
      exact Finset.min'_mem _ _
    exact (Finset.disjoint_left.mp hd ((a : Finset (Fin n)).min'_mem (hne a))) hmem
  · -- both sets live in the last `2k - 1` elements
    have hxN : N ≤ x := by omega
    have hyN : N ≤ y := by omega
    refine not_disjoint_of_tail c hc _ _ a.2 b.2 ?_ ?_ hd
    · intro i hi
      have h1 := Fin.le_def.mp (Finset.min'_le (a : Finset (Fin n)) i hi)
      exact Finset.mem_Ici.mpr (Fin.le_def.mpr (by omega))
    · intro i hi
      have h1 := Fin.le_def.mp (Finset.min'_le (b : Finset (Fin n)) i hi)
      exact Finset.mem_Ici.mpr (Fin.le_def.mpr (by omega))

theorem kneser_chromaticNumber_le (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    (KneserGraph n k).chromaticNumber ≤ (n - 2 * k + 2 : ℕ) :=
  (kneser_colorable n k hk hn).chromaticNumber_le

/-! ### The base case `k = 1`: `KG_{n,1}` is the complete graph -/

lemma kneserGraph_one_eq_top (n : ℕ) : KneserGraph n 1 = ⊤ := by
  ext a b
  simp only [kneserGraph_adj, SimpleGraph.top_adj]
  refine ⟨fun h => h.1, fun hab => ⟨hab, ?_⟩⟩
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp a.2
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp b.2
  have hxy : x ≠ y := by
    rintro rfl
    exact hab (Subtype.ext (hx.trans hy.symm))
  simp [hx, hy, hxy]

lemma card_kneserVertex_one (n : ℕ) : Fintype.card (KneserVertex n 1) = n := by
  simp [Fintype.card_finset_len (α := Fin n) 1]

/-- **Lovász–Kneser theorem, base case `k = 1`.**  The chromatic number of the Kneser graph
`KG_{n,1}` — which is the complete graph on `n` vertices — is `n - 2 * 1 + 2 = n`, for `n ≥ 2`. -/
theorem lovasz_kneser_k_one (n : ℕ) (hn : 2 ≤ n) :
    (KneserGraph n 1).chromaticNumber = (n - 2 * 1 + 2 : ℕ) := by
  have htop : (KneserGraph n 1).chromaticNumber = (Fintype.card (KneserVertex n 1) : ℕ∞) := by
    rw [kneserGraph_one_eq_top]
    exact SimpleGraph.chromaticNumber_top
  rw [htop, card_kneserVertex_one n]
  congr 1
  omega

/-! ### The base case `n = 2k`: `KG_{2k,k}` is a perfect matching -/

/-- **Lovász–Kneser theorem, base case `n = 2k`.**  The chromatic number of `KG_{2k,k}` is
`2k - 2k + 2 = 2`, for `k ≥ 1`. -/
theorem lovasz_kneser_two_k (k : ℕ) (hk : 1 ≤ k) :
    (KneserGraph (2 * k) k).chromaticNumber = (2 * k - 2 * k + 2 : ℕ) := by
  classical
  have hle : (KneserGraph (2 * k) k).chromaticNumber ≤ (2 * k - 2 * k + 2 : ℕ) :=
    kneser_chromaticNumber_le (2 * k) k hk le_rfl
  refine le_antisymm hle ?_
  have hklt : k < 2 * k := by omega
  set c : Fin (2 * k) := ⟨k, hklt⟩ with hcdef
  set A : Finset (Fin (2 * k)) := Finset.Iio c with hA
  set B : Finset (Fin (2 * k)) := Finset.Ici c with hB
  have hAcard : A.card = k := by rw [hA, Fin.card_Iio]
  have hBcard : B.card = k := by rw [hB, Fin.card_Ici]; simp [hcdef]; omega
  have hdisjAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    rw [hA, Finset.mem_Iio] at hi
    rw [hB, Finset.mem_Ici] at hi'
    exact absurd hi (not_lt.mpr hi')
  let va : KneserVertex (2 * k) k := ⟨A, hAcard⟩
  let vb : KneserVertex (2 * k) k := ⟨B, hBcard⟩
  have hne : va ≠ vb := by
    intro h
    have hAB : A = B := congrArg Subtype.val h
    have hcB : c ∈ B := Finset.mem_Ici.mpr le_rfl
    rw [← hAB, hA, Finset.mem_Iio] at hcB
    exact lt_irrefl c hcB
  have hge : (2 : ℕ∞) ≤ (KneserGraph (2 * k) k).chromaticNumber := by
    refine SimpleGraph.le_chromaticNumber_of_pairwise_adj (ι := Fin 2) (n := 2)
      (f := fun i => if i = 0 then va else vb) ?_ ?_
    · simp
    · intro i j hij
      have hadj : (KneserGraph (2 * k) k).Adj va vb := ⟨hne, hdisjAB⟩
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · simpa using hadj
      · simpa using hadj.symm
      · exact absurd rfl hij
  simpa using hge

/-! ### The case `k = 2` -/

/-- **Lovász–Kneser theorem, the case `k = 2`.**  The chromatic number of `KG_{n,2}` is
`n - 2 * 2 + 2 = n - 2`, for `n ≥ 4`.  The lower bound is proved combinatorially, via the
fact that an intersecting family of pairs is either a star or a triangle. -/
theorem lovasz_kneser_k_two (n : ℕ) (hn : 4 ≤ n) :
    (KneserGraph n 2).chromaticNumber = (n - 2 * 2 + 2 : ℕ) := by
  classical
  refine le_antisymm (kneser_chromaticNumber_le n 2 (by norm_num) (by omega)) ?_
  rw [SimpleGraph.le_chromaticNumber_iff_coloring]
  intro m Col
  set col : Finset (Fin n) → Option (Fin m) :=
    fun s => if h : s.card = 2 then some (Col ⟨s, h⟩) else none with hcoldef
  have hcol : ∀ a ∈ (Finset.univ : Finset (Fin n)).powersetCard 2,
      ∀ b ∈ (Finset.univ : Finset (Fin n)).powersetCard 2, Disjoint a b → col a ≠ col b := by
    intro a ha b hb hdisj
    rw [Finset.mem_powersetCard_univ] at ha hb
    have hne : (⟨a, ha⟩ : KneserVertex n 2) ≠ ⟨b, hb⟩ := by
      intro h
      have hab : a = b := congrArg Subtype.val h
      subst hab
      rw [disjoint_self, Finset.bot_eq_empty] at hdisj
      rw [hdisj] at ha
      simp at ha
    have hvalid := Col.valid (show (KneserGraph n 2).Adj ⟨a, ha⟩ ⟨b, hb⟩ from ⟨hne, hdisj⟩)
    simp only [hcoldef, ha, hb, dif_pos, ne_eq, Option.some.injEq]
    exact hvalid
  have hkey := card_image_ge_of_pair_coloring n (Finset.univ : Finset (Fin n)) (by simp) col hcol
  have hsub : ((Finset.univ : Finset (Fin n)).powersetCard 2).image col ⊆
      (Finset.univ : Finset (Fin m)).image some := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨e, he, rfl⟩ := hx
    rw [Finset.mem_powersetCard_univ] at he
    simp [hcoldef, he]
  have hcard :
      ((Finset.univ : Finset (Fin m)).image (some : Fin m → Option (Fin m))).card = m := by
    rw [Finset.card_image_of_injective _ (Option.some_injective _)]
    simp
  have hfin := le_trans hkey (le_trans (Finset.card_le_card hsub) (le_of_eq hcard))
  simp only [Finset.card_univ, Fintype.card_fin] at hfin
  have hfin2 : (n - 2 * 2 + 2 : ℕ) ≤ m := by omega
  exact_mod_cast hfin2

/-! ### The Lovász–Kneser theorem in the cases established here -/

/-- **Lovász's theorem on the chromatic number of Kneser graphs**, in the cases proved here:
the chromatic number of `KG_{n,k}` is `n - 2k + 2` whenever `1 ≤ k`, `2k ≤ n` and one of
`k = 1`, `k = 2`, `n = 2k` holds.

The general case (Lovász's theorem, whose usual proof goes through the Borsuk–Ulam theorem) is
not proved here; the upper bound `χ(KG_{n,k}) ≤ n - 2k + 2` is established in full generality
in `Frontier.kneser_chromaticNumber_le`. -/
theorem lovasz_kneser (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (hcase : k = 1 ∨ k = 2 ∨ n = 2 * k) :
    (KneserGraph n k).chromaticNumber = (n - 2 * k + 2 : ℕ) := by
  rcases hcase with rfl | rfl | rfl
  · exact lovasz_kneser_k_one n (by omega)
  · exact lovasz_kneser_k_two n (by omega)
  · exact lovasz_kneser_two_k k hk

end Frontier

