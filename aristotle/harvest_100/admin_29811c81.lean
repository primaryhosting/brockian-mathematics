/-
Franklin's involution and the combinatorial core of Euler's pentagonal number theorem.
-/
import Mathlib

namespace EulerPentagonal

open Finset

/-- The minimum of a finset of naturals (`0` for the empty set). -/
def mn (S : Finset ℕ) : ℕ := if h : S.Nonempty then S.min' h else 0

/-- The maximum of a finset of naturals (`0` for the empty set). -/
def mx (S : Finset ℕ) : ℕ := if h : S.Nonempty then S.max' h else 0

lemma mn_eq (S : Finset ℕ) (h : S.Nonempty) : mn S = S.min' h := dif_pos h

lemma mx_eq (S : Finset ℕ) (h : S.Nonempty) : mx S = S.max' h := dif_pos h

lemma mn_mem (S : Finset ℕ) (h : S.Nonempty) : mn S ∈ S := by
  rw [mn_eq S h]; exact S.min'_mem h

lemma mx_mem (S : Finset ℕ) (h : S.Nonempty) : mx S ∈ S := by
  rw [mx_eq S h]; exact S.max'_mem h

lemma mn_le (S : Finset ℕ) {a : ℕ} (ha : a ∈ S) : mn S ≤ a := by
  rw [mn_eq S ⟨a, ha⟩]; exact S.min'_le a ha

lemma le_mx (S : Finset ℕ) {a : ℕ} (ha : a ∈ S) : a ≤ mx S := by
  rw [mx_eq S ⟨a, ha⟩]; exact S.le_max' a ha

/-- The length of the maximal run of consecutive integers at the top of `S`. -/
def stair (S : Finset ℕ) : ℕ :=
  Nat.findGreatest (fun j => Finset.Icc (mx S + 1 - j) (mx S) ⊆ S) (mx S)

/-- Franklin's move when the smallest part is at most the staircase length:
remove the smallest part `s` and add one to each of the `s` largest parts. -/
def fA (S : Finset ℕ) : Finset ℕ :=
  ((S.erase (mn S)) \ Finset.Icc (mx S + 1 - mn S) (mx S)) ∪
    Finset.Icc (mx S + 2 - mn S) (mx S + 1)

/-- Franklin's move when the smallest part exceeds the staircase length:
subtract one from each of the `σ` largest parts and adjoin a new part `σ`. -/
def fB (S : Finset ℕ) : Finset ℕ :=
  insert (stair S)
    ((S \ Finset.Icc (mx S + 1 - stair S) (mx S)) ∪ Finset.Icc (mx S - stair S) (mx S - 1))

/-- Franklin's involution. -/
def franklin (S : Finset ℕ) : Finset ℕ := if mn S ≤ stair S then fA S else fB S

/-- The exceptional (fixed) partitions: the two families of pentagonal staircases. -/
def IsExc (S : Finset ℕ) : Prop :=
  ∃ c : ℕ, 1 ≤ c ∧ (S = Finset.Icc c (2 * c - 1) ∨ S = Finset.Icc (c + 1) (2 * c))

/-- Partitions of `n` into distinct positive parts, as finsets. -/
def D (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 n).powerset.filter (fun S => ∑ i ∈ S, i = n)

lemma mem_D_iff {n : ℕ} {S : Finset ℕ} : S ∈ D n ↔ (0 ∉ S ∧ ∑ i ∈ S, i = n) := by
  simp only [D, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hsub, hsum⟩
    refine ⟨fun h0 => ?_, hsum⟩
    have := hsub h0
    simp at this
  · rintro ⟨h0, hsum⟩
    refine ⟨fun x hx => ?_, hsum⟩
    have hx1 : 1 ≤ x := by
      rcases Nat.eq_zero_or_pos x with h | h
      · exact absurd (h ▸ hx) h0
      · exact h
    have hxn : x ≤ n := by
      rw [← hsum]
      exact Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) hx
    simp [Finset.mem_Icc, hx1, hxn]

section Basic

variable {S : Finset ℕ}

lemma one_le_mn (h0 : 0 ∉ S) (hne : S.Nonempty) : 1 ≤ mn S := by
  rcases Nat.eq_zero_or_pos (mn S) with h | h
  · exact absurd (h ▸ mn_mem S hne) h0
  · exact h

lemma one_le_mx (h0 : 0 ∉ S) (hne : S.Nonempty) : 1 ≤ mx S := by
  rcases Nat.eq_zero_or_pos (mx S) with h | h
  · exact absurd (h ▸ mx_mem S hne) h0
  · exact h

lemma mn_le_mx (hne : S.Nonempty) : mn S ≤ mx S := le_mx S (mn_mem S hne)

lemma subset_Icc_mn_mx : S ⊆ Finset.Icc (mn S) (mx S) := by
  intro x hx
  simp only [Finset.mem_Icc]
  exact ⟨mn_le S hx, le_mx S hx⟩

lemma stair_block_sub_self (h0 : 0 ∉ S) (hne : S.Nonempty) :
    Finset.Icc (mx S + 1 - stair S) (mx S) ⊆ S := by
  have h := Nat.findGreatest_spec (P := fun j => Finset.Icc (mx S + 1 - j) (mx S) ⊆ S)
    (m := 1) (n := mx S) (one_le_mx h0 hne) (by simpa using mx_mem S hne)
  exact h

lemma one_le_stair (h0 : 0 ∉ S) (hne : S.Nonempty) : 1 ≤ stair S := by
  unfold stair
  refine Nat.le_findGreatest (one_le_mx h0 hne) ?_
  simpa using mx_mem S hne

lemma stair_le_mx : stair S ≤ mx S := Nat.findGreatest_le _

lemma le_stair {j : ℕ} (hj : j ≤ mx S) (h : Finset.Icc (mx S + 1 - j) (mx S) ⊆ S) :
    j ≤ stair S := Nat.le_findGreatest hj h

lemma stair_not_mem (h0 : 0 ∉ S) (hne : S.Nonempty) : mx S - stair S ∉ S := by
  rcases eq_or_lt_of_le (stair_le_mx (S := S)) with h | h
  · simpa [h] using h0
  · intro hmem
    have hgt := Nat.findGreatest_is_greatest (P := fun j => Finset.Icc (mx S + 1 - j) (mx S) ⊆ S)
      (k := stair S + 1) (n := mx S) (by simp [stair]) h
    apply hgt
    intro x hx
    simp only [Finset.mem_Icc] at hx
    rcases eq_or_lt_of_le hx.1 with hxe | hxl
    · have hxx : x = mx S - stair S := by omega
      rw [hxx]; exact hmem
    · exact stair_block_sub_self h0 hne (by simp only [Finset.mem_Icc]; omega)

lemma card_stair_block : (Finset.Icc (mx S + 1 - stair S) (mx S)).card = stair S := by
  have := stair_le_mx (S := S)
  rw [Nat.card_Icc]
  omega

lemma stair_le_card (h0 : 0 ∉ S) (hne : S.Nonempty) : stair S ≤ S.card := by
  have := Finset.card_le_card (stair_block_sub_self h0 hne)
  rwa [card_stair_block] at this

lemma eq_stair_block_of_card (h0 : 0 ∉ S) (hne : S.Nonempty) (h : S.card = stair S) :
    S = Finset.Icc (mx S + 1 - stair S) (mx S) :=
  (Finset.eq_of_subset_of_card_le (stair_block_sub_self h0 hne)
    (by rw [card_stair_block, h])).symm

lemma mn_lt_of_stair_lt_card (h0 : 0 ∉ S) (hne : S.Nonempty) (h : stair S < S.card) :
    mn S < mx S - stair S := by
  have hmem := mn_mem S hne
  have hblock := stair_block_sub_self h0 hne
  have hnot := stair_not_mem h0 hne
  have hst := stair_le_mx (S := S)
  -- the minimum is not in the top block
  have hnb : mn S ∉ Finset.Icc (mx S + 1 - stair S) (mx S) := by
    intro hin
    simp only [Finset.mem_Icc] at hin
    have : Finset.Icc (mn S) (mx S) ⊆ S := by
      intro x hx
      simp only [Finset.mem_Icc] at hx
      exact hblock (by simp only [Finset.mem_Icc]; omega)
    have hSeq : S = Finset.Icc (mn S) (mx S) :=
      Finset.Subset.antisymm subset_Icc_mn_mx this
    have hcard : S.card = mx S + 1 - mn S := by
      rw [show S.card = (Finset.Icc (mn S) (mx S)).card from congrArg Finset.card hSeq,
        Nat.card_Icc]
    have hle : mx S + 1 - mn S ≤ stair S := by
      have hsub2 : Finset.Icc (mx S + 1 - (mx S + 1 - mn S)) (mx S) ⊆ S := by
        intro x hx
        simp only [Finset.mem_Icc] at hx
        exact this (by simp only [Finset.mem_Icc]; omega)
      unfold stair
      exact Nat.le_findGreatest (by omega) hsub2
    omega
  simp only [Finset.mem_Icc, not_and_or, not_le] at hnb
  have hle : mn S ≤ mx S := mn_le_mx hne
  have hne' : mn S ≠ mx S - stair S := by
    intro hcon; exact hnot (hcon ▸ hmem)
  omega

lemma sum_Icc_shift (a b : ℕ) :
    ∑ i ∈ Finset.Icc (a + 1) (b + 1), i = (∑ i ∈ Finset.Icc a b, i) + (b + 1 - a) := by
  rw [← Finset.map_add_right_Icc a b 1, Finset.sum_map]
  simp [Finset.sum_add_distrib, Nat.card_Icc]

lemma mn_Icc {a b : ℕ} (h : a ≤ b) : mn (Finset.Icc a b) = a := by
  have hmem : a ∈ Finset.Icc a b := by simp [Finset.mem_Icc, h]
  refine le_antisymm (mn_le _ hmem) ?_
  have := mn_mem (Finset.Icc a b) ⟨a, hmem⟩
  simp only [Finset.mem_Icc] at this
  exact this.1

lemma mx_Icc {a b : ℕ} (h : a ≤ b) : mx (Finset.Icc a b) = b := by
  have hmem : b ∈ Finset.Icc a b := by simp [Finset.mem_Icc, h]
  refine le_antisymm ?_ (le_mx _ hmem)
  have := mx_mem (Finset.Icc a b) ⟨b, hmem⟩
  simp only [Finset.mem_Icc] at this
  exact this.2

end Basic

section CaseA

variable {S : Finset ℕ}

/-- In case A (smallest part at most the staircase length), if `S` is not exceptional then
twice the smallest part is at most the largest part. -/
lemma two_mn_le_mx (h0 : 0 ∉ S) (hne : S.Nonempty) (hA : mn S ≤ stair S) (hnex : ¬ IsExc S) :
    2 * mn S ≤ mx S := by
  by_contra hcon
  push_neg at hcon
  have hs1 : 1 ≤ mn S := one_le_mn h0 hne
  have hsM : mn S ≤ mx S := mn_le_mx hne
  have hblock : Finset.Icc (mx S + 1 - stair S) (mx S) ⊆ S := stair_block_sub_self h0 hne
  have hsub : Finset.Icc (mn S) (mx S) ⊆ S := by
    intro x hx
    simp only [Finset.mem_Icc] at hx
    exact hblock (by simp only [Finset.mem_Icc]; omega)
  have hSeq : S = Finset.Icc (mn S) (mx S) := Finset.Subset.antisymm subset_Icc_mn_mx hsub
  have hstle : stair S ≤ mx S + 1 - mn S := by
    have := hblock (show mx S + 1 - stair S ∈ Finset.Icc (mx S + 1 - stair S) (mx S) by
      simp only [Finset.mem_Icc]; have := stair_le_mx (S := S); omega)
    have hmm := mn_le S this
    have := stair_le_mx (S := S)
    omega
  have hstge : mx S + 1 - mn S ≤ stair S := by
    have hsub2 : Finset.Icc (mx S + 1 - (mx S + 1 - mn S)) (mx S) ⊆ S := by
      intro x hx
      simp only [Finset.mem_Icc] at hx
      exact hsub (by simp only [Finset.mem_Icc]; omega)
    unfold stair
    exact Nat.le_findGreatest (by omega) hsub2
  have hMeq : mx S = 2 * mn S - 1 := by omega
  refine hnex ⟨mn S, hs1, Or.inl ?_⟩
  rw [← hMeq]
  exact hSeq

/-- The properties of Franklin's move in case A. -/
lemma caseA (h0 : 0 ∉ S) (hne : S.Nonempty) (hA : mn S ≤ stair S) (hnex : ¬ IsExc S) :
    0 ∉ fA S ∧ (∑ i ∈ fA S, i) = ∑ i ∈ S, i ∧ (fA S).card + 1 = S.card ∧
      ¬ IsExc (fA S) ∧ franklin (fA S) = S := by
  have hs1 : 1 ≤ mn S := one_le_mn h0 hne
  have hsS : mn S ∈ S := mn_mem S hne
  have hMS : mx S ∈ S := mx_mem S hne
  have hsM : mn S ≤ mx S := le_mx S hsS
  have h2s : 2 * mn S ≤ mx S := two_mn_le_mx h0 hne hA hnex
  have hleM : ∀ x ∈ S, x ≤ mx S := fun x hx => le_mx S hx
  have hges : ∀ x ∈ S, mn S ≤ x := fun x hx => mn_le S hx
  have hstM := stair_le_mx (S := S)
  have hblock : Finset.Icc (mx S + 1 - mn S) (mx S) ⊆ S := by
    intro x hx
    simp only [Finset.mem_Icc] at hx
    exact stair_block_sub_self h0 hne (by simp only [Finset.mem_Icc]; omega)
  have hBcard : (Finset.Icc (mx S + 1 - mn S) (mx S)).card = mn S := by
    rw [Nat.card_Icc]; omega
  have hTdef : fA S =
      ((S.erase (mn S)) \ Finset.Icc (mx S + 1 - mn S) (mx S)) ∪
        Finset.Icc (mx S + 2 - mn S) (mx S + 1) := rfl
  have hmemT : ∀ x, x ∈ fA S ↔
      ((x ∈ S ∧ x ≠ mn S ∧ x ≤ mx S - mn S) ∨ (mx S + 2 - mn S ≤ x ∧ x ≤ mx S + 1)) := by
    intro x
    rw [hTdef]
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_Icc]
    constructor
    · rintro (⟨⟨hxs, hxS⟩, hxb⟩ | h)
      · refine Or.inl ⟨hxS, hxs, ?_⟩
        have := hleM x hxS
        push_neg at hxb
        by_cases hle : mx S + 1 - mn S ≤ x
        · have := hxb hle; omega
        · omega
      · exact Or.inr h
    · rintro (⟨hxS, hxs, hxle⟩ | h)
      · refine Or.inl ⟨⟨hxs, hxS⟩, ?_⟩
        simp only [not_and, not_le]
        omega
      · exact Or.inr h
  have hB_sub_erase : Finset.Icc (mx S + 1 - mn S) (mx S) ⊆ S.erase (mn S) := by
    intro x hx
    have hx' := hx
    simp only [Finset.mem_Icc] at hx'
    rw [Finset.mem_erase]
    exact ⟨by omega, hblock hx⟩
  have hdisj : Disjoint ((S.erase (mn S)) \ Finset.Icc (mx S + 1 - mn S) (mx S))
      (Finset.Icc (mx S + 2 - mn S) (mx S + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_Icc, not_and, not_le] at hx hx2
    have hxS : x ∈ S := hx.1.2
    have := hleM x hxS
    have h2 := hx.2
    by_cases hle : mx S + 1 - mn S ≤ x
    · have := h2 hle; omega
    · omega
  have hsumB : ∑ i ∈ Finset.Icc (mx S + 2 - mn S) (mx S + 1), i
      = (∑ i ∈ Finset.Icc (mx S + 1 - mn S) (mx S), i) + mn S := by
    have h1 : mx S + 2 - mn S = (mx S + 1 - mn S) + 1 := by omega
    rw [h1, sum_Icc_shift]
    congr 1
    omega
  have hsum : (∑ i ∈ fA S, i) = ∑ i ∈ S, i := by
    rw [hTdef, Finset.sum_union hdisj, hsumB, ← add_assoc,
      Finset.sum_sdiff hB_sub_erase]
    exact Finset.sum_erase_add S _ hsS
  have hcard : (fA S).card + 1 = S.card := by
    have hcb : (Finset.Icc (mx S + 1 - mn S) (mx S)).card ≤ (S.erase (mn S)).card :=
      Finset.card_le_card hB_sub_erase
    rw [hBcard, Finset.card_erase_of_mem hsS] at hcb
    have h1 : 1 ≤ S.card := Finset.card_pos.mpr hne
    rw [hTdef, Finset.card_union_of_disjoint hdisj, Finset.card_sdiff_of_subset hB_sub_erase, hBcard,
      Finset.card_erase_of_mem hsS, Nat.card_Icc]
    omega
  have h0T : 0 ∉ fA S := by
    intro hmem
    rcases (hmemT 0).mp hmem with ⟨h1, _, _⟩ | ⟨h1, _⟩
    · exact h0 h1
    · omega
  have hMT_mem : mx S + 1 ∈ fA S := (hmemT _).mpr (Or.inr ⟨by omega, le_refl _⟩)
  have hTne : (fA S).Nonempty := ⟨mx S + 1, hMT_mem⟩
  have hTmx : mx (fA S) = mx S + 1 := by
    refine le_antisymm ?_ (le_mx _ hMT_mem)
    have hall : ∀ x ∈ fA S, x ≤ mx S + 1 := by
      intro x hx
      rcases (hmemT x).mp hx with ⟨h1, _, h3⟩ | ⟨_, h3⟩
      · omega
      · exact h3
    exact hall _ (mx_mem _ hTne)
  have hTmn_gt : mn S < mn (fA S) := by
    have hmem := mn_mem (fA S) hTne
    rcases (hmemT _).mp hmem with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · have := hges _ h1; omega
    · omega
  have hnotinT : mx S + 1 - mn S ∉ fA S := by
    intro hmem
    rcases (hmemT _).mp hmem with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ <;> omega
  have hTstair : stair (fA S) = mn S := by
    have hlow : mn S ≤ stair (fA S) := by
      unfold stair
      rw [hTmx]
      refine Nat.le_findGreatest (by omega) ?_
      intro x hx
      simp only [Finset.mem_Icc] at hx
      exact (hmemT x).mpr (Or.inr ⟨by omega, by omega⟩)
    by_contra hcon
    have hgt : mn S < stair (fA S) := lt_of_le_of_ne hlow (fun h => hcon h.symm)
    have hsub := stair_block_sub_self h0T hTne
    have hle := stair_le_mx (S := fA S)
    rw [hTmx] at hsub hle
    exact hnotinT (hsub (by simp only [Finset.mem_Icc]; omega))
  have hTnex : ¬ IsExc (fA S) := by
    rintro ⟨c, hc1, hcase | hcase⟩
    · have hmn' : mn (fA S) = c := by rw [hcase]; exact mn_Icc (by omega)
      have hmx' : mx (fA S) = 2 * c - 1 := by rw [hcase]; exact mx_Icc (by omega)
      rw [hTmx] at hmx'
      apply hnotinT
      rw [hcase]
      simp only [Finset.mem_Icc]
      omega
    · have hmn' : mn (fA S) = c + 1 := by rw [hcase]; exact mn_Icc (by omega)
      have hmx' : mx (fA S) = 2 * c := by rw [hcase]; exact mx_Icc (by omega)
      rw [hTmx] at hmx'
      apply hnotinT
      rw [hcase]
      simp only [Finset.mem_Icc]
      omega
  refine ⟨h0T, hsum, hcard, hTnex, ?_⟩
  rw [franklin, if_neg (by omega : ¬ (mn (fA S) ≤ stair (fA S))), fB, hTstair, hTmx]
  ext x
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_sdiff, Finset.mem_Icc,
    not_and, not_le, hmemT x]
  constructor
  · rintro (rfl | ⟨h1, h2⟩ | h3)
    · exact hsS
    · rcases h1 with ⟨hxS, _, _⟩ | ⟨ha, hb⟩
      · exact hxS
      · have := h2 (by omega)
        omega
    · exact hblock (by simp only [Finset.mem_Icc]; omega)
  · intro hxS
    by_cases hxs : x = mn S
    · exact Or.inl hxs
    · have hxle := hleM x hxS
      have hxge := hges x hxS
      by_cases hbig : mx S + 1 - mn S ≤ x
      · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
      · exact Or.inr (Or.inl ⟨Or.inl ⟨hxS, hxs, by omega⟩, by omega⟩)

end CaseA

section CaseB

variable {S : Finset ℕ}

/-- In case B (smallest part exceeding the staircase length), if `S` is not exceptional then
twice the staircase length is less than the largest part. -/
lemma two_stair_lt_mx (h0 : 0 ∉ S) (hne : S.Nonempty) (hB : stair S < mn S) (hnex : ¬ IsExc S) :
    2 * stair S < mx S := by
  have hst1 : 1 ≤ stair S := one_le_stair h0 hne
  have hstM := stair_le_mx (S := S)
  rcases eq_or_lt_of_le (stair_le_card h0 hne) with heq | hlt
  · have hSeq : S = Finset.Icc (mx S + 1 - stair S) (mx S) :=
      eq_stair_block_of_card h0 hne heq.symm
    have hmn' : mn S = mx S + 1 - stair S := by
      conv_lhs => rw [hSeq]
      exact mn_Icc (by omega)
    have hM2 : mx S ≠ 2 * stair S := by
      intro hcon
      refine hnex ⟨stair S, hst1, Or.inr ?_⟩
      have hIcc : Finset.Icc (stair S + 1) (2 * stair S)
          = Finset.Icc (mx S + 1 - stair S) (mx S) := by
        congr 1 <;> omega
      rw [hIcc]
      exact hSeq
    omega
  · have := mn_lt_of_stair_lt_card h0 hne hlt
    omega

/-- The properties of Franklin's move in case B. -/
lemma caseB (h0 : 0 ∉ S) (hne : S.Nonempty) (hB : ¬ (mn S ≤ stair S)) (hnex : ¬ IsExc S) :
    0 ∉ fB S ∧ (∑ i ∈ fB S, i) = ∑ i ∈ S, i ∧ (fB S).card = S.card + 1 ∧
      ¬ IsExc (fB S) ∧ franklin (fB S) = S := by
  push_neg at hB
  have hs1 : 1 ≤ mn S := one_le_mn h0 hne
  have hsS : mn S ∈ S := mn_mem S hne
  have hMS : mx S ∈ S := mx_mem S hne
  have hsM : mn S ≤ mx S := le_mx S hsS
  have hst1 : 1 ≤ stair S := one_le_stair h0 hne
  have hstM := stair_le_mx (S := S)
  have hkey : 2 * stair S < mx S := two_stair_lt_mx h0 hne hB hnex
  have hleM : ∀ x ∈ S, x ≤ mx S := fun x hx => le_mx S hx
  have hges : ∀ x ∈ S, mn S ≤ x := fun x hx => mn_le S hx
  have hblock : Finset.Icc (mx S + 1 - stair S) (mx S) ⊆ S := stair_block_sub_self h0 hne
  have hBcard : (Finset.Icc (mx S + 1 - stair S) (mx S)).card = stair S := card_stair_block
  have hnotmem : mx S - stair S ∉ S := stair_not_mem h0 hne
  have hTdef : fB S = insert (stair S)
      ((S \ Finset.Icc (mx S + 1 - stair S) (mx S)) ∪
        Finset.Icc (mx S - stair S) (mx S - 1)) := rfl
  have hmemT : ∀ x, x ∈ fB S ↔
      (x = stair S ∨ (x ∈ S ∧ x ≤ mx S - stair S) ∨
        (mx S - stair S ≤ x ∧ x ≤ mx S - 1)) := by
    intro x
    rw [hTdef]
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_sdiff, Finset.mem_Icc,
      not_and, not_le]
    constructor
    · rintro (h | ⟨hxS, hxb⟩ | h)
      · exact Or.inl h
      · refine Or.inr (Or.inl ⟨hxS, ?_⟩)
        have := hleM x hxS
        by_cases hle : mx S + 1 - stair S ≤ x
        · have := hxb hle; omega
        · omega
      · exact Or.inr (Or.inr h)
    · rintro (h | ⟨hxS, hxle⟩ | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨hxS, by omega⟩)
      · exact Or.inr (Or.inr h)
  have hlowS : ∀ x ∈ S, x ∉ Finset.Icc (mx S + 1 - stair S) (mx S) → x ≤ mx S - stair S - 1 := by
    intro x hxS hxb
    simp only [Finset.mem_Icc, not_and, not_le] at hxb
    have h1 := hleM x hxS
    have h2 : x ≠ mx S - stair S := by
      intro hcon; exact hnotmem (hcon ▸ hxS)
    by_cases hle : mx S + 1 - stair S ≤ x
    · have := hxb hle; omega
    · omega
  have hdisj : Disjoint (S \ Finset.Icc (mx S + 1 - stair S) (mx S))
      (Finset.Icc (mx S - stair S) (mx S - 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    simp only [Finset.mem_sdiff] at hx
    have := hlowS x hx.1 hx.2
    simp only [Finset.mem_Icc] at hx2
    omega
  have hsigma_notmem : stair S ∉ (S \ Finset.Icc (mx S + 1 - stair S) (mx S)) ∪
      Finset.Icc (mx S - stair S) (mx S - 1) := by
    intro hmem
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_Icc] at hmem
    rcases hmem with ⟨hxS, _⟩ | ⟨h1, h2⟩
    · have := hges _ hxS; omega
    · omega
  have hsumB : ∑ i ∈ Finset.Icc (mx S + 1 - stair S) (mx S), i
      = (∑ i ∈ Finset.Icc (mx S - stair S) (mx S - 1), i) + stair S := by
    have h1 : mx S + 1 - stair S = (mx S - stair S) + 1 := by omega
    have h2 : mx S = (mx S - 1) + 1 := by omega
    rw [h1]
    rw [show mx S = (mx S - 1) + 1 from h2]
    rw [sum_Icc_shift]
    congr 1
    omega
  have hsum : (∑ i ∈ fB S, i) = ∑ i ∈ S, i := by
    rw [hTdef, Finset.sum_insert hsigma_notmem, Finset.sum_union hdisj]
    have hs2 : (∑ i ∈ S \ Finset.Icc (mx S + 1 - stair S) (mx S), i)
        + (∑ i ∈ Finset.Icc (mx S + 1 - stair S) (mx S), i) = ∑ i ∈ S, i :=
      Finset.sum_sdiff hblock
    omega
  have hcard : (fB S).card = S.card + 1 := by
    have hsub : (Finset.Icc (mx S + 1 - stair S) (mx S)).card ≤ S.card :=
      Finset.card_le_card hblock
    rw [hBcard] at hsub
    rw [hTdef, Finset.card_insert_of_notMem hsigma_notmem,
      Finset.card_union_of_disjoint hdisj, Finset.card_sdiff_of_subset hblock, hBcard,
      Nat.card_Icc]
    omega
  have h0T : 0 ∉ fB S := by
    intro hmem
    rcases (hmemT 0).mp hmem with h | ⟨h1, _⟩ | ⟨h1, h2⟩
    · omega
    · exact h0 h1
    · omega
  have hsigma_mem : stair S ∈ fB S := (hmemT _).mpr (Or.inl rfl)
  have hTne : (fB S).Nonempty := ⟨stair S, hsigma_mem⟩
  have hMmem : mx S - 1 ∈ fB S := (hmemT _).mpr (Or.inr (Or.inr ⟨by omega, le_refl _⟩))
  have hTmx : mx (fB S) = mx S - 1 := by
    refine le_antisymm ?_ (le_mx _ hMmem)
    have hall : ∀ x ∈ fB S, x ≤ mx S - 1 := by
      intro x hx
      rcases (hmemT x).mp hx with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · omega
      · omega
      · exact h2
    exact hall _ (mx_mem _ hTne)
  have hTmn : mn (fB S) = stair S := by
    refine le_antisymm (mn_le _ hsigma_mem) ?_
    have hall : ∀ x ∈ fB S, stair S ≤ x := by
      intro x hx
      rcases (hmemT x).mp hx with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · omega
      · have := hges _ h1; omega
      · omega
    exact hall _ (mn_mem _ hTne)
  have hTstair : stair S ≤ stair (fB S) := by
    refine le_stair (S := fB S) (by rw [hTmx]; omega) ?_
    rw [hTmx]
    intro x hx
    simp only [Finset.mem_Icc] at hx
    exact (hmemT x).mpr (Or.inr (Or.inr ⟨by omega, by omega⟩))
  have hTnex : ¬ IsExc (fB S) := by
    rintro ⟨c, hc1, hcase | hcase⟩
    · have hmn' : mn (fB S) = c := by rw [hcase]; exact mn_Icc (by omega)
      have hmx' : mx (fB S) = 2 * c - 1 := by rw [hcase]; exact mx_Icc (by omega)
      rw [hTmn] at hmn'
      rw [hTmx] at hmx'
      omega
    · have hmn' : mn (fB S) = c + 1 := by rw [hcase]; exact mn_Icc (by omega)
      have hmx' : mx (fB S) = 2 * c := by rw [hcase]; exact mx_Icc (by omega)
      rw [hTmn] at hmn'
      rw [hTmx] at hmx'
      omega
  refine ⟨h0T, hsum, hcard, hTnex, ?_⟩
  rw [franklin, if_pos (by omega : mn (fB S) ≤ stair (fB S)), fA, hTmn, hTmx]
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_Icc,
    not_and, not_le, hmemT x]
  constructor
  · rintro (⟨⟨hxne, hxT⟩, hxb⟩ | h)
    · rcases hxT with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd h hxne
      · exact h1
      · have := hxb (by omega); omega
    · exact hblock (by simp only [Finset.mem_Icc]; omega)
  · intro hxS
    have hxle := hleM x hxS
    have hxge := hges x hxS
    by_cases hbig : mx S + 1 - stair S ≤ x
    · exact Or.inr ⟨by omega, by omega⟩
    · have hlow : x ≤ mx S - stair S - 1 :=
        hlowS x hxS (by simp only [Finset.mem_Icc, not_and, not_le]; omega)
      exact Or.inl ⟨⟨by omega, Or.inr (Or.inl ⟨hxS, by omega⟩)⟩, by omega⟩

end CaseB

section Involution

open scoped Classical in
/-- The non-exceptional distinct-part partitions of `n ≥ 1` cancel in pairs. -/
theorem sum_nonexc_eq_zero (n : ℕ) (hn : 1 ≤ n) :
    ∑ S ∈ (D n).filter (fun S => ¬ IsExc S), (-1 : ℤ) ^ S.card = 0 := by
  have key : ∀ S ∈ (D n).filter (fun S => ¬ IsExc S),
      ((-1 : ℤ) ^ S.card + (-1 : ℤ) ^ (franklin S).card = 0) ∧
        (franklin S).card ≠ S.card ∧
        franklin S ∈ (D n).filter (fun S => ¬ IsExc S) ∧
        franklin (franklin S) = S := by
    intro S hS
    simp only [Finset.mem_filter, mem_D_iff] at hS
    obtain ⟨⟨h0, hsum⟩, hnex⟩ := hS
    have hne : S.Nonempty := by
      rcases Finset.eq_empty_or_nonempty S with rfl | h
      · simp only [Finset.sum_empty] at hsum; omega
      · exact h
    by_cases hcase : mn S ≤ stair S
    · obtain ⟨h0T, hsumT, hcardT, hnexT, hinv⟩ := caseA h0 hne hcase hnex
      have hfr : franklin S = fA S := if_pos hcase
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hfr, ← hcardT, pow_succ]; ring
      · rw [hfr]; omega
      · rw [hfr]
        simp only [Finset.mem_filter, mem_D_iff]
        exact ⟨⟨h0T, by rw [hsumT, hsum]⟩, hnexT⟩
      · rw [hfr]; exact hinv
    · obtain ⟨h0T, hsumT, hcardT, hnexT, hinv⟩ := caseB h0 hne hcase hnex
      have hfr : franklin S = fB S := if_neg hcase
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hfr, hcardT, pow_succ]; ring
      · rw [hfr]; omega
      · rw [hfr]
        simp only [Finset.mem_filter, mem_D_iff]
        exact ⟨⟨h0T, by rw [hsumT, hsum]⟩, hnexT⟩
      · rw [hfr]; exact hinv
  refine Finset.sum_involution (fun S _ => franklin S) (fun S hS => (key S hS).1)
    (fun S hS _ => ?_) (fun S hS => (key S hS).2.2.1) (fun S hS => (key S hS).2.2.2)
  intro hcon
  simp only at hcon
  exact (key S hS).2.1 (by rw [hcon])

end Involution

section Exceptional

lemma two_mul_sum_Icc_add (a d : ℕ) :
    2 * (∑ i ∈ Finset.Icc a (a + d), i) = (2 * a + d) * (d + 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [show a + (d + 1) = (a + d) + 1 from rfl, Finset.sum_Icc_succ_top (by omega)]
    rw [Nat.mul_add, ih]
    ring

lemma two_mul_sum_pent1 {c : ℕ} (hc : 1 ≤ c) :
    2 * (∑ i ∈ Finset.Icc c (2 * c - 1), i) = c * (3 * c - 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, c = e + 1 := ⟨c - 1, by omega⟩
  have h1 : 2 * (e + 1) - 1 = (e + 1) + e := by omega
  have h2 : 3 * (e + 1) - 1 = 3 * e + 2 := by omega
  rw [h1, h2, two_mul_sum_Icc_add]
  ring

lemma two_mul_sum_pent2 {c : ℕ} (hc : 1 ≤ c) :
    2 * (∑ i ∈ Finset.Icc (c + 1) (2 * c), i) = c * (3 * c + 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, c = e + 1 := ⟨c - 1, by omega⟩
  have h1 : 2 * (e + 1) = (e + 1 + 1) + e := by omega
  rw [h1, two_mul_sum_Icc_add]
  ring

lemma card_pent1 {c : ℕ} (hc : 1 ≤ c) : (Finset.Icc c (2 * c - 1)).card = c := by
  rw [Nat.card_Icc]; omega

lemma card_pent2 {c : ℕ} (hc : 1 ≤ c) : (Finset.Icc (c + 1) (2 * c)).card = c := by
  rw [Nat.card_Icc]; omega

open scoped Classical in
lemma exc_eq (n : ℕ) :
    (D n).filter (fun S => IsExc S) =
      (((Finset.Icc 1 n).filter (fun c => c * (3 * c - 1) = 2 * n)).image
          (fun c => Finset.Icc c (2 * c - 1))) ∪
      (((Finset.Icc 1 n).filter (fun c => c * (3 * c + 1) = 2 * n)).image
          (fun c => Finset.Icc (c + 1) (2 * c))) := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image, mem_D_iff, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h0, hsum⟩, c, hc1, hcase | hcase⟩
    · refine Or.inl ⟨c, ⟨⟨hc1, ?_⟩, ?_⟩, hcase.symm⟩
      · have h2 : 2 * n = c * (3 * c - 1) := by
          rw [← hsum, hcase]; exact two_mul_sum_pent1 hc1
        have h3 : c * 2 ≤ c * (3 * c - 1) := Nat.mul_le_mul_left c (by omega)
        omega
      · rw [← hsum, hcase]; exact (two_mul_sum_pent1 hc1).symm
    · refine Or.inr ⟨c, ⟨⟨hc1, ?_⟩, ?_⟩, hcase.symm⟩
      · have h2 : 2 * n = c * (3 * c + 1) := by
          rw [← hsum, hcase]; exact two_mul_sum_pent2 hc1
        have h3 : c * 2 ≤ c * (3 * c + 1) := Nat.mul_le_mul_left c (by omega)
        omega
      · rw [← hsum, hcase]; exact (two_mul_sum_pent2 hc1).symm
  · rintro (⟨c, ⟨⟨hc1, hcn⟩, hpent⟩, rfl⟩ | ⟨c, ⟨⟨hc1, hcn⟩, hpent⟩, rfl⟩)
    · refine ⟨⟨?_, ?_⟩, c, hc1, Or.inl rfl⟩
      · simp only [Finset.mem_Icc]; omega
      · have := two_mul_sum_pent1 hc1
        omega
    · refine ⟨⟨?_, ?_⟩, c, hc1, Or.inr rfl⟩
      · simp only [Finset.mem_Icc]; omega
      · have := two_mul_sum_pent2 hc1
        omega

open scoped Classical in
lemma sum_exc (n : ℕ) :
    ∑ S ∈ (D n).filter (fun S => IsExc S), (-1 : ℤ) ^ S.card
      = (∑ c ∈ (Finset.Icc 1 n).filter (fun c => c * (3 * c - 1) = 2 * n), (-1 : ℤ) ^ c)
      + (∑ c ∈ (Finset.Icc 1 n).filter (fun c => c * (3 * c + 1) = 2 * n), (-1 : ℤ) ^ c) := by
  have hdisj : Disjoint
      (((Finset.Icc 1 n).filter (fun c => c * (3 * c - 1) = 2 * n)).image
        (fun c => Finset.Icc c (2 * c - 1)))
      (((Finset.Icc 1 n).filter (fun c => c * (3 * c + 1) = 2 * n)).image
        (fun c => Finset.Icc (c + 1) (2 * c))) := by
    rw [Finset.disjoint_left]
    rintro S hS1 hS2
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at hS1 hS2
    obtain ⟨c, ⟨⟨hc1, _⟩, _⟩, rfl⟩ := hS1
    obtain ⟨d, ⟨⟨hd1, _⟩, _⟩, hEq⟩ := hS2
    have hmn : mn (Finset.Icc (d + 1) (2 * d)) = mn (Finset.Icc c (2 * c - 1)) := by rw [hEq]
    have hmx : mx (Finset.Icc (d + 1) (2 * d)) = mx (Finset.Icc c (2 * c - 1)) := by rw [hEq]
    rw [mn_Icc (by omega), mn_Icc (by omega)] at hmn
    rw [mx_Icc (by omega), mx_Icc (by omega)] at hmx
    omega
  have hinj1 : Set.InjOn (fun c => Finset.Icc c (2 * c - 1))
      ↑((Finset.Icc 1 n).filter (fun c => c * (3 * c - 1) = 2 * n)) := by
    intro a ha b hb hEq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ha hb
    dsimp only at hEq
    have hmn : mn (Finset.Icc a (2 * a - 1)) = mn (Finset.Icc b (2 * b - 1)) := by rw [hEq]
    rw [mn_Icc (by omega), mn_Icc (by omega)] at hmn
    exact hmn
  have hinj2 : Set.InjOn (fun c => Finset.Icc (c + 1) (2 * c))
      ↑((Finset.Icc 1 n).filter (fun c => c * (3 * c + 1) = 2 * n)) := by
    intro a ha b hb hEq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ha hb
    dsimp only at hEq
    have hmn : mn (Finset.Icc (a + 1) (2 * a)) = mn (Finset.Icc (b + 1) (2 * b)) := by rw [hEq]
    rw [mn_Icc (by omega), mn_Icc (by omega)] at hmn
    omega
  rw [exc_eq n, Finset.sum_union hdisj, Finset.sum_image hinj1, Finset.sum_image hinj2]
  congr 1
  · refine Finset.sum_congr rfl (fun c hc => ?_)
    simp only [Finset.mem_filter, Finset.mem_Icc] at hc
    rw [card_pent1 (by omega)]
  · refine Finset.sum_congr rfl (fun c hc => ?_)
    simp only [Finset.mem_filter, Finset.mem_Icc] at hc
    rw [card_pent2 (by omega)]

end Exceptional

section Core

open scoped Classical in
/-- The combinatorial core of Euler's pentagonal number theorem: the signed count of
partitions of `n` into distinct parts. -/
theorem sum_D_eq (n : ℕ) :
    ∑ S ∈ D n, (-1 : ℤ) ^ S.card
      = (∑ c ∈ (Finset.Icc 1 n).filter (fun c => c * (3 * c - 1) = 2 * n), (-1 : ℤ) ^ c)
      + (∑ c ∈ (Finset.Icc 1 n).filter (fun c => c * (3 * c + 1) = 2 * n), (-1 : ℤ) ^ c)
      + (if n = 0 then 1 else 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
    rw [D, h1, Finset.powerset_empty, Finset.filter_singleton, if_pos (by simp)]
    simp
  · rw [if_neg (by omega), add_zero,
      ← Finset.sum_filter_add_sum_filter_not (D n) (fun S => IsExc S),
      sum_nonexc_eq_zero n hn, add_zero, sum_exc n]

end Core

end EulerPentagonal

/-
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
import RequestProject.Franklin

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

namespace Math

open EulerPentagonal

/-- Extracting the `n`-th coefficient of the finite product `∏_{k=1}^{N} (1 - X^k)`:
it is the signed count of the subsets of `{1, …, N}` summing to `n`. -/
lemma coeff_prod_one_sub_X_pow (N n : ℕ) :
    (PowerSeries.coeff n) (∏ k ∈ Finset.Icc 1 N, (1 - (PowerSeries.X : PowerSeries ℤ) ^ k))
      = ∑ S ∈ (Finset.Icc 1 N).powerset.filter (fun S => ∑ i ∈ S, i = n), (-1 : ℤ) ^ S.card := by
  have h : ∀ k : ℕ, (1 - (PowerSeries.X : PowerSeries ℤ) ^ k) = (-(PowerSeries.X ^ k) + 1) := by
    intro k; ring
  simp_rw [h]
  rw [Finset.prod_add]
  have key : ∀ t : Finset ℕ,
      ((∏ i ∈ t, -(PowerSeries.X : PowerSeries ℤ) ^ i) * ∏ _i ∈ (Finset.Icc 1 N) \ t, 1)
        = (-1 : ℤ) ^ t.card • (PowerSeries.X : PowerSeries ℤ) ^ (∑ i ∈ t, i) := by
    intro t
    simp [Finset.prod_neg, ← Finset.prod_pow_eq_pow_sum]
  simp_rw [key, map_sum, map_smul, PowerSeries.coeff_X_pow, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rcases eq_or_ne n (∑ i ∈ t, i) with ht | ht
  · rw [if_pos ht, if_pos ht.symm]
  · rw [if_neg ht, if_neg (fun hh => ht hh.symm)]

/-- For `n ≤ N`, the subsets of `{1, …, N}` summing to `n` are exactly the partitions of `n`
into distinct positive parts. -/
lemma powerset_filter_eq_D {N n : ℕ} (hN : n ≤ N) :
    (Finset.Icc 1 N).powerset.filter (fun S => ∑ i ∈ S, i = n) = D n := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_powerset, mem_D_iff]
  constructor
  · rintro ⟨hsub, hsum⟩
    refine ⟨fun h0 => ?_, hsum⟩
    have := hsub h0
    simp only [Finset.mem_Icc] at this
    omega
  · rintro ⟨h0, hsum⟩
    refine ⟨fun x hx => ?_, hsum⟩
    have hx1 : 1 ≤ x := by
      rcases Nat.eq_zero_or_pos x with h | h
      · exact absurd (h ▸ hx) h0
      · exact h
    have hxn : x ≤ n := by
      rw [← hsum]
      exact Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) hx
    simp only [Finset.mem_Icc]
    omega

/-- Splitting a sum over `[-n, n] ⊆ ℤ` into the term at `0` and the positive and negative parts. -/
lemma sum_Icc_int_split (n : ℕ) (f : ℤ → ℤ) :
    ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), f k
      = f 0 + ((∑ c ∈ Finset.Icc 1 n, f (c : ℤ)) + ∑ c ∈ Finset.Icc 1 n, f (-(c : ℤ))) := by
  have hpos : Set.InjOn (fun c : ℕ => (c : ℤ)) ↑(Finset.Icc 1 n) := by
    intro a _ b _ hab
    exact Nat.cast_injective (by simpa using hab)
  have hneg : Set.InjOn (fun c : ℕ => -(c : ℤ)) ↑(Finset.Icc 1 n) := by
    intro a _ b _ hab
    have : (a : ℤ) = (b : ℤ) := by simpa using neg_injective hab
    exact_mod_cast this
  have hdisj : Disjoint ((Finset.Icc 1 n).image (fun c : ℕ => (c : ℤ)))
      ((Finset.Icc 1 n).image (fun c : ℕ => -(c : ℤ))) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_image, Finset.mem_Icc] at hk1 hk2
    obtain ⟨a, ⟨ha1, _⟩, rfl⟩ := hk1
    obtain ⟨b, ⟨hb1, _⟩, hb⟩ := hk2
    omega
  have h0 : (0 : ℤ) ∉ ((Finset.Icc 1 n).image (fun c : ℕ => (c : ℤ))) ∪
      ((Finset.Icc 1 n).image (fun c : ℕ => -(c : ℤ))) := by
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc, not_or]
    constructor <;> rintro ⟨c, ⟨hc1, _⟩, hc⟩ <;> omega
  have hset : Finset.Icc (-(n : ℤ)) (n : ℤ) = insert 0
      (((Finset.Icc 1 n).image (fun c : ℕ => (c : ℤ))) ∪
        ((Finset.Icc 1 n).image (fun c : ℕ => -(c : ℤ)))) := by
    ext k
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
    constructor
    · intro hk
      rcases lt_trichotomy k 0 with h | h | h
      · exact Or.inr (Or.inr ⟨(-k).toNat, ⟨by omega, by omega⟩, by omega⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨k.toNat, ⟨by omega, by omega⟩, by omega⟩)
    · rintro (rfl | ⟨c, ⟨hc1, hc2⟩, rfl⟩ | ⟨c, ⟨hc1, hc2⟩, rfl⟩) <;> omega
  rw [hset, Finset.sum_insert h0, Finset.sum_union hdisj, Finset.sum_image hpos,
    Finset.sum_image hneg]

/-- **Euler's pentagonal number theorem**.

For every `n ≤ N`, the coefficient of `X ^ n` in the partition generating function
`∏_{k=1}^{N} (1 - X ^ k)` (which is the coefficient of `X ^ n` in the infinite product
`∏_{k ≥ 1} (1 - X ^ k)`, since larger factors do not contribute to this coefficient) equals
`∑_{k ∈ ℤ} (-1) ^ k` over the integers `k` with `k (3k - 1) / 2 = n`, i.e. it is `(-1) ^ k` if
`n` is the generalized pentagonal number `k (3k - 1) / 2` and `0` otherwise. -/
theorem euler_pentagonal (n N : ℕ) (hN : n ≤ N) :
    (PowerSeries.coeff n) (∏ k ∈ Finset.Icc 1 N, (1 - (PowerSeries.X : PowerSeries ℤ) ^ k))
      = ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
          if k * (3 * k - 1) = 2 * (n : ℤ) then (-1 : ℤ) ^ k.natAbs else 0 := by
  rw [coeff_prod_one_sub_X_pow, powerset_filter_eq_D hN, sum_D_eq n,
    sum_Icc_int_split n (fun k => if k * (3 * k - 1) = 2 * (n : ℤ) then (-1 : ℤ) ^ k.natAbs else 0)]
  have hzero : (if (0 : ℤ) * (3 * 0 - 1) = 2 * (n : ℤ) then (-1 : ℤ) ^ (0 : ℤ).natAbs else 0)
      = if n = 0 then 1 else 0 := by
    by_cases hn : n = 0 <;> simp [hn]
  have hposc : ∀ c ∈ Finset.Icc 1 n,
      (if (c : ℤ) * (3 * (c : ℤ) - 1) = 2 * (n : ℤ) then (-1 : ℤ) ^ ((c : ℤ)).natAbs else 0)
        = (if c * (3 * c - 1) = 2 * n then (-1 : ℤ) ^ c else 0) := by
    intro c hc
    simp only [Finset.mem_Icc] at hc
    have hcast : ((c * (3 * c - 1) : ℕ) : ℤ) = (c : ℤ) * (3 * (c : ℤ) - 1) := by
      have : 1 ≤ 3 * c := by omega
      push_cast [Nat.cast_sub this]
      ring
    have hiff : ((c : ℤ) * (3 * (c : ℤ) - 1) = 2 * (n : ℤ)) ↔ (c * (3 * c - 1) = 2 * n) := by
      rw [← hcast]
      exact_mod_cast Iff.rfl
    have hnat : ((c : ℤ)).natAbs = c := by simp
    rw [hnat]
    by_cases hcond : c * (3 * c - 1) = 2 * n
    · rw [if_pos (hiff.mpr hcond), if_pos hcond]
    · rw [if_neg (fun h => hcond (hiff.mp h)), if_neg hcond]
  have hnegc : ∀ c ∈ Finset.Icc 1 n,
      (if (-(c : ℤ)) * (3 * (-(c : ℤ)) - 1) = 2 * (n : ℤ)
        then (-1 : ℤ) ^ ((-(c : ℤ))).natAbs else 0)
        = (if c * (3 * c + 1) = 2 * n then (-1 : ℤ) ^ c else 0) := by
    intro c hc
    simp only [Finset.mem_Icc] at hc
    have hcast : ((c * (3 * c + 1) : ℕ) : ℤ) = (-(c : ℤ)) * (3 * (-(c : ℤ)) - 1) := by
      push_cast
      ring
    have hiff : ((-(c : ℤ)) * (3 * (-(c : ℤ)) - 1) = 2 * (n : ℤ)) ↔ (c * (3 * c + 1) = 2 * n) := by
      rw [← hcast]
      exact_mod_cast Iff.rfl
    have hnat : ((-(c : ℤ))).natAbs = c := by simp
    rw [hnat]
    by_cases hcond : c * (3 * c + 1) = 2 * n
    · rw [if_pos (hiff.mpr hcond), if_pos hcond]
    · rw [if_neg (fun h => hcond (hiff.mp h)), if_neg hcond]
  rw [Finset.sum_congr rfl hposc, Finset.sum_congr rfl hnegc, hzero, Finset.sum_filter,
    Finset.sum_filter]
  ring

end Math

