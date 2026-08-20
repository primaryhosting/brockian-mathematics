import Mathlib

/-!
# Franklin's involution

Combinatorial core of Euler's pentagonal number theorem: the signed count of partitions of
`n` into distinct parts (sign `(-1)^(number of parts)`) is `0` unless `n` is a generalized
pentagonal number.

Partitions into distinct parts are encoded as finite sets of positive naturals.
-/

namespace EulerPentagonal

open Finset

/-- The largest element of `s` (junk value `0` for `s = ∅`). -/
def mx (s : Finset ℕ) : ℕ := s.sup id

/-- The smallest element of `s` (junk value `0` for `s = ∅`). -/
noncomputable def mn (s : Finset ℕ) : ℕ := sInf (↑s : Set ℕ)

/-- The length of the maximal run of consecutive integers at the top of `s`. -/
noncomputable def sl (s : Finset ℕ) : ℕ := sInf {j | mx s - j ∉ s}

lemma le_mx {s : Finset ℕ} {a : ℕ} (ha : a ∈ s) : a ≤ mx s :=
  Finset.le_sup (f := id) ha

lemma mx_mem {s : Finset ℕ} (hne : s.Nonempty) : mx s ∈ s := by
  classical
  obtain ⟨a, ha⟩ := hne
  have : mx s = s.max' ⟨a, ha⟩ := by
    rw [Finset.max'_eq_sup' , Finset.sup'_eq_sup]
    rfl
  rw [this]
  exact s.max'_mem _

lemma mn_mem {s : Finset ℕ} (hne : s.Nonempty) : mn s ∈ s := by
  obtain ⟨a, ha⟩ := hne
  exact Nat.sInf_mem ⟨a, ha⟩

lemma mn_le {s : Finset ℕ} {a : ℕ} (ha : a ∈ s) : mn s ≤ a := Nat.sInf_le ha

lemma sl_nonempty (s : Finset ℕ) (h0 : 0 ∉ s) : {j | mx s - j ∉ s}.Nonempty :=
  ⟨mx s + 1, by simpa using h0⟩

lemma sl_notMem {s : Finset ℕ} (h0 : 0 ∉ s) : mx s - sl s ∉ s :=
  Nat.sInf_mem (sl_nonempty s h0)

lemma mem_of_lt_sl {s : Finset ℕ} {i : ℕ} (hi : i < sl s) : mx s - i ∈ s := by
  by_contra h
  have h2 : sl s ≤ i := Nat.sInf_le h
  omega

lemma sl_eq {s : Finset ℕ} {j : ℕ} (h1 : mx s - j ∉ s) (h2 : ∀ i < j, mx s - i ∈ s) :
    sl s = j := by
  have hle : sl s ≤ j := Nat.sInf_le h1
  refine le_antisymm hle ?_
  by_contra h
  push_neg at h
  have hmem : sInf {j | mx s - j ∉ s} ∈ {j | mx s - j ∉ s} := Nat.sInf_mem ⟨j, h1⟩
  exact hmem (h2 _ h)

lemma basic_facts {s : Finset ℕ} (h0 : 0 ∉ s) (hne : s.Nonempty) :
    1 ≤ mn s ∧ mn s ≤ mx s ∧ 1 ≤ sl s ∧ sl s ≤ mx s ∧ mn s + sl s ≤ mx s + 1 := by
  have hm := mn_mem hne
  have hM := mx_mem hne
  have h1 : 1 ≤ mn s := by
    rcases Nat.eq_zero_or_pos (mn s) with h | h
    · exact absurd (h ▸ hm) h0
    · exact h
  have h2 : mn s ≤ mx s := mn_le hM
  have h3 : 1 ≤ sl s := by
    rcases Nat.eq_zero_or_pos (sl s) with h | h
    · exact absurd hM (by simpa [h] using sl_notMem h0)
    · exact h
  have h4 : sl s ≤ mx s := by
    by_contra h
    push_neg at h
    have := mem_of_lt_sl (s := s) (i := mx s) h
    simp only [Nat.sub_self] at this
    exact h0 this
  have h5 : mn s + sl s ≤ mx s + 1 := by
    have := mn_le (mem_of_lt_sl (s := s) (i := sl s - 1) (by omega))
    omega
  exact ⟨h1, h2, h3, h4, h5⟩

/-- Franklin's map. -/
noncomputable def franklin (s : Finset ℕ) : Finset ℕ :=
  if mn s ≤ sl s then insert (mx s + 1) ((s.erase (mn s)).erase (mx s - mn s + 1))
  else insert (sl s) (insert (mx s - sl s) (s.erase (mx s)))

/-- The exceptional configurations, on which Franklin's map is not defined/not sign-reversing. -/
def IsExc (s : Finset ℕ) : Prop :=
  if mn s ≤ sl s then mx s = 2 * mn s - 1 else mx s = 2 * sl s

lemma caseA {s : Finset ℕ} (h0 : 0 ∉ s) (hne : s.Nonempty) (hle : mn s ≤ sl s)
    (hexc : ¬ IsExc s) :
    0 ∉ franklin s ∧ (franklin s).Nonempty ∧ (∑ i ∈ franklin s, i) = ∑ i ∈ s, i ∧
      (franklin s).card + 1 = s.card ∧ ¬ IsExc (franklin s) ∧ franklin (franklin s) = s := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := basic_facts h0 hne
  have hexc0 : mx s ≠ 2 * mn s - 1 := by rw [IsExc, if_pos hle] at hexc; exact hexc
  set m := mn s with hm_def
  set M := mx s with hM_def
  have hexc' : M ≠ 2 * m - 1 := hexc0
  have h2m : 2 * m ≤ M := by omega
  have hm : m ∈ s := mn_mem hne
  have hM : M ∈ s := mx_mem hne
  have hblock : M - m + 1 ∈ s := by
    have := mem_of_lt_sl (s := s) (i := m - 1) (by omega)
    have he : M - (m - 1) = M - m + 1 := by omega
    rwa [he] at this
  have hAdef : franklin s = insert (M + 1) ((s.erase m).erase (M - m + 1)) := if_pos hle
  set A : Finset ℕ := insert (M + 1) ((s.erase m).erase (M - m + 1)) with hA_def
  have hnotin : M + 1 ∉ (s.erase m).erase (M - m + 1) := by
    intro h
    have : M + 1 ∈ s := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h)
    exact absurd (le_mx this) (by omega)
  have hmemA : ∀ x, x ∈ A ↔ x = M + 1 ∨ (x ∈ s ∧ x ≠ m ∧ x ≠ M - m + 1) := by
    intro x
    simp [hA_def, Finset.mem_insert, Finset.mem_erase]
    tauto
  have h0A : 0 ∉ A := by
    rw [hmemA]
    rintro (h | ⟨h, -, -⟩)
    · omega
    · exact h0 h
  have hneA : A.Nonempty := ⟨M + 1, by rw [hmemA]; left; rfl⟩
  -- sum
  have hsum : (∑ i ∈ A, i) = ∑ i ∈ s, i := by
    have e1 : m + ∑ i ∈ s.erase m, i = ∑ i ∈ s, i := Finset.add_sum_erase s (fun i => i) hm
    have hmem2 : M - m + 1 ∈ s.erase m := Finset.mem_erase.mpr ⟨by omega, hblock⟩
    have e2 : (M - m + 1) + ∑ i ∈ (s.erase m).erase (M - m + 1), i = ∑ i ∈ s.erase m, i :=
      Finset.add_sum_erase (s.erase m) (fun i => i) hmem2
    have e3 : (∑ i ∈ A, i) = (M + 1) + ∑ i ∈ (s.erase m).erase (M - m + 1), i := by
      rw [hA_def, Finset.sum_insert hnotin]
    omega
  -- cardinality
  have hcard : A.card + 1 = s.card := by
    have hmem2 : M - m + 1 ∈ s.erase m := Finset.mem_erase.mpr ⟨by omega, hblock⟩
    have c1 : (s.erase m).card = s.card - 1 := Finset.card_erase_of_mem hm
    have c2 : ((s.erase m).erase (M - m + 1)).card = (s.erase m).card - 1 :=
      Finset.card_erase_of_mem hmem2
    have c3 : A.card = ((s.erase m).erase (M - m + 1)).card + 1 := by
      rw [hA_def, Finset.card_insert_of_notMem hnotin]
    have hcs : 2 ≤ s.card :=
      Finset.one_lt_card.mpr ⟨m, hm, M - m + 1, hblock, by omega⟩
    omega
  -- max of A
  have hmxA : mx A = M + 1 := by
    refine le_antisymm (Finset.sup_le ?_) (le_mx (by rw [hmemA]; left; rfl))
    intro b hb
    simp only [id_eq]
    rw [hmemA] at hb
    rcases hb with h | ⟨h, -, -⟩
    · omega
    · exact le_trans (le_mx h) (by omega)
  -- min of A
  have hmnA : m + 1 ≤ mn A := by
    have hmem := mn_mem hneA
    rw [hmemA] at hmem
    rcases hmem with h | ⟨h, hne1, -⟩
    · omega
    · have := mn_le (s := s) h
      omega
  -- slope of A
  have hslA : sl A = m := by
    refine sl_eq ?_ ?_
    · intro hx
      rw [hmxA, hmemA] at hx
      rcases hx with h | ⟨-, -, h⟩ <;> omega
    · intro i hi
      rw [hmxA, hmemA]
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · left; omega
      · right
        have hmem : M - (i - 1) ∈ s := mem_of_lt_sl (by omega)
        have he : M + 1 - i = M - (i - 1) := by omega
        exact ⟨by rw [he]; exact hmem, by omega, by omega⟩
  have hnotleA : ¬ (mn A ≤ sl A) := by rw [hslA]; omega
  have hexcA : ¬ IsExc A := by
    rw [IsExc, if_neg hnotleA, hmxA, hslA]
    omega
  have hff : franklin A = s := by
    rw [franklin, if_neg hnotleA, hslA, hmxA]
    have he1 : A.erase (M + 1) = (s.erase m).erase (M - m + 1) := by
      rw [hA_def, Finset.erase_insert hnotin]
    have he2 : M + 1 - m = M - m + 1 := by omega
    rw [he1, he2, Finset.insert_erase (Finset.mem_erase.mpr ⟨by omega, hblock⟩),
      Finset.insert_erase hm]
  rw [hAdef]
  exact ⟨h0A, hneA, hsum, hcard, hexcA, hff⟩

lemma caseB {s : Finset ℕ} (h0 : 0 ∉ s) (hne : s.Nonempty) (hle : ¬ (mn s ≤ sl s))
    (hexc : ¬ IsExc s) :
    0 ∉ franklin s ∧ (franklin s).Nonempty ∧ (∑ i ∈ franklin s, i) = ∑ i ∈ s, i ∧
      (franklin s).card = s.card + 1 ∧ ¬ IsExc (franklin s) ∧ franklin (franklin s) = s := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := basic_facts h0 hne
  have hexc0 : mx s ≠ 2 * sl s := by rw [IsExc, if_neg hle] at hexc; exact hexc
  have hsn : mx s - sl s ∉ s := sl_notMem h0
  have hsig_notin : sl s ∉ s := fun h => absurd (mn_le h) (by omega)
  set m := mn s with hm_def
  set M := mx s with hM_def
  set g := sl s with hg_def
  have hexc' : M ≠ 2 * g := hexc0
  have hlt : g < m := by omega
  have hMg : 2 * g + 1 ≤ M := by omega
  have hM : M ∈ s := mx_mem hne
  have hBdef : franklin s = insert g (insert (M - g) (s.erase M)) := if_neg hle
  set B : Finset ℕ := insert g (insert (M - g) (s.erase M)) with hB_def
  have hgM : g ≠ M - g := by omega
  have hnotin1 : M - g ∉ s.erase M := fun h => hsn (Finset.mem_of_mem_erase h)
  have hnotin2 : g ∉ insert (M - g) (s.erase M) := by
    simp only [Finset.mem_insert, Finset.mem_erase]
    rintro (h | ⟨-, h⟩)
    · exact hgM h
    · exact hsig_notin h
  have hmemB : ∀ x, x ∈ B ↔ x = g ∨ x = M - g ∨ (x ∈ s ∧ x ≠ M) := by
    intro x
    simp only [hB_def, Finset.mem_insert, Finset.mem_erase]
    tauto
  have h0B : 0 ∉ B := by
    rw [hmemB]
    rintro (h | h | ⟨h, -⟩)
    · omega
    · omega
    · exact h0 h
  have hneB : B.Nonempty := ⟨g, by rw [hmemB]; left; rfl⟩
  -- sum
  have hsum : (∑ i ∈ B, i) = ∑ i ∈ s, i := by
    have e1 : M + ∑ i ∈ s.erase M, i = ∑ i ∈ s, i := Finset.add_sum_erase s (fun i => i) hM
    have e2 : (∑ i ∈ B, i) = g + ((M - g) + ∑ i ∈ s.erase M, i) := by
      rw [hB_def, Finset.sum_insert hnotin2, Finset.sum_insert hnotin1]
    omega
  -- cardinality
  have hcard : B.card = s.card + 1 := by
    have c1 : (s.erase M).card = s.card - 1 := Finset.card_erase_of_mem hM
    have c2 : B.card = (insert (M - g) (s.erase M)).card + 1 := by
      rw [hB_def, Finset.card_insert_of_notMem hnotin2]
    have c3 : (insert (M - g) (s.erase M)).card = (s.erase M).card + 1 :=
      Finset.card_insert_of_notMem hnotin1
    have hcs : 1 ≤ s.card := Finset.card_pos.mpr hne
    omega
  -- max of B
  have hmxB : mx B = M - 1 := by
    refine le_antisymm (Finset.sup_le ?_) (le_mx ?_)
    · intro b hb
      simp only [id_eq]
      rw [hmemB] at hb
      rcases hb with h | h | ⟨h, hbM⟩
      · omega
      · omega
      · have := le_mx h
        omega
    · rw [hmemB]
      rcases Nat.lt_or_ge 1 g with hg1 | hg1
      · right; right
        refine ⟨?_, by omega⟩
        have := mem_of_lt_sl (s := s) (i := 1) (by omega)
        have he : M - 1 = M - 1 := rfl
        exact this
      · right; left; omega
  -- min of B
  have hmnB : mn B = g := by
    refine le_antisymm (mn_le (by rw [hmemB]; left; rfl)) ?_
    have hmem := mn_mem hneB
    rw [hmemB] at hmem
    rcases hmem with h | h | ⟨h, -⟩
    · omega
    · omega
    · have := mn_le (s := s) h
      omega
  -- slope of B
  have hslB : g ≤ sl B := by
    by_contra hcon
    push_neg at hcon
    have hmem : mx B - sl B ∈ B := by
      rw [hmxB, hmemB]
      rcases Nat.lt_or_ge (sl B + 1) g with hcase | hcase
      · right; right
        have hs : M - (sl B + 1) ∈ s := mem_of_lt_sl (s := s) (i := sl B + 1) (by omega)
        have he : M - 1 - sl B = M - (sl B + 1) := by omega
        exact ⟨by rw [he]; exact hs, by omega⟩
      · right; left; omega
    exact (sl_notMem h0B) hmem
  have hleB : mn B ≤ sl B := by rw [hmnB]; exact hslB
  have hexcB : ¬ IsExc B := by
    rw [IsExc, if_pos hleB, hmxB, hmnB]
    omega
  have hff : franklin B = s := by
    rw [franklin, if_pos hleB, hmnB, hmxB]
    have he1 : B.erase g = insert (M - g) (s.erase M) := by
      rw [hB_def, Finset.erase_insert hnotin2]
    have he2 : M - 1 - g + 1 = M - g := by omega
    have he3 : M - 1 + 1 = M := by omega
    rw [he1, he2, Finset.erase_insert hnotin1, he3, Finset.insert_erase hM]
  rw [hBdef]
  exact ⟨h0B, hneB, hsum, hcard, hexcB, hff⟩

/-! ### Pentagonal numbers and the exceptional configurations -/

lemma two_sum_Icc (a b : ℕ) (hab : a ≤ b + 1) :
    2 * (∑ x ∈ Finset.Icc a b, x) + a * (a - 1) = (b + 1) * b := by
  have hsub : Finset.range a ⊆ Finset.range (b + 1) :=
    Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (by omega))
  have h1 : Finset.Icc a b = Finset.range (b + 1) \ Finset.range a := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_sdiff, Finset.mem_range, not_lt]
    omega
  have h2 := Finset.sum_sdiff (f := fun i => i) hsub
  have h3 := Finset.sum_range_id_mul_two a
  have h4 := Finset.sum_range_id_mul_two (b + 1)
  rw [h1]
  simp only [Nat.add_sub_cancel] at h4
  linarith

/-- The `k`-th generalized pentagonal number `k(3k-1)/2`, as a natural number. -/
def pentN (k : ℤ) : ℕ := (k * (3 * k - 1) / 2).toNat

lemma pentN_spec (k : ℤ) : 2 * (pentN k : ℤ) = k * (3 * k - 1) := by
  have hnn : 0 ≤ k * (3 * k - 1) := by
    rcases le_or_gt k 0 with h | h
    · nlinarith
    · nlinarith
  obtain ⟨c, hc⟩ : (2 : ℤ) ∣ k * (3 * k - 1) := by
    rcases Int.even_or_odd k with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨t * (3 * k - 1), by subst ht; ring⟩
    · exact ⟨k * (3 * t + 1), by subst ht; ring⟩
  have hc0 : 0 ≤ c := by omega
  unfold pentN
  rw [hc, Int.mul_ediv_cancel_left _ (by norm_num), Int.toNat_of_nonneg hc0]

lemma pentN_of (k : ℤ) (c : ℕ) (h : k * (3 * k - 1) = 2 * (c : ℤ)) : pentN k = c := by
  have := pentN_spec k
  omega

lemma pentN_injective : Function.Injective pentN := by
  intro a b hab
  have h1 := pentN_spec a
  have h2 := pentN_spec b
  rw [hab] at h1
  have h3 : a * (3 * a - 1) = b * (3 * b - 1) := by omega
  have h4 : (a - b) * (3 * (a + b) - 1) = 0 := by ring_nf; ring_nf at h3; linarith
  rcases mul_eq_zero.mp h4 with h | h
  · omega
  · omega

lemma pentN_le (k : ℤ) : k.natAbs ≤ pentN k := by
  have h := pentN_spec k
  have hj0 : (0 : ℤ) ≤ (k.natAbs : ℤ) := Int.natCast_nonneg _
  zify
  rw [Int.abs_eq_natAbs]
  rcases le_or_gt 0 k with hk | hk
  · have hk' : (k.natAbs : ℤ) = k := by omega
    nlinarith
  · have hk' : (k.natAbs : ℤ) = -k := by omega
    nlinarith

lemma mx_empty : mx (∅ : Finset ℕ) = 0 := by simp [mx]

lemma mn_empty : mn (∅ : Finset ℕ) = 0 := by simp [mn]

lemma sl_empty : sl (∅ : Finset ℕ) = 0 := sl_eq (by simp) (by intro i hi; omega)

lemma isExc_empty : IsExc (∅ : Finset ℕ) := by
  rw [IsExc, if_pos (by rw [mn_empty, sl_empty]), mx_empty, mn_empty]

/-- The exceptional configurations of Franklin's involution, indexed by `k : ℤ`. -/
def excSet (k : ℤ) : Finset ℕ :=
  if 0 < k then Finset.Icc k.natAbs (2 * k.natAbs - 1)
  else if k < 0 then Finset.Icc (k.natAbs + 1) (2 * k.natAbs)
  else ∅

lemma mx_Icc {a b : ℕ} (h : a ≤ b) : mx (Finset.Icc a b) = b := by
  refine le_antisymm (Finset.sup_le ?_) (le_mx (Finset.mem_Icc.mpr ⟨h, le_rfl⟩))
  intro x hx
  simp only [id_eq]
  exact (Finset.mem_Icc.mp hx).2

lemma mn_Icc {a b : ℕ} (h : a ≤ b) : mn (Finset.Icc a b) = a := by
  refine le_antisymm (mn_le (Finset.mem_Icc.mpr ⟨le_rfl, h⟩)) ?_
  have := mn_mem (s := Finset.Icc a b) ⟨a, Finset.mem_Icc.mpr ⟨le_rfl, h⟩⟩
  exact (Finset.mem_Icc.mp this).1

lemma sum_excSet (k : ℤ) : (∑ x ∈ excSet k, x) = pentN k := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have hj : 1 ≤ k.natAbs := by omega
    have hk' : (k.natAbs : ℤ) = -k := by omega
    rw [excSet, if_neg (by omega), if_pos hk]
    set j := k.natAbs with hjdef
    have hsum := two_sum_Icc (j + 1) (2 * j) (by omega)
    refine (pentN_of k _ ?_).symm
    have hc := congrArg (fun t : ℕ => (t : ℤ)) hsum
    push_cast at hc
    push_cast
    rw [show k = -(j : ℤ) by omega]
    linarith [hc]
  · subst hk
    simp [excSet, pentN]
  · have hj : 1 ≤ k.natAbs := by omega
    have hk' : (k.natAbs : ℤ) = k := by omega
    rw [excSet, if_pos hk]
    set j := k.natAbs with hjdef
    have hsum := two_sum_Icc j (2 * j - 1) (by omega)
    refine (pentN_of k _ ?_).symm
    have h2j : (2 * j - 1 : ℕ) + 1 = 2 * j := by omega
    rw [h2j] at hsum
    have hc := congrArg (fun t : ℕ => (t : ℤ)) hsum
    push_cast [Nat.cast_sub (show 1 ≤ 2 * j by omega), Nat.cast_sub (show 1 ≤ j by omega)] at hc
    push_cast
    rw [show k = (j : ℤ) by omega]
    linarith [hc]

lemma card_excSet (k : ℤ) : (excSet k).card = k.natAbs := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · rw [excSet, if_neg (by omega), if_pos hk, Nat.card_Icc]
    omega
  · subst hk; simp [excSet]
  · rw [excSet, if_pos hk, Nat.card_Icc]
    have : 1 ≤ k.natAbs := by omega
    omega

lemma zero_notMem_excSet (k : ℤ) : 0 ∉ excSet k := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · rw [excSet, if_neg (by omega), if_pos hk]
    simp
  · subst hk; simp [excSet]
  · rw [excSet, if_pos hk]
    simp only [Finset.mem_Icc, not_and, not_le]
    intro h
    omega

lemma isExc_excSet (k : ℤ) : IsExc (excSet k) := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have hj : 1 ≤ k.natAbs := by omega
    rw [excSet, if_neg (by omega), if_pos hk]
    set j := k.natAbs with hjdef
    have hmn : mn (Finset.Icc (j + 1) (2 * j)) = j + 1 := mn_Icc (by omega)
    have hmx : mx (Finset.Icc (j + 1) (2 * j)) = 2 * j := mx_Icc (by omega)
    have hsl : sl (Finset.Icc (j + 1) (2 * j)) = j := by
      refine sl_eq ?_ ?_
      · rw [hmx]; simp only [Finset.mem_Icc, not_and, not_le]; intro h; omega
      · intro i hi
        rw [hmx]
        simp only [Finset.mem_Icc]
        omega
    rw [IsExc, if_neg (by rw [hmn, hsl]; omega), hmx, hsl]
  · subst hk
    simpa only [excSet, lt_irrefl, if_false] using isExc_empty
  · have hj : 1 ≤ k.natAbs := by omega
    rw [excSet, if_pos hk]
    set j := k.natAbs with hjdef
    have hmn : mn (Finset.Icc j (2 * j - 1)) = j := mn_Icc (by omega)
    have hmx : mx (Finset.Icc j (2 * j - 1)) = 2 * j - 1 := mx_Icc (by omega)
    have hsl : sl (Finset.Icc j (2 * j - 1)) = j := by
      refine sl_eq ?_ ?_
      · rw [hmx]; simp only [Finset.mem_Icc, not_and, not_le]; intro h; omega
      · intro i hi
        rw [hmx]
        simp only [Finset.mem_Icc]
        omega
    rw [IsExc, if_pos (by rw [hmn, hsl]), hmx, hmn]

/-! ### The signed count of partitions into distinct parts -/

noncomputable instance : DecidablePred IsExc := fun s => by unfold IsExc; infer_instance

lemma eq_Icc_of {s : Finset ℕ} (h : ∀ x, mn s ≤ x → x ≤ mx s → mx s - x < sl s) :
    s = Finset.Icc (mn s) (mx s) := by
  ext x
  constructor
  · intro hx
    exact Finset.mem_Icc.mpr ⟨mn_le hx, le_mx hx⟩
  · intro hx
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hx
    have hmem := mem_of_lt_sl (h x h1 h2)
    rwa [show mx s - (mx s - x) = x by omega] at hmem

lemma exc_classification {s : Finset ℕ} (h0 : 0 ∉ s) (hexc : IsExc s) : ∃ k : ℤ, s = excSet k := by
  rcases Finset.eq_empty_or_nonempty s with rfl | hne
  · exact ⟨0, by simp [excSet]⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := basic_facts h0 hne
  by_cases hle : mn s ≤ sl s
  · rw [IsExc, if_pos hle] at hexc
    have hsl : sl s = mn s := by omega
    have hs : s = Finset.Icc (mn s) (mx s) := eq_Icc_of (fun x hx1 hx2 => by omega)
    refine ⟨(mn s : ℤ), ?_⟩
    have hcast : ((mn s : ℤ)).natAbs = mn s := by simp
    rw [excSet, if_pos (by omega), hcast, ← hexc]
    exact hs
  · rw [IsExc, if_neg hle] at hexc
    have hmn : mn s = sl s + 1 := by omega
    have hs : s = Finset.Icc (mn s) (mx s) := eq_Icc_of (fun x hx1 hx2 => by omega)
    refine ⟨-(sl s : ℤ), ?_⟩
    have hcast : ((-(sl s : ℤ))).natAbs = sl s := by simp
    rw [excSet, if_neg (by omega), if_pos (by omega), hcast, ← hexc, ← hmn]
    exact hs

/-- Partitions of `n` into distinct parts, encoded as sets of positive integers. -/
def DP (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.range (n + 1)).powerset.filter (fun s => 0 ∉ s ∧ ∑ i ∈ s, i = n)

lemma mem_DP {n : ℕ} {s : Finset ℕ} : s ∈ DP n ↔ (0 ∉ s ∧ ∑ i ∈ s, i = n) := by
  simp only [DP, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨fun h => h.2, ?_⟩
  rintro ⟨h0, hsum⟩
  refine ⟨?_, h0, hsum⟩
  intro x hx
  have hle : x ≤ ∑ i ∈ s, i :=
    Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) hx
  exact Finset.mem_range.mpr (by omega)

/-- The signed count of partitions of `n` into distinct parts. -/
def W (n : ℕ) : ℤ := ∑ s ∈ DP n, (-1) ^ s.card

lemma franklin_spec {s : Finset ℕ} (h0 : 0 ∉ s) (hexc : ¬ IsExc s) :
    0 ∉ franklin s ∧ (∑ i ∈ franklin s, i) = ∑ i ∈ s, i ∧
      ((-1 : ℤ) ^ s.card + (-1) ^ (franklin s).card = 0) ∧ franklin s ≠ s ∧
      ¬ IsExc (franklin s) ∧ franklin (franklin s) = s := by
  have hne : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with rfl | h
    · exact absurd isExc_empty hexc
    · exact h
  by_cases hle : mn s ≤ sl s
  · obtain ⟨a1, -, a3, a4, a5, a6⟩ := caseA h0 hne hle hexc
    refine ⟨a1, a3, ?_, ?_, a5, a6⟩
    · rw [← a4, pow_succ]; ring
    · intro h; rw [h] at a4; omega
  · obtain ⟨a1, -, a3, a4, a5, a6⟩ := caseB h0 hne hle hexc
    refine ⟨a1, a3, ?_, ?_, a5, a6⟩
    · rw [a4, pow_succ]; ring
    · intro h; rw [h] at a4; omega

theorem W_eq_sum_exc (n : ℕ) : W n = ∑ s ∈ (DP n).filter IsExc, (-1 : ℤ) ^ s.card := by
  have hzero : ∑ s ∈ (DP n).filter (fun s => ¬ IsExc s), (-1 : ℤ) ^ s.card = 0 := by
    refine Finset.sum_involution (fun s _ => franklin s) ?_ ?_ ?_ ?_
    · intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      exact (franklin_spec (mem_DP.mp ha1).1 ha2).2.2.1
    · intro a ha _
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      exact (franklin_spec (mem_DP.mp ha1).1 ha2).2.2.2.1
    · intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      obtain ⟨h0, hs⟩ := mem_DP.mp ha1
      obtain ⟨b1, b2, -, -, b5, -⟩ := franklin_spec h0 ha2
      exact Finset.mem_filter.mpr ⟨mem_DP.mpr ⟨b1, by rw [b2, hs]⟩, b5⟩
    · intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      exact (franklin_spec (mem_DP.mp ha1).1 ha2).2.2.2.2.2
  rw [W, ← Finset.sum_filter_add_sum_filter_not (DP n) IsExc, hzero, add_zero]

theorem sum_exc_eq (n : ℕ) :
    ∑ s ∈ (DP n).filter IsExc, (-1 : ℤ) ^ s.card
      = ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), if pentN k = n then (-1 : ℤ) ^ k.natAbs else 0 := by
  have hset : (DP n).filter IsExc
      = ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun k => pentN k = n)).image excSet := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨hs, hexc⟩
      obtain ⟨h0, hsum⟩ := mem_DP.mp hs
      obtain ⟨k, rfl⟩ := exc_classification h0 hexc
      have hpk : pentN k = n := by rw [← sum_excSet k, hsum]
      have hb := pentN_le k
      rw [hpk] at hb
      exact ⟨k, ⟨⟨by omega, by omega⟩, hpk⟩, rfl⟩
    · rintro ⟨k, ⟨-, hpk⟩, rfl⟩
      exact ⟨mem_DP.mpr ⟨zero_notMem_excSet k, by rw [sum_excSet k, hpk]⟩, isExc_excSet k⟩
  rw [hset, Finset.sum_image ?inj, Finset.sum_filter]
  case inj =>
    intro x hx y hy _
    rw [Finset.mem_coe, Finset.mem_filter] at hx hy
    exact pentN_injective (by rw [hx.2, hy.2])
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [card_excSet]

theorem W_eq (n : ℕ) :
    W n = ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), if pentN k = n then (-1 : ℤ) ^ k.natAbs else 0 := by
  rw [W_eq_sum_exc, sum_exc_eq]

end EulerPentagonal

import Mathlib
import RequestProject.Franklin

/-!
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

open PowerSeries Finset EulerPentagonal
open scoped PowerSeries.WithPiTopology

namespace Math

/-- Expanding a finite product `∏ (1 - X^(i+1))` over all subsets. -/
lemma prod_one_sub_expand (t : Finset ℕ) :
    ∏ i ∈ t, (1 - (X : ℤ⟦X⟧) ^ (i + 1))
      = ∑ u ∈ t.powerset, ((-1 : ℤ) ^ u.card) • (X : ℤ⟦X⟧) ^ (∑ i ∈ u, (i + 1)) := by
  have h : ∀ i : ℕ, (1 - (X : ℤ⟦X⟧) ^ (i + 1)) = (-(X : ℤ⟦X⟧) ^ (i + 1)) + 1 := by
    intro i; ring
  simp_rw [h]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  simp only [Finset.prod_const_one, mul_one]
  have h2 : ∀ i : ℕ, -(X : ℤ⟦X⟧) ^ (i + 1) = (-1 : ℤ⟦X⟧) * X ^ (i + 1) := by
    intro i; ring
  simp_rw [h2, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum]
  rw [zsmul_eq_mul]
  push_cast
  ring

lemma coeff_prod_one_sub (t : Finset ℕ) (d : ℕ) :
    (coeff d) (∏ i ∈ t, (1 - (X : ℤ⟦X⟧) ^ (i + 1)))
      = ∑ u ∈ t.powerset.filter (fun u => ∑ i ∈ u, (i + 1) = d), (-1 : ℤ) ^ u.card := by
  rw [prod_one_sub_expand, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [coeff_smul, coeff_X_pow]
  by_cases h : ∑ i ∈ u, (i + 1) = d
  · rw [if_pos h.symm, if_pos h]; simp
  · rw [if_neg (fun hd => h hd.symm), if_neg h]; simp

/-- For `t ⊇ range d`, the signed count of subsets of `t` with weight `d` is `W d`. -/
lemma sum_subsets_eq_W (d : ℕ) (t : Finset ℕ) (ht : Finset.range d ⊆ t) :
    ∑ u ∈ t.powerset.filter (fun u => ∑ i ∈ u, (i + 1) = d), (-1 : ℤ) ^ u.card = W d := by
  have hpos : ∀ s : Finset ℕ, s ∈ DP d → ∀ x ∈ s, 1 ≤ x := by
    intro s hs x hx
    have h0 := (mem_DP.mp hs).1
    rcases Nat.eq_zero_or_pos x with rfl | h
    · exact absurd hx h0
    · exact h
  rw [W]
  refine Finset.sum_nbij' (fun u => u.image (· + 1)) (fun s => s.image (· - 1)) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    rw [Finset.mem_filter, Finset.mem_powerset] at hu
    refine mem_DP.mpr ⟨by simp, ?_⟩
    rw [Finset.sum_image (fun x _ y _ h => by omega)]
    exact hu.2
  · intro s hs
    obtain ⟨h0, hsum⟩ := mem_DP.mp hs
    have hp := hpos s hs
    have hle : ∀ x ∈ s, x ≤ d := by
      intro x hx
      have h1 : x ≤ ∑ i ∈ s, i := by
        simpa using Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) hx
      omega
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_⟩
    · intro y hy
      simp only [Finset.mem_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact ht (Finset.mem_range.mpr (by have := hp x hx; have := hle x hx; omega))
    · rw [Finset.sum_image (fun x hx y hy h => by
        have := hp x (Finset.mem_coe.mp hx); have := hp y (Finset.mem_coe.mp hy); omega)]
      rw [← hsum]
      exact Finset.sum_congr rfl (fun x hx => by have := hp x hx; omega)
  · intro u _
    show Finset.image (fun x => x - 1) (Finset.image (fun x => x + 1) u) = u
    rw [Finset.image_image]
    simp only [Function.comp_def, Nat.add_sub_cancel, Finset.image_id']
  · intro s hs
    have hp := hpos s hs
    show Finset.image (fun x => x + 1) (Finset.image (fun x => x - 1) s) = s
    rw [Finset.image_image]
    ext y
    simp only [Finset.mem_image, Function.comp_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := hp x hx
      rwa [show x - 1 + 1 = x by omega]
    · intro hy
      exact ⟨y, hy, by have := hp y hy; omega⟩
  · intro u _
    rw [Finset.card_image_of_injective _ (fun x y h => by omega)]

/-- The infinite product `∏_{i≥1} (1 - X^i)` is the generating function of the signed count of
partitions into distinct parts. -/
theorem hasProd_one_sub :
    HasProd (fun i : ℕ ↦ (1 - (X : ℤ⟦X⟧) ^ (i + 1))) (PowerSeries.mk W) := by
  rw [HasProd, WithPiTopology.tendsto_iff_coeff_tendsto]
  intro d
  refine tendsto_atTop_of_eventually_const (i₀ := Finset.range d) (fun s hs => ?_)
  rw [coeff_prod_one_sub, sum_subsets_eq_W d s hs, coeff_mk]

/-- Euler's pentagonal series sums to the same power series. -/
theorem hasSum_pentagonal :
    HasSum (fun k : ℤ ↦ ((-1 : ℤ) ^ k.natAbs) • (X : ℤ⟦X⟧) ^ pentN k) (PowerSeries.mk W) := by
  rw [WithPiTopology.hasSum_iff_hasSum_coeff]
  intro d
  have hco : ∀ k : ℤ, (coeff d) (((-1 : ℤ) ^ k.natAbs) • (X : ℤ⟦X⟧) ^ pentN k)
      = if pentN k = d then ((-1 : ℤ) ^ k.natAbs) else 0 := by
    intro k
    rw [coeff_smul, coeff_X_pow]
    by_cases h : pentN k = d
    · rw [if_pos h.symm, if_pos h]; simp
    · rw [if_neg (fun hd => h hd.symm), if_neg h]; simp
  simp_rw [hco]
  rw [coeff_mk, W_eq d]
  refine hasSum_sum_of_ne_finset_zero ?_
  intro k hk
  simp only [Finset.mem_Icc, not_and, not_le] at hk
  by_cases h : pentN k = d
  · exfalso
    have hb := pentN_le k
    rw [h] at hb
    omega
  · rw [if_neg h]

/-- **Euler's pentagonal number theorem**:
`∏_{i ≥ 1} (1 - X^i) = ∑_{k ∈ ℤ} (-1)^k X^(k(3k-1)/2)` as formal power series over `ℤ`,
where the infinite product is the reciprocal of the generating function of the partition
function. -/
theorem euler_pentagonal :
    HasSum (fun k : ℤ ↦ ((-1 : ℤ) ^ k.natAbs) • (X : ℤ⟦X⟧) ^ pentN k)
      (∏' i : ℕ, (1 - (X : ℤ⟦X⟧) ^ (i + 1))) := by
  rw [hasProd_one_sub.tprod_eq]
  exact hasSum_pentagonal

/-- Coefficient form of Euler's pentagonal number theorem: the coefficient of `X^n` in
`∏_{i ≥ 1} (1 - X^i)` is `(-1)^k` if `n = k(3k-1)/2` for some `k ∈ ℤ`, and `0` otherwise. -/
theorem coeff_tprod_one_sub (n : ℕ) :
    (coeff n) (∏' i : ℕ, (1 - (X : ℤ⟦X⟧) ^ (i + 1)))
      = ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), if pentN k = n then (-1 : ℤ) ^ k.natAbs else 0 := by
  rw [hasProd_one_sub.tprod_eq, coeff_mk, W_eq]

/-! ### Relation with the generating function of the partition function -/

/-- Coefficients of the geometric series `∑_{j ≥ 1} X^(m j)`. -/
lemma coeff_tsum_geom {m : ℕ} (hm : m ≠ 0) (d : ℕ) :
    (coeff d) (∑' j : ℕ, (1 : ℤ) • (X : ℤ⟦X⟧) ^ (m * (j + 1)))
      = if (m ∣ d ∧ d ≠ 0) then 1 else 0 := by
  have hs := Nat.Partition.summable_genFun_term' (R := ℤ) (fun _ _ => (1 : ℤ)) hm
  rw [hs.map_tsum _ (WithPiTopology.continuous_coeff ℤ d)]
  have hterm : ∀ j : ℕ, (coeff d) ((1 : ℤ) • (X : ℤ⟦X⟧) ^ (m * (j + 1)))
      = if d = m * (j + 1) then (1 : ℤ) else 0 := by
    intro j
    rw [coeff_smul, coeff_X_pow]
    simp
  simp_rw [hterm]
  by_cases h : m ∣ d ∧ d ≠ 0
  · obtain ⟨c, hc⟩ := h.1
    have hc0 : c ≠ 0 := by rintro rfl; exact h.2 (by omega)
    rw [if_pos h, tsum_eq_single (c - 1) ?_]
    · rw [if_pos (by rw [show c - 1 + 1 = c from by omega]; exact hc)]
    · intro b hb
      rw [if_neg (by
        intro hcon
        apply hb
        have h2 : m * c = m * (b + 1) := by omega
        have := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm) h2
        omega)]
  · rw [if_neg h]
    have hz : ∀ j : ℕ, (if d = m * (j + 1) then (1 : ℤ) else 0) = 0 := by
      intro j
      rw [if_neg]
      rintro rfl
      exact h ⟨⟨j + 1, rfl⟩, Nat.mul_ne_zero hm (by omega)⟩
    simp_rw [hz]
    exact tsum_zero

/-- The `m`-th factor of the partition generating function is inverse to `1 - X^m`. -/
lemma geom_mul_one_sub {m : ℕ} (hm : m ≠ 0) :
    (1 + ∑' j : ℕ, (1 : ℤ) • (X : ℤ⟦X⟧) ^ (m * (j + 1))) * (1 - X ^ m) = 1 := by
  have hc : ∀ d : ℕ, (coeff d) (1 + ∑' j : ℕ, (1 : ℤ) • (X : ℤ⟦X⟧) ^ (m * (j + 1)))
      = if m ∣ d then 1 else 0 := by
    intro d
    rw [map_add, coeff_tsum_geom hm, coeff_one]
    by_cases hd : d = 0
    · subst hd
      simp
    · simp [hd]
  ext d
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', coeff_one]
  simp only [hc]
  by_cases hd : d = 0
  · subst hd
    rw [if_pos (dvd_zero m), if_neg (by omega), if_pos rfl]
    ring
  · rw [if_neg hd]
    by_cases hdvd : m ∣ d
    · have hmd : m ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd) hdvd
      rw [if_pos hdvd, if_pos hmd, if_pos (Nat.dvd_sub hdvd dvd_rfl)]
      ring
    · rw [if_neg hdvd]
      by_cases hle : m ≤ d
      · rw [if_pos hle, if_neg (fun hcon => hdvd (by
          have := Nat.dvd_add hcon (dvd_refl m)
          rwa [Nat.sub_add_cancel hle] at this))]
        ring
      · rw [if_neg hle]
        ring

/-- The generating function of the partition function. -/
lemma genFun_one_eq :
    Nat.Partition.genFun (fun _ _ => (1 : ℤ))
      = PowerSeries.mk (fun n => (Fintype.card (Nat.Partition n) : ℤ)) := by
  ext n
  rw [Nat.Partition.coeff_genFun, coeff_mk]
  simp [Finsupp.prod]

/-- **Euler's pentagonal number theorem for the partition generating function**: the pentagonal
series `∑_{k ∈ ℤ} (-1)^k X^(k(3k-1)/2)` is the multiplicative inverse of the generating function
`∑_n p(n) X^n` of the partition function. -/
theorem partition_genFun_mul_pentagonal :
    (PowerSeries.mk (fun n => (Fintype.card (Nat.Partition n) : ℤ)))
        * (∑' k : ℤ, ((-1 : ℤ) ^ k.natAbs) • (X : ℤ⟦X⟧) ^ pentN k) = 1 := by
  have hG : HasProd (fun i : ℕ ↦ (1 : ℤ⟦X⟧) + ∑' j : ℕ, (1 : ℤ) • X ^ ((i + 1) * (j + 1)))
      (Nat.Partition.genFun (fun _ _ => (1 : ℤ))) := Nat.Partition.hasProd_genFun _
  have hmul := hG.mul hasProd_one_sub
  have hone : ∀ i : ℕ,
      ((1 : ℤ⟦X⟧) + ∑' j : ℕ, (1 : ℤ) • X ^ ((i + 1) * (j + 1))) * (1 - X ^ (i + 1)) = 1 :=
    fun i => geom_mul_one_sub (Nat.succ_ne_zero i)
  simp_rw [hone] at hmul
  have h1 : Nat.Partition.genFun (fun _ _ => (1 : ℤ)) * PowerSeries.mk W = 1 :=
    hmul.unique hasProd_one
  rw [hasSum_pentagonal.tsum_eq, ← genFun_one_eq]
  exact h1

end Math

