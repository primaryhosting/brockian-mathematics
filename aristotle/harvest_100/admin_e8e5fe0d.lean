import Mathlib

/-!
# Franklin's involution and the pentagonal number theorem (combinatorial core)

A partition of `n` into distinct positive parts is encoded as a `Finset ℕ` not containing `0`
whose sum is `n`.  The main result of this file, `Franklin.sum_sign_DP`, is Franklin's theorem:
the signed count `∑ (-1)^(number of parts)` over all partitions of `n` into distinct parts is
`(-1)^k` if `n` is a generalized pentagonal number `k(3k∓1)/2`, and `0` otherwise.
-/

namespace Franklin

open Finset

/-- Partitions of `n` into distinct positive parts, encoded as finsets of positive naturals. -/
def DP (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.range (n + 1)).powerset.filter (fun s => 0 ∉ s ∧ ∑ i ∈ s, i = n)

/-- The smallest part (junk value `0` for the empty finset). -/
noncomputable def mn (s : Finset ℕ) : ℕ := if h : s.Nonempty then s.min' h else 0

/-- The largest part (junk value `0` for the empty finset). -/
def mx (s : Finset ℕ) : ℕ := s.sup id

/-- The length of the "staircase" run of consecutive parts at the top of `s`. -/
noncomputable def run (s : Finset ℕ) : ℕ := sInf {r | 1 ≤ r ∧ mx s - r ∉ s}

/-- Franklin's first move: delete the smallest part `a` and add `1` to each of the `a`
largest parts. -/
noncomputable def op1 (s : Finset ℕ) : Finset ℕ :=
  ((s.erase (mn s)).filter (fun x => x ≤ mx s - mn s)) ∪ Finset.Icc (mx s - mn s + 2) (mx s + 1)

/-- Franklin's second move: subtract `1` from each of the `σ` largest parts (where `σ` is the
run length) and adjoin a new part equal to `σ`. -/
noncomputable def op2 (s : Finset ℕ) : Finset ℕ :=
  insert (run s)
    ((s.filter (fun x => x ≤ mx s - run s)) ∪ Finset.Icc (mx s - run s) (mx s - 1))

section Basic

variable {s : Finset ℕ} {n : ℕ}

@[simp] lemma mem_DP : s ∈ DP n ↔ 0 ∉ s ∧ ∑ i ∈ s, i = n := by
  classical
  simp only [DP, Finset.mem_filter, Finset.mem_powerset, Finset.mem_range]
  constructor
  · rintro ⟨-, h⟩; exact h
  · rintro ⟨h0, hsum⟩
    refine ⟨fun x hx => ?_, h0, hsum⟩
    have : x ≤ ∑ i ∈ s, i := Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) hx
    simp only [Finset.mem_range]
    omega

lemma mn_mem (hs : s.Nonempty) : mn s ∈ s := by
  simp only [mn, dif_pos hs]
  exact s.min'_mem hs

lemma mn_le (hs : s.Nonempty) {x : ℕ} (hx : x ∈ s) : mn s ≤ x := by
  simp only [mn, dif_pos hs]
  exact s.min'_le x hx

lemma le_mx {x : ℕ} (hx : x ∈ s) : x ≤ mx s := Finset.le_sup (f := id) hx

lemma mx_mem (hs : s.Nonempty) : mx s ∈ s := by
  obtain ⟨x, hx⟩ := hs
  have := Finset.max'_mem s ⟨x, hx⟩
  have h1 : mx s = s.max' ⟨x, hx⟩ := by
    refine le_antisymm ?_ (le_mx (Finset.max'_mem s ⟨x, hx⟩))
    exact Finset.sup_le (fun y hy => Finset.le_max' s y hy)
  rw [h1]; exact Finset.max'_mem s ⟨x, hx⟩

lemma run_exists (h0 : 0 ∉ s) : ∃ r, r ∈ {r | 1 ≤ r ∧ mx s - r ∉ s} := by
  refine ⟨max 1 (mx s), le_max_left _ _, ?_⟩
  have h : mx s - max 1 (mx s) = 0 := by omega
  rw [h]; exact h0

lemma run_spec (h0 : 0 ∉ s) : 1 ≤ run s ∧ mx s - run s ∉ s :=
  Nat.sInf_mem (run_exists h0)

lemma run_pos (h0 : 0 ∉ s) : 1 ≤ run s := (run_spec h0).1

lemma run_notMem (h0 : 0 ∉ s) : mx s - run s ∉ s := (run_spec h0).2

lemma run_minimal {r : ℕ} (hr : r < run s) (h1 : 1 ≤ r) : mx s - r ∈ s := by
  by_contra hc
  exact absurd (Nat.sInf_le (s := {r | 1 ≤ r ∧ mx s - r ∉ s}) ⟨h1, hc⟩) (by simpa [run] using hr)

lemma Icc_run_subset (hs : s.Nonempty) : Finset.Icc (mx s - run s + 1) (mx s) ⊆ s := by
  intro x hx
  simp only [Finset.mem_Icc] at hx
  rcases eq_or_lt_of_le hx.2 with rfl | hlt
  · exact mx_mem hs
  · have hr : mx s - x < run s := by omega
    have h1 : 1 ≤ mx s - x := by omega
    have := run_minimal hr h1
    have hxx : mx s - (mx s - x) = x := by omega
    rwa [hxx] at this

lemma mn_pos (hs : s.Nonempty) (h0 : 0 ∉ s) : 1 ≤ mn s := by
  rcases Nat.eq_zero_or_pos (mn s) with h | h
  · exact absurd (h ▸ mn_mem hs) h0
  · exact h

lemma mn_le_mx (hs : s.Nonempty) : mn s ≤ mx s := le_mx (mn_mem hs)

lemma run_le_mx (hs : s.Nonempty) (h0 : 0 ∉ s) : run s ≤ mx s := by
  have h1 : 1 ≤ mx s := le_trans (mn_pos hs h0) (mn_le_mx hs)
  have : mx s ∈ {r | 1 ≤ r ∧ mx s - r ∉ s} := ⟨h1, by simpa using h0⟩
  exact Nat.sInf_le this

lemma card_Icc_run (hs : s.Nonempty) (h0 : 0 ∉ s) :
    (Finset.Icc (mx s - run s + 1) (mx s)).card = run s := by
  have := run_le_mx hs h0
  rw [Nat.card_Icc]
  omega

lemma run_le_card (hs : s.Nonempty) (h0 : 0 ∉ s) : run s ≤ s.card := by
  have := Finset.card_le_card (Icc_run_subset hs)
  rwa [card_Icc_run hs h0] at this

lemma card_le_range (hs : s.Nonempty) : s.card ≤ mx s - mn s + 1 := by
  have hsub : s ⊆ Finset.Icc (mn s) (mx s) := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨mn_le hs hx, le_mx hx⟩
  have h := Finset.card_le_card hsub
  rw [Nat.card_Icc] at h
  have := mn_le_mx hs
  omega

end Basic

section Moves

variable {s : Finset ℕ} {n : ℕ}

/-- `s` admits Franklin's first move: the smallest part is at most the length of the top run,
and `s` is not the exceptional staircase `{k, …, 2k-1}`. -/
def IsA (s : Finset ℕ) : Prop :=
  s.Nonempty ∧ mn s ≤ run s ∧ ¬(s.card = run s ∧ run s = mn s)

/-- `s` admits Franklin's second move: the smallest part exceeds the length of the top run,
and `s` is not the exceptional staircase `{k+1, …, 2k}`. -/
def IsB (s : Finset ℕ) : Prop :=
  s.Nonempty ∧ run s < mn s ∧ ¬(s.card = run s ∧ mn s = run s + 1)

noncomputable instance : DecidablePred IsA := fun s => by unfold IsA; infer_instance

noncomputable instance : DecidablePred IsB := fun s => by unfold IsB; infer_instance

lemma IsA.two_mn_le_mx (h0 : 0 ∉ s) (hA : IsA s) : 2 * mn s ≤ mx s := by
  obtain ⟨hs, hle, hne⟩ := hA
  have h1 := run_le_card hs h0
  have h2 := card_le_range hs
  have h3 := mn_le_mx hs
  have h4 := mn_pos hs h0
  by_contra hc
  exact hne ⟨by omega, by omega⟩

lemma IsB.two_run_lt_mx (h0 : 0 ∉ s) (hB : IsB s) : 2 * run s < mx s := by
  obtain ⟨hs, hlt, hne⟩ := hB
  have h1 := run_le_card hs h0
  have h2 := card_le_range hs
  have h3 := mn_le_mx hs
  have h4 := mn_pos hs h0
  have h5 := run_pos h0
  by_contra hc
  exact hne ⟨by omega, by omega⟩

lemma sum_Icc_succ_succ (u v : ℕ) :
    ∑ i ∈ Finset.Icc (u + 1) (v + 1), i
      = (∑ i ∈ Finset.Icc u v, i) + (Finset.Icc u v).card := by
  rw [← Finset.image_add_right_Icc u v 1,
    Finset.sum_image (by intro x _ y _ h; simpa using h)]
  simp [Finset.sum_add_distrib]

private lemma decompA (hA : IsA s) :
    s = insert (mn s) ((s.erase (mn s)).filter (fun x => x ≤ mx s - mn s)
      ∪ Finset.Icc (mx s - mn s + 1) (mx s)) := by
  obtain ⟨hs, hle, -⟩ := hA
  ext x
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_erase,
    Finset.mem_Icc]
  constructor
  · intro hx
    by_cases hxa : x = mn s
    · exact Or.inl hxa
    · refine Or.inr ?_
      by_cases hcase : x ≤ mx s - mn s
      · exact Or.inl ⟨⟨hxa, hx⟩, hcase⟩
      · exact Or.inr ⟨by omega, le_mx hx⟩
  · rintro (rfl | ⟨⟨-, hx⟩, -⟩ | ⟨h1, h2⟩)
    · exact mn_mem hs
    · exact hx
    · exact Icc_run_subset hs (Finset.mem_Icc.mpr ⟨by omega, h2⟩)

section ASide

variable {s : Finset ℕ}

private lemma op1_eq (s : Finset ℕ) :
    op1 s = (s.erase (mn s)).filter (fun x => x ≤ mx s - mn s)
      ∪ Finset.Icc (mx s - mn s + 2) (mx s + 1) := rfl

private lemma disjA1 :
    Disjoint ((s.erase (mn s)).filter (fun x => x ≤ mx s - mn s))
      (Finset.Icc (mx s - mn s + 1) (mx s)) := by
  rw [Finset.disjoint_left]
  intro x hx hx2
  simp only [Finset.mem_filter, Finset.mem_erase] at hx
  simp only [Finset.mem_Icc] at hx2
  omega

private lemma disjA2 :
    Disjoint ((s.erase (mn s)).filter (fun x => x ≤ mx s - mn s))
      (Finset.Icc (mx s - mn s + 2) (mx s + 1)) := by
  rw [Finset.disjoint_left]
  intro x hx hx2
  simp only [Finset.mem_filter, Finset.mem_erase] at hx
  simp only [Finset.mem_Icc] at hx2
  omega

private lemma mn_notMemA (h0 : 0 ∉ s) (hA : IsA s) :
    mn s ∉ ((s.erase (mn s)).filter (fun x => x ≤ mx s - mn s)
      ∪ Finset.Icc (mx s - mn s + 1) (mx s)) := by
  have hM := IsA.two_mn_le_mx h0 hA
  have h1 := mn_pos hA.1 h0
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc, not_or]
  constructor
  · rintro ⟨⟨h, -⟩, -⟩; exact h rfl
  · rintro ⟨h, -⟩; omega

private lemma card_IccA (h0 : 0 ∉ s) (hA : IsA s) :
    (Finset.Icc (mx s - mn s + 1) (mx s)).card = mn s := by
  have hM := IsA.two_mn_le_mx h0 hA
  rw [Nat.card_Icc]; omega

private lemma card_IccA' (h0 : 0 ∉ s) (hA : IsA s) :
    (Finset.Icc (mx s - mn s + 2) (mx s + 1)).card = mn s := by
  have hM := IsA.two_mn_le_mx h0 hA
  rw [Nat.card_Icc]; omega

lemma op1_sum (h0 : 0 ∉ s) (hA : IsA s) : ∑ i ∈ op1 s, i = ∑ i ∈ s, i := by
  have hM := IsA.two_mn_le_mx h0 hA
  have hshift : ∑ i ∈ Finset.Icc (mx s - mn s + 2) (mx s + 1), i
      = (∑ i ∈ Finset.Icc (mx s - mn s + 1) (mx s), i) + mn s := by
    have h2 : mx s - mn s + 2 = (mx s - mn s + 1) + 1 := by omega
    rw [h2, sum_Icc_succ_succ, card_IccA h0 hA]
  conv_rhs => rw [decompA hA]
  rw [Finset.sum_insert (mn_notMemA h0 hA), Finset.sum_union disjA1, op1_eq,
    Finset.sum_union disjA2, hshift]
  omega

lemma op1_card (h0 : 0 ∉ s) (hA : IsA s) : (op1 s).card + 1 = s.card := by
  conv_rhs => rw [decompA hA]
  rw [Finset.card_insert_of_notMem (mn_notMemA h0 hA), Finset.card_union_of_disjoint disjA1,
    op1_eq, Finset.card_union_of_disjoint disjA2, card_IccA h0 hA, card_IccA' h0 hA]

lemma op1_zero_notMem (h0 : 0 ∉ s) (hA : IsA s) : 0 ∉ op1 s := by
  have hM := IsA.two_mn_le_mx h0 hA
  rw [op1_eq]
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc, not_or]
  exact ⟨fun h => h0 h.1.2, by rintro ⟨h, -⟩; omega⟩

lemma op1_mem (h0 : 0 ∉ s) (hA : IsA s) : mx s + 1 ∈ op1 s := by
  have hM := IsA.two_mn_le_mx h0 hA
  have hpos := mn_pos hA.1 h0
  rw [op1_eq]
  refine Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨by omega, le_refl _⟩)

lemma op1_nonempty (h0 : 0 ∉ s) (hA : IsA s) : (op1 s).Nonempty :=
  ⟨_, op1_mem h0 hA⟩

lemma op1_mx (h0 : 0 ∉ s) (hA : IsA s) : mx (op1 s) = mx s + 1 := by
  have hM := IsA.two_mn_le_mx h0 hA
  refine le_antisymm ?_ (le_mx (op1_mem h0 hA))
  rw [op1_eq]
  apply Finset.sup_le
  intro x hx
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc] at hx
  simp only [id]
  omega

lemma op1_gt (h0 : 0 ∉ s) (hA : IsA s) {x : ℕ} (hx : x ∈ op1 s) : mn s < x := by
  have hM := IsA.two_mn_le_mx h0 hA
  rw [op1_eq] at hx
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc] at hx
  rcases hx with ⟨⟨hne, hmem⟩, -⟩ | ⟨h1, -⟩
  · exact lt_of_le_of_ne (mn_le hA.1 hmem) (Ne.symm hne)
  · omega

lemma op1_run (h0 : 0 ∉ s) (hA : IsA s) : run (op1 s) = mn s := by
  have hM := IsA.two_mn_le_mx h0 hA
  have hmx := op1_mx h0 hA
  have hpos := mn_pos hA.1 h0
  have hnot : mx (op1 s) - mn s ∉ op1 s := by
    rw [hmx, op1_eq]
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc, not_or]
    exact ⟨by rintro ⟨-, h⟩; omega, by rintro ⟨h, -⟩; omega⟩
  have hle : run (op1 s) ≤ mn s := Nat.sInf_le ⟨hpos, hnot⟩
  refine le_antisymm hle ?_
  by_contra hc
  push_neg at hc
  have h1 : 1 ≤ run (op1 s) := run_pos (op1_zero_notMem h0 hA)
  have hIcc : ∀ r : ℕ, 1 ≤ r → r < mn s → mx (op1 s) - r ∈ op1 s := by
    intro r hr1 hr2
    have hrw : mx (op1 s) - r = mx s + 1 - r := by rw [hmx]
    rw [hrw, op1_eq]
    exact Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  exact (run_notMem (op1_zero_notMem h0 hA)) (hIcc _ h1 hc)

lemma op1_isB (h0 : 0 ∉ s) (hA : IsA s) : IsB (op1 s) := by
  have hM := IsA.two_mn_le_mx h0 hA
  have hrun := op1_run h0 hA
  have hmx := op1_mx h0 hA
  refine ⟨op1_nonempty h0 hA, ?_, ?_⟩
  · rw [hrun]
    exact op1_gt h0 hA (mn_mem (op1_nonempty h0 hA))
  · rintro ⟨hcard, hmn⟩
    rw [hrun] at hcard hmn
    -- `op1 s` has `mn s` elements, and contains the interval `Icc (mx s - mn s + 2) (mx s + 1)`
    have hsub : Finset.Icc (mx s - mn s + 2) (mx s + 1) ⊆ op1 s := by
      rw [op1_eq]; exact Finset.subset_union_right
    have hcard' : (Finset.Icc (mx s - mn s + 2) (mx s + 1)).card = mn s := card_IccA' h0 hA
    have heq : Finset.Icc (mx s - mn s + 2) (mx s + 1) = op1 s :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    have hmem : mn (op1 s) ∈ Finset.Icc (mx s - mn s + 2) (mx s + 1) := by
      rw [heq]; exact mn_mem (op1_nonempty h0 hA)
    simp only [Finset.mem_Icc] at hmem
    omega

lemma op2_op1 (h0 : 0 ∉ s) (hA : IsA s) : op2 (op1 s) = s := by
  have hM := IsA.two_mn_le_mx h0 hA
  have hpos := mn_pos hA.1 h0
  have hmx := op1_mx h0 hA
  have hrun := op1_run h0 hA
  have hfilter : (op1 s).filter (fun x => x ≤ mx (op1 s) - run (op1 s))
      = (s.erase (mn s)).filter (fun x => x ≤ mx s - mn s) := by
    rw [hmx, hrun, op1_eq]
    ext x
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_Icc, Finset.mem_erase]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact h1
      · omega
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inl ⟨h1, h2⟩, by omega⟩
  have hIccEq : Finset.Icc (mx (op1 s) - run (op1 s)) (mx (op1 s) - 1)
      = Finset.Icc (mx s - mn s + 1) (mx s) := by
    rw [hmx, hrun]
    congr 1 <;> omega
  conv_rhs => rw [decompA hA]
  rw [op2, hfilter, hIccEq, hrun]

end ASide

section BSide

variable {t : Finset ℕ}

private lemma op2_eq (t : Finset ℕ) :
    op2 t = insert (run t)
      ((t.filter (fun x => x ≤ mx t - run t)) ∪ Finset.Icc (mx t - run t) (mx t - 1)) := rfl

private lemma decompB (ht : t.Nonempty) :
    t = (t.filter (fun x => x ≤ mx t - run t)) ∪ Finset.Icc (mx t - run t + 1) (mx t) := by
  ext x
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · intro hx
    by_cases hc : x ≤ mx t - run t
    · exact Or.inl ⟨hx, hc⟩
    · exact Or.inr ⟨by omega, le_mx hx⟩
  · rintro (⟨hx, -⟩ | ⟨h1, h2⟩)
    · exact hx
    · exact Icc_run_subset ht (Finset.mem_Icc.mpr ⟨h1, h2⟩)

private lemma memL'_lt (h0 : 0 ∉ t) {x : ℕ}
    (hx : x ∈ t.filter (fun x => x ≤ mx t - run t)) : x < mx t - run t := by
  simp only [Finset.mem_filter] at hx
  rcases lt_or_eq_of_le hx.2 with h | h
  · exact h
  · exact absurd (h ▸ hx.1) (run_notMem h0)

private lemma disjB1 (h0 : 0 ∉ t) :
    Disjoint (t.filter (fun x => x ≤ mx t - run t)) (Finset.Icc (mx t - run t + 1) (mx t)) := by
  rw [Finset.disjoint_left]
  intro x hx hx2
  have := memL'_lt h0 hx
  simp only [Finset.mem_Icc] at hx2
  omega

private lemma disjB2 (h0 : 0 ∉ t) :
    Disjoint (t.filter (fun x => x ≤ mx t - run t)) (Finset.Icc (mx t - run t) (mx t - 1)) := by
  rw [Finset.disjoint_left]
  intro x hx hx2
  have := memL'_lt h0 hx
  simp only [Finset.mem_Icc] at hx2
  omega

private lemma run_notMemB (h0 : 0 ∉ t) (hB : IsB t) :
    run t ∉ (t.filter (fun x => x ≤ mx t - run t)) ∪ Finset.Icc (mx t - run t) (mx t - 1) := by
  have h2 := IsB.two_run_lt_mx h0 hB
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, not_or]
  refine ⟨?_, ?_⟩
  · rintro ⟨hmem, -⟩
    exact absurd (mn_le hB.1 hmem) (by have := hB.2.1; omega)
  · rintro ⟨h, -⟩; omega

private lemma card_IccB (h0 : 0 ∉ t) (hB : IsB t) :
    (Finset.Icc (mx t - run t) (mx t - 1)).card = run t := by
  have h2 := IsB.two_run_lt_mx h0 hB
  rw [Nat.card_Icc]; omega

lemma op2_sum (h0 : 0 ∉ t) (hB : IsB t) : ∑ i ∈ op2 t, i = ∑ i ∈ t, i := by
  have h2 := IsB.two_run_lt_mx h0 hB
  have hshift : ∑ i ∈ Finset.Icc (mx t - run t + 1) (mx t), i
      = (∑ i ∈ Finset.Icc (mx t - run t) (mx t - 1), i) + run t := by
    have h3 : mx t = (mx t - 1) + 1 := by omega
    rw [show Finset.Icc (mx t - run t + 1) (mx t)
        = Finset.Icc ((mx t - run t) + 1) ((mx t - 1) + 1) by rw [← h3],
      sum_Icc_succ_succ, card_IccB h0 hB]
  conv_rhs => rw [decompB hB.1]
  rw [op2_eq, Finset.sum_insert (run_notMemB h0 hB), Finset.sum_union (disjB2 h0),
    Finset.sum_union (disjB1 h0), hshift]
  omega

lemma op2_card (h0 : 0 ∉ t) (hB : IsB t) : (op2 t).card = t.card + 1 := by
  conv_rhs => rw [decompB hB.1]
  rw [op2_eq, Finset.card_insert_of_notMem (run_notMemB h0 hB),
    Finset.card_union_of_disjoint (disjB2 h0), Finset.card_union_of_disjoint (disjB1 h0),
    card_IccB h0 hB, card_Icc_run hB.1 h0]

lemma op2_zero_notMem (h0 : 0 ∉ t) (hB : IsB t) : 0 ∉ op2 t := by
  have h2 := IsB.two_run_lt_mx h0 hB
  have h1 := run_pos h0
  rw [op2_eq]
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, not_or]
  exact ⟨by omega, fun h => h0 h.1, by rintro ⟨h, -⟩; omega⟩

lemma op2_mem (h0 : 0 ∉ t) (hB : IsB t) : run t ∈ op2 t := by
  rw [op2_eq]; exact Finset.mem_insert_self _ _

lemma op2_nonempty (h0 : 0 ∉ t) (hB : IsB t) : (op2 t).Nonempty := ⟨_, op2_mem h0 hB⟩

lemma op2_ge (h0 : 0 ∉ t) (hB : IsB t) {x : ℕ} (hx : x ∈ op2 t) : run t ≤ x := by
  have h2 := IsB.two_run_lt_mx h0 hB
  rw [op2_eq] at hx
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc] at hx
  rcases hx with rfl | ⟨hmem, -⟩ | ⟨h1, -⟩
  · exact le_refl _
  · exact le_of_lt (lt_of_lt_of_le hB.2.1 (mn_le hB.1 hmem))
  · omega

lemma op2_mn (h0 : 0 ∉ t) (hB : IsB t) : mn (op2 t) = run t :=
  le_antisymm (mn_le (op2_nonempty h0 hB) (op2_mem h0 hB))
    (op2_ge h0 hB (mn_mem (op2_nonempty h0 hB)))

lemma op2_mx (h0 : 0 ∉ t) (hB : IsB t) : mx (op2 t) = mx t - 1 := by
  have h2 := IsB.two_run_lt_mx h0 hB
  have h1 := run_pos h0
  have hmem : mx t - 1 ∈ op2 t := by
    rw [op2_eq]
    exact Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨by omega, le_refl _⟩))
  refine le_antisymm ?_ (le_mx hmem)
  rw [op2_eq]
  apply Finset.sup_le
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc] at hx
  simp only [id]
  rcases hx with rfl | ⟨hmem', hle⟩ | ⟨-, h⟩
  · omega
  · have := memL'_lt h0 (Finset.mem_filter.mpr ⟨hmem', hle⟩)
    omega
  · exact h

lemma op2_run_ge (h0 : 0 ∉ t) (hB : IsB t) : run t ≤ run (op2 t) := by
  have h2 := IsB.two_run_lt_mx h0 hB
  have h1 := run_pos h0
  by_contra hc
  push_neg at hc
  have h3 : 1 ≤ run (op2 t) := run_pos (op2_zero_notMem h0 hB)
  have hmem : ∀ r : ℕ, 1 ≤ r → r < run t → mx (op2 t) - r ∈ op2 t := by
    intro r hr1 hr2
    have hrw : mx (op2 t) - r = mx t - 1 - r := by rw [op2_mx h0 hB]
    rw [hrw, op2_eq]
    exact Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
  exact (run_notMem (op2_zero_notMem h0 hB)) (hmem _ h3 hc)

lemma op2_isA (h0 : 0 ∉ t) (hB : IsB t) : IsA (op2 t) := by
  refine ⟨op2_nonempty h0 hB, ?_, ?_⟩
  · rw [op2_mn h0 hB]; exact op2_run_ge h0 hB
  · rintro ⟨hcard, hrun⟩
    rw [op2_mn h0 hB] at hrun
    rw [op2_card h0 hB, hrun] at hcard
    have := run_le_card hB.1 h0
    omega

lemma op1_op2 (h0 : 0 ∉ t) (hB : IsB t) : op1 (op2 t) = t := by
  have h2 := IsB.two_run_lt_mx h0 hB
  have h1 := run_pos h0
  have hmn := op2_mn h0 hB
  have hmx := op2_mx h0 hB
  have herase : (op2 t).erase (mn (op2 t))
      = (t.filter (fun x => x ≤ mx t - run t)) ∪ Finset.Icc (mx t - run t) (mx t - 1) := by
    rw [hmn, op2_eq, Finset.erase_insert (run_notMemB h0 hB)]
  have hfilter : ((op2 t).erase (mn (op2 t))).filter (fun x => x ≤ mx (op2 t) - mn (op2 t))
      = t.filter (fun x => x ≤ mx t - run t) := by
    rw [herase, hmn, hmx]
    ext x
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_Icc]
    constructor
    · rintro ⟨h3 | h3, h4⟩
      · exact h3
      · omega
    · intro h3
      have := memL'_lt h0 (Finset.mem_filter.mpr h3)
      exact ⟨Or.inl h3, by omega⟩
  have hIccEq : Finset.Icc (mx (op2 t) - mn (op2 t) + 2) (mx (op2 t) + 1)
      = Finset.Icc (mx t - run t + 1) (mx t) := by
    rw [hmn, hmx]
    congr 1
    · omega
    · omega
  conv_rhs => rw [decompB hB.1]
  rw [op1_eq, hfilter, hIccEq]

end BSide

section Cancellation

/-- Franklin's involution cancels the sets admitting the first move against those admitting
the second move. -/
lemma sum_A_add_sum_B (n : ℕ) :
    (∑ s ∈ (DP n).filter IsA, (-1 : ℤ) ^ s.card)
      + ∑ s ∈ (DP n).filter IsB, (-1 : ℤ) ^ s.card = 0 := by
  have key : (∑ s ∈ (DP n).filter IsA, (-1 : ℤ) ^ s.card)
      = ∑ t ∈ (DP n).filter IsB, (-((-1 : ℤ) ^ t.card)) := by
    refine Finset.sum_nbij' op1 op2 ?_ ?_ ?_ ?_ ?_
    · intro s hs
      rw [Finset.mem_filter, mem_DP] at hs
      obtain ⟨⟨h0, hsum⟩, hA⟩ := hs
      rw [Finset.mem_filter, mem_DP]
      exact ⟨⟨op1_zero_notMem h0 hA, by rw [op1_sum h0 hA, hsum]⟩, op1_isB h0 hA⟩
    · intro t ht
      rw [Finset.mem_filter, mem_DP] at ht
      obtain ⟨⟨h0, hsum⟩, hB⟩ := ht
      rw [Finset.mem_filter, mem_DP]
      exact ⟨⟨op2_zero_notMem h0 hB, by rw [op2_sum h0 hB, hsum]⟩, op2_isA h0 hB⟩
    · intro s hs
      rw [Finset.mem_filter, mem_DP] at hs
      exact op2_op1 hs.1.1 hs.2
    · intro t ht
      rw [Finset.mem_filter, mem_DP] at ht
      exact op1_op2 ht.1.1 ht.2
    · intro s hs
      rw [Finset.mem_filter, mem_DP] at hs
      obtain ⟨⟨h0, hsum⟩, hA⟩ := hs
      have hc := op1_card h0 hA
      rw [← hc, pow_succ]
      ring
  rw [key, Finset.sum_neg_distrib, neg_add_cancel]

end Cancellation

end Moves

section Exceptional

/-- The signed count of generalized pentagonal representations of `n`: the coefficient of `X^n`
in `∑ k, (-1)^k (X^(k(3k-1)/2) + X^(k(3k+1)/2))`. -/
def pentSign (n : ℕ) : ℤ :=
  (∑ k ∈ (Finset.range (n + 1)).filter (fun k => 2 * n = k * (3 * k - 1)), (-1 : ℤ) ^ k)
    + ∑ k ∈ (Finset.range (n + 1)).filter (fun k => 2 * n = k * (3 * k + 1) ∧ k ≠ 0), (-1 : ℤ) ^ k

lemma sum_stair1 (k : ℕ) : 2 * ∑ i ∈ Finset.Ico k (2 * k), i = k * (3 * k - 1) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have h : 2 * k - k = k := by omega
  rw [h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  cases k with
  | zero => simp
  | succ m =>
    have hs := Finset.sum_range_id_mul_two (m + 1)
    simp only [Nat.add_sub_cancel] at hs
    have h3 : 3 * (m + 1) - 1 = 3 * m + 2 := by omega
    rw [h3]
    nlinarith [hs]

lemma sum_stair2 (k : ℕ) : 2 * ∑ i ∈ Finset.Ico (k + 1) (2 * k + 1), i = k * (3 * k + 1) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have h : 2 * k + 1 - (k + 1) = k := by omega
  rw [h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  cases k with
  | zero => simp
  | succ m =>
    have hs := Finset.sum_range_id_mul_two (m + 1)
    simp only [Nat.add_sub_cancel] at hs
    nlinarith [hs]

lemma mx_Ico {a b : ℕ} (h : a < b) : mx (Finset.Ico a b) = b - 1 := by
  refine le_antisymm (Finset.sup_le ?_) ?_
  · intro x hx
    simp only [Finset.mem_Ico] at hx
    simp only [id]; omega
  · exact Finset.le_sup (f := id) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)

lemma mn_Ico {a b : ℕ} (h : a < b) : mn (Finset.Ico a b) = a := by
  have hne : (Finset.Ico a b).Nonempty := ⟨a, Finset.mem_Ico.mpr ⟨le_refl _, h⟩⟩
  simp only [mn, dif_pos hne]
  refine le_antisymm (Finset.min'_le _ _ (Finset.mem_Ico.mpr ⟨le_refl _, h⟩)) ?_
  exact Finset.le_min' _ _ _ (fun y hy => (Finset.mem_Ico.mp hy).1)

lemma zero_notMem_Ico {a b : ℕ} (ha : 1 ≤ a) : 0 ∉ Finset.Ico a b := by
  simp only [Finset.mem_Ico, not_and, not_lt]
  omega

lemma run_Ico {a b : ℕ} (h : a < b) (ha : 1 ≤ a) : run (Finset.Ico a b) = b - a := by
  have h0 : (0 : ℕ) ∉ Finset.Ico a b := zero_notMem_Ico ha
  have hmx := mx_Ico h
  have hnot : mx (Finset.Ico a b) - (b - a) ∉ Finset.Ico a b := by
    rw [hmx]
    simp only [Finset.mem_Ico, not_and, not_lt]
    intro hc; omega
  have hle : run (Finset.Ico a b) ≤ b - a := Nat.sInf_le ⟨by omega, hnot⟩
  refine le_antisymm hle ?_
  by_contra hc
  push_neg at hc
  have h1 : 1 ≤ run (Finset.Ico a b) := run_pos h0
  have h2 : mx (Finset.Ico a b) - run (Finset.Ico a b) ∈ Finset.Ico a b := by
    rw [hmx]
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  exact run_notMem h0 h2

/-- A set whose top run exhausts it is an interval. -/
lemma eq_Ico_of_run_eq_card {s : Finset ℕ} (hs : s.Nonempty) (h0 : 0 ∉ s)
    (h : run s = s.card) : s = Finset.Ico (mx s - s.card + 1) (mx s + 1) := by
  have hsub : Finset.Icc (mx s - run s + 1) (mx s) ⊆ s := Icc_run_subset hs
  have hcard : (Finset.Icc (mx s - run s + 1) (mx s)).card = run s := card_Icc_run hs h0
  have heq : Finset.Icc (mx s - run s + 1) (mx s) = s :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  rw [h] at heq
  exact heq.symm.trans (Finset.Ico_add_one_right_eq_Icc _ _).symm

/-- The staircases `{k, …, 2k-1}`. -/
lemma stair1_mem_DP {n k : ℕ} (hk : 2 * n = k * (3 * k - 1)) :
    Finset.Ico k (2 * k) ∈ DP n := by
  rw [mem_DP]
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk1
    · simp
    · exact zero_notMem_Ico hk1
  · have := sum_stair1 k
    omega

/-- The staircases `{k+1, …, 2k}`. -/
lemma stair2_mem_DP {n k : ℕ} (hk : 2 * n = k * (3 * k + 1)) :
    Finset.Ico (k + 1) (2 * k + 1) ∈ DP n := by
  rw [mem_DP]
  refine ⟨zero_notMem_Ico (by omega), ?_⟩
  have := sum_stair2 k
  omega

/-- The exceptional sets of the first kind: `{k, …, 2k-1}` (including `∅` for `k = 0`). -/
noncomputable def X1 (n : ℕ) : Finset (Finset ℕ) :=
  (DP n).filter (fun s => s = Finset.Ico s.card (2 * s.card))

/-- The exceptional sets of the second kind: `{k+1, …, 2k}` with `k ≥ 1`. -/
noncomputable def X2 (n : ℕ) : Finset (Finset ℕ) :=
  (DP n).filter (fun s => s = Finset.Ico (s.card + 1) (2 * s.card + 1) ∧ s.card ≠ 0)

lemma notIsA_notIsB_of_X1 {s : Finset ℕ} (h0 : 0 ∉ s) (hshape : s = Finset.Ico s.card (2 * s.card)) :
    ¬IsA s ∧ ¬IsB s := by
  set k := s.card with hk
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · have hemp : s = ∅ := by rw [hshape, hk0]; simp
    constructor
    · rintro ⟨hs, -⟩; rw [hemp] at hs; exact absurd hs (by simp)
    · rintro ⟨hs, -⟩; rw [hemp] at hs; exact absurd hs (by simp)
  · have hmn : mn s = k := by rw [hshape]; exact mn_Ico (by omega)
    have hrun : run s = k := by rw [hshape, run_Ico (by omega) (by omega)]; omega
    constructor
    · rintro ⟨-, -, hex⟩
      exact hex ⟨by omega, by omega⟩
    · rintro ⟨-, hlt, -⟩
      omega

lemma notIsA_notIsB_of_X2 {s : Finset ℕ} (h0 : 0 ∉ s)
    (hshape : s = Finset.Ico (s.card + 1) (2 * s.card + 1)) (hne : s.card ≠ 0) :
    ¬IsA s ∧ ¬IsB s := by
  set k := s.card with hk
  have hk1 : 1 ≤ k := by omega
  have hmn : mn s = k + 1 := by rw [hshape]; exact mn_Ico (by omega)
  have hrun : run s = k := by rw [hshape, run_Ico (by omega) (by omega)]; omega
  constructor
  · rintro ⟨-, hle, -⟩
    omega
  · rintro ⟨-, -, hex⟩
    exact hex ⟨by omega, by omega⟩

lemma exc_eq (n : ℕ) :
    (DP n).filter (fun s => ¬IsA s ∧ ¬IsB s) = X1 n ∪ X2 n := by
  ext s
  simp only [X1, X2, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hmem, hnA, hnB⟩
    have h0 := (mem_DP.mp hmem).1
    by_cases hemp : s = ∅
    · refine Or.inl ⟨hmem, ?_⟩
      rw [hemp]; simp
    · have hs : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
      have hcardpos : 1 ≤ s.card := Finset.card_pos.mpr hs
      have hmnpos := mn_pos hs h0
      have hmnmx := mn_le_mx hs
      rw [IsA] at hnA
      rw [IsB] at hnB
      push_neg at hnA hnB
      by_cases hcase : mn s ≤ run s
      · obtain ⟨hcr, hrm⟩ := hnA hs hcase
        have hIco := eq_Ico_of_run_eq_card hs h0 hcr.symm
        set M := mx s with hM
        set k := s.card with hk
        have hmnval : mn s = M - k + 1 := by rw [hIco]; exact mn_Ico (by omega)
        refine Or.inl ⟨hmem, ?_⟩
        rw [hIco]
        congr 1 <;> omega
      · push_neg at hcase
        obtain ⟨hcr, hrm⟩ := hnB hs hcase
        have hIco := eq_Ico_of_run_eq_card hs h0 hcr.symm
        set M := mx s with hM
        set k := s.card with hk
        have hmnval : mn s = M - k + 1 := by rw [hIco]; exact mn_Ico (by omega)
        refine Or.inr ⟨hmem, ?_, by omega⟩
        rw [hIco]
        congr 1 <;> omega
  · rintro (⟨hmem, hshape⟩ | ⟨hmem, hshape, hne⟩)
    · exact ⟨hmem, notIsA_notIsB_of_X1 (mem_DP.mp hmem).1 hshape⟩
    · exact ⟨hmem, notIsA_notIsB_of_X2 (mem_DP.mp hmem).1 hshape hne⟩

lemma X1_disjoint_X2 (n : ℕ) : Disjoint (X1 n) (X2 n) := by
  rw [Finset.disjoint_left]
  intro s hs1 hs2
  simp only [X1, X2, Finset.mem_filter] at hs1 hs2
  obtain ⟨-, h1⟩ := hs1
  obtain ⟨-, h2, hne⟩ := hs2
  set k := s.card with hk
  have hk1 : 1 ≤ k := by omega
  have hmem : k ∈ s := by rw [h1]; exact Finset.mem_Ico.mpr ⟨le_refl _, by omega⟩
  rw [h2] at hmem
  simp only [Finset.mem_Ico] at hmem
  omega

lemma le_of_pent1 {n k : ℕ} (h : 2 * n = k * (3 * k - 1)) : k ≤ n := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · omega
  · have h2 : 2 ≤ 3 * k - 1 := by omega
    have : 2 * k ≤ k * (3 * k - 1) := by nlinarith
    omega

lemma le_of_pent2 {n k : ℕ} (h : 2 * n = k * (3 * k + 1)) : k ≤ n := by
  nlinarith

lemma sum_X1 (n : ℕ) :
    (∑ s ∈ X1 n, (-1 : ℤ) ^ s.card)
      = ∑ k ∈ (Finset.range (n + 1)).filter (fun k => 2 * n = k * (3 * k - 1)), (-1 : ℤ) ^ k := by
  refine Finset.sum_nbij' (fun s => s.card) (fun k => Finset.Ico k (2 * k)) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    simp only [X1, Finset.mem_filter, mem_DP] at hs
    obtain ⟨⟨h0, hsum⟩, hshape⟩ := hs
    have hsum' : ∑ i ∈ Finset.Ico s.card (2 * s.card), i = n := by rw [← hshape]; exact hsum
    have hpent := sum_stair1 s.card
    rw [hsum'] at hpent
    have hk_le := le_of_pent1 hpent
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hpent⟩
  · intro k hk
    rw [Finset.mem_filter] at hk
    have hcard : (Finset.Ico k (2 * k)).card = k := by rw [Nat.card_Ico]; omega
    simp only [X1, Finset.mem_filter]
    exact ⟨stair1_mem_DP hk.2, by rw [hcard]⟩
  · intro s hs
    simp only [X1, Finset.mem_filter] at hs
    exact hs.2.symm
  · intro k hk
    simp only [Nat.card_Ico]
    omega
  · intro s _
    rfl

lemma sum_X2 (n : ℕ) :
    (∑ s ∈ X2 n, (-1 : ℤ) ^ s.card)
      = ∑ k ∈ (Finset.range (n + 1)).filter (fun k => 2 * n = k * (3 * k + 1) ∧ k ≠ 0),
          (-1 : ℤ) ^ k := by
  refine Finset.sum_nbij' (fun s => s.card) (fun k => Finset.Ico (k + 1) (2 * k + 1)) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    simp only [X2, Finset.mem_filter, mem_DP] at hs
    obtain ⟨⟨h0, hsum⟩, hshape, hne⟩ := hs
    have hsum' : ∑ i ∈ Finset.Ico (s.card + 1) (2 * s.card + 1), i = n := by
      rw [← hshape]; exact hsum
    have hpent := sum_stair2 s.card
    rw [hsum'] at hpent
    have hk_le := le_of_pent2 hpent
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hpent, hne⟩
  · intro k hk
    rw [Finset.mem_filter] at hk
    have hcard : (Finset.Ico (k + 1) (2 * k + 1)).card = k := by rw [Nat.card_Ico]; omega
    simp only [X2, Finset.mem_filter]
    exact ⟨stair2_mem_DP hk.2.1, by rw [hcard], by rw [hcard]; exact hk.2.2⟩
  · intro s hs
    simp only [X2, Finset.mem_filter] at hs
    exact hs.2.1.symm
  · intro k hk
    simp only [Nat.card_Ico]
    omega
  · intro s _
    rfl

lemma not_isA_of_isB {s : Finset ℕ} (hB : IsB s) : ¬IsA s := by
  rintro ⟨-, hle, -⟩
  have := hB.2.1
  omega

/-- **Franklin's theorem** (the combinatorial form of Euler's pentagonal number theorem):
the number of partitions of `n` into an even number of distinct parts minus the number with an
odd number of distinct parts is `(-1)^k` when `n = k(3k±1)/2`, and `0` otherwise. -/
theorem sum_sign_DP (n : ℕ) : (∑ s ∈ DP n, (-1 : ℤ) ^ s.card) = pentSign n := by
  classical
  have hsplit1 : (∑ s ∈ (DP n).filter IsA, (-1 : ℤ) ^ s.card)
      + ∑ s ∈ (DP n).filter (fun s => ¬IsA s), (-1 : ℤ) ^ s.card
      = ∑ s ∈ DP n, (-1 : ℤ) ^ s.card :=
    Finset.sum_filter_add_sum_filter_not (DP n) IsA _
  have hsplit2 : (∑ s ∈ ((DP n).filter (fun s => ¬IsA s)).filter IsB, (-1 : ℤ) ^ s.card)
      + ∑ s ∈ ((DP n).filter (fun s => ¬IsA s)).filter (fun s => ¬IsB s), (-1 : ℤ) ^ s.card
      = ∑ s ∈ (DP n).filter (fun s => ¬IsA s), (-1 : ℤ) ^ s.card :=
    Finset.sum_filter_add_sum_filter_not _ IsB _
  have hB : ((DP n).filter (fun s => ¬IsA s)).filter IsB = (DP n).filter IsB := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr ?_
    intro s _
    simp only [eq_iff_iff, and_iff_right_iff_imp]
    exact fun h => not_isA_of_isB h
  have hX : ((DP n).filter (fun s => ¬IsA s)).filter (fun s => ¬IsB s)
      = (DP n).filter (fun s => ¬IsA s ∧ ¬IsB s) := Finset.filter_filter _ _ _
  rw [← hsplit1, ← hsplit2, hB, hX, exc_eq n, Finset.sum_union (X1_disjoint_X2 n), sum_X1, sum_X2,
    ← add_assoc, sum_A_add_sum_B n, zero_add, pentSign]

end Exceptional

end Franklin

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
open scoped Classical

set_option maxHeartbeats 2000000

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

namespace Math

/-- The coefficient sequence of the pentagonal number series
`∑ k, (-1)^k (X^(k(3k-1)/2) + X^(k(3k+1)/2))`, indexed by the generalized pentagonal numbers.
The value at `n` is `(-1)^k` if `n = k(3k-1)/2` or `n = k(3k+1)/2` for some `k`, and `0`
otherwise. -/
noncomputable def pentagonalCoeff (n : ℕ) : ℤ := Franklin.pentSign n

/-- The character function whose partition generating function is `∏ (1 - X^i)`: a partition
contributes `(-1)^(number of parts)` if all its parts are distinct, and `0` otherwise. -/
noncomputable def fsgn : ℕ → ℕ → ℤ := fun _ c => if c = 1 then -1 else 0

private lemma prod_fsgn (n : ℕ) (p : n.Partition) :
    p.parts.toFinsupp.prod fsgn = if p.parts.Nodup then (-1 : ℤ) ^ (Multiset.card p.parts) else 0 := by
  rw [Finsupp.prod]
  simp only [Multiset.toFinsupp_support, Multiset.toFinsupp_apply, fsgn]
  by_cases h : p.parts.Nodup
  · rw [if_pos h]
    rw [Finset.prod_congr rfl (fun i hi => if_pos (by
      rw [Multiset.nodup_iff_count_eq_one] at h
      exact h i (Multiset.mem_toFinset.mp hi)))]
    rw [Finset.prod_const, Multiset.toFinset_card_of_nodup h]
  · rw [if_neg h]
    rw [Multiset.nodup_iff_count_le_one] at h
    push_neg at h
    obtain ⟨i, hi⟩ := h
    refine Finset.prod_eq_zero (i := i) ?_ ?_
    · exact Multiset.mem_toFinset.mpr (Multiset.count_pos.mp (by omega))
    · exact if_neg (by omega)

/-- Signed counting of distinct partitions, transported from `Finset ℕ` to `Nat.Partition`. -/
private lemma sum_distinct_eq_sum_DP (n : ℕ) :
    ∑ p ∈ (univ.filter (fun p : n.Partition => p.parts.Nodup)), (-1 : ℤ) ^ (Multiset.card p.parts)
      = ∑ s ∈ Franklin.DP n, (-1 : ℤ) ^ s.card := by
  refine Finset.sum_bij (fun p _ => p.parts.toFinset) ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp
    rw [Franklin.mem_DP]
    constructor
    · intro h0
      exact absurd (p.parts_pos (Multiset.mem_toFinset.mp h0)) (by simp)
    · rw [Finset.sum_eq_multiset_sum]
      simpa [Multiset.dedup_eq_self.mpr hp.2] using p.parts_sum
  · intro p hp q hq h
    rw [Finset.mem_filter] at hp hq
    apply Nat.Partition.ext
    have := congrArg Finset.val h
    simpa [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hp.2, Multiset.dedup_eq_self.mpr hq.2]
      using this
  · intro s hs
    rw [Franklin.mem_DP] at hs
    refine ⟨⟨s.val, ?_, ?_⟩, ?_, ?_⟩
    · intro i hi
      have : i ≠ 0 := by rintro rfl; exact hs.1 hi
      omega
    · rw [← hs.2, Finset.sum_eq_multiset_sum]; simp
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, s.nodup⟩
    · simp
  · intro p hp
    rw [Finset.mem_filter] at hp
    rw [Multiset.toFinset_card_of_nodup hp.2]

/-- The generating function attached to `fsgn` is the series with coefficients
`pentagonalCoeff`; this is Franklin's theorem restated for power series. -/
theorem genFun_fsgn_eq : Nat.Partition.genFun fsgn = PowerSeries.mk pentagonalCoeff := by
  ext n
  rw [Nat.Partition.coeff_genFun, PowerSeries.coeff_mk, pentagonalCoeff,
    ← Franklin.sum_sign_DP n, ← sum_distinct_eq_sum_DP n, Finset.sum_filter]
  exact Finset.sum_congr rfl (fun p _ => prod_fsgn n p)

/-- The product `∏ (1 - X^(i+1))` is the generating function attached to `fsgn`. -/
theorem hasProd_one_sub_X_pow :
    HasProd (fun i : ℕ => (1 : ℤ⟦X⟧) - X ^ (i + 1)) (Nat.Partition.genFun fsgn) := by
  have h := Nat.Partition.hasProd_genFun fsgn
  convert h using 2 with i
  rw [tsum_eq_single 0]
  · simp [fsgn]
    ring
  · intro b hb
    simp [fsgn, hb]

/-- **Euler's pentagonal number theorem.**  The infinite product `∏_{i ≥ 1} (1 - X^i)`, which is
the reciprocal of the generating function of the partition function, equals the pentagonal
number series `∑_{k} (-1)^k (X^(k(3k-1)/2) + X^(k(3k+1)/2))`. -/
theorem euler_pentagonal :
    ∏' i : ℕ, (1 - (X : ℤ⟦X⟧) ^ (i + 1)) = PowerSeries.mk pentagonalCoeff := by
  rw [hasProd_one_sub_X_pow.tprod_eq, genFun_fsgn_eq]

end Math

