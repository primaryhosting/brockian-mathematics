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

