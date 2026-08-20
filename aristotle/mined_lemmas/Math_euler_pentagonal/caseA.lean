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

