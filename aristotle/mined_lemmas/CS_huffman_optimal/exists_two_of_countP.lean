import RequestProject.HuffmanKraft

/-!
# Weighted depth multisets, the Huffman merging process, and the optimality bound
-/

namespace CS

/-- A *weighted depth multiset*: a finite multiset of pairs `(weight, codeword length)`. -/
abbrev WD := Multiset (ℝ × ℕ)

/-- The expected codeword length associated to a weighted depth multiset. -/

theorem exists_two_of_countP {P : ℝ × ℕ → Prop} [DecidablePred P] {D : WD}
    (h : 2 ≤ D.countP P) : ∃ p q D₀, P p ∧ P q ∧ D = p ::ₘ q ::ₘ D₀ := by
  rw [Multiset.countP_eq_card_filter] at h
  obtain ⟨p, hp⟩ := (Multiset.card_pos_iff_exists_mem (s := D.filter P)).1 (by omega)
  have hcard2 : 0 < ((D.filter P).erase p).card := by
    rw [Multiset.card_erase_of_mem hp]; omega
  obtain ⟨q, hq⟩ := (Multiset.card_pos_iff_exists_mem (s := (D.filter P).erase p)).1 hcard2
  have hpD : p ∈ D := Multiset.mem_of_mem_filter hp
  have hPp : P p := Multiset.of_mem_filter hp
  have hPq : P q := Multiset.of_mem_filter (Multiset.mem_of_mem_erase hq)
  have hqD : q ∈ D.erase p :=
    Multiset.mem_of_le (Multiset.erase_le_erase p (Multiset.filter_le P D)) hq
  refine ⟨p, q, (D.erase p).erase q, hPp, hPq, ?_⟩
  rw [Multiset.cons_erase hqD, Multiset.cons_erase hpD]

