import RequestProject.HuffmanKraft

/-!
# Weighted depth multisets, the Huffman merging process, and the optimality bound
-/

namespace CS

/-- A *weighted depth multiset*: a finite multiset of pairs `(weight, codeword length)`. -/
abbrev WD := Multiset (ℝ × ℕ)

/-- The expected codeword length associated to a weighted depth multiset. -/

theorem cost_nonneg {D : WD} (h : ∀ p ∈ D, 0 ≤ p.1) : 0 ≤ cost D := by
  refine Multiset.sum_nonneg ?_
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hx
  exact mul_nonneg (h p hp) (Nat.cast_nonneg _)

/-- Existence of a maximal element of a nonempty multiset in a linear order. -/
