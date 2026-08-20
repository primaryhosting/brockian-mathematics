import Mathlib
namespace Brockian.Dilworth
/-- Dilworth's theorem: in a finite partial order, the maximum size of an antichain equals the
    minimum number of chains needed to cover the order. -/
theorem dilworth {α : Type*} [Fintype α] [PartialOrder α] [DecidableEq α]
    (n : ℕ)
    (hanti : ∀ s : Finset α, IsAntichain (· ≤ ·) (s : Set α) → s.card ≤ n) :
    ∃ (C : Finset (Finset α)), C.card = n ∧
      (∀ c ∈ C, IsChain (· ≤ ·) (c : Set α)) ∧
      (∀ a : α, ∃ c ∈ C, a ∈ c) := by
  sorry
end Brockian.Dilworth
