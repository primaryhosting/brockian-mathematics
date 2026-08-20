import Mathlib
namespace Brockian.MsMirsky
/-- Mirsky's theorem (dual of Dilworth): if every chain in a finite poset has size ≤ n, then the
    poset can be covered by n antichains. -/
theorem mirsky {α : Type*} [Fintype α] [PartialOrder α] [DecidableEq α] (n : ℕ)
    (hchain : ∀ c : Finset α, IsChain (· ≤ ·) (c : Set α) → c.card ≤ n) :
    ∃ A : Finset (Finset α), A.card = n ∧
      (∀ a ∈ A, IsAntichain (· ≤ ·) (a : Set α)) ∧ (∀ x : α, ∃ a ∈ A, x ∈ a) := by
  sorry
end Brockian.MsMirsky
