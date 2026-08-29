import Mathlib


theorem hyperperfect_pos_of_hyperperfect {k n : ℕ} (hk : 1 ≤ k)
    (h : Hyperperfect k n) : n = 1 ∨ 3 ≤ n := by
  obtain ⟨hn, he⟩ := h
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · interval_cases n
    · left; rfl
    · exfalso
      have h2 : sigma1 2 = 3 := by decide
      rw [h2] at he
      omega
  · right; exact h3

