import Mathlib
namespace Brockian.MsBeatty
/-- Rayleigh–Beatty theorem: if 1/r + 1/s = 1 with r > 1 irrational, the Beatty sequences ⌊n·r⌋
    and ⌊n·s⌋ partition the positive integers — each n > 0 is hit by exactly one. -/
theorem beatty (r s : ℝ) (hr : 1 < r) (hirr : Irrational r) (hsum : 1 / r + 1 / s = 1)
    (n : ℕ) (hn : 0 < n) :
    (∃ m : ℕ, 0 < m ∧ ⌊(m : ℝ) * r⌋ = (n : ℤ)) ↔
      ¬ (∃ m : ℕ, 0 < m ∧ ⌊(m : ℝ) * s⌋ = (n : ℤ)) := by
  sorry
end Brockian.MsBeatty
