import Mathlib

theorem not_isSquare_sq_add_one (n : ℕ) (hn : 0 < n) : ¬ IsSquare (n ^ 2 + 1) := by
  rintro ⟨r, hr⟩
  have h1 : n < r := by nlinarith
  have h2 : r < n + 1 := by nlinarith
  omega
