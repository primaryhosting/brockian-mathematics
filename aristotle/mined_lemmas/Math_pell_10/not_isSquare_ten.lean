import Mathlib

/-!
# Pell 10 — Mathlib-based proof

A second, non-constructive proof of the statement `Math.pell_10` (see `RequestProject/Main.lean`),
obtained from Mathlib's general existence theorem for Pell equations,
`Pell.exists_of_not_isSquare : 0 < d → ¬IsSquare d → ∃ x y, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0`.
-/

namespace Math

/-- `10` is not a perfect square (as an integer). -/

theorem not_isSquare_ten : ¬ IsSquare (10 : ℤ) := by
  rw [show (10 : ℤ) = ((10 : ℕ) : ℤ) by norm_num, Int.isSquare_natCast_iff]
  rintro ⟨r, hr⟩
  have hr10 : r ≤ 10 := by nlinarith
  interval_cases r <;> omega

/-- **Pell's equation for `d = 10`**, via `Pell.exists_of_not_isSquare`. -/
