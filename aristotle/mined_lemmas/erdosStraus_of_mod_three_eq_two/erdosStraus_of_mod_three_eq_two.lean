import Mathlib

/-- `4 / n` is a sum of three unit fractions with positive denominators. -/

theorem erdosStraus_of_mod_three_eq_two {n : ℕ} (hn : 2 ≤ n)
    (h : n % 3 = 2) : ErdosStrausSolvable n := by
  obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
  refine ⟨n, k + 1, n * (k + 1), by omega, by omega, by positivity, ?_⟩
  subst hk
  push_cast
  have h1 : (3 * (k : ℚ) + 2) ≠ 0 := by positivity
  have h2 : ((k : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  ring

