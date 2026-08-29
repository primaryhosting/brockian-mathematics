import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem two_zpow_neg_eq_div {k n : ℕ} (h : k ≤ n) :
    (2 : ℝ) ^ (-(k : ℤ)) = 2 ^ (n - k) / 2 ^ n := by
  have key : (2:ℝ) ^ (n - k) * 2 ^ k = 2 ^ n := by
    rw [← pow_add]; congr 1; omega
  rw [eq_div_iff (by positivity : (2:ℝ) ^ n ≠ 0), ← key, zpow_neg, zpow_natCast]
  field_simp

/-- A code `c` is *prefix-free* if no codeword is a prefix of a different symbol's codeword.
Note that this in particular forces `c` to be injective. -/
