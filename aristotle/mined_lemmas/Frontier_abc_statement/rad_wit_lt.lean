import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Frontier

/-- The radical of a natural number: the product of its distinct prime factors. -/

private lemma rad_wit_lt (n : ℕ) :
    rad (3 ^ (2 ^ (n + 1)) - 1) * 3 < 3 ^ (2 ^ (n + 1)) := by
  set N := 2 ^ (n + 1) with hN
  have hN2 : 2 ≤ N := by
    have : (2 : ℕ) ^ 1 ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa [hN] using this
  have hc9 : 9 ≤ (3 : ℕ) ^ N := by
    calc (9 : ℕ) = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ N := Nat.pow_le_pow_right (by norm_num) hN2
  set b := 3 ^ N - 1 with hb
  have hbne : b ≠ 0 := by omega
  have hdvd : 2 ^ (n + 3) ∣ b := two_pow_dvd_three_pow n
  have hkey : 2 ^ (n + 3) * rad b ≤ 2 * b := two_pow_mul_rad_le hbne hdvd
  have h8 : (8 : ℕ) ≤ 2 ^ (n + 3) := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (n + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 4 * rad b ≤ b := by
    have : 8 * rad b ≤ 2 ^ (n + 3) * rad b := Nat.mul_le_mul_right _ h8
    omega
  omega

