/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open scoped Real

/-- The radical of a natural number: the product of its distinct prime divisors. -/

lemma nine_pow_triple_mem_exceptional {n : ℕ} (hn : 1 ≤ n) :
    ((1, 9 ^ n - 1, 9 ^ n) : ℕ × ℕ × ℕ) ∈ exceptionalSet 0 := by
  have h9 : 9 ≤ 9 ^ n := by
    calc (9 : ℕ) = 9 ^ 1 := by norm_num
      _ ≤ 9 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set m := 9 ^ n - 1 with hm
  have hmc : m + 1 = 9 ^ n := by omega
  have hmpos : 0 < m := by omega
  have h8 : 8 ∣ m := by
    have h := Nat.sub_dvd_pow_sub_pow 9 1 n
    simpa [hm] using h
  have hkey : 4 * rad m ≤ m := four_mul_rad_le_of_eight_dvd hmpos h8
  have hcop : Nat.Coprime m (9 ^ n) := by
    rw [← hmc]
    simp [Nat.Coprime]
  have hrad9 : rad (9 ^ n) = 3 := by
    have h : (9 : ℕ) ^ n = 3 ^ (2 * n) := by rw [pow_mul]; norm_num
    rw [h, rad_pow 3 (by omega), rad_prime (by norm_num)]
  have hradprod : rad (1 * m * 9 ^ n) = rad m * 3 := by
    rw [one_mul, rad_mul_of_coprime hcop hmpos.ne' (by positivity), hrad9]
  refine ⟨⟨one_pos, hmpos, show 1 + m = 9 ^ n by omega, by simp⟩, ?_⟩
  have hlt : rad m * 3 < 9 ^ n := by omega
  simp only [hradprod, add_zero, Real.rpow_one]
  exact_mod_cast hlt

/-- The exponent `ε > 0` in the abc conjecture cannot be dropped: there are infinitely many
coprime triples `a + b = c` with `c > rad (a * b * c)`. -/
