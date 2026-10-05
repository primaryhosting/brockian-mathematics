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

private lemma wit_mem (n : ℕ) : wit n ∈ AbcExceptions 0 := by
  set N := 2 ^ (n + 1) with hN
  have hNne : N ≠ 0 := by positivity
  have hN2 : 2 ≤ N := by
    have : (2 : ℕ) ^ 1 ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa [hN] using this
  have hc9 : 9 ≤ (3 : ℕ) ^ N := by
    calc (9 : ℕ) = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ N := Nat.pow_le_pow_right (by norm_num) hN2
  set b := 3 ^ N - 1 with hb
  have hbne : b ≠ 0 := by omega
  have hcne : (3 : ℕ) ^ N ≠ 0 := by omega
  have hradle : rad (1 * b * (3 ^ N)) ≤ rad b * 3 := by
    have h1 : (1 : ℕ) * b * 3 ^ N = b * 3 ^ N := by ring
    rw [h1]
    calc rad (b * 3 ^ N) ≤ rad b * rad (3 ^ N) := rad_mul_le hbne hcne
      _ = rad b * 3 := by rw [rad_prime_pow Nat.prime_three hNne]
  have hlt : rad (1 * b * (3 ^ N)) < 3 ^ N := lt_of_le_of_lt hradle (rad_wit_lt n)
  show (1, b, 3 ^ N) ∈ AbcExceptions 0
  simp only [AbcExceptions, Set.mem_setOf_eq]
  refine ⟨by norm_num, by omega, by omega, Nat.coprime_one_left b, ?_⟩
  rw [add_zero, Real.rpow_one]
  exact_mod_cast hlt

