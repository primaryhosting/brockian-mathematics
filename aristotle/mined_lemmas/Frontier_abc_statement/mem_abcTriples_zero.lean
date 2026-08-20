/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
Mathlib does not state the `abc` conjecture. The closest existing material is
`UniqueFactorizationMonoid.radical` (`Mathlib/RingTheory/Radical.lean`), a general radical
of an element of a UFM, and the Mason–Stothers theorem
(`Mathlib/NumberTheory/FLT/MasonStothers.lean`), the polynomial analogue of `abc`.
Neither closes the statement below, so the radical for `ℕ` and both formulations of the
conjecture are set up here from scratch.
-/

namespace Frontier

open scoped BigOperators

/-- The radical of a natural number: the product of its distinct prime factors.
By convention `rad 0 = rad 1 = 1`. -/

lemma mem_abcTriples_zero (k : ℕ) :
    ((1, 3 ^ 2 ^ (k + 1) - 1, 3 ^ 2 ^ (k + 1)) : ℕ × ℕ × ℕ) ∈ abcTriples 0 := by
  set c : ℕ := 3 ^ 2 ^ (k + 1) with hc
  have hc9 : 9 ≤ c := by
    calc (9 : ℕ) = 3 ^ 2 ^ 1 := by norm_num
      _ ≤ 3 ^ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega))
  set b : ℕ := c - 1 with hbdef
  have hb : 0 < b := by omega
  have hsum : 1 + b = c := by omega
  have hcop : Nat.Coprime b c := by
    have : c = b + 1 := by omega
    rw [this]
    simp [Nat.Coprime]
  have hdvd : 2 ^ (k + 2 + 1) ∣ b := two_pow_dvd_three_pow_sub_one k
  have hbound : 2 ^ (k + 2) * rad b ≤ b := rad_mul_two_pow_le hb hdvd
  have hfour : (4 : ℕ) ≤ 2 ^ (k + 2) := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 4 * rad b ≤ b := le_trans (Nat.mul_le_mul_right _ hfour) hbound
  have hradc : rad c = 3 := rad_prime_pow (by norm_num) (by positivity)
  have hradbc : rad (1 * b * c) = rad b * 3 := by
    rw [one_mul, rad_mul_of_coprime hb.ne' (by omega) hcop, hradc]
  have hlt : rad (1 * b * c) < c := by
    have h1 : 1 ≤ rad b := one_le_rad b
    rw [hradbc]; omega
  refine ⟨one_pos, hb, Nat.coprime_one_left b, hsum, ?_⟩
  have : ((rad (1 * b * c) : ℝ)) < (c : ℝ) := by exact_mod_cast hlt
  simpa using this

/-- **The exponent `1 + ε` is necessary**: with `ε = 0` there are infinitely many coprime
triples `a + b = c` with `rad (a*b*c) < c`. -/
