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

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- The radical of a natural number: the product of its distinct prime divisors. -/

lemma mem_abcExceptions_zero (n : ℕ) :
    ((1 : ℕ), 2 ^ (6 * (n + 1)) - 1, 2 ^ (6 * (n + 1))) ∈ abcExceptions 0 := by
  set c : ℕ := 2 ^ (6 * (n + 1)) with hc
  have hc64 : 64 ≤ c := by
    have : (2 : ℕ) ^ 6 ≤ 2 ^ (6 * (n + 1)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa [hc] using this
  set b : ℕ := c - 1 with hb
  have hb1 : b + 1 = c := by omega
  have hb0 : b ≠ 0 := by omega
  have hc0 : c ≠ 0 := by omega
  have h9 : 9 ∣ b := by
    rw [hb, hc]; exact nine_dvd_two_pow_six_mul_sub_one (n + 1)
  have hcop : Nat.Coprime b c := by
    rw [← hb1]; simp
  have hradc : rad c = 2 := by
    rw [hc, rad_pow_eq 2 (by omega), rad_of_prime Nat.prime_two]
  have hradbc : rad (1 * b * c) = rad b * 2 := by
    rw [one_mul, rad_mul_of_coprime hb0 hc0 hcop, hradc]
  have hkey : rad b * 2 < c := by
    have := three_mul_rad_le hb0 h9
    omega
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩
  · dsimp only
    omega
  · dsimp only
    simp
  · dsimp only
    omega
  simp only
  rw [hradbc]
  rw [show (1 : ℝ) + 0 = 1 by norm_num, Real.rpow_one]
  exact_mod_cast hkey

/-- The exponent `1 + ε` with `ε > 0` is necessary: for `ε = 0` there are infinitely many
coprime triples `a + b = c` with `rad (a*b*c) < c`. -/
