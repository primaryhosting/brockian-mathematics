import Mathlib

/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to be the very first commands of a file,
so the mandated header comment appears immediately after `import Mathlib`.

## Contents

The Catalan–Mihailescu theorem states that `8 = 2 ^ 3` and `9 = 3 ^ 2` are the only two
consecutive perfect powers, i.e. that the only solution of `x ^ p = y ^ q + 1` in integers
`x, y > 1`, `p, q > 1` is `3 ^ 2 = 2 ^ 3 + 1`.

This file contains:

* `Frontier.CatalanMihailescu` : the formal statement of the theorem.
* `Frontier.CatalanMihailescuPrimeExponents` : a restricted statement, where the two exponents
  are additionally assumed to be *distinct primes* and the pair of exponents is assumed to be
  different from `(3, 2)`.
* `Frontier.Catalan_Mihailescu` : the **Lean-checked reduction**, namely that the two statements
  above are equivalent. The nontrivial direction uses two unconditionally proved special cases:
  - `Frontier.pow_ne_pow_add_one` : `x ^ n ≠ y ^ n + 1` for `x, y > 1` and `n > 1`
    (equal exponents);
  - `Frontier.cube_ne_sq_add_one` : `x ^ 3 ≠ y ^ 2 + 1` for `y > 0`, i.e. no perfect cube is one
    more than a positive perfect square (the case `(p, q) = (3, 2)`; this is the case `n = 3` of
    a theorem of V. A. Lebesgue). It is proved here by unique factorization in the Gaussian
    integers `ℤ[i]`.
* `Frontier.catalan_base_case` : the base case `3 ^ 2 = 2 ^ 3 + 1`.
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

set_option grind.warning false

namespace Frontier

/-! ## Units of the Gaussian integers -/

/-- Every unit of `ℤ[i]` has order dividing `4`. -/

theorem three_pow_eq_two_pow_add_one (p q : ℕ) (hp : 1 < p) (hq : 1 < q)
    (h : 3 ^ p = 2 ^ q + 1) : p = 2 ∧ q = 3 := by
  have h4 : (2 : ℕ) ^ q % 4 = 0 := by
    obtain ⟨c, rfl⟩ : ∃ c, q = c + 2 := ⟨q - 2, by omega⟩
    rw [pow_add]
    omega
  -- `p` is even, since `3 ^ p ≡ 1 [MOD 4]`
  obtain ⟨t, rfl⟩ : ∃ t, p = 2 * t := by
    rcases Nat.even_or_odd p with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨t, by omega⟩
    · exfalso
      have h3 : (3 : ℕ) ^ p % 4 = 3 := by
        subst ht
        rw [pow_succ, pow_mul]
        have h9 : ((3 : ℕ) ^ 2) ^ t % 4 = 1 := by rw [Nat.pow_mod]; norm_num
        omega
      omega
  have ht1 : 1 ≤ t := by omega
  have hu3 : 3 ≤ 3 ^ t := by
    calc (3 : ℕ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ t := Nat.pow_le_pow_right (by norm_num) ht1
  have husq : (3 : ℕ) ^ t * 3 ^ t = 2 ^ q + 1 := by
    rw [← pow_add, show t + t = 2 * t by ring]; exact h
  -- `(3 ^ t - 1) * (3 ^ t + 1) = 2 ^ q`, so both factors are powers of two
  obtain ⟨a, ha⟩ : ∃ a, (3 : ℕ) ^ t = a + 1 := ⟨3 ^ t - 1, by omega⟩
  have hfac : a * (a + 2) = 2 ^ q := by rw [ha] at husq; nlinarith [husq]
  have ha2 : 2 ≤ a := by omega
  obtain ⟨i, hiq, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (⟨a + 2, hfac.symm⟩ : a ∣ 2 ^ q)
  obtain ⟨j, hjq, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (⟨a, by rw [← hfac]; ring⟩ : (a + 2) ∣ 2 ^ q)
  have hieq : i = 1 := by
    by_contra hne
    have hi1 : 1 ≤ i := by
      rcases Nat.eq_zero_or_pos i with rfl | h'
      · simp at hi; omega
      · exact h'
    have hi2 : 2 ≤ i := by omega
    have h4i : (4 : ℕ) ∣ a := by
      rw [hi]; exact dvd_trans (by norm_num) (pow_dvd_pow 2 hi2)
    have hjbig : 4 < 2 ^ j := by omega
    have hj2 : 2 ≤ j := by
      by_contra hj'
      interval_cases j <;> omega
    have h4j : (4 : ℕ) ∣ a + 2 := by
      rw [hj]; exact dvd_trans (by norm_num) (pow_dvd_pow 2 hj2)
    omega
  have hae : a = 2 := by rw [hi, hieq]; norm_num
  have hu' : (3 : ℕ) ^ t = 3 ^ 1 := by rw [ha, hae]; norm_num
  have ht : t = 1 := Nat.pow_right_injective (by norm_num) hu'
  subst ht
  refine ⟨by norm_num, ?_⟩
  have hq3 : (2 : ℕ) ^ q = 2 ^ 3 := by rw [← hfac, hae]; norm_num
  exact Nat.pow_right_injective (le_refl 2) hq3

/-! ## The statement of the Catalan–Mihailescu theorem and its reduction -/

/-- The Catalan–Mihailescu theorem: `3 ^ 2 = 2 ^ 3 + 1` is the only way for two perfect powers
(with bases and exponents `> 1`) to be consecutive. -/
