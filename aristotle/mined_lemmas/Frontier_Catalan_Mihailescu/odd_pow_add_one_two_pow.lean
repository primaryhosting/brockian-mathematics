import Mathlib

/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Catalan's conjecture, proved by Mihailescu (2004), states that the only pair of consecutive
perfect powers is `8 = 2 ^ 3` and `9 = 3 ^ 2`; equivalently the only solution of
`x ^ p - y ^ q = 1` in integers `x, y, p, q > 1` is `3 ^ 2 - 2 ^ 3 = 1`.

Mihailescu's theorem is **not** available in Mathlib (a search of Mathlib turns up no
`Catalan`/`Mihailescu` result about the exponential Diophantine equation; the files mentioning
"Catalan" concern Catalan *numbers*, and `Mathlib/NumberTheory/FLT/Polynomial.lean` only contains
the *polynomial* analogue).  Accordingly this file:

* formalizes the statement (`Frontier.IsCatalanPair`);
* proves *unconditionally* the elementary base cases:
  - equal exponents (`Frontier.not_isCatalanPair_of_eq_exponents`),
  - base `2` on the left (`Frontier.not_isCatalanPair_two_left`): `2 ^ p` is never one more
    than a perfect power,
  - base `2` on the right (`Frontier.isCatalanPair_two_right`): the only perfect power that
    is one more than a power of two is `9 = 2 ^ 3 + 1`;
* proves a Lean-checked **reduction** (`Frontier.Catalan_Mihailescu`) of the full statement,
  for arbitrary exponents `> 1`, to the genuinely deep *core case* `Frontier.CatalanCoreCase`:
  distinct **prime** exponents and both bases `≥ 3`.
-/

namespace Frontier

/-- `IsCatalanPair x p y q` says that `x ^ p - y ^ q = 1`, where all four of
`x, y, p, q` are `> 1`; i.e. `x ^ p` and `y ^ q` are consecutive perfect powers. -/

theorem odd_pow_add_one_two_pow {y q n : ℕ} (hy3 : 3 ≤ y) (hyo : Odd y) (hq : Odd q)
    (h : y ^ q + 1 = 2 ^ n) : q = 1 := by
  have hcast : ((2 : ℤ) ^ n) = ((y : ℕ) ^ q + 1 : ℕ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) h.symm
  set T : ℤ := ∑ i ∈ Finset.range q, (y : ℤ) ^ i * (-1) ^ (q - 1 - i) with hT
  have hmul : T * ((y : ℤ) + 1) = 2 ^ n := by
    have h2 := geom_sum₂_mul ((y : ℤ)) (-1) q
    rw [hq.neg_one_pow] at h2
    rw [show ((y : ℤ) - (-1)) = (y : ℤ) + 1 by ring] at h2
    rw [hT, h2]
    push_cast at hcast
    linarith
  have hTodd : Odd T := by
    rw [Int.odd_iff, hT, Finset.sum_int_mod]
    have hterm : ∀ i ∈ Finset.range q, ((y : ℤ) ^ i * (-1) ^ (q - 1 - i)) % 2 = 1 := by
      intro i _
      exact Int.odd_iff.1 (Odd.mul ((Int.odd_coe_nat y).2 hyo).pow (Odd.pow (by decide)))
    rw [Finset.sum_congr rfl hterm]
    simp [Int.odd_iff.1 (by exact_mod_cast hq : Odd (q : ℤ))]
  have hTpos : 0 < T := by
    rcases lt_trichotomy T 0 with hlt | heq | hgt
    · nlinarith [pow_pos (show (0 : ℤ) < 2 by norm_num) n]
    · rw [heq] at hmul; simp at hmul; nlinarith [pow_pos (show (0 : ℤ) < 2 by norm_num) n]
    · exact hgt
  have hdvd : T.natAbs ∣ 2 ^ n := by
    have h1 : T ∣ (2 : ℤ) ^ n := ⟨(y : ℤ) + 1, hmul.symm⟩
    simpa using Int.natAbs_dvd_natAbs.2 h1
  have hT1 : T = 1 := by
    have := eq_one_of_odd_of_dvd_two_pow (Int.natAbs_odd.2 hTodd) hdvd
    omega
  rw [hT1, one_mul] at hmul
  have hpow : (y : ℤ) ^ q = (y : ℤ) ^ 1 := by
    push_cast at hcast
    simp
    linarith
  exact Nat.pow_right_injective (show 2 ≤ y by omega) (by exact_mod_cast hpow : y ^ q = y ^ 1)

/-! ### Base cases of Catalan's equation -/

/-- **Equal exponents**: `x ^ n - y ^ n = 1` has no solution with `x, y, n > 1`. -/
