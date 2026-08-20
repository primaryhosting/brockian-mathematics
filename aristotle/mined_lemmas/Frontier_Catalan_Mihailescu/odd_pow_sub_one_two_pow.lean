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

theorem odd_pow_sub_one_two_pow {x p n : ℕ} (hx3 : 3 ≤ x) (hxo : Odd x) (hp : Odd p)
    (h : x ^ p = 2 ^ n + 1) : p = 1 := by
  obtain ⟨z, rfl⟩ : ∃ z, x = z + 1 := ⟨x - 1, by omega⟩
  set S : ℕ := ∑ i ∈ Finset.range p, (z + 1) ^ i with hS
  have hnat : (z + 1) ^ p = z * S + 1 := by
    have h2 := geom_sum_mul ((z : ℤ) + 1) p
    have h3 : ((z : ℤ) + 1) ^ p = (z : ℤ) * (∑ i ∈ Finset.range p, ((z : ℤ) + 1) ^ i) + 1 := by
      ring_nf at h2 ⊢
      linarith
    have h4 : ((z + 1 : ℕ) ^ p : ℤ) = ((z * S + 1 : ℕ) : ℤ) := by
      push_cast [hS]
      convert h3 using 2
    exact_mod_cast h4
  have hdvd : S ∣ 2 ^ n := ⟨z, by rw [mul_comm]; omega⟩
  have hSodd : Odd S := by
    rw [Nat.odd_iff, hS, Finset.sum_nat_mod]
    have hterm : ∀ i ∈ Finset.range p, (z + 1) ^ i % 2 = 1 := fun i _ => Nat.odd_iff.1 hxo.pow
    rw [Finset.sum_congr rfl hterm]
    simp [Nat.odd_iff.1 hp]
  have hS1 : S = 1 := eq_one_of_odd_of_dvd_two_pow hSodd hdvd
  have hpow : (z + 1) ^ p = (z + 1) ^ 1 := by rw [hS1] at hnat; simpa using hnat
  exact Nat.pow_right_injective (by omega) hpow

/-- If `y ≥ 3` is odd, `q` is odd and `y ^ q + 1` is a power of two, then `q = 1`.
The point is that `(y ^ q + 1) / (y + 1) = ∑ i < q, (-1) ^ i y ^ i` is odd, hence equal to `1`. -/
