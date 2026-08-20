import Mathlib

/-!
# Legendre's three-square theorem

A natural number `n` is a sum of three squares if and only if it is not of the
form `4 ^ a * (8 * b + 7)`.

The proof is self-contained (only core `Mathlib` is used).  The hard direction
goes through the classical route:

* Minkowski's convex body theorem shows that every positive definite integral
  ternary quadratic form of determinant one represents `1`, hence (by descent)
  is of the shape `Nᵀ * N`.
* Dirichlet's theorem on primes in arithmetic progressions together with
  quadratic reciprocity produces, for every `n` with `n % 4 ≠ 0` and
  `n % 8 ≠ 7`, an integer `m > 0` with `n ∣ m + 1` and `-n` a square modulo `m`.
  Out of these data one builds an explicit positive definite integral ternary
  form of determinant one whose `(0,0)` entry is `n`.
-/

namespace Brockian.LegendreThreeSquare

open Matrix MeasureTheory
open scoped ENNReal

/-! ## Integral quadratic forms -/

/-- The value at `v` of the quadratic form attached to the integer matrix `A`. -/

lemma good_case2 (n : ℕ) (hn : 3 ≤ n) (h : n % 8 = 3) :
    ∃ m : ℕ, 0 < m ∧ n ∣ m + 1 ∧ ∃ y : ℤ, (m : ℤ) ∣ y ^ 2 + n := by
  obtain ⟨b, hb⟩ : ∃ b, n = 8 * b + 3 := ⟨n / 8, by omega⟩
  have hcop : Nat.Coprime (4 * b + 1) n := by
    refine nat_coprime_of_bezout _ _ (-2) 1 ?_
    rw [hb]; push_cast; ring
  obtain ⟨p, hp, hpgt, hpmod⟩ := exists_prime_mod n (by omega) (4 * b + 1) hcop n
  have hmod : p % n = 4 * b + 1 := by rw [hpmod, Nat.mod_eq_of_lt (by omega)]
  set q := p / n with hq
  have hpk : p = n * q + (4 * b + 1) := by conv_lhs => rw [← Nat.div_add_mod p n, hmod]
  have h2p : n ∣ 2 * p + 1 := ⟨2 * q + 1, by rw [hpk, hb]; ring⟩
  have hpn : (2 * p + 1) % n = 0 := Nat.mod_eq_zero_of_dvd h2p
  have hp2 : p ≠ 2 := by omega
  have hja := jacobi_case2 n p h hn hp hp2 hpn
  obtain ⟨y0, hy0⟩ := sq_of_jacobi_eq_one p hp _ (not_dvd_neg_of_lt n p (by omega) hpgt) hja
  have hy0' : (p : ℤ) ∣ y0 ^ 2 + n := by simpa using hy0
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨y, hyodd, hyp⟩ : ∃ y : ℤ, Odd y ∧ (p : ℤ) ∣ y ^ 2 + n := by
    rcases Int.even_or_odd y0 with he | ho
    · refine ⟨y0 + p, ?_, ?_⟩
      · obtain ⟨k, hk⟩ := he
        obtain ⟨j, hj⟩ := hpodd
        exact ⟨k + j, by push_cast [hk, hj]; ring⟩
      · obtain ⟨d, hd⟩ := hy0'
        exact ⟨d + 2 * y0 + p, by rw [show (y0 + p) ^ 2 + (n : ℤ) = (y0 ^ 2 + n) + p * (2 * y0 + p) by ring, hd]; ring⟩
    · exact ⟨y0, ho, hy0'⟩
  refine ⟨2 * p, by omega, by omega, y, ?_⟩
  have h2dvd : (2 : ℤ) ∣ y ^ 2 + n := by
    obtain ⟨j, hj⟩ := hyodd
    refine ⟨2 * j ^ 2 + 2 * j + 4 * b + 2, ?_⟩
    rw [hj, hb]; push_cast; ring
  have hcop2 : IsCoprime (2 : ℤ) (p : ℤ) := by
    obtain ⟨j, hj⟩ := hpodd
    exact ⟨-(j : ℤ), 1, by rw [hj]; push_cast; ring⟩
  have := hcop2.mul_dvd h2dvd hyp
  push_cast
  exact this

