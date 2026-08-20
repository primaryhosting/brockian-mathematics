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

lemma good_case1 (n : ℕ) (hn : 3 ≤ n) (h : n % 4 = 1) :
    ∃ m : ℕ, 0 < m ∧ n ∣ m + 1 ∧ ∃ y : ℤ, (m : ℤ) ∣ y ^ 2 + n := by
  have hcop : Nat.Coprime (2 * n - 1) (4 * n) := by
    refine nat_coprime_of_bezout _ _ (2 * (n : ℤ) - 1) (-((n : ℤ) - 1)) ?_
    have hc : ((2 * n - 1 : ℕ) : ℤ) = 2 * (n : ℤ) - 1 := by
      have h1 : 1 ≤ 2 * n := by omega
      push_cast [Nat.cast_sub h1]; ring
    rw [hc]; push_cast; ring
  obtain ⟨p, hp, hpgt, hpmod⟩ := exists_prime_mod (4 * n) (by omega) (2 * n - 1) hcop n
  have hmod : p % (4 * n) = 2 * n - 1 := by rw [hpmod, Nat.mod_eq_of_lt (by omega)]
  set q := p / (4 * n) with hq
  set X := 4 * n * q with hX
  have hpk : p = X + (2 * n - 1) := by
    conv_lhs => rw [← Nat.div_add_mod p (4 * n), hmod]
  have hXdvd4 : 4 ∣ X := ⟨n * q, by rw [hX]; ring⟩
  have hXdvdn : n ∣ X := ⟨4 * q, by rw [hX]; ring⟩
  have hp4 : p % 4 = 1 := by obtain ⟨t, ht⟩ := hXdvd4; omega
  have hdvd : n ∣ p + 1 := by
    have hp1 : p + 1 = X + 2 * n := by omega
    rw [hp1]
    exact Nat.dvd_add hXdvdn ⟨2, by ring⟩
  have hpn : (p + 1) % n = 0 := Nat.eq_zero_of_dvd_of_lt hdvd |> fun _ => Nat.mod_eq_zero_of_dvd hdvd
  refine ⟨p, hp.pos, hdvd, ?_⟩
  obtain ⟨y, hy⟩ := sq_of_jacobi_eq_one p hp _ (not_dvd_neg_of_lt n p (by omega) hpgt)
    (jacobi_case1 n p h hn hp hp4 hpn)
  exact ⟨y, by simpa using hy⟩

