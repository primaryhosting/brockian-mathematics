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

lemma good_case3 (n : ℕ) (hn : 3 ≤ n) (h : n % 8 = 2) :
    ∃ m : ℕ, 0 < m ∧ n ∣ m + 1 ∧ ∃ y : ℤ, (m : ℤ) ∣ y ^ 2 + n := by
  obtain ⟨a, ha⟩ : ∃ a, n = 8 * a + 2 := ⟨n / 8, by omega⟩
  have hcop : Nat.Coprime (8 * a + 1) (8 * (4 * a + 1)) := by
    refine nat_coprime_of_bezout _ _ (8 * (a : ℤ) + 1) (-(2 * (a : ℤ))) ?_
    push_cast; ring
  obtain ⟨p, hp, hpgt, hpmod⟩ := exists_prime_mod (8 * (4 * a + 1)) (by omega) (8 * a + 1) hcop n
  have hmod : p % (8 * (4 * a + 1)) = 8 * a + 1 := by
    rw [hpmod, Nat.mod_eq_of_lt (by omega)]
  set q := p / (8 * (4 * a + 1)) with hq
  set X := 8 * (4 * a + 1) * q with hX
  have hpk : p = X + (8 * a + 1) := by
    conv_lhs => rw [← Nat.div_add_mod p (8 * (4 * a + 1)), hmod]
  have hXdvd8 : 8 ∣ X := ⟨(4 * a + 1) * q, by rw [hX]; ring⟩
  have hp8 : p % 8 = 1 := by obtain ⟨t, ht⟩ := hXdvd8; omega
  have hdvdn : n ∣ p + 1 := by
    refine ⟨4 * q + 1, ?_⟩
    have : p + 1 = X + (8 * a + 2) := by omega
    rw [this, hX, ha]; ring
  have hdvdn' : (4 * a + 1) ∣ p + 1 := by
    refine ⟨8 * q + 2, ?_⟩
    have : p + 1 = X + (8 * a + 2) := by omega
    rw [this, hX]; ring
  have hpn : (p + 1) % (4 * a + 1) = 0 := Nat.mod_eq_zero_of_dvd hdvdn'
  have hja : jacobiSym (-(n : ℤ)) p = 1 := by
    have h3 := jacobi_case3 (4 * a + 1) p (by omega) (by omega) hp hp8 hpn
    rw [show ((n : ℤ)) = 2 * ((4 * a + 1 : ℕ) : ℤ) by rw [ha]; push_cast; ring]
    exact h3
  obtain ⟨y, hy⟩ := sq_of_jacobi_eq_one p hp _ (not_dvd_neg_of_lt n p (by omega) hpgt) hja
  exact ⟨p, hp.pos, hdvdn, y, by simpa using hy⟩

