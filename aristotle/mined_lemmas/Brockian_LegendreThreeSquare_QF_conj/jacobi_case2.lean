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

lemma jacobi_case2 (n p : ℕ) (hn : n % 8 = 3) (hn3 : 3 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : (2 * p + 1) % n = 0) : jacobiSym (-(n : ℤ)) p = 1 := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hnodd : Odd n := by rw [Nat.odd_iff]; omega
  obtain ⟨b, hb⟩ : ∃ b, n = 8 * b + 3 := ⟨n / 8, by omega⟩
  have hn2 : n / 2 = 4 * b + 1 := by omega
  have hchi4n : ZMod.χ₄ (n : ZMod 4) = -1 := by
    rw [ZMod.χ₄_nat_eq_if_mod_four]
    simp only [if_neg (by omega : ¬ n % 2 = 0), if_neg (by omega : ¬ n % 4 = 1)]
  have hchi8n : ZMod.χ₈ (n : ZMod 8) = -1 := by
    rw [ZMod.χ₈_nat_eq_if_mod_eight]
    simp only [if_neg (by omega : ¬ n % 2 = 0), if_neg (by omega : ¬ (n % 8 = 1 ∨ n % 8 = 7))]
  have hpn1 : jacobiSym (p : ℤ) n = 1 := by
    have h1 : jacobiSym (2 * p : ℤ) n = jacobiSym (-1) n := jacobi_two_p_mod_n n p hpn
    rw [show ((2 * p : ℤ)) = (2 : ℤ) * (p : ℤ) by ring, jacobiSym.mul_left,
      jacobiSym.at_two hnodd, jacobiSym.at_neg_one hnodd, hchi4n, hchi8n] at h1
    linarith [h1]
  have hrec : jacobiSym (n : ℤ) p = (-1) ^ (n / 2 * (p / 2)) * jacobiSym (p : ℤ) n :=
    jacobiSym.quadratic_reciprocity hnodd hpodd
  have hneg : jacobiSym (-(n : ℤ)) p = jacobiSym (-1) p * jacobiSym (n : ℤ) p := by
    rw [← jacobiSym.mul_left]; ring_nf
  rw [hneg, hrec, hpn1, jacobiSym.at_neg_one hpodd, ZMod.χ₄_nat_eq_if_mod_four]
  have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by rw [Nat.odd_iff] at hpodd; omega
  rcases hp4 with h4 | h4
  · obtain ⟨k, hk⟩ : ∃ k, p = 4 * k + 1 := ⟨p / 4, by omega⟩
    have hpd : p / 2 = 2 * k := by omega
    simp only [if_neg (by omega : ¬ p % 2 = 0), if_pos h4]
    rw [show ((-1 : ℤ) ^ (n / 2 * (p / 2))) = 1 from
      Even.neg_one_pow (by rw [hn2, hpd]; exact ⟨(4 * b + 1) * k, by ring⟩)]
    ring
  · obtain ⟨k, hk⟩ : ∃ k, p = 4 * k + 3 := ⟨p / 4, by omega⟩
    have hpd : p / 2 = 2 * k + 1 := by omega
    simp only [if_neg (by omega : ¬ p % 2 = 0), if_neg (by omega : ¬ p % 4 = 1)]
    rw [show ((-1 : ℤ) ^ (n / 2 * (p / 2))) = -1 from
      Odd.neg_one_pow (by rw [hn2, hpd]; exact ⟨(4 * b + 1) * k + 2 * b, by ring⟩)]
    ring

/-- Case `n ≡ 2 [MOD 8]`, `n = 2 * n'`. -/
