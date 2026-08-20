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

lemma jacobi_case1 (n p : ℕ) (hn : n % 4 = 1) (hn3 : 3 ≤ n) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hpn : (p + 1) % n = 0) : jacobiSym (-(n : ℤ)) p = 1 := by
  have hpodd : Odd p := by rw [Nat.odd_iff]; omega
  have hnodd : Odd n := by rw [Nat.odd_iff]; omega
  have hchi4n : ZMod.χ₄ (n : ZMod 4) = 1 := by
    rw [ZMod.χ₄_nat_eq_if_mod_four]
    simp only [if_neg (by omega : ¬ n % 2 = 0), if_pos hn]
  have hchi4p : ZMod.χ₄ (p : ZMod 4) = 1 := by
    rw [ZMod.χ₄_nat_eq_if_mod_four]
    simp only [if_neg (by omega : ¬ p % 2 = 0), if_pos hp4]
  have hpn1 : jacobiSym (p : ℤ) n = 1 := by
    rw [jacobi_p_mod_n n p hpn, jacobiSym.at_neg_one hnodd, hchi4n]
  have hrec : jacobiSym (n : ℤ) p = (-1) ^ (n / 2 * (p / 2)) * jacobiSym (p : ℤ) n :=
    jacobiSym.quadratic_reciprocity hnodd hpodd
  have hneg : jacobiSym (-(n : ℤ)) p = jacobiSym (-1) p * jacobiSym (n : ℤ) p := by
    rw [← jacobiSym.mul_left]; ring_nf
  obtain ⟨k, hk⟩ : ∃ k, p = 4 * k + 1 := ⟨p / 4, by omega⟩
  have hpd : p / 2 = 2 * k := by omega
  rw [hneg, hrec, hpn1, jacobiSym.at_neg_one hpodd, hchi4p,
    show ((-1 : ℤ) ^ (n / 2 * (p / 2))) = 1 from
      Even.neg_one_pow (by rw [hpd]; exact ⟨n / 2 * k, by ring⟩)]
  ring

/-- Case `n ≡ 3 [MOD 8]`. -/
