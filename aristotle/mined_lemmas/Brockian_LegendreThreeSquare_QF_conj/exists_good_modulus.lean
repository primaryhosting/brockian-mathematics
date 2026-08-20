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

theorem exists_good_modulus (n : ℕ) (hn : 3 ≤ n) (h4 : n % 4 ≠ 0) (h8 : n % 8 ≠ 7) :
    ∃ m : ℕ, 0 < m ∧ n ∣ m + 1 ∧ ∃ y : ℤ, (m : ℤ) ∣ y ^ 2 + n := by
  have h8' : n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 6 := by omega
  rcases h8' with h | h | h | h | h
  · exact good_case1 n hn (by omega)
  · exact good_case3 n hn h
  · exact good_case2 n hn h
  · exact good_case1 n hn (by omega)
  · exact good_case4 n hn h

/-! ## The two directions -/

