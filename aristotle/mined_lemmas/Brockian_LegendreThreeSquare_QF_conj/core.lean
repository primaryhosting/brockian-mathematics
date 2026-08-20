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

theorem core (n : ℕ) (h4 : n % 4 ≠ 0) (h8 : n % 8 ≠ 7) : ∃ a b c : ℕ, n = a ^ 2 + b ^ 2 + c ^ 2 := by
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · interval_cases n
    · omega
    · exact ⟨1, 0, 0, by norm_num⟩
    · exact ⟨1, 1, 0, by norm_num⟩
  · obtain ⟨m, hm, hdvd, y, hy⟩ := exists_good_modulus n hge h4 h8
    exact three_squares_of_modulus n hge m hm hdvd y hy

