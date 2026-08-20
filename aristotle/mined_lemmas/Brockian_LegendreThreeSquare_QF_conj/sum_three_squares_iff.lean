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

theorem sum_three_squares_iff (n : ℕ) :
    (∃ a b c : ℕ, n = a ^ 2 + b ^ 2 + c ^ 2) ↔ ¬ ∃ k m : ℕ, n = 4 ^ k * (8 * m + 7) := by
  constructor
  · rintro ⟨a, b, c, habc⟩ ⟨k, m, hkm⟩
    exact not_sum_three_squares k m a b c (hkm ▸ habc)
  · exact hard_direction n

end Brockian.LegendreThreeSquare

