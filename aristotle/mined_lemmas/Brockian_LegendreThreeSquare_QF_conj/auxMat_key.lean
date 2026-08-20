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

lemma auxMat_key (n x c m : ℤ) (hrel : n * (c * m - x ^ 2) - m = 1) (u v w : ℤ) :
    n * (n * c - 1) * QF (auxMat n x c m) ![u, v, w]
      = (n * c - 1) * (n * u + v) ^ 2 + ((n * c - 1) * v - n * x * w) ^ 2 + n * w ^ 2 := by
  simp [QF, dotProduct, auxMat, Fin.sum_univ_three, Matrix.mulVec, Matrix.of_apply]
  have h1 : m * (n * c - 1) = n * x ^ 2 + 1 := by linarith
  linear_combination n * w ^ 2 * h1

