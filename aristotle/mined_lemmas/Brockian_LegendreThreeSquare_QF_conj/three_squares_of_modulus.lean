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

theorem three_squares_of_modulus (n : ℕ) (hn : 3 ≤ n) (m : ℕ) (hm : 0 < m) (hdvd : n ∣ m + 1)
    (y : ℤ) (hy : (m : ℤ) ∣ y ^ 2 + n) : ∃ a b c : ℕ, n = a ^ 2 + b ^ 2 + c ^ 2 := by
  obtain ⟨x, c, hc1, hrel⟩ := exists_aux_data n m hn hm hdvd y hy
  have hnz : (0 : ℤ) < (n : ℤ) := by exact_mod_cast (by omega : 0 < n)
  refine sum_three_squares_of_matrix n (auxMat (n : ℤ) x c (m : ℤ)) ?_
    (auxMat_isSymm _ _ _ _) (auxMat_posDef _ _ _ _ hnz hc1 hrel) (auxMat_det _ _ _ _ hrel)
  simp [auxMat]

/-! ## Dirichlet's theorem and quadratic reciprocity -/

