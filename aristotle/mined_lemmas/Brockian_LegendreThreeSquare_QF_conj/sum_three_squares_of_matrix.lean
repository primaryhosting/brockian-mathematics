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

theorem sum_three_squares_of_matrix (n : ℕ) (A : Matrix (Fin 3) (Fin 3) ℤ) (h00 : A 0 0 = (n : ℤ))
    (hsym : A.IsSymm) (hpos : PosDefZ A) (hdet : A.det = 1) :
    ∃ a b c : ℕ, n = a ^ 2 + b ^ 2 + c ^ 2 := by
  obtain ⟨N, hN⟩ := classify3 A hsym hpos hdet
  have hentry : A 0 0 = (N 0 0) ^ 2 + (N 1 0) ^ 2 + (N 2 0) ^ 2 := by
    rw [hN]
    simp [Matrix.mul_apply, Fin.sum_univ_three]
    ring
  rw [h00] at hentry
  refine ⟨Int.natAbs (N 0 0), Int.natAbs (N 1 0), Int.natAbs (N 2 0), ?_⟩
  have h1 : ((N 0 0).natAbs : ℤ) ^ 2 = (N 0 0) ^ 2 := by simp [sq_abs]
  have h2 : ((N 1 0).natAbs : ℤ) ^ 2 = (N 1 0) ^ 2 := by simp [sq_abs]
  have h3 : ((N 2 0).natAbs : ℤ) ^ 2 = (N 2 0) ^ 2 := by simp [sq_abs]
  push_cast at h1 h2 h3 ⊢
  linarith

/-- From `n ∣ m + 1` and `m ∣ y ^ 2 + n` one produces the entries of the auxiliary form. -/
