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

lemma factor_of_conj {k : ℕ} (A S N : Matrix (Fin k) (Fin k) ℤ) (hS : S.det = 1)
    (h : Sᵀ * A * S = Nᵀ * N) : ∃ M : Matrix (Fin k) (Fin k) ℤ, A = Mᵀ * M := by
  obtain ⟨T, hST, hTS⟩ := exists_inv_of_det_one S hS
  use N * T
  have key : Tᵀ * Sᵀ = 1 := by rw [← Matrix.transpose_mul, hST, Matrix.transpose_one]
  calc A = 1 * A * 1 := by rw [Matrix.one_mul, Matrix.mul_one]
    _ = (Tᵀ * Sᵀ) * A * (S * T) := by rw [key, hST]
    _ = Tᵀ * (Sᵀ * A * S) * T := by simp [Matrix.mul_assoc]
    _ = Tᵀ * (Nᵀ * N) * T := by rw [h]
    _ = (N * T)ᵀ * (N * T) := by rw [Matrix.transpose_mul]; simp [Matrix.mul_assoc]

/-! ## Minkowski's convex body theorem -/

/-- Minkowski's convex body theorem for the lattice spanned by a basis of `Fin k → ℝ`. -/
