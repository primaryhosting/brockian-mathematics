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

lemma QF_conj {k : ℕ} (A U : Matrix (Fin k) (Fin k) ℤ) (v : Fin k → ℤ) :
    QF (Uᵀ * A * U) v = QF A (U.mulVec v) := by
  simp only [QF]
  simp only [Matrix.mulVec_mulVec]
  simp only [Matrix.mul_assoc]
  have h : (Uᵀ * (A * U)) *ᵥ v = Uᵀ *ᵥ ((A * U) *ᵥ v) := (Matrix.mulVec_mulVec _ _ _).symm
  rw [h]
  have key : ∀ (x y : Fin k → ℤ) (M : Matrix (Fin k) (Fin k) ℤ), x ⬝ᵥ (Mᵀ *ᵥ y) = (M *ᵥ x) ⬝ᵥ y := by
    intro x y M
    simp [Matrix.mulVec, dotProduct]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    congr 1 with i
    simp [mul_comm, Finset.mul_sum]
    ring_nf
  exact key v _ U

