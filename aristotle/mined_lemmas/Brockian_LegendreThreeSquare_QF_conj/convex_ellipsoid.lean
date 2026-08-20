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

lemma convex_ellipsoid (k : ℕ) (r : ℝ) : Convex ℝ {x : Fin k → ℝ | ∑ i, (x i) ^ 2 < r} := by
  intro x hx y hy s t hs ht hst
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have hle : ∀ i ∈ Finset.univ,
      ((s • x + t • y : Fin k → ℝ) i) ^ 2 ≤ s * (x i) ^ 2 + t * (y i) ^ 2 := by
    intro i _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [sq_nonneg (x i - y i), mul_nonneg hs ht]
  have hrr : s * r + t * r = r := by rw [← add_mul, hst, one_mul]
  have key : s * (∑ i, (x i) ^ 2) + t * (∑ i, (y i) ^ 2) < r := by
    rcases lt_or_eq_of_le hs with hs' | hs'
    · have h1 : s * (∑ i, (x i) ^ 2) < s * r := mul_lt_mul_of_pos_left hx hs'
      have h2 : t * (∑ i, (y i) ^ 2) ≤ t * r := mul_le_mul_of_nonneg_left hy.le ht
      linarith
    · have hs0 : s = 0 := hs'.symm
      have ht1 : t = 1 := by linarith
      rw [hs0, ht1]; simpa using hy
  calc ∑ i, ((s • x + t • y : Fin k → ℝ) i) ^ 2
      ≤ ∑ i, (s * (x i) ^ 2 + t * (y i) ^ 2) := Finset.sum_le_sum hle
    _ = s * (∑ i, (x i) ^ 2) + t * (∑ i, (y i) ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ < r := key

/-- Minkowski's convex body theorem for the lattice spanned by a basis of `Fin k → ℝ`. -/
