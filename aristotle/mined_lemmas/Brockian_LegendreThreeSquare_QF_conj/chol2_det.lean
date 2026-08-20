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

lemma chol2_det (C : Matrix (Fin 2) (Fin 2) ℤ) (h00 : 0 < C 0 0) :
    (chol2Mat C).det = 1 := by
  have h1 : (0 : ℝ) < (C 0 0 : ℝ) := by exact_mod_cast h00
  have hs : Real.sqrt (C 0 0) > 0 := Real.sqrt_pos.mpr h1
  simp [chol2Mat, Matrix.det_fin_two]
  field_simp

