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

lemma ball_set_eq (k : ℕ) (r : ℝ) (hr : 0 < r) :
    {x : Fin k → ℝ | ∑ i, (x i) ^ 2 < r ^ 2}
      = {x : Fin k → ℝ | (∑ i, |x i| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) < r} := by
  ext x
  have h1 : (∑ i, |x i| ^ (2 : ℝ)) = ∑ i, (x i) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  have hnn : (0 : ℝ) ≤ ∑ i, (x i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, h1, ← Real.sqrt_eq_rpow,
    show r = Real.sqrt (r ^ 2) by rw [Real.sqrt_sq hr.le],
    Real.sqrt_lt_sqrt_iff hnn, Real.sq_sqrt (by positivity)]

