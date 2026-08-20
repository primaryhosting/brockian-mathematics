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

lemma auxMat_posDef (n x c m : ℤ) (hn : 0 < n) (hc : 0 < n * c - 1)
    (hrel : n * (c * m - x ^ 2) - m = 1) : PosDefZ (auxMat n x c m) := by
  intro v hv
  have hv3 : v = ![v 0, v 1, v 2] := by funext i; fin_cases i <;> rfl
  rw [hv3]
  have hkey := auxMat_key n x c m hrel (v 0) (v 1) (v 2)
  set t := n * c - 1 with ht
  have hA : 0 ≤ t * (n * v 0 + v 1) ^ 2 := by positivity
  have hB : 0 ≤ (t * v 1 - n * x * v 2) ^ 2 := sq_nonneg _
  have hC : 0 ≤ n * (v 2) ^ 2 := by positivity
  have hpos : 0 < t * (n * v 0 + v 1) ^ 2 + (t * v 1 - n * x * v 2) ^ 2 + n * (v 2) ^ 2 := by
    rcases eq_or_ne (v 2) 0 with h2 | h2
    · rcases eq_or_ne (v 1) 0 with h1 | h1
      · have h0 : v 0 ≠ 0 := by
          intro h0; apply hv; funext i; fin_cases i <;> simp [h0, h1, h2]
        have hne : n * v 0 + v 1 ≠ 0 := by
          rw [h1, add_zero]; exact mul_ne_zero (by omega) h0
        have hpp : 0 < t * (n * v 0 + v 1) ^ 2 := by positivity
        linarith
      · have hne : t * v 1 - n * x * v 2 ≠ 0 := by
          rw [h2]; simpa using mul_ne_zero (by omega) h1
        have hpp : 0 < (t * v 1 - n * x * v 2) ^ 2 := by positivity
        linarith
    · have hpp : 0 < n * (v 2) ^ 2 := by positivity
      linarith
  have hnt : 0 < n * t := mul_pos hn hc
  nlinarith [hkey, hpos, hnt]

/-! ## From the arithmetic data to three squares -/

