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

noncomputable def chol3Mat (A : Matrix (Fin 3) (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.sqrt (A 0 0), (A 0 1 : ℝ) / Real.sqrt (A 0 0), (A 0 2 : ℝ) / Real.sqrt (A 0 0);
     0, Real.sqrt (((A 0 0 * A 1 1 - A 0 1 ^ 2 : ℤ) : ℝ) / (A 0 0 : ℝ)),
        ((A 0 0 * A 1 2 - A 0 1 * A 0 2 : ℤ) : ℝ) /
          Real.sqrt ((A 0 0 : ℝ) * ((A 0 0 * A 1 1 - A 0 1 ^ 2 : ℤ) : ℝ));
     0, 0, 1 / Real.sqrt ((A 0 0 * A 1 1 - A 0 1 ^ 2 : ℤ) : ℝ)]

