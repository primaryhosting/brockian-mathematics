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

theorem exists_unimodular_col2 (v : Fin 2 → ℤ) (w : Fin 2 → ℤ) (h : w ⬝ᵥ v = 1) :
    ∃ U : Matrix (Fin 2) (Fin 2) ℤ, U.det = 1 ∧ ∀ i, U i 0 = v i := by
  use !![v 0, -w 1; v 1, w 0]
  refine ⟨?_, fun i => by fin_cases i <;> rfl⟩
  simp [Matrix.det_fin_two]
  linarith [show w 0 * v 0 + w 1 * v 1 = 1 from by simpa [dotProduct, Fin.sum_univ_two] using h]

