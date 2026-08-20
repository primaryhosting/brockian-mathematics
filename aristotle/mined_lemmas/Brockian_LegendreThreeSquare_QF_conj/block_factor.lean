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

lemma block_factor (p q r : ℤ) (N : Matrix (Fin 2) (Fin 2) ℤ)
    (h : (!![p, q; q, r] : Matrix (Fin 2) (Fin 2) ℤ) = Nᵀ * N) :
    ∃ N' : Matrix (Fin 3) (Fin 3) ℤ,
      (!![1, 0, 0; 0, p, q; 0, q, r] : Matrix (Fin 3) (Fin 3) ℤ) = N'ᵀ * N' := by
  refine ⟨!![1, 0, 0; 0, N 0 0, N 0 1; 0, N 1 0, N 1 1], ?_⟩
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h11
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;> linarith

/-! ## Classification of unimodular positive definite forms -/

