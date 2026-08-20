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

lemma clear_first3 (A : Matrix (Fin 3) (Fin 3) ℤ) (hsym : A.IsSymm) (h00 : A 0 0 = 1) :
    ∃ V : Matrix (Fin 3) (Fin 3) ℤ, V.det = 1 ∧ Vᵀ * A * V =
      !![1, 0, 0;
         0, A 1 1 - A 0 1 ^ 2, A 1 2 - A 0 1 * A 0 2;
         0, A 1 2 - A 0 1 * A 0 2, A 2 2 - A 0 2 ^ 2] := by
  use !![1, -A 0 1, -A 0 2; 0, 1, 0; 0, 0, 1]
  have sym01 : A 1 0 = A 0 1 := by have := congrFun (congrFun hsym 1) 0; simp at this; exact this.symm
  have sym02 : A 2 0 = A 0 2 := by have := congrFun (congrFun hsym 2) 0; simp at this; exact this.symm
  have sym12 : A 2 1 = A 1 2 := by have := congrFun (congrFun hsym 2) 1; simp at this; exact this.symm
  refine ⟨by simp [Matrix.det_fin_three], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, sym01, sym02, sym12, h00] <;> ring_nf

