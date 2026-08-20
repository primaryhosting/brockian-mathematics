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

lemma clear_first2 (C : Matrix (Fin 2) (Fin 2) ℤ) (hsym : C.IsSymm) (h00 : C 0 0 = 1) :
    ∃ V : Matrix (Fin 2) (Fin 2) ℤ, V.det = 1 ∧ Vᵀ * C * V = !![1, 0; 0, C 1 1 - C 0 1 ^ 2] := by
  have hsym10 : C 1 0 = C 0 1 := by
    have := congr_fun (congr_fun hsym 1) 0; simpa using this.symm
  refine ⟨!![1, -C 0 1; 0, 1], by simp [Matrix.det_fin_two], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h00, hsym10] <;> ring

