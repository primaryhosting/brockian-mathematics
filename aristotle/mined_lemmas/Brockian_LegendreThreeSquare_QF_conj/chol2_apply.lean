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

lemma chol2_apply (C : Matrix (Fin 2) (Fin 2) ℤ) (hsym : C.IsSymm) (h00 : 0 < C 0 0)
    (hdet : C.det = 1) (v : Fin 2 → ℤ) :
    ((QF C v : ℤ) : ℝ) = ∑ i, ((chol2Mat C).mulVec (fun j => (v j : ℝ)) i) ^ 2 := by
  have h1 : (0 : ℝ) < (C 0 0 : ℝ) := by exact_mod_cast h00
  have hs : Real.sqrt (C 0 0) > 0 := Real.sqrt_pos.mpr h1
  have hsq : Real.sqrt (C 0 0) ^ 2 = (C 0 0 : ℝ) := Real.sq_sqrt h1.le
  have hsym10 : C 1 0 = C 0 1 := by
    have := congr_fun (congr_fun hsym 1) 0; simpa using this.symm
  have hd : (C 0 0 : ℝ) * (C 1 1 : ℝ) - (C 0 1 : ℝ) * (C 0 1 : ℝ) = 1 := by
    have h3 : C.det = C 0 0 * C 1 1 - C 0 1 * C 1 0 := by simp [Matrix.det_fin_two]
    rw [hsym10] at h3
    have h2 : C 0 0 * C 1 1 - C 0 1 * C 0 1 = 1 := by rw [← h3, hdet]
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h2
  simp only [QF, chol2Mat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Int.cast_add, Int.cast_mul]
  push_cast [hsym10]
  field_simp
  rw [hsq]
  linear_combination ((v 1 : ℝ)) ^ 2 * hd

